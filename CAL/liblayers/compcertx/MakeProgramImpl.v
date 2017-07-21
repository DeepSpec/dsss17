Require Import liblayers.lib.Decision.
Require Export MakeProgramSpec.


(** * Implementation of [make_program] *)

(** Below we construct [make_program] from the bottom up, first
  defining functions to produce individual definitions, then using
  them while enumerating the stencil to construct the actual
  program.

  Our proofs of [make_program]'s properties follow the same pattern:
  we first caracterize the components, then use those lemmas as we
  build things up. *)

Local Arguments ret : simpl never.
Local Arguments bind : simpl never.

Section MAKE_PROGRAM_DEF.
  Context `{progfmt: ProgramFormat}.

  (** ** Individual definitions *)

  (** First, we define how to construct global definition from the
    components we'll obtain from the module and layer. *)

  Definition make_fundef_at {D} i (ML: module * layer D): res (option Fp) :=
    mf <- get_module_layer_function i ML;
    match mf with
      | None => OK None
      | Some f => fdef <- make_fundef D i f; OK (Some fdef)
    end.

  Definition make_vardef_at {D} i (ML: module * layer D) :=
    mτ <- get_module_layer_variable i ML;
    match mτ with
      | None => OK None
      | Some τ => vdef <- make_varinfo τ; OK (Some vdef)
    end.

  Definition make_globdef_at D (i: ident) (ML: module * layer D) :=
    make_globdef
      (make_fundef_at i ML)
      (make_vardef_at i ML).

  Lemma make_globdef_noconflict D i M L d:
    make_globdef_at D i (M, L) = OK d ->
    noconflict
      (get_module_function i M)
      (get_module_variable i M)
      (get_layer_primitive i L)
      (get_layer_globalvar i L).
  Proof.
    unfold make_globdef_at, make_globdef.
    unfold make_vardef_at, make_fundef_at.
    unfold get_module_layer_function.
    unfold get_module_layer_variable.
    unfold fst, snd.
    destruct (get_module_function i M) as [[|]|];
    destruct (get_layer_primitive i L) as [[|]|]; simpl; monad_norm;
    try destruct (make_fundef _ _ _); monad_norm; try discriminate;
    destruct (get_module_variable i M) as [[ τM |]|];
    destruct (get_layer_globalvar i L) as [[ τL |]|]; simpl; monad_norm;
    GlobalVars.res_option_globalvar_red; monad_norm;
    try destruct (make_varinfo _); monad_norm; try discriminate;
    try constructor;
    destruct (decide (τM = τL));
    subst;
    autorewrite with res_option_globalvar;
    monad_norm; try (destruct (make_varinfo _); monad_norm; try discriminate);
    try constructor;
    rewrite GlobalVars.res_option_globalvar_oplus_diff by congruence;
      monad_norm;
      discriminate.
  Qed.

  (** ** [add_prog_defs] *)

  (** Now we want to build the program by iterating over the list of
    identifiers in the stencil, taking into account that we may fail
    at any point if the given layer and modules do not satisfy the
    required conditions.

    Note that we append at the end of the list at each iteration. This
    works best with [globdefs_rel] but there's a change it will stack
    overflow and/or be very slow? *)

  Definition make_prog_defs D (ML: module * layer D) :=
    positive_rec
      (res (list (ident × option (globdef Fp Vp))))
      (OK nil)
      (fun (i: ident) (defs: res (list _)) =>
         l <- defs;
         d <- make_globdef_at D i ML;
         OK (l ++ (i, d) :: nil))
      glob_threshold.

  (** ** Definition of [make_program] *)

  (** Once we've built the definitions, building the program is
    straightforward: we check that the program is valid in the
    following sense (all module/layer entries are within
    [glob_threshold]), then combine the definitions with a fixed
    identifier for the main() function. *)

  Definition valid_program {D} (ML: module * layer D): Prop :=
    (forall i,
       ~ isOKNone (get_layer_primitive i (snd ML)) ->
       (i < glob_threshold)%positive) /\
    (forall i,
       ~ isOKNone (get_layer_globalvar i (snd ML)) ->
       (i < glob_threshold)%positive) /\
    (forall i,
       ~ isOKNone (get_module_function i (fst ML)) ->
       (i < glob_threshold)%positive) /\
    (forall i,
       ~ isOKNone (get_module_variable i (fst ML)) ->
       (i < glob_threshold)%positive).

  Definition make_program D (ML: module * layer D): res (AST.program Fp Vp) :=
    Hvalid <- eassert nil (valid_program ML);
    defs <- make_prog_defs D ML;
    ret {|
      prog_defs := defs;
      prog_public := map fst defs;
      prog_main := xH (* dummy *)
    |}.

  Lemma positive_rec_inv {A} (f: positive -> A -> res A) (v1: A) i r:
    positive_rec (res A) (OK v1) (fun i => Monad.bind (f i)) i = OK r ->
    forall j, (j < i)%positive -> exists vj vj', f j vj = OK vj'.
  Proof.
    revert r.
    pattern i.
    apply positive_Peano_ind.
    - rewrite positive_rec_base.
      intros.
      xomega.
    - setoid_rewrite positive_rec_succ.
      intros i' IHi r Hfi j Hj.
      inv_monad Hfi.
      apply Pos.lt_succ_r in Hj.
      apply Pos.lt_eq_cases in Hj.
      destruct Hj as [Hj|Hj]; eauto.
      subst; eauto.
  Qed.

  Lemma make_program_noconflict D M L p i:
    make_program D (M, L) = OK p ->
    noconflict
      (get_module_function i M)
      (get_module_variable i M)
      (get_layer_primitive i L)
      (get_layer_globalvar i L).
  Proof.
    intros Hp.
    unfold make_program in Hp.
    inv_monad Hp.
    destruct (decide (i < glob_threshold)%positive) as [Hi|Hi].
    - unfold make_prog_defs in H1.
      eapply positive_rec_inv in H1; eauto.
      destruct H1 as (? & ? & H1); inv_monad H1.
      eapply make_globdef_noconflict; eauto.
    - match goal with
          Y: eassert _ _ = _ |- _ =>
          clear Y
      end.
      match goal with
          X: valid_program (M, L) |- _ =>
          destruct X as (Xlp & Xlv & Xmf & Xmv)
      end.
      specialize (Xlp i).
      specialize (Xlv i).
      specialize (Xmf i).
      specialize (Xmv i).
      unfold fst in *.
      unfold snd in *.
      unfold ident in * |- * .
      destruct (get_module_function i M) as [ [ | ] | ] ;
        try (edestruct Hi; apply Xmf; unfold isOKNone; congruence).
      destruct (get_module_variable i M) as [ [ | ] | ] ;
        try (edestruct Hi; apply Xmv; unfold isOKNone; congruence).
      destruct (get_layer_primitive i L) as [ [ | ] | ] ;
        try (edestruct Hi; apply Xlp; unfold isOKNone; congruence).
      destruct (get_layer_globalvar i L) as [ [ | ] | ] ;
        try (edestruct Hi; apply Xlv; unfold isOKNone; congruence).
      constructor.
  Qed.
End MAKE_PROGRAM_DEF.

Global Instance make_program_ops: MakeProgramOps :=
  {
    make_program := @make_program
  }.


(** * Relational properties *)

Section MAKE_PROGRAM_REL.
  Context `{HR: MakeProgramRelations}.

  Instance make_fundef_rel i:
    Monotonic
      (make_fundef _ i)
      (RFm i @@ Some ++> res_le (RFp i @@ Some)).
  Proof.
    intros f1 f2 Hf.
    destruct (make_fundef D1 i f1) as [fp1|] eqn:Hf1.
    - destruct (make_fundef D2 i f2) as [fp2|] eqn:Hf2; constructor.
      eapply (make_program_function_relations i); eauto; constructor; eauto.
    - edestruct (make_fundef_error i f1 f2 Hf).
      + red.
        eauto.
      + rewrite H.
        constructor.
  Qed.

  Instance make_fundef_rel_params:
    Params (@make_fundef) 1.

  Instance make_vardef_rel i:
    Monotonic
      make_varinfo
      (RVm i @@ Some ++> res_le (RVp i @@ Some)).
  Proof.
    intros τ1 τ2 Hτ.
    destruct (make_varinfo τ1) as [τ1'|] eqn:H1.
    - destruct (make_varinfo τ2) as [τ2'|] eqn:H2; constructor.
      eapply (make_program_variable_relations i); eauto; constructor; eauto.
    - edestruct (make_vardef_error i _ _ Hτ).
      + red.
        eauto.
      + rewrite H.
        constructor.
  Qed.

  Instance make_varinfo_rel_params:
    Params (@make_varinfo) 1.

  Local Hint Extern 1 (RStep _ (_ (_ <- _ ;_) (_ <- _; _))) =>
    eapply bind_res_le : typeclass_instances.

  Instance make_fundef_at_rel i:
    Monotonic
      (make_fundef_at i)
      (module_layer_rel D1 D2 RFm RVm ++> res_le (RFp i /\ option_le ⊤)).
  Proof.
    unfold make_fundef_at.
    repeat rstep.
    destruct x0, y0.
    - solve_monotonic.
      split; eauto.
      repeat constructor.
    - eapply option_rel_fw in H0; eauto.
      discriminate.
    - destruct (make_fundef _ _ _) eqn:Hfdef; constructor.
      split.
      + eapply has_image; eauto; constructor; eauto.
      + constructor.
    - constructor.
      split.
      + eapply has_image; eauto; constructor.
      + constructor.
  Qed.

  Instance make_fundef_at_rel_params:
    Params (@make_fundef_at) 1.

  Instance make_vardef_at_rel i:
    Monotonic
      (make_vardef_at i)
      (module_layer_rel D1 D2 RFm RVm ++> res_le (RVp i /\ option_le ⊤)).
  Proof.
    destruct HR as [_ Hvo].
    unfold make_vardef_at.
    repeat rstep.
    destruct x0, y0.
    - repeat rstep.
      split; eauto.
      repeat constructor.
    - eapply option_rel_fw in H0; eauto.
      discriminate.
    - destruct (make_varinfo _) eqn:Hvdef; constructor.
      split.
      + eapply has_image; eauto; constructor; eauto.
      + constructor.
    - constructor.
      split.
      + eapply has_image; eauto; constructor.
      + constructor.
  Qed.

  Instance make_vardef_at_rel_params:
    Params (@make_vardef_at) 1.

  Instance make_globdef_at_rel i:
    Monotonic
      (make_globdef_at _ i)
      (module_layer_rel D1 D2 RFm RVm ++> res_le (globdef_rel RFp RVp i)).
  Proof.
    unfold make_globdef_at.
    rauto.
  Qed.

  Instance make_glolbdef_at_rel_params:
    Params (@make_globdef_at) 1.

  Instance positive_rec_rel:
    Monotonic
      positive_rec
      (forallr R : fun A B => positive -> rel A B,
         R 1%positive ++>
         (forall_pointwise_rel (fun i => R i ++> R (Pos.succ i))) ++>
         forall_pointwise_rel R).
  Proof.
    intros A B R x y Hxy f g Hfg i.
    revert i.
    apply positive_Peano_ind.
    - rewrite !positive_rec_base.
      assumption.
    - intros i IHi.
      rewrite !positive_rec_succ.
      solve_monotonic.
  Qed.

  Instance make_prog_defs_rel:
    Monotonic
      (make_prog_defs _)
      (module_layer_rel D1 D2 RFm RVm ++>
       res_le (globdefs_rel RFp RVp glob_threshold)).
  Proof.
    unfold make_prog_defs.
    repeat rstep.
    eapply (positive_rec_rel _ _ (fun i => res_le (globdefs_rel _ _ i)));
    repeat (repeat rstep; constructor).
  Qed.

  Instance make_prog_defs_rel_params:
    Params (@make_prog_defs) 1.

  Instance valid_program_rel:
    Monotonic
      valid_program
      (module_layer_rel D1 D2 RFm RVm --> impl).
  Proof.
    repeat red.
    unfold flip.
    unfold module_layer_rel.
    unfold valid_program.
    intros x y H H0.
    destruct H0 as (Xlp & Xlv & Xmf & Xmv).
    split.
    { intros i H0.
      specialize (H i).
      destruct H as (Hf & _).
      unfold get_module_layer_function in Hf.
      unfold ident in * |- * .
      specialize (Xlp i).
      specialize (Xmf i).
      cut (~ isOKNone (get_layer_primitive i (snd x)) \/
              ~ isOKNone (get_module_function i (fst x))).
      {
        tauto.
      }
      unfold isOKNone in *.
      destruct (get_module_function i (fst x)) as [ [ | ] | ] ;
        (try intuition congruence);
        destruct (get_layer_primitive i (snd x)) as [ [ | ] | ] ;
        (try intuition congruence).
      destruct (get_layer_primitive i (snd y)) as [ [ | ] | ] ;
        (try congruence);
      destruct (get_module_function i (fst y)) as [ [ | ] | ] ;
        simpl in Hf;
        inversion Hf;
        subst.
      match goal with
          K: RFm _ _ _ |- _ =>
          apply (make_program_function_relation_fw i) in K;
            specialize (K (eq_refl _));
            discriminate
      end.
    }
    split.
    { intros i H0.
      specialize (H i).
      destruct H as (_ & Hv).
      unfold get_module_layer_variable in Hv.
      unfold ident in * |- * .
      specialize (Xlv i).
      specialize (Xmv i).
      cut (~ isOKNone (get_layer_globalvar i (snd x)) \/
              ~ isOKNone (get_module_variable i (fst x))).
      {
        tauto.
      }
      unfold isOKNone in *.
      destruct (get_module_variable i (fst x)) as [ [ | ] | ] ;
        (try intuition congruence);
        destruct (get_layer_globalvar i (snd x)) as [ [ | ] | ] ;
        (try intuition congruence).
      revert Hv.
      GlobalVars.res_option_globalvar_red.
      destruct (get_layer_globalvar i (snd y)) as [ [ gl | ] | ] ;
        (try congruence);
      destruct (get_module_variable i (fst y)) as [ [ gm | ] | ] ;
      GlobalVars.res_option_globalvar_red;
      inversion 1;
        subst;
      match goal with
          K: RVm _ _ _ |- _ =>
          apply (make_program_variable_relation_fw i) in K;
            specialize (K (eq_refl _));
            try discriminate
      end.
      subst.
      match goal with
          K: _ = _ ⊕ _ |- _ =>
          revert K
      end.
      destruct (decide (gm = gl)).
      + subst. GlobalVars.res_option_globalvar_red. discriminate.
      + rewrite GlobalVars.res_option_globalvar_oplus_diff by assumption.
        discriminate.
    }
    split.
    { intros i H0.
      specialize (H i).
      destruct H as (Hf & _).
      unfold get_module_layer_function in Hf.
      unfold ident in * |- * .
      specialize (Xlp i).
      specialize (Xmf i).
      cut (~ isOKNone (get_layer_primitive i (snd x)) \/
              ~ isOKNone (get_module_function i (fst x))).
      {
        tauto.
      }
      unfold isOKNone in *.
      destruct (get_module_function i (fst x)) as [ [ | ] | ] ;
        (try intuition congruence);
        destruct (get_layer_primitive i (snd x)) as [ [ | ] | ] ;
        (try intuition congruence).
      destruct (get_module_function i (fst y)) as [ [ | ] | ] ;
        (try congruence);
      destruct (get_layer_primitive i (snd y)) as [ [ | ] | ] ;
        simpl in Hf;
        inversion Hf;
        subst.
      match goal with
          K: RFm _ _ _ |- _ =>
          apply (make_program_function_relation_fw i) in K;
            specialize (K (eq_refl _));
            discriminate
      end.
    }
    { intros i H0.
      specialize (H i).
      destruct H as (_ & Hv).
      unfold get_module_layer_variable in Hv.
      unfold ident in * |- * .
      specialize (Xlv i).
      specialize (Xmv i).
      cut (~ isOKNone (get_layer_globalvar i (snd x)) \/
              ~ isOKNone (get_module_variable i (fst x))).
      {
        tauto.
      }
      unfold isOKNone in *.
      destruct (get_module_variable i (fst x)) as [ [ | ] | ] ;
        (try intuition congruence);
        destruct (get_layer_globalvar i (snd x)) as [ [ | ] | ] ;
        (try intuition congruence).
      revert Hv.
      GlobalVars.res_option_globalvar_red.
      destruct (get_module_variable i (fst y)) as [ [ gm | ] | ] ;
        (try congruence);
      destruct (get_layer_globalvar i (snd y)) as [ [ gl | ] | ] ;
      GlobalVars.res_option_globalvar_red;
      inversion 1;
        subst;
      match goal with
          K: RVm _ _ _ |- _ =>
          apply (make_program_variable_relation_fw i) in K;
            specialize (K (eq_refl _));
            try discriminate
      end.
      subst.
      match goal with
          K: _ = _ ⊕ _ |- _ =>
          revert K
      end.
      destruct (decide (gm = gl)).
      + subst. GlobalVars.res_option_globalvar_red. discriminate.
      + rewrite GlobalVars.res_option_globalvar_oplus_diff by assumption.
        discriminate.
    }
  Qed.

  Instance valid_program_rel_params:
    Params (@valid_program) 1.

  Instance make_program_rel:
    Monotonic
      (make_program _)
      (module_layer_rel D1 D2 RFm RVm ++> res_le (program_rel RFp RVp)).
  Proof.
    unfold make_program, ret; simpl.
    repeat rstep.
    eapply eassert_le; solve_monotonic.
    constructor; repeat rstep.
    + induction H1; simpl; repeat rstep. eauto.
      instantiate (1 := ⊤%rel).
      rauto.
    + intros i H2.
      clear H0.
      destruct y0 as (Ylp & _ & Ymf & _).
      specialize (Ylp i).
      assert (get_layer_primitive i (snd y) = OK None) as Hylp.
      {
        destruct (decide (isOKNone (get_layer_primitive i (snd y)))); auto.
        apply Ylp in n.
        xomega.
      }
      specialize (Ymf i).
      assert (get_module_function i (fst y) = OK None) as Hymf.
      {
        destruct (decide (isOKNone (get_module_function i (fst y)))); auto.
        apply Ymf in n.
        xomega.
      }
      destruct x0 as (Xlp & _ & Xmf & _).
      specialize (Xlp i).
      assert (get_layer_primitive i (snd x) = OK None) as Hxlp.
      {
        destruct (decide (isOKNone (get_layer_primitive i (snd x)))); auto.
        apply Xlp in n.
        xomega.
      }
      specialize (Xmf i).
      assert (get_module_function i (fst x) = OK None) as Hxmf.
      {
        destruct (decide (isOKNone (get_module_function i (fst x)))); auto.
        apply Xmf in n.
        xomega.
      }
      unfold module_layer_rel in H.
      specialize (H i).
      destruct H as (H & _).
      unfold get_module_layer_function in H.
      unfold ident in *.
      rewrite Hylp in H.
      rewrite Hymf in H.
      rewrite Hxlp in H.
      rewrite Hxmf in H.
      simpl in H.
      inversion H; subst.
      generalize (make_program_function_relations i).
      intro K.
      repeat red in K.
      eapply K; eauto; constructor.
    + intros i H2.
      clear H0.
      destruct y0 as (_  & Ylv & _ & Ymv).
      specialize (Ylv i).
      assert (get_layer_globalvar i (snd y) = OK None) as Hylv.
      {
        destruct (decide (isOKNone (get_layer_globalvar i (snd y)))); auto.
        apply Ylv in n.
        xomega.
      }
      specialize (Ymv i).
      assert (get_module_variable i (fst y) = OK None) as Hymv.
      {
        destruct (decide (isOKNone (get_module_variable i (fst y)))); auto.
        apply Ymv in n.
        xomega.
      }
      destruct x0 as (_ & Xlv & _ & Xmv).
      specialize (Xlv i).
      assert (get_layer_globalvar i (snd x) = OK None) as Hxlv.
      {
        destruct (decide (isOKNone (get_layer_globalvar i (snd x)))); auto.
        apply Xlv in n.
        xomega.
      }
      specialize (Xmv i).
      assert (get_module_variable i (fst x) = OK None) as Hxmv.
      {
        destruct (decide (isOKNone (get_module_variable i (fst x)))); auto.
        apply Xmv in n.
        xomega.
      }
      unfold module_layer_rel in H.
      specialize (H i).
      destruct H as (_ & H).
      unfold get_module_layer_variable in H.
      unfold ident in *.
      rewrite Hylv in H.
      rewrite Hymv in H.
      rewrite Hxlv in H.
      rewrite Hxmv in H.
      revert H.
      GlobalVars.res_option_globalvar_red.
      inversion 1; subst.
      generalize (make_program_variable_relations i).
      intro K.
      repeat red in K.
      eapply K; eauto; constructor.
  Qed.
End MAKE_PROGRAM_REL.


Lemma make_prog_defs_map_fst:
  forall `{ProgramFormatOps} D1 M1 L1 x,
    make_prog_defs D1 (M1, L1) = ret x ->
    map fst x = positive_rec _ nil (fun i d => d ++ i :: nil) glob_threshold.
Proof.
  unfold make_prog_defs.
  intros layerdata Fm Vm Fp Vp module primsem layer gv_ops primsem_ops layer_ops module_ops H D1 M1 L1.
  generalize glob_threshold.
  intro b.
  pattern b. apply positive_Peano_ind.
  - intros. rewrite positive_rec_base in *. inv H0. reflexivity.
  - intros. rewrite positive_rec_succ in *.
    inv_monad H1.
    specialize (H0 _ H4). subst.
    rewrite map_app. simpl. setoid_rewrite H0.
    reflexivity.
Qed.

(** * Instance of [MakeProgram] *)

Global Instance make_program_spec:
  MakeProgram.
Proof.
  split.
  - eapply @make_program_rel.
  - eapply @make_program_noconflict.
  - simpl. unfold make_program.
    intros. inv_monad H0. subst. simpl. apply incl_refl.
  - simpl. unfold make_program.
    intros. inv_monad H0. inv_monad H1. subst. simpl.
    clear - H3 H5.
    setoid_rewrite (make_prog_defs_map_fst _ _ _ _ H5).
    setoid_rewrite (make_prog_defs_map_fst _ _ _ _ H3). reflexivity.
Qed.
