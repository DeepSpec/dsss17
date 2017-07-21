Require Import Decision.
Require Import Semantics. (* for [module_layer_disjoint] *)
Require Export MakeProgramSpec.

Local Arguments ret : simpl never.
Local Arguments bind : simpl never.

Section MAKE_PROGRAM_FACTS.
  Context `{Hmkp: MakeProgram}.
  Context `{Hpf: ProgramFormat}.
  Context `{Hmodule: !Modules ident Fm (globvar Vm) module}.
  Context `{Hlayer: !Layers ident primsem (globvar Vm) layer}.

  Global Instance top_preo A:
    @PreOrder A ⊤%rel.
  Proof.
    firstorder.
  Qed.

  (** * Preliminaries *)

  (** ** Using [make_program_noconflict] *)

  Lemma make_program_make_globalenv {D} ML p:
    make_program D ML = OK p ->
    make_globalenv D ML = OK (Genv.globalenv p).
  Proof.
    intros Hp.
    unfold make_globalenv.
    rewrite Hp.
    reflexivity.
  Qed.

  Lemma make_globalenv_make_program {D} ML ge:
    make_globalenv D ML = OK ge ->
    exists p, make_program D ML = OK p.
  Proof.
    intros Hge.
    unfold make_globalenv in Hge.
    inv_monad Hge.
    eauto.
  Qed.

  Ltac noconflict_for H i :=
    lazymatch type of H with
      | make_program _ (?M, ?L) = _ =>
        let tac :=
          destruct (make_program_noconflict _ _ _ _ i H); eauto; discriminate
        in
          try assert (HMfi: get_module_function i M = OK None) by tac;
          try assert (HMvi: get_module_variable i M = OK None) by tac;
          try assert (HLpi: get_layer_primitive i L = OK None) by tac;
          try assert (HLvi: get_layer_globalvar i L = OK None) by tac;
          try assert (HMLv: get_layer_globalvar i L = get_module_variable i M) by tac
      | make_globalenv _ _ = _ =>
        let p := fresh "p" in
        let Hp := fresh "H" p in
          destruct (make_globalenv_make_program _ _ H) as [p Hp];
          noconflict_for Hp i
    end.

  (** ** Elementary relations for [make_program_rel] *)

  (** We're going to prove many theorems by constructing
    relation families that encode constraints on the module-layer pair
    corresponding to the theorem's premises, then showing that once
    the relations are transported to the program or global
    environment, they entail our conclusion. To facilitate this
    process we introduce the following language.

    So far the following relations can be used:
      - [mprc_empty] imposes no contraints on the program;
      - [mprc_fun i κ] requires that the program define [i] to be the
        internal function [κ];
      - [mprc_prim i σ] requires that the program define [i] to be the
        primitive with specification [σ];
      - [mprc_var i τ] requires that the program define [i] to be the
        global variable with definition [τ].

    Of course, we could come up with something much more general,
    however this suffices for now. *)

  Inductive mprc D :=
    | mprc_empty
    | mprc_fun (i: ident) (κ: Fm)
    | mprc_prim (i: ident) (σ: primsem D)
    | mprc_var (i: ident) (τ: globvar Vm).

  Definition mprc_funrel {D} (R: mprc D): funrel D D :=
    fun j =>
      (eq /\
       match R with
         | mprc_fun i κ =>
           if decide (i = j) then fun x y => y = Some (inl κ) else ⊤
         | mprc_prim i σ =>
           if decide (i = j) then fun x y => y = Some (inr σ) else ⊤
         | _ =>
           ⊤
       end)%rel.

  Definition mprc_varrel {D} (R: mprc D): varrel :=
    fun j =>
      (eq /\
       match R with
         | mprc_var i τ =>
           if decide (i = j) then fun x y => y = Some τ else ⊤
         | _ =>
           ⊤
       end)%rel.

  (** We will be interested in establishing that a module-layer pair
    is related to itself, and expoiting the fact that the resulting
    global environement is the related to itself as well. *)

  Definition mprc_pre {D} (R: @mprc D) (ML: module * layer D) :=
    match R with
      | mprc_empty =>
        True
      | mprc_fun i κ =>
        get_module_function i (fst ML) = OK (Some κ)
      | mprc_prim i σ =>
        get_layer_primitive i (snd ML) = OK (Some σ)
      | mprc_var i τ =>
        get_module_variable i (fst ML) = OK (Some τ) \/
        get_layer_globalvar i (snd ML) = OK (Some τ)
    end.

  (** XXX: we need this for the proof below; perhaps it should be in coqrel. *)

  Lemma rel_inter_preo {A} (R1 R2: rel A A):
    PreOrder R1 ->
    PreOrder R2 ->
    PreOrder (R1 /\ R2).
  Proof.
    intros HR1 HR2.
    split.
    - intros x.
      rauto.
    - intros x y z Hxy Hyz.
      split; etransitivity; rauto.
  Qed.

  Hint Extern 2 (PreOrder (_ /\ _)) =>
    eapply rel_inter_preo : typeclass_instances.

  Lemma mprc_pre_sound {D} R ML:
    @mprc_pre D R ML ->
    module_layer_rel D D (mprc_funrel R) (mprc_varrel R) ML ML.
  Proof.
    destruct ML as [M L], R;
    unfold mprc_pre, mprc_funrel, mprc_varrel, fst, snd;
    intros H j;
    try destruct H as [H|H];
    try destruct (decide (i = j)); subst;
    split;
    try reflexivity;
    unfold get_module_layer_function, get_module_layer_variable, fst, snd;
    rewrite H.
    - destruct (get_layer_primitive j L) as [[|]|]; repeat constructor.
    - destruct (get_module_function j M) as [[|]|]; repeat constructor.
    - destruct (get_layer_globalvar j L) as [[ τ'|]|]; repeat constructor.
      destruct (GlobalVars.globalvar_eq_dec τ τ').
      + subst. autorewrite with res_option_globalvar. repeat constructor.
      + rewrite GlobalVars.res_option_globalvar_oplus_diff by assumption.
        constructor.
    - destruct (get_module_variable j M) as [[ τ' |]|]; repeat constructor.
      destruct (GlobalVars.globalvar_eq_dec τ' τ).
      + subst. autorewrite with res_option_globalvar. repeat constructor.
      + rewrite GlobalVars.res_option_globalvar_oplus_diff by assumption.
        constructor.
  Qed.

  Definition mprc_post {D} (R: @mprc D) (ge: Genv.t Fp Vp) :=
    match R with
      | mprc_empty =>
        True
      | mprc_fun i κ =>
        exists fdef b,
          make_internal κ = OK fdef /\
          Genv.find_symbol ge i = Some b /\
          Genv.find_funct_ptr ge b = Some fdef
      | mprc_prim i σ =>
        exists fdef b,
          make_external D i σ = OK fdef /\
          Genv.find_symbol ge i = Some b /\
          Genv.find_funct_ptr ge b = Some fdef
      | mprc_var i τ =>
        exists vdef b,
          make_varinfo τ = OK vdef /\
          Genv.find_symbol ge i = Some b /\
          Genv.find_var_info ge b = Some vdef
    end.

  Lemma mprc_post_complete {D} R ge:
    genv_rel
      (fundef_rel D D (mprc_funrel R))
      (vardef_rel (mprc_varrel R))
      ge ge ->
    @mprc_post D R ge.
  Proof.
    intros H.
    destruct R; simpl; eauto;
    [ pose proof (genv_rel_find_funct_ptr _ _ _ _ i H) as H' ..
    | pose proof (genv_rel_find_var_info _ _ _ _ i H) as H' ];
    inv_monad H';
    destruct H2 as [? ?];
    simpl in *;
    (destruct (decide (i = i)); [ | congruence]; subst);
    inversion H1; clear H1; subst;
    inv_monad H3;
    simpl in *;
    eauto.
  Qed.

  (** We can use the relational property of [make_program] with
    [mprc_funrel] and [mprc_varrel] to brige these two things. *)

  Instance mprc_funrel_mpr D (R: mprc D) i:
    OptionRelationForward (mprc_funrel R i).
  Proof.
    destruct R; simpl; intros x y Hxy Hy;
    try destruct (decide (_ = _)); inversion Hxy; congruence.
  Qed.

  Instance mprc_varrel_mpr D (R: mprc D) i:
    OptionRelationForward (mprc_varrel R i).
  Proof.
    destruct R; simpl; intros x y Hxy Hy;
    try destruct (decide (_ = _)); inversion Hxy; congruence.
  Qed.

  Instance mprc_funrel_err D (R: mprc D) i:
    Monotonic (make_fundef D i) (mprc_funrel R i @@ Some ++> impl @@ isError).
  Proof.
    intros x y [Hxy _].
    inversion Hxy; subst; reflexivity.
  Qed.

  Instance mprc_varrel_err D (R: mprc D) i:
    Monotonic make_varinfo (mprc_varrel R i @@ Some ++> impl @@ isError).
  Proof.
    intros x y [Hxy _].
    inversion Hxy; subst; reflexivity.
  Qed.

  Lemma make_globalenv_rel_mprc D R ML ge:
    make_globalenv D ML = OK ge ->
    module_layer_rel D D (mprc_funrel R) (mprc_varrel R) ML ML ->
    genv_rel (fundef_rel D D (mprc_funrel R)) (vardef_rel (mprc_varrel R)) ge ge.
  Proof.
    intros Hge HML.
    assert (Hge':
      res_le (genv_rel (fundef_rel D D (mprc_funrel R))
                       (vardef_rel (mprc_varrel R))) (OK ge) (OK ge)).
    {
      rewrite <- !Hge.
      (* FIXME: solve_monotonic should work *)
      eapply make_globalenv_rel; eauto.
      typeclasses eauto.
    }
    inversion Hge'.
    assumption.
  Qed.

  (** We can now design a tactic that puts all of these components together. *)

  Ltac use_mprc H R :=
    lazymatch type of H with
      | make_program ?D ?ML = _ =>
        let Hge := fresh "Hge" in
        pose proof (make_program_make_globalenv _ _ H) as Hge;
        use_mprc Hge R
      | make_globalenv ?D ?ML = _ =>
        let HR := fresh "HR" in
        pose proof H as HR;
        eapply (make_globalenv_rel_mprc _ R) in HR;
        [ eapply mprc_post_complete in HR;
          simpl in H
        | eapply mprc_pre_sound;
          simpl;
          get_module_normalize;
          get_layer_normalize ]
    end.

  (** ** Other useful lemmas *)

  Instance res_le_refl `(Reflexive):
    Reflexive (res_le R).
  Proof.
    intros [|]; constructor; reflexivity.
  Qed.

  Global Instance module_layer_rel_refl D RF RV:
    (forall i, Reflexive (RF i)) ->
    (forall i, Reflexive (RV i)) ->
    Reflexive (module_layer_rel D D RF RV).
  Proof.
    intros HRF HRV [M L] i.
    split; reflexivity.
  Qed.

  Lemma make_globalenv_stencil_matches D ML ge:
    make_globalenv D ML = OK ge ->
    stencil_matches ge.
  Proof.
    intros Hge.
    eapply genv_le_stencil_matches_l.
    eapply (make_globalenv_rel_mprc D (mprc_empty D)); eauto.
    unfold mprc_funrel, mprc_varrel.
    reflexivity.
  Qed.

  Hint Resolve make_globalenv_stencil_matches.

  (** * Properties relating module-layer pairs with their global environments *)

  (** ** Intensional properties about single-binding module-layer pairs *)

  (** Those are only used in [MakeProgramInv] and we may want to
    relocate them there. *)

  Lemma make_globalenv_external {D} (i: ident) (σ: primsem D) ge:
    make_globalenv D (∅, i ↦ σ) = ret ge ->
    exists σdef b,
      make_external D i σ = OK σdef /\
      Genv.find_symbol ge i = Some b /\
      Genv.find_funct_ptr ge b = Some σdef.
  Proof.
    intros Hge.
    use_mprc Hge (mprc_prim D i σ); eauto.
  Qed.

  Lemma make_globalenv_internal {D} (i: ident) (f: Fm) ge:
    make_globalenv D (i ↦ f, ∅) = ret ge ->
    exists fdef b,
      make_internal f = OK fdef /\
      Genv.find_symbol ge i = Some b /\
      Genv.find_funct_ptr ge b = Some fdef.
  Proof.
    intros Hge.
    use_mprc Hge (mprc_fun D i f); eauto.
  Qed.

  Lemma make_globalenv_module_globvar {D} (i: ident) (τ: globvar Vm) ge:
    make_globalenv D (i ↦ τ, ∅) = ret ge ->
    exists vdef b,
      make_varinfo τ = OK vdef /\
      Genv.find_symbol ge i = Some b /\
      Genv.find_var_info ge b = Some vdef.
  Proof.
    intros Hge.
    use_mprc Hge (mprc_var D i τ); eauto.
  Qed.

  Lemma make_globalenv_layer_globvar {D} (i: ident) (τ: globvar Vm) ge:
    make_globalenv D (∅, i ↦ τ) = ret ge ->
    exists vdef b,
      make_varinfo τ = OK vdef /\
      Genv.find_symbol ge i = Some b /\
      Genv.find_var_info ge b = Some vdef.
  Proof.
    intros Hge.
    use_mprc Hge (mprc_var D i τ); eauto.
  Qed.

  (** ** Extensional properties *)

  (** Those are used by legacy code, and we may want to remove them if
    they end up unused after we migrate everything to use the
    relational property of [make_program] instead of painstakingly
    moving back-and-forth between the representations of modules and
    their global environments. *)

  Lemma make_globalenv_get_module_function {D} M L ge i fi f:
    make_globalenv D (M, L) = OK ge ->
    get_module_function i M = OK (Some fi) ->
    make_internal fi = OK f ->
    exists b,
      Genv.find_symbol ge i = Some b /\
      Genv.find_funct_ptr ge b = Some f.
  Proof.
    intros Hge HMi Hfi.
    use_mprc Hge (mprc_fun D i fi); eauto.
    destruct HR as (f' & b & Hf' & HR).
    replace f with f' by congruence.
    eauto.
  Qed.

  Lemma make_globalenv_get_module_variable {D} M L ge i vi v:
    make_globalenv D (M, L) = OK ge ->
    get_module_variable i M = OK (Some vi) ->
    make_varinfo vi = OK v ->
    exists b,
      Genv.find_symbol ge i = Some b /\
      Genv.find_var_info ge b = Some v.
  Proof.
    intros Hge HMi Hvi.
    use_mprc Hge (mprc_var D i vi); eauto.
    destruct HR as (v' & b & Hv' & Hb & Hbv').
    assert (v' = v) by congruence; subst.
    eauto.
  Qed.

  Lemma make_globalenv_get_layer_primitive {D} M L ge i fe f:
    make_globalenv D (M, L) = OK ge ->
    get_layer_primitive i L = OK (Some fe) ->
    make_external D i fe = OK f ->
    exists b,
      Genv.find_symbol ge i = Some b /\
      Genv.find_funct_ptr ge b = Some f.
  Proof.
    intros Hge HMi Hfe.
    use_mprc Hge (mprc_prim D i fe); eauto.
    destruct HR as (f' & b & Hf' & HR).
    replace f with f' by congruence.
    eauto.
  Qed.

  Lemma make_globalenv_get_layer_globalvar {D} M L ge i vi v:
    make_globalenv D (M, L) = OK ge ->
    get_layer_globalvar i L = OK (Some vi) ->
    make_varinfo vi = OK v ->
    exists b,
      Genv.find_symbol ge i = Some b /\
      Genv.find_var_info ge b = Some v.
  Proof.
    intros Hge HMi Hvi.
    use_mprc Hge (mprc_var D i vi); eauto.
    destruct HR as (v' & b & Hv' & Hb & Hbv').
    assert (v' = v) by congruence; subst.
    eauto.
  Qed.

  (** ** Consequences of single hypotheses *)

  Lemma genv_find_symbol_glob_threshold {F V} (ge: Genv.t F V) i b:
    stencil_matches ge ->
    Genv.find_symbol ge i = Some b ->
    (i < glob_threshold)%positive.
  Proof.
    intros Hge.
    rewrite stencil_matches_symbols by eauto.
    Local Transparent find_symbol.
    unfold find_symbol, find_symbol_upto.
    destruct (decide (i < glob_threshold)%positive).
    - tauto.
    - discriminate.
  Qed.

  Hint Resolve genv_find_symbol_glob_threshold.
  Hint Extern 1 (isOK _) => eexists.

  (** * Alternative monotonicity theorems *)

  (** The specification of [make_program] is a very general relational
    property, however prior to this we were already using simpler
    monotonicity properties to characterize some aspects of
    [make_program]. Here we prove those properties for backward
    compatibility. We will want to remove those eventually. *)

  Lemma module_layer_rel_intro:
    forall (D1 D2: layerdata)
      (ML1: module * layer D1)
      (ML2: module * layer D2)
      (R: simrel D1 D2)
      (LESIM: ( le * sim R)%rel ML1 ML2),
      module_layer_rel D1 D2 (fun _ => option_le (eq + sim R)) (fun _ => option_le eq) ML1 ML2.
  Proof.
    intros D1 D2 (M1 & L1) (M2 & L2) R (Hle & Hsim); simpl in *.
    split.
    - unfold get_module_layer_function; simpl.
      repeat match goal with
             | |- res_le _ (res_option_inj ?a ?b) _ =>
               let A := fresh "A" in
               let f := fresh "f" in
               let msg := fresh "msg" in
               destruct a as [[f|]|msg] eqn:A; simpl;
                 let B := fresh "B" in
                 let v := fresh "v" in
                 let msg := fresh "msg" in
                 destruct b as [[v|]|msg] eqn:B; simpl
             | H: le ?M1 ?M2, A: get_module_function ?i ?M1 = _ |- _
               =>
               generalize (get_module_function_monotonic i _ _ H); rewrite A;
                 let C := fresh "C" in
                 intro C; inv C; revert A
             | H: sim ?R ?L1 ?L2, A: get_layer_primitive ?i ?L1 = _ |- _
               =>
               generalize (get_layer_primitive_sim_monotonic _ _ R i _ _ H); rewrite A;
                 let C := fresh "C" in
                 intro C; inv C; revert A
             | H: option_le _ (Some _) _ |- _ => inv H
             | |- _ => simpl; repeat constructor
             end; intros; repeat rstep.
      + destruct y0; repeat constructor.
      + destruct y; repeat constructor. auto.
      + destruct y; repeat constructor.
      + destruct y; repeat constructor.
    - unfold get_module_layer_variable; simpl.
      repeat match goal with
             | |- res_le _ (_ (get_module_variable ?i ?M1) ?b) _ =>
               let A := fresh "A" in
               let f := fresh "f" in
               let msg := fresh "msg" in
               destruct (get_module_variable i M1) as [[f|]|msg] eqn:A; simpl;
                 let B := fresh "B" in
                 let v := fresh "v" in
                 let msg := fresh "msg" in
                 destruct b as [[v|]|msg] eqn:B; simpl
             | H: le ?M1 ?M2, A: get_module_variable ?i ?M1 = _ |- _
               =>
               generalize (get_module_variable_monotonic i _ _ H); rewrite A;
                 let C := fresh "C" in
                 intro C; inv C; revert A
             | H: sim ?R ?L1 ?L2, A: get_layer_globalvar ?i ?L1 = _ |- _
               =>
               generalize (get_layer_globalvar_sim_monotonic _ _ R i _ _ H); rewrite A;
                 let C := fresh "C" in
                 intro C; inv C; revert A
             | H: option_le _ (Some _) _ |- _ => inv H
             end; intros; repeat rstep.
  Qed.

  Global Instance make_program_monotonic:
    Monotonic
      make_program
      (forallr -, (≤) * (≤) ++> res_le (program_le (fun _ => eq))).
  Proof.
    intros D ML1 ML2 HML.
    unfold program_le.
    assert
      ((- ==> subrel)%rel
         (fundef_rel D D (fun i => option_le (eq + sim id)))
         (fun i => option_le eq)).
    {
      intros i x y Hxy.
      destruct Hxy as [fm1 fp1 Hf1 fm2 fp2 Hf2 Hfm].
      destruct Hf1, Hf2; inversion Hfm; constructor; subst.
      destruct H3; try congruence.
      unfold match_fundef in *; simpl in *.
      pose proof (make_external_monotonic i i eq_refl _ _ H1) as Hme.
      destruct Hme; congruence.
    }
    assert
      ((- ==> subrel)%rel
         (vardef_rel (fun i => option_le eq))
         (fun i => option_le eq)).
    {
      intros i x y Hxy.
      destruct Hxy as [vm1 vp1 Hv1 vm2 vp2 Hv2 Hvm].
      + destruct Hv1, Hv2; inversion Hvm; constructor; subst.
        unfold match_vardef in *; simpl in *.
        congruence.
    }
    pose (subrel_at := fun A B (R1 R2: rel A B) (HR: subrel R1 R2) x y (H: R1 x y) => HR x y H).
    eapply @subrel_at.
    - eapply res_le_monotonic.
      eapply program_subrel;
      eassumption.
    - assert
        (forall i,
           Monotonic
             (make_fundef D i)
             (option_le (eq + sim id) @@ (Some) ++> impl @@ (isError))).
      {
        intros i f1 f2 Hf.
        inversion Hf; clear Hf; subst.
        unfold make_fundef.
        repeat rstep.
        + subst.
          reflexivity.
        + eapply @make_external_monotonic; eauto. (* ?? *)
      }
      assert
        (Monotonic make_varinfo (option_le eq @@ (Some) ++> impl @@ (isError))).
      {
        intros v1 v2 Hv.
        inversion Hv; clear Hv; subst.
        reflexivity.
      }
      eapply make_program_rel. (** FIXME: monotonicity should work *)
      + typeclasses eauto.
      + apply module_layer_rel_intro; auto.
  Qed.

  Global Instance make_program_monotonic_params:
    Params (@make_program) 2.

  Global Instance make_globalenv_monotonic:
    Monotonic
      make_globalenv
      (forallr -, (≤) * (≤) ++> res_le (genv_le (fun _ => eq))).
  Proof.
    unfold make_globalenv, ret; simpl.
    rauto.
  Qed.

  Global Instance make_globalenv_monotonic_params:
    Params (@make_globalenv) 2.

  Global Instance make_program_sim_monotonic:
    Monotonic
      (fun D => make_external D)
      (forallr R, - ==> sim R ++> res_le eq) ->
    Monotonic
      (fun D => make_program D)
      (forallr R, (≤) * sim R ++> res_le (program_le (fun _ => eq))).
  Proof.
    intros Hme D1 D2 R ML1 ML2 HML.
    unfold program_le.
    assert
      ((- ==> subrel)%rel
         (fundef_rel D1 D2 (fun i => option_le (eq + sim R)))
         (fun i => option_le eq)).
    {
      intros i x y Hxy.
      destruct Hxy as [fm1 fp1 Hf1 fm2 fp2 Hf2 Hfm].
      destruct Hf1, Hf2; inversion Hfm; constructor; subst.
      destruct H3; unfold match_fundef in *; simpl in *; try congruence.
      pose proof (Hme D1 D2 R i _ _ H1) as Hme'.
      simpl in *.
      destruct Hme'; congruence.
    }
    assert
      ((- ==> subrel)%rel
         (vardef_rel (fun i => option_le eq))
         (fun i => option_le eq)).
    {
      intros i x y Hxy.
      destruct Hxy as [vm1 vp1 Hv1 vm2 vp2 Hv2 Hvm].
      + destruct Hv1, Hv2; inversion Hvm; constructor; subst.
        unfold match_vardef in *; simpl in *.
        congruence.
    }
    pose (subrel_at := fun A B (R1 R2: rel A B) (HR: subrel R1 R2) x y (H: R1 x y) => HR x y H).
    eapply @subrel_at.
    - eapply res_le_monotonic.
      eapply program_subrel; eassumption.
    - assert
        (forall i,
           Related
             (make_fundef D1 i)
             (make_fundef D2 i)
             (option_le (eq + sim R) @@ (Some) ++> impl @@ (isError))).
      {
        intros i f1 f2 Hf.
        inversion Hf; clear Hf; subst.
        unfold make_fundef.
        repeat rstep.
        + subst.
          reflexivity.
        + eapply Hme; eauto.
      }
      assert
        (Monotonic make_varinfo (option_le eq @@ (Some) ++> impl @@ (isError))).
      {
        intros v1 v2 Hv.
        inversion Hv; clear Hv; subst.
        reflexivity.
      }
      eapply make_program_rel. (** FIXME: monotonicity should work *)
      + typeclasses eauto.
      + apply module_layer_rel_intro; auto.
  Qed.

  (** * Other global properties *)

  Lemma make_program_layer_ok {D} M L:
    isOK (make_program D (M, L)) ->
    LayerOK L.
  Proof.
    intros [p Hp] i.
    split.
    - destruct (make_program_noconflict D M L p i Hp); eauto.
    - destruct (make_program_noconflict D M L p i Hp); eauto.
    - destruct (make_program_noconflict D M L p i Hp); eauto.
  Qed.

  Lemma make_program_module_ok {D} M L:
    isOK (make_program D (M, L)) ->
    ModuleOK M.
  Proof.
    intros [p Hp] i.
    split.
    - destruct (make_program_noconflict D M L p i Hp); eauto.
    - destruct (make_program_noconflict D M L p i Hp); eauto.
    - destruct (make_program_noconflict D M L p i Hp); eauto.
  Qed.

  Lemma make_program_module_layer_disjoint {D} M L:
    isOK (make_program D (M, L)) ->
    module_layer_disjoint M L.
  Proof.
    intros [p Hp] i.
    apply (make_program_noconflict D M L p i Hp).
  Qed.

  (** Our specification is probably not sufficient to prove
    [make_program_exists] below, but it should be possible to replace
    uses of that lemma.

      <<<
      make_program_exists {D} (L: _ D) M:
        LayerOK L ->
        ModuleOK M ->
        (forall i fe, get_layer_primitive i L = OK (Some fe) ->
                      isOK (make_external D i fe) /\
                      isOKNone (get_module_function i M) /\
                      isOKNone (get_module_variable i M) /\
                      (i < glob_threshold)%positive) ->
        (forall i fi, get_module_function i M = OK (Some fi) ->
                      isOK (make_internal fi) /\
                      isOKNone (get_layer_primitive i L) /\
                      isOKNone (get_layer_globalvar i L) /\
                      (i < glob_threshold)%positive) ->
        (forall i v, get_layer_globalvar i L = OK (Some v) ->
                     isOKNone (get_module_function i M) /\
                     isOKNone (get_module_variable i M) /\
                     (i < glob_threshold)%positive) ->
        (forall i v, get_module_variable i M = OK (Some v) ->
                     isOKNone (get_layer_primitive i L) /\
                     isOKNone (get_layer_globalvar i L) /\
                     (i < glob_threshold)%positive) ->
        isOK (make_program D (M, L))
      >>>
  *)

  (** We could add this one to the spec, but actually it should be
    enough that the [main] of two programs are equal, we don't need to
    know the specific identifier.

      <<<
      make_program_prog_main
        {D} (L: layer D)
        (M: module) (p: _)
        (prog: make_program D (M, L) = OK p)
      :
        (prog_main p) = xH;
      >>>
   *)
End MAKE_PROGRAM_FACTS.
