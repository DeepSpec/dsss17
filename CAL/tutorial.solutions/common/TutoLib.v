(**
 * TutoLib.v
 *
 * A library of tactics and lemmas used in the layer tutorial.
 *)

(** Compcert helper lib *)
Require Import Coqlib.
Require Import Maps.
(** Compcert types and semantics *)
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Clight.
Require Import Ctypes.
Require Import Cop.
Require Import Smallstep.
(** CertiKOS layer library *)
Require Import Semantics.
Require Import Structures.
Require Import PTreeLayers.
Require Import PTreeSemantics.
Require Import GenSem.
Require Import CGenSem.
Require Import CPrimitives.
Require Import SimulationRelation.
Require Import SimrelInvariant.
Require Import LayerLogicImpl.
Require Import PseudoJoinReflection.
Require Import ClightModules.
Require Import ClightXSemantics.
Require Import AbstractData.
Require Import AbstractionRelation.

(** Notations for some Compcert types *)
Notation tint := (Tint I32 Signed noattr).
Notation tuint := (Tint I32 Unsigned noattr).
Notation tvoid := (Tvoid).
Notation tptr := (fun (t: type) => Tpointer t noattr).
Notation tarray := (fun (t: type) (sz: Z) => Tarray t sz noattr).

(** ** Helper tactics *)

(** *** Code and Refinement Proof Helpers *)

Ltac cprimitive_sim_tac :=
  match goal with
  | |- cprimitive_sim _ _ _ _ _ =>
      constructor;
      [intros w sg (xargs, xmem) (yargs, ymem) (ArgsRel & MemRel) xres CStep |
       try now apply incl_refl]
  | |- _ => fail
  end.

Ltac find_prim gv :=
  match goal with
  | [H: MakeProgramSpec.make_globalenv _ _ = _ |- _] =>
      pose proof H as H';
      eapply MakeProgramFacts.make_globalenv_get_layer_primitive with (i := gv) in H';
      try reflexivity;
      match goal with
      | [H1: exists _,
          Genv.find_symbol _ gv = Some _ /\
          Genv.find_funct_ptr _ _ = Some _ |- _] =>
            let b := fresh "b_" gv in
            let Hb := fresh "Hb_" gv in
            let Hfp := fresh "Hfp_" gv in
            destruct H1 as (b & Hb & Hfp)
      | _ => idtac
      end
  end.

Ltac eval_expr_tac :=
  repeat lazymatch goal with
  | |- Genv.find_funct _ _ = _ =>
      rewrite Genv.find_funct_find_funct_ptr; eassumption
  | |- external_call ?ef ?t ?vs ?m ?tr ?v ?m' =>
      constructor; [eapply MakeProgramFacts.make_globalenv_stencil_matches; eauto |];
      repeat (esplit; cbn); auto
  | |- eval_lvalue ?t ?env ?le ?ml ?ty ?ml' ?ofs =>
      match ty with
      | Evar ?gc ?typ => eapply eval_Evar_global;
                         [try now apply PTree.gempty |
                          (eassumption ||
                           rewrite stencil_matches_symbols; eauto;
                           eapply MakeProgramFacts.make_globalenv_stencil_matches; eauto)]
      | Ederef ?e1 ?typ => eapply eval_Ederef
      | Efield ?e1 ?fid ?fty => eapply eval_Efield_struct;
                                [eval_expr_tac |
                                 reflexivity |
                                 idtac |
                                 idtac]
      end
  | |- eval_expr ?t ?env ?le ?ml (Ebinop ?op ?e1 ?e2 ?type) ?v =>
      eapply eval_Ebinop; [eval_expr_tac | eval_expr_tac | try reflexivity]
  | |- eval_expr ?t ?env ?le ?ml (Etempvar ?id ?typ) ?v =>
      eapply eval_Etempvar; try reflexivity
  | |- eval_expr ?t ?env ?le ?ml (Ecast ?e ?typ) ?v =>
      eapply eval_Ecast; [eval_expr_tac | try reflexivity]
  | |- eval_expr ?t ?env ?le ?ml ?ty ?v =>
      match ty with
      | Evar ?gv ?typ => eapply eval_Elvalue
      | Ederef ?e1 ?typ => eapply eval_Elvalue
      | Efield ?e ?id ?typ => eapply eval_Elvalue
      | Econst_int ?i ?typ => econstructor
      | Econst_long ?l ?typ => econstructor
      | Econst_single ?f ?typ => econstructor
      | Econst_float ?f ?typ => econstructor
      | Esizeof ?typ ?ty' => econstructor
      | Ealignof ?typ ?ty' => econstructor
      end
  | |- eval_exprlist ?t ?env ?le ?m nil ?ts ?vs =>
      econstructor
  | |- eval_exprlist ?t ?env ?le ?m ?es ?ts ?vs =>
      econstructor; [eval_expr_tac | try reflexivity | eval_expr_tac]
  | |- deref_loc ?ty ?m ?b ?ofs ?v =>
      match goal with
      | |- deref_loc (Tarray _ _ _) _ _ _ _ => now eapply deref_loc_reference
      | |- deref_loc (Tfunction _ _ _) _ _ _ _ => now eapply deref_loc_reference
      | |- deref_loc (Tstruct _ _) _ _ _ _ => now eapply deref_loc_copy
      | |- deref_loc (Tunion _ _) _ _ _ _ => now eapply deref_loc_copy
      | |- deref_loc (typeof _) _ _ _ _ => progress cbn
      | |- deref_loc _ _ _ _ _ => eapply deref_loc_value; [easy |]
      end
  | |- assign_loc ?ge ?ty ?m ?b ?ofs ?v ?m' =>
      match ty with
      | Vptr ?b' ?ofs' => eapply assign_loc_copy
      | _ => econstructor; cbn; try (reflexivity || now eauto)
      end
  end.

Ltac step_tac :=
  match goal with
  | |- star _ ?t (Returnstate _ _ _) _ (Returnstate _ _ _) => apply star_refl
  | |- star _ _ _ _ _ =>
      eapply star_left; [econstructor; (reflexivity || eval_expr_tac; cbn; try now eauto || idtac) |
                         idtac |
                         traceEq]
  end.

Ltac cprim_step :=
  constructor; [auto | eapply plus_left];
  [repeat econstructor; try decision |
   idtac |
   traceEq].

Ltac mkcprim_tac step sg :=
  refine (mkcprimitive _ step sg _);
  intros ? ? ? ? Hstep; inv Hstep; easy.

Ltac inv_abrel_init_props :=
  repeat match goal with
  | AIP : abrel_init_props ?m ?glbl |- _ =>
      destruct AIP as ((?b & ?aip_find_symbol & ?aip_load & ?aip_perm) & ?AIP')
  | AIP : abrel_init_props ?m nil |- _ => clear AIP
  end.

(** *** General Helpers *)

Ltac destr :=
  match goal with
  | |- context [match ?A with _ => _ end] => destruct A eqn:?; cbn in *
  | |- context [if ?A then _ else _] => destruct A eqn:?; cbn in *
  end.

Ltac destr_in H :=
  match type of H with
  | context [match ?A with _ => _ end] => destruct A eqn:?; cbn in *
  | context [if ?A then _ else _] => destruct A eqn:?; cbn in *
  end.

Ltac destr_eq x y :=
  let Heq := fresh "Heq" in
  let Hneq := fresh "Hneq" in
  destruct (decide (x = y)) as [Heq | Hneq].

Section LayerLemmas.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.
  Context `{ce: ClightCompositeEnv}.

  (** Lemmas about lifting simulations from cprimitive to clayer *)
  Lemma cprimitive_sim_union:
    forall D R cprim c1 c2,
      cprimitive_sim D D R cprim c1 ->
      cprimitive_sim D D R cprim (cprimitive_union D c1 c2).
  Proof.
    intros D R cprim c1 c2 CS.
    inv CS.
    constructor.
    - repeat red; simpl; intros.
      specialize (cprimitive_sim_step p a x y H0 a0 H1).
      destruct cprimitive_sim_step as (b & STEP & REL).
      exists b; split; auto.
    - simpl.
      apply incl_appl. auto.
  Qed.

  Theorem cprimitive_correct :
    forall (D: layerdata) i (cprim : cprimitive D) (cimpl : function) (L: clayer D) R
      (CSIM: forall t,
          MakeProgramSpec.make_globalenv D (i ↦ cimpl, L) = OK t ->
          cprimitive_sim D D R cprim (clight_cprimitive D L (Build_genv t ce) cimpl)),
      sim R (i ↦ cprim) ( 〚 i ↦ cimpl 〛 L).
  Proof.
    intros.
    apply ptree_layer_pointwise_sim.
    - intros.
      destruct (ident_eq i0 i); subst.
      +
        assert (res_le (option_le (sim R))
                       (get_layer_primitive i (i ↦ cprim))
                       (semof_function D (i ↦ cimpl, L) i (get_module_function i (i ↦ cimpl)) ⊕ get_layer_primitive i L)).
        {
          get_layer_normalize.
          get_module_normalize.
          unfold semof_function.
          monad_norm.
          simpl.
          destruct (MakeProgramSpec.make_globalenv D (i ↦ cimpl, L)) eqn:?;
                   simpl; monad_norm; try constructor.
          destruct (get_layer_primitive i L); try constructor.
          destruct o; try constructor; constructor; auto.
          apply cprimitive_sim_union. auto.
        }
        setoid_rewrite <- ptree_get_semof_primitive in H0. auto.
      +
        assert (res_le (option_le (sim R))
                       (get_layer_primitive i0 (i ↦ cprim))
                       (semof_function D (i ↦ cimpl, L) i0 (get_module_function i0 (i ↦ cimpl)) ⊕ get_layer_primitive i0 L)).
        {
          get_module_normalize; get_layer_normalize.
          simpl.
          destruct (get_layer_primitive i0 L) eqn:?; try constructor.
          destruct o; repeat constructor.
        }
        setoid_rewrite <- ptree_get_semof_primitive in H0. auto.
    - intros.
      get_layer_normalize.
      assert (res_le (option_le eq)
                     (OK None)
                     (get_module_variable i0 (i ↦ cimpl) ⊕ get_layer_globalvar i0 L)).
      {
        get_module_normalize; get_layer_normalize.
        destruct (get_layer_globalvar i0 L); simpl; try constructor.
        destruct o; simpl; repeat constructor.
      }
      setoid_rewrite <- (ptree_get_semof_globalvar) in H0. auto.
  Qed.

  Theorem layer_sim :
    forall D1 D2 (HSpec: cprimitive D1) (CPrim: cprimitive D2) (i: ident)
      (R: simrel D1 D2)
      (SIM: sim R HSpec CPrim),
      sim R
          ((i ↦ HSpec) : clayer D1)
          ((i ↦ CPrim) : clayer D2).
  Proof.
    intros.
    apply ptree_layer_pointwise_sim.
    - intros.
      destruct (ident_eq i0 i); subst.
      + get_layer_normalize. constructor. constructor.
        auto.
      + get_layer_normalize. constructor. constructor.
    - intros; get_layer_normalize.
      constructor. constructor.
  Qed.

  Lemma layer_pres_inv : forall D σ M (L: clayer D),
    ForallPrimitive D (CPrimitivePreservesInvariant D) L ->
    L ⊢ (id, M) : σ ->
    L ⊢ (inv, M) : σ.
  Proof.
    intros ? ? ? ? Hinv Hsim.
    apply cprimitive_invariant_inv in Hinv.
    apply logic_intro. apply logic_elim in Hsim.
    ehtransitivity; eauto.
    rauto.
  Qed.

  (** Needed in function_entry2 to show the lists of parameters and temps are
     disjoint *)
  Global Instance decide_disjoint `{Heq: EqDec} : forall (xs ys: list A),
    Decision (list_disjoint xs ys) := list_disjoint_dec Heq.

  (** Needed to use pjr in linking *)
  Global Instance pj_clayer {D} : PseudoJoin (clayer D) ∅.
  Proof. constructor; typeclasses eauto. Qed.

  (** Clight functions preserve the layer invariant if all primitives at
    that layer preserve it. *)
  Lemma clight_prim_inv : forall D (L: clayer D) i impl t,
    MakeProgramSpec.make_globalenv D (i ↦ impl, L) = OK t ->
    let spec := clight_cprimitive D L {| genv_genv := t; genv_cenv := ce |} impl in
    get_layer_primitive i L = OK None ->
    sim inv (〚 i ↦ impl 〛L) (〚 i ↦ impl 〛L) ->
    cprimitive_sim D D inv spec spec.
  Proof.
    intros until t; intros Hge ? Hnin Hsim; subst spec.
    pose proof Hge as Hge'.
    unfold MakeProgramSpec.make_globalenv in Hge'.
    inv_monad Hge'; subst.
    rename H1 into Hprog.
    apply ptree_layer_sim_pointwise in Hsim.
    destruct Hsim as (Hle & _).
    specialize Hle with i.
    rewrite get_semof_primitive in Hle.
    get_module_normalize_in Hle.
    inv_monad Hle.
    - rewrite <- H0 in H1; inv H1.
      destruct (get_layer_primitive i L); inv Hnin.
      destruct (semof_function D (_, L) i _) eqn:?; inv H0.
      cbn in Heqr.
      rewrite Hprog in Heqr.
      inv_monad Heqr.
      inv H3. inv H2.
      auto.
    - destruct (get_layer_primitive i L); inv Hnin.
      destruct (semof_function D (_, L) i _) eqn:?; inv H2.
      + destruct o; inv H1.
      + cbn in Heqr.
        rewrite Hprog in Heqr.
        inv_monad Heqr.
  Qed.

  Lemma clight_prim_pres_inv : forall D prim impl L t,
    get_layer_primitive prim L = OK None ->
    MakeProgramSpec.make_globalenv D (prim ↦ impl, L) = OK t ->
    ForallPrimitive D (CPrimitivePreservesInvariant D) L ->
    CPrimitivePreservesInvariant D
      (clight_cprimitive D L {| genv_genv := t; genv_cenv := ce |} impl).
  Proof.
    intros until t; intros Hnin Hge Hpres_inv.
    apply inv_cprimitive_inv.
    apply clight_prim_inv with prim; auto.
    apply cprimitive_invariant_inv in Hpres_inv.
    cut (sim inv L L); auto; intros.
    repeat rstep.
  Qed.

  (** Convenience lemmas to change goals of the form L1 ⊢ (R, M) : L2 to an
    explicit simulation diagram *)
  Lemma link_to_diag_code_id : forall D (L: clayer D) prim spec (impl: function)
      (Hdiag: forall (t: Genv.t Clight.fundef type)
                     (Hge: MakeProgramSpec.make_globalenv D (prim ↦ impl, L) = OK t)
                     (sg: csignature) (args: list val) (m: mem) (d: D)
                     (res: val) (m': mem) (d': D)
         (CStep: cprimitive_step D spec sg (args, (m, d)) (res, (m', d'))),
         cprimitive_step D
           (clight_cprimitive D L {| genv_genv := t; genv_cenv := ce |} impl)
           sg (args, (m, d)) (res, (m', d')))
      (Hincl: incl (cprimitive_csig D spec) (clight_cprimitive_csig impl :: nil)),
    L ⊢ (id, prim ↦ impl) : (prim ↦ spec).
  Proof.
    intros.
    apply logic_intro. apply cprimitive_correct; intros ? Hge.
    apply cprimitive_sim_id_intro; auto.
    intros sg (args & m & d) (res & m' & d') step.
    auto.
  Qed.

  Lemma link_to_diag_code_inv : forall D (L: clayer D) prim spec (impl: function)
      (Hlayer_inv: ForallPrimitive D (CPrimitivePreservesInvariant D) L)
      (Hprim_not_in: get_layer_primitive prim L = OK None)
      (Hdiag: forall (t: Genv.t Clight.fundef type)
                     (Hge: MakeProgramSpec.make_globalenv D (prim ↦ impl, L) = OK t)
                     (sg: csignature) (args: list val) (m: mem) (d: D)
                     (res: val) (m': mem) (d': D)
                (Hmatch: cprimitive_inv_init_state D args m d)
                (CStep: cprimitive_step D spec sg (args, (m, d)) (res, (m', d'))),
                cprimitive_step D
                  (clight_cprimitive D L {| genv_genv := t; genv_cenv := ce |} impl)
                  sg (args, (m, d)) (res, (m', d')))
      (Hincl: incl (cprimitive_csig D spec) (clight_cprimitive_csig impl :: nil)),
    L ⊢ (inv, prim ↦ impl) : (prim ↦ spec).
  Proof.
    intros.
    apply logic_intro. apply cprimitive_correct; intros ? Hge.
    apply cprimitive_sim_inv_intro; auto.
    eapply clight_prim_pres_inv; eauto.
    intros sg args mem data (res & mem' & data') xmatch step.
    auto.
  Qed.

  Lemma link_to_diag_refine_R : forall (Dlow Dhigh: layerdata) R prim lspec hspec
      (Hdiag: forall (sg: csignature) (xargs yargs: list val) (xm ym: mem)
                     (xd: Dhigh) (yd: Dlow) (xres: val)
                     (xm': mem) (xd': Dhigh)
         (ArgsRel: list_rel (match_val (abrel_simrel Dhigh Dlow R) tt) xargs yargs)
         (MemExtends: Mem.extends xm ym)
         (MemRel: abrel_match_mem Dhigh Dlow R xm xd ym yd)
         (CStep: cprimitive_step Dhigh hspec sg (xargs, (xm, xd)) (xres, (xm', xd'))),
         exists yres ym' yd',
           cprimitive_step Dlow lspec sg (yargs, (ym, yd)) (yres, (ym', yd')) /\
           cprimitive_match_final_state _ _ (abrel_simrel Dhigh Dlow R)
                                        tt (xres, (xm', xd')) (yres, (ym', yd')))
      (Hincl: incl (cprimitive_csig Dhigh hspec) (cprimitive_csig Dlow lspec)),
    (prim ↦ lspec) ⊢ (abrel_simrel Dhigh Dlow R, ∅) : (prim ↦ hspec).
  Proof.
    intros.
    eapply conseq_le_sim; [constructor | apply empty_rule | reflexivity | apply layer_sim].
    constructor; auto.
    repeat red.
    intros w sg (xargs & xmem & xdata) (yargs & ymem & ydata)
           xmatch (res & xmem' & xdata') step.
    destruct w. destruct xmatch as (ArgsMatch & MemExtend & MemMatch).
    cbn in ArgsMatch, MemExtend, MemMatch.
    eapply Hdiag in step; eauto.
    destruct step as (yres & ymem' & ydata' & ystep & ymatch).
    exists (yres, (ymem', ydata')); split; eauto.
    exists tt. split; repeat rstep.
  Qed.

  Lemma link_to_diag_refine_inv : forall (Dlow Dhigh: layerdata) R prim lspec hspec
      (Hinv_high: CPrimitivePreservesInvariant Dhigh hspec)
      (Hinv_low: CPrimitivePreservesInvariant Dlow lspec)
      (Hdiag: forall (sg: csignature) (xargs yargs: list val) (xm ym: mem)
                     (xd: Dhigh) (yd: Dlow) (xres: val)
                     (xm': mem) (xd': Dhigh)
         (ArgsRel: list_rel (match_val (abrel_simrel Dhigh Dlow R) tt) xargs yargs)
         (MemExtends: Mem.extends xm ym)
         (MemRel: abrel_match_mem Dhigh Dlow R xm xd ym yd)
         (InvHi: cprimitive_inv_init_state Dhigh xargs xm xd)
         (InvLo: cprimitive_inv_init_state Dlow yargs ym yd)
         (CStep: cprimitive_step Dhigh hspec sg (xargs, (xm, xd)) (xres, (xm', xd'))),
         exists yres ym' yd',
           cprimitive_step Dlow lspec sg (yargs, (ym, yd)) (yres, (ym', yd')) /\
           cprimitive_match_final_state _ _ (abrel_simrel Dhigh Dlow R)
                                        tt (xres, (xm', xd')) (yres, (ym', yd')))
      (Hincl: incl (cprimitive_csig Dhigh hspec) (cprimitive_csig Dlow lspec)),
    (prim ↦ lspec) ⊢ (inv ∘ abrel_simrel Dhigh Dlow R ∘ inv, ∅) : (prim ↦ hspec).
  Proof.
    intros.
    eapply conseq_le_sim; [constructor | apply empty_rule | reflexivity | apply layer_sim].
    apply cprimitive_sim_wrapinv_intro; auto.
    repeat red.
    intros w sg ? ? xmatch (res & xmem' & xdata') step.
    destruct w. destruct xmatch. rename H0 into xinv, H1 into yinv, H2 into xmatch.
    destruct xmatch as (ArgsMatch & MemExtend & MemMatch).
    cbn in ArgsMatch, MemExtend, MemMatch.
    eapply Hdiag in step; eauto.
    destruct step as (yres & ymem' & ydata' & ystep & ymatch).
    exists (yres, (ymem', ydata')); split; eauto.
    exists tt. split; repeat rstep.
  Qed.

End LayerLemmas.

(** Tactics to apply the appropriate simulation diagram lemma *)

Ltac code_proof_id := apply link_to_diag_code_id; intros; [| try apply incl_refl].

Ltac code_proof_inv :=
  apply link_to_diag_code_inv; intros;
  [auto with linking | try decision | | try apply incl_refl].

Ltac code_proof_tac :=
  lazymatch goal with
  | |- ?L1 ⊢ (id, ?M) : ?L2 => code_proof_id
  | |- ?L1 ⊢ (inv, ?M) : ?L2 => code_proof_inv
  end.

Ltac refine_proof_R := apply link_to_diag_refine_R; intros; [| try apply incl_refl].

Ltac refine_proof_inv :=
  apply link_to_diag_refine_inv; intros; try (typeclasses eauto || apply incl_refl).

Ltac refine_proof_tac :=
  lazymatch goal with
  | |- ?L1 ⊢ (inv ∘ ?R ∘ inv, ?M) : ?L2 => refine_proof_inv
  | |- ?L1 ⊢ (?R, ?M) : ?L2 => refine_proof_R
  end.

(** *** Linking Helpers *)

Section LinkingLemmas.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.
  Context `{ce: ClightCompositeEnv}.

  Lemma link_id_R_vsplit : forall Dlow Dhigh M (Llow: clayer Dlow) (Lhigh: clayer Dhigh) R Σ,
    Llow ⊢ (id, M): Σ ->
    Σ ⊢ (R, ∅): Lhigh ->
    Llow ⊢ (R, M) : Lhigh.
  Proof.
    intros.
    apply (vdash_rel_equiv _ _ (id ∘ R)).
    apply cat_compose_id_left.
    apply (vdash_module_le _ _ _ _ _ (M ⊕ ∅)); [constructor | pjr |].
    apply (vcomp_rule _ _ _ _ _ _ Σ); [constructor | |]; auto.
  Qed.

  Lemma link_inv_R_vsplit : forall Dlow Dhigh M (Llow: clayer Dlow) (Lhigh: clayer Dhigh) R Σ,
    Llow ⊢ (inv, M): Σ ->
    Σ ⊢ (inv ∘ R ∘ inv, ∅): Lhigh ->
    Llow ⊢ (inv ∘ R ∘ inv, M) : Lhigh.
  Proof.
    intros.
    apply (vdash_rel_equiv _ _ (inv ∘ (inv ∘ R ∘ inv))).
    rewrite cat_compose_assoc; rewrite cat_compose_assoc.
    cbn. rewrite simrel_compose_inv_inv. reflexivity.
    apply (vdash_module_le _ _ _ _ _ (M ⊕ ∅)); [constructor | pjr |].
    apply (vcomp_rule _ _ _ _ _ _ Σ); [constructor | |]; auto.
  Qed.

  Lemma link_wrapinv : forall Dlow Dhigh M (Llow: clayer Dlow) (Lhigh: clayer Dhigh) R,
    ForallPrimitive _ (CPrimitivePreservesInvariant _) Llow ->
    ForallPrimitive _ (CPrimitivePreservesInvariant _) Lhigh ->
    Llow ⊢ (R, M) : Lhigh ->
    Llow ⊢ (inv ∘ R ∘ inv, M) : Lhigh.
  Proof.
    intros.
    eapply conseq_rule; [constructor | | |];
    try apply cprimitive_invariant_inv; auto.
  Qed.

End LinkingLemmas.

Ltac extract_spec i Σ :=
  let H := fresh "H_" i in
  let spec := fresh i "_σ" in
  assert (H: exists lspec, get_layer_primitive i Σ = OK (Some lspec)) by
    (get_layer_normalize; eexists; reflexivity);
  destruct H as (spec & H);
  get_layer_normalize_in H;
  repeat (rewrite get_layer_primitive_mapsto_other_primitive in H; [| discriminate]);
  cbn in H;
  injection H; clear H; intro H.

Ltac link_solve_code :=
  repeat (apply hcomp_rule; [constructor | |]); eauto with linking.

Ltac link_solve_refine :=
  repeat lazymatch goal with
  | |- ?L1 ⊕ ?L2 ⊢ (?R, ?M ⊕ ∅) : ?L3 ⊕ ?L4 =>
      apply hcomp_rule; [constructor | |]
  | |- ?L1 ⊕ ?L2 ⊢ (?R, ?M) : ?L3 ⊕ ?L4 =>
      apply (vdash_module_le _ _ _ _ _ (∅ ⊕ ∅)); [constructor | reflexivity |]
  | |- ?Σ ⊢ (?R, ?M) : (?i ↦ ?spec) =>
      extract_spec i Σ;
      match goal with
      | spec: cprimitive ?D |- _=>
          apply conseq_le_left with (L1 := (i ↦ spec));
          subst spec;
          [constructor | | pjr]
      end
  | |- ?Σ ⊢ (?R, ?M) : ?L => try unfold L
  end; eauto with linking.

Ltac link_id_R Σ R M L :=
  apply link_id_R_vsplit with Σ;
  try unfold Σ; try unfold L;
  [try link_solve_code | try link_solve_refine].

Ltac link_inv_R Σ R M L :=
  apply link_inv_R_vsplit with Σ;
  try unfold Σ; try unfold L;
  [try link_solve_code | try link_solve_refine].

Ltac link_tac Σ :=
  lazymatch goal with
  | |- ?Llow ⊢ (inv ∘ ?R ∘ inv, ?M) : ?Lhigh => link_inv_R Σ R M Lhigh
  | |- ?Llow ⊢ (?R, ?M) : ?Lhigh => link_id_R Σ R M Lhigh
  end.

(** Hints to help automate linking *)

Hint Resolve layer_pres_inv link_wrapinv : linking.
Hint Extern 1 (sim inv ?L ?L) => apply cprimitive_invariant_inv : linking.
Hint Extern 1 (layer_wf ?L) => constructor : linking.
Hint Extern 10 (?L1 ⊢ (inv ∘ ?R ∘ inv, ∅): ?L2) =>
  apply link_wrapinv; solve [typeclasses eauto | eauto with linking].

Hint Extern 2 (ForallPrimitive _ _ (_ ⊕ _)) =>
  eapply forallprim_oplus_disjoint; [decision | |] : typeclass_instances.

Section MathLemmas.

  Lemma ptrofs_max_val : Ptrofs.max_unsigned = (if Archi.ptr64 then 18446744073709551615 else 4294967295).
  Proof.
    unfold Ptrofs.max_unsigned, Ptrofs.modulus,
           Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
    destruct Archi.ptr64; reflexivity.
  Qed.

  Lemma int_ptrofs_max : Int.max_unsigned <= Ptrofs.max_unsigned.
  Proof.
    rewrite ptrofs_max_val; cbn.
    destruct Archi.ptr64; omega.
  Qed.

End MathLemmas.

Section HelperFunctions.

  (** Copied from mCertiKOSType to reduce the number of dependencies in the
     tutorial *)
  Fixpoint type_of_list_type (params : list type) : typelist :=
    match params with
    | nil => Ctypes.Tnil
    | ty :: rem => Ctypes.Tcons ty (type_of_list_type rem)
    end.

End HelperFunctions.
