Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.lib.Decision.
Require Import coqrel.LogicalRelations.
Require Import liblayers.lib.ExtensionalityAxioms.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Primitives.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import SimulationRelation.
Require Import SimrelInvariant.
Require Import SimClight.
Require Export liblayers.compcertx.CGlobalVars.

Infix "×" := prod_rel (right associativity, at level 45) : signature_scope.

Lemma eqrel_iff {A B} {R S: rel A B}:
  eqrel R S -> forall x y, R x y <-> S x y.
Proof.
  clear.
  firstorder.
Qed.

Lemma iff_eqrel {A B} {R S: rel A B}:
  (forall x y, R x y <-> S x y) ->
  eqrel R S.
Proof.
  clear.
  firstorder.
Qed.

(* To allow using external function properties for external functions
that are not primitives (i.e., that are builtins or CompCert
internals.) *)

(*
Theorem external_call_spec_not_external
        {mem}
        `{memory_model: Mem.MemoryModel mem}
        `{external_calls_ops_x: !CompCertBuiltins.ExternalCallsOpsX mem}
        `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet}
:
  forall ef,
    (forall id sg, ef <> EF_external id sg) ->
    extcall_properties (external_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call, ef_sig. destruct ef.
  edestruct H; eauto.
  (** [CompCertX:test-compcert-param-extcall] We separate [EF_builtin] from [EF_external]. *)
  apply CompCertBuiltins.builtin_functions_properties.
  apply volatile_load_ok.
  apply volatile_store_ok.
  apply volatile_load_global_ok.
  apply volatile_store_global_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
  apply extcall_memcpy_ok.
  apply extcall_annot_ok.
  apply extcall_annot_val_ok.
  constructor; simpl; contradiction.
Qed.
*)

Section CPRIMITIVES.
  Context `{Hmem: BaseMemoryModel}.

  Record cprimitive (D: layerdata) :=
    {
      cprimitive_step:
        csignature -> list val × mwd D -> val × mwd D -> Prop;
      cprimitive_csig:
        list csignature;
      cprimitive_csig_ne:
        cprimitive_csig <> nil;
      cprimitive_step_wt sg sinit v' m' :
        cprimitive_step sg sinit (v', m') ->
        Val.has_type v' (typ_of_type (csig_res sg))
    }.

  Program Definition mkcprimitive D (step: _ -> _ -> _ -> Prop) sg
          (Hwt: forall sg sinit v' m',
                  step sg sinit (v', m') ->
                  Val.has_type v' (typ_of_type (csig_res sg)))
  : cprimitive D :=
    {|
      cprimitive_step := step;
      cprimitive_csig := sg :: nil
    |}.

  Definition cprimitive_match_init_state D1 D2 (R: simrel D1 D2) p :=
    (list_rel (match_val R p) * match_mem R p)%rel.

  Definition cprimitive_match_final_state D1 D2 (R: simrel D1 D2) p :=
    (match_val R p * match_mem R p)%rel.

  Record cprimitive_sim D1 D2 R σ1 σ2 :=
    {
      cprimitive_sim_step p:
        (- ==> cprimitive_match_init_state D1 D2 R p ++>
         set_rel (incr p (cprimitive_match_final_state D1 D2 R p)))%rel
          (cprimitive_step D1 σ1)
          (cprimitive_step D2 σ2);
      cprimitive_sim_csig:
        incl
          (cprimitive_csig D1 σ1)
          (cprimitive_csig D2 σ2)
    }.

  Global Instance cprimitive_sim_proper:
    Monotonic cprimitive_sim (forallr -, forallr -, simrel_equiv ++> subrel).
  Proof.
    repeat red.
    intros D D' R1 R2 H pr pr' H0.
    destruct H as [s H].
    inversion H0.
    constructor; auto.
    repeat red.
    intros p2 sg x y H1 a H2.
    inversion H1.
    assert (cprimitive_match_init_state _ _ R1 (simrel_equiv_bw s p2) x y) as INIT1.
    {
      constructor; auto.
      + eapply list_subrel. apply match_val_simrel_equiv_bw. auto.
      + apply match_mem_simrel_equiv_bw.
        assumption.
    }
    specialize (cprimitive_sim_step0 _ _ _ _ INIT1 _ H2).
    destruct cprimitive_sim_step0 as (b & STEP & FIN1).
    red in FIN1.
    destruct FIN1 as (p1' & INCR1 & FIN1).
    inversion FIN1.
    apply simrel_equiv_le_fw in INCR1.
    esplit.
    split; eauto.
    esplit.
    split; eauto.
    etransitivity. 2: apply INCR1. apply simrel_fw_bw_le.
    econstructor.
    + apply match_val_simrel_equiv_fw.
      assumption.
    + apply match_mem_simrel_equiv_fw.
      assumption.
  Qed.

  Global Instance cprimitive_sim_refl D:
    Reflexive (cprimitive_sim D D simrel_id).
  Proof.
    intros σ.
    constructor.
    - unfold cprimitive_match_init_state; simpl.
      unfold cprimitive_match_final_state; simpl.
      intros [] sg (vargs1 & m1) (vargs2 & m2) (Hvargs & Hm).
      simpl in *; subst.
      intros (vres1 & m1') H1.
      simpl in *.
      exists (vres1, m1').
      split.
      + rewrite match_val_simrel_id in Hvargs.
        rewrite list_rel_eq in Hvargs.
        congruence.
      + exists tt. rewrite match_val_simrel_id. repeat constructor.
    - eapply incl_refl.
  Qed.

  Lemma list_rel_match_val_elim_simrel_compose
        D1 D2 D3 (R12: simrel D1 D2) (R23: simrel D2 D3)
        p12 p23 l1 l3:
    list_rel (match_val (simrel_compose_ops R12 R23) (p12, p23)) l1 l3 ->
    exists l2,
      list_rel (match_val R12 p12) l1 l2 /\
      list_rel (match_val R23 p23) l2 l3.
  Proof.
    induction 1.
    + exists nil.
      repeat constructor.
    + destruct IHlist_rel as (? & ? & ?).
      exploit (match_val_elim_simrel_compose R12 R23); eauto.
      destruct 1 as (? & ? & ?).
      eexists (_ :: _); repeat constructor; eauto.
  Qed.

  Global Instance cprimitive_match_init_state_id D w:
    Coreflexive (cprimitive_match_init_state D D id w).
  Proof.
    intros [vargs1 m1] [vargs2 m2] [Hvargs Hm].
    simpl in *.
    rewrite match_val_simrel_id in Hvargs.
    rauto.
  Qed.

  Global Instance cprimitive_match_init_state_compose D1 D2 D3 R12 R23 w:
    RTransitive
      (cprimitive_match_init_state D1 D2 R12 (fst w))
      (cprimitive_match_init_state D2 D3 R23 (snd w))
      (cprimitive_match_init_state D1 D3 (simrel_compose R12 R23) w).
  Proof.
    destruct w as [w12 w23].
    simpl.
    intros s1 s3 Hinit13.
    inversion Hinit13 as [Hargs13 Hmem13]; subst.
    simpl in Hargs13, Hmem13.
    apply list_rel_match_val_elim_simrel_compose in Hargs13.
    destruct Hargs13 as (? & ? & ?).
    destruct Hmem13 as (? & ? & ?).
    eexists (_, _).
    repeat (econstructor; eauto).
  Qed.

  Global Instance cprimitive_match_final_state_id D w:
    Reflexive (cprimitive_match_final_state D D id w).
  Proof.
    intros [vres m].
    constructor; simpl; eauto.
    rewrite match_val_simrel_id.
    reflexivity.
  Qed.

  Global Instance cprimitive_match_final_state_compose D1 D2 D3 R12 R23 w:
    HTransitive
      (cprimitive_match_final_state D1 D2 R12 (fst w))
      (cprimitive_match_final_state D2 D3 R23 (snd w))
      (cprimitive_match_final_state D1 D3 (simrel_compose R12 R23) w).
  Proof.
    destruct w as [w12 w23]; simpl.
    intros s1 s2 s3 Hs12 Hs23.
    destruct Hs12.
    destruct Hs23.
    constructor.
    - eapply match_val_intro_simrel_compose; eauto.
      typeclasses eauto.
    - esplit; eauto.
  Qed.

  Global Instance cprimitive_sim_htrans D1 D2 D3 R12 R23:
    HTransitive
      (cprimitive_sim D1 D2 R12)
      (cprimitive_sim D2 D3 R23)
      (cprimitive_sim D1 D3 (simrel_compose R12 R23)).
  Proof.
    intros σ1 σ2 σ3 Hσ12 Hσ23.
    constructor.
    + intros [p12 p23] sg [args1 m1] [args3 m3] Hinit13 [res1 m1'] Hstep1.
      edestruct cprimitive_match_init_state_compose
        as ([args2 m2] & Hinit12 & Hinit23); eauto.
      eapply cprimitive_sim_step in Hinit12; eauto.
      apply Hinit12 in Hstep1; clear Hinit12.
      destruct Hstep1 as ( [res2 m'2] & Hstep2 & p12' & Hp12 & Hfinal12 ).
      eapply cprimitive_sim_step in Hinit23; eauto.
      apply Hinit23 in Hstep2; clear Hinit23.
      destruct Hstep2 as ( [ res3 m'3] & Hstep3 & p23' & Hp23 & Hfinal23 ).
      esplit.
      split; eauto.
      eexists (_, _).
      split.
      { split; eassumption. }
      ehtransitivity; eauto.
    + inversion Hσ12.
      inversion Hσ23.
      eapply incl_tran; eassumption.
  Qed.

  Global Instance cprimitive_sim_ops: Sim simrel cprimitive :=
    {
      simRR := cprimitive_sim
    }.

  Global Instance cprimitive_sim_prf:
    CategorySim layerdata simrel cprimitive.
  Proof.
    split; try typeclasses eauto.
  Qed.

  (** Union *)

  Program Definition cprimitive_union (D: layerdata) (σ1 σ2: cprimitive D) :=
    {|
      cprimitive_step sg s s' :=
        cprimitive_step D σ1 sg s s' \/
        cprimitive_step D σ2 sg s s';
      cprimitive_csig :=
        cprimitive_csig D σ1 ++ cprimitive_csig D σ2
    |}.
  Next Obligation.
    intros H.
    eapply app_eq_nil in H.
    destruct H.
    eapply cprimitive_csig_ne; eauto.
  Qed.
  Next Obligation.
    destruct H; eapply cprimitive_step_wt; eauto.
  Qed.

  Global Instance cprimitive_ops: PrimitiveOps cprimitive :=
    {
      prim_union D := {| oplus := cprimitive_union D |}
    }.

  Import PseudoJoin.

  Local Instance cprimitive_union_prf:
    SimJoin layerdata simrel cprimitive.
  Proof.
    intros D σ1 σ2.
    split.
    - simpl.
      unfold cprimitive_union.
      constructor.
      + unfold cprimitive_match_init_state, cprimitive_match_final_state.
        intros [] sg s1 s2 Hs s1' Hs1'.
        simpl in *.
        rewrite match_val_simrel_id, list_rel_eq, prod_rel_eq in Hs; subst.
        eexists; split; eauto.
        exists tt; split; eauto.
        rewrite match_val_simrel_id, prod_rel_eq.
        reflexivity.
      + simpl.
        eapply incl_appl.
        eapply incl_refl.
    - simpl.
      unfold cprimitive_union.
      constructor.
      + unfold cprimitive_match_init_state, cprimitive_match_final_state.
        intros [] sg s1 s2 Hs s1' Hs1'.
        simpl in *.
        rewrite match_val_simrel_id, list_rel_eq, prod_rel_eq in Hs; subst.
        eexists; split; eauto.
        exists tt; split; eauto.
        rewrite match_val_simrel_id, prod_rel_eq.
        reflexivity.
      + simpl.
        eapply incl_appr.
        eapply incl_refl.
    - intros D' R σ [Hstep1 Hsig1] [Hstep2 Hsig2].
      simpl.
      unfold cprimitive_union.
      constructor.
      + intros w sg s1 s2 Hs s1' Hs1'.
        simpl in *.
        destruct Hs1' as [Hs1'|Hs1'].
        * eapply Hstep1; eauto.
        * eapply Hstep2; eauto.
      + simpl.
        eapply incl_app; eauto.
  Qed.

  Global Instance cprimitive_prf:
    Primitives cprimitive.
  Proof.
    split; try typeclasses eauto.
  Qed.

  (** ** Invariant *)

  Record cprimitive_inv_init_state (D: layerdata) (args: list val) (m: mem) (d: D) :=
    {
      cprimitive_inv_init_state_data_inv:
        data_inv d;
      cprimitive_inv_init_state_valid:
        forall b, block_is_global b -> Mem.valid_block m b;
      cprimitive_inv_init_state_mem_wf:
        Mem.inject_neutral (Mem.nextblock m) m;
      cprimitive_inv_init_state_data_wf:
        data_inject (Mem.flat_inj (Mem.nextblock m)) d d;
      cprimitive_inv_init_state_args_wf:
        Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args
    }.

  Record cprimitive_inv_final_state (D: layerdata) (res: val) (m: mem) (d: D) :=
    {
      cprimitive_inv_final_state_data_inv:
        data_inv d;
      cprimitive_inv_final_state_valid:
        forall b, block_is_global b -> Mem.valid_block m b;
      cprimitive_inv_final_state_mem_wf:
        Mem.inject_neutral (Mem.nextblock m) m;
      cprimitive_inv_final_state_data_wf:
        data_inject (Mem.flat_inj (Mem.nextblock m)) d d;
      cprimitive_inv_final_state_res_wf:
        Val.inject (Mem.flat_inj (Mem.nextblock m)) res res
    }.

  Class CPrimitivePreservesInvariant D (σ: cprimitive D) :=
    {
      cprimitive_preserves_invariant sg args m d res m' d':
        cprimitive_step D σ sg (args, (m, d)) (res, (m', d')) ->
        cprimitive_inv_init_state D args m d ->
        cprimitive_inv_final_state D res m' d';
      cprimitive_nextblock_incr sg args m d res m' d':
        cprimitive_step D σ sg (args, (m, d)) (res, (m', d')) ->
        cprimitive_inv_init_state D args m d ->
        (Mem.nextblock m <= Mem.nextblock m')%positive
    }.

  Lemma inv_cprimitive_inv_init_state D args m d s p:
    cprimitive_match_init_state D D inv p (args, (m, d)) s ->
    cprimitive_inv_init_state D args m d /\ proj1_sig p = Mem.nextblock m /\ (args, (m, d)) = s.
  Proof.
    intros [Hargs Hm]; simpl in *.
    assert ((args, (m, d)) = s).
    {
      destruct s as [sargs sm].
      simpl in *.
      f_equal; solve_monotonic.
    }
    subst s.
    inversion Hm; clear Hm; subst.
    simpl in  *.
    split; auto.
    rewrite <- inv_inject_neutral_match_vals in Hargs.
    constructor; auto.
  Qed.

  Lemma inv_cprimitive_inv_final_state D res m d s p:
    cprimitive_match_final_state D D inv p (res, (m, d)) s ->
    cprimitive_inv_final_state D res m d /\ proj1_sig p = Mem.nextblock m /\ (res, (m, d)) = s.
  Proof.
    intros [Hrs Hm]; simpl in *.
    assert ((res, (m, d)) = s).
    {
      destruct s as [sres sm].
      simpl in *.
      f_equal; solve_monotonic.
    }
    subst s.
    inversion Hm; clear Hm; subst.
    split; auto.
    rewrite <- inv_inject_neutral_match_val in Hrs.
    constructor; auto.
  Qed.

  Lemma cprimitive_inv_init_state_inv D args m d:
    cprimitive_inv_init_state D args m d ->
    exists p,
      cprimitive_match_init_state D D inv p (args, (m, d)) (args, (m, d)).
  Proof.
    intro Hinv.
    exists (exist _ (Mem.nextblock m) (cprimitive_inv_init_state_valid _ _ _ _ Hinv)).
    inversion Hinv.
    constructor; simpl; auto.
    + rewrite <- inv_inject_neutral_match_vals. assumption.
    + constructor; auto.
  Qed.

  Lemma cprimitive_inv_final_state_inv D res m d:
    cprimitive_inv_final_state D res m d ->
    exists p,
      cprimitive_match_final_state D D inv p (res, (m, d)) (res, (m, d)).
  Proof.
    intro Hinv.
    exists (exist _ (Mem.nextblock m) (cprimitive_inv_final_state_valid _ _ _ _ Hinv)).
    inversion Hinv.
    constructor; simpl; auto.
    + rewrite <- inv_inject_neutral_match_val. assumption.
    + constructor; auto.
  Qed.

  Global Instance cprimitive_inv_inv D σ:
    CPrimitivePreservesInvariant D σ ->
    Proper (cprimitive_sim D D inv) σ.
  Proof.
    intros Hσ.
    split; [ | apply incl_refl ].
    intros p sg (args1 & m1 & d1) (args & m & d) Hs.
    apply inv_cprimitive_inv_init_state in Hs.
    destruct Hs as (Hinv & Hnext & EQ).
    inversion EQ; clear EQ; subst.
    intros s' Hs'.
    exists s'.
    split; auto.
    destruct s' as [res [m' d']].
    generalize Hinv. intro Hinv_.
    eapply cprimitive_preserves_invariant in Hinv; eauto.
    apply cprimitive_nextblock_incr in Hs'; auto.
    apply cprimitive_inv_final_state_inv in Hinv.
    destruct Hinv as [p' Hfin].
    exploit inv_cprimitive_inv_final_state; eauto.
    destruct 1 as (_ & Hnext' & _).
    exists p'.
    split; auto.
    destruct p; destruct p'; simpl in * ; subst; assumption.
  Qed.

  Lemma inv_cprimitive_inv D σ:
    Proper (cprimitive_sim D D inv) σ ->
    CPrimitivePreservesInvariant D σ.
  Proof.
    intros Hσ.
    cut (
        forall sg args m d res m' d',
          cprimitive_step D σ sg (args, (m, d)) (res, (m', d')) ->
          cprimitive_inv_init_state D args m d ->
          cprimitive_inv_final_state D res m' d' /\
          (Mem.nextblock m <= Mem.nextblock m')%positive
      ).
    {
      intros H.
      split; eapply H; eauto.
    }
    intros sg args m d res m' d' Hstep Hinit.
    apply cprimitive_inv_init_state_inv in Hinit.
    destruct Hinit as (p & Hinit).
    exploit inv_cprimitive_inv_init_state; eauto.
    destruct 1 as (_ & Hnext & _).
    eapply Hσ in Hinit.
    apply Hinit in Hstep; clear Hinit.
    destruct Hstep as ([res' m'_] & _ & p' & Hp' & Hfin).
    apply inv_cprimitive_inv_final_state in Hfin.
    destruct Hfin as (Hfin & Hnext' & EQ).
    inversion EQ; clear EQ; subst.
    split; auto.
    destruct p; destruct p'; simpl in *; subst; assumption.
  Qed.

  Lemma cprimitive_inv_sim_id D:
    Monotonic
      (CPrimitivePreservesInvariant D)
      (sim id --> impl).
  Proof.
    intros σ2 σ1 Hσ Hσ2.
    red in Hσ.
    split.
    - intros sg args m d res m' d' Hstep1 Hs.
      edestruct cprimitive_sim_step as (s' & Hstep2 & w' & Hw' & Hs'); eauto.
      {
        instantiate (2 := tt).
        econstructor; try reflexivity.
        setoid_rewrite match_val_simrel_id.
        reflexivity.
      }
      destruct w', s' as [xres xm'].
      destruct Hs' as [Hvres Hm'].
      simpl in *.
      rewrite match_val_simrel_id in Hvres.
      subst.
      eapply cprimitive_preserves_invariant; eauto.
    - intros sg args m d res m' d' Hstep1 Hs.
      edestruct cprimitive_sim_step as (s' & Hstep2 & w' & Hw' & Hs'); eauto.
      {
        instantiate (2 := tt).
        econstructor; try reflexivity.
        setoid_rewrite match_val_simrel_id.
        reflexivity.
      }
      destruct w', s' as [xres xm'].
      destruct Hs' as [Hvres Hm'].
      simpl in *.
      rewrite match_val_simrel_id in Hvres.
      subst.
      eapply cprimitive_nextblock_incr; eauto.
  Qed.


  (** ** Properties *)

  Require Import SimrelInject.
  Require Import SimrelLessdef.

  Class CPrimitiveExtcallProperties D (σ: cprimitive D) :=
    {
      cprimitive_ec_mem_extends:
        Monotonic σ (cprimitive_sim D D simrel_strong_extends);
      cprimitive_ec_mem_inject:
        Monotonic σ (cprimitive_sim D D simrel_strong_inject);
      cprimitive_ec_determ_sg:
        forall sg1 sg2,
          In sg1 (cprimitive_csig D σ) ->
          In sg2 (cprimitive_csig D σ) ->
          sg1 = sg2;
      cprimitive_ec_determ:
        forall sg s s'1 s'2,
          cprimitive_step D σ sg s s'1 ->
          cprimitive_step D σ sg s s'2 ->
          s'1 = s'2
    }.

  Global Existing Instances cprimitive_ec_mem_extends cprimitive_ec_mem_inject.

  Global Instance cprimitives_strong_extends_weaken D:
    Related
      (cprimitive_sim D D simrel_strong_extends)
      (cprimitive_sim D D ext)
      subrel.
  Proof.
    intros σ σ'.
    inversion 1.
    constructor; auto.
    intros p sg s1 s2 INIT.
    inversion INIT as (Hargs & Hm).
    generalize (strong_extends_intro _ _ Hm).
    destruct 1 as (mm & Hmm).
    simpl in Hargs.
    rewrite match_val_simrel_lessdef in Hargs.
    rewrite <- (match_strong_extends_val mm) in Hargs.
    assert (cprimitive_match_init_state _ _ simrel_strong_extends mm s1 s2) as Hstrong
      by (constructor; auto).
    intros s'1 STEP.
    specialize (cprimitive_sim_step0 _ _ _ _ Hstrong _ STEP).
    destruct cprimitive_sim_step0 as (s'2 & STEP' & FIN).
    destruct FIN as (mm' & INCR & FIN).
    esplit.
    split; eauto.
    exists p.
    split; simpl; auto.
    inversion FIN as (Hres & Hm').
    simpl in Hres.
    rewrite match_strong_extends_val in Hres.
    rewrite <- (match_val_simrel_lessdef p) in Hres.
    split; auto.
    simpl in Hm'.
    eapply strong_extends_elim; eauto.
  Qed.

  Global Instance cprimitives_strong_inject_weaken D:
    Related
      (cprimitive_sim D D simrel_strong_inject)
      (cprimitive_sim D D inj)
      subrel.
  Proof.
    intros σ σ'.
    inversion 1.
    constructor; auto.
    intros p sg s1 s2 INIT.
    inversion INIT as (Hargs & Hm).
    generalize (strong_inject_intro' _ _ _ Hm).
    destruct 1 as (mm & Hmm & ? ); subst.
    simpl in Hargs.
    rewrite <- match_val_strong_inject' in Hargs.
    assert (cprimitive_match_init_state _ _ simrel_strong_inject mm s1 s2) as Hstrong
      by (constructor; auto).
    intros s'1 STEP.
    specialize (cprimitive_sim_step0 _ _ _ _ Hstrong _ STEP).
    destruct cprimitive_sim_step0 as (s'2 & STEP' & FIN).
    destruct FIN as (mm' & INCR & FIN).
    esplit.
    split; eauto.
    exists (strong_inject_meminj mm').
    split.
    { apply strong_inject_acc_elim' ; auto. }
    inversion FIN as (Hres & Hm').
    simpl in Hres.
    rewrite match_val_strong_inject' in Hres.
    split; auto.
    simpl in Hm'.
    eapply strong_inject_elim' ; eauto.
  Qed.

(* The following succeeds:
<<
  Check (_: forall D σ,
    CPrimitiveExtcallProperties D σ ->
    RAuto (cprimitive_sim D D simrel_inject σ σ)).
>>
*)

  (** Occasionally we need to validate whether a primitive has exactly
    one signature, and recover it in case it does. The following
    helper functions allow us to accomplish this. *)

  Section UNIQUE_ELEMENT.
    Context `{Adec: EqDec}.

    Fixpoint unique_element (l: list A): res A :=
      match l with
        | nil => Error (msg "no sig")
        | a :: nil => OK a
        | a :: l' =>
          match unique_element l' with
            | OK a' =>
              if decide (a = a') then OK a else Error (msg "duplicate")
            | Error e => Error e
          end
      end.

    Lemma unique_element_correct l a:
      unique_element l = OK a ->
      (forall a', In a' l <-> a' = a).
    Proof.
      induction l; simpl; try discriminate.
      destruct l.
      + revert IHl. clear. simpl. intuition congruence.
      + destruct (unique_element (_ :: _)); try discriminate.
        destruct (decide (_ = _)); try discriminate.
        subst.
        intros H a'.
        generalize (IHl H a').
        revert H. clear.
        intuition congruence.
    Qed.

    Lemma unique_element_complete l a:
      (forall a', In a' l <-> a' = a) ->
      unique_element l = OK a.
    Proof.
      revert a.
      induction l; simpl.
      { intros a H.
        specialize (H a).
        intuition congruence. }
      intros a0 H.
      destruct l.
      + generalize (H a0). clear. simpl. intuition congruence.
      + specialize (IHl a0).
        assert (a1 = a0) by (apply H; simpl; auto).
        subst.
        assert (a = a0) by (apply H; simpl; auto).
        subst.
        rewrite IHl; clear IHl.
        - destruct (decide (_ = _)); congruence.
        - intro a'. generalize (H a'). clear.
          simpl; intuition congruence.
    Qed.

    Global Opaque unique_element.
  End UNIQUE_ELEMENT.

  Definition unique_csig D (σ: cprimitive D) :=
    unique_element (cprimitive_csig D σ).

  Global Instance unique_csig_rel:
    Monotonic (@unique_csig) (forallr R, cprimitive_sim _ _ R ++> res_le eq).
  Proof.
    intros D1 D2 R σ1 σ2 Hσ.
    unfold unique_csig.
    destruct Hσ as [_ Hsig].
    destruct (unique_element (cprimitive_csig D2 σ2)) as [sg|] eqn:H; [|constructor].
    replace (unique_element (cprimitive_csig D1 σ1)) with (OK sg).
    { reflexivity. }
    symmetry.
    apply unique_element_complete.
    split.
    + intros H0.
      eapply unique_element_correct; eauto.
    + intro; subst.
      generalize (cprimitive_csig_ne _ σ1).
      destruct (cprimitive_csig D1 σ1); try congruence.
      intros _.
      specialize (Hsig _ (or_introl _ (refl_equal _))).
      erewrite unique_element_correct in Hsig by eassumption.
      subst; simpl; auto.
  Qed.


  (** * User diagrams *)

  (** ** Identity diagram *)

  Lemma cprimitive_sim_id_intro D σ1 σ2:
    (forall sg s s',
       cprimitive_step D σ1 sg s s' ->
       cprimitive_step D σ2 sg s s') ->
    incl (cprimitive_csig D σ1) (cprimitive_csig D σ2) ->
    cprimitive_sim D D id σ1 σ2.
  Proof.
    intros H Hsig.
    split; eauto.
    intros [] sg s1 s2 Hs s1' Hs1'.
    exists s1'.
    split; eauto.
    - replace s2 with s1 by eauto using coreflexivity.
      eauto.
    - exists tt.
      split; reflexivity.
  Qed.

  (** ** General diagram with invariants *)

  Inductive cprimitive_inv_match_state D1 D2 R w: rel _ _ :=
    | cprimitive_inv_match_intro vs1 m1 d1 vs2 m2 d2:
        cprimitive_inv_init_state D1 vs1 m1 d1 ->
        cprimitive_inv_init_state D2 vs2 m2 d2 ->
        cprimitive_match_init_state D1 D2 R w (vs1, (m1, d1)) (vs2, (m2, d2)) ->
        cprimitive_inv_match_state D1 D2 R w (vs1, (m1, d1)) (vs2, (m2, d2)).

  Lemma cprimitive_sim_wrapinv_intro D1 D2 R σ1 σ2:
    CPrimitivePreservesInvariant D1 σ1 ->
    CPrimitivePreservesInvariant D2 σ2 ->
    (forall w sg,
      (cprimitive_inv_match_state D1 D2 R w ++>
       set_rel (incr w (cprimitive_match_final_state D1 D2 R w)))%rel
      (cprimitive_step D1 σ1 sg)
      (cprimitive_step D2 σ2 sg)) ->
    incl (cprimitive_csig D1 σ1) (cprimitive_csig D2 σ2) -> (* use incl_refl *)
    cprimitive_sim D1 D2 (inv ∘ R ∘ inv) σ1 σ2.
  Proof.
    intros Hσ1 Hσ2 H.
    split; eauto.
    intros w sg s1 s2 Hs s1' Hs1'.

    (* split up the composite relations *)
    apply cprimitive_match_init_state_compose in Hs.
    destruct Hs as (s1x & Hs1 & Hs).
    apply cprimitive_match_init_state_compose in Hs.
    destruct Hs as (s2x & Hs & Hs2).
    destruct w as [w1 [w w2]]; simpl in * |-.

    (* establish the invariant holds on s1 *)
    destruct s1 as [vargs1 [m1 d1]].
    pose proof Hs1 as Hs1inv.
    apply inv_cprimitive_inv_init_state in Hs1inv.
    destruct Hs1inv as (Hs1inv & Hw1 & ?); subst s1x.

    (* establish the invariant holds on s2 *)
    destruct s2x as [vargs2 [m2 d2]].
    pose proof Hs2 as Hs2inv.
    apply inv_cprimitive_inv_init_state in Hs2.
    destruct Hs2 as (Hs2 & Hw2 & ?); subst s2.

    (* establish the [inv] relation for [s1'] *)
    edestruct (cprimitive_sim_step D1 D1 inv)
      as (s1'x & Hs1'x & w1' & Hw1' & Hs1'inv); eauto.
    {
      apply cprimitive_inv_inv.
      assumption.
    }

    (* use the user-provided simulation diagram *)
    edestruct H as (s2' & Hs2' & w' & Hw' & Hs'); eauto.
    {
      econstructor; eauto.
    }

    (* establish the [inv] relation for [s2'] *)
    edestruct (cprimitive_sim_step D2 D2 inv)
      as (s2'x & Hs2'x & w2' & Hw2' & Hs2'inv); eauto.
    {
      apply cprimitive_inv_inv.
      assumption.
    }

    (* establish the composite relation for final states *)
    exists s2'x.
    split; eauto.
    exists (w1', (w', w2')).
    split; [ rauto | ].
    htransitivity s1'x; eauto.
    htransitivity s2'; eauto.
  Qed.

  (** ** Inclusion diagram with invariants *)

  Lemma cprimitive_sim_inv_intro D σ1 σ2:
    CPrimitivePreservesInvariant D σ2 ->
    (forall sg vs m d s',
       cprimitive_inv_init_state D vs m d ->
       cprimitive_step D σ1 sg (vs, (m, d)) s' ->
       cprimitive_step D σ2 sg (vs, (m, d)) s') ->
    incl (cprimitive_csig D σ1) (cprimitive_csig D σ2) ->
    cprimitive_sim D D inv σ1 σ2.
  Proof.
    intros Hσ2 H Hsg.
    assert (Hinv: (inv (D:=D)) ≡ inv ∘ id ∘ inv).
    {
      rewrite cat_compose_id_right.
      symmetry.
      apply simrel_compose_inv_inv.
    }
    simpl in Hinv. (* fix *)
    rewrite Hinv.
    assert (Hσ1: CPrimitivePreservesInvariant D σ1).
    {
      split.
      - eauto using cprimitive_preserves_invariant.
      - eauto using cprimitive_nextblock_incr.
    }
    eapply cprimitive_sim_wrapinv_intro; eauto.
    intros w sg.
    intros s1 s2 Hs s1' Hs1'.
    exists s1'.
    split.
    - destruct Hs.
      assert (Hs: (vs1, (m1, d1)) = (vs2, (m2, d2))).
      {
        eapply coreflexivity; eauto.
      }
      rewrite <- Hs.
      eauto.
    - exists w.
      split; reflexivity.
  Qed.
End CPRIMITIVES.

Require Import compcert.common.Events.
Require Import compcertx.common.EventsX.
Require Import compcertx.driver.CompCertBuiltins.
Require Import liblayers.logic.PTreeLayers.

Notation clayer := (ptree_layer cprimitive (globvar type)).

Section CLAYERS.
  Context `{Hmem: BaseMemoryModel}.

  Global Instance clayer_ops : LayerOps ident cprimitive (globvar type) clayer :=
    ptree_layer_ops.

  Global Instance clayer_sim_op : Sim simrel clayer :=
    ptree_layer_sim_op.

  Global Instance clayer_prf : Layers ident cprimitive (globvar type) clayer :=
    ptree_layer_prf.

  Global Instance cprimitive_to_clayer_stability D (R: simrel D D) (L: clayer D):
    ForallPrimitive D (fun σ => Proper (cprimitive_sim D D R) σ) L ->
    Proper (sim R) L.
  Proof.
    intro PRIM.
    apply ptree_layer_pointwise_sim; try reflexivity.
    intros i.
    specialize (forall_primitive_at i).
    intro H.
    destruct (get_layer_primitive i L); try constructor.
    destruct o; try constructor.
    eapply H; eauto.
  Qed.

  Global Instance cprimitive_invariant_inv D (L: clayer D):
    ForallPrimitive D (CPrimitivePreservesInvariant D) L ->
    Proper (sim inv) L.
  Proof.
    (* TODO: automate this proof? *)
    intros HL.
    apply cprimitive_to_clayer_stability.
    eapply forallprim_mono; eauto.
    intros ? ?.
    typeclasses eauto.
  Qed.

  Global Instance cprimitive_properties_lessdef D (L: clayer D):
    ForallPrimitive D (CPrimitiveExtcallProperties D) L ->
    Proper (sim ext) L.
  Proof.
    (* TODO: automate this proof? *)
    intros HL.
    apply cprimitive_to_clayer_stability.
    eapply forallprim_mono; eauto.
    intros ? ?.
    red; rauto.
  Qed.

  Global Instance cprimitive_properties_inject D (L: clayer D):
    ForallPrimitive D (CPrimitiveExtcallProperties D) L ->
    Proper (sim inj) L.
  Proof.
    (* TODO: automate this proof? *)
    intros HL.
    apply cprimitive_to_clayer_stability.
    eapply forallprim_mono; eauto.
    intros ? ?.
    red; rauto.
  Qed.

End CLAYERS.

Section EXTCALLS.
  Context `{Hmem: BaseMemoryModel}.

  Local Instance cprimitive_extcall_ops D (L: clayer D):
    ExternalCallsOpsX (mwd D) :=
    {
      external_functions_sem i sg ge vargs m t vres m' :=
        stencil_matches ge /\
        exists (σ: cprimitive D) csg j,
          i = name_of_ident j /\
          get_layer_primitive j L = OK (Some σ) /\
          cprimitive_step D σ csg (vargs, m) (vres, m') /\
          In csg (cprimitive_csig D σ) /\
          csig_sig csg = sg /\
          t = E0
    }.

  Ltac destruct_extfun H :=
    let Hge := fresh "Hge" in
    let σ := fresh "σ" in
    let csg := fresh "csg" in
    let j := fresh "j" in
    let GET := fresh "GET" in
    let PRIM := fresh "PRIM" in
    let STEP := fresh "STEP" in
    let INSIG := fresh "INSIG" in
    let SIG := fresh "SIG" in
    let TRACE := fresh "TRACE" in
    destruct H as (Hge & σ & csg & j & GET & PRIM & STEP & INSIG & SIG & TRACE).

  Lemma external_functions_sem_receptive D L i sg ge vargs m t1 vres1 m1 t2:
    external_functions_sem
      (ExternalCallsOpsX := cprimitive_extcall_ops D L)
      i sg ge vargs m t1 vres1 m1 ->
    match_traces ge t1 t2 ->
    exists vres2 m2,
      external_functions_sem
        (ExternalCallsOpsX := cprimitive_extcall_ops D L)
        i sg ge vargs m t2 vres2 m2.
  Proof.
    intros H H0.
    destruct_extfun H; subst.
    inversion H0; subst.
    esplit. esplit. esplit; eauto.
    esplit; eauto 10.
  Qed.

  Lemma external_functions_sem_trace_length D L i sg ge vargs m t1 vres1 m1:
    external_functions_sem
      (ExternalCallsOpsX := cprimitive_extcall_ops D L)
      i sg ge vargs m t1 vres1 m1 ->
    (length t1 <= 1)%nat.
  Proof.
    intros H.
    destruct_extfun H; subst.
    simpl; omega.
  Qed.

  Require Import CompCertBuiltins.

  Existing Instance meminj_preserves_globals'_instance.

  Local Instance cprimitive_extcall_prf D L:
    ForallPrimitive D (CPrimitiveExtcallProperties D) L ->
    ExternalCallsPropsX (external_calls_ops_x := cprimitive_extcall_ops D L) (mwd D).
  Proof.
    intros PROPS.
    constructor.
    intros i sg.
    constructor.

    + (* ec_well_typed *)
      intros ge vargs m1 t vres m2 H.
      destruct_extfun H; subst.
      exploit cprimitive_step_wt; eauto.
      simpl.
      destruct csg. simpl.
      unfold csig_sig. simpl.
      unfold proj_sig_res. simpl.
      destruct csig_res; simpl; auto.

    + (* ec_symbols_preserved *)
      intros ge1 ge2 vargs m1 t vres m2 SE H1.
      destruct_extfun H1; subst.
      econstructor; eauto 10.
      rewrite <- SE.
      assumption.

    + (* ec_valid_block *)
      intros ge vargs m1 t vres m2 b H H0.
      destruct_extfun H; subst. 
      specialize (forall_primitive_at _ _ PRIM). clear PROPS. intro PROPS.
      generalize (Mem.extends_refl m1). intro Hm.
      generalize (strong_extends_intro _ _ Hm).
      destruct 1 as (mm & Hmm).
      assert (cprimitive_match_init_state _ _ simrel_strong_extends mm (vargs, m1) (vargs, m1))
             as INIT.
      {
        constructor; auto.
        simpl. rewrite match_strong_extends_val.
        clear.
        induction vargs; constructor; auto.
      }
      specialize (cprimitive_ec_mem_extends). intro EXT.
      inversion EXT; subst.
      specialize (cprimitive_sim_step0 _ _ _ _ INIT _ STEP).
      destruct cprimitive_sim_step0 as (s'2 & STEP' & FIN).
      destruct FIN as (mm' & INCR & FIN).
      inversion FIN; subst.
      simpl in *.
      eapply strong_extends_le_elim; try eexact INCR; eauto.

    + (* ec_max_perm *)
      intros ge vargs m1 t vres m2 b ofs p H H0 H1.
      destruct_extfun H; subst.
      specialize (forall_primitive_at _ _ PRIM). clear PROPS. intro PROPS.
      generalize (Mem.extends_refl m1). intro Hm.
      generalize (strong_extends_intro _ _ Hm).
      destruct 1 as (mm & Hmm).
      assert (cprimitive_match_init_state _ _ simrel_strong_extends mm (vargs, m1) (vargs, m1))
             as INIT.
      {
        constructor; auto.
        simpl. rewrite match_strong_extends_val.
        clear.
        induction vargs; constructor; auto.
      }
      specialize (cprimitive_ec_mem_extends). intro EXT.
      inversion EXT; subst.
      specialize (cprimitive_sim_step0 _ _ _ _ INIT _ STEP).
      destruct cprimitive_sim_step0 as (s'2 & STEP' & FIN).
      destruct FIN as (mm' & INCR & FIN).
      inversion FIN as ( ? & Hm' ); subst.
      eapply (strong_extends_le_elim (D := D));
        simpl in INCR, Hm';
        try eexact INCR;
        eauto.

    + (* ec_readonly *)
      intros ge vargs m1 t vres m2 H.
      destruct_extfun H; subst.
      specialize (forall_primitive_at _ _ PRIM). clear PROPS. intro PROPS.
      generalize (Mem.extends_refl m1). intro Hm.
      generalize (strong_extends_intro _ _ Hm).
      destruct 1 as (mm & Hmm).
      assert (cprimitive_match_init_state _ _ simrel_strong_extends mm (vargs, m1) (vargs, m1))
             as INIT.
      {
        constructor; auto.
        simpl. rewrite match_strong_extends_val.
        clear.
        induction vargs; constructor; auto.
      }
      specialize (cprimitive_ec_mem_extends). intro EXT.
      inversion EXT; subst.
      specialize (cprimitive_sim_step0 _ _ _ _ INIT _ STEP).
      destruct cprimitive_sim_step0 as (s'2 & STEP' & FIN).
      destruct FIN as (mm' & INCR & FIN).
      inversion FIN as ( ? & Hm' ); subst.
      eapply (strong_extends_le_elim (D := D));
        simpl in INCR, Hm';
        try eexact INCR;
        eauto.

    + (* ec_mem_extends *)
      intros ge vargs m1 t vres m2 m1' vargs' H H0 H1.
      destruct_extfun H; subst.
      specialize (forall_primitive_at _ _ PRIM). clear PROPS. intro PROPS.
      generalize (strong_extends_intro _ _ H0).
      destruct 1 as (mm & Hmm).
      assert (cprimitive_match_init_state _ _ simrel_strong_extends mm (vargs, m1) (vargs', m1'))
             as INIT.
      {
        constructor; auto.
        simpl. rewrite match_strong_extends_val.
        revert H1.
        clear.
        induction 1; constructor; auto.
      }
      specialize (cprimitive_ec_mem_extends). intro EXT.
      inversion EXT; subst.
      specialize (cprimitive_sim_step0 _ _ _ _ INIT _ STEP).
      destruct cprimitive_sim_step0 as (s'2 & STEP' & FIN).
      destruct FIN as (mm' & INCR & FIN).
      inversion FIN as ( Hres & Hm' ); subst.
      destruct s'2.
      esplit. esplit. 
      split.
      {
        esplit; eauto 10.
      }
      split.
      {
        simpl in Hres. rewrite match_strong_extends_val in Hres. assumption.
      }
      exploit (strong_extends_le_elim (D := D));
        simpl in INCR, Hm';
        try eexact INCR;
        eauto.
      apply strong_extends_elim in Hm'.
      tauto.

    + (* ec_mem_inject *)
      intros ge1 ge2 vargs m1 t vres m2 f m1' vargs' H H0 H1 H2.
      destruct_extfun H0; subst.
      specialize (forall_primitive_at _ _ PRIM). clear PROPS. intro PROPS.
      destruct H as [[Hfs Hvol] Hge12]; subst ge2.
      edestruct (strong_inject_intro (D:=D)) as (mm & Hm & Hf); eauto; subst.
      assert (cprimitive_match_init_state _ _ simrel_strong_inject mm (vargs, m1) (vargs', m1'))
             as INIT.
      {
        constructor; auto.
        simpl. rewrite match_val_strong_inject.
        revert H2.
        clear.
        induction 1; constructor; auto.
      }
      specialize (cprimitive_ec_mem_inject). intro INJ.
      inversion INJ; subst.
      specialize (cprimitive_sim_step0 _ _ _ _ INIT _ STEP).
      destruct cprimitive_sim_step0 as (s'2 & STEP' & FIN).
      destruct FIN as (mm' & INCR & FIN).
      inversion FIN as ( Hres & Hm' ); subst.
      destruct s'2.
      exists (strong_inject_meminj mm'). esplit. esplit.
      split.
      {
        esplit; eauto 10.
      }
      split.
      {
        simpl in Hres. rewrite match_val_strong_inject in Hres. assumption.
      }
      exploit (strong_inject_acc_elim (D := D));
        simpl in INCR, Hm';
        try eexact INCR;
        eauto.
      apply strong_inject_elim' in Hm'.
      apply simrel_inject_match_mem_base in Hm'.
      tauto.

    + (* ec_trace_length *)
      apply external_functions_sem_trace_length.

    + (* ec_receptive *)
      apply external_functions_sem_receptive.

    + (* ec_determ *)
      intros ge vargs m t1 vres1 m1 t2 vres2 m2 H H0.
      destruct_extfun H; subst.
      specialize (forall_primitive_at _ _ PRIM). clear PROPS. intro PROPS.
      destruct_extfun H0; subst.
      split; try now constructor.
      intros _.
      apply name_of_ident_inj in GET. subst.
      replace σ0 with σ in * by congruence.
      assert (csg0 = csg) by eauto using cprimitive_ec_determ_sg; subst.
      generalize (cprimitive_ec_determ _ _ _ _ STEP STEP0).
      inversion 1; subst.
      auto.
  Qed.

  Local Instance cprimitive_cc_ops D L:
    @EnableBuiltins
      (mwd D)
      (mwd_ops D)
      (external_calls_ops_x_to_external_calls_ops
         (mwd D)
         (external_calls_ops_x := cprimitive_extcall_ops D L)) :=
    {
      cc_enable_external_as_builtin := false
    }.

  (* Context `{Hnorepet: !BuiltinIdentsNorepet}. *)

  Lemma external_call_spec_no_extcall D L:
    forall ef,
      (forall i sg', ef <> EF_external i sg') ->
      extcall_properties
        (external_call
           (external_calls_ops :=
              external_calls_ops_x_to_external_calls_ops
                (mwd D) (external_calls_ops_x := cprimitive_extcall_ops D L))
           ef) (ef_sig ef).
  Proof.
    intros; destruct ef; simpl.
    edestruct H; simpl; eauto.
    apply builtin_functions_properties.
    apply runtime_functions_properties.
    eapply volatile_load_ok; eauto.
    eapply volatile_store_ok; eauto.
    eapply extcall_malloc_ok; eauto.
    eapply extcall_free_ok; eauto.
    eapply extcall_memcpy_ok; eauto.
    eapply extcall_annot_ok.
    eapply extcall_annot_val_ok.
    simpl. easy.
    eapply extcall_debug_ok; eauto.
  Qed.

  Lemma external_call_receptive D L ge ef vargs m t1 vres1 m1 t2:
    external_call
      (external_calls_ops :=
         external_calls_ops_x_to_external_calls_ops
           (mwd D) (external_calls_ops_x := cprimitive_extcall_ops D L))
      ef ge vargs m t1 vres1 m1 ->
    match_traces ge t1 t2 ->
    exists vres2 m2,
      external_call
        (external_calls_ops :=
           external_calls_ops_x_to_external_calls_ops
             (mwd D) (external_calls_ops_x := cprimitive_extcall_ops D L))
        ef ge vargs m t2 vres2 m2.
  Proof.
    destruct ef; try (apply external_call_spec_no_extcall; congruence).
    apply external_functions_sem_receptive. 
  Qed.

  Lemma external_call_trace_length D L ge ef vargs m t1 vres1 m1:
    external_call
      (external_calls_ops :=
         external_calls_ops_x_to_external_calls_ops
           (mwd D) (external_calls_ops_x := cprimitive_extcall_ops D L))
      ef ge vargs m t1 vres1 m1 ->
    (length t1 <= 1)%nat.
  Proof.
    destruct ef; try (apply external_call_spec_no_extcall; congruence).
    apply external_functions_sem_trace_length.
  Qed.

  Local Instance cprimitive_ec_props D L:
    ForallPrimitive D (CPrimitiveExtcallProperties D) L ->
    ExternalCallsProps
      (mwd D)
      (external_calls_ops :=
         external_calls_ops_x_to_external_calls_ops
           (mwd D)
           (external_calls_ops_x := cprimitive_extcall_ops D L)).
  Proof.
    intros.
    apply cprimitive_extcall_prf in H. typeclasses eauto.
  Qed.

  Local Instance cprimitive_ec D L
        (H: ForallPrimitive D (CPrimitiveExtcallProperties D) L):
    @ExternalCalls
      _ _ 
      (external_calls_ops_x_to_external_calls_ops
         (mwd D)
         (external_calls_ops_x := cprimitive_extcall_ops D L))
      (cprimitive_cc_ops D L) _
      (Mem.memory_model_x_memory_model)
      (cprimitive_ec_props D L H)
  .


  (** Relating instances of ExternalCallsOpsX *)
  Definition ec_rel D1 D2 R
      (ec1: ExternalCallsOpsX (mwd D1))
      (ec2: ExternalCallsOpsX (mwd D2)) :=
    forall F V i sg ge1 ge2 vargs1 vargs2 m1 m2 t vres1 m1' p,
      SimEvents.senv_le (F:=F) (V:=V) (fun _ => ⊤%rel) ge1 ge2 ->
      list_rel (match_val R p) vargs1 vargs2 ->
      match_mem R p m1 m2 ->
      external_functions_sem i sg ge1 vargs1 m1 t vres1 m1' ->
      exists p' vres2 m2',
        match_val R p' vres1 vres2 /\
        match_mem R p' m1' m2' /\
        external_functions_sem i sg ge2 vargs2 m2 t vres2 m2'.

End EXTCALLS.
