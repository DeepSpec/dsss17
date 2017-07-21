Require Import compcertx.common.MemoryX.
Require Import liblayers.simrel.AbstractData.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.logic.PTrees.
Require Import LogicalRelations.
Require Import liblayers.compcertx.MakeProgram.
Require Export liblayers.compcertx.CPrimitives.
Require Export liblayers.compcertx.ClightModules. (* IMPORTANT to have it imported AFTER CPrimitives, to hide AST.Internal and Clight.function *)
Require Import compcertx.common.EventsX.
Require Import SimulationRelation.
Require Import liblayers.compcertx.SimClight.
Require Export liblayers.compcertx.ClightWellTyped.
Require liblayers.compcertx.InitMemMakeProgram.

(** * LayerLib Semantics of ClightX *)

(** For Clight, the structure and union definitions are stored in an
  auxiliary [composite_env]. Eventually, we will want such definitions
  to be part of our modules and go through [make_program]. But for
  now, we take the [composite_env] as a global parameter, with the
  following instance defining an empty one as the default. *)

Class ClightCompositeEnv := cenv : composite_env.
Global Instance default_cenv : ClightCompositeEnv := PTree.empty _.

Section SEMANTICS.
  Context `{Hmem: BaseMemoryModel}.

  (** Specialize [Clight.step2] to use a specific layer for external calls. *)
  Definition clight_step D L (m: mwd D) :=
    Clight.step2
      (enable_builtins_instance := cprimitive_cc_ops D L)
  .

  Definition clight_cprimitive_csig κ :=
    {|
      csig_args := type_of_params (fn_params κ);
      csig_res := fn_return κ;
      csig_cc := fn_callconv κ
    |}.

  Inductive clight_cprimitive_step D L ge (κ: ClightModules.function):
    csignature ->
    (list val × mwd D) -> (val × mwd D) -> Prop :=
    | clight_cprimitive_step_intro vargs m vres m':
        forall csg, csg = clight_cprimitive_csig κ ->
        (Smallstep.plus (clight_step D L m) ge)
          (Callstate (Internal (InlinableFunction.function κ)) vargs Kstop m) (* pour tout k is_call_cont *)
          E0
          (Returnstate vres Kstop m') ->
        clight_cprimitive_step D L ge κ csg (vargs, m) (vres, m').

  Program Definition clight_cprimitive D L ge κ : cprimitive D :=
    mkcprimitive D (clight_cprimitive_step D L ge κ) (clight_cprimitive_csig κ) _.
  Next Obligation.
    inversion H; subst.
    eapply clight_funcall_wt; eauto.
  Qed.

  Lemma unique_csig_clight_cprimitive D L ge κ:
    unique_csig D (clight_cprimitive D L ge κ) = OK (clight_cprimitive_csig κ).
  Proof.
    reflexivity.
  Qed.

  Global Instance make_clight_fundef_varinfo_ops:
    ProgramFormatOps function type fundef type :=
    {
      make_internal κ :=
        OK (Internal (InlinableFunction.function κ));
      make_external D i σ :=
        csig <- unique_csig D σ;
        OK (External
              (EF_external (name_of_ident i) (csig_sig csig))
              (csig_args csig)
              (csig_res csig)
              (csig_cc csig));
      make_varinfo x :=
        OK x
    }.

  Global Instance make_clight_fundef_varinfo_prf:
    ProgramFormat function type fundef type.
  Proof.
    constructor.
    - simpl.
      intros.
      repeat rstep.
      + eapply unique_csig_rel; eauto.
      + congruence.
  Qed.

  Context `{Hmkp: MakeProgram}.
  Context `{ce: ClightCompositeEnv}.

  Global Instance clight_function_semantics_ops:
    FunctionSemanticsOps ident function cprimitive (globvar type)
      cmodule
      clayer
    :=
    {
      semof_fundef D ML i κ :=
        ge <- make_globalenv D ML;
        ret (clight_cprimitive D (snd ML) (Build_genv ge cenv) κ)
    }.

  Local Opaque ptree_layer_ops.
  Local Opaque ptree_layer_sim_op.
  Local Opaque ptree_module_ops.

  (** ** Monotonicity in terms of [genv_sim] *)

  Global Instance clight_semantics_ops:
    SemanticsOps _ function cprimitive (globvar type) cmodule clayer :=
    ptree_semof (Fops:= clight_function_semantics_ops).

  Section CLIGHT_MONOT.
    Context D1 D2 (R: simrel D1 D2).
    Context (M1: cmodule).
    Context (L1: clayer D1).
    Context (M2: cmodule).
    Context (L2: clayer D2).
    Context (HM: M1 ≤ M2).
    Context (HL: sim R L1 (〚M2〛 L2)).
    Context p1 (Hp1: MakeProgramSpec.make_program D1 (M1, L1) = OK p1).
    Context p2 (Hp2: MakeProgramSpec.make_program D2 (M2, L2) = OK p2).

    Inductive clight_funrel:
      ident -> rel (function+cprimitive D1)%type (function+cprimitive D2)%type :=
      | clight_funrel_function i κ:
          clight_funrel i (inl κ) (inl κ)
      | clight_funrel_primitive i σ1 σ2:
          get_layer_primitive i L1 = OK (Some σ1) ->
          get_layer_primitive i L2 = OK (Some σ2) ->
          sim R σ1 σ2 ->
          clight_funrel i (inr σ1) (inr σ2)
      | clight_funrel_replace i σ1 κ2 σ2:
          get_layer_primitive (V := globvar type) i L1 = OK (Some σ1) ->
          get_module_function (V := globvar type) i M2 = OK (Some κ2) ->
          get_layer_primitive i (〚M2〛 L2) = OK (Some σ2) ->
          sim R σ1 σ2 ->
          forall HL2i : get_layer_primitive (V := globvar type) i L2 = OK None,
          clight_funrel i (inr σ1) (inl κ2).

    Global Instance make_clight_fundef_error i:
      Related
        (make_fundef D1 i)
        (make_fundef D2 i)
        (clight_funrel i ++> impl @@ isError).
    Proof.
      unfold make_fundef.
      simpl.
      intros f1 f2 Hf [err H].
      unfold isError.
      destruct Hf; eauto.
      - simpl in H2.
        assert (Hsig: res_le eq (unique_csig D1 σ1) (unique_csig D2 σ2))
          by (eapply unique_csig_rel; eauto).
        destruct Hsig.
        + discriminate.
        + exists msg.
          reflexivity.
      - setoid_rewrite ptree_get_semof_primitive in H2.
        unfold semof_function in H2.
        setoid_rewrite H1 in H2.
        monad_norm.
        simpl semof_fundef in H2.
        destruct (make_globalenv D2 (M2, L2)) as [ge|] eqn:Hge; try discriminate.
        monad_norm.
        apply make_globalenv_make_program in Hge.
        destruct Hge as [p Hp].
        apply (make_program_noconflict D2 M2 L2 p i) in Hp.
        destruct Hp; try discriminate.
        simpl in H2.
        inv_monad H2.
        inv_monad H2.
        assert (Hsig: res_le eq (unique_csig D1 σ1) (unique_csig D2 σ2))
          by (eapply unique_csig_rel; eauto).
        subst.
        change (unique_csig D2 _) with (OK (clight_cprimitive_csig κ2)) in Hsig.
        inversion Hsig.
        rewrite <- H2 in H.
        discriminate.
    Qed.

    Global Instance make_clight_vardef_error R:
      Monotonic make_varinfo (R ++> impl @@ isError).
    Proof.
      intros v1 v2 _ [err H].
      simpl in H.
      discriminate.
    Qed.

    (** First, we show that our premises are sufficient to establish
      the "syntactic" module-layer relation derived from [clight_funrel].
      The idea is to go from whole-layer hypotheses (which will however
      remain available throughout the proof) to a per-definition
      relation which we can easily show is preserved by [make_globalenv]. *)

    Lemma clight_module_layer_funrel:
      module_layer_le D1 D2 clight_funrel (M1,L1) (M2,L2).
    Proof.
      intro i.
      apply PTreeLayers.ptree_layer_sim_pointwise in HL.
      destruct HL as (HL_prim & HL_var).
      clear HL.
      specialize (HL_prim i).
      specialize (HL_var i).
      generalize (ptree_get_semof_globalvar (Fops := clight_function_semantics_ops) _ i M2 L2).
      unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
      intro EQ. rewrite EQ in HL_var. clear EQ.
      generalize (ptree_get_semof_primitive (Fops := clight_function_semantics_ops) _ i M2 L2).
      unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
      intro EQ. rewrite EQ in HL_prim. clear EQ.
      unfold semof_function in HL_prim.
      unfold semof_fundef in HL_prim.
      unfold clight_function_semantics_ops in HL_prim.
      erewrite make_program_make_globalenv in HL_prim by eassumption.
      generalize (get_module_function_monotonic i _ _ HM).
      intro Hm_func.
      generalize (get_module_variable_monotonic i _ _ HM).
      intro Hm_var.
      clear HM.
      assert (HM_OK: ModuleOK M2).
      {
        eapply make_program_module_ok; esplit; eauto.
      }
      specialize (HM_OK i).
      destruct HM_OK as [HM_OK_fun HM_OK_var module_ok_disjoint].
      destruct HM_OK_fun as (? & HM_OK_fun).
      destruct HM_OK_var as (? & HM_OK_var).
      unfold get_module_layer_function.
      unfold get_module_layer_variable.
      simpl @fst.
      simpl @snd.
      generalize (make_program_noconflict _ _ _ _ i Hp2).
      intro Hnc2.
      unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
      rewrite HM_OK_fun in Hm_func, module_ok_disjoint, Hnc2 |- *.
      rewrite HM_OK_fun in HL_prim.
      rewrite HM_OK_var in HL_var.
      monad_norm.
      rewrite HM_OK_var in Hm_var, module_ok_disjoint, Hnc2 |- *.
      generalize (make_program_noconflict _ _ _ _ i Hp1).
      intro Hnc1.
      revert HL_prim HL_var Hm_func Hm_var.
      inversion Hnc1; clear Hnc1; subst; split; intros;
      autorewrite with res_option_globalvar; auto;
      (try now 
          match goal with
              |- res_le _ _ ?y => destruct y; repeat constructor
          end).
      + (* module function *)
        inversion Hm_func; clear Hm_func; subst.
        match goal with
            K: option_le _ _ _ |- _ =>
            inversion K; clear K; subst
        end.
        inversion Hnc2; subst.
        constructor.
        constructor.
        constructor.
      + (* module variable *)
        inversion Hm_var; clear Hm_var; subst.
        match goal with
            K: option_le _ _ _ |- _ =>
            inversion K; clear K; subst
        end.
        inversion Hnc2; subst; autorewrite with res_option_globalvar;
        reflexivity.
      + (* layer primitive *)
        destruct (get_layer_primitive i L2) as [ pr2 | ] eqn:Hprim2;
        [ | now 
            match type of HM_OK_fun with
                _ = OK ?z =>
                destruct z; constructor
            end ].
        inversion Hnc2; subst; try now
        (
          exfalso; simpl in HL_prim; inversion HL_prim; subst;
          match goal with
              K: option_le _ _ None |- _ =>
              inversion K; clear K; subst
          end
        ).
        - monad_norm.
          simpl in HL_prim.
          inversion HL_prim; subst.
          match goal with
              K: option_le _ (Some _) _ |- _ =>
              inversion K; clear K; subst
          end.
          constructor.
          constructor.
          econstructor; eauto.
          unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
          rewrite ptree_get_semof_primitive.
          rewrite HM_OK_fun.
          unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
          rewrite Hprim2.
          simpl.
          unfold semof_function.
          monad_norm.
          unfold semof_fundef.
          simpl.
          erewrite make_program_make_globalenv by eassumption.
          reflexivity.
        - simpl in HL_prim.
          inversion HL_prim; subst.
          match goal with
              K: option_le _ (Some _) (Some _) |- _ =>
              inversion K; clear K; subst
          end.
          constructor.
          constructor.
          constructor; auto.
    Qed.

    (** Next, we want to show that once this per-definition relation
      has been transported to global environments, we can establish a
      simulation in terms of the operational semantics of Clight. Most
      of this proof is done in the [SimClight] library. Here we
      establish that [clight_funrel] has the required properties for
      this proof to work: namely, that function calls in global
      environments related by [clight_funrel] will be compatible. *)

    Instance clight_funrel_prf:
      let _ := cprimitive_extcall_ops D1 L1 in
      let _ := cprimitive_extcall_ops D2 L2 in
      let _ := cprimitive_cc_ops D1 L1 in
      let _ := cprimitive_cc_ops D2 L2 in
      ClightFunrel R
        (fundef_le D1 D2 clight_funrel)
        (Build_genv (Genv.globalenv p1) cenv)
        (Build_genv (Genv.globalenv p2) cenv).
    Proof.
      intros ecops1 ecops2 ccops1 ccops2.
      split.
      - intros b f1 f2 Hf.
        destruct Hf as [fm1 fp1 Hfp1 fm2 fp2 Hfp2 Hfm].
        unfold match_fundef in *.
        destruct Hfm as [i κ | i σ1 σ2 Hσ1 Hσ2 Hσ | i σ1 κ2 σ2 Hσ1 Hκ2 Hσ2 Hσ].
        + simpl in *; congruence.
        + simpl in Hfp1, Hfp2.
          inv_monad Hfp1; inv_monad Hfp2; subst; simpl.
          destruct (unique_csig D1 σ1) eqn:SIG1; try discriminate.
          destruct (unique_csig D2 σ2) eqn:SIG2; try discriminate.
          repeat
            match goal with
                K: unique_csig ?D ?σ = OK ?u |- _ =>
                generalize (unique_element_correct _ _ K);
                  clear K; intro K;
                  let L := fresh "Hsig" σ in
                  (assert (In u (cprimitive_csig D σ)) as L by (generalize (K u); intro; intuition congruence));
                    revert K
            end.
          eapply cprimitive_sim_csig in Hsigσ1; eauto.
          intros _ U2.
          rewrite U2 in Hsigσ1; clear U2.
          congruence.
        + simpl in Hfp1, Hfp2.
          inv_monad Hfp1; inversion Hfp2; clear Hfp2; subst; simpl.
          unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
          rewrite (ptree_get_semof_primitive) in Hσ2.
          rewrite Hκ2 in Hσ2.
          unfold semof_function in Hσ2.
          match type of Hσ2 with
            _ ⊕ ?b = OK _ => assert (b = OK None) as NONE
          end.
          (* assert (get_layer_primitive i L2 = OK None) as NONE. *)
          {
            exploit (fun K => make_program_module_layer_disjoint M2 L2 K i).
            { unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
              rewrite Hp2. red; eauto. }
            unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
            rewrite Hκ2.
            inversion 1; congruence.
          }
          monad_norm.
          destruct (unique_csig D1 σ1) eqn:SIG1; try discriminate.
          simpl in H0. inv H0. simpl.
          rewrite NONE in Hσ2.
          simpl in Hσ2.
          simpl in Hσ.
          apply cprimitive_sim_csig in Hσ.
          simpl in Hσ.
          match goal with
              K: unique_csig ?D ?σ = OK ?u |- _ =>
              generalize (unique_element_correct _ _ K);
                clear K; intro K;
                let L := fresh "Hsig" σ in
                (assert (In u (cprimitive_csig D σ)) as L by (generalize (K u); intro; intuition congruence));
                  clear K
          end.
          apply Hσ in Hsigσ1.
          simpl in Hsigσ1.
          destruct κ2.
          simpl.
          unfold type_of_function.
          erewrite make_program_make_globalenv in Hσ2 by eassumption.
          simpl in Hσ2.
          inversion Hσ2; clear Hσ2; subst.
          simpl in Hσ.
          destruct Hsigσ1; subst; try contradiction.
          reflexivity. 
      - reflexivity.
      - intros p b t Hge.
        intros f1 f2 Hf vargs1 vargs2 Hvargs k1 k2 [Hk Hk_cc] m1 m2 Hm s1' Hs1'.
        destruct Hf as [fm1 fp1 Hfp1 fm2 fp2 Hfp2 Hfm].
        destruct Hfm as [i κ | i σ1 σ2 Hσ1 Hσ2 Hσ | i σ1 κ2 σ2 Hσ1 Hκ2 Hσ2 Hσ].
        + (** Identical internal functions *)
          simpl in *.
          inversion Hfp1; inversion Hfp2; clear Hfp1 Hfp2; subst; simpl.
          inversion Hs1'; clear Hs1'; subst.
          eapply transport in H5.
          Focus 2.
            Set Printing All.
            instantiate (3 := mwd D2).
            (** XXX: monotonicity *)
            eapply function_entry2_match; solve_monotonic.
            Unset Printing All.
          split_hyp H5.
          eexists.
          split.
          * eapply Smallstep.plus_one.
            econstructor; eauto.
          * exists p'.
            split; eauto.
            solve_monotonic.
            (* TODO: this step should be automatic. *)
            eapply cont_match_le; eauto.
        + (** Related primitive specifications *)
          simpl in *.
          inversion Hfp1; inversion Hfp2; clear Hfp1 Hfp2; subst; simpl.
          destruct (unique_csig D1 σ1) eqn:SIG1; try discriminate.
          destruct (unique_csig D2 σ2) eqn:SIG2; try discriminate.
          inv_monad H0; inv_monad H1; subst; simpl.
          inversion Hs1'; clear Hs1'; subst.
          simpl in H8.
          destruct H8 as (Hgep & xσ1 & sg & i1 & name_eq1 & Hxσ1 & Hstep1 & Hcsg & _ & Ht); subst.
          exploit name_of_ident_inj; eauto. intro; subst.
          rewrite Hxσ1 in Hσ1.
          inversion Hσ1; clear Hσ1; subst.
          edestruct (cprimitive_sim_step D1 D2 R σ1 σ2)
            as ([vres2 m2'] & Hstep2 & p' & Hp' & Hvres & Hm');
            eauto.
          {
            solve_monotonic.
          }
          assert (res_le eq (unique_csig D1 σ1) (unique_csig D2 σ2)) as LE.
          { eapply unique_csig_rel; eauto. }
          rewrite SIG1 in LE. rewrite SIG2 in LE.
          inversion LE; clear LE; subst.
          generalize (let (_, K) := (unique_element_correct _ _ SIG2 c0) in (K Logic.eq_refl)).
          intro.
          erewrite unique_element_correct in Hcsg by eauto.
          subst.
          exists (Returnstate vres2 k2 m2').
          split.
          * eapply Smallstep.plus_one; econstructor; eauto.
            destruct Hge.
            simpl; eauto 20.
          * exists p'.
            split; eauto.
            constructor; eauto.
            split; eauto.
            (* TODO: this step should be automatic. *)
            eapply cont_match_le; eauto.
        + (** Implemented primitive *)
          unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
          rewrite ptree_get_semof_primitive in Hσ2.
          match type of Hσ2 with
            _ ⊕ ?b = OK _ => assert (b = OK None) as NONE
          end.
          {
            exploit (fun K => make_program_module_layer_disjoint M2 L2 K i).
            { unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
              rewrite Hp2. red; eauto. }
            unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
            rewrite Hκ2.
            inversion 1; congruence.
          }
          rewrite NONE in Hσ2.
          simpl in Hσ2.
          unfold semof_function in Hσ2.
          rewrite Hκ2 in Hσ2.
          monad_norm.
          unfold semof_fundef in Hσ2.
          simpl in Hσ2.
          erewrite make_program_make_globalenv in Hσ2 by eassumption.
          monad_norm.
          inversion Hσ2; clear Hσ2; subst.
          simpl in *.
          inversion Hfp1; inversion Hfp2; clear Hfp1 Hfp2; subst; simpl.
          destruct (unique_csig D1 σ1) eqn:SIG1; try discriminate. simpl in H0. inv H0.
          inversion Hs1'; clear Hs1'; subst.
          simpl in H8.
          destruct H8 as (Hge1 & xσ1 & sg & i1 & eq_name1 & Hxσ1 & Hstep1 & Hsg & _ & Ht); subst.
          exploit name_of_ident_inj; eauto. intro; subst.
          unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
          rewrite Hxσ1 in Hσ1. inversion Hσ1; clear Hσ1; subst.
          edestruct (cprimitive_sim_step D1 D2 R σ1)
            as ([vres2 m2'] & Hstep2 & p' & Hp' & Hvres & Hm');
            eauto.
          {
            solve_monotonic.
          }
          simpl in *.
          erewrite unique_element_correct in Hsg by eauto.
          subst.
          inversion Hstep2; clear Hstep2; subst.
          exists (Returnstate vres2 k2 m2').
          split.
          * assert (is_call_cont k2) as Hk2_cc.
            {
              revert Hk_cc.
              eapply @is_call_cont_match_weak.
              exact Hk.
            }
            apply (plus2_frame_cont k2 Hk2_cc _
                                    (Callstate _ _ Kstop _)
                                    _ (Returnstate _ Kstop _)).
            simpl. assumption.
          * exists p'.
            split; eauto.
            eapply Returnstate_rel; solve_monotonic.
            split; eauto.
            eapply cont_match_le; eauto.
    Qed.

    (** Now we can use [clight_sim] to prove several properties.
      First, we show the monotonicity of our semantics "probes".
      This can then be used to prove both the simple monotonicity
      required by [FunctionSemantics], and hopefully vertical
      composition as well. *)

    Instance clight_cprimitive_step_match:
      let _ := cprimitive_extcall_ops D1 L1 in
      let _ := cprimitive_extcall_ops D2 L2 in
      let _ := cprimitive_cc_ops D1 L1 in
      let _ := cprimitive_cc_ops D2 L2 in
      Related
        (clight_cprimitive_step D1 L1)
        (clight_cprimitive_step D2 L2)
        (genv_sim R (rexists i, fundef_le D1 D2 clight_funrel i) ++>
         - ==>
         - ==>
             rforall p, list_rel (match_val R p) * match_mem R p ++>
       set_rel (incr p (match_val R p * match_mem R p)))%rel.
    Proof.
      clear p1 p2 Hp1 Hp2.
      intros ecops1 ecops2 ccops1 ccops2.
      intros ge1 ge2 Hge κ sg p is1 [vargs2 m2] [Hvargs Hm] fs1 H.
      destruct H as [vargs1 m1 vres1 m1' sg Hsg H].
      subst.
      simpl in *.
      eapply (genv_sim_plus _ _ p) in Hge.

      -
        assert
          (Hs: state_match R (rexists i, fundef_le D1 D2 clight_funrel i) p
            (Callstate (Internal (InlinableFunction.function κ)) vargs1 Kstop m1)
            (Callstate (Internal (InlinableFunction.function κ)) vargs2 Kstop m2)).
        {
          eapply Callstate_rel; solve_monotonic; repeat constructor.
          exists 1%positive.
          econstructor.
          - instantiate (1 := inl κ).
            reflexivity.
          - instantiate (1 := inl κ).
            reflexivity.
          - constructor.
        }
        specialize (Hge _ _ Hs E0 _ H).
        destruct Hge as (s2' & Hs2' & p' & Hs'incr & Hs').
        inversion Hs'; clear Hs'; subst.
        destruct H5 as [H5 ?].
        inversion H5; clear H5; subst.
        eexpair.
        split.
        + instantiate (1 := y1).
          instantiate (1 := y).
          constructor.
          reflexivity.
          eapply Hs2'.
        + exists p'.
          split; eauto.
          split; eauto.
    Qed.

    Instance clight_cprimitive_match:
      let _ := cprimitive_extcall_ops D1 L1 in
      let _ := cprimitive_extcall_ops D2 L2 in
      let _ := cprimitive_cc_ops D1 L1 in
      let _ := cprimitive_cc_ops D2 L2 in
      Related
        (clight_cprimitive D1 L1)
        (clight_cprimitive D2 L2)
        (genv_sim R (rexists i, fundef_le D1 D2 clight_funrel i) ++> - ==> cprimitive_sim D1 D2 R)%rel.
    Proof.
      split.
      - intros p sg m1 m2 Hm fs1 H1.
        edestruct clight_cprimitive_step_match as (fs2 & Hfs1 & p' & Hfs_incr & Hfs); eauto.
        + eapply H1.
        + eexists.
          split.
          * eapply Hfs1.
          * exists p'.
            auto.
      - simpl. unfold incl; auto.
    Qed.

    (** Then, we show that [clight_sim] can also be use to establish a
      Compcert forward simulation for whole programs. In particular
      this will be used for the soundness proof. *)

    Require Import Smallstep.

    Lemma module_layer_le_program_le:
      program_le (fundef_le D1 D2 clight_funrel) p1 p2.
    Proof.
      cut (res_le (program_le (fundef_le D1 D2 clight_funrel)) (OK p1) (OK p2)).
      {
        inversion 1; subst; auto.
      }
      rewrite <- Hp1.
      rewrite <- Hp2.
      unfold program_le.
      monotonicity.
      eapply clight_module_layer_funrel.
    Qed.

    Definition clight_program_of_program types (p: AST.program fundef type) : res program :=
      make_program types (AST.prog_defs p) (AST.prog_public p) (AST.prog_main p).

    Lemma clight_program_of_program_eq' t p p':
      clight_program_of_program t p = OK p' ->
      exists ce (pf : (build_composite_env t = OK ce)),
        OK p' = OK {| prog_defs := AST.prog_defs p;
                    prog_public := AST.prog_public p;
                    prog_main := AST.prog_main p;
                    prog_types := t;
                    prog_comp_env := ce;
                    prog_comp_env_eq := pf |}.
    Proof.
      clear. intros.
      unfold clight_program_of_program, make_program in H.
      rewrite <- H.
      assert (forall (A B: Type)
                (x : res A)
                (a: A)
                (EQ: x = OK a)
                (F: forall α, OK α = x -> res B)
                (G: forall e, Error e = x -> res B)
                P
                (H: forall α Hα, P (F α Hα))
                (H': forall e He, P (G e He))
               ,
                 P
                   (match x as chi return chi = x -> res B with
                    | OK α => F α
                    | Error e => G e
                    end eq_refl)).
      intros. destruct x; auto. 
      refine (match build_composite_env t as x' return x' = build_composite_env t -> _ with
              | OK ce => _
              | Error e => _
              end eq_refl).
      intros.
      eapply X. eauto. eauto.
      intuition.

      assert (forall (A B: Type)
                (x : res A)
                a
                (EQ: x = Error a)
                (F: forall α, OK α = x -> res B)
                (G: forall e, Error e = x -> res B)
                P
                (H: forall α Hα, P (F α Hα))
                (H': forall e He, P (G e He))
               ,
                 P
                   (match x as chi return chi = x -> res B with
                    | OK α => F α
                    | Error e => G e
                    end eq_refl)).
      intros. destruct x; auto.
      intros. revert H. eapply X0; eauto.
      intuition.
    Qed.

    Lemma clight_program_of_program_eq t p p':
      clight_program_of_program t p = OK p' ->
      exists ce (pf : (build_composite_env t = OK ce)),
        p' = {| prog_defs := AST.prog_defs p;
                prog_public := AST.prog_public p;
                prog_main := AST.prog_main p;
                prog_types := t;
                prog_comp_env := ce;
                prog_comp_env_eq := pf |}.
    Proof.
      intros CPOP; eapply clight_program_of_program_eq' in CPOP.
      destruct CPOP as (ce' & pf & EQ). inv EQ. eauto.
    Qed.

    Lemma globalenv_cpop t p p':
      clight_program_of_program t p = OK p' ->
      Genv.globalenv p' = Genv.globalenv p.
    Proof.
      clear.
      intros CPOP.
      destruct (clight_program_of_program_eq _ _ _ CPOP) as (x & H & J). subst.
      unfold Genv.globalenv. f_equal.
    Qed.

    Lemma init_mem_cpop D t p p':
      clight_program_of_program t p = OK p' ->
      Genv.init_mem (memory_model_ops := mwd_ops D ) p' = Genv.init_mem p.
    Proof.
      clear.
      intros CPOP.
      destruct (clight_program_of_program_eq _ _ _ CPOP) as (x & H & J). subst.
      unfold Genv.init_mem, Genv.globalenv. f_equal.
    Qed.

    Lemma genv_public_add:
      forall {F V}  l (ge: Genv.t F V),
        Genv.genv_public (Genv.add_globals ge l) = Genv.genv_public ge.
    Proof.
      clear. induction l; simpl; intros; auto.
      rewrite IHl. reflexivity.
    Qed.

    Lemma find_symbol_add:
      forall {F V} s l (ge: Genv.t F V),
      (exists b, Genv.find_symbol ge s = Some b) \/ In s (map fst l) ->
      exists b, Genv.find_symbol (Genv.add_globals ge l) s = Some b.
    Proof.
      induction l; simpl; intros.
      - intuition.
      - apply IHl.
        destruct H.
        left. unfold Genv.find_symbol. simpl.
        rewrite PTree.gsspec.
        destruct (peq s (fst a)). eauto. apply H.
        destruct H.
        left. unfold Genv.find_symbol. simpl.
        rewrite PTree.gsspec.
        subst. rewrite peq_true. eauto. auto.
    Qed.

    Lemma public_symbol_globalenv:
      forall {F V} (p: AST.program F V) (INCL: incl (AST.prog_public p) (map fst (AST.prog_defs p))) i,
        Genv.public_symbol (Genv.globalenv p) i = in_dec ident_eq i (AST.prog_public p).
    Proof.
      clear. intros.
      unfold Genv.public_symbol, Genv.globalenv.
      rewrite genv_public_add. simpl.
      destruct (Genv.find_symbol (Genv.add_globals (Genv.empty_genv F V (AST.prog_public p)) (AST.prog_defs p)) i) eqn:?.
      - auto.
      - destruct (in_dec ident_eq i (AST.prog_public p)); auto.
        exfalso. destruct (find_symbol_add i (AST.prog_defs p) (Genv.empty_genv _ _ (AST.prog_public p))).
        right. apply INCL. auto. congruence.
    Qed.

    Lemma clight_fw types (TE: build_composite_env types = OK cenv) p1' p2':
      InitMemMakeProgram.module_layer_init_rel R (M1, L1) (M2, L2) ->
      clight_program_of_program types p1 = OK p1' ->
      clight_program_of_program types p2 = OK p2' ->
      forward_simulation
        (Clight.semantics2 (enable_builtins_instance := cprimitive_cc_ops D1 L1) p1')
        (Clight.semantics2 (enable_builtins_instance := cprimitive_cc_ops D2 L2) p2').
    Proof.
      intros INITREL CPOP1 CPOP2.
      eapply forward_simulation_plus with
        (match_states :=
           (rexists p, state_match R (rexists i, fundef_le D1 D2 clight_funrel i) p)%rel).
      - intros id. simpl.
        rewrite (globalenv_cpop _ _ _ CPOP1).
        rewrite (globalenv_cpop _ _ _ CPOP2).
        rewrite ! public_symbol_globalenv. 
        rewrite (make_program_public_eq _ _ _ _ _ _ _ _ Hp1 Hp2). auto.
        eapply make_program_public_incl; eauto.
        eapply make_program_public_incl; eauto.
      - intros s1 Hs1.
        destruct Hs1.
        generalize module_layer_le_program_le.
        intro PR.
        assert (simrel_program_rel R p1 p2) as PR_init.
        {
          cut (res_le (simrel_program_rel R) (MakeProgramSpec.make_program D1 (M1, L1)) (MakeProgramSpec.make_program D2 (M2, L2))).
          {
            rewrite Hp1.
            rewrite Hp2.
            inversion 1; subst; auto.
          }
          eapply InitMemMakeProgram.simrel_program_rel_intro.
          3: eapply clight_module_layer_funrel.
          {
            intro i.
            red.
            inversion 1; subst; auto; congruence.
          }
          {
            intros i f1 f2 Hf.
            inversion Hf.
            eapply make_clight_fundef_error; eauto.
          }
          assumption.
        }
        
        apply simrel_init_mem in PR_init.
        erewrite init_mem_cpop in H; eauto.
        rewrite H in PR_init.
        inversion PR_init as [ | ? m2 Hm _init2 INIT2 ]; subst; clear PR_init.
        destruct Hm as (w & Hm).
        generalize PR. intro PR_main.
        apply prog_main_rel in PR_main.
        apply genv_globalenv_rel in PR.
        rewrite stencil_matches_symbols in H0.
        Focus 2.
        + eapply genv_le_stencil_matches_l. unfold ge. erewrite globalenv_cpop. eauto. eauto.
        replace (prog_main p1') with (AST.prog_main p1) in H0.
        Focus 2.
        + destruct (clight_program_of_program_eq _ _ _ CPOP1) as (x & EQ1 & J). subst. reflexivity.
        rewrite PR_main in H0.
        generalize H0. intro H0_.
        erewrite <- stencil_matches_symbols in H0 by eauto using genv_le_stencil_matches_r.
        apply genv_rel_upto_glob_threshold in PR.
        eapply genv_rel_upto_find_funct_ptr in PR; eauto.
        unfold ge in H1.
        rewrite (globalenv_cpop _ _ _ CPOP1) in H1.
        setoid_rewrite H1 in PR.
        inversion PR; subst.
        exists (Callstate y nil Kstop m2).
        split.
        { econstructor; eauto.
          + rewrite INIT2. eapply init_mem_cpop; eauto.
          + rewrite <- H0.
            destruct (clight_program_of_program_eq _ _ _ CPOP2) as (x & EQ1 & J). subst. simpl. reflexivity.
          + erewrite globalenv_cpop; eauto.
          + 
            match goal with
              K: fundef_le _ _ _ _ _ _ |- _ =>
              inversion K; clear K; subst
            end.
            match goal with
              K: clight_funrel _ _ _,
                 U1: match_fundef D1 _ _ _,
                     U2: match_fundef D2 _ _ _ |- _ =>
              inversion K; subst; inversion U1; subst; inversion U2; subst; auto
            end.
            * Require Import Errors.
              Local Open Scope error_monad_scope.

              destruct (unique_csig D2 σ2) eqn:SIG2; try discriminate.
              simpl in H12. inv H12. simpl.
              destruct (unique_csig D1 σ1) eqn:SIG1; try discriminate.
              simpl in H11. inv H11. simpl in H2.
              
              match goal with
                K: sim _ _ _ |- _ =>
                simpl in K;
                  apply unique_csig_rel in K
              end.
              match goal with
                K: res_le _ (unique_csig D1 ?u) _,
                   E: unique_csig D1 ?u = _ |- _ =>
                rewrite E in K;
                  unfold ret in K;
                  simpl in K;
                  inversion K;
                  unfold ret in *;
                  simpl in *;
                  congruence
              end.
            * destruct (unique_csig D1 σ1) eqn:SIG1; try discriminate.
              simpl in H12. inv H12.
              match goal with
                K: sim _ _ _ |- _ =>
                simpl in K;
                  apply unique_csig_rel in K
              end.
              simpl.
              match goal with
                K: res_le _ (unique_csig D1 ?u) _,
                   E: unique_csig D1 ?u = _ |- _ =>
                rename K into Hsig;
                  rename E into SIG1
              end.
              rewrite SIG1 in Hsig.
              match goal with
                K: get_layer_primitive _ (〚 _ 〛 _) = _ |- _ =>
                rename K into PRIM2
              end.
              unfold clight_semantics_ops, clayer_ops, cmodule_ops in PRIM2.
              rewrite PTreeSemantics.ptree_get_semof_primitive in PRIM2.
              match goal with
                K: get_module_function _ _ = _ |- _ =>
                rename K into FUN2
              end.
              unfold cmodule_ops in FUN2.
              rewrite FUN2 in PRIM2.
              revert PRIM2.
              unfold semof_function.
              monad_norm.
              unfold semof_fundef.
              unfold clight_function_semantics_ops.
              rewrite (make_program_make_globalenv _ _ _ Hp2).
              monad_norm.
              simpl.
              setoid_rewrite HL2i.
              inversion 1; subst.
              simpl in Hsig.
              rewrite unique_csig_clight_cprimitive in Hsig.
              inversion Hsig; subst.
              unfold ret in *.
              simpl in *.
              destruct κ2 as [ ? [] ]; simpl in * |- * .
              unfold type_of_function. simpl. congruence.
        }
        exists w.
        constructor; auto; try now repeat constructor.
        esplit; eauto.
      - intros s1 s2 r [p Hs] H.
        destruct H.
        inversion Hs; clear Hs; subst.
        inversion H2; clear H2; subst.
        destruct H4 as [H4 ?].
        inversion H4; clear H4; subst.
        constructor.
      - simpl.
        intros s1 t s1' Hstep.
        simpl in *.
        intros s2 (p & Hs2).
        pose (cprimitive_extcall_ops D1 L1) as ec_ops_1.
        pose (cprimitive_extcall_ops D2 L2) as ec_ops_2.
        pose (cprimitive_cc_ops D1 L1) as cc_ops_1.
        pose (cprimitive_cc_ops D2 L2) as cc_ops_2.
        apply (clight_sim R (ec1_ops := ec_ops_1) (ec2_ops := ec_ops_2) (eb1 := cc_ops_1) (eb2 := cc_ops_2)) in Hs2. auto.
        + specialize (Hs2 t s1').
          unfold Clight.globalenv in Hstep.
          rewrite (globalenv_cpop _ _ _ CPOP1) in Hstep.
          destruct (clight_program_of_program_eq _ _ _ CPOP1) as (x & EQ1 & J). subst. simpl in *.
          generalize TE; intro TE'.
          rewrite EQ1 in TE. inv TE.
          specialize (Hs2 Hstep).
          destruct Hs2 as (? & ? & ? & ? & ?).
          esplit.
          split; eauto.
          unfold Clight.globalenv.
          rewrite (globalenv_cpop _ _ _ CPOP2).
          destruct (clight_program_of_program_eq _ _ _ CPOP2) as (x2 & EQ2 & J2). subst. simpl in *.
          rewrite EQ2 in TE'. inv TE'.
          eauto.
          esplit.
          eassumption.
        + constructor. eapply genv_globalenv_rel.
          assert (res_le (program_le (fundef_le D1 D2 clight_funrel)) (OK p1) (OK p2)).
          {
            rewrite <- Hp1.
            rewrite <- Hp2.
            unfold program_le.
            monotonicity.
            eapply clight_module_layer_funrel.
          }
          inversion H; clear H; subst.
          assumption.
    Qed.
  End CLIGHT_MONOT.

  Instance res_le_transport {A B} (R: rel A B) (x: res A) (y: res B) (b: B):
    Transport (res_le R) x y (y = OK b) (exists a, x = OK a /\ R a b).
  Proof.
    intros H Hy.
    destruct H; try congruence.
    inversion Hy; clear Hy; subst.
    exists x; eauto.
  Qed.

  Lemma res_option_inj_inv {A B} (x: res (option A)) (y: res (option B)):
    (x = OK None /\ y = OK None /\ res_option_inj x y = OK None) \/
    (exists t, x = OK (Some t) /\ y = OK None /\ res_option_inj x y = OK (Some (inl t))) \/
    (exists t, x = OK None /\ y = OK (Some t) /\ res_option_inj x y = OK (Some (inr t))) \/
    (exists e, res_option_inj x y = Error e).
  Proof.
    unfold res_option_inj.
    clear.
    destruct x as [ [ | ] | ]; destruct y as [ [ | ] | ]; simpl; eauto;
    intuition eauto.
  Qed.


  Global Instance clight_function_semantics_prf:
    FunctionSemantics ident function cprimitive (globvar type)
      (ptree_module _ _)
      (ptree_layer _ _).
  Proof.
    split.
    - intros D1 D2 R ML1 ML2 HML i κ.
      inversion HML as [M1 M2 L1 L2 HM HL HL2wf HML2ok]; subst.
      simpl.
      destruct (make_globalenv D2 (M2, L2)) as [ge2 | ] eqn:Hge2.
      2: constructor.
      generalize (make_globalenv_make_program (M2, L2) _ Hge2).
      destruct 1 as (p2 & Hp2).
      assert (isOK (MakeProgramSpec.make_program _ (M1, L1))) as P1.
      {
        assert (exists r, res_le r (MakeProgramSpec.make_program _ (M1, L1)) (MakeProgramSpec.make_program _ (M2, L2))) as P1.
        {
          exploit (foodef_rel_mpr D1 D2
                                  (fun i => option_le (clight_funrel D1 D2 R L1 M2 L2 i)) 
                                  (fun i => option_le ⊤)).
          {
            intros j x y Hxy.
            eapply make_clight_fundef_error.
            inversion Hxy.
            eassumption.
          }
          intro RELS.
          esplit.
          eapply make_program_rel; eauto.
          clear i.
          intro i; split.
          + unfold get_module_layer_function; simpl.
            generalize (get_layer_primitive_sim_monotonic _ _ _ i _ _ HL).
            unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
            rewrite ptree_get_semof_primitive.
            intro LE.
            generalize (res_option_inj_inv (get_module_function i M2) (get_layer_primitive i L2)).
            destruct 1 as [ (Hm2 & Hl2 & RES) | [
                              (f & Hm2 & Hl2 & RES) | [
                                (v & Hm2 & Hl2 & RES) |
                                (e & RES)
                          ]]];
              unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * ;
              rewrite RES;
            clear RES;
            (try rewrite Hm2 in LE);
            (try rewrite Hl2 in LE);
            simpl in LE;
            try now constructor.
            Local Remove Hints lower_bound : typeclass_instances.
            - transport Hm2.
              unfold semof_function in LE.
              monad_norm.
              inversion LE; subst.
              repeat
              match goal with
                  K: option_le _ _ None |- _ =>
                  inversion K; clear K; subst
              end.
              match goal with
                  K: ptree_module_function i M1 = _ |- _ =>
                  setoid_rewrite K
              end.
              constructor.
              constructor.
            - unfold semof_function in LE.
              monad_norm.
              unfold semof_fundef in LE.
              simpl in LE.
              unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
              rewrite Hge2 in LE.
              monad_norm.
              generalize Hm2. intro Hm2_.
              transport Hm2.
              match goal with
                  K: ptree_module_function i M1 = _ |- _ =>
                  setoid_rewrite K
              end.
              inversion LE; subst; simpl;
              (repeat
                match goal with
                    K: option_le _ _ (Some _) |- _ =>
                    inversion K; clear K; subst
                end);
              try now repeat constructor.
              * repeat constructor.
                econstructor; eauto.
                setoid_rewrite ptree_get_semof_primitive.
                setoid_rewrite Hl2.
                rewrite id_right.
                rewrite Hm2_.
                unfold semof_function.
                monad_norm.
                simpl.
                setoid_rewrite Hge2.
                reflexivity.
              * edestruct @modules_layers_function_primitive_ok; eauto.
            - transport Hm2.
              match goal with
                  K: option_le _ _ None |- _ =>
                  inversion K; clear K; subst
              end.
              match goal with
                  K: ptree_module_function i M1 = _ |- _ =>
                  setoid_rewrite K
              end.
              inversion LE; subst.
              simpl.
              match goal with
                  K: OK ?u = get_layer_primitive i L1 |- _ =>
                  destruct u; try now (repeat constructor)
              end.
              constructor.
              constructor.
              constructor; eauto.
              inversion H2; eauto.
          + unfold get_module_layer_variable.
            unfold fst. unfold snd.
            generalize (get_layer_globalvar_sim_monotonic _ _ _ i _ _ HL).
            unfold clight_semantics_ops, clayer_ops, cmodule_ops in * |- * .
            rewrite ptree_get_semof_globalvar.
            intro LE.
            simpl.
            cut (res_le (option_le eq)
                        (get_module_variable i M1 ⊕ get_layer_globalvar i L1)
                        (get_module_variable i M2 ⊕ get_layer_globalvar i L2)).
            {
              unfold clayer_ops, cmodule_ops.
              inversion 1; subst;
              try
              match goal with
                K: option_le _ _ _ |- _ =>
                inversion K; subst
              end;
              repeat constructor.
            }
            apply GlobalVars.res_option_globalvar_lub; auto.
            destruct (get_module_variable i M2) as [ [ g | ] | ] eqn:Hm2;
              try
                (transport Hm2;
                 match goal with
                   K: ptree_module_variable i M1 = _ |- _ =>
                   setoid_rewrite K
                 end);
              res_option_globalvar_red;
              try now constructor.
            - destruct (get_layer_globalvar i L2) as [ [ g0 | ] | ];
              res_option_globalvar_red;
              try constructor; auto.
              destruct (globalvar_eq_dec g g0).
              {
                subst.
                autorewrite with res_option_globalvar.
                constructor; auto.
              }
              rewrite res_option_globalvar_oplus_diff by assumption.
              constructor.
            - match goal with
                K: option_le _ _ _ |- _ =>
                inversion K; subst
              end.
              apply oplus_lower_bound.
        }
        destruct P1 as (_R & Hp1).
        rewrite Hp2 in Hp1.
        inversion Hp1; subst.
        esplit; eauto.
      }
      destruct P1 as (p1 & Hp1).
      pose proof Hge2 as Hge1.
      eapply transport in Hge1.
      2: instantiate (1 := (make_globalenv D1 (M1, L1))).
      2: instantiate (1 := genv_le (fundef_le D1 D2 (clight_funrel D1 D2 R L1 M2 L2))).
      2: monotonicity.
      2: eapply clight_module_layer_funrel; eauto.
    *
      split_hyp Hge1.
      rewrite H.
      monad_norm. simpl. 
      constructor.
      split. 
      + eapply clight_cprimitive_match.
        eapply clight_sim; eauto.
        unfold make_globalenv in *.
        inv_monad Hge2.
        inv_monad H; subst.
        eapply clight_funrel_prf; eauto.
        constructor. auto.
      + simpl.
        unfold incl; auto.
  Qed.

  Global Instance clight_semantics_basics_prf:
    Semantics.Semantics _ function cprimitive (globvar type) cmodule clayer.
  Proof.
    apply ptree_semof_prf.
  Qed.

  (** TODO: here we should be able to prove vertical composition as
    well. To do that we could modify [FunctionSemantics] to use the
    generalized notion of monotonicity and let [PTreeSemantics] do the
    rest. But this would break the existing code so maybe we want to
    start with adding hlper lemmas there. *)

  (** And now, the soundness proof. *)

  Require Import LayerLogicImpl.

  (* Instance LayerLogicOps (simrel := simrel) ident function cprimitive (globvar type) cmodule clayer) := _. *)

  Lemma soundness_fw D1 D2 (R: simrel D1 D2) (LL: clayer D2) (M: cmodule) (LH: clayer D1) ph pl:
    InitMemMakeProgram.module_layer_init_rel R (∅, LH) (M, LL) ->
    LL ⊢ (R, M) : LH ->
    forall CTXT,
      (forall i, ~ isOKNone (get_module_variable i CTXT) ->
                 ~ isOKNone (get_module_layer_variable i (M, LL)) ->
                 ~ In i (map fst (simrel_new_glbl R))) ->
      MakeProgramSpec.make_program D1 (CTXT, LH) = OK ph ->
      MakeProgramSpec.make_program D2 (CTXT ⊕ M, LL) = OK pl ->
      forall types (TE: build_composite_env types = OK cenv) ph' pl' ,
        clight_program_of_program types ph = OK ph' ->
        clight_program_of_program types pl = OK pl' ->
      forward_simulation
        (Clight.semantics2 (enable_builtins_instance := cprimitive_cc_ops D1 LH) ph')
        (Clight.semantics2 (enable_builtins_instance := cprimitive_cc_ops D2 LL) pl').
  Proof.
    intros HINITREL HLM CTXT HCTXT_COMPAT Hph Hpl.
    intros types TEQ ph' pl' CPOPh CPOPl.
    eapply clight_fw; eauto.
    {
      apply oplus_le_left.
    }
    htransitivity (〚M〛 LL).
    - exact HLM.
    - (* solve_monotonic idtac. # loops forever, module_layer_sim *)
      apply semof_monotonic.
      apply layer_sim_module_layer_sim.
      split.
      + simpl. apply right_upper_bound.
      + split.
        { instantiate (1 := id). reflexivity. }
        { (* rsat *) exact I. }
    - simpl.
      assert (
          InitMemMakeProgram.module_layer_init_rel R
                                                   (CTXT ⊕ ∅, LH) (CTXT ⊕ M, LL)
        ) as HINITREL'.
      { apply InitMemMakeProgram.module_layer_init_rel_context; auto. }
      clear HINITREL.
      revert HINITREL' .
      apply InitMemMakeProgram.module_layer_init_rel_ext; auto.
      + symmetry. apply simrel_compose_id_left.
      + intro i.
        unfold get_module_layer_function.
        simpl.
        rewrite get_module_function_oplus.
        rewrite get_module_function_empty.
        match goal with
          |- context [ ?u ⊕ OK None ] =>
          replace (u ⊕ OK None) with u; auto
        end.
        destruct (get_module_function i CTXT) as [ [ | ] | ] ; auto.
      + intro i.
        unfold get_module_layer_variable.
        simpl.
        rewrite get_module_variable_oplus.
        rewrite get_module_variable_empty.
        GlobalVars.res_option_globalvar_red.
        reflexivity.
  Qed.

(** Receptiveness of whole-machine ClightX for LayerLib C-style
    primitives.

    Here, we need to weaken the hypotheses of
    [compcert.cfrontend.Clight.semantics_receptive], which assume that
    functions satisfy all external function properties. In fact, we
    only need [ec_receptive] and [ec_trace_length], which are related
    to the event trace, and thus trivially hold since LayerLib
    primitives produce no events. *)

  (* Context `{Hnorepet: !CompCertBuiltins.BuiltinIdentsNorepet}. *)

  Context {SI: SymbolsInject}.

  Theorem semantics_receptive D L p:
    Smallstep.receptive
      (Clight.semantics2 (enable_builtins_instance := cprimitive_cc_ops D L) p).
  Proof.
    constructor.
    + intros s t1 s1 t2 H H0.
      inversion H; subst; (try now (inversion H0; subst; eauto));
      exploit CPrimitives.external_call_receptive; eauto;
      destruct 1 as (? & ? & ?);
      esplit;
      econstructor; eauto.
    + unfold single_events.
      intros s t s' H.
      inversion H; subst; (try now (simpl; auto with arith));
      eapply CPrimitives.external_call_trace_length; eauto.
  Qed.

End SEMANTICS.


(** Determinacy of whole-machine ClightX when primitives satisfy
    external function properties. *)

Section WITHCOMPILERCONFIG.
  Context `{Hcfg: ExternalCalls}.

  Lemma assign_loc_determ ge ty m loc ofs v m1 m2:
    assign_loc ge ty m loc ofs v m1 ->
    assign_loc ge ty m loc ofs v m2 ->
    m1 = m2.
  Proof.
    inversion 1;
    inversion 1;
    congruence.
  Qed.

  Lemma deref_loc_determ ty m b o v1 v2:
    deref_loc ty m b o v1 ->
    deref_loc ty m b o v2 ->
    v1 = v2.
  Proof.
    inversion 1;
    inversion 1;
    congruence.
  Qed.

  Lemma eval_expr_lvalue_determ (genv: Clight.genv) (env: env) (tenv: temp_env) (m: mem0):
    (forall e v1,
       eval_expr genv env tenv m e v1 ->
       forall v2,
         eval_expr genv env tenv m e v2 ->
         v1 = v2) /\
    (forall e b1 o1,
       eval_lvalue genv env tenv m e b1 o1 ->
       forall b2 o2,
         eval_lvalue genv env tenv m e b2 o2 ->
         (b1, o1) = (b2, o2)).
  Proof.
    apply eval_expr_lvalue_ind;
    try now
        ( inversion 1; subst;
          (try congruence);
          try (match goal with K: eval_lvalue _ _ _ _ _ _ _ |- _ =>
                               now inversion K
               end)
        ).
    *
        ( inversion 2; subst;
          (try congruence);
          try (match goal with K: eval_lvalue _ _ _ _ _ _ _ |- _ =>
                               now inversion K
               end)
        ).
    * intros a ty loc ofs H H0 v2 H1.
      inversion H1; subst.
      + exploit H0; eauto.
        congruence.
      + clear H.
        match goal with K: eval_lvalue _ _ _ _ _ _ _ |- _ =>
                        now inversion K
        end.
    * intros op a ty v1 v H H0 H1 v2 H2.
      inversion H2; subst.
      + exploit H0; eauto.
        congruence.
      + match goal with K: eval_lvalue _ _ _ _ _ _ _ |- _ =>
                        now inversion K
        end.
    * intros op a1 a2 ty v1 v2 v H H0 H1 H2 H3 v0 H4.
      inversion H4; subst.
      + exploit H0; eauto.
        exploit H2; eauto.
        congruence.
      + match goal with K: eval_lvalue _ _ _ _ _ _ _ |- _ =>
                        now inversion K
        end.
    * intros a ty v1 v H H0 H1 v2 H2.
      inversion H2; subst.
      + exploit H0; eauto.
        congruence.
      + match goal with K: eval_lvalue _ _ _ _ _ _ _ |- _ =>
                        now inversion K
        end.
    * intros a loc ofs v H H0 H1 v2 H2. 
      inversion H2; subst; try now inversion H.
      exploit H0; eauto.
      inversion 1; subst.
      eapply deref_loc_determ; eauto. 
    * inversion 2; congruence.
    * inversion 3; congruence.
    * intros a ty l ofs H H0 b2 o2 H1.
      inversion H1; subst.
      exploit H0; eauto.
      congruence.
    * intros a i ty l ofs id co fList att delta H H0 H1 H2 b2 o2 H3.
      inversion H3; subst; try congruence.
      exploit H; eauto.
      congruence.
    * intros a i ty l ofs id co fList att H H0 H1 b2 o2 H2.
      inversion H2; subst; try congruence.
      exploit H; eauto.
      congruence.
  Qed.

  Lemma eval_expr_determ (genv: Clight.genv) (env: env) (tenv: temp_env) (m: mem0):
    (forall e v1,
       eval_expr genv env tenv m e v1 ->
       forall v2,
         eval_expr genv env tenv m e v2 ->
         v1 = v2).
  Proof.
    exact (proj1 (eval_expr_lvalue_determ _ _ _ _)).
  Qed.

  Lemma eval_lvalue_determ (genv: Clight.genv) (env: env) (tenv: temp_env) (m: mem0):
    (forall e b1 o1,
       eval_lvalue genv env tenv m e b1 o1 ->
       forall b2 o2,
         eval_lvalue genv env tenv m e b2 o2 ->
         (b1, o1) = (b2, o2)).
  Proof.
    exact (proj2 (eval_expr_lvalue_determ _ _ _ _)).
  Qed.

  Ltac eval_expr_lvalue_determ :=
    match goal with
        K1: eval_expr ?genv ?env ?tenv ?m ?e ?v1,
        K2: eval_expr ?genv ?env ?tenv ?m ?e ?v2
        |- _ =>
        generalize (eval_expr_determ genv env tenv m e v1 K1 v2 K2);
          clear K1 K2;
          intro; subst
      |
        K1: eval_lvalue ?genv ?env ?tenv ?m ?e ?b1 ?o1,
        K2: eval_lvalue ?genv ?env ?tenv ?m ?e ?b2 ?o2
        |- _ =>
        generalize (eval_lvalue_determ genv env tenv m e b1 o1 K1 b2 o2 K2);
          clear K1 K2;
          let K := fresh in
          intro K; inversion K; clear K; subst
    end.

  Lemma eval_exprlist_determ (genv: Clight.genv) (env: env) (tenv: temp_env) (m: mem0):
    forall el tyl vl1,
      eval_exprlist genv env tenv m el tyl vl1 ->
      forall vl2,
        eval_exprlist genv env tenv m el tyl vl2 ->
        vl1 = vl2.
  Proof.
    induction 1; inversion 1; subst; auto.
    f_equal; eauto.
    eval_expr_lvalue_determ.
    congruence.
  Qed.

  Lemma alloc_variables_determ ge e m:
    forall l e1 m1,
      alloc_variables ge e m l e1 m1 ->
      forall e2 m2,
        alloc_variables ge e m l e2 m2 ->
        e1 = e2 /\ m1 = m2.
  Proof.
    clear Hcfg.
    induction 1; inversion 1; subst; auto.
    eapply IHalloc_variables; eauto.
    congruence.
  Qed.

  Lemma function_entry2_determ ge f vargs m e1 le1 m1 e2 le2 m2:
    function_entry2 ge f vargs m e1 le1 m1 ->
    function_entry2 ge f vargs m e2 le2 m2 ->
    le1 = le2 /\ e1 = e2 /\ m1 = m2.
  Proof.
    inversion 1; subst.
    inversion 1; subst.
    split.
    + congruence.
    + eapply alloc_variables_determ; eauto.
  Qed.

  Ltac eval_determ :=

    match goal with
        _ => eval_expr_lvalue_determ
      |
        K1: assign_loc ?ge ?ty ?m ?loc ?ofs ?v ?m1,
        K2: assign_loc ?ge ?ty ?m ?loc ?ofs ?v ?m2
        |- _ =>
        generalize (assign_loc_determ ge ty m loc ofs v m1 m2 K1 K2);
          clear K1 K2;
          intro; subst
      |
        K1: deref_loc ?ty ?m ?b ?o ?v1,
        K2: deref_loc ?ty ?m ?b ?o ?v2
        |- _ =>
        generalize (deref_loc_determ ty m b o v1 v2 K1 K2);
          clear K1 K2;
          intro; subst
      |
        K1: ?a = Some ?b1,
        K2: ?a = Some ?b2
        |- _ =>
        assert (b1 = b2) by congruence;
          clear K1 K2;
          subst
      |
        K1: ?a = Cop.fun_case_f ?tyargs1 ?tyres1 ?cconv1,
        K2: ?a = Cop.fun_case_f ?tyargs2 ?tyres2 ?cconv2
        |- _ =>
        let K := fresh in
        assert (tyargs1 = tyargs2 /\ tyres1 = tyres2 /\ cconv1 = cconv2)
          as K
            by ((repeat split); clear Hcfg; congruence);
        clear K1 K2;
        destruct K as (? & ? & ?);
        subst
      |
        K1: eval_exprlist ?genv ?env ?tenv ?m ?el ?tyl ?vl1,
        K2: eval_exprlist ?genv ?env ?tenv ?m ?el ?tyl ?vl2
        |- _ =>
        generalize (eval_exprlist_determ genv env tenv m el tyl vl1 K1 vl2 K2);
          clear K1 K2;
          intro; subst
      |
        K: Vint ?u = Vint ?v
        |- _ =>
        inversion K; clear K; subst
      |
        K: (_, _) = (_, _)
        |- _ =>
        inversion K; clear K; subst
      |
        K1: function_entry2 ?ge ?f ?vargs ?m ?e1 ?le1 ?m1,
        K2: function_entry2 ?ge ?f ?vargs ?m ?e2 ?le2 ?m2
        |- _ =>
        generalize (function_entry2_determ ge f vargs m e1 le1 m1 e2 le2 m2 K1 K2);
          clear K1 K2;
          destruct 1 as (? & ? & ?);
          subst
    end.

  Theorem semantics_determinate p:
    Smallstep.determinate
      (Clight.semantics2 p).
  Proof.
    constructor.
    + inversion 1; subst;
      try now (
            inversion 1; subst; (try now (clear Hcfg; intuition discriminate));
            (try contradiction);
            (repeat eval_determ);
            clear; intuition constructor
          ).
      * inversion 1; subst; (try now (clear Hcfg; intuition discriminate)).
        repeat eval_determ.
        match goal with
            K1: external_call _ _ _ _ ?u1 _ _,
            K2: external_call _ _ _ _ ?u2 _ _
          |- match_traces _ ?u1 ?u2 /\ _ =>
            generalize (external_call_determ _ _ _ _ _ _ _ _ _ _ K1 K2)
        end.
        destruct 1 as (? & U).
        split; auto.
        intro; subst.
        destruct U; subst; auto.
      * inversion 1; subst; (try now (clear Hcfg; intuition discriminate)).
        repeat eval_determ.
        match goal with
            K1: external_call _ _ _ _ ?u1 _ _,
            K2: external_call _ _ _ _ ?u2 _ _
          |- match_traces _ ?u1 ?u2 /\ _ =>
            generalize (external_call_determ _ _ _ _ _ _ _ _ _ _ K1 K2)
        end.
        destruct 1 as (? & U).
        split; auto.
        intro; subst.
        destruct U; subst; auto.
    + unfold single_events.
      inversion 1; subst; simpl; eauto using external_call_trace_length with arith.
    + inversion 1; subst.
      inversion 1; subst.
      unfold ge in *.
      unfold ge0 in *.
      congruence.
    + inversion 1; subst.
      unfold nostep.
      intros t s'.
      intro ABSURD.
      inversion ABSURD.
    + inversion 1; inversion 1; congruence.
  Qed.

End WITHCOMPILERCONFIG.

Section BACKWARD_SIMULATION.
  Context
    `{Hmem: BaseMemoryModel}
    (* {Hmwd: UseMemWithData mem} *)
    (* {res_id: I64helpers.ReservedId} *)
    `{mkp_prf: MakeProgram}
    (* `{Hnorepet: !CompCertBuiltins.BuiltinIdentsNorepet} *).

  Existing Instance meminj_preserves_globals'_instance.

  Lemma soundness_bw
        D1 D2 (R: simrel D1 D2) (LL: clayer D2) (M: cmodule) (LH: clayer D1) ph pl:
    ForallPrimitive D2 (CPrimitiveExtcallProperties D2) LL ->
    InitMemMakeProgram.module_layer_init_rel R (∅, LH) (M, LL) ->
    LL ⊢ (R, M) : LH ->
    forall CTXT,
      (forall i, ~ isOKNone (get_module_variable i CTXT) ->
                 ~ isOKNone (get_module_layer_variable i (M, LL)) ->
                 ~ In i (map fst (simrel_new_glbl R))) ->
      MakeProgramSpec.make_program D1 (CTXT, LH) = OK ph ->
      MakeProgramSpec.make_program D2 (CTXT ⊕ M, LL) = OK pl ->
       forall types (TE: build_composite_env types = OK cenv) ph' pl' ,
        clight_program_of_program types ph = OK ph' ->
        clight_program_of_program types pl = OK pl' ->
      backward_simulation
        (Clight.semantics2 (enable_builtins_instance := cprimitive_cc_ops D1 LH) ph')
        (Clight.semantics2 (enable_builtins_instance := cprimitive_cc_ops D2 LL) pl').
  Proof.
    intros H H0 H1 CTXT H2 H3 H4 types TEQ ph' pl'  CPOPh CPOPl.
    apply Smallstep.forward_to_backward_simulation.
    + eapply soundness_fw; eauto.
    + apply semantics_receptive.
    + pose proof cprimitive_ec_props.
      apply semantics_determinate.
  Qed.

End BACKWARD_SIMULATION.
