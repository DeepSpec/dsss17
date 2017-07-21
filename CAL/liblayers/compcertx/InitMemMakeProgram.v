Require Export MakeProgramFacts.
Require Export SimulationRelation.


(** * Prerequisites *)

(** Some extra definitions and lemmas related to [make_program]. *)

Section MODULE_LAYER_ACCESS.
  Context `{Hpf: ProgramFormat}.

  Lemma get_module_layer_function_ok_none {D} i (ML: module * layer D):
    isOKNone (get_module_layer_function i ML) <->
    (isOKNone (get_module_function i (fst ML)) /\ isOKNone (get_layer_primitive i (snd ML))).
  Proof.
    unfold isOKNone.
    unfold get_module_layer_function.
    split.
    + destruct (get_module_function _ _) as [ [ | ] | ] ;
      destruct (get_layer_primitive _ _) as [ [ | ] | ] ;
      simpl;
      clear;
      intuition congruence.
    + destruct 1 as (HM & HL).
      rewrite HM.
      rewrite HL.
      reflexivity.
  Qed.

  Lemma get_module_layer_function_dec_aux
        {D} (P: _ -> Prop) ML:
    ((forall i,
        get_module_function i (fst ML) <> OK None ->
        P i) /\
     (forall i,
        get_layer_primitive i (snd ML) <> OK None ->
        P i)) <->
    (forall i, get_module_layer_function (D := D) i ML <> OK None -> P i).
  Proof.
    split.
    + destruct 1 as (HM & HL).
      intro i.
      specialize (HM i).
      specialize (HL i).
      revert HM HL.
      repeat
        match goal with
            |- context [ ?u <> OK None ] =>
            replace (u <> OK None) with (~ isOKNone u)
              by reflexivity
        end.
      rewrite get_module_layer_function_ok_none.
      clear.
      tauto.
    + intro HML; split; intro i;
      specialize (HML i);
      revert HML;
      (repeat
         match goal with
             |- context [ ?u <> OK None ] =>
             replace (u <> OK None) with (~ isOKNone u)
               by reflexivity
         end);
      rewrite get_module_layer_function_ok_none;
      clear;
      tauto.
  Qed.

  Global Instance get_module_layer_function_dec
        `{Hmodules: !Modules ident Fm (globvar Vm) module}
        `{Hlayers: !Layers ident primsem (globvar Vm) layer}
        {D} (P: _ -> Prop):
    (forall i, Decision.Decision (P i)) ->
    forall ML,
      Decision.Decision (forall i, get_module_layer_function (D := D) i ML <> OK None -> P i).
  Proof.
    intros X ML.
    eapply Decision.decide_rewrite.
    { apply get_module_layer_function_dec_aux. }
    typeclasses eauto.
  Defined.

  Lemma get_module_layer_variable_ok_none {D} i (ML: module * layer D):
    isOKNone (get_module_layer_variable i ML) <->
    (isOKNone (get_module_variable i (fst ML)) /\ isOKNone (get_layer_globalvar i (snd ML))).
  Proof.
    unfold isOKNone.
    unfold get_module_layer_variable.
    split.
    + destruct (get_module_variable _ _) as [ [ gm | ] | ] ;
      destruct (get_layer_globalvar _ _) as [ [ gl | ] | ] ;
      simpl;
      clear;
      GlobalVars.res_option_globalvar_red;
      try intuition congruence.
      destruct (Decision.decide (gm = gl)).
      - subst.
        GlobalVars.res_option_globalvar_red.
        intuition congruence.
      - rewrite GlobalVars.res_option_globalvar_oplus_diff by assumption.
        intuition congruence.
    + destruct 1 as (HM & HL).
      rewrite HM.
      rewrite HL.
      reflexivity.
  Qed.

  Lemma get_module_layer_variable_dec_aux
        {D} (P: _ -> Prop) ML:
    ((forall i,
        get_module_variable i (fst ML) <> OK None ->
        P i) /\
     (forall i,
        get_layer_globalvar i (snd ML) <> OK None ->
        P i)) <->
    (forall i, get_module_layer_variable (D := D) i ML <> OK None -> P i).
  Proof.
    split.
    + destruct 1 as (HM & HL).
      intro i.
      specialize (HM i).
      specialize (HL i).
      revert HM HL.
      repeat
        match goal with
            |- context [ ?u <> OK None ] =>
            replace (u <> OK None) with (~ isOKNone u)
              by reflexivity
        end.
      rewrite get_module_layer_variable_ok_none.
      clear.
      tauto.
    + intro HML; split; intro i;
      specialize (HML i);
      revert HML;
      (repeat
         match goal with
             |- context [ ?u <> OK None ] =>
             replace (u <> OK None) with (~ isOKNone u)
               by reflexivity
         end);
      rewrite get_module_layer_variable_ok_none;
      clear;
      tauto.
  Qed.

  Global Instance get_module_layer_variable_dec
        `{Hmodules: !Modules ident Fm (globvar Vm) module}
        `{Hlayers: !Layers ident primsem (globvar Vm) layer}
        {D} (P: _ -> Prop):
    (forall i, Decision.Decision (P i)) ->
    forall ML,
      Decision.Decision (forall i, get_module_layer_variable (D := D) i ML <> OK None -> P i).
  Proof.
    intros X ML.
    eapply Decision.decide_rewrite.
    { apply get_module_layer_variable_dec_aux. }
    typeclasses eauto.
  Defined.
End MODULE_LAYER_ACCESS.

Section RELATIONS.
  Context {ld1 Fm1 Vm1 Fp1 Vp1 module1 primsem1 layer1}
    `{pf_ops1: ProgramFormatOps ld1 Fm1 Vm1 Fp1 Vp1 module1 primsem1 layer1}.
  Context {ld2 Fm2 Vm2 Fp2 Vp2 module2 primsem2 layer2}
    `{pf_ops2: ProgramFormatOps ld2 Fm2 Vm2 Fp2 Vp2 module2 primsem2 layer2}.

  Lemma option_relation_forward_function_strong D1 D2 (RF: funrel D1 D2) ML1 ML2:
    (forall i, OptionRelationForward (RF i)) ->
    (forall i, OptionRelationForward (fun f1 f2 =>
                                        RF i f1 f2 /\
                                        get_module_layer_function i ML1 = OK f1 /\
                                        get_module_layer_function i ML2 = OK f2)).
  Proof.
    intros H i.
    specialize (H i).
    revert H.
    unfold OptionRelationForward.
    clear.
    firstorder.
  Qed.

  Lemma option_relation_forward_variable_strong D1 D2 (RV: varrel) (ML1: _ * _ D1) (ML2: _ * _ D2):
    (forall i, OptionRelationForward (RV i)) ->
    (forall i, OptionRelationForward (fun f1 f2 =>
                                        RV i f1 f2 /\
                                        get_module_layer_variable i ML1 = OK f1 /\
                                        get_module_layer_variable i ML2 = OK f2)).
  Proof.
    intros H i.
    specialize (H i).
    revert H.
    unfold OptionRelationForward.
    clear.
    firstorder.
  Qed.

  Definition module_layer_rel_strong (D1: ld1) (D2: ld2)
             (RF: funrel D1 D2) (RV: varrel (Vm1:=Vm1) (Vm2:=Vm2))
             (ML1: module1 × layer1 D1) (ML2: module2 × layer2 D2):
    Prop :=
    module_layer_rel D1 D2
                     (fun i f1 f2 =>
                        RF i f1 f2 /\
                        get_module_layer_function i ML1 = OK f1 /\
                        get_module_layer_function i ML2 = OK f2)
                     (fun i v1 v2 =>
                        RV i v1 v2 /\
                        get_module_layer_variable i ML1 = OK v1 /\
                        get_module_layer_variable i ML2 = OK v2)
                     ML1 ML2.

  Lemma module_layer_rel_strengthen (D1: ld1) (D2: ld2)
        (RF: funrel D1 D2) (RV: varrel (Vm1:=Vm1) (Vm2:=Vm2))
        (ML1: module1 × layer1 D1) (ML2: module2 × layer2 D2):
    module_layer_rel D1 D2 RF RV ML1 ML2 ->
    module_layer_rel_strong D1 D2 RF RV ML1 ML2.
  Proof.
    intros H.
    intro i.
    specialize (H i).
    destruct H as (HF & HV).
    split.
    + inversion HF; subst; constructor; auto.
    + inversion HV; subst; constructor; auto.
  Qed.

  Lemma module_layer_rel_weaken (D1: ld1) (D2: ld2)
        (RF: funrel D1 D2) (RV: varrel (Vm1:=Vm1) (Vm2:=Vm2))
        (ML1: module1 × layer1 D1) (ML2: module2 × layer2 D2):
    module_layer_rel_strong D1 D2 RF RV ML1 ML2 ->
    module_layer_rel D1 D2 RF RV ML1 ML2.
  Proof.
    intros H.
    intro i.
    specialize (H i).
    destruct H as (HF & HV).
    split.
    + inversion HF; subst; constructor; tauto.
    + inversion HV; subst; constructor; tauto.
  Qed.
End RELATIONS.


(** * Proving [simrel_program_rel] *)

Section SIMREL_INIT_MEM.
  Context `{Hmwd: BaseMemoryModel}.

  Context {primsem V layer} `{Hlayers: Layers layerdata simrel ident primsem (globvar V) layer}
          {module F} `{Hmodule_ops: !ModuleOps ident F (globvar V) module}
          `{Hmodules: !Modules ident F (globvar V) module}
          `{Hmp: MakeProgram}.

  Context
    {Fp Vp}
    {pf: ProgramFormatOps F V Fp Vp}
    {Hpf: ProgramFormat F V Fp Vp}
    {Vp_eq_dec: EqDec (globvar Vp)}.

Definition module_layer_init_rel {D1 D2}
           (R: simrel D1 D2)
           (ML1: module * layer D1)
           (ML2: module * layer D2) :=
  (forall i,
     get_module_layer_function i ML2 <> OK None ->
     ~ isOKNone (get_module_layer_function i ML1) \/
     simrel_undef_matches_values_bool R = true
  ) /\
  (forall i,
     get_module_layer_variable i ML2 <> OK None ->
     isOKNone (get_module_layer_variable i ML1) ->
     match get_module_layer_variable i ML2 with
       | OK (Some v2) =>
         match make_varinfo v2 with
           | OK vp2 =>
             simrel_newvar_ok (simrel_new_glbl R) (simrel_undef_matches_values_bool R) i (gvar_init vp2) /\
             Genv.init_data_list_valid find_symbol 0 (gvar_init vp2) = true /\
             gvar_readonly vp2 = false /\
             gvar_volatile vp2 = false
           | _ => False
         end
       | _ => False
     end
  ) /\
  (forall i,
     get_module_layer_variable i ML1 <> OK None ->
     ~ List.In i (List.map fst (simrel_new_glbl R)))
  /\
  Forall (fun i => ~ isOKNone (get_module_layer_variable i ML2)) (List.map fst (simrel_new_glbl R)).

Lemma module_layer_init_rel_ext {D1 D2} (R R': simrel D1 D2)
      (ML1 ML1': module * layer D1)
      (ML2 ML2': module * layer D2):
  SimrelEquivalence.simrel_equiv R R' ->
  (forall i,
     get_module_layer_function i ML1 =
     get_module_layer_function i ML1') ->
  (forall i,
     get_module_layer_variable i ML1 =
     get_module_layer_variable i ML1') ->
  (forall i,
     get_module_layer_function i ML2 =
     get_module_layer_function i ML2') ->
  (forall i,
     get_module_layer_variable i ML2 =
     get_module_layer_variable i ML2') ->
  module_layer_init_rel R ML1 ML2 ->
  module_layer_init_rel R' ML1' ML2'.
Proof.
  intros Hequiv Hfun1 Hvar1 Hfun2 Hvar2 H.
  destruct H as (Hfuns & Hvars & Hnew1 & Hnew2).
  destruct Hequiv as (equiv & Hequiv).
  split.
  {
    intro i.
    rewrite <- Hfun2.
    rewrite <- Hfun1.
    specialize (Hfuns i).
    revert Hfuns.
    SimrelEquivalence.simrel_equiv_rewrite.
    auto.
  }
  split.
  {
    intro i.
    rewrite <- Hvar2.
    rewrite <- Hvar1.
    specialize (Hvars i).
    revert Hvars.
    SimrelEquivalence.simrel_equiv_rewrite.
    auto.
  }
  split.
  {
    intro i.
    rewrite <- Hvar1.
    specialize (Hnew1 i).
    revert Hnew1.
    SimrelEquivalence.simrel_equiv_rewrite.
    auto.
  }
  {
    rewrite Forall_forall in Hnew2.
    rewrite Forall_forall.
    intro i.
    rewrite <- Hvar2.
    specialize (Hnew2 i).
    revert Hnew2.
    SimrelEquivalence.simrel_equiv_rewrite.
    auto.
  }
Qed.

Global Instance module_layer_init_rel_dec {D1 D2} (R: simrel D1 D2) ML1 ML2:
  Decision (module_layer_init_rel R ML1 ML2).
Proof.
  repeat (apply and_dec; try typeclasses eauto).
  apply get_module_layer_variable_dec.
  intro i.
  apply impl_dec; try typeclasses eauto.
  destruct (get_module_layer_variable i ML2) as [ [ g | ] | ] ; try now (right; auto).
  destruct (make_varinfo g) as [ | ] ; try now (right; auto).
  unfold simrel_newvar_ok.
  apply and_dec; try typeclasses eauto.
Defined.

Lemma get_module_layer_variable_context {D} i CTXT M L:
  get_module_layer_variable (D := D) i (CTXT ⊕ M, L) =
  get_module_variable i CTXT ⊕
  get_module_layer_variable i (M, L).
Proof.
  unfold get_module_layer_variable.
  simpl.
  rewrite get_module_variable_oplus.
  apply GlobalVars.res_option_globalvar_oplus_assoc.
Qed.

Lemma module_layer_init_rel_context {D1 D2}
        (R: simrel D1 D2)
        (CTXT M1 M2: module)
        (L1: layer D1) (L2: layer D2):
  (* context has to be compatible with new globals *)
  (forall i, ~ isOKNone (get_module_variable i CTXT) ->
             ~ isOKNone (get_module_layer_variable i (M2, L2)) ->
             ~ List.In i (List.map fst (simrel_new_glbl R))) ->
  module_layer_init_rel R (M1, L1) (M2, L2) ->
  module_layer_init_rel R (CTXT ⊕ M1, L1) (CTXT ⊕ M2, L2).
Proof.
  intro HCTXT.
  unfold module_layer_init_rel.
  destruct 1 as (Hfun & Hvar2 & Hvar1 & Hnew).
  split.
  {
    intros i Hi.
    specialize (Hfun i).
    revert Hi Hfun.
    repeat
      match goal with
          |- context [ ?u <> OK None ] =>
          replace (u <> OK None) with (~ isOKNone u)
            by reflexivity
      end.
    repeat rewrite get_module_layer_function_ok_none.
    simpl.
    repeat rewrite get_module_function_none_oplus.
    clear.
    tauto.
  }
  split.
  {
    intros i Hi.
    specialize (Hvar2 i).
    revert Hi Hvar2.
    repeat
      match goal with
          |- context [ ?u <> OK None ] =>
          replace (u <> OK None) with (~ isOKNone u)
            by reflexivity
      end.
    intros Hi Hvar2.
    repeat rewrite get_module_layer_variable_ok_none.
    simpl.
    repeat rewrite get_module_variable_none_oplus.
    intros [[CTXT_NONE M1_NONE] L1_NONE].
    unfold isOKNone in CTXT_NONE.
    rewrite get_module_layer_variable_context.
    rewrite CTXT_NONE.
    GlobalVars.res_option_globalvar_red.
    apply Hvar2.
    + revert Hi.
      repeat rewrite get_module_layer_variable_ok_none.
      simpl.
      repeat rewrite get_module_variable_none_oplus.
      revert CTXT_NONE.
      clear.
      tauto.
    + rewrite get_module_layer_variable_ok_none; auto.
  }
  split.
  {
    intros i Hi.
    specialize (Hvar1 i).
    revert Hi Hvar1.
    repeat
      match goal with
          |- context [ ?u <> OK None ] =>
          replace (u <> OK None) with (~ isOKNone u)
            by reflexivity
      end.
    specialize (HCTXT i).
    revert HCTXT.
    rewrite Forall_forall in Hnew.
    specialize (Hnew i).
    revert Hnew.
    repeat rewrite get_module_layer_variable_ok_none.
    simpl.
    repeat rewrite get_module_variable_none_oplus.
    tauto.
  }
  {
    revert Hnew.
    repeat rewrite Forall_forall.
    intro Hnew.
    intro i.
    specialize (Hnew i).
    revert Hnew.
    repeat rewrite get_module_layer_variable_ok_none.
    simpl.
    repeat rewrite get_module_variable_none_oplus.
    clear.
    tauto.
  }
Qed.

Lemma simrel_not_new_glbl_spec ng i:
  simrel_not_new_glbl ng i <->
  ~ In i (List.map fst ng).
Proof.
  rewrite in_map_iff.
  unfold simrel_not_new_glbl.
  unfold simrel_new_glbl_for.
  split; intro H.
  + intro ABS.
    destruct ABS as (x & ? & Hx).
    subst.
    apply in_split in Hx.
    destruct Hx as (? & ? & ?); subst.
    rewrite SimrelCategory.filter_app in H.
    simpl in H.
    unfold test in H.
    destruct (decide (fst x = fst x)); try congruence.
    simpl in H.
    match type of H with
        ?e ++ _ :: _ = _ =>
        destruct e; discriminate
    end.
  + revert H.
    induction ng; simpl; auto.
    intros H.
    unfold test at 1.
    destruct (decide (fst a = i)).
    - subst.
      destruct H.
      exists a.
      auto.
    - apply IHng.
      intro ABSURD.
      apply H.
      destruct ABSURD as (x & ? & Hx).
      subst.
      exists x.
      auto.
Qed.

Theorem simrel_program_rel_intro
        {D1 D2} (R: simrel D1 D2) ML1 ML2 RF:
  (forall i : ident, OptionRelationForward (RF i)) ->
  (forall i, Monotonic (make_fundef _ i) (RF i @@ Some ++> impl @@ isError)) ->
  module_layer_rel D1 D2 RF (fun _ => option_le eq) ML1 ML2 ->
  module_layer_init_rel R ML1 ML2 ->
  res_le (simrel_program_rel R) (make_program D1 ML1) (make_program D2 ML2).
Proof.
  intros HRF HRFerr Hrel Hinit.
  apply module_layer_rel_strengthen in Hrel.
  red in Hrel.
  eapply @make_program_rel in Hrel.
  2: eassumption.
  2: apply foodef_rel_mpr.
  2: apply option_relation_forward_function_strong; assumption.
  * inversion Hrel; clear Hrel; constructor.
    match goal with
        K: program_rel _ _ _ _ |- _ =>
        revert K
    end.
    apply program_subrel.
    + intros i fp1 fp2.
      unfold fundef_rel.
      intro Hf.
      inversion Hf as [ f1 ? Hfp1 f2 ? Hfp2 Hf_ ]; clear Hf; subst.
      destruct Hf_ as (Hf & HF1 & HF2).
      red.
      inversion Hfp2; subst.
      - inversion Hfp1; subst; try now repeat constructor.
        destruct Hinit as (Hfuns & _).
        specialize (Hfuns i).
        destruct Hfuns; try congruence.
        constructor.
        assumption.
      - apply HRF in Hf.
        specialize (Hf (eq_refl _)).
        subst.
        inversion Hfp1; subst.
        constructor.
    + intros i vp1 vp2.
      unfold vardef_rel.
      intro Hv.
      inversion Hv as [ v1 ? Hvp1 v2 ? Hvp2 Hv_ ]; clear Hv; subst.
      destruct Hv_ as (Hv & HV1 & HV2).
      inversion Hvp2; clear Hvp2; subst.
      - inversion Hv; clear Hv; subst.
        {
          inversion Hvp1; clear Hvp1; subst.
          destruct Hinit as (_ & Hvar & _).
          specialize (Hvar i).
          exploit Hvar.
          { congruence. }
          { assumption. }
          rewrite HV2.
          match goal with
              K: match_vardef _ ?u |- _ =>
              rename K into Hvardef;
                rename u into vp
          end.
          unfold match_vardef in Hvardef.
          rewrite Hvardef.
          destruct 1 as (Hvarok & Hvalid & Hreadonly & Hvolatile).
          destruct vp.
          simpl in *.
          subst.
          constructor; auto.
        }
        inversion Hvp1; subst.
        match goal with
            K1: match_vardef _ ?u1,
               K2: match_vardef _ ?u2 |- _ =>
            unfold match_vardef in K1, K2;
              assert (u2 = u1) by congruence;
              subst
          end.
        constructor.
        rewrite simrel_not_new_glbl_spec.
        destruct Hinit as (_ & _ & Hnew1 & _).
        apply Hnew1.
        congruence.
      - inversion Hv; clear Hv; subst.
        inversion Hvp1; clear Hvp1; subst.
        constructor.
        rewrite simrel_not_new_glbl_spec.
        destruct Hinit as (_ & _ & _ & Hnew2).
        intro ABSURD.
        rewrite Forall_forall in Hnew2.
        apply Hnew2 in ABSURD.
        contradiction.
  * intro i.
    unfold OptionRelationForward.
    destruct 1 as (Hopt & _).
    inversion Hopt; subst; congruence.
  * intros i f1 f2 (Hf & Hf1 & Hf2).
    try rauto. (* XXX auto for @@ ? *)
    eapply HRFerr.
    assumption.
  * intros i v1 v2 (Hv & Hv1 & Hv2).
    inversion Hv; subst.
    reflexivity.
Qed.

End SIMREL_INIT_MEM.
