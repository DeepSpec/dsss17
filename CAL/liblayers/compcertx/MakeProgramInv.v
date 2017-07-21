Require Export MakeProgramFacts.

(** * The [inv_make_globalenv] tactic *)

(** The tactic defined in the following decomposes a hypothesis of the
  form [make_globalenv _ s (M, L) = ret ge] into statements abour the
  blocks, variables and functions mapped by the global environment [ge].
  First, assuming [M] and [L] are of the form [i_1 ↦ d_1 ⊕ ⋯ ⊕ i_n ↦ d_n],
  the hypothesis is split recursively along [⊕] until hypotheses of
  the forms [make_globalenv _ s (i ↦ d, ∅) = ret ge'] or
  [make_globalenv _ s (∅, i ↦ d) = ret ge'] are obtained, with [genv_le (fun _ => eq) ge' ge].
  Then, the monotonicity of [make_globalenv] is exploited to convert
  those into, for example, [find_symbol ge i = Some b] and
  [find_var_info ge b = Some d].

  This is useful when doing proofs about actual code, since the
  Compcert semantics are expressed in terms of global environments
  rather than in terms of stencils. *)

Section PROPERTIES.
  Context `{Hmkp: MakeProgram}.
  Context `{Hpf: ProgramFormat}.
  Context `{Hdata: !Category layerdata simrel}.
  Context `{Hlayer: !Layers AST.ident primsem (AST.globvar Vm) layer}.
  Context `{Hmodule: !Modules AST.ident Fm (AST.globvar Vm) module}.

  Lemma make_program_make_globalenv {D} (M: module) (L: layer D) p:
    make_program _ (M, L) = ret p ->
    make_globalenv _ (M, L) = ret (Genv.globalenv p).
  Proof.
    intros H.
    unfold make_globalenv.
    rewrite H.
    reflexivity.
  Qed.

  Lemma make_globalenv_split_module_left {D} M1 M2 (L: _ D) ge:
    make_globalenv _ (M1 ⊕ M2, L) = ret ge ->
    exists ge1,
      make_globalenv _ (M1, L) = ret ge1 /\
      genv_le (fun _ => eq) ge1 ge.
  Proof.
    intros Hge.
    assert (HL: L ≤ L) by reflexivity.
    assert (HM1: M1 ≤ M1 ⊕ M2) by apply left_upper_bound.
    pose proof (make_globalenv_monotonic D (M1, L) (M1 ⊕ M2, L) (conj HM1 HL)) as Hge1.
    rewrite Hge in Hge1.
    inversion Hge1 as [ge1 xge Hge_ge1 Hge1' Hxge | ].
    exists ge1; intuition congruence.
  Qed.

  Lemma make_globalenv_split_module_right {D} M1 M2 (L: _ D) ge:
    make_globalenv _ (M1 ⊕ M2, L) = ret ge ->
    exists ge2,
      make_globalenv _ (M2, L) = ret ge2 /\
      genv_le (fun _ => eq) ge2 ge.
  Proof.
    intros Hge.
    assert (HL: L ≤ L) by reflexivity.
    assert (HM2: M2 ≤ M1 ⊕ M2) by apply right_upper_bound.
    pose proof (make_globalenv_monotonic D (M2, L) (M1 ⊕ M2, L) (conj HM2 HL)) as Hge2.
    rewrite Hge in Hge2.
    inversion Hge2 as [ge2 xge Hge_ge2 Hge2' Hxge | ].
    exists ge2; intuition congruence.
  Qed.

  Lemma make_globalenv_split_module {D} M1 M2 (L: _ D) ge:
    make_globalenv _ (M1 ⊕ M2, L) = ret ge ->
    exists ge1 ge2,
      (make_globalenv _ (M1, L) = ret ge1 /\ genv_le (fun _ => eq) ge1 ge) /\
      (make_globalenv _ (M2, L) = ret ge2 /\ genv_le (fun _ => eq) ge2 ge).
  Proof.
    intros Hge.
    generalize Hge.
    intro Hge'.
    apply make_globalenv_split_module_left in Hge.
    apply make_globalenv_split_module_right in Hge'.
    destruct Hge as [? [? ?]].
    destruct Hge' as [? [? ?]].
    eauto 10.
  Qed.

  Lemma make_globalenv_split_layer_left {D} M (L1 L2: _ D) ge:
    make_globalenv _ (M, L1 ⊕ L2) = ret ge ->
    exists ge1,
      make_globalenv _ (M, L1) = ret ge1 /\
      genv_le (fun _ => eq) ge1 ge.
  Proof.
    intros Hge.
    assert (HM: M ≤ M) by reflexivity.
    assert (HL1: L1 ≤ L1 ⊕ L2) by apply left_upper_bound.
    pose proof (make_globalenv_monotonic D (_,_) (_,_) (conj HM HL1)) as Hge1.
    rewrite Hge in Hge1.
    inversion Hge1 as [ge1 xge Hge_ge1 Hge1' Hxge | ].
    exists ge1; intuition congruence.
  Qed.

  Lemma make_globalenv_split_layer_right {D} M (L1 L2: _ D) ge:
    make_globalenv _ (M, L1 ⊕ L2) = ret ge ->
    exists ge2,
      make_globalenv _ (M, L2) = ret ge2 /\
      genv_le (fun _ => eq) ge2 ge.
  Proof.
    intros Hge.
    assert (HM: M ≤ M) by reflexivity.
    assert (HL2: L2 ≤ L1 ⊕ L2) by apply right_upper_bound.
    pose proof (make_globalenv_monotonic D (_,_) (_,_) (conj HM HL2)) as Hge2.
    rewrite Hge in Hge2.
    inversion Hge2 as [ge2 xge Hge_ge2 Hge2' Hxge | ].
    exists ge2; intuition congruence.
  Qed.

  Lemma make_globalenv_split_layer {D} M (L1 L2: _ D) ge:
    make_globalenv _ (M, L1 ⊕ L2) = ret ge ->
    exists ge1 ge2,
      (make_globalenv _ (M, L1) = ret ge1 /\ genv_le (fun _ => eq) ge1 ge) /\
      (make_globalenv _ (M, L2) = ret ge2 /\ genv_le (fun _ => eq) ge2 ge).
  Proof.
    intros Hge.
    generalize Hge.
    intro Hge'.
    apply make_globalenv_split_layer_left in Hge.
    apply make_globalenv_split_layer_right in Hge'.
    destruct Hge as [? [? ?]].
    destruct Hge' as [? [? ?]].
    eauto 10.
  Qed.

  Lemma make_globalenv_split_module_layer {D} M L ge:
    make_globalenv _ (M, L) = ret ge ->
    exists geM geL,
      (make_globalenv D (M, ∅) = ret geM /\ genv_le (fun _ => eq) geM ge) /\
      (make_globalenv D (∅, L) = ret geL /\ genv_le (fun _ => eq) geL ge).
  Proof.
    intros Hge.
    assert (HM: res_le (genv_le (fun _=>eq)) (make_globalenv D (M, ∅)) (ret ge)).
    {
      rewrite <- Hge; clear Hge.
      rauto.
    }
    assert (HL: res_le (genv_le (fun _=>eq)) (make_globalenv D (∅, L)) (ret ge)).
    {
      rewrite <- Hge; clear Hge.
      rauto.
    }
    inversion HM; subst.
    inversion HL; subst.
    exists x, x0.
    eauto.
  Qed.
End PROPERTIES.

Ltac inv_make_globalenv_leaftac Hge Hgele :=
  match type of Hge with
    (** Module function *)
    | make_globalenv ?D (?i ↦ ?f, ∅) = ret ?ge =>
      let κdef := fresh "κdef" in
      let b := fresh "b" in
      let Hκdef := fresh "H" κdef in
      let Hbfs := fresh "H" b "fs" in
      let Hbfp := fresh "H" b "fp" in
      let H := fresh "H" in
      pose proof (make_globalenv_internal (D:=D) i f ge) as H;
      apply H in Hge;
      clear H;
      destruct Hge as (κdef & b & Hκdef & Hbfs & Hbfp);
      try (injection Hκdef; clear Hκdef; intro; subst κdef);
      apply (genv_le_find_symbol_some _ _ _ _ _ Hgele) in Hbfs;
      apply (genv_le_find_funct_ptr_some _ _ _ _ Hgele) in Hbfp;
      clear ge Hgele

    (** Module variable *)
    | make_globalenv ?D (?i ↦ ?τ, ∅) = ret ?ge =>
      let vdef := fresh "vdef" in
      let b := fresh "b" in
      let Hvdef := fresh "H" vdef in
      let Hbfs := fresh "H" b "fs" in
      let Hbvi := fresh "H" b "vi" in
      let H := fresh "H" in
      pose proof (make_globalenv_module_globvar (D:=D) i τ ge) as H;
      apply H in Hge;
      clear H;
      destruct Hge as (vdef & b & Hvdef & Hbfs & Hbvi);
      apply (genv_le_find_symbol_some _ _ _ _ _ Hgele) in Hbfs;
      apply (genv_le_find_var_info_some _ _ _ _ _ Hgele) in Hbvi;
      clear ge Hgele

    (** Layer primitive *)
    | make_globalenv ?D (∅, ?i ↦ ?σ) = ret ?ge =>
      let σdef := fresh "σdef" in
      let b := fresh "b" in
      let Hσdef := fresh "H" σdef in
      let Hbfs := fresh "H" b "fs" in
      let Hbfp := fresh "H" b "fp" in
      let H := fresh "H" in
      pose proof (make_globalenv_external (D:=D) i σ ge) as H;
      apply H in Hge;
      clear H;
      destruct Hge as (σdef & b & Hσdef & Hbfs & Hbfp);
      try (injection Hσdef; clear Hσdef; intro; subst σdef);
      apply (genv_le_find_symbol_some _ _ _ _ _ Hgele) in Hbfs;
      apply (genv_le_find_funct_ptr_some _ _ _ _ Hgele) in Hbfp;
      clear ge Hgele

    (** Layer variable *)
    | make_globalenv ?D (∅, ?i ↦ ?τ) = ret ?ge =>
      let vdef := fresh "vdef" in
      let b := fresh "b" in
      let Hvdef := fresh "H" vdef in
      let Hbfs := fresh "H" b "fs" in
      let Hbvi := fresh "H" b "vi" in
      let H := fresh "H" in
      pose proof (make_globalenv_layer_globvar (D:=D) i τ ge) as H;
      apply H in Hge;
      clear H;
      destruct Hge as (vdef & b & Hvdef & Hbfs & Hbvi);
      apply (genv_le_find_symbol_some _ _ _ _ _ Hgele) in Hbfs;
      apply (genv_le_find_var_info_some _ _ _ _ _ Hgele) in Hbvi;
      clear ge Hgele

    | _ => idtac
  end.

Ltac inv_make_globalenv_split_layer leaftac HLge Hgele :=
  lazymatch type of HLge with
    | make_globalenv _ (?M, ?L1 ⊕ ?L2) = ret ?ge =>
      let ge1 := fresh "ge0" in
      let ge2 := fresh "ge0" in
      let HLge1 := fresh "HL" ge1 in
      let HLge2 := fresh "HL" ge2 in
      let Hge1le := fresh "HL" ge1 "le" in
      let Hge2le := fresh "HL" ge2 "le" in
      destruct (make_globalenv_split_layer M L1 L2 ge HLge)
        as [ge1 [ge2 [[HLge1 Hge1le] [HLge2 Hge2le]]]];
      clear HLge;
      try rewrite Hgele in Hge1le;
      try rewrite Hgele in Hge2le;
      clear ge Hgele;
      inv_make_globalenv_split_layer leaftac HLge1 Hge1le;
      inv_make_globalenv_split_layer leaftac HLge2 Hge2le

    | _ =>
      leaftac HLge Hgele
  end.

Ltac inv_make_globalenv_split_module leaftac HMge Hgele :=
  lazymatch type of HMge with
    | make_globalenv _ (?M1 ⊕ ?M2, ?L) = ret ?ge =>
      let ge1 := fresh "ge0" in
      let ge2 := fresh "ge0" in
      let HMge1 := fresh "HM" ge1 in
      let HMge2 := fresh "HM" ge2 in
      let Hge1le := fresh "HM" ge1 "le" in
      let Hge2le := fresh "HM" ge2 "le" in
      destruct (make_globalenv_split_module M1 M2 L ge HMge)
        as [ge1 [ge2 [[HMge1 Hge1le] [HMge2 Hge2le]]]];
      clear HMge;
      try rewrite Hgele in Hge1le;
      try rewrite Hgele in Hge2le;
      clear ge Hgele;
      inv_make_globalenv_split_module leaftac HMge1 Hge1le;
      inv_make_globalenv_split_module leaftac HMge2 Hge2le

    | _ =>
      leaftac HMge Hgele
  end.

Ltac inversion_make_globalenv H :=
  lazymatch type of H with
    | make_globalenv _ (?M, ?L) = ret ?ge =>
      let geM := fresh "geM" in
      let geL := fresh "geL" in
      let HgeM := fresh "H" geM in
      let HgeL := fresh "H" geL in
      let HgeMle := fresh "H" geM "le" in
      let HgeLle := fresh "H" geL "le" in
      destruct (make_globalenv_split_module_layer M L ge H)
        as [geM [geL [[HgeM HgeMle] [HgeL HgeLle]]]];
      inv_make_globalenv_split_module inv_make_globalenv_leaftac HgeM HgeMle;
      inv_make_globalenv_split_layer inv_make_globalenv_leaftac HgeL HgeLle
  end.

Ltac inv_make_globalenv H :=
  inversion_make_globalenv H;
  clear H.


(** * Test *)

Section MAKE_PROGRAM_INV_TEST.
  Context `{Hmkp: MakeProgram}.
  Context `{Hpf: ProgramFormat}.
  Context `{Hmodule: !Modules _ _ _ _}.
  Context `{Hlayer: !Layers _ _ _ _}.

  Goal
    forall D (i j k m n: ident) (σ: primsem D) (κ: Fm) (τ υ: globvar Vm) ge,
      make_globalenv D (i ↦ κ ⊕ j ↦ τ ⊕ k ↦ τ, m ↦ υ ⊕ n ↦ σ) = ret ge ->
      False.
  Proof.
    intros.
    inv_make_globalenv H.
    match goal with
      | H: context [make_globalenv] |- _ => fail 1
      | _ => idtac
    end.
  Abort.
End MAKE_PROGRAM_INV_TEST.
