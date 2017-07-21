Require Import ExtensionalityAxioms.
Require Import MemoryRel.
Require Export SimrelDefinition.
Require Export SimrelEquivalence.
Require Export SimrelInitMem.
Require Import MemOpv.
Local Opaque mwd_ops.


(** * Categorical structure *)

(** ** Identity *)

Section IDENTITY.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Definition simrel_id_ops: simrel_components D D :=
    {|
      simrel_world := unit;
      simrel_acc := {| le x y := True |};
      simrel_undef_matches_values_bool := false;
      simrel_undef_matches_block p b := False;
      simrel_new_glbl := nil;
      simrel_meminj p := inject_id;
      match_mem p := @eq (mwd D)
    |}.

  Lemma list_forall2_eq {A}:
    list_forall2 (@eq A) = eq.
  Proof.
    eapply eqrel_eq.
    split.
    - induction 1; congruence.
    - intros l1 l2 H.
      subst.
      induction l2; constructor; eauto.
  Qed.

  Lemma match_block_sameofs_simrel_id p:
    match_block_sameofs simrel_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - inversion 1.
      reflexivity.
    - intros b _ [].
      reflexivity.
  Qed.

  Lemma match_block_simrel_id p:
    match_block simrel_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - intros b1 b2 [ofs H].
      inversion H; congruence.
    - intros b _ [].
      exists 0%Z.
      reflexivity.
  Qed.

  Lemma match_ptr_simrel_id p:
    match_ptr simrel_id_ops p = eq.
  Proof.
    eapply eqrel_eq.
    split.
    - destruct 1.
      inversion H; subst.
      rewrite Z.add_0_r.
      reflexivity.
    - intros [b ofs] y [].
      rewrite <- (Z.add_0_r ofs) at 2.
      constructor.
      reflexivity.
  Qed.

  Lemma match_ptrbits_simrel_id p:
    match_ptrbits simrel_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - destruct 1.
      inversion H; subst.
      change (Ptrofs.repr 0) with Ptrofs.zero.
      rewrite Ptrofs.add_zero.
      reflexivity.
    - intros [b ofs] y [].
      rewrite <- (Ptrofs.add_zero ofs) at 2.
      change Ptrofs.zero with (Ptrofs.repr 0).
      constructor.
      reflexivity.
  Qed.

  Lemma match_ptrrange_simrel_id p:
    match_ptrrange simrel_id_ops p = eq.
  Proof.
    eapply eqrel_eq.
    split.
    - destruct 1.
      inversion H; subst.
      rewrite match_ptr_simrel_id in H.
      congruence.
    - intros [[b lo] hi] _ [].
      replace hi with (lo + (hi - lo))%Z by omega.
      constructor.
      rewrite match_ptr_simrel_id.
      reflexivity.
  Qed.

  Lemma match_val_simrel_id p:
    match_val simrel_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - destruct 1; try discriminate; try contradiction; try reflexivity.
      rewrite match_ptrbits_simrel_id in H.
      congruence.
    - intros v _ [].
      destruct v; repeat rstep.
      rewrite match_ptrbits_simrel_id.
      reflexivity.
  Qed.

  Lemma match_memval_simrel_id p:
    match_memval simrel_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - destruct 1; try discriminate; try contradiction; try reflexivity.
      rewrite match_val_simrel_id in H.
      congruence.
    - intros v _ [].
      destruct v; repeat rstep.
      rewrite match_val_simrel_id.
      reflexivity.
  Qed.

  Lemma simrel_option_le_id {A}:
    flex_option_le (false = true) (@eq A) = eq.
  Proof.
    apply eqrel_eq; split; intros x y H.
    - destruct H; try congruence.
    - subst.
      reflexivity.
  Qed.

  Lemma simrel_fundef_rel_id {F1 F2}:
    simrel_fundef_rel (F1:=F1) (F2:=F2) false =
    fun _ => option_rel ⊤%rel.
  Proof.
    apply functional_extensionality; intros i.
    unfold simrel_fundef_rel.
    apply eqrel_eq; split; intros x y H; destruct H; repeat constructor.
    discriminate.
  Qed.

  Lemma simrel_vardef_rel_id {V}:
    simrel_vardef_rel (V:=V) nil false =
    fun _ => eq.
  Proof.
    apply functional_extensionality; intros i.
    apply eqrel_eq; split; intros x y H.
    - destruct H; eauto.
      destruct H as [? | [? ?]]; try discriminate.
    - subst.
      destruct y; constructor; reflexivity.
  Qed.

  Hint Rewrite
    match_block_simrel_id
    match_block_sameofs_simrel_id
    match_ptr_simrel_id
    match_ptrbits_simrel_id
    match_ptrrange_simrel_id
    match_val_simrel_id
    match_memval_simrel_id
    @simrel_fundef_rel_id
    @simrel_vardef_rel_id
    : simrel.

  Global Instance simrel_id_init_mem {F1 F2 V}:
    InitMemSimrel (D1:=D) (D2:=D) (F1:=F1) (F2:=F2) (V:=V) nil false
      (fun _ _ _ _ => eq).
  Proof.
    assert (forall i, ~ simrel_newfun_ok nil false i).
    {
      intros i [H _].
      discriminate.
    }
    assert (forall i init, ~ simrel_newvar_ok nil false i init).
    {
      intros i init [|[? ?]]; discriminate.
    }
    split; intros.
    - reflexivity.
    - repeat rstep; subst; reflexivity.
    - exfalso; unfold not in *; eauto.
    - exfalso; unfold not in *; eauto.
    - repeat rstep; subst; reflexivity.
    - split; repeat intro; repeat rstep; subst; try reflexivity.
      + congruence.
      + erewrite (Genv.store_init_data_symbols_preserved x y) in H6.
        * congruence.
        * intro.
          rewrite !stencil_matches_symbols by eauto.
          reflexivity.
      + destruct H4.
        congruence.
  Qed.

  Local Instance simrel_id_prf:
    SimulationRelation simrel_id_ops.
  Proof.
    split; simpl; intros; autorewrite with simrel.

    (** Compatibility with order *)
    - repeat constructor.
    - solve_monotonic.
    - solve_monotonic.

    (** Properties of match_ptr *)
    - discriminate.
    - contradiction.
    - autorewrite with simrel in *. congruence.
    - autorewrite with simrel in *. congruence.
    - autorewrite with simrel in *. congruence.
    - constructor.

    (** [Genv.init_mem] *)
    - eapply genv_init_mem_simrel; try typeclasses eauto.
      simpl.
      intros ? ? [[] _].
      exists tt.
      reflexivity.

    (** [Mem.alloc] *)
    - exists tt.
      autorewrite with simrel.
      split; simpl; eauto.
      split; congruence.

    (** [Mem.free] *)
    - repeat rstep; subst.
      destruct (uncurry _ _); constructor.
      exists p; repeat constructor.

    (** [Mem.load] *)
    - repeat rstep; subst.
      destruct y0; simpl.
      rauto.

    (** [Mem.store] *)
    - repeat rstep; subst.
      destruct (uncurry _ _); constructor.
      exists p; repeat constructor.

    (** [Mem.loadbytes] *)
    - repeat rstep; subst.
      destruct y0; simpl.
      rauto.

    (** [Mem.storebytes] *)
    - repeat rstep; subst.
      rewrite @list_rel_eq in *.
      subst.
      destruct (uncurry _ _); constructor.
      exists p; repeat constructor.

    (** [Mem.perm] *)
    - repeat rstep; congruence.

    (** [Mem.valid_block] *)
    - unfold Mem.valid_block.
      repeat rstep; congruence.

    (** [Mem.different_pointers_inject] *)
    - inversion H3; clear H3; subst.
      inversion H4; clear H4; subst.
      tauto.

    (** [Mem.weak_valid_pointer_inject_val] *)
    - autorewrite with simrel in *.
      congruence.

    (** [weak_valid_pointer_address_inject_weak] *)
    - unfold inject_id in *.
      inversion H0; clear H0; subst.
      exists 0. intros.
      rewrite Ptrofs.add_zero.
      omega.

    (** [Mem.address_inject] *)
    - inversion H1; subst.
      rewrite Ptrofs.add_zero.
      omega.

    (** [Mem.aligned_area_inject] *)
    - inversion H5; subst.
      auto with zarith.

    (** [Mem.disjoint_or_equal_inject] *)
    - inversion H0; subst.
      inversion H1; subst.
      repeat rewrite Z.add_0_r.
      assumption.
  Qed.

  Definition simrel_id: simrel D D :=
    {|
      simrel_ops := simrel_id_ops
    |}.
End IDENTITY.


(** ** Composition *)

Require Import Decision.

Lemma list_rel_compose {A B C} (R: rel A B) (S: rel B C):
  list_rel (rel_compose R S) = rel_compose (list_rel R) (list_rel S).
Proof.
  eapply eqrel_eq; split.
  - intros l1 l3 H.
    induction H as [ | x1 x3 (x2 & Hx12 & Hx23) l1 l3 _ (l2 & Hl12 & Hl23)];
      ehtransitivity; constructor; eauto.
  - intros l1 l3 (l2 & Hl12 & Hl23).
    revert l3 Hl23.
    induction Hl12; inversion 1; clear Hl23; subst; constructor.
    + eexists; eauto.
    + eauto.
Qed.

Section COMPOSE.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2 D3: layerdata}.

  Definition simrel_compose_ops
      (R12: simrel_components D1 D2)
      (R23: simrel_components D2 D3) :=
    {|
      simrel_world :=
        simrel_world R12 * simrel_world R23;
      simrel_acc :=
        {| le := ((≤) * (≤))%rel |};
      simrel_undef_matches_values_bool :=
        simrel_undef_matches_values_bool R12 ||
        simrel_undef_matches_values_bool R23;
      simrel_undef_matches_block p b :=
        (exists b',
           simrel_undef_matches_block R12 (fst p) b' /\
           match_block R23 (snd p) b' b) \/
        simrel_undef_matches_block R23 (snd p) b;
      simrel_new_glbl :=
        simrel_new_glbl R12 ++ simrel_new_glbl R23;
      simrel_meminj p :=
        compose_meminj
          (simrel_meminj R12 (fst p))
          (simrel_meminj R23 (snd p));
      match_mem p :=
        rel_compose
          (match_mem R12 (fst p))
          (match_mem R23 (snd p))
    |}.

  Hint Extern 2 (rel_compose ?R12 ?R23 ?x ?z) => eexists; split.
  Hint Resolve @match_ptrbits_block.

  Lemma simrel_undef_matches_values_compose R12 R23:
    simrel_undef_matches_values (simrel_compose_ops R12 R23) =
    (simrel_undef_matches_values R12 \/ simrel_undef_matches_values R23).
  Proof.
    unfold simrel_undef_matches_values; simpl.
    apply prop_ext.
    apply orb_true_iff.
  Qed.

  Lemma simrel_undef_matches_values_compose_introl R12 R23:
    simrel_undef_matches_values R12 ->
    simrel_undef_matches_values (simrel_compose_ops R12 R23).
  Proof.
    rewrite simrel_undef_matches_values_compose; eauto.
  Qed.

  Lemma simrel_undef_matches_values_compose_intror R12 R23:
    simrel_undef_matches_values R23 ->
    simrel_undef_matches_values (simrel_compose_ops R12 R23).
  Proof.
    rewrite simrel_undef_matches_values_compose; eauto.
  Qed.

  Hint Rewrite simrel_undef_matches_values_compose : simrel.
  Hint Immediate simrel_undef_matches_values_compose_introl.
  Hint Immediate simrel_undef_matches_values_compose_intror.

  Local Instance compose_meminj_inject_incr:
    Monotonic
      (@compose_meminj)
      ((- ==> option_le eq) ++> (- ==> option_le eq) ++> (- ==> option_le eq)).
  Proof.
    unfold compose_meminj.
    solve_monotonic.
  Qed.

  (** This only works one way, because a block may be shifted by [R12],
    and shifted back the same amount by [R23]. *)

  Global Instance match_block_sameofs_simrel_compose R12 R23 p12 p23:
    HTransitive
      (match_block_sameofs R12 p12)
      (match_block_sameofs R23 p23)
      (match_block_sameofs (simrel_compose_ops R12 R23) (p12, p23)).
  Proof.
    unfold match_block_sameofs; simpl.
    intros b1 b2 b3 Hb12 Hb23.
    unfold compose_meminj.
    rewrite Hb12.
    rewrite Hb23.
    reflexivity.
  Qed.

  Lemma match_block_simrel_compose R12 R23 p12 p23:
    match_block (simrel_compose_ops R12 R23) (p12, p23) =
    rel_compose
      (match_block R12 p12)
      (match_block R23 p23).
  Proof.
    apply eqrel_eq; split.
    - intros b1 b3 [delta H].
      simpl in H; unfold compose_meminj in H.
      destruct (simrel_meminj R12 _ _) as [[b2 d12]|] eqn:H12; try discriminate.
      destruct (simrel_meminj R23 _ _) as [[x3 d23]|] eqn:H23; try discriminate.
      inversion H; clear H; subst.
      exists b2.
      unfold match_block.
      eauto.
    - intros b1 b3 (b2 & [d12 H12] & [d23 H23]).
      exists (d12 + d23).
      simpl; unfold compose_meminj.
      rewrite H12, H23.
      reflexivity.
  Qed.

  Lemma match_ptr_simrel_compose R12 R23 p12 p23:
    match_ptr (simrel_compose_ops R12 R23) (p12, p23) =
    rel_compose
      (match_ptr R12 p12)
      (match_ptr R23 p23).
  Proof.
    apply eqrel_eq; split.
    - intros _ _ [b1 ofs1 b3 delta H].
      simpl in H; unfold compose_meminj in H.
      destruct (simrel_meminj R12 _ _) as [[b2 d12]|] eqn:H12; try discriminate.
      destruct (simrel_meminj R23 _ _) as [[x3 d23]|] eqn:H23; try discriminate.
      inversion H; clear H; subst.
      exists (b2, ofs1 + d12); split.
      + constructor; eauto.
      + replace (ofs1 + (d12 + d23)) with ((ofs1 + d12) + d23) by omega.
        constructor; eauto.
    - intros ptr1 ptr3 (ptr2 & H12 & H23).
      destruct H12 as [b1 ofs1 b2 d12 H12].
      inversion H23 as [b2' ofs2 b3 d23 H23']; clear H23; subst.
      replace (ofs1 + d12 + d23) with (ofs1 + (d12 + d23)) by omega.
      constructor.
      simpl; unfold compose_meminj.
      rewrite H12, H23'.
      reflexivity.
  Qed.

  Lemma match_ptrbits_simrel_compose R12 R23 p12 p23:
    match_ptrbits (simrel_compose_ops R12 R23) (p12, p23) =
    rel_compose
      (match_ptrbits R12 p12)
      (match_ptrbits R23 p23).
  Proof.
    apply eqrel_eq; split.
    - intros _ _ [b1 ofs1 b3 delta H].
      simpl in H; unfold compose_meminj in H.
      destruct (simrel_meminj R12 _ _) as [[b2 d12]|] eqn:H12; try discriminate.
      destruct (simrel_meminj R23 _ _) as [[x3 d23]|] eqn:H23; try discriminate.
      inversion H; clear H; subst.
      exists (b2, Ptrofs.add ofs1 (Ptrofs.repr d12)); split.
      + constructor; eauto.
      + replace (Ptrofs.add ofs1 (Ptrofs.repr (d12 + d23)))
           with (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr d12)) (Ptrofs.repr d23)).
        * constructor; eauto.
        * rewrite Ptrofs.add_assoc.
          f_equal.
          auto using add_repr.
    - intros ptr1 ptr3 (ptr2 & Hptr12 & Hptr23).
      destruct Hptr12 as [b1 ofs1 b2 d12 H12].
      inversion Hptr23 as [x2 ofs2 b3 d23 H23]; clear Hptr23; subst.
      rewrite Ptrofs.add_assoc.
      rewrite <- add_repr.
      constructor; eauto.
      simpl; unfold compose_meminj.
      rewrite H12.
      rewrite H23.
      reflexivity.
  Qed.

  Lemma match_ptrrange_simrel_compose R12 R23 p12 p23:
    SimulationRelation R23 ->
    match_ptrrange (simrel_compose_ops R12 R23) (p12, p23) =
    rel_compose (match_ptrrange R12 p12) (match_ptrrange R23 p23).
  Proof.
    intros.
    eapply eqrel_eq.
    split.
    - intros r1 r3 Hr.
      destruct Hr as [b1 ofs1 b3 ofs3 sz H13].
      rewrite match_ptr_simrel_compose in H13.
      destruct H13 as ([b2 ofs2] & H12 & H23).
      exists (b2, ofs2, ofs2+sz); split; constructor; eauto.
    - intros r1 r3 (r2 & Hr12 & Hr23).
      destruct Hr12; inversion Hr23; clear Hr23; subst.
      assert (sz0 = sz) by xomega; subst.
      constructor.
      rewrite match_ptr_simrel_compose.
      eexists; eauto.
  Qed.

  Lemma match_val_intro_simrel_compose R12 R23 p12 p23 v1 v2 v3:
    SimulationRelation R23 ->
    match_val R12 p12 v1 v2 ->
    match_val R23 p23 v2 v3 ->
    match_val (simrel_compose_ops R12 R23) (p12, p23) v1 v3.
  Proof.
    intros HR23 H12 H23.
    destruct H12; inversion H23; clear H23; subst;
    constructor; simpl; eauto 10.
    rewrite match_ptrbits_simrel_compose; eauto.
  Qed.

  Lemma match_val_elim_simrel_compose R12 R23 p12 p23 v1 v3:
    SimulationRelation R23 ->
    match_val (simrel_compose_ops R12 R23) (p12, p23) v1 v3 ->
    exists v2,
      match_val R12 p12 v1 v2 /\
      match_val R23 p23 v2 v3.
  Proof.
    intros HR23.
    destruct 1;
    try solve [ eexists; split; econstructor; eauto ].
    - rewrite match_ptrbits_simrel_compose in *.
      destruct H as ([b ofs] & ? & ?).
      eexists; split; econstructor; eauto.
    - autorewrite with simrel in H.
      destruct H.
      + eexists; split; [ | constructor]; constructor; eauto.
      + exists Vundef; split; constructor; eauto.
    - autorewrite with simrel in H.
      destruct H.
      + eexists; split; [ | constructor]; constructor; eauto.
      + exists Vundef; split; constructor; eauto.
    - autorewrite with simrel in H.
      destruct H.
      + eexists; split; [ | constructor]; constructor; eauto.
      + exists Vundef; split; constructor; eauto.
    - autorewrite with simrel in H.
      destruct H.
      + eexists; split; [ | constructor]; constructor; eauto.
      + exists Vundef; split; constructor; eauto.
    - simpl in H.
      destruct H as [H|H].
      + destruct H as (b' & Hb' & Hb).
        destruct Hb as [delta Hb].
        exists (Vptr b' (Ptrofs.sub ofs (Ptrofs.repr delta))).
        split; constructor; eauto.
        pattern ofs at 2.
        replace ofs with (Ptrofs.add (Ptrofs.sub ofs (Ptrofs.repr delta)) (Ptrofs.repr delta)).
        * constructor; eauto.
        * rewrite Ptrofs.sub_add_opp.
          rewrite Ptrofs.add_assoc.
          rewrite (Ptrofs.add_commut (Ptrofs.neg _) _).
          rewrite Ptrofs.add_neg_zero.
          rewrite Ptrofs.add_zero.
          reflexivity.
      + exists Vundef.
        split; constructor; eauto.
  Qed.

  Lemma match_val_simrel_compose R12 R23 p12 p23:
    SimulationRelation R23 ->
    match_val (simrel_compose_ops R12 R23) (p12, p23) =
    rel_compose (match_val R12 p12) (match_val R23 p23).
  Proof.
    intros.
    eapply eqrel_eq.
    split.
    - intros x z.
      apply match_val_elim_simrel_compose; eauto.
    - intros x z (y & Hxy & Hyz).
      eapply match_val_intro_simrel_compose; eauto.
  Qed.

  Lemma match_memval_intro_simrel_compose R12 R23 p12 p23 v1 v2 v3:
    SimulationRelation R23 ->
    match_memval R12 p12 v1 v2 ->
    match_memval R23 p23 v2 v3 ->
    match_memval (simrel_compose_ops R12 R23) (p12, p23) v1 v3.
  Proof.
    intros HR23 H12 H23.
    destruct H12; inversion H23; subst; constructor; simpl;
    eauto 10;
    rewrite match_val_simrel_compose; eauto.
    exists Vundef; split; rauto.
  Qed.

  Lemma match_memval_elim_simrel_compose R12 R23 p12 p23 v1 v3:
    SimulationRelation R23 ->
    match_memval (simrel_compose_ops R12 R23) (p12, p23) v1 v3 ->
    exists v2,
      match_memval R12 p12 v1 v2 /\
      match_memval R23 p23 v2 v3.
  Proof.
    intros HR23.
    destruct 1;
    try solve [ eexists; split; econstructor; eauto ].
    - rewrite match_val_simrel_compose in *; eauto.
      destruct H as (? & ? & ?).
      eexists; split; econstructor; eauto.
    - autorewrite with simrel in H.
      destruct H.
      + exists (Byte b); split; constructor; eauto.
      + exists Undef; split; constructor; eauto.
    - autorewrite with simrel in H.
      rewrite match_val_simrel_compose in *; eauto.
      destruct H0 as (x & ? & ?).
      destruct H.
      + exists (Fragment x q n); split; constructor; eauto.
      + exists Undef; split; simpl; constructor; auto.
        inv H0; inv H1; try constructor; auto.
        eapply simrel_undef_matches_values_also_block; eauto.
  Qed.

  Lemma match_memval_simrel_compose R12 R23 p12 p23:
    SimulationRelation R23 ->
    match_memval (simrel_compose_ops R12 R23) (p12, p23) =
    rel_compose (match_memval R12 p12) (match_memval R23 p23).
  Proof.
    intros.
    eapply eqrel_eq.
    split.
    - intros x z.
      apply match_memval_elim_simrel_compose; eauto.
    - intros x z (y & Hxy & Hyz).
      eapply match_memval_intro_simrel_compose; eauto.
  Qed.

  Lemma match_memvals_intro_simrel_compose R12 R23 p12 p23 vs1 vs2 vs3:
    SimulationRelation R23 ->
    list_forall2 (match_memval R12 p12) vs1 vs2 ->
    list_forall2 (match_memval R23 p23) vs2 vs3 ->
    list_forall2 (match_memval (simrel_compose_ops R12 R23) (p12, p23)) vs1 vs3.
  Proof.
    intros HR23 Hvs12 Hvs23.
    revert vs3 Hvs23.
    induction Hvs12 as [ | v1 vs1 v2 vs2 Hv12 Hvs12 IHvs12];
    inversion 1 as [ | v2' vs2' v3 vs3' Hv23 Hvs23'];
    subst.
    - constructor.
    - constructor; simpl; eauto.
      eapply match_memval_intro_simrel_compose; eauto.
  Qed.

  Lemma match_memvals_elim_simrel_compose R12 R23 p12 p23 vs1 vs3:
    SimulationRelation R23 ->
    list_forall2 (match_memval (simrel_compose_ops R12 R23) (p12,p23)) vs1 vs3 ->
    exists vs2,
      list_forall2 (match_memval R12 p12) vs1 vs2 /\
      list_forall2 (match_memval R23 p23) vs2 vs3.
  Proof.
    intros HR23 Hvs13.
    induction Hvs13 as [ | v1 vs1 v3 vs3 Hv13 Hvs13 IHvs13].
    - exists nil.
      split; constructor.
    - apply match_memval_elim_simrel_compose in Hv13; eauto.
      destruct Hv13 as (v2 & Hv12 & Hv23).
      destruct IHvs13 as (v2s & Hvs12 & Hvs23).
      exists (v2 :: v2s).
      split; constructor; assumption.
  Qed.

  Lemma match_memvals_simrel_compose R12 R23 p12 p23:
    SimulationRelation R23 ->
    list_forall2 (match_memval (simrel_compose_ops R12 R23) (p12, p23)) =
    rel_compose
      (list_forall2 (match_memval R12 p12))
      (list_forall2 (match_memval R23 p23)).
  Proof.
    intros.
    eapply eqrel_eq.
    split.
    - intros x z.
      apply match_memvals_elim_simrel_compose; eauto.
    - intros x z (y & Hxy & Hyz).
      eapply match_memvals_intro_simrel_compose; eauto.
  Qed.

  Hint Rewrite
      match_block_simrel_compose
      match_block_sameofs_simrel_compose
      match_ptr_simrel_compose
      match_ptrbits_simrel_compose
      match_ptrrange_simrel_compose
      match_val_simrel_compose
      match_memval_simrel_compose
      match_memvals_simrel_compose
    using eassumption : simrel.

  (** To prove initialization, we need to construct an intermediate
    program [p2], so that if [p1] and [p3] are related by the
    composite relation, then [p1]/[p2], and [p2]/[p3], are related by
    the respective components. *)

  Section UNCOMPOSE_PROGRAMS.
    Context {F1 F3 V : Type}.
    Context (ng12: list (ident * list AST.init_data)) (b12: bool).
    Context (ng23: list (ident * list AST.init_data)) (b23: bool).

    Lemma filter_app {A} p l1 l2:
      @filter A p (l1 ++ l2) = filter p l1 ++ filter p l2.
    Proof.
      induction l1.
      - reflexivity.
      - simpl.
        rewrite IHl1.
        destruct (p a); reflexivity.
    Qed.

    Program Instance simrel_vardef_not_new_glbl_dec i:
      Decision (simrel_not_new_glbl ng23 i) :=
        match (simrel_new_glbl_for ng23 i) with
          | nil => left _
          | _ => right _
        end.
    Next Obligation.
      red.
      congruence.
    Qed.

    Notation simrel_undef_matches_variable ng b i :=
      (b = true \/ In i (map fst ng)).

    Lemma simrel_newvar_ok_compose i init:
      simrel_newvar_ok (ng12 ++ ng23) (b12 || b23) i init ->
      (simrel_newvar_ok ng12 b12 i init /\ simrel_not_new_glbl ng23 i) \/
      (simrel_not_new_glbl ng12 i /\ simrel_newvar_ok ng23 b23 i init).
    Proof.
      intros [Hng | [Hng Hb]].
      - unfold simrel_new_glbl_for in Hng.
        rewrite filter_app in Hng.
        apply app_eq_unit in Hng.
        unfold simrel_newvar_ok, simrel_not_new_glbl.
        destruct Hng as [[H12 H23] | [H12 H23]]; eauto.
      - apply orb_true_iff in Hb.
        unfold simrel_newvar_ok, simrel_not_new_glbl.
        unfold simrel_new_glbl_for in *.
        rewrite filter_app in Hng.
        apply app_eq_nil in Hng.
        destruct Hng as [? ?], Hb as [?|?]; eauto.
    Qed.

    Lemma simrel_undef_matches_new_glbl ng b i init:
      simrel_newvar_ok ng b i init ->
      simrel_undef_matches_variable ng b i.
    Proof.
      unfold simrel_newvar_ok, simrel_new_glbl_for.
      induction ng; simpl.
      - intros [?|[? ?]]; left; congruence.
      - unfold test at 1 4.
        destruct (decide _); subst; eauto.
        intro.
        edestruct IHng; eauto.
    Qed.

    Lemma simrel_undef_matches_not_new_glbl ng b i:
      simrel_not_new_glbl ng i ->
      simrel_undef_matches_variable ng b i ->
      b = true.
    Proof.
      intros Hi [Hglbl|Hundef]; eauto.
      unfold simrel_not_new_glbl in Hi.
      unfold simrel_new_glbl_for in Hi.
      exfalso.
      induction ng; simpl in *; eauto.
      unfold test at 1 in Hi.
      destruct (decide _).
      - discriminate.
      - destruct Hundef; try contradiction.
        eauto.
    Qed.

    Lemma simrel_not_new_glbl_compose i:
      simrel_not_new_glbl (ng12 ++ ng23) i ->
      simrel_not_new_glbl ng12 i /\
      simrel_not_new_glbl ng23 i.
    Proof.
      intros H.
      unfold simrel_not_new_glbl in H.
      unfold simrel_new_glbl_for in H.
      simpl in H.
      rewrite filter_app in H.
      apply app_eq_nil in H.
      destruct H as [H12 H23]; eauto.
    Qed.

    Definition simrel_uncompose_fundef (f1: option F1) (f3: option F3) :=
      match f1, f3 with
        | Some f1, Some f3 => Some f3
        | None, Some f3 => if b12 then Some f3 else None
        | _, _ => None
      end.

    Lemma simrel_fundef_rel_compose i f1 f3:
      simrel_fundef_rel (b12 || b23) i f1 f3 ->
      simrel_fundef_rel b12 i f1 (simrel_uncompose_fundef f1 f3) /\
      simrel_fundef_rel b23 i (simrel_uncompose_fundef f1 f3) f3.
    Proof.
      unfold simrel_fundef_rel.
      intros Hf.
      destruct Hf; simpl.
      - repeat constructor.
      - repeat constructor.
      - autorewrite with simrel in H.
        destruct b12.
        + split; repeat constructor; eauto.
          destruct y; repeat constructor.
        + destruct y; repeat constructor.
          assumption.
    Qed.

    Definition simrel_uncompose_vardef i (v1 v3: option (globvar V)) :=
      match v1, v3 with
        | Some v1, Some v3 => Some v3
        | None, Some v3 =>
          if decide (simrel_undef_matches_variable ng12 b12 i /\
                     simrel_not_new_glbl ng23 i) then Some v3 else None
        | _, _ =>
          None
      end.

    Lemma simrel_vardef_rel_compose i v1 v3:
      simrel_vardef_rel (ng12 ++ ng23) (b12 || b23) i v1 v3 ->
      simrel_vardef_rel ng12 b12 i v1 (simrel_uncompose_vardef i v1 v3) /\
      simrel_vardef_rel ng23 b23 i (simrel_uncompose_vardef i v1 v3) v3.
    Proof.
      intros [Hng | v Hng | v init Hng Hinit].
      - eapply simrel_not_new_glbl_compose in Hng.
        destruct Hng.
        split; constructor; eauto.
      - eapply simrel_not_new_glbl_compose in Hng.
        destruct Hng.
        split; constructor; eauto.
      - eapply simrel_newvar_ok_compose in Hng.
        simpl.
        destruct Hng as [[H12 H23] | [H12 H23]].
        + destruct (decide _) as [[H12u _] | H].
          * repeat (constructor; eauto).
          * elim H.
            split; eauto using simrel_undef_matches_new_glbl.
        + destruct (decide _) as [[H12u H23n] | H].
          * eapply simrel_undef_matches_not_new_glbl in H12u; eauto.
            split; constructor; eauto.
            right.
            eauto.
          * repeat (constructor; eauto).
    Qed.

    Definition simrel_uncompose_def i (d1: _ (globdef F1 V)) (d3: _ (globdef F3 V)) :=
      match d1, d3 with
        | None, None => None
        | Some (Gfun f1), Some (Gfun f3) => Some (Gfun f3)
        | Some (Gvar v1), Some (Gvar v3) => Some (Gvar v3)
        | None, Some (Gfun f3) =>
          if b12 then Some (Gfun f3) else None
        | None, Some (Gvar v3) =>
          if decide (simrel_undef_matches_variable ng12 b12 i /\
                     simrel_not_new_glbl ng23 i) then Some (Gvar v3) else None
        | _, _ => None
      end.

    Lemma simrel_globdef_rel_uncompose i d1 d3:
      globdef_rel
        (simrel_fundef_rel (F1:=F1) (F2:=F3) (b12 || b23))
        (simrel_vardef_rel (V:=V) (ng12 ++ ng23) (b12 || b23))
        i d1 d3 ->
      globdef_rel
        (simrel_fundef_rel (F1:=F1) (F2:=F3) b12)
        (simrel_vardef_rel (V:=V) ng12 b12)
        i d1 (simrel_uncompose_def i d1 d3) /\
      globdef_rel
        (simrel_fundef_rel (F1:=F3) (F2:=F3) b23)
        (simrel_vardef_rel (V:=V) ng23 b23)
        i (simrel_uncompose_def i d1 d3) d3.
    Proof.
      unfold globdef_rel, rel_inter, rel_pull.
      intros [Hf Hv].
      apply simrel_fundef_rel_compose in Hf.
      destruct Hf as [Hf12 Hf23].
      apply simrel_vardef_rel_compose in Hv.
      destruct Hv as [Hv12 Hv23].
      destruct d1 as [[f1|v1]|] eqn:Hd1, d3 as [[f3|v3]|] eqn:Hd3;
      simpl; monad_norm; simpl in *; eauto.
      - inversion Hf12.
      - destruct b12; eauto.
        inversion Hv12.
      - destruct b12; eauto.
      - destruct (decide _); eauto.
    Qed.

    Fixpoint simrel_uncompose_defs (l1 l3: list (ident * option (globdef _ _))) :=
      match l1, l3 with
        | (i, d1) :: l1', (_, d3) :: l3' =>
          (i, simrel_uncompose_def i d1 d3) :: simrel_uncompose_defs l1' l3'
        | _, _ => nil
      end.

    Lemma simrel_globdefs_rel_uncompose l1 l3:
      globdefs_rel
        (simrel_fundef_rel (F1:=F1) (F2:=F3) (b12 || b23))
        (simrel_vardef_rel (V:=V) (ng12 ++ ng23) (b12 || b23))
        glob_threshold
        l1 l3 ->
      globdefs_rel
        (simrel_fundef_rel (F1:=F1) (F2:=F3) b12)
        (simrel_vardef_rel (V:=V) ng12 b12)
        glob_threshold
        l1 (simrel_uncompose_defs l1 l3) /\
      globdefs_rel
        (simrel_fundef_rel (F1:=F3) (F2:=F3) b23)
        (simrel_vardef_rel (V:=V) ng23 b23)
        glob_threshold
        (simrel_uncompose_defs l1 l3) l3.
    Proof.
      rewrite !globdefs_fw_bw_rel_eq.
      induction 1 as [ | i def1 def2 Hdef defs1 defs2 Hdefs IHdefs]; simpl.
      - split; constructor.
      - destruct IHdefs as [H12 H23].
        split; constructor; eauto;
        eapply simrel_globdef_rel_uncompose; eauto.
    Qed.

    Definition simrel_uncompose_prog p1 p3 :=
      {|
        prog_defs := simrel_uncompose_defs (prog_defs p1) (prog_defs p3);
        prog_public := prog_public p1;
        prog_main := prog_main p1
      |}.

    Lemma simrel_program_rel_uncompose p1 p3:
      program_rel
        (simrel_fundef_rel (F1:=F1) (F2:=F3) (b12 || b23))
        (simrel_vardef_rel (V:=V) (ng12 ++ ng23) (b12 || b23))
        p1 p3 ->
      program_rel
        (simrel_fundef_rel (F1:=F1) (F2:=F3) b12)
        (simrel_vardef_rel (V:=V) ng12 b12)
        p1 (simrel_uncompose_prog p1 p3) /\
      program_rel
        (simrel_fundef_rel (F1:=F3) (F2:=F3) b23)
        (simrel_vardef_rel (V:=V) ng23 b23)
        (simrel_uncompose_prog p1 p3) p3.
    Proof.
      intros H13.
      destruct H13 as [H13 HRF HRV].
      destruct H13 as [defs1 defs3 Hdefs main].
      split.
      - constructor.
        + constructor.
          apply simrel_globdefs_rel_uncompose; eauto.
        + intros i Hi.
          specialize (HRF i Hi).
          apply simrel_fundef_rel_compose in HRF.
          simpl in HRF.
          destruct HRF.
          assumption.
        + intros i Hi.
          specialize (HRV i Hi).
          apply simrel_vardef_rel_compose in HRV.
          simpl in HRV.
          destruct HRV.
          assumption.
        + simpl in *.
          assumption.
      - constructor.
        + constructor.
          apply simrel_globdefs_rel_uncompose; eauto.
        + intros i Hi.
          specialize (HRF i Hi).
          apply simrel_fundef_rel_compose in HRF.
          simpl in HRF.
          destruct HRF.
          assumption.
        + intros i Hi.
          specialize (HRV i Hi).
          apply simrel_vardef_rel_compose in HRV.
          simpl in HRV.
          destruct HRV.
          assumption.
        + simpl in *.
          subst main.
          apply globdefs_fw_bw_rel in Hdefs.
          induction Hdefs; simpl; eauto.
          rewrite IHHdefs.
          reflexivity.
    Qed.
  End UNCOMPOSE_PROGRAMS.

  Local Instance simrel_compose_prf R12 R23:
    SimulationRelation R12 ->
    SimulationRelation R23 ->
    SimulationRelation (simrel_compose_ops R12 R23).
  Proof.
    intros HR12 HR23.
    split.

    (** [≤] is a preorder *)
    - simpl.
      typeclasses eauto.

    (** [simrel_undef_matches_block] is compatible *)
    - intros [p1 p2] [p1' p2'] [Hp Hp'] v.
      simpl in *.
      rauto.

    (** [simrel_meminj] is compatible with the carrier order *)
    - intros [p1 p2] [p1' p2'] [Hp Hp'].
      simpl in *.
      solve_monotonic.

    (** [simrel_undef_matches_values] implies [simrel_undef_matches_block] *)
    - intros [p1 p2] ptr1 b3 ofs3.
      autorewrite with simrel.
      intros Hmv ([b2 ofs2] & Hptr12 & Hptr23).
      simpl in *.
      destruct Hmv as [Hmv12 | Hmv23];
      eauto 10 using @simrel_undef_matches_values_also_block.

    (** [simrel_undef_matches_block] implies [simrel_undef_matches_values] *)
    - intros [p1 p2] b3 Hmb.
      simpl in *.
      rewrite simrel_undef_matches_values_compose.
      destruct Hmb as [(b2 & Hb12 & Hb23) | ];
      eauto 10 using @simrel_undef_matches_block_also_values.

    (** [simrel_undef_matches_block] or at most one block injects. *)
    - simpl.
      intros [p12 p23] b3 b1 b1' H H0 H1.
      autorewrite with simrel in *.
      destruct H0 as (b2 & H12 & H23).
      destruct H1 as (b2' & H12' & H23').
      simpl.
      destruct (peq b2' b2).
      + subst.
        left.
        esplit.
        split; eauto.
        eapply (simrel_undef_matches_block_or_injective p12); eauto.
      + right.
        eapply (simrel_undef_matches_block_or_injective p23); eauto.

    (** [simrel_undef_matches_block] for non weakly valid pointers *)
    - simpl.
      intros [p12 p23] m1 m3 b1 ofs1 b3 ofs3.
      autorewrite with simrel.
      simpl.
      intros (m2 & Hm12 & Hm23) INVAL1.
      intros [[b2 ofs2] [Hb12 Hb23]].
      intros VAL3.
      destruct (Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned ofs2)) eqn:VAL2.
      + left.
        esplit.
        split; eauto.
        eapply simrel_undef_matches_block_invalid_weak; eauto.
      + right.
        eapply simrel_undef_matches_block_invalid_weak; eauto.

    (** [simrel_undef_matches_block] for invalid pointers *)
    - simpl.
      intros [p12 p23] m1 m3 b1 ofs1 b3 ofs3.
      autorewrite with simrel.
      simpl.
      intros (m2 & Hm12 & Hm23) INVAL1.
      intros [[b2 ofs2] [Hb12 Hb23]].
      intros VAL3.
      destruct (Mem.valid_pointer m2 b2 (Ptrofs.unsigned ofs2)) eqn:VAL2.
      + left.
        esplit.
        split; eauto.
        eapply simrel_undef_matches_block_invalid; eauto.
      + right.
        eapply simrel_undef_matches_block_invalid; eauto.             

    (** [match_block] for global blocks *)
    - intros [p1 p2] b Hb.
      pose proof (match_global_block_sameofs p1 b Hb) as H1.
      pose proof (match_global_block_sameofs p2 b Hb) as H2.
      unfold Proper, match_block_sameofs in *.
      simpl; unfold compose_meminj.
      rewrite H1, H2.
      reflexivity.

    (** [Genv.init_mem] *)
    - intros F V p1 p3 Hp.
      red in Hp.
      simpl in Hp.
      apply simrel_program_rel_uncompose in Hp.
      destruct Hp as [Hp12 Hp23].
      apply simrel_init_mem in Hp12.
      apply simrel_init_mem in Hp23.
      destruct Hp12 as [ | m1 m2 [p12 Hm12]]; [constructor | ].
      inversion Hp23 as [ | xm2 m3 [p23 Hm23] Hxm2 Hm3]; clear Hp23 Hm3; subst.
      constructor.
      exists (p12, p23).
      eexists; split; eauto.

    (** [Mem.alloc] *)
    - intros [p12 p23] m1 m3 (m2 & Hm12 & Hm23) lo hi.
      edestruct (simrel_alloc p23) as (p23' & Hp23' & Hm23' & Hb23'); eauto.
      edestruct (simrel_alloc p12) as (p12' & Hp12' & Hm12' & Hb12'); eauto.
      exists (p12', p23').
      simpl.
      split; split; eauto.
      ehtransitivity; eauto.

    (** [Mem.free] *)
    - intros [p12 p23] m1 m3 (m2 & Hm12 & Hm23).
      repeat rstep.
      destruct x as [[x1 x2] x3].
      destruct y as [[y1 y2] y3].
      simpl in *.
      rewrite match_ptrrange_simrel_compose in H; eauto.
      destruct H as ([[z1 z2] z3] & H12 & H23).
      destruct (Mem.free m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
      transport Hm1'.
      transport H.
      rewrite H1.
      rstep.
      reexists; repeat rstep.
      ehtransitivity; eauto.

    (** [Mem.load] *)
    - intros [p12 p23] chunk.
      autorewrite with simrel.
      intros m1 m3 (m2&Hm12&Hm23) p1 p3 (p2 & Hp12 & Hp23).
      destruct p1 as [b1 ofs1], p2 as [b2 ofs2], p3 as [b3 ofs3].
      simpl in *.
      ehtransitivity; solve_monotonic.

    (** [Mem.store] *)
    - intros [p12 p23] chunk.
      autorewrite with simrel.
      intros m1 m3 (m2 & Hm12 & Hm23).
      intros [b1 ofs1] [b3 ofs3] ([b2 ofs2] & Hp12 & Hp23).
      intros v1 v3 (v2 & Hv12 & Hv23).
      simpl in *.
      destruct (Mem.store _ m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
      transport Hm1'.
      transport H.
      rewrite H1.
      constructor.
      reexists; repeat rstep.
      ehtransitivity; eauto.

    (** [Mem.loadbytes] *)
    - intros [p12 p23] m1 m3 (m2 & Hm12 & Hm23).
      autorewrite with simrel.
      intros [b1 ofs1] [b3 ofs3]([b2 ofs2] & Hp12 & Hp23) n.
      simpl in *.
      rewrite list_rel_compose.
      ehtransitivity; solve_monotonic. 

    (** [Mem.storebytes] *)
    - intros [p12 p23] m1 m3 (m2 & Hm12 & Hm23).
      autorewrite with simrel.
      intros [b1 ofs1] [b3 ofs3]([b2 ofs2] & Hp12 & Hp23) v1 v3 Hv.
      rewrite @list_rel_compose in * by eauto.
      destruct Hv as (v2 & Hv12 & Hv23).
      simpl in *.
      destruct (Mem.storebytes m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
      transport Hm1'.
      transport H.
      rewrite H1.
      constructor.
      reexists; repeat rstep.
      ehtransitivity; eauto.

    (** [Mem.perm] *)
    - intros [p12 p23] m1 m3 (m2 & Hm12 & Hm23).
      autorewrite with simrel.
      intros [b1 ofs1] [b3 ofs3] ([b2 ofs2] & Hp12 & Hp23) k p.
      simpl in *.
      ehtransitivity; solve_monotonic.

    (** [Mem.valid_block] antitonic *)
    - intros [p12 p23] m1 m3 (m2 & Hm12 & Hm23) b1 b3.
      rewrite match_block_simrel_compose.
      intros (b2 & Hb12 & Hb23).
      etransitivity; solve_monotonic.

    (** [Mem.different_pointers_inject] *)
    - intros [p12 p23] m1 m3 b1 ofs1 b1' ofs1' b3 delta13 b3' delta13'.
      simpl.
      unfold compose_meminj.
      intros (m2 & Hm12 & Hm23) DIFF VAL VAL' J J'.
      destruct (simrel_meminj R12 p12 b1) as [ [b2 delta12] | ] eqn:J12;
        try discriminate.
      destruct (simrel_meminj R23 p23 b2) as [ [b3_ delta23] | ] eqn:J23;
        try discriminate.
      inversion J; clear J; subst.
      destruct (simrel_meminj R12 p12 b1') as [ [b2' delta12'] | ] eqn:J12';
        try discriminate.
      destruct (simrel_meminj R23 p23 b2') as [ [b3'_ delta23'] | ] eqn:J23';
        try discriminate.
      inversion J'; clear J'; subst.
      destruct (peq b2 b2').
      {
        subst.
        exploit (simrel_different_pointers_inject p12); eauto.
        intro DIFF12.
        destruct DIFF12 as [ | DIFF12 ] ; try congruence.
        right.
        replace b3' with b3 in * by congruence.
        replace delta23' with delta23 in * by congruence.
        repeat rewrite add_repr.
        repeat rewrite <- Ptrofs.add_assoc.
        intro ABSURD.
        apply (f_equal Ptrofs.repr) in ABSURD.
        repeat rewrite Ptrofs.repr_unsigned in ABSURD.
        apply (f_equal (fun z => Ptrofs.add z (Ptrofs.neg (Ptrofs.repr delta23))))
        in ABSURD.
        repeat rewrite Ptrofs.add_assoc in ABSURD.
        rewrite Ptrofs.add_neg_zero in ABSURD.
        repeat rewrite Ptrofs.add_zero in ABSURD.
        congruence.
      }
      repeat rewrite add_repr.
      repeat rewrite <- Ptrofs.add_assoc.
      eapply (simrel_different_pointers_inject p23); eauto.
      + rewrite Mem.valid_pointer_nonempty_perm.
        rewrite Mem.valid_pointer_nonempty_perm in VAL.
        change (Mem.permv m2 (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta12))) Nonempty).
        eapply (simrel_permv p12); eauto.
        {
          econstructor.
          econstructor.
          eassumption.
        }
        assumption.
      + rewrite Mem.valid_pointer_nonempty_perm.
        rewrite Mem.valid_pointer_nonempty_perm in VAL'.
        change (Mem.permv m2 (Vptr b2' (Ptrofs.add ofs1' (Ptrofs.repr delta12'))) Nonempty).
        eapply (simrel_permv p12); eauto.
        {
          econstructor.
          econstructor.
          eassumption.
        }
        assumption.

    (** [Mem.weak_valid_pointer_inject_val] *)
    - intros [p12 p23] m1 m3 b1 ofs1 b3 ofs3
             (m2 & Hm12 & Hm23) V1.
      autorewrite with simrel.
      simpl in Hm12, Hm23.
      intros [[b2 o2] [Hv12 Hv23]].
      eapply (simrel_weak_valid_pointer_inject_val p23); eauto.
      eapply (simrel_weak_valid_pointer_inject_val p12); eauto.

    (** [weak_valid_pointer_address_inject_weak] *)
    - simpl.
      intros [p12 p23] m1 m3 b1 b3 delta13.
      simpl.
      intros (m2 & Hm12 & Hm23).
      unfold compose_meminj.
      destruct (simrel_meminj R12 _ _) as [ [ b2 delta12 ] | ]
      eqn:INJ12;
        try discriminate.
      destruct (simrel_meminj R23 _ _) as [ [ b3_ delta23 ] | ]
      eqn:INJ23;
        try discriminate.
      intro K.
      inversion K; clear K; subst.
      generalize (simrel_weak_valid_pointer_address_inject_weak _ _ _ _ _ _ Hm12 INJ12).
      destruct 1 as (delta12' & Hdelta12').
      generalize (simrel_weak_valid_pointer_address_inject_weak _ _ _ _ _ _ Hm23 INJ23).
      destruct 1 as (delta23' & Hdelta23').
      exists (delta12' + delta23').
      intros ofs1 H.
      rewrite add_repr.
      rewrite <- Ptrofs.add_assoc.
      rewrite Hdelta23'.
      * rewrite Hdelta12' by assumption.
        omega.
      * eapply (simrel_weak_valid_pointer_inject_val p12); eauto.
        constructor.
        assumption.

    (** [Mem.address_inject] *)
    - intros [p12 p23] m1 m3 b1 ofs1 b3 delta13 pe (m2 & Hm12 & Hm23).
      intros PERM.
      simpl.
      intros INJ.
      simpl in *.
      unfold compose_meminj in INJ.
      destruct (simrel_meminj R12 p12 b1) as [ [b2 delta12] | ] eqn:INJ12 ; try discriminate.
      destruct (simrel_meminj R23 p23 b2) as [ [b3_ delta23] | ] eqn:INJ23; try discriminate.
      inversion INJ; clear INJ; subst.
      rewrite Z.add_assoc.
      generalize (simrel_address_inject _ _ _ _ _ _ _ _ Hm12 PERM INJ12).
      intro EQ12.
      rewrite <- EQ12.
      assert (match_ptr R12 p12 (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs1 + delta12)) as MATCH12.
      {
        constructor.
        assumption.
      }
      generalize (simrel_perm _ _ _ Hm12 _ _ MATCH12 _ _ PERM).
      intro PERM2.
      simpl in PERM2.
      rewrite <- EQ12 in PERM2.
      generalize (simrel_address_inject _ _ _ _ _ _ _ _ Hm23 PERM2 INJ23).
      intro EQ23.
      rewrite <- EQ23.
      f_equal.
      rewrite Ptrofs.add_assoc.
      f_equal.
      rewrite Ptrofs.add_unsigned.
      auto using Ptrofs.eqm_samerepr,
      Ptrofs.eqm_add, Ptrofs.eqm_unsigned_repr.

    (** [Mem.aligned_area_inject] *)
    - intros (p12 & p23) m m' b ofs al sz b' delta (m2 & Hm12 & Hm23) H0 H1 H2 H3 H4 H5.
      simpl in H5.
      unfold compose_meminj in H5.
      destruct (simrel_meminj R12 p12 b) as [ [b2 delta12] | ] eqn:INJ12; try discriminate.
      destruct (simrel_meminj R23 p23 b2) as [ [b3 delta23] | ] eqn:INJ23; try discriminate.
      inversion H5; clear H5; subst.
      rewrite Z.add_assoc.
      generalize (simrel_aligned_area_inject _ _ _ _ _ _ _ _ _ Hm12 H0 H1 H2 H3 H4 INJ12).
      intro ALIGN2.
      assert (Mem.range_perm m2 b2 (ofs + delta12) (ofs + delta12 + sz) Cur Nonempty) as PERM2.
      {
        red.
        intros ofs0 H.
        replace ofs0 with (ofs0 - delta12 + delta12) by omega.
        apply (simrel_perm _ _ _ Hm12 (b, ofs0 - delta12) (b2, ofs0 - delta12 + delta12)).
        {
          econstructor; eauto.
        }
        red.
        eapply H3.
        omega.
      }
      exact (simrel_aligned_area_inject _ _ _ _ _ _ _ _ _ Hm23 H0 H1 H2 PERM2 ALIGN2 INJ23).

    (** [Mem.disjoint_or_equal_inject] *)
    - intros p m_1 m_3 b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz (m_2 & Hm_12 & Hm_23) H0 H1 H2 H3 H4 H5.
      simpl in H0, H1.
      unfold compose_meminj in H0, H1.
      destruct (simrel_meminj R12 (fst p) b1) as [ [b1_2 delta1_12] | ] eqn:INJ1_12 ; try discriminate.
      destruct (simrel_meminj R23 (snd p) b1_2) as [ [b1_3 delta1_23] | ] eqn:INJ1_23 ; try discriminate.
      inversion H0; clear H0; subst.
      destruct (simrel_meminj R12 (fst p) b2) as [ [b2_2 delta2_12] | ] eqn:INJ2_12 ; try discriminate.
      destruct (simrel_meminj R23 (snd p) b2_2) as [ [b2_3 delta2_23] | ] eqn:INJ2_23 ; try discriminate.
      inversion H1; clear H1; subst.
      repeat rewrite Z.add_assoc.
      generalize (simrel_disjoint_or_equal_inject
      _ _ _ _ _ _ _ _ _ _ _ _ Hm_12 INJ1_12 INJ2_12 H2 H3 H4 H5).
      intro DOE.
      assert (Mem.range_perm m_2 b1_2 (ofs1 + delta1_12) (ofs1 + delta1_12 + sz) Max Nonempty) as PERM1_2.
      {
        red. intros.
        replace ofs with (ofs - delta1_12 + delta1_12) by omega.
        apply (simrel_perm _ _ _ Hm_12 (b1, ofs - delta1_12) (_, _)).
        {
          constructor.
          assumption.
        }
        simpl. apply H2. omega.
      }
      assert (Mem.range_perm m_2 b2_2 (ofs2 + delta2_12) (ofs2 + delta2_12 + sz) Max Nonempty) as PERM2_2.
      {
        red. intros.
        replace ofs with (ofs - delta2_12 + delta2_12) by omega.
        apply (simrel_perm _ _ _ Hm_12 (b2, ofs - delta2_12) (_, _)).
        {
          constructor.
          assumption.
        }
        simpl. apply H3. omega.
      }
      exact (simrel_disjoint_or_equal_inject
      _ _ _ _ _ _ _ _ _ _ _ _ Hm_23 INJ1_23 INJ2_23 PERM1_2 PERM2_2 H4 DOE).
  Qed.

  Definition simrel_compose: simrel D1 D2 -> simrel D2 D3 -> simrel D1 D3 :=
    fun R12 R23 =>
      {|
        simrel_ops := simrel_compose_ops R12 R23
      |}.

  Global Instance simrel_compose_equiv:
    Monotonic
      simrel_compose
      (simrel_equiv ++> simrel_equiv ++> simrel_equiv).
  Proof.
    clear.
    intros R12 S12 [f Hf] R23 S23 [g Hg].
    exists
      (Build_simrel_equiv_maps
         (simrel_compose R12 R23)
         (simrel_compose S12 S23)
         (fun p => match p with
                     | (p12, p23) =>
                       (simrel_equiv_fw f p12, simrel_equiv_fw g p23)
                   end)
         (fun q => match q with
                     | (q12, q23) =>
                       (simrel_equiv_bw f q12, simrel_equiv_bw g q23)
                   end)).
    split;
    try destruct p as [p12 p23];
    try destruct q as [q12 q23];
    simpl;
    simrel_equiv_rewrite;
    try reflexivity;
    repeat rstep;
    try (destruct H; destruct x; destruct y; rauto).
    - simpl.
      intros b [(b' & SUMB & Hb)|SUMB]; auto.
      left; eexists; split; eauto.
      eapply simrel_equiv_undef_matches_block_fw; eauto.
      eapply match_block_simrel_equiv_fw; eauto.
      right; eapply simrel_equiv_undef_matches_block_fw; eauto.
    - simpl.
      intros b [(b' & SUMB & Hb)|SUMB]; auto.
      left; eexists; split; eauto.
      eapply simrel_equiv_undef_matches_block_bw; eauto.
      eapply match_block_simrel_equiv_bw; eauto.
      right; eapply simrel_equiv_undef_matches_block_bw; eauto.
    - apply match_mem_simrel_equiv_fw.
    - apply match_mem_simrel_equiv_fw.
    - apply match_mem_simrel_equiv_bw.
    - apply match_mem_simrel_equiv_bw.
    - intros.
      unfold compose_meminj.
      generalize (simrel_equiv_meminj_fw p12 b).
      inversion 1; try constructor. subst.
      destruct y.
      generalize (simrel_equiv_meminj_fw p23 b0).
      inversion 1; try constructor. subst.
      destruct y. constructor; auto.
    - intros.
      unfold compose_meminj.
      generalize (simrel_equiv_meminj_bw p12 b).
      inversion 1; try constructor. subst.
      destruct y.
      generalize (simrel_equiv_meminj_bw p23 b0).
      inversion 1; try constructor. subst.
      destruct y. constructor; auto.
    - intros (p12 & p23).
      split; simpl; apply simrel_bw_fw_le.
    - intros (p12 & p23).
      split; simpl; apply simrel_fw_bw_le.
  Qed.
End COMPOSE.

Global Instance: Params (@simrel_compose) 2.


(** ** Categorical properties *)

Section CATEGORY.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2 D3 D4: layerdata}.

  Lemma simrel_compose_id_left (R: simrel D1 D2):
    simrel_equiv (simrel_compose R simrel_id) R.
  Proof.
    exists
      (Build_simrel_equiv_maps (simrel_compose R simrel_id) R
         (fun p => fst p)
         (fun q => (q, tt))).
    split; try destruct p as [p []]; simpl;
      rewrite ?orb_false_r;
      try reflexivity;
      try now solve_monotonic.
    - symmetry. apply app_nil_end.
    - rewrite match_block_simrel_id.
      intro b.
      intros [(b' & Hb' & Hb)|H]; try tauto.
      congruence.
    - rewrite match_block_simrel_id.
      intros p b SUMB. eauto.
    - apply rel_compose_id_left.
    - intros; apply rel_compose_id_left.
    - intro b.
      unfold compose_meminj, inject_id.
      destruct (simrel_meminj _ _ _) as [[? ?]|]; constructor; eauto.
      replace (z+0) with z by omega; eauto.
    - intros.
      unfold compose_meminj, inject_id.
      destruct (simrel_meminj _ _ _) as [[? ?]|]; constructor; eauto.
      replace (z+0) with z by omega; eauto.
  Qed.

  Lemma simrel_compose_id_right (R: simrel D1 D2):
    simrel_equiv (simrel_compose simrel_id R) R.
  Proof.
    exists
      (Build_simrel_equiv_maps (simrel_compose simrel_id R) R
         (fun p => snd p)
         (fun q => (tt, q))).
    split; try destruct p as [[] p]; simpl;
      rewrite ?orb_false_l;
      try reflexivity;
      try now solve_monotonic.
    - intros b [(b' & Hb' & Hb)|H]; try tauto.
    - intros p b A. eauto.
    - apply rel_compose_id_right.
    - intros; apply rel_compose_id_right.
    - unfold compose_meminj, inject_id.
      intros; destruct (simrel_meminj _ _ _) as [[? ?]|]; constructor; eauto.
    - unfold compose_meminj, inject_id.
      intros; destruct (simrel_meminj _ _ _) as [[? ?]|]; constructor; eauto.
  Qed.

  Hint Extern 2 (rel_compose ?R12 ?R23 ?x ?z) => eexists; split.

  Lemma simrel_compose_assoc:
    forall (R12: simrel D1 D2) (R23: simrel D2 D3) (R34: simrel D3 D4),
      simrel_equiv
        (simrel_compose (simrel_compose R12 R23) R34)
        (simrel_compose R12 (simrel_compose R23 R34)).
  Proof.
    intros.
    exists
      (Build_simrel_equiv_maps
         (simrel_compose (simrel_compose R12 R23) R34)
         (simrel_compose R12 (simrel_compose R23 R34))
         (fun p => match p with ((p1, p2), p3) => (p1, (p2, p3)) end)
         (fun q => match q with (q1, (q2, q3)) => ((q1, q2), q3) end)).
    split;      
      try destruct p as [[p1 p2] p3];
      try destruct q as [q1 [q2 q3]];
      simpl; clear; try firstorder.
    - repeat rstep;
      destruct x as [ [ ? ? ] ? ];
      destruct y as [ [ ? ? ] ? ];
      firstorder.
    - repeat rstep;
      destruct x as [ ? [ ? ? ] ];
      destruct y as [ ? [ ? ? ] ];
      firstorder.
    - rewrite match_block_simrel_compose.
      intros [[b' [[(? & ? & ?)|?] ?]] | ?]; eauto 10.
    - destruct p. destruct p. simpl.
      rewrite match_block_simrel_compose.
      intros [(b' & Hb & Hb1)|[(b' & Hb & Hb1)|Hb]]; eauto 10.
      unfold rel_compose in Hb1. destruct Hb1 as (b'' & Hb1 & Hb2). eauto 10.
    - intros. destruct p. destruct p. simpl. apply rel_compose_assoc.
    - unfold compose_meminj.
      destruct (simrel_meminj R12 _ _) as [[? ?]|]; try constructor; eauto.
      destruct (simrel_meminj R23 _ _) as [[? ?]|]; try constructor; eauto.
      destruct (simrel_meminj R34 _ _) as [[? ?]|]; try constructor; eauto.
      rewrite Z.add_assoc.
      reflexivity.
    - unfold compose_meminj. simpl. destruct p. destruct p.
      destruct (simrel_meminj R12 _ _) as [[? ?]|]; try constructor; eauto.
      destruct (simrel_meminj R23 _ _) as [[? ?]|]; try constructor; eauto.
      destruct (simrel_meminj R34 _ _) as [[? ?]|]; try constructor; eauto.
      rewrite Z.add_assoc.
      reflexivity.
    - destruct w as ((p12 & p23) & p34); simpl. reflexivity.
    - destruct w as ((p12 & p23) & p34); simpl. reflexivity.
    - destruct w as ((p12 & p23) & p34); simpl. reflexivity.
    - destruct w as (p12 & p23 & p34); simpl. reflexivity.
    - destruct w as (p12 & p23 & p34); simpl. reflexivity.
    - destruct w as (p12 & p23 & p34); simpl. reflexivity.
  Qed.
End CATEGORY.


(** ** [simrel] is a [Category] *)

Section SIMREL.
  Context `{Hmem: BaseMemoryModel}.

  Global Instance simrel_cat_ops: CategoryOps layerdata simrel :=
    {
      cat_equiv D1 D2 := {| equiv := simrel_equiv |};
      cat_id D := {| id := simrel_id |};
      cat_compose D1 D2 D3 := {| compose := simrel_compose |}
    }.

  Global Instance simrel_cat_prf: Category layerdata simrel.
  Proof.
    split; try typeclasses eauto; intros; simpl.
    - apply simrel_compose_id_left.
    - apply simrel_compose_id_right.
    - apply simrel_compose_assoc.
  Qed.
End SIMREL.
