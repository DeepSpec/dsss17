Require Import Coq.Program.Basics.
Require Import LogicalRelations.
Require Import SimulationRelation.
Require Import Structures.
Require Import OptionOrders.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Local Opaque mwd_ops.

(** * [lessdef] (and [Mem.extends]) as a simulation relation *)

Section LESSDEF_SIMREL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Definition simrel_lessdef_ops: simrel_components D D :=
    {|
      simrel_world := unit;
      simrel_acc := {| Structures.le x y := True |};
      simrel_undef_matches_values_bool := true;
      simrel_undef_matches_block p b := True;
      simrel_new_glbl := nil;
      simrel_meminj p := inject_id;
      match_mem p := Mem.extends
    |}.

  Require Import ExtensionalityAxioms.

  Lemma match_ptr_simrel_lessdef p:
    match_ptr simrel_lessdef_ops p = eq.
  Proof.
    eapply functional_extensionality; intros [b1 o1].
    eapply functional_extensionality; intros [b2 o2].
    eapply prop_ext.
    split.
    - destruct 1; simpl in *; subst; try constructor.
      inversion H; subst.
      f_equal.
      omega.
    - destruct 1.
      apply match_block_sameofs_ptr; auto.
      reflexivity.
  Qed.

  Lemma match_ptrbits_simrel_lessdef p:
    match_ptrbits simrel_lessdef_ops p = eq.
  Proof.
    eapply functional_extensionality; intros [b1 o1].
    eapply functional_extensionality; intros [b2 o2].
    eapply prop_ext.
    split.
    - destruct 1; simpl in *; subst; try constructor.
      inversion H; subst.
      rewrite Ptrofs.add_zero.
      reflexivity.
    - destruct 1.
      apply match_block_sameofs_ptrbits; auto.
      reflexivity.
  Qed.

  Lemma match_ptrrange_simrel_lessdef p:
    match_ptrrange simrel_lessdef_ops p = eq.
  Proof.
    eapply functional_extensionality; intros [[b1 lo1] hi1].
    eapply functional_extensionality; intros [[b2 lo2] hi2].
    eapply prop_ext.
    split.
    - destruct 1.
      inversion H; simpl in *.
      inversion H1; simpl in *.
      rewrite Z.add_0_r.
      reflexivity.
    - inversion 1; subst.
      replace hi2 with (lo2 + (hi2 - lo2)) by omega.
      constructor.
      pattern lo2 at 2.
      replace lo2 with (lo2 + 0) by omega.
      constructor.
      reflexivity.
  Qed.

  Lemma match_block_simrel_lessdef p:
    match_block simrel_lessdef_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - intros b1 b2 [delta Hdelta].
      inversion Hdelta.
      reflexivity.
    - intros b1 b2 H; subst.
      eexists.
      reflexivity.
  Qed.

  Lemma match_block_sameofs_simrel_lessdef p:
    match_block_sameofs simrel_lessdef_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - intros b1 b2 Hb.
      inversion Hb.
      reflexivity.
    - intros b1 b2 H; subst.
      constructor.
  Qed.

  Lemma match_val_simrel_lessdef p:
    match_val simrel_lessdef_ops p = Val.lessdef.
  Proof.
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext.
    split.
    - destruct 1; simpl in *; subst; try constructor.
      rewrite match_ptrbits_simrel_lessdef in H.
      inversion H; subst.
      reflexivity.
    - destruct 1.
      + destruct v; try constructor.
        rewrite match_ptrbits_simrel_lessdef.
        reflexivity.
      + destruct v; constructor; constructor.
  Qed.

  Lemma match_memval_simrel_lessdef p:
    match_memval simrel_lessdef_ops p = memval_lessdef.
  Proof.
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext.
    split.
    - destruct 1; simpl in *; subst; try constructor.
      destruct H; try constructor.
      inversion H; subst.
      inversion H1; subst.
      econstructor.      
      reflexivity.
      reflexivity.
    - destruct 1.
      + constructor.
      + constructor.
        rewrite match_val_simrel_lessdef.
        destruct H; try constructor; eauto.
        inversion H; clear H; subst.
        rewrite Ptrofs.add_zero.
        reflexivity.
      + destruct mv; constructor; try constructor.
        rewrite match_val_simrel_lessdef.
        constructor.
  Qed.

  (** Initial memory *)

  Require Import InitMemRel.

  Lemma store_zeros_right_extends:
    forall (m2: mwd D) b lo hi m2',
      store_zeros m2 b lo hi = Some m2' ->
      forall m1, Mem.extends m1 m2 ->
                 (forall o k p, Mem.perm m1 b o k p -> False) ->
                 Mem.extends m1 m2'.
  Proof.
    intros until hi.
    functional induction (store_zeros m2 b lo hi); try congruence.
    intros. eapply IHo; eauto using (Mem.store_outside_extends (mem := mwd D)).
  Qed.

(* XXX: coqrel *)

Global Instance prod_rel_fst {A1 A2 B1 B2} (RA: rel A1 A2) (RB: rel B1 B2):
  Related (prod_rel RA RB) (RA @@ fst)%rel subrel.
Proof.
  clear.
  firstorder.
Qed.

Global Instance prod_rel_snd {A1 A2 B1 B2} (RA: rel A1 A2) (RB: rel B1 B2):
  Related (prod_rel RA RB) (RB @@ snd)%rel subrel.
Proof.
  clear.
  firstorder.
Qed.

Global Instance option_ifsome_le_subrel {A B} (R: rel A B):
  Related (option_le R) (option_ifsome_rel R) subrel.
Proof.
  destruct 1; red; congruence.
Qed.

Global Instance: Params (@Mem.drop_perm) 5.

  Global Instance simrel_lessdef_init_mem {F1 F2 V} ng umv:
    InitMemSimrel (D1:=D) (D2:=D) (F1:=F1) (F2:=F2) (V:=V)
      ng umv
      (fun _ _ _ _ => Mem.extends).
  Proof.
    assert (forall i, simrel_newfun_ok nil true i).
    {
      intros i.
      split; reflexivity.
    }
    assert (forall i init, simrel_newvar_ok nil true i init).
    {
      intros i init.
      right.
      split; reflexivity.
    }
    split; intros.
    - apply Mem.extends_refl.
    - intros m1 m2 Hm.
      unfold alloc_none.
      destruct (Mem.alloc m1 _ _) as [m1' b] eqn:Hm1'.
      edestruct (Mem.alloc_extends m1 m2) as (m2' & Hm2' & Hm'); eauto.
      + reflexivity.
      + reflexivity.
      + rewrite Hm2'.
        constructor.
        eauto.
    - intros m1 m2 Hm.
      unfold alloc_none, alloc_fun.
      destruct (Mem.alloc m1 _ _) as [m1' b] eqn:Hm1'.
      edestruct (Mem.alloc_extends m1 m2) as (m2' & Hm2' & Hm'); eauto.
      + reflexivity.
      + instantiate (1:=1).
        omega.
      + rewrite Hm2'.
        edestruct (Mem.range_perm_drop_2 m2' b 0 1 Nonempty) as [m2'' Hm2''].
        {
          intros ofs Hofs.
          eapply Mem.perm_alloc_2; eauto.
        }
        rewrite Hm2''.
        constructor.
        eapply Mem.drop_perm_right_extends; eauto.
        intros ofs k p Hp Hofs.
        eapply Mem.perm_alloc_3 in Hp; eauto.
        omega.
    - split.
      + assumption.
      + intros sz Hsz m1 m2 Hm.
        destruct (Mem.alloc m1 _ _) as [m1' b1] eqn:Hm1'; simpl.
        edestruct (Mem.alloc_extends m1 m2) as (m2' & Hm2' & Hm');
        rewrite ?Hm2'; eauto.
        * reflexivity.
        * subst.
          apply genv_init_data_list_size_pos.
      + intros p sz m1 m2 m2' Hsz Hm1 Hm2' Hm.
        eapply Mem.store_outside_extends; eauto.
        intros ofs Hofs _.
        eapply Hm1; eauto.
      + intros sz ge1 ge2 base next m1 m2 m2' Hsz Hm1 Hge Hm2' Hm.
        eapply Genv.store_init_data_right_extends; eauto.
        intros.
        eapply Hm1; eauto.
      + intros sz m1 m2 m2' Hsz Hm1 Hm2' Hm.
        eapply Mem.drop_perm_right_extends; eauto.
        intros.
        eapply Hm1; eauto.
    - intros m1 m2 Hm.
      unfold alloc_fun.
      destruct (Mem.alloc m1 _ _) as [m1' b1] eqn:Hm1'.
      transport Hm1'.
      rewrite H1; subst.
      solve_monotonic.
    - split.
      + reflexivity.
      + intros.
        solve_monotonic.
      + intros.
        solve_monotonic.
      + intros sz base next Hsz ge1 ge2 Hge m1 m2 Hm m1' m2' Hm1' Hm2'.
        edestruct (Genv.store_init_data_parallel_extends (mem := mwd D) ge1) as (?&?&?); eauto.
        erewrite (Genv.store_init_data_symbols_preserved ge1 ge2) in Hm2'.
        congruence.
        intro.
        rewrite !stencil_matches_symbols by eauto.
        reflexivity.
      + unfold alloc_var_perm.
        intros.
        solve_monotonic.
  Qed.

  Global Instance simrel_lessdef_prf:
    SimulationRelation simrel_lessdef_ops.
  Proof.
    assert (Heqsub: forall A B, subrel (@eqrel A B) (@subrel A B)).
    {
      intros A B x y H.
      repeat red in H.
      tauto.
    }
    constructor; try now repeat constructor.

    (** [Genv.init_mem] *)
    - intros.
      eapply genv_init_mem_simrel.
      + typeclasses eauto.
      + simpl.
        intros m1 m2 Hm.
        exists tt; solve_monotonic.

    (** [Mem.alloc] *)
    - exists tt.
      split; simpl; eauto.
      destruct (Mem.alloc x _ _) eqn:Halloc1.
      simpl in H.
      edestruct (Mem.alloc_extends x) as (? & Halloc2 & ?); eauto; try reflexivity.
      rewrite Halloc2.
      constructor; eauto.
      reflexivity.

    (** [Mem.free] *)
    - repeat red.
      simpl.
      inversion 2; subst.
      rewrite match_ptr_simrel_lessdef in H1.
      inversion H1; subst.
      simpl.
      destruct (Mem.free x _ _ _) eqn:Hfree1; try constructor.
      edestruct (Mem.free_parallel_extends x) as (? & Hfree2 & ?); eauto.
      rewrite Hfree2.
      constructor.
      exists p; eauto.

    (** [Mem.load] *)
    - intro p.
      rewrite match_val_simrel_lessdef.
      rewrite match_ptr_simrel_lessdef.
      simpl.
      repeat red.
      intros a x y H x0 y0 H0.
      subst.
      destruct y0.
      simpl.
      destruct (Mem.load _ x _ _) eqn:Hload; try constructor.
      edestruct (Mem.load_extends a x) as (? & Hload2 & ?); eauto.
      rewrite Hload2.
      constructor; assumption.

    (** [Mem.store] *)
    - intro p.
      rewrite match_val_simrel_lessdef.
      rewrite match_ptr_simrel_lessdef.
      simpl.
      repeat red.
      intros a x y H x0 y0 H0 x1 y1 H1.
      subst.
      destruct y0.
      simpl.
      destruct (Mem.store _ x _ _ _) eqn:Hstore1; try constructor.
      edestruct (Mem.store_within_extends a x) as (? & Hstore2 & ?); eauto.
      rewrite Hstore2.
      constructor.
      exists p; eauto.

    (** [Mem.loadbytes] *)
    - intro p.
      rewrite match_memval_simrel_lessdef.
      rewrite match_ptr_simrel_lessdef.
      repeat red.
      intros x y H x0 y0 H0 a.
      subst.
      destruct y0.
      simpl in *.
      destruct (Mem.loadbytes x _ _ _) eqn:Hlb1; try constructor.
      edestruct (Mem.loadbytes_extends x) as (? & Hlb2 & ?); eauto.
      rewrite Hlb2.
      constructor.
      rewrite <- CompcertStructures.list_forall2_list_rel; assumption.

    (** [Mem.storebytes] *)
    - intro p.
      rewrite match_memval_simrel_lessdef.
      rewrite match_ptr_simrel_lessdef.
      repeat red.
      intros x y H x0 y0 H0 x1 y1 H1.
      subst.
      destruct y0.
      simpl in *.
      destruct (Mem.storebytes x _ _ _) eqn:Hsb1; try constructor.
      edestruct (Mem.storebytes_within_extends x) as (? & Hsb2 & ?); eauto.
      { rewrite CompcertStructures.list_forall2_list_rel; eassumption. }
      rewrite Hsb2.
      constructor.
      exists p; eauto.

    (** [Mem.perm] *)
    - intros p.
      rewrite match_ptr_simrel_lessdef.
      repeat red.
      intros x y H x0 y0 H0 a a0 H1.
      subst.
      destruct y0.
      simpl in *.
      eapply Mem.perm_extends; eauto.

    (** [Mem.valid_block] *)
    - intros p.
      rewrite match_block_simrel_lessdef.
      simpl.
      intros m1 m2 Hm b1 b2 Hb; subst.
      eapply Mem.valid_block_extends; eauto.

    (** [Mem.different_pointers_inject] *)
    - inversion 5; subst.
      inversion 1; subst.
      tauto.

    (** [Mem.weak_valid_pointer_inject_val] *)
    - intros p m1 m2 b1 ofs1 b2 ofs2 H H0 H1.
      rewrite match_ptrbits_simrel_lessdef in H1.
      inversion H1; clear H1; subst.
      eapply Mem.weak_valid_pointer_extends; eauto.

    (** [Mem.weak_valid_pointer_address_inject_weak] *)
    - intros p m1 m2 b1 b2 delta H H0.
      inversion H0; clear H0; subst.
      exists 0.
      intros ofs1 H0.
      rewrite Ptrofs.add_zero.
      omega.

    (** [Mem.address_inject *)
    - simpl.
      inversion 4; subst.
      rewrite Ptrofs.add_zero.
      omega.

    (** [Mem.aligned_area_inject] *)
    - simpl.
      inversion 8; subst.
      rewrite Z.add_0_r.
      assumption.

    (** [Mem.disjoint_or_equal_inject] *)
    - simpl.
      inversion 3; subst.
      inversion 1; subst.
      repeat rewrite Z.add_0_r.
      tauto.
  Qed.

  Definition ext :=
    {|
      simrel_ops := simrel_lessdef_ops
    |}.
End LESSDEF_SIMREL.

(* Memory extension is absorbed by any other simulation relation
   with Vundef/Undef as lower bounds. *)

Section EXTENDS_COMPOSE.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  Program  (* improves type checking. *)
  Definition equiv_extends_compose_left:
    simrel_equiv_maps (simrel_compose (ext (D:=D1)) R) R
    :=
      {|
        simrel_equiv_fw := snd;
        simrel_equiv_bw q := (tt, q)
      |}.

  Program  (* improves type checking. *)
  Definition equiv_extends_compose_right:
    simrel_equiv_maps (simrel_compose R (ext (D:=D2))) R
    :=
      {|
        simrel_equiv_fw := fst;
        simrel_equiv_bw q := (q, tt)
      |}.

  Hypothesis undef_values:
    simrel_undef_matches_values R.

  Section LEFT.

    Hypothesis undef_block:
      forall p b,
        (exists b' : block, match_block R p b' b) ->
        simrel_undef_matches_block R p b.

    Hypothesis compose_left:
      forall p m1 m2 m3,
        Mem.extends m1 m2 ->
        match_mem R p m2 m3 ->
        match_mem R p m1 m3.

    Theorem extends_compose_left:
      SimulationRelationEquivalence _ _ equiv_extends_compose_left.
    Proof.
      constructor; simpl; auto; try tauto; try (compute; tauto).
      + intros p.
        intro b.
        destruct 1 as [ [ ? [ ? ? ] ] | ] ; eauto.
      + intros p.
        intros m1 m3 (m2 & Hm1 & Hm2). eauto.
      + intros p m1 m2 Hm.
        exists m1; split; auto. apply Mem.extends_refl.
      + intros p b. unfold compose_meminj, inject_id.
        destruct (simrel_meminj R (snd p) b) as [ [ ? ? ] | ] ; constructor; auto.
      + intros p b.
        unfold compose_meminj, inject_id.
        destruct (simrel_meminj R p b) as [ [ ? ? ] | ] ; constructor; auto.
      + intros [u p]. split; simpl; auto. reflexivity.
      + intros p. reflexivity.
    Qed.

  End LEFT.

  Section RIGHT.

    Hypothesis undef_block:
      forall p b,
        simrel_undef_matches_block R p b.

    Hypothesis compose_right:
      forall p m1 m2 m3,
        match_mem R p m1 m2 ->
        Mem.extends m2 m3 ->
        match_mem R p m1 m3.

    Theorem extends_compose_right:
      SimulationRelationEquivalence _ _ equiv_extends_compose_right.
    Proof.
      constructor; simpl; auto; try tauto; try (compute; tauto).
      + red in undef_values.
        rewrite undef_values.
        reflexivity.
      + symmetry; apply app_nil_end.
      + intros p b. intro H. apply undef_block.
      + intros p m1 m3 (m2 & Hm12 & Hm23). eauto.
      + intros p m1 m2 Hm12.
        exists m2; split; auto.
        apply Mem.extends_refl.
      + intros p b.
        unfold compose_meminj, inject_id.
        destruct (simrel_meminj R (fst p) b) as [ [ ? ? ] | ] ; constructor; auto.
        rewrite Z.add_0_r; reflexivity.
      + intros p b. unfold compose_meminj, inject_id.
        destruct (simrel_meminj R p b) as [ [ ? ? ] | ] ; constructor; auto.
        rewrite Z.add_0_r; reflexivity.
      + intros [u p]; split; simpl; reflexivity.
      + intros p; simpl; reflexivity.
    Qed.

  End RIGHT.

End EXTENDS_COMPOSE.

(* As an application, memory extension is idempotent. *)

Section EXTENDS_IDEM.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Global Instance extends_compose:
    SimulationRelationEquivalence _ _ (equiv_extends_compose_right (ext (D:=D))).
  Proof.
    apply extends_compose_right; simpl; auto.
    - reflexivity.
    - intro.
      apply Mem.extends_extends_compose.
  Qed.
End EXTENDS_IDEM.


(** * Strong version of extends for [ec_mem_extends]. Coincidentally,
      it will also work for [ec_max_perm] and [ec_valid_block] (which
      are necessary for Mem.unchanged_on to work).
      To factor proofs, we enrich it with [ec_readonly].
 *)

Section STRONG_LESSDEF_SIMREL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Record strong_extends_carrier: Type :=
    mk_strong_extends_carrier
    {
      strong_extends_high: mwd D;
      strong_extends_low: mwd D;
      strong_extends_prop: Mem.extends strong_extends_high strong_extends_low
    }.

  Lemma strong_extends_carrier_eq mm1 mm2:
    strong_extends_high mm1 = strong_extends_high mm2 ->
    strong_extends_low mm1 = strong_extends_low mm2 ->
    mm1 = mm2.
  Proof.
    intros H H0.
    destruct mm1; destruct mm2; simpl in * |- * ; subst.
    f_equal;
      apply ProofIrrelevance.proof_irrelevance.
  Qed.

  Definition strong_extends (mm: strong_extends_carrier) m m': Prop :=
    m = strong_extends_high mm /\
    m' = strong_extends_low mm.

  Lemma strong_extends_intro m m':
    Mem.extends m m' ->
    { mm | strong_extends mm m m' }.
  Proof.
    intros H.
    exists (mk_strong_extends_carrier _ _ H).
    split; auto.
  Qed.

  Lemma strong_extends_elim mm m m':
    strong_extends mm m m' ->
    Mem.extends m m'.
  Proof.
    unfold strong_extends.
    destruct mm; simpl; intuition congruence.
  Qed.

  Hint Resolve strong_extends_elim.

  Definition strong_extends_le (mm1 mm2: strong_extends_carrier): Prop :=
    let m1 := strong_extends_high mm1 in
      let m'1 := strong_extends_low mm1 in
      let m2 := strong_extends_high mm2 in
      let m'2 := strong_extends_low mm2 in
      Mem.unchanged_on (Events.loc_not_writable m1) m1 m2 /\
      Mem.unchanged_on (Events.loc_out_of_bounds m1) m'1 m'2 /\
      (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b) /\
      (forall b o p, Mem.valid_block m1 b -> Mem.perm m2 b o Max p -> Mem.perm m1 b o Max p).

  Local Instance strong_extends_le_refl:
    Reflexive strong_extends_le.
  Proof.
    red. intros [m m' ?]; simpl.
    unfold strong_extends_le. simpl.
    constructor; auto using (Mem.unchanged_on_refl (mem := mwd D)).
  Qed.

  Local Instance strong_extends_le_trans:
    Transitive strong_extends_le.
  Proof.
    red.
    intros [m1 m'1 ?] [m2 m'2 ?] [m3 m'3 ?].
    unfold strong_extends_le. simpl.
    destruct 1 as (? & ? & ? & ?).
    destruct 1 as (? & ? & ? & ?).
    split.
    {
      eapply Mem.unchanged_on_trans_strong with (Q := Events.loc_not_writable m2); eauto.
      unfold Events.loc_not_writable.
      intros b H5_ o H6_.
      intro ABSURD.
      apply H6_.
      eapply H2; eauto.
    }
    split; auto.
    eapply Mem.unchanged_on_trans_strong with (Q := Events.loc_out_of_bounds m2); eauto.
    unfold Events.loc_out_of_bounds.
    intros b H5_ o H6_.
    intro ABSURD.
    apply H6_.
    eapply H2; eauto.
    erewrite Mem.valid_block_extends; eauto.
  Qed.

  Lemma strong_extends_le_intro mm1 m1 m'1 m2 m'2:
    strong_extends mm1 m1 m'1 ->
    Mem.extends m2 m'2 ->
    Mem.unchanged_on (Events.loc_not_writable m1) m1 m2 ->
    Mem.unchanged_on (Events.loc_out_of_bounds m1) m'1 m'2 ->
    (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
    (forall b o p, Mem.valid_block m1 b -> Mem.perm m2 b o Max p -> Mem.perm m1 b o Max p) ->
    { mm2 | strong_extends mm2 m2 m'2 /\
            strong_extends_le mm1 mm2 }.
  Proof.
    intros H H0 H1 H2 H3 H4.
    exists (mk_strong_extends_carrier _ _ H0).
    split.
    { constructor; auto. }
    inversion H; subst.
    constructor; auto.
  Qed.

  Lemma strong_extends_le_elim mm1 m1 m'1 mm2 m2 m'2:
    strong_extends mm1 m1 m'1 ->
    strong_extends mm2 m2 m'2 ->
    strong_extends_le mm1 mm2 ->
    Mem.unchanged_on (Events.loc_not_writable m1) m1 m2 /\
    Mem.unchanged_on (Events.loc_out_of_bounds m1) m'1 m'2 /\
    (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b) /\
    (forall b o p, Mem.valid_block m1 b -> Mem.perm m2 b o Max p -> Mem.perm m1 b o Max p).
  Proof.
    inversion 1; subst.
    inversion 1; subst.
    inversion 1; subst.
    tauto.
  Qed.    

  Definition simrel_strong_extends_ops :=
    {|
      simrel_world := strong_extends_carrier;
      simrel_acc := {| Structures.le := strong_extends_le |};
      simrel_undef_matches_values_bool := true;
      simrel_undef_matches_block p b := True;
      simrel_meminj p := inject_id;
      simrel_new_glbl := nil;
      match_mem := strong_extends
    |}.

  Require Import ExtensionalityAxioms.

  (* We try to take advantage of the fact that simrel_meminj is
     the same as for lessdef, to share proofs. *)

  Lemma match_strong_extends_ptr p:
    match_ptr simrel_strong_extends_ops p = eq.
  Proof.
    rewrite <- (match_ptr_simrel_lessdef (D:=D) tt).
    eapply functional_extensionality; intros [b1 o1].
    eapply functional_extensionality; intros [b2 o2].
    eapply prop_ext.
    split; inversion 1; constructor; auto.
  Qed.

  Lemma match_strong_extends_ptrbits p:
    match_ptrbits simrel_strong_extends_ops p = eq.
  Proof.
    rewrite <- (match_ptrbits_simrel_lessdef (D:=D) tt).
    eapply functional_extensionality; intros [b1 o1].
    eapply functional_extensionality; intros [b2 o2].
    eapply prop_ext.
    split; inversion 1; constructor; auto.
  Qed.

  Lemma match_strong_extends_block p:
    match_block simrel_strong_extends_ops p = eq.
  Proof.
    rewrite <- (match_block_simrel_lessdef (D:=D) tt).
    apply eqrel_eq; split; repeat red; tauto.
  Qed.

  Lemma match_strong_extends_val p:
    match_val simrel_strong_extends_ops p = Val.lessdef.
  Proof.
    rewrite <- (match_val_simrel_lessdef (D:=D) tt).
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext; split; inversion 1; constructor; auto;
    (try rewrite (match_ptrbits_simrel_lessdef tt) in * |- *);
    (try rewrite (match_strong_extends_ptrbits p) in * |- *);
    auto.
    match goal with
        K: match_ptrbits simrel_lessdef_ops _ _ _ |- _ =>
        rewrite (match_ptrbits_simrel_lessdef tt) in K
    end.
    congruence.
  Qed.

  Lemma match_strong_extends_memval p:
    match_memval simrel_strong_extends_ops p = memval_lessdef.
  Proof.
    rewrite <- (match_memval_simrel_lessdef (D:=D) tt).
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext; split; inversion 1; constructor; auto;
    (try rewrite (match_ptrbits_simrel_lessdef tt) in * |- *);
    (try rewrite (match_strong_extends_ptrbits p) in * |- *);
    (try rewrite (match_strong_extends_val p) in * |- *);
    (try rewrite (match_val_simrel_lessdef tt) in * |- *);
    auto.
    rewrite (match_val_simrel_lessdef tt) in H0.
    assumption.
  Qed.

  Global Instance simrel_strong_extends_prf:
    SimulationRelation simrel_strong_extends_ops.
  Proof.
    assert (Heqsub: forall A B, subrel (@eqrel A B) (@subrel A B)).
    {
      intros A B x y H.
      repeat red in H.
      tauto.
    }
    constructor; try now repeat constructor.

    (** preorder *)
    - constructor; typeclasses eauto.

    (** [Genv.init_mem] *)
    - intros F V p1 p2 Hp.
      apply (simrel_init_mem (R := ext (D:=D))) in Hp.
      inversion Hp; clear Hp; subst; try now constructor.
      lazymatch goal with
        K: _ x y |- _ =>
        destruct K as [w Hm];
          rename x into m1;
          rename y into m2
      end.
      simpl in Hm.
      apply strong_extends_intro in Hm.
      destruct Hm as [ mm Hm ].
      constructor.
      exists mm.
      assumption.

    (** [Mem.alloc] *)
    - intros p m1 m1' Hm1 lo hi.
      destruct (Mem.alloc m1 _ _) eqn:Halloc1.
      edestruct (Mem.alloc_extends m1) as (? & Halloc2 & Hm2); eauto; try reflexivity.
      rewrite Halloc2.
      destruct (strong_extends_le_intro p _ _ _ _ Hm1 Hm2) as [p' Hp'].
      + eapply Mem.alloc_unchanged_on; eauto.
      + eapply Mem.alloc_unchanged_on; eauto.
      + eapply Mem.valid_block_alloc; eauto.
      + intros; eapply Mem.perm_alloc_4; eauto.
        intro ABSURD; subst.
        edestruct (Mem.fresh_block_alloc m1); eauto.
      + destruct Hp'.
        reexists; repeat rstep.
        reflexivity.

    (** [Mem.free] *)
    - intros p m1 m1' Hm1 [[b_ o_] ?] [[b o] ? ] Hb.
      inversion Hb as [? ? ? ? sz]; clear Hb; subst.
      match goal with
          K: match_ptr _ _ _ _ |- _ =>
          rewrite match_strong_extends_ptr in K;
            inversion K; clear K; subst
      end.
      simpl.
      destruct (Mem.free m1 _ _ _) eqn:Hfree1; try now solve_monotonic.
      edestruct (Mem.free_parallel_extends m1) as (? & Hfree2 & Hm2); eauto.
      rewrite Hfree2.
      destruct (strong_extends_le_intro p _ _ _ _ Hm1 Hm2) as [p' Hp'].
      + eapply Mem.free_unchanged_on; eauto.
        intros i H.
        unfold Events.loc_not_writable.
        intro ABSURD. apply ABSURD; clear ABSURD.
        apply Mem.perm_cur_max.
        eapply Mem.perm_implies ; [ eapply Mem.free_range_perm; eauto | ].
        constructor.
      + eapply Mem.free_unchanged_on; eauto.
        intros i H.
        unfold Events.loc_out_of_bounds.
        intro ABSURD. apply ABSURD; clear ABSURD.
        apply Mem.perm_cur_max.
        eapply Mem.perm_implies ; [ eapply Mem.free_range_perm; eauto | ].
        constructor.
      + eapply Mem.valid_block_free_1; eauto.
      + intros b0 o0 p0 H H0. eapply Mem.perm_free_3; eauto.
      + destruct Hp' . solve_monotonic.

    (** [Mem.load] *)
    - intro p.
      rewrite match_strong_extends_val.
      rewrite match_strong_extends_ptr.
      simpl.
      repeat red.
      intros a x y H x0 y0 H0.
      subst.
      destruct y0.
      simpl.
      destruct (Mem.load _ x _ _) eqn:Hload; try constructor.
      edestruct (Mem.load_extends a x) as (? & Hload2 & ?); eauto.
      rewrite Hload2.
      constructor; assumption.

    (** [Mem.store] *)
    - intro p.
      rewrite match_strong_extends_val.
      rewrite match_strong_extends_ptr.
      simpl.
      intros a x y H x0 y0 H0 x1 y1 H1.
      subst.
      destruct y0 as [b o].
      simpl.
      destruct (Mem.store a x b o x1) eqn:STORE1; try now solve_monotonic.
      edestruct (Mem.store_within_extends a x) as (? & Hstore2 & Hm2); eauto.
      rewrite Hstore2.
      destruct (strong_extends_le_intro p _ _ _ _ H Hm2) as [p' Hp'].
      + eapply Mem.store_unchanged_on; eauto.
        intros i H0.
        unfold Events.loc_not_writable.
        intro ABSURD. apply ABSURD; clear ABSURD.
        apply Mem.perm_cur_max.
        eapply Mem.store_valid_access_3; eauto.
      + eapply Mem.store_unchanged_on; eauto.
        intros i H0.
        unfold Events.loc_out_of_bounds.
        intro ABSURD. apply ABSURD; clear ABSURD.
        apply Mem.perm_cur_max.
        eapply Mem.perm_implies; [ eapply Mem.store_valid_access_3; eauto | ].
        constructor.
      + eapply Mem.store_valid_block_1; eauto.
      + intros b0 o0 p0 H0 H2; eapply Mem.perm_store_2; eauto.
      + destruct Hp' ; solve_monotonic.

    (** [Mem.loadbytes] *)
    - intro p.
      rewrite match_strong_extends_memval.
      rewrite match_strong_extends_ptr.
      intros x y H x0 y0 H0 a.
      subst.
      destruct y0.
      simpl.
      destruct (Mem.loadbytes x _ _ _) eqn:Hlb1; try constructor.
      edestruct (Mem.loadbytes_extends x) as (? & Hlb2 & ?); eauto.
      rewrite Hlb2.
      constructor.
      rewrite <- CompcertStructures.list_forall2_list_rel; assumption.

    (** [Mem.storebytes] *)
    - intro p.
      rewrite match_strong_extends_memval.
      rewrite match_strong_extends_ptr.
      intros x y H x0 y0 H0 x1 y1 H1.
      subst.
      destruct y0.
      simpl.
      destruct (Mem.storebytes x _ _ _) eqn:Hsb1; try now solve_monotonic.
      edestruct (Mem.storebytes_within_extends x) as (? & Hsb2 & Hm2); eauto.
      { rewrite CompcertStructures.list_forall2_list_rel; eassumption. }
      rewrite Hsb2.
      destruct (strong_extends_le_intro p _ _ _ _ H Hm2) as [p' Hp'].
      + eapply Mem.storebytes_unchanged_on; eauto.
        intros i H0. unfold Events.loc_not_writable.
        intro ABSURD. apply ABSURD. clear ABSURD.
        apply Mem.perm_cur_max.
        eapply Mem.storebytes_range_perm; eauto.
      + eapply Mem.storebytes_unchanged_on; eauto.
        assert (length y1 = length x1) as LEN by (symmetry; solve_monotonic).
        rewrite LEN.
        intros i H0. unfold Events.loc_out_of_bounds.
        intro ABSURD. apply ABSURD. clear ABSURD.
        apply Mem.perm_cur_max.
        clear Hsb2.
        eapply Mem.perm_implies; [ eapply Mem.storebytes_range_perm; eauto | ].
        constructor.
      + eapply Mem.storebytes_valid_block_1; eauto.
      + intros; eapply Mem.perm_storebytes_2; eauto.
      + destruct Hp' . solve_monotonic.

    (** [Mem.perm] *)
    - intros p.
      rewrite match_strong_extends_ptr.
      repeat red.
      intros x y H x0 y0 H0 a a0 H1.
      subst.
      destruct y0.
      simpl in *.
      eapply Mem.perm_extends; eauto.

    (** [Mem.valid_block] *)
    - intros p.
      rewrite match_strong_extends_block.
      simpl.
      intros m1 m2 Hm b1 b2 Hb; subst.
      eapply Mem.valid_block_extends; eauto.

    (** [Mem.different_pointers_inject] *)
    - inversion 5; subst.
      inversion 1; subst.
      tauto.

    (** [Mem.weak_valid_pointer_inject_val] *)
    - intros p m1 m2 b1 ofs1 b2 ofs2 H H0 H1.
      rewrite match_strong_extends_ptrbits in H1.
      inversion H1; clear H1; subst.
      eapply Mem.weak_valid_pointer_extends; eauto.

    (** [Mem.weak_valid_pointer_address_inject_weak] *)
    - intros p m1 m2 b1 b2 delta H H0.
      inversion H0; clear H0; subst.
      exists 0.
      intros ofs1 H0.
      rewrite Ptrofs.add_zero.
      omega.

    (** [Mem.address_inject *)
    - simpl.
      inversion 3; subst.
      rewrite Ptrofs.add_zero.
      omega.

    (** [Mem.aligned_area_inject] *)
    - simpl.
      inversion 7; subst.
      rewrite Z.add_0_r.
      assumption.

    (** [Mem.disjoint_or_equal_inject] *)
    - simpl.
      inversion 2; subst.
      inversion 1; subst.
      repeat rewrite Z.add_0_r.
      tauto.
  Qed.

  Definition simrel_strong_extends :=
    {|
      simrel_ops := simrel_strong_extends_ops
    |}.
End STRONG_LESSDEF_SIMREL.
