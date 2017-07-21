Require Import ExtensionalityAxioms.
Require Export SimrelDefinition.


(** * Equivalences *)

(** Because of the structure of [simrel_ops], functional and
  propositional extensionality are not enough to establish equality
  in all the cases we want. In particular, we need to be able to use
  non-trivial isomorphisms between the underlying carrier types when
  we show that two relations are equivalent. Univalence would
  probably work but let's not open that can of worms.

  Instead, we define our own equivalence relation. We will expect
  code that uses simulation relations, such as our definitions of
  simulation diagrams for primitive specifications, to be compatible
  with such equivalences. *)

Section EQUIV_DEF.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2: layerdata}.

  (** ** Definition *)

  (** To establish that two simulation relations kits are equivalent,
    we need provide an isomorphism between the two relations' carrier
    types, such that the different components of the relation are
    compatible with this mapping.

    Note that I make [simrel_equiv_maps] a record rather than a type
    class. This is because even with just the basic equivalences
    (identity, composition and inverse) we have more than enough to
    spin into an infinite search for a given pair of simulation
    relations. Because of this, in most contexts, designating the
    underlying equivalence explicitely is more appropriate. *)

  Record simrel_equiv_maps (R1 R2: simrel D1 D2) :=
    {
      simrel_equiv_fw (p: simrel_world R1): simrel_world R2;
      simrel_equiv_bw (q: simrel_world R2): simrel_world R1
    }.

  Global Arguments simrel_equiv_fw {R1 R2} _ p.
  Global Arguments simrel_equiv_bw {R1 R2} _ q.

  Class SimulationRelationEquivalence R1 R2 (f: simrel_equiv_maps R1 R2) :=
    {
      (* Monotonicity with respect to [le] *)
      simrel_equiv_le_fw:
        Monotonic (simrel_equiv_fw f) (le ++> le);
      simrel_equiv_le_bw:
        Monotonic (simrel_equiv_bw f) (le ++> le);
      (* undef_matches_values_bool are equal *)
      simrel_equiv_undef_matches_values_bool:
        simrel_undef_matches_values_bool R1 =
        simrel_undef_matches_values_bool R2;
      (* The new globals are the same *)
      simrel_equiv_new_glbl:
        simrel_new_glbl R1 = simrel_new_glbl R2;
      (* [simrel_undef_matches_block] are preserved under the isomorphism. *)
      simrel_equiv_undef_matches_block_fw p b:
        impl (simrel_undef_matches_block R1 p b) (simrel_undef_matches_block R2 (simrel_equiv_fw f p) b);
      simrel_equiv_undef_matches_block_bw p b:
        impl (simrel_undef_matches_block R2 p b) (simrel_undef_matches_block R1 (simrel_equiv_bw f p) b);
      (* [match_mem] are preserved under the isomorphism. *)
      match_mem_simrel_equiv_fw p:
        subrel (match_mem R1 p) (match_mem R2 (simrel_equiv_fw f p));
      match_mem_simrel_equiv_bw p:
        subrel (match_mem R2 p) (match_mem R1 (simrel_equiv_bw f p));
      (* [simrel_meminj] are preserved under the isomorphism. *)
      simrel_equiv_meminj_fw p b:
        option_le eq (simrel_meminj R1 p b) (simrel_meminj R2 (simrel_equiv_fw f p) b);
      simrel_equiv_meminj_bw p b:
        option_le eq (simrel_meminj R2 p b) (simrel_meminj R1 (simrel_equiv_bw f p) b);
      (* A round-trip in either direction makes the world grow. *)
      simrel_bw_fw_le w:
        w ≤ simrel_equiv_bw f (simrel_equiv_fw f w);
      simrel_fw_bw_le w:
        w ≤ simrel_equiv_fw f (simrel_equiv_bw f w);
    }.

  Global Existing Instance simrel_equiv_le_fw.
  Global Existing Instance simrel_equiv_le_bw.

  Global Instance: Params (@simrel_equiv_fw) 1.
  Global Instance: Params (@simrel_equiv_bw) 1.

  Context `{Hf: SimulationRelationEquivalence}.

  Lemma simrel_equiv_undef_matches_values:
    simrel_undef_matches_values R1 =
    simrel_undef_matches_values R2.
  Proof.
    unfold simrel_undef_matches_values.
    rewrite simrel_equiv_undef_matches_values_bool.
    reflexivity.
  Qed.

  Lemma match_ptr_simrel_equiv_fw p:
    subrel (match_ptr R1 p) (match_ptr R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1; constructor.
    generalize (simrel_equiv_meminj_fw p b1). rewrite H; inversion 1; subst; eauto.
  Qed.

  Lemma match_ptrbits_simrel_equiv_fw p:
    subrel (match_ptrbits R1 p) (match_ptrbits R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1; constructor.
    generalize (simrel_equiv_meminj_fw p b1). rewrite H; inversion 1; subst; eauto.
  Qed.

  Lemma match_ptrrange_simrel_equiv_fw p:
    subrel (match_ptrrange R1 p) (match_ptrrange R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1; constructor.
    eapply match_ptr_simrel_equiv_fw; eauto.
  Qed.

  Lemma match_block_simrel_equiv_fw p:
    subrel (match_block R1 p) (match_block R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1; econstructor.
    generalize (simrel_equiv_meminj_fw p x). rewrite H; inversion 1; subst; eauto.
  Qed.

  Lemma match_block_sameofs_simrel_equiv_fw p:
    subrel (match_block_sameofs R1 p) (match_block_sameofs R2 (simrel_equiv_fw f p)).
  Proof.
    unfold match_block_sameofs. simpl; intros b1 b2.
    intro H; generalize (simrel_equiv_meminj_fw p b1). rewrite H; inversion 1; subst; eauto.
  Qed.

  Lemma match_val_simrel_equiv_fw p:
    subrel (match_val R1 p) (match_val R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1;
    constructor;
    erewrite
        ?@simrel_equiv_undef_matches_values,
        ?@simrel_equiv_undef_matches_block_fw
      in *
      by typeclasses eauto;
    try assumption.
    eapply match_ptrbits_simrel_equiv_fw; eauto.
  Qed.

  Lemma match_memval_simrel_equiv_fw p:
    subrel (match_memval R1 p) (match_memval R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1;
    constructor;
    erewrite
      ?@simrel_equiv_undef_matches_values
      in *
      by typeclasses eauto;
    try eapply match_val_simrel_equiv_fw; eauto;
    assumption.
  Qed.

  Lemma match_ptr_simrel_equiv_bw q:
    subrel (match_ptr R2 q) (match_ptr R1 (simrel_equiv_bw f q)).
  Proof.
    destruct 1.
    generalize (simrel_equiv_meminj_bw q b1); rewrite H. inversion 1; subst; econstructor; auto.
  Qed.

  Lemma match_ptrbits_simrel_equiv_bw q:
    subrel (match_ptrbits R2 q) (match_ptrbits R1 (simrel_equiv_bw f q)).
  Proof.
    destruct 1.
    generalize (simrel_equiv_meminj_bw q b1); rewrite H. inversion 1; subst; econstructor; auto.
  Qed.

  Lemma match_ptrrange_simrel_equiv_bw q:
    subrel (match_ptrrange R2 q) (match_ptrrange R1 (simrel_equiv_bw f q)).
  Proof.
    destruct 1.
    eapply match_ptr_simrel_equiv_bw in H. constructor; auto.
  Qed.

  Lemma match_val_simrel_equiv_bw q:
    subrel (match_val R2 q) (match_val R1 (simrel_equiv_bw f q)).
  Proof.
    destruct 1;
      constructor;
      erewrite
        ?@simrel_equiv_undef_matches_values,
      ?@simrel_equiv_undef_matches_block_bw
        in *
        by typeclasses eauto;
      try eapply match_ptrbits_simrel_equiv_bw; eauto;
      try assumption.
  Qed.

  Lemma match_memval_simrel_equiv_bw q:
    subrel (match_memval R2 q) (match_memval R1 (simrel_equiv_bw f q)).
  Proof.
    destruct 1;
      constructor;
      erewrite
        ?@simrel_equiv_undef_matches_values
        in *
        by typeclasses eauto;
      try eapply match_val_simrel_equiv_bw; eauto;
      assumption.
  Qed.

  Lemma match_block_simrel_equiv_bw q:
    subrel (match_block R2 q) (match_block R1 (simrel_equiv_bw f q)).
  Proof.
    destruct 1; econstructor.
    generalize (simrel_equiv_meminj_bw q x); rewrite H. inversion 1; subst; econstructor; auto.
  Qed.

  Lemma match_block_sameofs_simrel_equiv_bw q:
    subrel (match_block_sameofs R2 q) (match_block_sameofs R1 (simrel_equiv_bw f q)).
  Proof.
    unfold match_block_sameofs; intros ? ? ?;
    generalize (simrel_equiv_meminj_bw q x); rewrite H. inversion 1; subst; econstructor; auto.
  Qed.    
End EQUIV_DEF.

Global Instance: Params (@simrel_equiv_fw) 1.
Global Instance: Params (@simrel_equiv_bw) 1.

(** ** Rewriting tactic *)

(** The properties above are perfect to be used as a set of
  rewriting rules. I expect proofs of compatibility with simulation
  relation blueprint equivalence will need little more than an
  invocation of the rewriting tactic, and the occasional [exists
  (simrel_maps_bw f q')].

  The one less well-behaved property is [simrel_equiv_undef_lb].
  Because it does not involve an element of the carrier, the
  equivalence is not involved in the equation. As a result we cannot
  find it by unification. Because of this, we need to explicitely
  figure out which equivalences are available. *)

Ltac simrel_equiv_rewrite_using f :=
  erewrite
      (* ?(simrel_equiv_undef_matches_block_fw (f:=f)), *)
      (* ?(simrel_equiv_meminj_fw (f:=f)), *)
      (* ?(match_mem_simrel_equiv_fw (f:=f)), *)
      (* ?(match_ptr_simrel_equiv_fw (f:=f)), *)
      (* ?(match_ptrbits_simrel_equiv_fw (f:=f)), *)
      (* ?(match_ptrrange_simrel_equiv_fw (f:=f)), *)
      (* ?(match_block_simrel_equiv_fw (f:=f)), *)
      (* ?(match_block_sameofs_simrel_equiv_fw (f:=f)), *)
      (* ?(match_val_simrel_equiv_fw (f:=f)), *)
      (* ?(match_memval_simrel_equiv_fw (f:=f)), *)
      (* ?(simrel_equiv_undef_matches_block_bw (f:=f)), *)
      (* ?(simrel_equiv_meminj_bw (f:=f)), *)
      (* ?(match_mem_simrel_equiv_bw (f:=f)), *)
      (* ?(match_ptr_simrel_equiv_bw (f:=f)), *)
      (* ?(match_ptrbits_simrel_equiv_bw (f:=f)), *)
      (* ?(match_ptrrange_simrel_equiv_bw (f:=f)), *)
      (* ?(match_block_simrel_equiv_bw (f:=f)), *)
      (* ?(match_block_sameofs_simrel_equiv_bw (f:=f)), *)
      (* ?(match_val_simrel_equiv_bw (f:=f)), *)
      (* ?(match_memval_simrel_equiv_bw (f:=f)), *)
      ?(simrel_equiv_new_glbl (f := f)),
      ?(simrel_equiv_undef_matches_values_bool (f:=f)),
      ?(simrel_equiv_undef_matches_values (f:=f))
    in *.

Ltac simrel_equiv_rewrite :=
  repeat
    match goal with
      | H: SimulationRelationEquivalence _ _ ?f |- _ =>
        progress simrel_equiv_rewrite_using f
    end.

(** ** Basic equivalences *)

Section EQUIVALENCES.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2: layerdata}.

  (** *** Identity *)

  Definition simrel_equiv_id_maps (R: simrel D1 D2):
    simrel_equiv_maps R R :=
    {|
      simrel_equiv_fw p := p;
      simrel_equiv_bw q := q
    |}.

  Lemma simrel_equiv_id_prf (R: simrel D1 D2):
    SimulationRelationEquivalence R R (simrel_equiv_id_maps R).
  Proof.
    split; simpl; intros; try reflexivity; solve_monotonic.
  Qed.

  (** *** Composition *)

  Definition simrel_equiv_compose_maps (R1 R2 R3: simrel D1 D2):
    simrel_equiv_maps R1 R2 ->
    simrel_equiv_maps R2 R3 ->
    simrel_equiv_maps R1 R3 :=
    fun f g =>
      {|
        simrel_equiv_fw p := simrel_equiv_fw g (simrel_equiv_fw f p);
        simrel_equiv_bw q := simrel_equiv_bw f (simrel_equiv_bw g q)
      |}.

  Lemma simrel_equiv_compose_prf R1 R2 R3 f g:
    SimulationRelationEquivalence R1 R2 f ->
    SimulationRelationEquivalence R2 R3 g ->
    SimulationRelationEquivalence R1 R3 (simrel_equiv_compose_maps R1 R2 R3 f g).
  Proof.
    split; intros; simpl; simrel_equiv_rewrite; try reflexivity; solve_monotonic.
    - red; intros. repeat apply simrel_equiv_undef_matches_block_fw; auto.
    - red; intros. repeat apply simrel_equiv_undef_matches_block_bw; auto.
    - red; intros. apply match_mem_simrel_equiv_fw. apply match_mem_simrel_equiv_fw. auto.
    - red; intros. apply match_mem_simrel_equiv_bw. apply match_mem_simrel_equiv_bw. auto.
    - generalize (simrel_equiv_meminj_fw p b).
      generalize (simrel_equiv_meminj_fw (simrel_equiv_fw f p) b).
      inversion 1; inversion 1; constructor. congruence.
    - generalize (simrel_equiv_meminj_bw p b).
      generalize (simrel_equiv_meminj_bw (simrel_equiv_bw g p) b).
      inversion 1; inversion 1; constructor. congruence.
    - etransitivity. apply simrel_bw_fw_le. monotonicity. apply simrel_bw_fw_le.
    - etransitivity. apply simrel_fw_bw_le. monotonicity. apply simrel_fw_bw_le.
  Qed.

  (** *** Inverse *)

  Definition simrel_equiv_inverse_maps (R1 R2: simrel D1 D2) f :=
    {|
      simrel_equiv_fw := simrel_equiv_bw (R1:=R1) (R2:=R2) f;
      simrel_equiv_bw := simrel_equiv_fw (R1:=R1) (R2:=R2) f
    |}.

  Lemma simrel_equiv_inverse_prf R1 R2 f:
    SimulationRelationEquivalence R1 R2 f ->
    SimulationRelationEquivalence R2 R1 (simrel_equiv_inverse_maps R1 R2 f).
  Proof.
    split; intros; simpl; simrel_equiv_rewrite; try reflexivity;
      eauto with typeclass_instances.
    - apply simrel_equiv_undef_matches_block_bw.
    - apply simrel_equiv_undef_matches_block_fw.
    - apply match_mem_simrel_equiv_bw.
    - apply match_mem_simrel_equiv_fw.
    - apply simrel_equiv_meminj_bw.
    - apply simrel_equiv_meminj_fw.
    - apply simrel_fw_bw_le.
    - apply simrel_bw_fw_le. 
  Qed.

  (** ** The [simrel_equiv] relation *)

  (** The packaged version of equivalences consists in the following
    relation. *)

  Definition simrel_equiv (R1 R2: simrel D1 D2) :=
    exists (f: simrel_equiv_maps R1 R2), SimulationRelationEquivalence R1 R2 f.

  (** The fact that [simrel_equiv] is an equivalence relation can be
    established using the identity, inverse, and composite equivalences. *)

  Global Instance simrel_equiv_prf:
    Equivalence simrel_equiv.
  Proof.
    split.
    - intros R.
      exists (simrel_equiv_id_maps R).
      apply simrel_equiv_id_prf.
    - intros R1 R2 [f Hf].
      exists (simrel_equiv_inverse_maps _ _ f).
      apply simrel_equiv_inverse_prf; typeclasses eauto.
    - intros R1 R2 R3 [f Hf] [g Hg].
      exists (simrel_equiv_compose_maps _ _ _ f g).
      apply simrel_equiv_compose_prf; typeclasses eauto.
  Qed.
End EQUIVALENCES.
