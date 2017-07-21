Require Export SimrelCategory.


(** * Simrel functors *)

Section SIMREL_FUNCTOR.
  Context `{Hmem: BaseMemoryModel}.

  (** ** Relations without worlds *)

  (** By "[simrel] functor", we mean [sim D1 D2 R] relations indexed
    by [simrel]s, usually between types [T D] indexed by [layerdata],
    so that [T] and [sim] are the object and morphism components of a
    functor from the category of [layerdata] and [simrel]s into the
    category of [Type]s and [rel]ations. *)

  (** *** Definition *)

  Definition simrel_rel (T: layerdata -> Type) :=
    forall D1 D2 (R: simrel D1 D2), rel (T D1) (T D2).

  Class SimrelFunctor {T} (RR: simrel_rel T) :=
    {
      simrel_functor_equiv :>
        Monotonic RR (forallr -, forallr -, simrel_equiv ==> subrel);
      simrel_functor_id D:
        RR D D simrel_id = eq;
      simrel_functor_compose D1 D2 D3 R12 R23:
        RR D1 D3 (simrel_compose R12 R23) =
        rel_compose (RR D1 D2 R12) (RR D2 D3 R23);
    }.

  (** NB: Note that in order for [simrel_functor_equiv] to be used for
    [monotonicity] queries, the user needs to define an instance of
    [Params _ 5] for their relation. *)

  (** *** Properties *)

  Section SIMREL_FUNCTOR_PROPERTIES.
    Context `{HRR: SimrelFunctor}.

    Global Instance simrel_functor_id_refl D:
      Reflexive (RR D D simrel_id).
    Proof.
      rewrite simrel_functor_id.
      typeclasses eauto.
    Qed.

    Global Instance simrel_functor_id_corefl D:
      Coreflexive (RR D D simrel_id).
    Proof.
      rewrite simrel_functor_id.
      typeclasses eauto.
    Qed.

    Global Instance simrel_functor_compose_htrans D1 D2 D3 R12 R23:
      HTransitive
        (RR D1 D2 R12)
        (RR D2 D3 R23)
        (RR D1 D3 (simrel_compose R12 R23)).
    Proof.
      rewrite simrel_functor_compose.
      typeclasses eauto.
    Qed.

    Global Instance simrel_functor_compose_rtrans D1 D2 D3 R12 R23:
      RTransitive
        (RR D1 D2 R12)
        (RR D2 D3 R23)
        (RR D1 D3 (simrel_compose R12 R23)).
    Proof.
      rewrite simrel_functor_compose.
      typeclasses eauto.
    Qed.
  End SIMREL_FUNCTOR_PROPERTIES.

  (** ** Relations indexed by [simrel_world]s *)

  (** A slightly more complicated version of this involves relations
    [match D1 D2 R w] which are also indexed by a [w : simrel_world R].
    In this case the target category is technically the category of
    [Type]s and world-indexed [rel]s.

    Note that unfortunately, because the basic [match_val], [match_mem]
    and so on are defined in terms of [simrel_components] rather than
    [simrel], they cannot be declared as [SimrelFunctorW]. *)

  (** *** Definition *)

  Definition simrel_wrel (T: layerdata -> Type) :=
    forall D1 D2 (R: simrel D1 D2), simrel_world R -> rel (T D1) (T D2).

  Definition simrel_world_equiv {D1 D2} {R1 R2: simrel D1 D2} f: rel _ _ :=
    fun w1 w2 => simrel_equiv_fw (R1:=R1) (R2:=R2) f w1 = w2.

  Class SimrelFunctorW {T} (RR: simrel_wrel T) :=
    {
      simrel_functor_wequiv D1 D2 (RA RB: simrel D1 D2) f:
        SimulationRelationEquivalence RA RB f ->
        Related (RR D1 D2 RA) (RR D1 D2 RB) (simrel_world_equiv f ++> subrel);
      simrel_functor_wid_def D:
        RR D D simrel_id tt = eq;
      simrel_functor_wcompose_def D1 D2 D3 R12 R23 w12 w23:
        RR D1 D3 (simrel_compose R12 R23) (w12, w23) =
        rel_compose (RR D1 D2 R12 w12) (RR D2 D3 R23 w23);
    }.

  (** Note that except for [match_mem], most are covariant in the
    world index: a larger world yields a larger relation. So in
    addition to [SimrelFunctorW] you may want to define an instance
    [match_foo_acc: Monotonic (RR D1 D2 R) ((≤) ++> subrel)]. *)

  (** *** Properties *)

  Section SIMREL_FUNCTORW_PROPERTIES.
    Context `{HRR: SimrelFunctorW}.

    (** These more broadly applicable versions of the functor
      equations use a variable for the world on the left-hand side. *)

    Lemma simrel_functor_wid D w:
      RR D D simrel_id w = eq.
    Proof.
      destruct w.
      apply simrel_functor_wid_def.
    Qed.

    Lemma simrel_functor_wcompose D1 D2 D3 R12 R23 w:
      RR D1 D3 (simrel_compose R12 R23) w =
      rel_compose (RR D1 D2 R12 (fst w)) (RR D2 D3 R23 (snd w)).
    Proof.
      destruct w.
      apply simrel_functor_wcompose_def.
    Qed.

    (** Relation property instances. *)

    Global Instance simrel_functor_wid_refl D w:
      Reflexive (RR D D simrel_id w).
    Proof.
      rewrite simrel_functor_wid.
      typeclasses eauto.
    Qed.

    Global Instance simrel_functor_wid_corefl D w:
      Coreflexive (RR D D simrel_id w).
    Proof.
      rewrite simrel_functor_wid.
      typeclasses eauto.
    Qed.

    Global Instance simrel_functor_wcompose_htrans D1 D2 D3 R12 R23 w:
      HTransitive
        (RR D1 D2 R12 (fst w))
        (RR D2 D3 R23 (snd w))
        (RR D1 D3 (simrel_compose R12 R23) w).
    Proof.
      rewrite simrel_functor_wcompose.
      typeclasses eauto.
    Qed.

    Global Instance simrel_functor_wcompose_rtrans D1 D2 D3 R12 R23 w:
      RTransitive
        (RR D1 D2 R12 (fst w))
        (RR D2 D3 R23 (snd w))
        (RR D1 D3 (simrel_compose R12 R23) w).
    Proof.
      rewrite simrel_functor_wcompose.
      typeclasses eauto.
    Qed.
  End SIMREL_FUNCTORW_PROPERTIES.
End SIMREL_FUNCTOR.
