Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.common.AST. (* For ident. *)
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PseudoJoin.
Require Import liblayers.logic.OptionOrders.
Require Import liblayers.logic.PTrees.
Require Import liblayers.logic.PTreeModules.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.Primitives.
Require Import liblayers.logic.GlobalVars.


(** * Construction of layers *)

Definition ptree_layer {layerdata} primsem V (D: layerdata) :=
  (PTree.t (res (primsem D)) * PTree.t (res V))%type.

Section PTREE_LAYER_INSTANCES.
  Context {layerdata simrel} `{Hprim: Primitives layerdata simrel}.
  Context {V: Type}.
  Local Existing Instance ptree_mapsto.

  Definition ptree_layer_conflict i :=
    MSG "duplicate symbol in layer: " :: CTX i :: nil.

  (** ** Querying functions *)

  (** The functions [ptree_layer_primitive] and [ptree_layer_globvar]
    retreive the primitive semantics or global variable definition
    associated with an identifier in a given layer. Because we want
    them to be monotonic, we need to distinguish between two kinds of
    failures.

    Consider [ptree_layer_primitive]. If the layer does not associate
    a primitive semantics to identifier [i], which is to say it is
    undefined at [i], or it is defined a a variable definition, then
    [ptree_layer_primitive] return [OK None]. We can interpret this
    as a successful determination that there is no primitive semantics
    at [i]. On the other hand, is the layer maps [i] to [anything]
    (the special "overdefined" value), then all bets are off: a
    smaller layer may very well contain a primitive
    definition. Consequently, [ptree_layer_primitive] returns [Error]
    to indicate failure to make any determination at all.

    The same principle applies for [ptree_layer_globvar]. *)

  Definition ptree_layer_primitive {D} i (L: ptree_layer primsem V D) :=
    option_res_flip ((fst L) ! i).

  Definition ptree_layer_globalvar {D} i (L: ptree_layer primsem V D) :=
    option_res_flip ((snd L) ! i).

  Local Instance ptree_layer_sim_op:
    Sim simrel (ptree_layer primsem V) :=
    {
      simRR D1 D2 R :=
        (ptree_rel (option_le (res_le (sim R))) *
         ptree_rel (option_le (res_le eq)))%rel
    }.

  Local Existing Instance cat_sim_cat.

  Local Instance ptree_layer_rg_sim_prf:
    CategorySim layerdata simrel (ptree_layer primsem V).
  Proof.
    split; simpl; try typeclasses eauto.
    - rauto.
  Qed.

  Existing Instance ptree_emptyset.
  Existing Instance ptree_oplus.
  Existing Instance ptree_mapsto.

  Local Instance ptree_prim_oplus D: Oplus (option (res (primsem D))) :=
    {
      oplus p1 p2 :=
        match p1, p2 with
          | _, None => p1
          | None, _ => p2
          | Some (Error msg), _ => Some (Error msg)
          | _, Some (Error msg) => Some (Error msg)
          | Some (OK σ1), Some (OK σ2) => Some (OK (σ1 ⊕ σ2))
        end
    }.

  Context {gv_ops: GlobalVarsOps V}.

  Local Instance ptree_layer_ops:
    LayerOps ident primsem V (ptree_layer primsem V) :=
    {
      layer_empty D := {| emptyset := (PTree.empty _, PTree.empty _) |};
      layer_oplus D := {| oplus L1 L2 := (fst L1 ⊕ fst L2, snd L1 ⊕ snd L2) |};
      layer_mapsto_primitive D := {| mapsto i σ := (i ↦ OK σ, ∅) |};
      layer_mapsto_globalvar D := {| mapsto i τ := (∅, i ↦ OK τ) |};
      get_layer_primitive := @ptree_layer_primitive;
      get_layer_globalvar := @ptree_layer_globalvar;
      layers_disjoint D1 D2 L1 L2 :=
        ptree_disjoint (fst L1) (fst L2) /\
        ptree_disjoint (snd L1) (snd L2);
      layer_wf D L :=
        True
    }.
  Proof.
  * intros.
    unfold ptree_layer_primitive.
    refine (_
              (ptree_forall_decision_strong
                 (fun _ def => P (option_res_flip (Some def)))
                 (P (OK None))
                 _ _ (fst L))).
    apply decide_rewrite.
    split.
    + intros J i.
      generalize (J i).
      destruct ((fst L) ! i); simpl; monad_norm; auto.
    + intros J i.
      generalize (J i).
      destruct ((fst L) ! i); simpl; monad_norm; auto.
  * intros D P DP M.
    refine (_
              (ptree_forall_decision
                 (fun i _ => ptree_layer_primitive i M = OK None \/ P i) 
                 _ (fst M))).
    + apply decide_rewrite.
      unfold ptree_layer_primitive.
      unfold ptree_forall.
      split.
      - intros J i.
        destruct ((fst M) ! i) eqn:HM; try (compute; congruence).
        rewrite <- HM.
        intro.
        destruct (J _ _ HM); try contradiction.
        assumption.
      - intros.
        destruct (decide (option_res_flip (fst M) ! i = OK None)); auto.
  * intros.
    unfold ptree_layer_globalvar.
    refine (_
              (ptree_forall_decision_strong
                 (fun _ def => P (option_res_flip (Some def)))
                 (P (OK None))
                 _ _ (snd L))).
    apply decide_rewrite.
    split.
    + intros J i.
      generalize (J i).
      destruct ((snd L) ! i); simpl; monad_norm; auto.
    + intros J i.
      generalize (J i).
      destruct ((snd L) ! i); simpl; monad_norm; auto.
  * intros D P DP M.
    refine (_
              (ptree_forall_decision
                 (fun i _ => ptree_layer_globalvar i M = OK None \/ P i) 
                 _ (snd M))).
    + apply decide_rewrite.
      unfold ptree_layer_globalvar.
      unfold ptree_forall.
      split.
      - intros J i.
        destruct ((snd M) ! i) eqn:HM; try (compute; congruence).
        rewrite <- HM.
        intro.
        destruct (J _ _ HM); try contradiction.
        assumption.
      - intros.
        destruct (decide (option_res_flip (snd M) ! i = OK None)); auto.
  Defined.

  Arguments fmap : simpl never.

  Global Instance ptree_layer_primitive_monotonic:
    Monotonic
      (@ptree_layer_primitive)
      (forallr R, - ==> sim R ++> res_le (option_le (sim R))).
  Proof.
    unfold ptree_layer_primitive.
    intros D1 D2 R i L1 L2 HL.
    solve_monotonic.
  Qed.

  Global Instance ptree_layer_globalvar_monotonic:
    Monotonic
      (@ptree_layer_globalvar)
      (forallr R, - ==> sim R ++> res_le (option_le eq)).
  Proof.
    unfold ptree_layer_globalvar.
    intros D1 D2 R i L1 L2 HL.
    solve_monotonic.
  Qed.

  Local Opaque PTree.combine.

  (** Note: because we have to define our own instance of [Oplus] here
    to be used with ptrees, rather than use [prim_oplus], we don't
    benefit from the [SimJoin] proof in [Primitives]. *)

  Local Instance:
    SimJoin layerdata simrel (ptree_layer primsem V).
  Proof.
    split.
    - split; simpl.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        destruct ((fst x) ! i) as [[|]|]; repeat constructor;
        destruct ((fst y) ! i) as [[|]|]; repeat constructor.
        * eapply hlub_ub_l; eauto.
        * reflexivity.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        exact (oplus_le_left ((snd x) ! i) ((snd y) ! i)).
    - split; simpl.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        destruct ((fst x) ! i) as [[|]|]; repeat constructor;
        destruct ((fst y) ! i) as [[|]|]; repeat constructor.
        * eapply hlub_ub_r; eauto.
        * reflexivity.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        rewrite option_res_globalvar_oplus_comm.
        exact (oplus_le_left ((snd y) ! i) ((snd x) ! i)).
    - intros v' e t Hx Hy; simpl.
      split; simpl.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        destruct Hx as [Hx _]; specialize (Hx i).
        destruct Hy as [Hy _]; specialize (Hy i).
        revert Hx Hy.
        generalize ((fst x) ! i), ((fst y) ! i), ((fst t) ! i).
        clear x y t.
        intros x y t Hx Hy.
        destruct Hx as [t | _ _ [x t Hx | msg x]].
        * destruct y; assumption.
        * inversion Hy; clear Hy; subst; repeat constructor; eauto.
          inversion H1; clear H1; subst; repeat constructor; eauto.
          eapply hlub_intro; eauto.
        * destruct x; inversion Hy; repeat constructor.
          destruct x; repeat constructor.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        destruct Hx as [_ Hx]; specialize (Hx i).
        destruct Hy as [_ Hy]; specialize (Hy i).
        apply option_res_globalvar_lub; auto.
  Qed.

  Global Instance ptree_layer_lb D1 D2 R:
    LowerBound (A := ptree_layer primsem V D1) (simRR D1 D2 R) (∅, ∅).
  Proof.
    intros L2.
    constructor; apply lower_bound.
  Qed.

  Lemma option_fold {A} (o: option A):
    match o with
      | Some x => Some x
      | None => None
    end = o.
  Proof.
    destruct o; reflexivity.
  Qed.

  Local Instance ptree_layer_prf:
    Layers ident primsem V (ptree_layer primsem V).
  Proof.
    split.
    * typeclasses eauto.
    * typeclasses eauto.
    * typeclasses eauto.

    * intros.
      simpl.
      solve_monotonic.

    * intros D i.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gempty.
      reflexivity.
    * intros D i σ.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gss.
      reflexivity.
    * intros D i j σ Hij.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gso by assumption.
      rewrite PTree.gempty.
      reflexivity.
    * intros D i j τ.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gempty.
      reflexivity.
    * intros D i L1 L2.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gcombine by reflexivity.
      destruct ((fst L1) ! i) as [[σ1|]|];
      destruct ((fst L2) ! i) as [[σ2|]|];
      simpl;
      monad_norm;
      simpl;
      solve_monotonic.
    * typeclasses eauto.

    * intros D i.
      simpl.
      unfold ptree_layer_globalvar.
      rewrite PTree.gempty.
      reflexivity.
    * simpl.
      intros D i τ.
      unfold ptree_layer_globalvar; simpl.
      rewrite PTree.gss.
      reflexivity.
    * simpl.
      intros D i j τ Hij.
      unfold ptree_layer_globalvar; simpl.
      rewrite PTree.gso by assumption.
      rewrite PTree.gempty.
      reflexivity.
    * simpl.
      intros D i j τ.
      unfold ptree_layer_globalvar; simpl.
      rewrite PTree.gempty.
      reflexivity.
    * simpl.
      intros D i L1 L2.
      unfold ptree_layer_globalvar; simpl.
      rewrite PTree.gcombine by reflexivity.
      destruct ((snd L1) ! i) as [[τ1|]|];
      destruct ((snd L2) ! i) as [[τ2|]|];
      simpl;
      monad_norm;
      simpl;
      solve_monotonic.
    * typeclasses eauto.

    * intros D1 D2 L.
      split; intros i xi; simpl; rewrite PTree.gempty; discriminate.
    * intros D1 D2 L1 L2; simpl; destruct 1; eauto using ptree_disjoint_sym.
    * intros D1 D2 L1 L21 L22. simpl.
      destruct 1.
      destruct 1.
      auto using ptree_disjoint_combine.
    * intros D1 D2 i1 i2 σ1 σ2 H.
      simpl.
      unfold ptree_disjoint, ptree_forall.
      split; intros i a.
      + repeat rewrite PTree.gsspec.
        destruct (Coqlib.peq i i1); try (rewrite PTree.gempty; congruence).
        destruct (Coqlib.peq i i2); try (rewrite PTree.gempty; congruence).
        congruence.
      + rewrite PTree.gempty; congruence.
    * intros D1 D2 i1 i2 σ1 σ2 H.
      simpl.
      unfold ptree_disjoint, ptree_forall.
      split; intros i a.
      + intros _. apply PTree.gempty.
      + rewrite PTree.gempty. congruence.
    * intros D1 D2 i1 i2 σ1 σ2 H.
      simpl.
      unfold ptree_disjoint, ptree_forall.
      split; intros i a.
      + rewrite PTree.gempty; congruence.
      + repeat rewrite PTree.gsspec.
        destruct (Coqlib.peq i i1); try (rewrite PTree.gempty; congruence).
        destruct (Coqlib.peq i i2); try (rewrite PTree.gempty; congruence).
        congruence.

    * intros D D' R [Lp Lv] [L1p L1v] [L2p L2v] [HLL2p HLL2v] [Hp Hv].
      Local Opaque option_res_oplus_op.
      constructor; simpl in *.
      + intros i.
        specialize (Hp i).
        specialize (HLL2p i); simpl in *.
        destruct (Lp ! i) as [σ|]; repeat constructor.
        specialize (HLL2p σ eq_refl).
        rewrite PTree.gcombine in Hp by reflexivity.
        rewrite HLL2p in Hp.
        destruct (L1p ! i) as [[|]|];
        assumption.
      + intros i.
        specialize (Hv i).
        specialize (HLL2v i); simpl in *.
        destruct (Lv ! i) as [τ|]; repeat constructor.
        specialize (HLL2v τ eq_refl).
        rewrite PTree.gcombine in Hv by reflexivity.
        rewrite HLL2v in Hv.
        destruct (L1v ! i) as [[|]|];
        assumption.
    * intros i D L1 L2 [Ldisj _].
      simpl in *.
      specialize (Ldisj i).
      unfold ptree_layer_primitive.
      simpl in *.
      rewrite !PTree.gcombine by reflexivity.
      destruct ((fst L1) ! i).
      + specialize (Ldisj _ eq_refl).
        rewrite Ldisj.
        destruct r; eauto.
      + destruct ((fst L2) ! i); eauto.
    * intros i D L1 L2 [_ Ldisj].
      simpl in *.
      specialize (Ldisj i).
      unfold ptree_layer_globalvar.
      simpl in *.
      rewrite !PTree.gcombine by reflexivity.
      destruct ((snd L1) ! i).
      + specialize (Ldisj _ eq_refl).
        rewrite Ldisj.
        autorewrite with option_res_globalvar.
        auto.
      + autorewrite with option_res_globalvar.
        auto.

    * tauto.
  Qed.

  (** * Additional properties *)

  Lemma ptree_layer_pointwise_sim D1 D2 (R: simrel D1 D2) L1 L2:
    (forall i, res_le (option_le (sim R))
                      (get_layer_primitive i L1)
                      (get_layer_primitive i L2)) ->
    (forall i, res_le (option_le eq)
                      (get_layer_globalvar i L1)
                      (get_layer_globalvar i L2)) ->
    sim R L1 L2.
  Proof.
    intros Hp Hv.
    destruct L1 as [L1p L1v], L2 as [L2p L2v].
    simpl in *.
    unfold ptree_layer_primitive, ptree_layer_globalvar in *.
    constructor; simpl in *;
    intros i; apply option_res_le_flip; auto.
  Qed.

  Lemma ptree_layer_sim_pointwise D1 D2 R L1 L2:
    simRR D1 D2 R L1 L2 ->
    (forall i, res_le (option_le (sim R))
                      (get_layer_primitive i L1)
                      (get_layer_primitive i L2)) /\
    (forall i, res_le (option_le eq)
                      (get_layer_globalvar i L1)
                      (get_layer_globalvar i L2)).
  Proof.
    intros H.
    destruct H as [Hp Hv].
    split; intros i; apply option_res_le_flip; eauto.
  Qed.
End PTREE_LAYER_INSTANCES.

(** Now, we can forget how [ptree_layer] is defined, and only access
  it through the interfaces above. This is necessary, to avoid
  instances from [PTree.v] to sneak in when using [ptree_layer]s.
  But it makes sense anyway. *)
Global Opaque ptree_layer.
Global Opaque ptree_layer_ops.
