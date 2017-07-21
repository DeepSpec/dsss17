Require Import liblayers.logic.Structures.


(** * Categories of abstract data and simulation relations *)

Class CategoryOps (V: Type) (E: V -> V -> Type): Type :=
  {
    cat_equiv v1 v2 :> Equiv (E v1 v2);
    cat_id v :> Id (E v v);
    cat_compose v1 v2 v3 :> Compose (E v1 v2) (E v2 v3) (E v1 v3)
  }.

(** TODO: generalize [LeftIdentity], [RightIdentity], and [Associative]
  so that we can use them here. *)
Class Category V E `{VEops: CategoryOps V E}: Prop :=
  {
    cat_equiv_prf {v1 v2: V} :>
      @Equivalence (E v1 v2) (≡);
    cat_compose_prf {v1 v2 v3: V} :>
      Monotonic (compose (A := E v1 v2) (B := E v2 v3)) ((≡) ==> (≡) ==> (≡));
    cat_compose_id_left {v1 v2: V}:
      forall (e: E v1 v2),
        id ∘ e ≡ e;
    cat_compose_id_right {v1 v2: V}:
      forall (e: E v1 v2),
        e ∘ id ≡ e;
    cat_compose_assoc {v1 v2 v3 v4: V}:
      forall (e12: E v1 v2) (e23: E v2 v3) (e34: E v3 v4),
        e34 ∘ (e23 ∘ e12) ≡ (e34 ∘ e23) ∘ e12
  }.

Global Instance cat_compose_params:
  Params (@compose) 2.


(** * Associated concrete simulation relations *)

(** We map the objects and arrows onto types and relations in some
  kind of structure-preserving ways. *)

Class CategorySim V E T `{cat_ops: CategoryOps V E} `{cat_sim: Sim V E T} :=
  {
    cat_sim_cat: Category V E;
    cat_sim_proper :> Monotonic simRR (forallr -, forallr -, (≡) ==> subrel);
    cat_sim_refl v :> @Reflexive (T v) (sim id);
    cat_sim_trans v1 v2 v3 (e12: E v1 v2) (e23: E v2 v3) :>
      HTransitive (sim e12) (sim e23) (sim (e23 ∘ e12))
  }.

Global Instance cat_sim_proper_params:
  Params (@simRR) 5.

Local Existing Instance cat_sim_cat.

(** We can specialize [cat_sim_trans] to account for situations where
  either [e12] or [e23] are [id], in which case the goal does not need
  to be of the form [sim (_ ∘ _)]. *)

Global Instance cat_sim_trans_le_left `{CategorySim}:
  forall v1 v2 (e12: E v1 v2),
    HTransitive (sim e12) (sim id) (sim e12) | 2.
Proof.
  intros v1 v2 e12.
  intros a b c Hab Hbc.
  rewrite <- cat_compose_id_left.
  ehtransitivity; eassumption.
Qed.

Global Instance cat_sim_trans_le_right `{CategorySim}:
  forall v1 v2 (e12: E v1 v2),
    HTransitive (sim id) (sim e12) (sim e12) | 2.
Proof.
  intros v1 v2 e12.
  intros a b c Hab Hbc.
  rewrite <- cat_compose_id_right.
  ehtransitivity; eassumption.
Qed.

Global Instance cat_sim_preorder `{CategorySim}:
  forall v, @PreOrder (T v) (sim id).
Proof.
  intros v.
  split.
  * apply cat_sim_refl.
  * intros x y z Hxy Hyz.
    htransitivity y;
    eassumption.
Qed.

(** We write [sim id] as [(≤)]. *)
Global Instance cat_sim_le_op `{CategoryOps} T `{Sim V E T} v: Le (T v) :=
  {
    le := sim id
  }.

(** [sim e] is compatible with [sim id]. *)
Global Instance cat_sim_monotonic `(CategorySim):
  forall v1 v2 e, Proper (sim id --> sim id ++> impl) (simRR v1 v2 e).
Proof.
  intros v1 v2 e x1 x2 Hx y1 y2 Hy Hxy.
  htransitivity x1; eauto.
  htransitivity y1; eauto.
Qed.

(** [sim e] is compatible with [≡]. *)
Global Instance cat_sim_equiv_compat `(CategorySim):
  forall v1 v2 e, Proper ((≡) ==> (≡) ==> impl) (simRR v1 v2 e).
Proof.
  intros v1 v2 e x1 x2 [Hx12 Hx21] y1 y2 [Hy12 Hy21] Hxy.
  htransitivity x1; eauto.
  htransitivity y1; eauto.
Qed.
