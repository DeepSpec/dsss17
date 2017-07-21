Require Import ExtensionalityAxioms.
Require Import Functor.
Require Import Monad.

(** * [- -> Prop] is a [Functor] *)

(** [fmap f pA] is the image of the "set" [pA : A -> Prop] by the
  function [f]. *)

Inductive powerset_fmap {A B} (f: A -> B) (pA: A -> Prop): B -> Prop :=
  | powerset_fmap_intro a: pA a -> powerset_fmap f pA (f a).

Arguments powerset_fmap_intro {A B f pA} a _.

Instance powerset_functor_ops: FunctorOps (fun X => X -> Prop) := {
  fmap A B := powerset_fmap
}.

Instance powerset_functor: Functor (fun X => X -> Prop).
Proof.
  split.
  * intros A pA.
    apply functional_extensionality; intro x.
    apply prop_ext; split; simpl.
    - intro H; inversion H; subst.
      assumption.
    - intro H.
      fold (id x).
      constructor.
      assumption.
  * intros A B C f g pA.
    simpl.
    apply functional_extensionality; intro c.
    apply prop_ext; split.
    - intro H; inversion H; subst.
      constructor.
      constructor.
      assumption.
    - intro H.
      inversion H; subst.
      inversion H0; subst.
      change (f (g a0)) with ((fun y => f (g y)) a0).
      apply powerset_fmap_intro.
      assumption.
Qed.

(** * [- -> Prop] is also a monad *)

(** The operation [ret a] constructs the singleton {[a]} and is simply
  the predicate [eq a]. On the other hand, [bind R pA] is the image of
  the set [pA] by the relation [R: A -> B -> Prop]. *)

Inductive pred_bind {A B} (R: A -> B -> Prop) (pA: A -> Prop) (b: B): Prop :=
  | pred_bind_intro a: pA a -> R a b -> pred_bind R pA b.

Arguments pred_bind_intro {A B R pA b} a _ _.

Instance pred_monad_ops: MonadOps (fun X => X -> Prop) := {
  ret A := eq;
  bind A B := pred_bind
}.

Instance pred_monad: Monad (fun X => X -> Prop).
Proof.
  split; unfold bind, ret; simpl; intros.
  * typeclasses eauto.
  * apply functional_extensionality; intro pA.
    apply functional_extensionality; intro b.
    apply prop_ext; split; intro H.
    - destruct H as [x Hx].
      apply (pred_bind_intro x).
      + assumption.
      + reflexivity.
    - destruct H as [x Hx Hxy]; subst.
      apply (powerset_fmap_intro x).
      assumption.
  * apply functional_extensionality; intro y.
    apply prop_ext; split; intro H.
    - inversion H; congruence.
    - apply (pred_bind_intro x); now auto.
  * apply functional_extensionality; intro x.
    apply prop_ext; split; intro H.
    - inversion H; congruence.
    - apply (pred_bind_intro x); now auto.
  * apply functional_extensionality; intro z.
    apply prop_ext; split; intro H.
    - destruct H as [y [x Hx Hxy] Hyz].
      apply (pred_bind_intro x).
      + assumption.
      + apply (pred_bind_intro y); now auto.
    - destruct H as [x Hx [y Hxy Hyz]].
      apply (pred_bind_intro y).
      + apply (pred_bind_intro x); now auto.
      + assumption.
Qed.

Global Instance powerset_inv_ret:
  MonadInvRet (fun X => X -> Prop).
Proof.
  intros A x y H.
  unfold bind, ret in *; simpl in *.
  rewrite H.
  reflexivity.
Qed.

Global Instance powerset_inv_bind_weak:
  MonadInvBindWeak (fun X => X -> Prop).
Proof.
  intros A B f ma b H.
  unfold bind, ret in *; simpl in *.
  pose proof (eq_refl b) as Hab.
  rewrite <- H in Hab.
  inversion Hab.
  exists a.
  apply functional_extensionality; intros b'.
  apply prop_ext; split; intro Hb'.
  * rewrite <- H.
    econstructor; eassumption.
  * congruence.
Qed.
