Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Classes.Morphisms.

Require Import ExtensionalityAxioms.
Require Import Lens.
Require Import Functor.
Require Import PowersetMonad.


(** * Lifting operations *)

(** Because [Mem.MemoryModel] contains so many theorems, we need some
  systematic way to lift the memory operations along a lens, so that
  the lifting of the theorems is convenient to automate.

  The signature of most of the memory operations are variations on
  the theme [mem -> F mem], where [F] is a functor such as [option]
  or [- × Z]. Using the functor's [fmap] and the lens operations,
  we can define a generic lifting operator as in the following. *)

Class Lift {S V} π `{πops: LensOps S V π} A B := { lift: A -> B }.

Arguments lift {S V} π {πops A B Lift} _.

Section LIFT.
  Context {S V} `{HSV: Lens S V} `{HF: Functor}.

  Global Instance lens_lift: Lift π (V -> F V) (S -> F S) := {
    lift f s := fmap (fun v => set π v s) (f (π s))
  }.
End LIFT.

(** Typeclass resolution needs some help to figure out those functors
  by unification. *)

Section LIFTINSTANCES.
  Context {S V} `{HSV: Lens S V}.

  Global Instance lift_const A: Lift π (V -> A) (S -> A) :=
    lens_lift (F := (fun _ => A)).
  Global Instance lift_prod A: Lift π (V -> V * A) (S -> S * A) :=
    lens_lift.
  Global Instance lift_powerset: Lift π (V -> V -> Prop) (S -> S -> Prop) :=
    lens_lift (F := (fun X => X -> Prop)).
End LIFTINSTANCES.


(** ** The [lift_peel] tactic *)

(** This is the main tactic we use: it lifts a theorem [Hf] of
  the underlying memory model by "peeling off" its structure
  recursively to prove the lifted goal. The leaf goals are
  handled with the caller-provided tactic [leaftac]. *)

(* Premises are "translated" and used to specialize Hf *)
Ltac lift_peel_intro π recurse Hf x :=
  intro x;
  (specialize (Hf x) ||
   specialize (Hf (π x)) ||
   (match type of Hf with
      forall (H: ?T), _ =>
        let H' := fresh H in
        assert (H': T) by recurse x;
        specialize (Hf H');
        clear H'
    end));
  recurse Hf.

(* Existential: we must use [set] to augment any memory state
  provided by Hf, but we can otherwise just pass everything along *)
Ltac lift_peel_exists π recurse Hf x :=
  let Hf' := fresh Hf in
  destruct Hf as [x Hf'];
  (exists x || eexists (set _ x _));
  recurse Hf'.

(* Conjunction: split and peel each side independently *)
Ltac lift_peel_conj π recurse Hf :=
  let Hl := fresh Hf "l" in
  let Hr := fresh Hf "r" in
  destruct Hf as [Hl Hr];
  split; [recurse Hl | recurse Hr].

Ltac lift_peel π Hf leaftac :=
  let recurse Hf := lift_peel π Hf leaftac in
  try match goal with
    | |- forall (x: _), _ =>
      let x := fresh x in
      lift_peel_intro π recurse Hf x
    | |- exists (x: _), _ =>
      let x := fresh x in
        lift_peel_exists π recurse Hf x
    | |- { x: _ | _ } =>
      let x := fresh x in
        lift_peel_exists π recurse Hf x
    | |- _ /\ _ =>
      lift_peel_conj π recurse Hf
    | |- ?T =>
      leaftac
  end.

(** Now the goal is to come up with an appropriate leaf tactic which
  will be able to prove some theorems instanciated with the lifted
  operations using the original version. *)


(** ** Expressing everything in terms of [lift] *)

(** As a first step, in order to be able to apply general theorems
  about it, we will want to make sure the goal and premises are all
  stated in terms of [lift]. In order to do this, we use the rule
  below to make sure that the [simpl] tactic stops whenever [lift] is
  reached. Then [simpl] allows us to unfold typeclass methods which
  are defined in terms of lift (the most common case). *)

Arguments lift _ _ _ _ _ _ _ _ : simpl never.

(** There are also derived operations (such as [free_list] for
  instance), which are defined in terms of the typeclass methods.
  In such cases, we usually want to prove that lifting such operations
  is equivalent to applying them to a lifted typeclass instance.
  Then we can rewrite them in terms of [lift] as well. Such proofs are
  collected into the "lift" rewrite database. *)

Ltac lift_norm :=
  repeat progress (simpl in *; autorewrite with lift in *).

(** Unfortunately there is no [Create HintDb] command for rewrite
  databases, so we have to create it by adding a fake entry. *)
Hint Rewrite injective_projections using fail : lift.


(** ** Simplifying occurences of [lift] *)

(** Once everything is stated in terms of lift, futher rewriting rules
  from the [lift_simpl] database can be applied. In particular, the
  theorems below try to ensure that the goal and hypotheses are stated
  in terms of [get] and [same_context] rather than in terms of [lift]. *)

Ltac lift_simpl :=
  repeat progress (lift_norm; autorewrite with lift_simpl in *; lens_simpl).

Section LIFTOPTION.
  Context {S V} `{HSV: Lens S V}.

  Lemma lift_option_eq_unlift (f: V -> option V) (s s': S):
    lift π f s = Some s' ->
    f (π s) = Some (π s').
  Proof.
    unfold lift; simpl.
    intros.
    destruct (f (π s)); try discriminate.
    inversion H.
    autorewrite with lens.
    reflexivity.
  Qed.

  Theorem lift_option_eq_same_context (f: V -> option V) (s s': S):
    lift π f s = Some s' ->
    same_context π s s'.
  Proof.
    unfold lift; simpl.
    case (f (π s)).
    * intros ? H; inversion H; subst.
      symmetry.
      apply lens_set_same_context.
    * discriminate.
  Qed.

  Theorem lift_option_eq_intro (f: V -> option V) (s s': S):
      same_context π s s' ->
      f (π s) = Some (π s') ->
      lift π f s = Some s'.
  Proof.
    intros Hc Hv.
    unfold lift; simpl.
    rewrite Hv; clear Hv.
    f_equal.
    rewrite Hc.
    apply lens_set_get.
  Qed.

  Theorem lift_option_eq_iff f s s' `{!Lens π}:
    lift π f s = Some s' <->
    f (π s) = Some (π s') /\ same_context π s s'.
  Proof.
    repeat split.
    - apply lift_option_eq_unlift.
      assumption.
    - eapply lift_option_eq_same_context.
      eassumption.
    - intros [Hf Hc].
      eapply lift_option_eq_intro;
      assumption.
  Qed.
End LIFTOPTION.

Section LIFTPROD.
  Context {S V} `{Hgs: Lens S V} {A: Type}.

  Theorem lift_prod_eq_unlift (f: V -> V * A) (s s': S) (a: A):
    lift π f s = (s', a) ->
    f (π s) = (π s', a).
  Proof.
    unfold lift; simpl.
    destruct (f (π s)) as [v' a'].
    intros H.
    inversion H.
    autorewrite with lens.
    reflexivity.
  Qed.

  Theorem lift_prod_eq_same_context (f: V -> V * A) (s s': S) (a: A):
    lift π f s = (s', a) ->
    same_context π s s'.
  Proof.
    unfold lift; simpl.
    destruct (f (π s)).
    intro H; inversion H; subst.
    symmetry.
    apply lens_set_same_context.
  Qed.

  Theorem lift_prod_eq_intro (f: V -> V * A) (s s': S) (a: A):
    same_context π s s' ->
    f (π s) = (π s', a) ->
    lift π f s = (s', a).
  Proof.
    unfold lift; simpl.
    intros Hc Hv.
    destruct (f (π s)) as [v'].
    inversion Hv; subst; clear Hv.
    rewrite Hc; clear Hc.
    autorewrite with lens.
    reflexivity.
  Qed.

  Theorem lift_prod_eq_iff (f: V -> V * A) (s s': S) (a: A):
    lift π f s = (s', a) <->
    f (π s) = (π s', a) /\ same_context π s s'.
  Proof.
    repeat split.
    - apply lift_prod_eq_unlift.
      assumption.
    - eapply lift_prod_eq_same_context.
      eassumption.
    - intros [Hf Hc].
      apply lift_prod_eq_intro;
      assumption.
  Qed.
End LIFTPROD.

Section LIFTREL.
  Context {S V} `{Lens S V}.

  Global Instance lift_relation_unlift (R: relation V):
    subrelation (lift π R) (R @@ π)%signature.
  Proof.
    unfold lift, RelCompFun; simpl.
    intros s1 s2 Hs.
    inversion Hs.
    autorewrite with lens.
    assumption.
  Qed.

  Global Instance lift_relation_same_context (R: relation V):
    subrelation (lift π R) (same_context π).
  Proof.
    unfold lift; simpl.
    intros s1 s2 Hs.
    inversion Hs.
    autorewrite with lens.
    reflexivity.
  Qed.

  Lemma lift_relation_intro (R: V -> V -> Prop) (s1 s2: S):
    same_context π s1 s2 ->
    R (π s1) (π s2) ->
    lift (Lift := lift_powerset) π R s1 s2.
  Proof.
    intros Hc Hv.
    unfold lift; simpl.
    replace s2 with (set π (π s2) s1).
    * change (set π (π s2) s1) with ((fun v => set π v s1) (π s2)).
      eapply powerset_fmap_intro.
      assumption.
    * rewrite Hc.
      autorewrite with lens.
      reflexivity.
  Qed.

  Lemma lift_relation_iff (R: V -> V -> Prop) (s1 s2: S):
    lift π R s1 s2 <->
    R (π s1) (π s2) /\ same_context π s1 s2.
  Proof.
    repeat split.
    - apply lift_relation_unlift.
      assumption.
    - eapply lift_relation_same_context.
      eassumption.
    - intros [Hv Hc].
      apply lift_relation_intro;
      assumption.
  Qed.
End LIFTREL.

Hint Rewrite
  @lift_option_eq_iff
  @lift_prod_eq_iff
  @lift_relation_iff
  using typeclasses eauto : lift_simpl.


(** ** Solving the residual goals *)

(** The rewriting rules above likely leaves us with several conjunctions.
  We destruct them to make sure that the components are readily available. *)

Ltac split_conjuncts :=
  repeat match goal with
           | [ H: _ /\ _ |- _ ] =>
             let Hl := fresh H "l" in
             let Hr := fresh H "r" in
             destruct H as [Hl Hr]
         end.

(** Hopefully, the residual goal can then easily be solved with
  [eauto], given a few hints in the "lift" database which we use to
  solve corner cases. *)
Hint Extern 10 (eq _ _) =>
  congruence : lift.

(* Use the minimal priority, because we want to use [same_context] as
  a side-condition for some immediate hints. *)
Hint Extern 0 (same_context _ _ _) =>
  congruence || reflexivity : lift.

(** As a last resort, we unfold [lift] and try to normalize the
  result. Hopefully we'll get something easily solvable. *)
Ltac lift_unfold :=
  repeat progress (lift_simpl; unfold lift in *).

(** We're now ready to define our leaf tactic, and use it in
  conjunction with [peel] to solve the goals automatically. *)
Ltac lift_auto :=
  lift_simpl;
  split_conjuncts;
  eauto 10 with lift typeclass_instances;
  lift_unfold;
  eauto 10 with lift typeclass_instances.

(** The [lift_partial] variant allows for some unsolved leaves. *)
Ltac lift_partial π f :=
  pose proof f as Hf;
  lift_peel π Hf lift_auto.

(** The [lift] variant demands 100% success *)
Ltac lift π f :=
  now lift_partial π f.


(** ** Properties of lifted operations *)

(** Lifting commutes with lens composition *)

Section COMPOSE.
  Existing Instances lens_compose compose_lensops.
  Context {A B C} (π: A -> B) (ρ: B -> C) `{Hπ: Lens _ _ π} `{Hρ: Lens _ _ ρ}.
  Context `{HF: Functor}.
  Context (f: C -> F C).

  Lemma lift_compose:
    lift (compose ρ π) f = lift π (lift ρ f).
  Proof.
    unfold lift.
    simpl.
    apply functional_extensionality.
    intros a.
    unfold Basics.compose.
    reflexivity.
  Qed.
End COMPOSE.
