(** DeepSpec Summer School 2017
  * Lectures by Adam Chlipala on proof automation
  * Lecture 1: introduction to proof scripting and the Ltac language
  * Author: Adam Chlipala <http://adam.chlipala.net/>
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Much of the material comes from CPDT <http://adam.chlipala.net/cpdt/> by the same author. *)

(** * Ltac Programming Basics *)

(* We have already seen a few examples of Ltac programs, without much explanation.
 * Ltac is the proof scripting language built into Coq.  Actually, every
 * primitive step in our proofs has been a (degenerate, small) Ltac program.
 * Let's take a bottom-up look at more Ltac features.
 *
 * We've seen [match goal] tactics a few times so far.  They allow syntactic
 * inspection of hypothesis and conclusion formulas of current goals, where we
 * pick tactics to run based on what we find.  Here's a simple example to
 * find an [if] and do a case split based on its test expression. *)

Ltac find_if :=
  match goal with
    | [ |- if ?X then _ else _ ] => destruct X
  end.

(* Here's a proof that becomes trivial, given [find_if].  You can imagine a
 * whole family of similar theorems that also become trivial. *)

Theorem hmm : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
Proof.
  intros.
  repeat find_if. (* Note [repeat] for "run over and over until you can't
                   * progress." *)
  trivial.
  trivial.
  trivial.
  trivial.

  (* Let's write that again with more automation. *)
  Restart.
  intros; repeat find_if; trivial.
Qed.

(* Another very useful Ltac building block is *context patterns*. *)

Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

(* The behavior of this tactic is to find any subterm of the conclusion that is
 * an [if] and then [destruct] the test expression.  This version subsumes
 * [find_if].  The general behavior of [context] (an Ltac keyword) is to allow
 * matching in arbitrary subterms. *)

Theorem hmm' : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
Proof.
  intros; repeat find_if_inside; trivial.
Qed.

(* We can also use [find_if_inside] to prove goals that [find_if] does not
 * simplify sufficiently. *)

Theorem hmm2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
Proof.
  intros; repeat find_if_inside; reflexivity.
Qed.


(** * Implementing some of [tauto] ourselves *)

(* In class, we develop our own implementation of [tauto] one feature
 * at a time, but here's just the final product.  To understand it, we print
 * the definitions of the logical connectives.  Interestingly enough, they are
 * special cases of the machinery we met last time for inductive relations! *)

Print True.
Print False.
Locate "/\".
Print and.
Locate "\/".
Print or.
(* Implication ([->]) is built into Coq, so nothing to look up there. *)

Ltac my_tauto :=
  repeat match goal with
	   | [ H : ?P |- ?P ] => exact H

	   | [ |- True ] => constructor
	   | [ |- _ /\ _ ] => constructor
	   | [ |- _ -> _ ] => intro

	   | [ H : False |- _ ] => destruct H
	   | [ H : _ /\ _ |- _ ] => destruct H
	   | [ H : _ \/ _ |- _ ] => destruct H

	   | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
	 end.

Section propositional.
  Variables P Q R : Prop.

  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
  Proof.
    my_tauto.
  Qed.
End propositional.

(* [match goal] has useful backtracking semantics.  When one rule fails, we
 * backtrack automatically to the next one. *)

(* For instance, this (unnecessarily verbose) proof script works: *)

Theorem m1 : True.
Proof.
  match goal with
    | [ |- _ ] => intro
    | [ |- True ] => constructor
  end.
Qed.

(* The example shows how failure can move to a different pattern within a
 * [match].  Failure can also trigger an attempt to find _a different way of
 * matching a single pattern_.  Consider another example: *)

Theorem m2 : forall P Q R : Prop, P -> Q -> R -> Q.
Proof.
  intros; match goal with
            | [ H : _ |- _ ] => idtac H
          end.

  (* Coq prints "[H1]".  By applying [idtac] with an argument, a convenient
   * debugging tool for "leaking information out of [match]es," we see that
   * this [match] first tries binding [H] to [H1], which cannot be used to prove
   * [Q].  Nonetheless, the following variation on the tactic succeeds at
   * proving the goal: *)

  match goal with
    | [ H : _ |- _ ] => idtac H; exact H
  end.
Qed.

(* The tactic first unifies [H] with [H1], as before, but [exact H] fails in
 * that case, so the tactic engine searches for more possible values of [H].
 * Eventually, it arrives at the correct value, so that [exact H] and the
 * overall tactic succeed. *)

(* Let's try some more ambitious reasoning, with quantifiers.  We'll be
 * instantiating quantified facts heuristically.  If we're not careful, we get
 * in a loop repeating the same instantiation forever.  We'll need a way to
 * check that a fact is not already known.  Here's a tactic: *)

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
      (* A hypothesis already asserts this fact. *)
    | _ =>
      match P with
        | ?P1 /\ ?P2 =>
          (* Check each conjunct of [P] separately, since they might be known by
           * different means. *)
          first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
          (* If we manage to get this far, then we found no redundancy, so
           * declare success. *)
      end
  end.

(* The number for [fail N] indicates failing at the backtracking point [N]
 * levels out from where we are.  [first] applies the first tactic that does not
 * fail. *)

(* This tactic adds a fact to the context, only if it is not not already
 * present. *)

Ltac extend pf :=
  let t := type of pf in
    notHyp t; pose proof pf.

(* With these tactics defined, we can write a tactic [completer] for, among
 * other things, adding to the context all consequences of a set of simple
 * first-order formulas. *)

Ltac completer :=
  repeat match goal with
	   | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')

           | [ |- _ /\ _ ] => constructor
           | [ |- forall x, _ ] => intro
           | [ |- _ -> _ ] => intro
         end.

Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall (y x : A), P x -> S x.
  Proof.
    completer.
    assumption.
  Qed.
End firstorder.


(** * Recursive Proof Search *)

(* Let's work on a tactic to try all possible instantiations of quantified
 * hypotheses, attempting to find out where the goal becomes obvious. *)

Ltac inster n :=
  intuition;
    match n with
      | S ?n' =>
        match goal with
          | [ H : forall x : ?T, _, y : ?T |- _ ] => pose proof (H y); inster n'
        end
    end.

(* Important: when one recursive call fails, the backtracking semantics of
 * [match goal] cause us to try the next instantiation! *)

Section test_inster.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable f : A -> A.
  Variable g : A -> A -> A.

  Hypothesis H1 : forall x y, P (g x y) -> Q (f x).

  Theorem test_inster : forall x, P (g x x) -> Q (f x).
  Proof.
    inster 2.
  Qed.

  Hypothesis H3 : forall u v, P u /\ P v /\ u <> v -> P (g u v).
  Hypothesis H4 : forall u, Q (f u) -> P u /\ P (f u).

  Theorem test_inster2 : forall x y, x <> y -> P x -> Q (f y) -> Q (f x).
  Proof.
    inster 3.
  Qed.
End test_inster.


(** * Creating Unification Variables *)

(* A final useful ingredient in tactic crafting is the ability to allocate new
 * unification variables explicitly.  Before we are ready to write a tactic, we
 * can try out its ingredients one at a time. *)

Theorem t5 : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intros.

  evar (y : nat).

  let y' := eval unfold y in y in
    clear y; specialize (H y').

  apply H.
Qed.

Ltac newEvar T k :=
  let x := fresh "x" in
  evar (x : T);
  let x' := eval unfold x in x in
    clear x; k x'.

Ltac insterU H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             newEvar T ltac:(fun y => specialize (H y))
         end.

Theorem t5' : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intro H.
  insterU H.
  apply H.
Qed.

(* This particular example is somewhat silly, since [apply] by itself would have
 * solved the goal originally.  Separate forward reasoning is more useful on
 * hypotheses that end in existential quantifications.  Before we go through an
 * example, it is useful to define a variant of [insterU] that does not clear
 * the base hypothesis we pass to it. *)

Ltac insterKeep H :=
  let H' := fresh "H'" in
    pose proof H as H'; insterU H'.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros.

    do 2 insterKeep H1.

    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H
           end.

    eauto.
  Qed.
End t6.

(* Here's an example where something bad happens. *)

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros; do 2 insterKeep H1;
      repeat match goal with
               | [ H : ex _ |- _ ] => destruct H
             end; eauto.

    (* Oh, two trivial goals remain. *)
    Unshelve.
    assumption.
    assumption.
  Qed.
End t7.

(* Why did we need to do that extra work?  The [forall] rule was also matching
 * implications! *)

Module Import FixedInster.
  Ltac insterU tac H :=
    repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
             | Prop =>
               (let H' := fresh "H'" in
                assert (H' : T) by solve [ tac ];
                specialize (H H'); clear H')
               || fail 1
             | _ =>
               newEvar T ltac:(fun y => specialize (H y))
             end
           end.

  Ltac insterKeep tac H :=
    let H' := fresh "H'" in
      pose proof H as H'; insterU tac H'.
End FixedInster.

Section t7'.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7' : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros.
    do 2 insterKeep ltac:(idtac; match goal with
                                 | [ H : Q ?v |- _ ] =>
                                   match goal with
                                   | [ _ : context[P v _] |- _ ] => fail 1
                                   | _ => apply H
                                   end
                                 end) H1;
    repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           end; eauto.
  Qed.
End t7'.

Theorem t8 : exists p : nat * nat, fst p = 3.
Proof.
  econstructor.
  instantiate (1 := (3, 2)).
  reflexivity.
Qed.

(* A way that plays better with automation: *)

Ltac equate x y :=
  let dummy := constr:(eq_refl x : x = y) in idtac.

Theorem t9 : exists p : nat * nat, fst p = 3.
Proof.
  econstructor; match goal with
                  | [ |- fst ?x = 3 ] => equate x (3, 2)
                end; reflexivity.
Qed.
