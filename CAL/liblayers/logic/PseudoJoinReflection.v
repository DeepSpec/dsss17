Require Import Coqlib.
Require Import RelationPairs.
Require Import AST.
Require Import Decision.
Require Import Structures.
Require Import PseudoJoin.

Module PJR.

  (** * Syntax *)

  Section SYNTAX.
    Inductive term :=
      | empty: term
      | var: nat -> term
      | combine: term -> term -> term.

    (** Normalization *)

    Fixpoint insert (i: nat) (t: term): term :=
      match t with
        | combine (var j) u =>
          if decide (i <= j)%nat then
            combine (var i) (combine (var j) u)
          else
            combine (var j) (insert i u)
        | _ =>
          combine (var i) t
      end.

    Fixpoint insert_term (t u: term): term :=
      match t with
        | empty => u
        | var i => insert i u
        | combine t1 t2 => insert_term t1 (insert_term t2 u)
      end.

    Definition sort (t: term) :=
      insert_term t empty.
  End SYNTAX.

  (** * Semantics *)

  Section SEMANTICS.
    Context {E} `{Ee: Emptyset E} `{HE: PseudoJoin E ∅}.
    Local Opaque equiv.

    Fixpoint lookup (i: nat) (env: list E) :=
      match i, env with
        | O, x::xs => x
        | S j, x::xs => lookup j xs
        | _, _ => ∅
      end.

    Fixpoint eval (env: list E) (t: term): E :=
      match t with
        | empty => ∅
        | var i => lookup i env
        | combine t1 t2 => eval env t1 ⊕ eval env t2
      end.

    Lemma insert_sound env i t:
      eval env (insert i t) ≡ eval env (combine (var i) t).
    Proof.
      simpl.
      induction t; try reflexivity.
      - simpl.
        destruct t1 as [ | j | u1 u2]; simpl; try reflexivity.
        destruct (decide _); simpl; try reflexivity.
        rewrite IHt2.
        rewrite <- !associativity.
        rewrite (commutativity (lookup _ _)).
        reflexivity.
    Qed.

    Lemma insert_term_sound env t u:
      eval env (insert_term t u) ≡ eval env (combine t u).
    Proof.
      revert u.
      induction t as [ | i | t1 IHt1 t2 IHt2 ]; intro u.
      - simpl.
        split.
        + apply right_upper_bound.
        + apply id_left.
      - transitivity (eval env (insert i u)).
        + reflexivity.
        + apply insert_sound.
      - simpl.
        rewrite IHt1; simpl.
        rewrite IHt2; simpl.
        symmetry.
        apply associativity.
    Qed.

    Lemma sort_sound env t:
      eval env (sort t) ≡ eval env t.
    Proof.
      unfold sort.
      transitivity (eval env (combine t empty)).
      - apply insert_term_sound.
      - simpl.
        split.
        + apply id_right.
        + apply left_upper_bound.
    Qed.
  End SEMANTICS.

  (** * Verification conditions *)

  Section VERIF.
    Context {E} `{Ee: Emptyset E} `{HE: PseudoJoin E ∅}.

    (** Sufficient check for 〚t〛 ≤ 〚u〛. Works on terms n normalize
      by [sort] above. *)
    Fixpoint termcmp (t u: term): bool :=
      match t, u with
        | empty, _ =>
          true
        | combine (var i) t', combine (var j) u' =>
          if decide (i = j) then
            termcmp t' u'
          else
            termcmp t u'
        | _, _ =>
          false
      end.

    Lemma termcmp_sound env t u:
      termcmp t u = true ->
      eval env t ≤ eval env u.
    Proof.
      revert t.
      induction u as [ | i | [ | i | u11 u12] IHu1 u2 IHu2];
        intros t;
        destruct t as [ | j | [ | j | t11 t12] t2];
        inversion 1;
        try apply lower_bound.
      destruct (decide _); subst.
      - simpl.
        monotonicity.
        + reflexivity.
        + eauto.
      - transitivity (eval env u2).
        + eauto.
        + simpl.
          apply right_upper_bound.
    Qed.

    Lemma termcmp_sort_sound env t u:
      termcmp (sort t) (sort u) = true ->
      eval env t ≤ eval env u.
    Proof.
      intros H.
      rewrite <- (sort_sound env t).
      rewrite <- (sort_sound env u).
      apply termcmp_sound.
      assumption.
    Qed.
  End VERIF.

  (** Lookup [x] in list [env]. If it's not in there, a corresponding
    element is added at the end of the list. Then pass the potentially
    extended environment and index to the continuation [cont]. *)
  Ltac l env x cont :=
    let rec iter i e :=
      lazymatch e with
        | x::?xs => cont env i
        | _::?xs => iter (S i) xs
        | _ =>
          let newenv := eval cbv [app] in (env++(x::nil)) in
          cont newenv i
      end in
    iter O env.

  (** Quote the pseudo-join expression [x] with the starting
    environment [env] for variables. The extended environment and
    quoted term are then passed to the continuation [cont]. *)
  Ltac q env x cont :=
    lazymatch x with
      | ∅ => cont env empty
      | ?x1 ⊕ ?x2 =>
        let cont1 env1 t1 :=
          let cont2 env2 t2 :=
            cont env2 (combine t1 t2) in
          q env1 x2 cont2 in
        q env x1 cont1
      | _ =>
        let lcont env i := cont env (var i) in
        l env x lcont
    end.

  Ltac quoteineq :=
    lazymatch goal with
      | |- le (A := ?E) ?x ?y =>
        let xcont xenv t :=
          let ycont yenv u :=
            (change (eval yenv t ≤ eval yenv u)) in
          q xenv y ycont in
        q (@nil E) x xcont
    end.
End PJR.

Ltac pjr :=
  PJR.quoteineq;
  eapply PJR.termcmp_sort_sound;
  reflexivity.

Section TEST.
  Context {E} `{Ee: Emptyset E} `{HE: PseudoJoin E ∅}.
  Context {a b c d e: E}.

  Goal a ⊕ ∅ ⊕ d ≤ b ⊕ e ⊕ d ⊕ a ⊕ b.
  Proof.
    pjr.
  Qed.
End TEST.
