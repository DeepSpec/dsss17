Require Import Arith List Permutation.

Set Implicit Arguments.

(* Let's introduce *proof by reflection* for the kind of permutation example that
 * Andrew Appel showed near the end of his first lecture. *)

Section lists.
  Variable A : Set.
  Variable default : A.

  (* Step 1: define types of syntax for important parts of the goals we want to solve. *)

  Notation base_var := nat.
  Notation list_var := nat.

  Inductive term :=
  | Nil
  | Cons (x : base_var) (t : term)
  | App (t1 t2 : term)
  | Var (X : list_var).

  (* Step 2: give meaning to syntax. *)

  Fixpoint termD (xs : list A) (Xs : list (list A)) (t : term) : list A :=
    match t with
    | Nil => nil
    | Cons x t' => nth_default default xs x :: termD xs Xs t'
    | App t1 t2 => termD xs Xs t1 ++ termD xs Xs t2
    | Var X => nth_default nil Xs X
    end.

  (* Step 3: define the automatic reasoning procedure in Gallina. *)

  Record summary := {
    BaseVars : list (base_var * nat); (* How many times does it occur? *)
    ListVars : list (list_var * nat); (* Ditto. *)
  }.
  (* All lists will be kept sorted by variable (in increasing order). *)

  Definition empty : summary := {|
    BaseVars := nil; ListVars := nil
  |}.

  (* Increment the count for a variable (of either kind) in a sorted list. *)
  Fixpoint increment (x : nat) (amt : nat) (ls : list (nat * nat)) : list (nat * nat) :=
    match ls with
    | nil => (x, amt) :: nil
    | (y, n) :: ls => if x =? y then (y, amt + n) :: ls
                      else if x <? y then (x, amt) :: (y, n) :: ls
                      else (y, n) :: increment x amt ls
    end.

  (* Merge two sorted lists, adding counts for duplicates. *)
  Fixpoint merge (ls1 ls2 : list (nat * nat)) : list (nat * nat) :=
    match ls1 with
    | nil => ls2
    | (x, n) :: ls1' => increment x n (merge ls1' ls2)
    end.

  (* Add one more occurrence of a base variable. *)
  Definition increment_base (s : summary) (x : base_var) := {|
    BaseVars := increment x 1 s.(BaseVars);
    ListVars := s.(ListVars)
  |}.

  (* Add the occurrence counts for all variables. *)
  Definition merge_summaries (s1 s2 : summary) := {|
    BaseVars := merge s1.(BaseVars) s2.(BaseVars);
    ListVars := merge s1.(ListVars) s2.(ListVars)
  |}.

  (* Compile a term into a summary. *)
  Fixpoint summarize (t : term) : summary :=
    match t with
    | Nil => empty
    | Cons x t => increment_base (summarize t) x
    | App t1 t2 => merge_summaries (summarize t1) (summarize t2)
    | Var X => {| BaseVars := nil; ListVars := (X, 1) :: nil |}
    end.

  (* Decidable equality for summaries *)

  Fixpoint lists_eq (ls1 ls2 : list (nat * nat)) : bool :=
    match ls1, ls2 with
    | nil, nil => true
    | (x1, n1) :: ls1', (x2, n2) :: ls2' => (x1 =? x2) && (n1 =? n2) && lists_eq ls1' ls2'
    | _, _ => false
    end.

  Definition summaries_eq (s1 s2 : summary) : bool :=
    lists_eq s1.(BaseVars) s2.(BaseVars)
    && lists_eq s1.(ListVars) s2.(ListVars).

  (* Step 4: prove the auomated procedure correct. *)

  (* First we'll need to give meaning to summaries. *)

  (* [n] copies of base value [v] *)
  Fixpoint repeatedBaseVar (v : A) (n : nat) : list A :=
    match n with
    | O => nil
    | S n' => v :: repeatedBaseVar v n'
    end.

  (* all copies implied by [xs], looking up variable values in [vs] *)
  Fixpoint baseVars (vs : list A) (xs : list (base_var * nat)) : list A :=
    match xs with
    | nil => nil
    | (x, n) :: xs' => let v := nth_default default vs x in
                       repeatedBaseVar v n ++ baseVars vs xs'
    end.

  (* [n] copies of list [V] *)
  Fixpoint repeatedListVar (V : list A) (n : nat) : list A :=
    match n with
    | O => nil
    | S n' => V ++ repeatedListVar V n'
    end.

  (* all copies implied by [Xs], looking up variable values in [Vs] *)
  Fixpoint listVars (Vs : list (list A)) (Xs : list (list_var * nat)) : list A :=
    match Xs with
    | nil => nil
    | (X, n) :: Xs' => let V := nth_default nil Vs X in
                       repeatedListVar V n ++ listVars Vs Xs'
    end.

  Hint Rewrite app_nil_r.

  (* Now, the meaning of a summary *)
  Definition summaryD (vs : list A) (Vs : list (list A)) (s : summary) : list A :=
    baseVars vs s.(BaseVars) ++ listVars Vs s.(ListVars).

  (* A whole darn lot of lemmas, whose statements tend to be more useful
   * descriptions than any English text *)

  Lemma repeatedBaseVar_plus : forall v n2 n1,
      Permutation
        (repeatedBaseVar v (n1 + n2))
        (repeatedBaseVar v n1 ++ repeatedBaseVar v n2).
  Proof.
    induction n1; simpl; auto.
  Qed.

  Lemma Permutation_assoc : forall A (ls1 ls2 ls3 : list A),
      Permutation ((ls1 ++ ls2) ++ ls3) (ls1 ++ (ls2 ++ ls3)).
  Proof.
    induction ls1; simpl; auto.
  Qed.

  Lemma Permutation_comm_front : forall A (ls1 ls2 ls3 : list A),
      Permutation (ls1 ++ ls2 ++ ls3) (ls2 ++ ls1 ++ ls3).
  Proof.
    induction ls1; simpl; intros; auto.
    eapply Permutation_trans.
    2: apply Permutation_middle.
    constructor.
    auto.
  Qed.

  Lemma baseVars_increment : forall vs x amt xs,
      Permutation
        (baseVars vs (increment x amt xs))
        (repeatedBaseVar (nth_default default vs x) amt ++ baseVars vs xs).
  Proof.
    induction xs as [ | [ ] ]; simpl; auto.
    destruct (Nat.eqb_spec x n); subst; simpl; auto.

    eapply Permutation_trans.
    apply Permutation_app.
    apply repeatedBaseVar_plus.
    auto.
    apply Permutation_assoc.

    destruct (Nat.ltb_spec x n); simpl; auto.

    eapply Permutation_trans.
    eapply Permutation_app.
    auto.
    eassumption.
    apply Permutation_comm_front.
  Qed.

  Lemma baseVars_increment1 : forall vs x xs,
      Permutation
        (baseVars vs (increment x 1 xs))
        (nth_default default vs x :: baseVars vs xs).
  Proof.
    intros; apply baseVars_increment.
  Qed.

  Lemma repeatedListVar_plus : forall V n2 n1,
      Permutation
        (repeatedListVar V (n1 + n2))
        (repeatedListVar V n1 ++ repeatedListVar V n2).
  Proof.
    induction n1; simpl; auto.
    eapply Permutation_trans.
    apply Permutation_app.
    auto.
    eassumption.
    symmetry; apply Permutation_assoc.
  Qed.

  Lemma listVars_increment : forall Vs X amt Xs,
      Permutation
        (listVars Vs (increment X amt Xs))
        (repeatedListVar (nth_default nil Vs X) amt ++ listVars Vs Xs).
  Proof.
    induction Xs as [ | [ ] ]; simpl; auto.
    destruct (Nat.eqb_spec X n); subst; simpl; auto.

    eapply Permutation_trans.
    apply Permutation_app.
    apply repeatedListVar_plus.
    auto.
    apply Permutation_assoc.

    destruct (Nat.ltb_spec X n); simpl; auto.

    eapply Permutation_trans.
    eapply Permutation_app.
    auto.
    eassumption.
    apply Permutation_comm_front.
  Qed.

  Lemma baseVars_merge : forall vs xs2 xs1,
      Permutation
        (baseVars vs (merge xs1 xs2))
        (baseVars vs xs1 ++ baseVars vs xs2).
  Proof.
    induction xs1 as [ | [ ] ]; simpl; auto.
    eapply Permutation_trans.
    apply baseVars_increment.
    eapply Permutation_trans.
    apply Permutation_app.
    auto.
    eassumption.
    symmetry; apply Permutation_assoc.
  Qed.

  Lemma listVars_merge : forall Vs Xs2 Xs1,
      Permutation
        (listVars Vs (merge Xs1 Xs2))
        (listVars Vs Xs1 ++ listVars Vs Xs2).
  Proof.
    induction Xs1 as [ | [ ] ]; simpl; auto.
    eapply Permutation_trans.
    apply listVars_increment.
    eapply Permutation_trans.
    apply Permutation_app.
    auto.
    eassumption.
    symmetry; apply Permutation_assoc.
  Qed.

  (* One of two key correctness properties behind our procedure *)
  Lemma summarize_correct : forall vs Vs t,
      Permutation (summaryD vs Vs (summarize t)) (termD vs Vs t).
  Proof.
    induction t; unfold summaryD in *; simpl; autorewrite with core; auto.

    eapply Permutation_trans.
    eapply Permutation_app.
    apply baseVars_increment1.
    eauto.
    simpl.
    eauto.

    eapply Permutation_trans.
    eapply Permutation_app.
    apply baseVars_merge.
    apply listVars_merge.
    eapply Permutation_trans.
    2: apply Permutation_app; eassumption.
    repeat rewrite <- app_assoc.
    apply Permutation_app; auto.
    apply Permutation_comm_front.
  Qed.

  Lemma lists_eq_correct : forall ls1 ls2,
      lists_eq ls1 ls2 = true -> ls1 = ls2.
  Proof.
    induction ls1 as [ | [ ] ]; destruct ls2 as [ | [ ] ]; simpl; intuition; try discriminate.
    apply Bool.andb_true_iff in H; intuition.
    apply Bool.andb_true_iff in H0; intuition.
    apply Nat.eqb_eq in H.
    apply Nat.eqb_eq in H2.
    apply IHls1 in H1.
    congruence.
  Qed.

  (* The other key property behind our procedure *)
  Lemma summaries_eq_correct : forall s1 s2,
      summaries_eq s1 s2 = true -> s1 = s2.
  Proof.
    destruct s1, s2; unfold summaries_eq; simpl; intros.
    apply Bool.andb_true_iff in H; intuition.
    apply lists_eq_correct in H0.
    apply lists_eq_correct in H1.
    congruence.
  Qed.

  (* We put the key properties together into one theorem. *)
  Theorem it_really_is_a_permutation : forall vs Vs t1 t2,
      summaries_eq (summarize t1) (summarize t2) = true
      -> Permutation (termD vs Vs t1) (termD vs Vs t2).
  Proof.
    intros.
    apply summaries_eq_correct in H.
    eapply Permutation_trans.
    apply Permutation_sym; apply summarize_correct.
    rewrite H; apply summarize_correct.
  Qed.
End lists.

Import ListNotations.

(* Step 5: reify! *)

(* Our next challenge is to take Coq goals and create related syntax trees.
 * We'll do some Ltac programming. *)

(* Is [X] an element of list [L]? *)
Ltac inList X L :=
  match L with
  | nil => false
  | X :: _ => true
    (* ^-- note that *this* [X] is *not* a pattern variable!
     * It checks equality with the [X] that is scope. *)
  | _ :: ?L' => inList X L'
  end.

(* Return a list of all unique "variables" in term [L].
 * [xs] is a list of base variables that should be extended.
 * [Xs] is a list of list variables that should be extended.
 * Note that "variable" here essentially means "term that doesn't match any of our
 * explicit syntax cases." *)
Ltac varsOf L xs Xs :=
  match L with
  | nil => constr:((xs, Xs))
  | ?x :: ?L' =>
    let p := varsOf L' xs Xs in
    match p with
    | (?xs, ?Xs) =>
      match inList x xs with
      | true => constr:((xs, Xs))
      | false => constr:((x :: xs, Xs))
      end
    end
  | ?L1 ++ ?L2 =>
    let p := varsOf L1 xs Xs in
    match p with
    | (?xs, ?Xs) => varsOf L2 xs Xs
    end
  | _ =>
    match inList L Xs with
    | true => constr:((xs, Xs))
    | false => constr:((xs, L :: Xs))
    end
  end.

(* What is the numeric position of [X] in list [Xs]? *)
Ltac posnOf X Xs :=
  match Xs with
  | X :: _ => O
  | _ :: ?Xs' =>
    let n := posnOf X Xs' in
    constr:(S n)
  end.

(* Given variable lists [xs] and [Xs], convert list term [E] into a syntactic [term]. *)
Ltac reifyTerm xs Xs E :=
  match E with
  | nil => Nil
  | ?e :: ?E' =>
    let x := posnOf e xs in
    let E' := reifyTerm xs Xs E' in
    constr:(Cons x E')
  | ?E1 ++ ?E2 =>
    let E1 := reifyTerm xs Xs E1 in
    let E2 := reifyTerm xs Xs E2 in
    constr:(App E1 E2)
  | _ =>
    let X := posnOf E Xs in
    constr:(Var X)
  end.

(* Convert a permutation goal into one that fits [it_really_is_a_permutation].
 * It takes in a default element of the base type. *)
Ltac reify default :=
  match goal with
  | [ |- @Permutation ?A ?ls1 ?ls2 ] =>
    let p := varsOf ls1 (@nil A) (@nil (list A)) in
    match p with
    | (?xs, ?Xs) =>
      let ls1 := reifyTerm xs Xs ls1 in
      let ls2 := reifyTerm xs Xs ls2 in
      change (Permutation (termD default xs Xs ls1) (termD default xs Xs ls2))
    end
  end.

(* Finish the procedure: also apply the main theorem and use [reflexivity]
 * to prove its premise. *)
Ltac permutation default :=
  reify default; apply it_really_is_a_permutation; reflexivity.

Example butterfly : forall b u t e r f l y : nat,
    Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
Proof.
  intros; permutation 0.
Qed.

Example butterfly2 : forall (b u t e r f l y : nat) (turtle : list nat),
    Permutation (turtle++[b;u;t;t;e;r]++turtle++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]++turtle++turtle).
Proof.
  intros; permutation 0.
Qed.
