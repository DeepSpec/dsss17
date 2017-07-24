Require Import Recdef Bool Arith Omega List Wellfounded Coq.Program.Wf.
Require Import MSets.
Require Import Maps Imp.
Require Import Sequences Semantics Deadcode.
Import VSdecide.

(** Advanced topic: computing fixpoints using Knaster-Tarski's theorem,
   with applications to liveness analysis. *)

(** * 1. Fixpoints *)

Section FIXPOINT.

(** Consider a type [A] equipped with a decidable equality [eq] and a
    transitive ordering [le]. *)

Variable A: Type.

Variable eq: A -> A -> Prop.
Variable beq: A -> A -> bool.
Hypothesis beq_correct: forall x y, if beq x y then eq x y else ~eq x y.

Variable le: A -> A -> Prop.
Hypothesis le_trans: forall x y z, le x y -> le y z -> le x z.

(** This is the strict order induced by [le].  We assume it is well-founded:
  all strictly ascending chains are finite. *)

Definition gt (x y: A) := le y x /\ ~eq y x.
Hypothesis gt_wf: well_founded gt.

(** Let [bot] be a smallest element of [A]. *)
Variable bot: A.
Hypothesis bot_smallest: forall x, le bot x.

(** Let [F] be a monotonic function from [A] to [A]. *)

Variable F: A -> A.
Hypothesis F_mon: forall x y, le x y -> le (F x) (F y).

(** Terminology: an element [x] of [A] is
- a fixpoint if [eq x (F x)] i.e. [F x = x] up to the equality [eq];
- a pre-fixpoint if [le (F x) x] i.e. [F x] is below [x] in the [le] ordering;
- a post-fixpoint if [le x (F x)] i.e. [F x] is above [x] in the [le] ordering.
*)

(** We iterate [F] starting from a post-fixpoint [x] until we reach a fixpoint.

  The [iterate] function takes as argument not just [x], but also a
  proof that [x] is a post-fixpoint, i.e. [le x (F x)].  This proof is
  needed to show that [x] increases strictly during iteration, thus
  ensuring termination. *)

(* To define [iterate], we use Coq's [Function] mechanism, which supports
  nonstructural recursion whose termination is ensured by a well-founded
  ordering.  [Function] also produces a convenient induction principle,
  accessible via the [functional induction] tactic, which mimics the
  case analysis and recursive calls made by the function. *)

Function iterate (x: A) (P: le x (F x)) {wf gt x} : A :=
  let x' := F x in
  if beq x x' then x else iterate x' (F_mon x (F x) P).
Proof.
- (* show that [gt (F x) x] in the recursive case, i.e. if [beq x (F x) = false]. *)
  split.
  auto.
  generalize (beq_correct x (F x)). rewrite teq. auto.
- (* show that the [gt] ordering is well-founded *)
  apply gt_wf.
Qed.

(** In the recursive case, [F_mon x (F x) P] is a proof term that shows
  [le (F x) (F (F x))], i.e. [le x' (F x')]. *)

(** [Function] produces some proof obligations, which it leaves for us to prove
  in interactive proof mode.  One of these obligations is that the [gt] ordering
  used to guarantee termination is indeed well-founded.  The other obligations
  (here, just one) are to show that arguments to recursive calls are in the [gt]
  relation with the current [x], thus guaranteeing termination. *)

(** The fixpoint is obtained by iterating from [bot]. *)

Definition fixpoint : A := iterate bot (bot_smallest (F bot)).

(** We now show that [fixpoint] is a fixpoint. *)

Theorem fixpoint_correct:
  eq fixpoint (F fixpoint).
Proof.
  assert (REC: forall x P, eq (iterate x P) (F (iterate x P))).
  {
    intros x P. functional induction (iterate x P).
  - (* base case [beq x (F x) = true] *)
    generalize (beq_correct x (F x)); rewrite e. auto.
  - (* recursive case [beq x (F x) = false] *)
    apply IHa. 
  }
  apply REC.
Qed.

(** Moreove, [fixpoint] is smaller or equal to any pre-fixpoint. *)

Theorem fixpoint_smallest:
  forall z, le (F z) z -> le fixpoint z.
Proof.
  intros z PREFIXPOINT.
  assert (REC: forall x P, le x z -> le (iterate x P) z).
  {
    intros x P. functional induction (iterate x P).
  - (* base case [beq x (F x) = true] *)
    auto.
  - (* recursive case [beq x (F x) = false] *)
    intros. apply IHa. apply le_trans with (F z). apply F_mon; auto. auto. 
  }
  apply REC. apply bot_smallest.
Qed.

End FIXPOINT.

(** *** Exercise (3 stars, optional) *)
(** The code above computes the smallest fixpoint of the functional [F].
    How would you modify it so that it computes the greatest fixpoint instead?
    Hint: you need to iterate starting from pre-fixpoints [x] (satisfying
    [le (F x) x]), creating a descending chain.  Hence, you need to make
    sure that all strictly descending chains are finite. *)

(** * 2. Subsets of a finite set of variables. *)

Section VARS.

(** Let [U] be the ``universe'' of variables: all variables appearing in the
  program we analyze. *)

Variable U: VS.t.

(** Define [vset] as the type of subsets of [U].  It is a dependent pair
  of a set [S] of variables and a proof that [S] is a subset of [U]. *)

Definition vset : Type := { S: VS.t | VS.Subset S U }.

(** This type comes with a constructor and two projections: *)

Definition make_vset (S: VS.t) (CONTAINED: VS.Subset S U) : vset := exist _ S CONTAINED.

Definition carrier (x: vset) : VS.t := proj1_sig x.

Definition contained (x: vset) : VS.Subset (carrier x) U := proj2_sig x.

(** Defining operations over [vset] is painful because we have to
- write [carrier] projections
- provide proof terms witnessing that the result is a subset of [U].
*)

(*
Definition vset_union(x y: vset) : vset := make_vset (VS.union (carrier x) (carrier y)) ???.
*)

(** The [Program Definition] mechanism helps:
- by automatically inserting projections and constructors for subset types;
- by letting us write [_] (underscore) for the proof terms and dropping us
  into interactive proof mode to fill these holes ("proof obligations").
*)

Program Definition vset_union(x y: vset) : vset := VS.union x y.
Next Obligation.
  intros. apply VSP.union_subset_3; apply contained.
Qed.

(** We equip the type [vset] with a decidable equality (= same elements)
  and the subset ordering. *)

Program Definition vset_eq (x y: vset) : Prop := VS.Equal x y.

Program Definition vset_beq (x y: vset) : bool := VS.equal x y.

Lemma vset_beq_correct: forall x y, if vset_beq x y then vset_eq x y else ~vset_eq x y.
Proof.
  unfold vset_beq, vset_eq; intros. destruct (VS.equal (proj1_sig x) (proj1_sig y)) eqn:EQ.
  apply VS.equal_spec; auto.
  rewrite <- VS.equal_spec. congruence.
Qed.

Program Definition vset_le (x y: vset) : Prop := VS.Subset x y.

Lemma vset_le_trans: forall x y z, vset_le x y -> vset_le y z -> vset_le x z.
Proof.
  unfold vset_le; intros. eapply VSP.subset_trans; eauto.
Qed.

(** The empty set is a smallest element. *)

Program Definition vset_empty : vset := VS.empty.
Next Obligation.
  apply VSP.subset_empty.
Qed.

Lemma vset_empty_le: forall x, vset_le vset_empty x.
Proof.
  unfold vset_le, vset_empty. simpl. intros. apply VSP.subset_empty. 
Qed.

(** To show that the strict order induced by [vset_eq] and [vset_le] is well-founded,
  we first define a nonnegative measure over the type [vset], which is the cardinal
  of the complement of the set. *)

Program Definition vset_measure (x: vset) : nat := VS.cardinal (VS.diff U x).

Lemma vset_measure_decreases:
  forall x y, vset_le x y -> ~vset_eq x y -> vset_measure y < vset_measure x.
Proof.
  intros. unfold vset_measure. red in H. 
  set (X := proj1_sig x) in *. set (Y := proj1_sig y) in *. 
  (* Find an element that is in [y] but not in [x]. *)
  destruct (VS.choose (VS.diff Y X)) as [a | ] eqn:CHOICE.
- assert (VS.In a (VS.diff Y X)) by (apply VS.choose_spec1; auto).
  assert (VS.In a Y) by (eapply VS.diff_spec; eauto).
  assert (~VS.In a X) by (eapply VS.diff_spec; eauto).
  apply VSP.subset_cardinal_lt with a.
  fsetdec.
  apply VS.diff_spec. split; auto. eapply contained; eauto.
  fsetdec.
- (* Show contradiction if no such element exists *)
  assert (VS.Empty (VS.diff Y X)) by (apply VS.choose_spec2; auto). 
  elim H0. red. rewrite VSP.double_inclusion. split; auto.
  fold X Y. fsetdec.
Qed.

(** It follows that the induced strict order is well-founded, because the
  [>] ordering over natural numbers is well-founded. *)

Lemma vset_measure_wf:
  well_founded (fun x y : vset => vset_measure x < vset_measure y).
Proof.
  apply well_founded_ltof.
Qed.

Lemma vset_gt_incl_measure:
  forall x y, gt _ vset_eq vset_le x y -> vset_measure x < vset_measure y.
Proof.
  intros. destruct H. apply vset_measure_decreases; auto.
Qed.

Lemma vset_gt_wf:
  well_founded (gt _ vset_eq vset_le).
Proof.
  eapply wf_incl. red. apply vset_gt_incl_measure. apply vset_measure_wf.
Qed.

(** We can therefore take fixpoints of monotone operators over [vset]. *)

Definition monotone (F: vset -> vset) : Prop :=
  forall x y, vset_le x y -> vset_le (F x) (F y).

Definition vset_fixpoint (F: vset -> vset) (M: monotone F) : vset :=
  fixpoint vset vset_eq vset_beq vset_beq_correct
           vset_le vset_gt_wf vset_empty vset_empty_le F M.

Lemma vset_fixpoint_correct:
  forall F (M: monotone F), vset_eq (vset_fixpoint F M) (F (vset_fixpoint F M)).
Proof.
  intros. unfold vset_fixpoint; apply fixpoint_correct.
Qed.

Lemma vset_fixpoint_smallest:
  forall F (M: monotone F) z, vset_le (F z) z -> vset_le (vset_fixpoint F M) z.
Proof.
  intros. unfold vset_fixpoint; apply fixpoint_smallest; eauto using vset_le_trans.
Qed.

(** Moreover, if an operator [F1] is pointwise below another operator [F2],
  [F1]'s fixpoint is below [F2]'s fixpoint. *)

Lemma vset_fixpoint_le:
  forall F1 F2 (M1: monotone F1) (M2: monotone F2),
  (forall x, vset_le (F1 x) (F2 x)) ->
  vset_le (vset_fixpoint F1 M1) (vset_fixpoint F2 M2).
Proof.
  intros.
  apply vset_fixpoint_smallest. 
  eapply VSP.subset_trans. apply H.
  apply VSP.subset_equal. apply VSP.equal_sym. apply vset_fixpoint_correct.
Qed.

(** * 3. IMP programs whose free variables are in [U]. *)

(** We redefine the abstract syntax of IMP to ensure that all
  variables mentioned in the program are taken from [U]. *)

Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AId : forall (x: id), VS.In x U -> aexp        (**r <--- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : forall (x: id), VS.In x U -> aexp -> com   (**r <--- NEW *)
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(** As a consequence, the [fv_] operations always return an element of type [vset]. *)

Program Fixpoint fv_aexp (a: aexp) : vset :=
  match a with
  | ANum n => vset_empty
  | AId v _ => VS.singleton v
  | APlus a1 a2 => vset_union (fv_aexp a1) (fv_aexp a2)
  | AMinus a1 a2 => vset_union (fv_aexp a1) (fv_aexp a2)
  | AMult a1 a2 => vset_union (fv_aexp a1) (fv_aexp a2)
  end.
Next Obligation.
  red; intros. apply VS.singleton_spec in H. congruence. 
Qed.

Fixpoint fv_bexp (b: bexp) : vset :=
  match b with
  | BTrue => vset_empty
  | BFalse => vset_empty
  | BEq a1 a2 => vset_union (fv_aexp a1) (fv_aexp a2)
  | BLe a1 a2 => vset_union (fv_aexp a1) (fv_aexp a2)
  | BNot b1 => fv_bexp b1
  | BAnd b1 b2 => vset_union (fv_bexp b1) (fv_bexp b2)
  end.

(** * 4. Application to liveness analysis *)

(** We now define (by structural induction on [c]) a function [dlive c]
  that returns a function from [L], the set of variables live "after"
  command [c], to the set of variables live "before" [c].
  In order to be able to take fixpoints within its definition, we
  must also return a proof that [dlive c] is a monotone function. *)

Program Fixpoint dlive (c: com) : { f: vset -> vset | monotone f } :=
  match c with
  | CSkip =>
      fun (L: vset) => L
  | CAss x _ a =>
      fun (L: vset) =>
        if VS.mem x L
        then vset_union (VS.remove x L) (fv_aexp a)
        else L
  | CSeq c1 c2 =>
      fun (L: vset) => dlive c1 (dlive c2 L)
  | CIf b c1 c2 =>
      fun (L: vset) => vset_union (fv_bexp b) (vset_union (dlive c1 L) (dlive c2 L))
  | CWhile b c =>
      fun (L: vset) =>
        let L' := vset_union (fv_bexp b) L in
        vset_fixpoint (fun x => vset_union L' (dlive c x)) _
  end.
Next Obligation.
  red; intros; auto.
Qed.
Next Obligation.
  apply VSP.subset_remove_3. apply contained.
Qed.
Next Obligation.
  red; intros. unfold vset_le in *. set (X := proj1_sig x0) in *. set (Y := proj1_sig y) in *.
  destruct (VS.mem x X) eqn:xlive1.
- replace (VS.mem x Y) with true.
+ simpl. fsetdec. 
+ symmetry; apply VS.mem_spec. apply VS.mem_spec in xlive1. fsetdec.
- destruct (VS.mem x Y) eqn:xlive2; simpl.
+ fold X. eapply VSP.subset_trans. 2: apply VSP.union_subset_1.
  apply VS.mem_spec in xlive2. red; intros. apply VS.remove_spec. split. fsetdec. apply VS.mem_spec in H0. congruence.
+ auto.
Qed.
Next Obligation.
  red; auto.
Defined.
Next Obligation.
  red; intros. unfold vset_le, vset_union; simpl.
  apply VSP.union_subset_5. 
  eapply VSP.subset_trans. apply VSP.union_subset_4. apply m. eauto. 
  apply VSP.union_subset_5. apply m0. auto.
Defined.
Next Obligation.
  red; intros. unfold vset_le, vset_union; simpl. 
  apply VSP.union_subset_5. apply m; auto.
Defined.
Next Obligation.
  red; intros. apply vset_fixpoint_le. 
  intros. unfold vset_le, vset_union; simpl. apply VSP.union_subset_4. 
  apply VSP.union_subset_5. auto.
Defined.

(** [live c L] returns the set of variables live "before" command [c],
  given the set [L] of variables live "after". *)

Definition live (c: com) (L: vset) : vset := proj1_sig (dlive c) L.

(** The [live] function satisfies the dataflow equations for liveness analysis,
  in particular: *)

Lemma live_while:
  forall b c L,
  vset_eq (live (CWhile b c) L)
         (vset_union (vset_union (fv_bexp b) L) (live c (live (CWhile b c) L))).
Proof.
  intros. unfold live. simpl. apply vset_fixpoint_correct.
Qed.

End VARS.




