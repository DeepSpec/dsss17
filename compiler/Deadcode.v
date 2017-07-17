Require Import Bool Arith Omega List Coq.Program.Equality.
Require Import MSets.
Require Import Maps Imp.
Require Import Sequences Semantics.

(** In this chapter: liveness analysis and its use for an optimization
  called dead code elimination. *)

(** * 1. Sets of variables *)

(** The static analysis we need -- liveness analysis -- operates over
  sets of variables.  Coq's standard library provides a rich, efficient
  implementation of finite sets.  Before being able to use it, however,
  we must provide it with a Coq module equipping the type of identifiers
  with a decidable equality.  The implementation of this module follows. *)

Module Id_Decidable <: DecidableType with Definition t := id.
  Definition t := id.
  Definition eq (x y: t) := x = y.
  Lemma eq_equiv: Equivalence eq.
  Proof.
    constructor; red; unfold eq; intros; congruence.
  Qed.
  Definition eq_dec: forall (x y: t), {eq x y} + {~eq x y}.
  Proof.
    intros. destruct  (beq_id x y) eqn:BEQ.
  - left; apply beq_id_true_iff; auto.
  - right; apply beq_id_false_iff; auto.
  Defined.
End Id_Decidable.

(** We then instantiate the finite sets modules from Coq's standard library
  with this ordered type of integers. *)

Module VS := MSetWeakList.Make(Id_Decidable).
Module VSP := MSetProperties.WProperties(VS).
Module VSdecide := MSetDecide.Decide(VS).
Import VSdecide.

(** * 2. Liveness analysis *)

(** ** Free variables *)

(** Computation of the set of variables appearing in an expression or command. *)

Fixpoint fv_aexp (a: aexp) : VS.t :=
  match a with
  | ANum n => VS.empty
  | AId v => VS.singleton v
  | APlus a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  | AMinus a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  | AMult a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  end.

Fixpoint fv_bexp (b: bexp) : VS.t :=
  match b with
  | BTrue => VS.empty
  | BFalse => VS.empty
  | BEq a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  | BLe a1 a2 => VS.union (fv_aexp a1) (fv_aexp a2)
  | BNot b1 => fv_bexp b1
  | BAnd b1 b2 => VS.union (fv_bexp b1) (fv_bexp b2)
  end.

Fixpoint fv_com (c: com) : VS.t :=
  match c with
  | SKIP => VS.empty
  | x ::= a => fv_aexp a
  | (c1 ;; c2) => VS.union (fv_com c1) (fv_com c2)
  | IFB b THEN c1 ELSE c2 FI => VS.union (fv_bexp b) (VS.union (fv_com c1) (fv_com c2))
  | WHILE b DO c END => VS.union (fv_bexp b) (fv_com c)
  end.

(** ** Computing post-fixpoints. *)

Section FIXPOINT.

Variable F: VS.t -> VS.t.
Variable default: VS.t.

(** Our goal is to find a set of variables [x] such that [F x] is a subset of [x]
  (a post-fixpoint of F).  We use a naive algorithm: iterate [F] at most [n] times,
  stopping as soon as a post-fixpoint is encountered.  If not,
  we return a safe default result. *)

Fixpoint iter (n: nat) (x: VS.t) : VS.t :=
  match n with
  | O => default
  | S n' =>
      let x' := F x in
      if VS.subset x' x then x else iter n' x'
  end.

Definition niter := 10%nat.

Definition fixpoint : VS.t := iter niter VS.empty.

Lemma fixpoint_charact:
  VS.Subset (F fixpoint) fixpoint \/ fixpoint = default.
Proof.
  unfold fixpoint. generalize niter, VS.empty. induction n; intros; simpl.
- auto.
- destruct (VS.subset (F t) t) eqn:SUBSET.
+ left. apply VS.subset_spec; auto.
+ apply IHn.
Qed.

Hypothesis F_stable:
  forall x, VS.Subset x default -> VS.Subset (F x) default.

Lemma fixpoint_upper_bound:
  VS.Subset fixpoint default.
Proof.
  assert (forall n x, VS.Subset x default -> VS.Subset (iter n x) default).
  { induction n; intros; simpl.
  - red; auto.
  - destruct (VS.subset (F x) x) eqn:SUBSET.
    + auto.
    + apply IHn; auto.
  }
  unfold fixpoint. apply H. apply VSP.subset_empty.
Qed.

End FIXPOINT.

(** ** Liveness analysis. *)

(** [L] is the set of variables live "after" command [c].
  The result of [live c L] is the set of variables live "before" [c]. *)

Fixpoint live (c: com) (L: VS.t) : VS.t :=
  match c with
  | SKIP => L
  | x ::= a =>
      if VS.mem x L
      then VS.union (VS.remove x L) (fv_aexp a)
      else L
  | (c1 ;; c2) =>
      live c1 (live c2 L)
  | IFB b THEN c1 ELSE c2 FI =>
      VS.union (fv_bexp b) (VS.union (live c1 L) (live c2 L))
  | WHILE b DO c END =>
      let L' := VS.union (fv_bexp b) L in
      let default := VS.union (fv_com (CWhile b c)) L in
      fixpoint (fun x => VS.union L' (live c x)) default
  end.

Lemma live_upper_bound:
  forall c L,
  VS.Subset (live c L) (VS.union (fv_com c) L).
Proof.
  induction c; intros; simpl.
- fsetdec.
- destruct (VS.mem i L) eqn:MEM. fsetdec. fsetdec.
- specialize (IHc1 (live c2 L)). specialize (IHc2 L). fsetdec.
- specialize (IHc1 L). specialize (IHc2 L). fsetdec.
- apply fixpoint_upper_bound. intro x. specialize (IHc x). fsetdec.
Qed.

Lemma live_while_charact:
  forall b c L,
  let L' := live (WHILE b DO c END) L in
  VS.Subset (fv_bexp b) L' /\ VS.Subset L L' /\ VS.Subset (live c L') L'.
Proof.
  intros.
  specialize (fixpoint_charact
    (fun x : VS.t => VS.union (VS.union (fv_bexp b) L) (live c x))
          (VS.union (VS.union (fv_bexp b) (fv_com c)) L)).
  simpl in L'. fold L'. intros [A|A].
- split. fsetdec. split; fsetdec.
- split. rewrite A. fsetdec.
  split. rewrite A. fsetdec.
  eapply VSP.subset_trans. apply live_upper_bound. rewrite A. fsetdec.
Qed.

(** * 3. Dead code elimination *)

(** ** Code transformation *)

(** The code transformation turns assignments [x ::= a] to dead variables [x]
  into [SKIP] statements. *)

Fixpoint dce (c: com) (L: VS.t): com :=
  match c with
  | SKIP => SKIP
  | x ::= a => if VS.mem x L then x ::= a else SKIP
  | (c1 ;; c2) => (dce c1 (live c2 L) ;; dce c2 L)
  | IFB b THEN c1 ELSE c2 FI => IFB b THEN dce c1 L ELSE dce c2 L FI
  | WHILE b DO c END => WHILE b DO dce c (live (WHILE b DO c END) L) END
  end.

(** Example of optimization. *)

Notation va := (Id "a").
Notation vb := (Id "b").
Notation vq := (Id "q").
Notation vr := (Id "r").

Definition prog :=
  ( vr ::= AId va ;;
    vq ::= ANum 0 ;;
    WHILE BLe (AId vb) (AId vr) DO
      vr ::= AMinus (AId vr) (AId vb) ;;
      vq ::= APlus (AId vq) (ANum 1)
    END ).

Compute (dce prog (VS.singleton vr)).

(** Result is:
<<
   r := a;                 ===>   r := a;
   q := 0;                        skip;
   while b <= r do                while b <= r do
     r := r - b;                    r := r - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

Compute (dce prog (VS.singleton vq)).

(** Program is unchanged. *)

(** ** Semantic correctness *)

(** Two states agree on a set [L] of live variables if they assign
  the same values to each live variable. *)

Definition agree (L: VS.t) (s1 s2: state) : Prop :=
  forall x, VS.In x L -> s1 x = s2 x.

(** Monotonicity property. *)

Lemma agree_mon:
  forall L L' s1 s2,
  agree L' s1 s2 -> VS.Subset L L' -> agree L s1 s2.
Proof.
  unfold VS.Subset, agree; intros. auto.
Qed.

(** Agreement on the free variables of an expression implies that this
    expression evaluates identically in both states. *)

Lemma aeval_agree:
  forall L s1 s2, agree L s1 s2 ->
  forall a, VS.Subset (fv_aexp a) L -> aeval s1 a = aeval s2 a.
Proof.
  induction a; simpl; intros.
- auto.
- apply H. fsetdec.
- f_equal. apply IHa1. fsetdec. apply IHa2. fsetdec.
- f_equal. apply IHa1. fsetdec. apply IHa2. fsetdec.
- f_equal. apply IHa1. fsetdec. apply IHa2. fsetdec.
Qed.

Lemma beval_agree:
  forall L s1 s2, agree L s1 s2 ->
  forall b, VS.Subset (fv_bexp b) L -> beval s1 b = beval s2 b.
Proof.
  induction b; simpl; intros.
- auto.
- auto.
- repeat rewrite (aeval_agree L s1 s2); auto; fsetdec.
- repeat rewrite (aeval_agree L s1 s2); auto; fsetdec.
- f_equal; apply IHb; auto.
- f_equal. apply IHb1; fsetdec. apply IHb2; fsetdec.
Qed.

(** Agreement is preserved by simultaneous assignment to a live variable. *)

Lemma agree_update_live:
  forall s1 s2 L x v,
  agree (VS.remove x L) s1 s2 ->
  agree L (t_update s1 x v) (t_update s2 x v).
Proof.
  intros; red; intros. unfold t_update. destruct (beq_id x x0) eqn:BEQ.
- auto.
- apply H. apply VS.remove_spec. split; auto. apply sym_not_equal. apply beq_id_false_iff. auto.
Qed.

(** Agreement is also preserved by unilateral assignment to a dead variable. *)

Lemma agree_update_dead:
  forall s1 s2 L x v,
  agree L s1 s2 -> ~VS.In x L ->
  agree L (t_update s1 x v) s2.
Proof.
  intros; red; intros. unfold t_update. destruct (beq_id x x0) eqn:BEQ.
- apply beq_id_true_iff in BEQ. subst x0. contradiction.
- apply H; auto.
Qed.

(** We now show that dead code elimination preserves semantics for terminating
  source program.  We use big-step semantics to show the following diagram:
<<
                agree (live c L) st st1
     c / st ----------------------------- dce C L / st1
       |                                          |
       |                                          |
       |                                          |
       v                                          v
      st' -------------------------------------- st1'
                    agree L st' st1'
>>
  The proof is a simple induction on the big-step evaluation derivation on the left. *)

Theorem dce_correct_terminating:
  forall st c st', c / st \\ st' ->
  forall L st1,
  agree (live c L) st st1 ->
  exists st1', dce c L / st1 \\ st1' /\ agree L st' st1'.
Proof.
  induction 1; intros; simpl.

- (* skip *)
  exists st1; split. constructor. auto.

- (* := *)
  simpl in H0. destruct (VS.mem x L) eqn:LIVE_AFTER.
  + (* x is live after *)
    assert (aeval st1 a1 = n).
    { rewrite <- H. symmetry. eapply aeval_agree. eauto. fsetdec. }
    exists (t_update st1 x n); split.
    apply E_Ass. auto.
    apply agree_update_live. eapply agree_mon. eauto. fsetdec.
  + (* x is dead after *)
    exists st1; split.
    apply E_Skip.
    apply agree_update_dead. auto.
    rewrite <- VS.mem_spec. congruence.

- (* seq *)
  simpl in H1.
  destruct (IHceval1 _ _ H1) as [st1' [E1 A1]].
  destruct (IHceval2 _ _ A1) as [st2' [E2 A2]].
  exists st2'; split.
  apply E_Seq with st1'; auto.
  auto.

- (* if true *)
  simpl in H1.
  assert (beval st1 b = true).
  { rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec. }
  destruct (IHceval L st1) as [st1' [E A]].
    eapply agree_mon; eauto. fsetdec.
  exists st1'; split.
  apply E_IfTrue; auto.
  auto.

- (* if false *)
  simpl in H1.
  assert (beval st1 b = false).
  { rewrite <- H. symmetry. eapply beval_agree; eauto. fsetdec. }
  destruct (IHceval L st1) as [st1' [E A]].
    eapply agree_mon; eauto. fsetdec.
  exists st1'; split.
  apply E_IfFalse; auto.
  auto.

- (* while end *)
  destruct (live_while_charact b c L) as [P [Q R]].
  assert (beval st1 b = false).
  { rewrite <- H. symmetry. eapply beval_agree; eauto. }
  exists st1; split.
  apply E_WhileFalse. auto.
  eapply agree_mon; eauto.

- (* while loop *)
  destruct (live_while_charact b c L) as [P [Q R]].
  assert (beval st1 b = true).
  { rewrite <- H. symmetry. eapply beval_agree; eauto. }
  destruct (IHceval1 (live (WHILE b DO c END) L) st1) as [st2 [E1 A1]].
    eapply agree_mon; eauto.
  destruct (IHceval2 L st2) as [st3 [E2 A2]].
    auto.
  exists st3; split.
  apply E_WhileTrue with st2; auto.
  auto.
Qed.


(** *** Exercise (3 stars, optional) *)

(** To prove semantic preservation both for terminating and diverging programs.
  complete the following simulation proof, which uses the small-step semantics
  of Imp, without continuations. *)

Fixpoint measure (c: com) : nat :=
  match c with
  | (x ::= a) => 1
  | (c1 ;; c2) => measure c1
  | _ => 0
  end.

Theorem dce_simulation:
  forall c st c' st',
  c / st ==> c' / st' ->
  forall L st1,
  agree (live c L) st st1 ->
  (exists st1',
   dce c L / st1 ==> dce c' L / st1' /\
   agree (live c' L) st' st1')
  \/
  (measure c' < measure c /\ dce c L = dce c' L /\ agree (live c' L) st' st1).
Proof.
   intros until st'. intro STEP. dependent induction STEP; simpl; intros.
  (* FILL IN HERE *)
Admitted.
