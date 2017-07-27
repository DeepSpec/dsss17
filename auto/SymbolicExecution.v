Require Import Bool String Arith Omega List Coq.Program.Equality.
Require Import Maps Imp.
Require Import Sequences Semantics.


(* Fun with notations!  We want to write more natural-looking imperative programs. *)
Infix "+" := APlus : imp_scope.
Coercion ANum : nat >-> aexp.
Coercion Id : string >-> id.
Coercion AId : id >-> aexp.
Delimit Scope imp_scope with imp.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* Let's generate some big programs, to stress-test tactic performance when we try to
 * prove properties of the programs. *)
Fixpoint keepAdding (n : nat) : com :=
  match n with
  | O => SKIP
  | S n' => "x" ::= "x" + 1;; keepAdding n'
  end%imp.

Compute keepAdding 3.

(* These SF facts about maps will be helpful to ask Coq to apply automatically. *)
Hint Rewrite t_update_eq t_update_neq t_update_shadow using congruence.

(* Here's a general way to "run a program" in the operational semantics:
 * keep inverting [ceval] premises. *)
Ltac symexec := intros;
  repeat match goal with
         | [ H : ceval _ _ _ |- _ ] => invert H
         end; simpl; autorewrite with core.

(* We can prove that particular programs output the expected results. *)

Lemma keepAdding_3 : forall st st',
  ceval (keepAdding 3) st st' ->
  st' "x" = st "x" + 3.
Proof.
  symexec.
  omega.
Qed.

Lemma keepAdding_9 : forall st st',
  ceval (keepAdding 9) st st' ->
  st' "x" = st "x" + 9.
Proof.
  symexec.
  omega.
Qed.

(* Hey, that was pretty slow!  Can we do better? *)

(* What if we just simplify after every inversion? *)
Ltac symexec ::= intros;
  repeat match goal with
         | [ H : ceval _ _ _ |- _ ] => invert H; simpl in *; autorewrite with core in *
         end; simpl; autorewrite with core.

Lemma keepAdding_9' : forall st st',
  ceval (keepAdding 9) st st' ->
  st' "x" = st "x" + 9.
Proof.
  symexec.
  omega.
Qed.

(* OK, that's an improvement. *)

Lemma keepAdding_12 : forall st st',
  ceval (keepAdding 12) st st' ->
  st' "x" = st "x" + 12.
Proof.
  symexec.
  omega.
Qed.

(* Well, shucks.  That was still noticeably slow. *)


(** * A symbolic evaluator in Gallina *)

(* Let's put all our reasoning into one Gallina program that was can "just run"! *)

(* We maintain this state as we traverse program syntax.
 * The list associates each variable ([id]) with its value ([aexp]).
 * Crucial point: the variable values themselves only mention
 * *the initial values of variables*! *)
Definition symstate := list (id * aexp).

(* Look up the expression associated with a variable. *)
Fixpoint symget (syt : symstate) (x : id) : aexp :=
  match syt with
  | nil => x
    (* Default case: a variable equals itself.
     * We don't expect ever to run into this case! *)
  | (y, a) :: syt' =>
    if beq_id x y
    then a
    else symget syt' x
  end.

(* Remove a variable from a mapping. *)
Fixpoint symdel (syt : symstate) (x : id) : symstate :=
  match syt with
  | nil => nil
  | (y, a) :: syt' =>
    if beq_id x y
    then syt'
    else (y, a) :: symdel syt' x
  end.

(* Simplify an expression using your favorite arithmetic identities. *)
Fixpoint symsimp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus a1 a2 =>
    let a1' := symsimp a1 in
    let a2' := symsimp a2 in
    match a1', a2' with
    | APlus a11 (ANum n1), ANum n2 => APlus a11 (ANum (n1 + n2))
    | _, _ => APlus a1' a2'
    end
  | AMinus a1 a2 => AMinus (symsimp a1) (symsimp a2)
  | AMult a1 a2 => AMult (symsimp a1) (symsimp a2)
  end.

(* Update the value of a variable. *)
Definition symset (syt : symstate) (x : id) (a : aexp) : symstate :=
  (x, a) :: symdel syt x.

(* Plug variable values into an expression. *)
Fixpoint symaeval (syt : symstate) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => symget syt x
  | APlus a1 a2 => APlus (symaeval syt a1) (symaeval syt a2)
  | AMinus a1 a2 => AMinus (symaeval syt a1) (symaeval syt a2)
  | AMult a1 a2 => AMult (symaeval syt a1) (symaeval syt a2)
  end.

(* Plug variable values into a Boolean expression. *)
Fixpoint symbeval (syt : symstate) (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (symaeval syt a1) (symaeval syt a2)
  | BLe a1 a2 => BLe (symaeval syt a1) (symaeval syt a2)
  | BNot b1 => BNot (symbeval syt b1)
  | BAnd b1 b2 => BAnd (symbeval syt b1) (symbeval syt b2)
  end.

(* Convert a symbolic state into a concrete state, consulting another concrete
 * state for initial variable values. *)
Fixpoint symconc (st0 : state) (syt : symstate) : state :=
  match syt with
  | nil => st0
  | (x, a) :: syt' => t_update (symconc st0 syt') x (aeval st0 a)
  end.

(* Run a command symbolically to produce a list of all possible ending points.
 * [path] is a Boolean condition that is known to be true when we start execution.
 * Each result element combines a Boolean condition that will be true with a state. *)
Fixpoint symceval (st0 : state) (syt : symstate) (path : bexp) (c : com) : list (bexp * symstate) :=
  match c with
  | CSkip => (path, syt) :: nil
  | CAss x a => (path, symset syt x (symsimp (symaeval syt a))) :: nil
  | CSeq c1 c2 =>
    let after_c1 := symceval st0 syt path c1 in
    fold_left (fun l b_syt' => symceval st0 (snd b_syt') (fst b_syt') c2 ++ l)
              after_c1 nil
  | CIf b c1 c2 =>
    let b' := symbeval syt b in
    symceval st0 syt (BAnd path b') c1
    ++ symceval st0 syt (BAnd path (BNot b')) c2
  | _ => nil
  end.

(* It will be good to use this fact for case splitting on [id] equality. *)
Lemma id_eq_dec : forall x y : id, x = y \/ x <> y.
Proof.
  destruct x, y.
  destruct (string_dec s s0); tauto.
Qed.

Hint Rewrite <- beq_id_refl.
Hint Rewrite false_beq_id using congruence.

Ltac simp := intros; subst; repeat (autorewrite with core; simpl); auto.

Ltac beqer :=
  repeat match goal with
         | [ |- context[beq_id ?a ?b] ] => destruct (id_eq_dec a b); simp
         end.

(* How does [symconc] relate to expression evaluation? *)
Lemma symconc_aeval : forall st0 syt i,
    symconc st0 syt i = aeval st0 (symget syt i).
Proof.
  induction syt as [ | [ ] ]; simp.
  beqer.
Qed.

Hint Resolve symconc_aeval.

(* The fundamental correctness property of [symaeval] *)
Lemma symaeval_correct : forall st0 syt a,
    aeval (symconc st0 syt) a = aeval st0 (symaeval syt a).
Proof.
  induction a; simpl; intuition.
Qed.

Hint Resolve symaeval_correct.

(* Basic algebraic properties of symbolic states *)

Lemma symget_symset_eq : forall x a syt,
    symget (symset syt x a) x = a.
Proof.
  simp.
Qed.

Lemma symget_symset_neq' : forall x y syt,
    x <> y
    -> symget (symdel syt x) y = symget syt y.
Proof.
  induction syt as [ | [ ] ]; simp.
  beqer.
Qed.

Hint Resolve symget_symset_neq'.

Lemma symget_symset_neq : forall x y a,
    x <> y
    -> forall syt, symget (symset syt x a) y = symget syt y.
Proof.
  simp.
Qed.

Hint Rewrite symget_symset_eq symget_symset_neq using congruence.

Lemma symaeval_nil : forall a,
    symaeval nil a = a.
Proof.
  induction a; simpl; congruence.
Qed.

Hint Rewrite symaeval_nil.

(* Deleting a variable right before setting it has no effect. *)
Lemma symok_update' : forall x v st0 syt,
  t_update (symconc st0 syt) x v =
  t_update (symconc st0 (symdel syt x)) x v.
Proof.
  induction syt as [ | [ ] ]; simp.
  beqer.
  rewrite t_update_permute by congruence.
  rewrite IHsyt.
  apply t_update_permute.
  auto.
Qed.

Hint Resolve symok_update'.

Lemma symok_update : forall st0 x a syt,
    t_update (symconc st0 syt) x (aeval (symconc st0 syt) a) = symconc st0 (symset syt x (symaeval syt a)).
Proof.
  simp.
  rewrite symaeval_correct.
  auto.
Qed.

Hint Extern 1 (t_update _ _ _ = t_update _ _ _) => apply symok_update.
(* The goal might not match the form of the lemma statement exactly,
 * so we use a more permissive pattern. *)

Hint Extern 1 (_ /\ _) => progress simpl.

(* Interlude: a basic fact about lists *)
Lemma Exists_app : forall A (P : A -> Prop) ls1 ls2,
    Exists P ls1 \/ Exists P ls2
    -> Exists P (ls1 ++ ls2).
Proof.
  induction ls1; simpl; intuition;
    match goal with
    | [ H : Exists _ _ |- _ ] => invert H; eauto
    end.
Qed.

Hint Resolve Exists_app.

(* The fundamental correctness property for [symbeval] *)
Lemma symbeval_correct : forall st0 syt b,
    beval (symconc st0 syt) b = beval st0 (symbeval syt b).
Proof.
  induction b; simp; f_equal; auto.
Qed.

Hint Resolve symbeval_correct andb_true_intro.

(* Restated as a more useful hint *)
Lemma symbeval_correct_eq : forall st0 syt b v,
    beval (symconc st0 syt) b = v
    -> beval st0 (symbeval syt b) = v.
Proof.
  intros; subst; symmetry; eauto.
Qed.

Lemma symbeval_correct_neq : forall st0 syt b v,
    beval (symconc st0 syt) b = negb v
    -> negb (beval st0 (symbeval syt b)) = v.
Proof.
  intros; subst.
  erewrite <- symbeval_correct; eauto.
  rewrite H.
  apply negb_involutive.
Qed.

Hint Resolve symbeval_correct_eq symbeval_correct_neq.

Hint Extern 1 (beval _ _ = _) => progress simpl.

(* More general list properties *)
Lemma Exists_weaken : forall A (P1 P2 : A -> Prop) ls,
    Exists P1 ls
    -> (forall x, P1 x -> P2 x)
    -> Exists P2 ls.
Proof.
  induction 1; eauto.
Qed.

Lemma Exists_nested' : forall A B P (f : A -> list B) ls acc,
    Exists P acc
    -> Exists P (fold_left (fun l x => f x ++ l) ls acc).
Proof.
  induction ls; simpl; auto.
Qed.

Hint Resolve Exists_nested'.

Lemma Exists_nested : forall A B P (f : A -> list B) ls,
    Exists (fun x => Exists P (f x)) ls
    -> forall acc, Exists P (fold_left (fun l x => f x ++ l) ls acc).
Proof.
  induction 1; simpl; eauto.
Qed.

Hint Resolve Exists_nested.

Hint Extern 1 (Exists _ _) =>
  eapply Exists_weaken; [ match goal with
                          | [ H : _ |- _ ] => apply H
                          end | simpl; intuition idtac ].

(* The fundamental correctness property of [symsimp] *)
Lemma aeval_symsimp : forall st a,
    aeval st (symsimp a) = aeval st a.
Proof.
  induction a; simp;
    repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] => destruct E; simpl in *; try congruence
           end; omega.
Qed.

Hint Rewrite aeval_symsimp.

Hint Extern 1 (t_update _ _ _ = t_update _ _ _) => progress autorewrite with core.

(* Now for the fundamental correctness property of [symceval] *)

Lemma symceval_ok' : forall st0 st st' c,
    ceval c st st'
    -> no_whiles c = true
    -> forall syt p, st = symconc st0 syt
      -> beval st0 p = true
      -> Exists (fun b_syt' => beval st0 (fst b_syt') = true
                               /\ st' = symconc st0 (snd b_syt'))
                (symceval st0 syt p c).
Proof.
  induction 1; simpl; intros; subst; try discriminate;
    try match goal with
        | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H1; intuition
        end; eauto 8.
Qed.

Theorem symceval_ok : forall st st' c,
    ceval c st st'
    -> no_whiles c = true
    -> Exists (fun b_syt' => beval st (fst b_syt') = true
                             /\ st' = symconc st (snd b_syt'))
              (symceval st nil BTrue c).
Proof.
  intros; eapply symceval_ok'; eauto.
Qed.

(* The tactics to bring it all together *)

Ltac exister := repeat match goal with
                       | [ H : Exists _ nil |- _ ] => invert H
                       | [ H : Exists _ (_ :: _) |- _ ] => invert H
                       end.

Ltac symexec ::= intros;
  match goal with
  | [ H : ceval _ _ _ |- _ ] =>
    apply symceval_ok in H; [ | reflexivity ];
    match type of H with
    | Exists _ ?E =>
      let E' := eval vm_compute in E in
        change E with E' in H
    end; exister; simpl in *; intuition idtac; simp
  end.

Lemma keepAdding_3' : forall st st',
  ceval (keepAdding 3) st st' ->
  st' "x" = st "x" + 3.
Proof.
  symexec.
Qed.

Lemma keepAdding_9'' : forall st st',
  ceval (keepAdding 9) st st' ->
  st' "x" = st "x" + 9.
Proof.
  symexec.
Qed.

Lemma keepAdding_12' : forall st st',
  ceval (keepAdding 12) st st' ->
  st' "x" = st "x" + 12.
Proof.
  symexec.
Qed.


Lemma keepAdding_100 : forall st st',
  ceval (keepAdding 100) st st' ->
  st' "x" = st "x" + 100.
Proof.
  symexec.
Qed.

Lemma keepAdding_1000 : forall st st',
  ceval (keepAdding 1000) st st' ->
  st' "x" = st "x" + 1000.
Proof.
  symexec.
Qed.

(* That last one would have taken a *long* time with the purely Ltac-based implementation! *)

