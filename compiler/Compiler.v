Require Import Bool Arith Omega List Coq.Program.Equality.
Require Import Maps Imp.
Require Import Sequences Semantics.

(** This chapter defines a compiler from the Imp language to a virtual machine
  (a small subset of the Java Virtual Machine) and proves that this
  compiler preserves the semantics of the source programs. *)

(** * 1. The virtual machine. *)

(** The machine operates on a code [c] (a fixed list of instructions)
  and three variable components:
- a program counter, denoting a position in [c]
- a state assigning integer values to variables
- an evaluation stack, containing integers.
*)

(** The instruction set of the machine. *)

Inductive instruction: Type :=
  | Iconst(n: nat)                 (**r push integer [n] on stack *)
  | Ivar(x: id)                    (**r push the value of variable [x] *)
  | Isetvar(x: id)                 (**r pop an integer, assign it to variable [x] *)
  | Iadd                           (**r pop [n2], pop [n1], push back [n1+n2] *)
  | Isub                           (**r pop [n2], pop [n1], push back [n1-n2] *)
  | Imul                           (**r pop [n2], pop [n1], push back [n1*n2] *)
  | Ibranch_forward(ofs: nat)      (**r skip [ofs] instructions forward *)
  | Ibranch_backward(ofs: nat)     (**r skip [ofs] instructions backward *)
  | Ibeq(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1=n2] *)
  | Ibne(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<>n2] *)
  | Ible(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<=n2] *)
  | Ibgt(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1>n2] *)
  | Ihalt.                         (**r terminate execution successfully *)

Definition code := list instruction.

(** [code_at C pc = Some i] if [i] is the instruction at position [pc]
  in the list of instructions [C]. *)

Fixpoint code_at (C: code) (pc: nat) : option instruction :=
  match C, pc with
  | nil, _ => None
  | i :: C', O => Some i
  | i :: C', S pc' => code_at C' pc'
  end.

Definition stack := list nat.

(** The semantics of the virtual machine is given in small-step style,
  as a transition relation between machine configuration: triples
  (program counter, evaluation stack, variable state).
  The transition relation is parameterized by the code [c].
  There is one transition rule for each kind of instruction,
  except [Ihalt], which has no transition. *)

Definition configuration := (nat * stack * state)%type.

Inductive transition (C: code): configuration -> configuration -> Prop :=
  | trans_const: forall pc stk s n,
      code_at C pc = Some(Iconst n) ->
      transition C (pc, stk, s) (pc + 1, n :: stk, s)
  | trans_var: forall pc stk s x,
      code_at C pc = Some(Ivar x) ->
      transition C (pc, stk, s) (pc + 1, s x :: stk, s)
  | trans_setvar: forall pc stk s x n,
      code_at C pc = Some(Isetvar x) ->
      transition C (pc, n :: stk, s) (pc + 1, stk, t_update s x n)
  | trans_add: forall pc stk s n1 n2,
      code_at C pc = Some(Iadd) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 + n2) :: stk, s)
  | trans_sub: forall pc stk s n1 n2,
      code_at C pc = Some(Isub) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 - n2) :: stk, s)
  | trans_mul: forall pc stk s n1 n2,
      code_at C pc = Some(Imul) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 * n2) :: stk, s)
  | trans_branch_forward: forall pc stk s ofs pc',
      code_at C pc = Some(Ibranch_forward ofs) ->
      pc' = pc + 1 + ofs ->
      transition C (pc, stk, s) (pc', stk, s)
  | trans_branch_backward: forall pc stk s ofs pc',
      code_at C pc = Some(Ibranch_backward ofs) ->
      pc' = pc + 1 - ofs ->
      transition C (pc, stk, s) (pc', stk, s)
  | trans_beq: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibeq ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_bne: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibne ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_ble: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ible ofs) ->
      pc' = (if leb n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_bgt: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibgt ofs) ->
      pc' = (if leb n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s).

(** As usual with small-step semantics, we form sequences of machine transitions
  to define the behavior of a code.  We always start with [pc = 0]
  and an empty evaluation stack.  We stop successfully if [pc] points
  to an [Ihalt] instruction and the evaluation stack is empty.

  If [R] is a binary relation, [star R] is its reflexive transitive closure.
  (See file [Sequences] for the definition.)  [star (transition C)]
  therefore represents a sequence of  zero, one or several machine transitions.
*)

Definition mach_terminates (C: code) (s_init s_fin: state) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, nil, s_init) (pc, nil, s_fin).

(** Likewise, [infseq R] represents an infinite sequence of [R] transitions.
  (Also defined in file [Sequences].) *)

Definition mach_diverges (C: code) (s_init: state) :=
  infseq (transition C) (0, nil, s_init).

(** A third case can occur: after a finite number of transitions,
  the machine hits a configuration where it cannot make any transition,
  and this state is not a final configuration ([Ihalt] instruction and empty stack).
  In this case, we say that the machine "goes wrong", which is
  a politically-correct way of saying that our program just crashed. *)

Definition mach_goes_wrong (C: code) (s_init: state) :=
  exists pc, exists stk, exists s_fin,
  star (transition C) (0, nil, s_init) (pc, stk, s_fin)
  /\ irred (transition C) (pc, stk, s_fin)
  /\ (code_at C pc <> Some Ihalt \/ stk <> nil).

(** An important property of the virtual machine is that it is deterministic:
  from a given configuration, it can transition to at most one other configuration. *)

Lemma machine_deterministic:
  forall C config config1 config2,
  transition C config config1 -> transition C config config2 -> config1 = config2.
Proof.
  intros. inversion H; subst; inversion H0; try congruence.
  destruct (beq_nat n1 n2); congruence.
  destruct (beq_nat n1 n2); congruence.
  destruct (leb n1 n2); congruence.
  destruct (leb n1 n2); congruence.
Qed.

(** As a consequence of this determinism, it follows that
  the final state of a terminating program is unique,
  and that a program cannot both terminate and diverge,
  or terminate and go wrong, or diverge and go wrong.
  These results follow from the generic determinism properties 
  found at the end of module [Sequence]. *)

Remark stop_irred:
  forall C pc stk st,
  code_at C pc = Some Ihalt -> irred (transition C) (pc, stk, st).
Proof.
  unfold irred; intros. unfold not; intros. inversion H0; congruence.
Qed.

Lemma terminates_unique:
  forall C st st1 st2, mach_terminates C st st1 -> mach_terminates C st st2 -> st1 = st2.
Proof.
  unfold mach_terminates; intros. destruct H as (pc1 & A1 & B1), H0 as (pc2 & A2 & B2).
  assert (((pc1, nil, st1) : configuration) = ((pc2, nil, st2) : configuration)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred. }
  congruence. 
Qed.

Lemma terminates_goeswrong_exclusive:
  forall C st st', mach_terminates C st st' -> mach_goes_wrong C st -> False.
Proof.
  unfold mach_terminates, mach_goes_wrong; intros.
  destruct H as (pc1 & A1 & B1), H0 as (pc2 & stk2 & st2 & A2 & B2 & C2).
  assert (((pc1, nil, st') : configuration) = ((pc2, stk2, st2) : configuration)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred. }
  inversion H. subst pc2 stk2 st2. destruct C2; congruence.
Qed.

Lemma terminates_diverges_exclusive:
  forall C st st', mach_terminates C st st' -> mach_diverges C st -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros.
  destruct H as (pc1 & A1 & B1).
  eapply infseq_finseq_excl with (R := transition C); eauto using machine_deterministic, stop_irred.
Qed.

Lemma goeswrong_diverges_exclusive:
  forall C st, mach_goes_wrong C st -> mach_diverges C st -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros. 
  destruct H as (pc2 & stk2 & st2 & A2 & B2 & C2).
  eapply infseq_finseq_excl with (R := transition C); eauto using machine_deterministic, stop_irred.
Qed.

(** *** Exercise (2 stars, recommended). *)
(** To quickly see how a machine program executes, it is convenient
  to redefine the semantics of the machine as an executable function
  instead of inductively-defined relations.  This is similar to the
  [ceval_step] function from the [Imp] chapter of Software Foundations,
  which provides an executable interpreter for the Imp language.

  To ensure termination of the machine interpreter, we need to bound 
  the number of instructions it can execute.  The result of the
  machine interpreter, therefore, is of the following type:
*)

Inductive machine_result : Type :=
  | Timeout : machine_result              (**r the interpreter ran out of fuel *)
  | GoesWrong : machine_result            (**r the machine goes wrong on an impossible case *)
  | Terminates : state -> machine_result. (**r the machine successfully stops with the given state *)

(** Please fill in the blanks in the following definition for a machine interpreter: *)

Fixpoint mach_interp (C: code) (fuel: nat)
                     (pc: nat) (stk: stack) (st: state) : machine_result :=
  match fuel with
  | O => Timeout
  | S fuel' =>
      match code_at C pc, stk with
      | Some Ihalt, nil => Terminates st
      | Some (Iconst n), stk => mach_interp C fuel' (pc + 1) (n :: stk) st
      (* FILL IN HERE *)
      | _, _ => GoesWrong
      end
  end.

(** * 2. The compilation scheme *)

(** The code for an arithmetic expression [a]
- executes in sequence (no branches)
- deposits the value of [a] at the top of the stack
- preserves the variable state.

This is the familiar translation to "reverse Polish notation".
*)

Fixpoint compile_aexp (a: aexp) : code :=
  match a with
  | ANum n => Iconst n :: nil
  | AId v => Ivar v :: nil
  | APlus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Iadd :: nil
  | AMinus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Isub :: nil
  | AMult a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Imul :: nil
  end.

(** Some examples. *)

Notation vx := (Id "X").
Notation vy := (Id "Y").

Compute (compile_aexp (APlus (AId vx) (ANum 1))).

(** Result is: [ [Ivar vx, Iconst 1, Iadd] ] *)

Compute (compile_aexp (AMult (AId vy) (APlus (AId vx) (ANum 1)))).

(** Result is: [ [Ivar vy, Ivar vx, Iconst 1, Iadd, Imul] ] *)

(** The code [compile_bexp b cond ofs] for a boolean expression [b]
- skips forward the [ofs] following instructions if [b] evaluates to [cond] (a boolean)
- executes in sequence if [b] evaluates to the negation of [cond]
- leaves the stack and the variable state unchanged.

See slides for explanation of the mysterious branch offsets!
*)

Fixpoint compile_bexp (b: bexp) (cond: bool) (ofs: nat) : code :=
  match b with
  | BTrue =>
      if cond then Ibranch_forward ofs :: nil else nil
  | BFalse =>
      if cond then nil else Ibranch_forward ofs :: nil
  | BEq a1 a2 =>
      compile_aexp a1 ++ compile_aexp a2 ++
      (if cond then Ibeq ofs :: nil else Ibne ofs :: nil)
  | BLe a1 a2 =>
      compile_aexp a1 ++ compile_aexp a2 ++
      (if cond then Ible ofs :: nil else Ibgt ofs :: nil)
  | BNot b1 =>
      compile_bexp b1 (negb cond) ofs
  | BAnd b1 b2 =>
      let c2 := compile_bexp b2 cond ofs in
      let c1 := compile_bexp b1 false (if cond then length c2 else ofs + length c2) in
      c1 ++ c2
  end.

(** Examples. *)

Compute (compile_bexp (BEq (AId vx) (ANum 1)) true 42).

(** Result is: [ [Ivar vx, Iconst 1, Ibeq 42] ] *)

Compute (compile_bexp (BAnd (BLe (ANum 1) (AId vx)) (BLe (AId vx) (ANum 10))) false 42).

(** Result is: [ [Iconst 1, Ivar vx, Ibgt 45, Ivar vx, Iconst 10, Ibgt 42] ] *)

Compute (compile_bexp (BNot (BAnd BTrue BFalse)) true 42).

(** Result is: [ [Ibranch_forward 42] ] *)

(** The code for a command [c]
- updates the variable state as prescribed by [c]
- preserves the stack
- finishes on the next instruction immediately following the generated code.

Again, see slides for explanations of the generated branch offsets.
*)

Fixpoint compile_com (c: com) : code :=
  match c with
  | SKIP =>
      nil
  | (id ::= a) =>
      compile_aexp a ++ Isetvar id :: nil
  | (c1 ;; c2) =>
      compile_com c1 ++ compile_com c2
  | IFB b THEN ifso ELSE ifnot FI =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in
      compile_bexp b false (length code_ifso + 1)
      ++ code_ifso
      ++ Ibranch_forward (length code_ifnot)
      :: code_ifnot
  | WHILE b DO body END =>
      let code_body := compile_com body in
      let code_test := compile_bexp b false (length code_body + 1) in
      code_test
      ++ code_body
      ++ Ibranch_backward (length code_test + length code_body + 1)
      :: nil
  end.

(** The code for a program [p] (a command) is similar, but terminates
  cleanly on an [Ihalt] instruction. *)

Definition compile_program (p: com) : code :=
  compile_com p ++ Ihalt :: nil.

(** Examples of compilation: *)

Compute (compile_program (vx ::= APlus (AId vx) (ANum 1))).

(** Result is: [ [Ivar vx, Iconst 1, Iadd, Isetvar vx, Ihalt] ] *)

Compute (compile_program (WHILE BTrue DO SKIP END)).

(** Result is: [ [Ibranch_backward 1, Ihalt] ].  That's a tight loop indeed! *)

Compute (compile_program (IFB BEq (AId vx) (ANum 1) THEN vx ::= ANum 0 ELSE SKIP FI)).

(** Result is: [ [Ivar vx, Iconst 1, Ibne 3, Iconst 0, Isetvar vx, Ibranch_forward 0, Ihalt] ] *)

(** *** Exercise (1 star, recommended) *)
(** The last example shows a slight inefficiency in the code generated for
  [IFB ... THEN ... ELSE SKIP FI].  How would you change [compile_com]
  to generate better code?  Hint: ponder the following function. *)

Definition smart_Ibranch_forward (ofs: nat) : code :=
  if beq_nat ofs 0 then nil else Ibranch_forward(ofs) :: nil.

(** * 3. Semantic preservation *)

(** ** Auxiliary results about code sequences. *)

(** To reason about the execution of compiled code, we need to consider
  code sequences [C2] that are at position [pc] in a bigger code
  sequence [C = C1 ++ C2 ++ C3].  The following predicate
  [codeseq_at C pc C2] does just this. *)

Inductive codeseq_at: code -> nat -> code -> Prop :=
  | codeseq_at_intro: forall C1 C2 C3 pc,
      pc = length C1 ->
      codeseq_at (C1 ++ C2 ++ C3) pc C2.

(** We show a number of no-brainer lemmas about [code_at] and [codeseq_at],
  then populate a "hint database" so that Coq can use them automatically. *)

Lemma code_at_app:
  forall i c2 c1 pc,
  pc = length c1 ->
  code_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; simpl; intros; subst pc; auto.
Qed.

Lemma codeseq_at_head:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  code_at C pc = Some i.
Proof.
  intros. inversion H. simpl. apply code_at_app. auto.
Qed.

Lemma codeseq_at_tail:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  codeseq_at C (pc + 1) C'.
Proof.
  intros. inversion H. 
  change (C1 ++ (i :: C') ++ C3)
    with (C1 ++ (i :: nil) ++ C' ++ C3).
  rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed. 

Lemma codeseq_at_app_left:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C pc C1.
Proof.
  intros. inversion H. rewrite app_ass. constructor. auto.
Qed.

Lemma codeseq_at_app_right:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inversion H. rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed.

Lemma codeseq_at_app_right2:
  forall C pc C1 C2 C3,
  codeseq_at C pc (C1 ++ C2 ++ C3) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inversion H. repeat rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed.

Hint Resolve codeseq_at_head codeseq_at_tail codeseq_at_app_left codeseq_at_app_right codeseq_at_app_right2: codeseq.

Ltac normalize :=
  repeat rewrite app_length in *;
  repeat rewrite plus_assoc in *;
  repeat rewrite plus_0_r in *;
  simpl in *.

(** ** Correctness of generated code for expressions. *)

(** Remember the informal specification we gave for the code generated
  for an arithmetic expression [a].  It should
- execute in sequence (no branches)
- deposit the value of [a] at the top of the stack
- preserve the variable state.

We now prove that the code [compile_aexp a] fulfills this contract.
The proof is a nice induction on the structure of [a]. *)

Lemma compile_aexp_correct:
  forall C st a pc stk,
  codeseq_at C pc (compile_aexp a) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_aexp a), aeval st a :: stk, st).
Proof.
  induction a; simpl; intros.

- (* ANum *)
  apply star_one. apply trans_const. eauto with codeseq. 

- (* AId *)
  apply star_one. apply trans_var. eauto with codeseq. 

- (* APlus *)
  eapply star_trans.
  apply IHa1. eauto with codeseq. 
  eapply star_trans.
  apply IHa2. eauto with codeseq. 
  apply star_one. normalize. apply trans_add. eauto with codeseq. 

- (* AMinus *)
  eapply star_trans.
  apply IHa1. eauto with codeseq. 
  eapply star_trans.
  apply IHa2. eauto with codeseq. 
  apply star_one. normalize. apply trans_sub. eauto with codeseq. 

- (* AMult *)
  eapply star_trans.
  apply IHa1. eauto with codeseq. 
  eapply star_trans.
  apply IHa2. eauto with codeseq. 
  apply star_one. normalize. apply trans_mul. eauto with codeseq. 
Qed.

(** Here is a similar proof for the compilation of boolean expressions. *)

Lemma compile_bexp_correct:
  forall C st b cond ofs pc stk,
  codeseq_at C pc (compile_bexp b cond ofs) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_bexp b cond ofs) + if eqb (beval st b) cond then ofs else 0, stk, st).
Proof.
  induction b; simpl; intros.

- (* BTrue *)
  destruct cond; simpl.
  + (* BTrue, true *)
    apply star_one. apply trans_branch_forward with ofs. eauto with codeseq. auto.
  + (* BTrue, false *)
    repeat rewrite plus_0_r. apply star_refl.
 
- (* BFalse *)
  destruct cond; simpl.
  + (* BFalse, true *)
    repeat rewrite plus_0_r. apply star_refl.
  + (* BFalse, false *)
    apply star_one. apply trans_branch_forward with ofs. eauto with codeseq. auto.

- (* BEq *)
  eapply star_trans. 
  apply compile_aexp_correct with (a := a). eauto with codeseq. 
  eapply star_trans.
  apply compile_aexp_correct with (a := a0). eauto with codeseq. 
  apply star_one. normalize.
  destruct cond.
  + (* BEq, true *)
    apply trans_beq with ofs. eauto with codeseq.
    destruct (beq_nat (aeval st a) (aeval st a0)); simpl; omega.
  + (* BEq, false *)
    apply trans_bne with ofs. eauto with codeseq. 
    destruct (beq_nat (aeval st a) (aeval st a0)); simpl; omega.

- (* BLe *)
  eapply star_trans. 
  apply compile_aexp_correct with (a := a). eauto with codeseq. 
  eapply star_trans.
  apply compile_aexp_correct with (a := a0). eauto with codeseq. 
  apply star_one. normalize.
  destruct cond.
  + (* BLe, true *)
    apply trans_ble with ofs. eauto with codeseq.
    destruct (leb (aeval st a) (aeval st a0)); simpl; omega.
  + (* BLe, false *)
    apply trans_bgt with ofs. eauto with codeseq. 
    destruct (leb (aeval st a) (aeval st a0)); simpl; omega.

- (* BNot *)
  replace (eqb (negb (beval st b)) cond)
     with (eqb (beval st b) (negb cond)).
  apply IHb; auto. 
  destruct (beval st b); destruct cond; auto.

- (* BAnd *)
  set (code_b2 := compile_bexp b2 cond ofs) in *.
  set (ofs' := if cond then length code_b2 else ofs + length code_b2) in *.
  set (code_b1 := compile_bexp b1 false ofs') in *.
  apply star_trans with (pc + length code_b1 + (if eqb (beval st b1) false then ofs' else 0), stk, st).
  apply IHb1. eauto with codeseq.
  destruct cond.
  + (* BAnd, true *)
    destruct (beval st b1); simpl.
    * (* b1 evaluates to true *)
      normalize. apply IHb2. eauto with codeseq. 
    * (* b1 evaluates to false *)
      normalize. apply star_refl.
  + (* BAnd, false *)
    destruct (beval st b1); simpl.
    * (* b1 evaluates to true *)
      normalize. apply IHb2. eauto with codeseq. 
    * (* b1 evaluates to false *)
      replace ofs' with (length code_b2 + ofs). normalize. apply star_refl.
      unfold ofs'; omega.
Qed.

(** ** Correctness of generated code for commands: terminating case. *)

Lemma compile_com_correct_terminating:
  forall C st c st',
  c / st \\ st' ->
  forall stk pc,
  codeseq_at C pc (compile_com c) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_com c), stk, st').
Proof.
  induction 1; intros stk pc AT.

- (* SKIP *)
  simpl in *. rewrite plus_0_r. apply star_refl.

- (* := *)
  simpl in *. subst n.
  eapply star_trans. apply compile_aexp_correct. eauto with codeseq.
  apply star_one. normalize. apply trans_setvar. eauto with codeseq. 

- (* sequence *)
  simpl in *.
  eapply star_trans. apply IHceval1. eauto with codeseq. 
  normalize. apply IHceval2. eauto with codeseq. 

- (* if true *)
  simpl in *.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  eapply star_trans. 
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq. 
  rewrite H. simpl. rewrite plus_0_r. fold codeb. normalize.
  eapply star_trans. apply IHceval. eauto with codeseq. 
  apply star_one. eapply trans_branch_forward. eauto with codeseq. omega.

- (* if false *)
  simpl in *.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  eapply star_trans. 
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq. 
  rewrite H. simpl. fold codeb. normalize.
  replace (pc + length codeb + length code1 + S(length code2))
     with (pc + length codeb + length code1 + 1 + length code2).
  apply IHceval. eauto with codeseq. omega. 

- (* while false *)
  simpl in *. 
  eapply star_trans.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length (compile_com c) + 1). 
  eauto with codeseq.
  rewrite H. simpl. normalize. apply star_refl.

- (* while true *)
  apply star_trans with (pc, stk, st').
  simpl in *.
  eapply star_trans.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length (compile_com c) + 1). 
  eauto with codeseq. 
  rewrite H; simpl. rewrite plus_0_r.
  eapply star_trans. apply IHceval1. eauto with codeseq. 
  apply star_one.
  eapply trans_branch_backward. eauto with codeseq. omega.
  apply IHceval2. auto.
Qed.

Theorem compile_program_correct_terminating:
  forall c st st',
  c / st \\ st' ->
  mach_terminates (compile_program c) st st'.
Proof.
  intros. unfold compile_program. red.
  exists (length (compile_com c)); split.
  apply code_at_app. auto.
  apply compile_com_correct_terminating with (pc := 0). auto. 
  apply codeseq_at_intro with (C1 := nil). auto.
Qed.


(** *** Exercise (2 stars, recommended) *)
(** The previous exercise in this chapter suggested to use
  [smart_Ibranch_forward] to avoid generating useless "branch forward"
  instructions when compiling [IFB ... THEN ... ELSE SKIP FI] commands.
  Once you have modified [compile_com] to use [smart_Ibranch_forward],
  adapt the proof of [compile_com_correct_terminating] accordingly.
  The following lemma will come handy: *)

Lemma trans_smart_branch_forward:
  forall C ofs pc stk st,
  codeseq_at C pc (smart_Ibranch_forward ofs) ->
  star (transition C) (pc, stk, st) (pc + length (smart_Ibranch_forward ofs) + ofs, stk, st).
Proof.
  unfold smart_Ibranch_forward; intros.
  (* FILL IN HERE *)
Admitted.

(** *** Exercise (3 stars, optional) *)
(** The manufacturer of our virtual machine offers a cheaper variant
  that lacks the [Ibge] and [Ibgt] conditional branches.  The only
  conditional branches available are [Ibeq] (branch if equal) and 
  [Ibne] (branch if different).  Modify the definition of [compile_bexp] and
  its correctness proof to target this cheaper virtual machine.
  Hint: study Coq's definition of subtraction between natural numbers
  (do [Print Nat.sub]). *)

(** ** Correctness of generated code for commands: general case. *)

(** We would like to strengthen the correctness result above so that it
  is not restricted to terminating source programs, but also applies to
  source program that diverge.  To this end, we abandon the big-step
  semantics for commands and switch to the small-step semantics with continuations.
  We then show a simulation theorem, establishing that every transition
  of the small-step semantics in the source program is simulated (in a sense
  to be made precise below) by zero, one or several transitions of the
  machine executing the compiled code for the source program. *)

(** Our first task is to relate configurations [(c, k, st)] of the small-step
  semantics with configurations [(C, pc, stk, st)] of the machine.
  We already know how to relate a command [c] with the machine code,
  using the [codeseq_at] predicate.  What needs to be defined is a relation
  between the continuation [k] and the machine code.

  Intuitively, when the machine finishes executing the generated code for
  command [c], that is, when it reaches the program point
  [pc + length(compile_com c)], the machine should continue by executing
  instructions that perform the pending computations described by
  continuation [k], then reach an [Ihalt] instruction to stop cleanly.

  We formalize this intution by the following inductive predicate
  [compile_cont C k pc], which states that, starting at program point [pc],
  there are instructions that perform the computations described in [k]
  and reach an [Ihalt] instruction. *)

Inductive compile_cont (C: code): cont -> nat -> Prop :=
  | ccont_stop: forall pc,
      code_at C pc = Some Ihalt ->
      compile_cont C Kstop pc
  | ccont_seq: forall c k pc pc',
      codeseq_at C pc (compile_com c) ->
      pc' = pc + length (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (Kseq c k) pc
  | ccont_while: forall b c k pc ofs pc' pc'',
      code_at C pc = Some(Ibranch_backward ofs) ->
      pc' = pc + 1 - ofs ->
      codeseq_at C pc' (compile_com (WHILE b DO c END)) ->
      pc'' = pc' + length (compile_com (WHILE b DO c END)) ->
      compile_cont C k pc'' ->
      compile_cont C (Kwhile b c k) pc
  | ccont_branch: forall ofs k pc pc',
      code_at C pc = Some(Ibranch_forward ofs) ->
      pc' = pc + 1 + ofs ->
      compile_cont C k pc' ->
      compile_cont C k pc.

(** Then, a configuration [(c,k,st)] of the small-step semantics matches
  a configuration [(C, pc, stk, st')] of the machine if the following conditions hold:
- The memory states are identical: [st' = st].
- The machine stack is empty: [stk = nil].
- The machine code at point [pc] is the compiled code for [c]:
  [codeseq_at C pc (compile_com c)].
- The machine code at point [pc + length (compile_com c)] matches continuation
  [k], in the sense of [compile_cont] above.
*)

Inductive match_config (C: code): com * cont * state -> configuration -> Prop :=
  | match_config_intro: forall c k st pc,
      codeseq_at C pc (compile_com c) ->
      compile_cont C k (pc + length (compile_com c)) ->
      match_config C (c, k, st) (pc, nil, st).

(** We are now ready to prove the expected simulation property.  Our first
  attempt is to show a diagram of the following form:
<<
                      match_config
     c / k / st  ----------------------- machstate
       |                                   |
       |                                   | *
       |                                   |
       v                                   v
    c' / k' / st' ----------------------- machstate'
                      match_config 
>>
Hypotheses:
- Left: one transition in the small-step continuation semantics for Imp.
- Top: the [match_config] invariant.

Conclusions:
- Bottom: the [match_config] invariant, which must be preserved.
- Right: zero, one or several transitions of the virtual machine.

Why "zero, one, or several"?  Some transitions of the Imp semantics involve
the evaluation of a complex expression, which requires several machine instructions
to be executed.  However, other transitions of the Imp semantics, such as
the [KS_Seq] and [KS_SkipSeq] rules, just change the focus on a sub-command,
but the machine need not execute any instruction to reflect this change of focus.
*)

Lemma simulation_step_first_attempt:
  forall C impstate1 impstate2 machstate1,
  kstep impstate1 impstate2 ->
  match_config C impstate1 machstate1 ->
  exists machstate2,
      star (transition C) machstate1 machstate2
   /\ match_config C impstate2 machstate2.
Proof.
Abort.

(** This simulation lemma is true and can be proved, but it is too weak to
  imply the preservation of diverging behaviors: we have an issue with
  "infinite stuttering".  Imagine a situation where the source program
  takes infinitely many transitions, but every such transition is matched
  by zero transitions of the virtual machine.  In this case, the source
  program diverges, but the machine code can do anything: it can diverge,
  as expected, but it can also terminate cleanly or go wrong. 
  The simulation lemma above is too weak to rule out the last two cases!

  We therefore need a stronger simulation result that rules out stuttering.
  To this end, we are going to require that if a source transition is
  matched by zero machine transition, some nonnegative measure of the source
  configuration must strictly decrease.  This ensures that only a finite
  number of stuttering steps can be taken before the machine actually does
  a transition.  Here is the revised simulation diagram:
 
<<
                      match_config
     c / k / st  ----------------------- machconfig
       |                                   |
       |                                   | + or ( * and |c',k'| < |c,k} )
       |                                   |
       v                                   v
    c' / k' / st' ----------------------- machconfig'
                      match_config 
>>
Note the stronger conclusion on the right:
- either the virtual machine does one or several transitions
- or it does zero, one or several transitions, but the size of the [c,k]
  pair decreases strictly.

It would be equivalent to state:
- either the virtual machine does one or several transitions
- or it does zero transitions, but the size of the [c,k] pair decreases strictly.

However, the formulation above, with the "star" case, is often more convenient.
*)

(** Finding an appropriate "anti-stuttering" measure is a bit of a black art.
After trial and error, we find that the following measure works.  It is
the sum of the sizes of the command [c] under focus and all the commands
appearing in the continuation [k]. *)

Fixpoint com_size (c: com) : nat :=
  match c with
  | SKIP => 1
  | x ::= a => 1
  | (c1 ;; c2) => com_size c1 + com_size c2 + 1
  | IFB b THEN ifso ELSE ifnot FI => com_size ifso + com_size ifnot + 1
  | WHILE b DO c1 END => com_size c1 + 1
  end.

Remark com_size_nonzero: forall c, com_size c > 0. 
Proof.
  induction c; simpl; omega.
Qed.

Fixpoint cont_size (k: cont) : nat :=
  match k with
  | Kstop => 0
  | Kseq c k' => com_size c + cont_size k'
  | Kwhile b c k' => cont_size k'
  end.

Definition measure (impconf: com * cont * state) : nat :=
  match impconf with (c, k, m) => com_size c + cont_size k end.

(** A few technical lemmas to help with the simulation proof. *)

Lemma compile_cont_Kstop_inv:
  forall C pc m,
  compile_cont C Kstop pc ->
  exists pc',
  star (transition C) (pc, nil, m) (pc', nil, m)
  /\ code_at C pc' = Some Ihalt.
Proof.
  intros. dependent induction H. 
- exists pc; split. apply star_refl. auto.
- destruct IHcompile_cont as [pc'' [A B]]; auto.
  exists pc''; split; auto. eapply star_step; eauto. eapply trans_branch_forward; eauto. 
Qed.

Lemma compile_cont_Kseq_inv:
  forall C c k pc m,
  compile_cont C (Kseq c k) pc ->
  exists pc',
  star (transition C) (pc, nil, m) (pc', nil, m)
  /\ codeseq_at C pc' (compile_com c)
  /\ compile_cont C k (pc' + length(compile_com c)).
Proof.
  intros. dependent induction H. 
  exists pc; split. apply star_refl. split; congruence. 
  destruct (IHcompile_cont _ _ eq_refl) as [pc'' [A [B D]]].
  exists pc''; split; auto. eapply star_step; eauto. eapply trans_branch_forward; eauto. 
Qed.

Lemma compile_cont_Kwhile_inv:
  forall C b c k pc m,
  compile_cont C (Kwhile b c k) pc ->
  exists pc',
  plus (transition C) (pc, nil, m) (pc', nil, m)
  /\ codeseq_at C pc' (compile_com (WHILE b DO c END))
  /\ compile_cont C k (pc' + length(compile_com (WHILE b DO c END))).
Proof.
  intros. dependent induction H.
- exists (pc + 1 - ofs); split.
  apply plus_one. eapply trans_branch_backward; eauto. 
  split; congruence.
- destruct (IHcompile_cont _ _ _ (refl_equal _)) as [pc'' [A [B D]]].
  exists pc''; split; auto. eapply plus_left. eapply trans_branch_forward; eauto. apply plus_star; auto. 
Qed.

Remark code_at_inv:
  forall C pc i, code_at C pc = Some i -> exists C1, exists C2, C = C1 ++ C2 /\ length C1 = pc.
Proof.
  induction C; simpl; intros.
  inversion H.
  destruct pc. inversion H. exists (@nil instruction); exists (i :: C); auto. 
  destruct (IHC _ _ H) as [C1 [C2 [A B]]].
  exists (a :: C1); exists C2; split. simpl; congruence. simpl; congruence.
Qed.

Remark code_at_codeseq:
  forall C pc i, code_at C pc = Some i -> codeseq_at C pc nil.
Proof.
  intros. destruct (code_at_inv _ _ _ H) as [C1 [C2 [A B]]]. 
  subst. change C2 with (nil ++ C2). constructor. auto.
Qed.

Lemma match_config_skip:
  forall C k m pc,
  compile_cont C k pc ->
  match_config C (SKIP, k, m) (pc, nil, m).
Proof.
  intros C.
  assert (forall k pc, compile_cont C k pc -> codeseq_at C pc nil).
    induction 1.
    eapply code_at_codeseq; eauto.
    change (compile_com c) with (nil ++ compile_com c) in H. eauto with codeseq.
    eapply code_at_codeseq; eauto.
    eapply code_at_codeseq; eauto.
  intros. constructor. simpl. eauto. simpl. rewrite plus_0_r; auto.
Qed.

(** At long last, we can state and prove the right simulation diagram. *)

Lemma simulation_step:
  forall C impstate1 impstate2 machstate1,
  kstep impstate1 impstate2 ->
  match_config C impstate1 machstate1 ->
  exists machstate2,
      (plus (transition C) machstate1 machstate2
       \/ (star (transition C) machstate1 machstate2 /\ measure impstate2 < measure impstate1))
   /\ match_config C impstate2 machstate2.
Proof.
  intros until machstate1; intros KSTEP MATCH. 
  inversion KSTEP; clear KSTEP; subst; inversion MATCH; clear MATCH; subst; simpl in *.

- (* assign *)
  econstructor; split.
  left. eapply plus_right. eapply compile_aexp_correct; eauto with codeseq. 
  eapply trans_setvar; eauto with codeseq. 
  normalize. apply match_config_skip. auto.

- (* seq *)
  econstructor; split.
  right; split. apply star_refl. omega. 
  normalize. constructor. eauto with codeseq. eapply ccont_seq; eauto with codeseq. 

- (* if true *)
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq.
  omega.
  rewrite H; simpl. fold codeb. normalize. constructor; eauto with codeseq. 
  eapply ccont_branch; eauto with codeseq. 
  change (S (length code2)) with (1 + length code2) in H5. normalize. auto.

- (* if false *)
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq.
  omega.
  rewrite H; simpl. fold codeb. normalize. constructor; eauto with codeseq. 
  change (S (length code2)) with (1 + length code2) in H5. normalize. auto.

- (* while true *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b false (length codec + 1)) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length codec + 1).
  eauto with codeseq.
  omega.
  rewrite H; simpl. fold codeb. normalize. constructor; eauto with codeseq.
  fold codec.
  assert (PC: pc + length codeb + length codec + 1 - (length codeb + length codec + 1) = pc)
      by omega.
  eapply ccont_while; eauto with codeseq. rewrite PC; auto. rewrite PC.
  simpl. normalize. auto.

- (* while false *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b false (length codec + 1)) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length codec + 1).
  eauto with codeseq.
  generalize (com_size_nonzero c). omega. 
  rewrite H; simpl. fold codeb. normalize. apply match_config_skip. auto. 

- (* skip seq *)
  normalize.
  destruct (compile_cont_Kseq_inv _ _ _ _ st H4) as [pc' [X [Y Z]]].
  econstructor; split.
  right; split. eexact X. omega.
  constructor; auto. 

- (* skip while *)
  normalize.
  destruct (compile_cont_Kwhile_inv _ _ _ _ _ st H4) as [pc' [X [Y Z]]].
  econstructor; split.
  left. eexact X. 
  constructor; auto.
Qed.

(** Simulation diagrams such as [simulation_step] above imply semantic preservation
  for terminating programs and for diverging programs.  We now develop a generic
  proof of this fact that we can reuse later for other program transformations. *)

Section SIMULATION_DIAGRAM.

(** The generic proof is parameterized over the small-step semantics for the
  source and target languages, and over an invariant between their states. *)

Variable state1: Type.	     (**r the type of configurations for the source language *)
Variable step1: state1 -> state1 -> Prop.   (**r the small-step semantics for the source language *)

Variable state2: Type.	     (**r the type of configurations for the target language *)
Variable step2: state2 -> state2 -> Prop.   (**r the small-step semantics for the target language *)

Variable match_states: state1 -> state2 -> Prop.  (**r the invariant *)

Variable measure: state1 -> nat.                  (**r the anti-stuttering measure *)

Hypothesis simulation:
  forall S1 S1' S2,
  step1 S1 S1' -> match_states S1 S2 ->
  exists S2',
    (plus step2 S2 S2' \/ (star step2 S2 S2' /\ measure S1' < measure S1))
  /\ match_states S1' S2'.

(** We first extend the simulation to finite sequences of source transitions.
  This will show semantic preservation for terminating programs. *)

Lemma simulation_star:
  forall S1 S1', star step1 S1 S1' ->
  forall S2, match_states S1 S2 ->
  exists S2', star step2 S2 S2' /\ match_states S1' S2'.
Proof.
  induction 1; intros.
- (* zero transition *)
  exists S2; split. apply star_refl. auto.
- (* one or more transitions *)
  destruct (simulation _ _ _ H H1) as [S2' [P Q]].
  destruct (IHstar _ Q) as [S2'' [U V]].
  exists S2''; split. 
  eapply star_trans; eauto. destruct P. apply plus_star; auto. destruct H2; auto.
  auto.
Qed.

(** Turning to infinite sequences, we first show that the target program
  can always make progress, while preserving the [match_states] relation,
  if the source diverges.  The proof is an induction on the maximal number
  [N] of stutterings the target can make before performing at least one transition. *)

Lemma simulation_infseq_productive:
  forall N S1 S2,
  measure S1 < N ->
  infseq step1 S1 ->
  match_states S1 S2 ->
  exists S1', exists S2',
      plus step2 S2 S2'
   /\ infseq step1 S1'
   /\ match_states S1' S2'.
Proof.
  induction N; intros. 
- (* N = 0 *)
  exfalso. omega.
- (* N > 0 *)
  inversion H0; clear H0; subst.
  destruct (simulation _ _ _ H2 H1) as [S2' [P Q]].
  destruct P.
  + (* one or several transitions *)
    exists b; exists S2'; auto.
  + (* zero, one or several transitions *)
    destruct H0. inversion H0; clear H0; subst.
    * (* zero transitions *)
      eapply IHN; eauto. omega.
    * (* one or several transitions *)
      exists b; exists S2'; split. eapply plus_left; eauto. auto.
Qed.

(** It follows that the target performs infinitely many transitions if
  started in a configuration that matches a diverging source configuration. *)

Lemma simulation_infseq:
  forall S1 S2,
  infseq step1 S1 ->
  match_states S1 S2 ->
  infseq step2 S2.
Proof.
  intros. 
  apply infseq_coinduction_principle_2 with
    (X := fun S2 => exists S1, infseq step1 S1 /\ match_states S1 S2).
  intros. destruct H1 as [S [A B]]. 
  destruct (simulation_infseq_productive (measure S + 1) S a) 
  as [S1' [S2' [P [Q R]]]].
  omega. auto. auto.
  exists S2'; split. auto. exists S1'; auto. 
  exists S1; auto.
Qed.

End SIMULATION_DIAGRAM.

(** We now apply these results to the Imp compiler.  We first obtain
  an alternate proof of semantic preservation for terminating Imp programs. *)

Lemma match_config_initial:
  forall c st,
  match_config (compile_program c) (c, Kstop, st) (0, nil, st).
Proof.
  intros. constructor.
  change (compile_program c) with (nil ++ compile_com c ++ Ihalt :: nil). constructor. auto.
  simpl. unfold compile_program. constructor. apply code_at_app. auto.
Qed.

Theorem compile_program_correct_terminating_2:
  forall c st st',
  kterminates c st st' ->
  mach_terminates (compile_program c) st st'.
Proof.
  intros.
  assert (exists machconf2, 
           star (transition (compile_program c)) (0, nil, st) machconf2
           /\ match_config (compile_program c) (SKIP, Kstop, st') machconf2).
  eapply simulation_star; eauto. eapply simulation_step. apply match_config_initial.
  destruct H0 as [machconf2 [STAR MS]]. 
  inversion MS; subst. simpl in *. normalize. 
  destruct (compile_cont_Kstop_inv _ _ st' H5) as [pc' [A B]].
  red. exists pc'; split. auto. eapply star_trans; eauto.
Qed.

(** More interestingly, we also prove semantic preservation for diverging
  Imp programs. *)

Theorem compile_program_correct_diverging:
  forall c st,
  kdiverges c st ->
  mach_diverges (compile_program c) st.
Proof.
  intros; red; intros. 
  eapply simulation_infseq with (match_states := match_config (compile_program c)); eauto.
  eapply simulation_step. apply match_config_initial.
Qed.

(** *** Mini-project (4 stars) *)

(** Our compiler for arithmetic expressions implements a left-to-right
  evaluation order: in [a1 + a2], [a1] is evaluated first, and its value
  left on the stack; then [a2] is evaluated; then an [Iadd] instruction
  is performed.  For commutative operators like [+] and [*], we
  could just as well evaluate [a2] first, then [a1], then combine
  their results.  

  This can help producing more efficient code in terms of how much
  stack space is required by the evaluation.  Consider the expression
  [1 + (2 + (3 + ... (N-1 + N)))].  With left-to-right evaluation,
  it uses [N+1] stack entries.  With right-to-left evaluation,
  it uses only 2 stack entries.  

  In this exercise, we explore the effect of different evaluation orders
  on stack usage.  Let us first parameterize [compile_aexp] with
  a heuristic function [ord] that, given the two arguments of a [+]
  or [*] operator, decides whether to evaluate them left-to-right
  or right-to-left: *)

Inductive eval_order : Type := LtoR | RtoL.

Fixpoint compile_aexp_gen (ord: aexp -> aexp -> eval_order) (a: aexp) : code :=
  match a with
  | ANum n => Iconst n :: nil
  | AId v => Ivar v :: nil
  | APlus a1 a2 =>
      match ord a1 a2 with
      | LtoR => compile_aexp_gen ord a1 ++ compile_aexp_gen ord a2 ++ Iadd :: nil
      | RtoL => compile_aexp_gen ord a2 ++ compile_aexp_gen ord a1 ++ Iadd :: nil
      end
  | AMinus a1 a2 =>
      compile_aexp_gen ord a1 ++ compile_aexp_gen ord a2 ++ Isub :: nil
  | AMult a1 a2 =>
      match ord a1 a2 with
      | LtoR => compile_aexp_gen ord a1 ++ compile_aexp_gen ord a2 ++ Imul :: nil
      | RtoL => compile_aexp_gen ord a2 ++ compile_aexp_gen ord a1 ++ Imul :: nil
      end
  end.

(** First show that, whatever the [ord] heuristic is, the code generated
by [compile_aexp_gen ord] is correct.  This is a simple extension of
the proof of [compile_aexp_correct]. *)

Lemma compile_aexp_gen_correct:
  forall ord C st a pc stk,
  codeseq_at C pc (compile_aexp_gen ord a) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_aexp_gen ord a), aeval st a :: stk, st).
Proof.
  induction a; simpl; intros.
  (* FILL IN HERE *)
Admitted.

(** Now, let us try to compute the minimum number of stack entries
  needed to evaluate an expression, regardless of the strategy used. *)

Require Import Min Max.     (**r Libraries of lemmas about min and max *)

Fixpoint stack_needs (a: aexp) : nat :=
  match a with
  | ANum n => 1
  | AId v => 1
  | APlus a1 a2 =>
      let n1 := stack_needs a1 in
      let n2 := stack_needs a2 in
      min (max n1 (n2 + 1)) (max n2 (n1 + 1))
  | AMinus a1 a2 =>
      let n1 := stack_needs a1 in
      let n2 := stack_needs a2 in
      max n1 (n2 + 1)
  | AMult a1 a2 =>
      let n1 := stack_needs a1 in
      let n2 := stack_needs a2 in
      min (max n1 (n2 + 1)) (max n2 (n1 + 1))
  end.

(** This definition is a variation on the Strahler numbering of a tree.
  Here are some intuitions.  Consider [APlus a1 a2].  If we
  evaluate [a1] then [a2], we will need at least [stack_needs a1]
  space for evaluating [a1], then [stack_needs a2 + 1] for [a2]:
  plus one, because during the evaluation of [a2], the value of [a1]
  sits in the stack.  So, our space usage is the max of these two
  quantities.  But we can also choose the other evaluation order,
  so our space usage is the min of the two max corresponding to the
  two possible evaluation orders. *)

(** To show that [stack_needs] is the minimal stack size required,
  we can define the stack usage (number of stack entries needed) of
  a given strategy [ord], the show that it is at least [stack_needs]. *)

Fixpoint stack_usage (ord: aexp -> aexp -> eval_order) (a: aexp) : nat :=
  match a with
  | ANum n => 1
  | AId v => 1
  | APlus a1 a2 =>
      match ord a1 a2 with
      | LtoR => max (stack_usage ord a1) (stack_usage ord a2 + 1)
      | RtoL => max (stack_usage ord a2) (stack_usage ord a1 + 1)
      end
  | AMinus a1 a2 =>
      max (stack_usage ord a1) (stack_usage ord a2 + 1)
  | AMult a1 a2 =>
      match ord a1 a2 with
      | LtoR => max (stack_usage ord a1) (stack_usage ord a2 + 1)
      | RtoL => max (stack_usage ord a2) (stack_usage ord a1 + 1)
      end
  end.

Lemma stack_needs_is_optimal:
  forall ord a, stack_needs a <= stack_usage ord a.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Useful tip: the tactic [zify; omega] works very well to prove
    arithmetic properties involving min and max operators. *)

(** An optimal strategy (with respect to stack usage) is to always
  compute the biggest subexpression first: *)

Definition optimal_ord (a1 a2: aexp) :=
  if leb (stack_needs a2) (stack_needs a1) then LtoR else RtoL.

Definition compile_aexp_optimal (a: aexp) : code :=
  compile_aexp_gen optimal_ord a.

(** The intuition is simple: if one of the arguments, say [a1], has
  stack needs strictly less than the other, say [a2], evaluating [a1]
  after [a2], with [a2]'s value as additional entry on the stack,
  will use no more stack space than evaluating [a2].  So, evaluating
  [a1 + a2] can be done with no extra space than evaluating just [a2].
  This would not be the case if we started with [a1], then evaluated [a2]:
  in this case, one more stack slot would be needed. 

  If both arguments have the same stack needs, the two evaluation
  orders use exactly the same amount of space, so it does not matter
  which one we choose. *)

(** We can show the optimality of the strategy by observing that 
  its stack usage is the minimum predicted by [stack_needs]. *)

Lemma stack_usage_optimal_ord:
  forall a, stack_usage optimal_ord a = stack_needs a.
Proof.
  (* FILL IN HERE *)
Admitted.  

(** So far, we've reasoned informally on the stack usage of a particular
  evaluation strategy.  Now, let us formally connect this reasoning with the
  execution of the compiled code.  First, we need to instrument the
  virtual machine so that it monitors its stack usage and goes wrong
  if the stack size goes over a given maximum [maxstack]. *)

Inductive checked_transition (C: code) (maxstack: nat) : configuration -> configuration -> Prop :=
  | ctrans: forall pc stk s pc' stk' s',
      transition C (pc, stk, s) (pc', stk', s') ->
      length stk' <= maxstack ->
      checked_transition C maxstack (pc, stk, s) (pc', stk', s').

(** Now, we can state and prove the fact that the compiled code for
  expression [a] with respect to a strategy [ord] execute safely
  if at least [stack_usage ord a] stack entries are available. *)

Lemma compile_aexp_gen_safe:
  forall ord C maxstack st a pc stk,
  codeseq_at C pc (compile_aexp_gen ord a) ->
  length stk + stack_usage ord a <= maxstack ->
  star (checked_transition C maxstack)
       (pc, stk, st)
       (pc + length (compile_aexp_gen ord a), aeval st a :: stk, st).
Proof.
  induction a; simpl; intros.
Admitted.

(** Moreover, the size [stack_usage ord a] is tight, in that there exists
  a point in the execution of the compiled code for [a] where the stack
  is at least that big. *)

Lemma stack_usage_reached:
  forall ord C st a pc stk,
  codeseq_at C pc (compile_aexp_gen ord a) ->
  exists pc', exists stk',
  star (transition C) (pc, stk, st) (pc', stk', st)
  /\ length stk' >= length stk + stack_usage ord a.
Proof.
  induction a; simpl; intros.
  (* FILL IN HERE *)
Admitted.

(** **** Full project (5 stars) *)

Module StorelessMachine.

(** The purpose of this project is to retarget the IMP compiler to a
  different, simpler virtual machine that has no store, just a stack
  that also supports direct accesses, i.e. reading or modifying the
  N-th entry of the stack.  Here is the instruction set of the machine:
*)

Inductive instruction: Type :=
  | Iconst(n: nat)                 (**r push integer [n] on stack *)
  | Iget(n: nat)                   (**r push the value of the [n]-th stack slot *)
  | Iset(n: nat)                   (**r pop an integer, assign it to the [n]-th stack slot *)
  | Iadd                           (**r pop [n2], pop [n1], push back [n1+n2] *)
  | Isub                           (**r pop [n2], pop [n1], push back [n1-n2] *)
  | Imul                           (**r pop [n2], pop [n1], push back [n1*n2] *)
  | Ibranch_forward(ofs: nat)      (**r skip [ofs] instructions forward *)
  | Ibranch_backward(ofs: nat)     (**r skip [ofs] instructions backward *)
  | Ibeq(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1=n2] *)
  | Ibne(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<>n2] *)
  | Ible(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<=n2] *)
  | Ibgt(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1>n2] *)
  | Ihalt.                         (**r terminate execution successfully *)

(** The only difference with the original virtual machine is that the
  [Ivar] and [Isetvar] instructions (to access the store by
  identifier) are gone and replaced by [Iget] and [Iset] instructions
  (to access the stack by position). *)

Definition code := list instruction.
Definition stack := list nat.
Definition configuration := (nat * stack)%type.

Fixpoint code_at (C: code) (pc: nat) : option instruction :=
  match C, pc with
  | nil, _ => None
  | i :: C', O => Some i
  | i :: C', S pc' => code_at C' pc'
  end.

(** To give semantics to the [Iget] and [Iset] instructions, start by
  defining two stack-manipulating functions, such that
<<
     get_nth_slot (v0 :: ... :: vN :: ...) N = Some vN
     set_nth_slot (v0 :: ... :: vN :: ...) N v' = Some (v0 :: ... :: v' :: ...)
>>
*)

Definition get_nth_slot (s: stack) (n: nat) : option nat :=
  None. (* FILL HERE *)

Fixpoint set_nth_slot (s: stack) (n: nat) (v: nat) : option stack :=
  None. (* FILL HERE *)

(** Then, the semantics of the machine is given by the following transition
  relation.  Note that machine states are just pairs of a program counter
  and a stack.  Note also that many transitions are exactly those of
  the original machine after erasing the store component of the state. *)

Inductive transition (C: code): configuration -> configuration -> Prop :=
  | trans_const: forall pc stk n,
      code_at C pc = Some(Iconst n) ->
      transition C (pc, stk) (pc + 1, n :: stk)
  | trans_get: forall pc stk n v,
      code_at C pc = Some(Iget n) ->
      get_nth_slot stk n = Some v ->
      transition C (pc, stk) (pc + 1, v :: stk)
  | trans_set: forall pc stk n v stk',
      code_at C pc = Some(Iset n) ->
      set_nth_slot stk n v = Some stk' ->
      transition C (pc, v :: stk) (pc + 1, stk')
  | trans_add: forall pc stk n1 n2,
      code_at C pc = Some(Iadd) ->
      transition C (pc, n2 :: n1 :: stk) (pc + 1, (n1 + n2) :: stk)
  | trans_sub: forall pc stk n1 n2,
      code_at C pc = Some(Isub) ->
      transition C (pc, n2 :: n1 :: stk) (pc + 1, (n1 - n2) :: stk)
  | trans_mul: forall pc stk n1 n2,
      code_at C pc = Some(Imul) ->
      transition C (pc, n2 :: n1 :: stk) (pc + 1, (n1 * n2) :: stk)
  | trans_branch_forward: forall pc stk ofs pc',
      code_at C pc = Some(Ibranch_forward ofs) ->
      pc' = pc + 1 + ofs ->
      transition C (pc, stk) (pc', stk)
  | trans_branch_backward: forall pc stk ofs pc',
      code_at C pc = Some(Ibranch_backward ofs) ->
      pc' = pc + 1 - ofs ->
      transition C (pc, stk) (pc', stk)
  | trans_beq: forall pc stk ofs n1 n2 pc',
      code_at C pc = Some(Ibeq ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk) (pc', stk)
  | trans_bne: forall pc stk ofs n1 n2 pc',
      code_at C pc = Some(Ibne ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk) (pc', stk)
  | trans_ble: forall pc stk ofs n1 n2 pc',
      code_at C pc = Some(Ible ofs) ->
      pc' = (if leb n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk) (pc', stk)
  | trans_bgt: forall pc stk ofs n1 n2 pc',
      code_at C pc = Some(Ibgt ofs) ->
      pc' = (if leb n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk) (pc', stk).

Definition mach_terminates (C: code) (stk_init stk_fin: stack) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, stk_init) (pc, stk_fin).

(** Now it's your turn: define a compilation scheme from IMP programs
    to machine code and prove its correctness w.r.t. terminating executions,
    as stated below. *)

Definition compile_program (c: com) : code := nil. (* FILL HERE *)

Theorem compile_program_correct_terminating:
  forall c st,
  c / empty_state \\ st ->
  exists stk,
     mach_terminates (compile_program c) nil stk
  /\ True.
Proof.
  (* Have fun! *)
Admitted.

(** The [True] above is to be replaced by some informative relation between
  the final stack [stk] and the final store [st]. *)

(** Some hints to get you started.  Clearly, we need to use a portion of
  the stack to hold the current values for the program variables.  It may
  seem impossible to represent a store (a function from identifiers to values,
  giving gives values to infinitely many variables) as a stack (a finite
  list of values).  However, only the variables that are ever assigned to
  within the program need to be associated with a stack slot: all
  other variables keep their initial value of 0 throughout the program
  execution. *)

(**  Hence, the first order of business is to construct a list of
  variables that are ever assigned in the program, and, from this
  list, to assign a position in the stack for every such variable.
  For example, if the list of assigned variables is [["x";"y";"z"]]
  we could say that the value of ["x"] is at the top of the stack,
  the value of ["y"] one slot below, and that of ["z"] two slots below.
  Those offsets need adjusting during the evaluation of expressions,
  because intermediate results are pushed on the stack on top of the
  values of variables. *)

(**  Using this information, the compilation of an expression [AId id] is
  either [Iconst 0] if the variable is not assigned in the program,
  or, [Iget N] otherwise, for a stack distance [N] that reflects the
  stack position of variable [id]. *)

(** To state and prove semantic preservation for the compilation functions,
  you will need a predicate [agree st stk] that relates an IMP store [st]
  with a machine stack [stk].  Typically, it will say that
- [st x = 0] for all non-assigned variables [x]
- [get_nth_slot stk N = Some (st x)] if [N] is the stack offset for variable [x]

  The predicate [agree st stk] acts both as a pre- and a post-condition, e.g.

<<
Lemma compile_com_correct_terminating:
  forall C st c st',
  c / st \\ st' ->
  forall stk pc,
  codeseq_at C pc (compile_com c) ->
  agree st stk ->
  exists stk',
     star (transition C) (pc, stk) (pc + length (compile_com c), stk')
  /\ agree st' stk'.
>>
*)

End StorelessMachine.
