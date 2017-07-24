(* Copied and modified from Xavier Leroy's lectures. *)

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

Notation stack := (list nat).

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

Hint Extern 1 (transition _ _ _) => eapply trans_const.
Hint Extern 1 (transition _ _ _) => eapply trans_var.
Hint Extern 1 (transition _ _ _) => eapply trans_setvar.
Hint Extern 1 (transition _ _ _) => eapply trans_add.
Hint Extern 1 (transition _ _ _) => eapply trans_sub.
Hint Extern 1 (transition _ _ _) => eapply trans_mul.
Hint Extern 1 (transition _ _ _) => eapply trans_branch_forward.
Hint Extern 1 (transition _ _ _) => eapply trans_branch_backward.

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

Ltac inverter1 ::=
  match goal with
  | [ H : transition _ _ _ |- _ ] =>
    (invert H; congruence)
    || (invert H; try congruence; [])
    || (invert H; try congruence; [|])
  end; simpl in *; eauto.

Lemma machine_deterministic:
  forall C config config1 config2,
  transition C config config1 -> transition C config config2 -> config1 = config2.
Proof.
  intros; invert H; inverter;
    match goal with
    | [ |- context[if ?E then _ else _] ] => destruct E; congruence
    end.
Qed.

(** As a consequence of this determinism, it follows that
  the final state of a terminating program is unique,
  and that a program cannot both terminate and diverge,
  or terminate and go wrong, or diverge and go wrong.
  These results follow from the generic determinism properties 
  found at the end of module [Sequence]. *)

Hint Resolve machine_deterministic.

Remark stop_irred:
  forall C pc stk st,
  code_at C pc = Some Ihalt -> irred (transition C) (pc, stk, st).
Proof.
  unfold irred; intuition; inverter.
Qed.

Ltac det :=
  match goal with
  | [ H1 : star _ ?x _, H2 : star _ ?x _ |- _ ] =>
    eapply finseq_unique in H1; try apply H2; try congruence; eauto;
      unfold irred; intuition; inverter
  end.

Lemma terminates_unique:
  forall C st st1 st2, mach_terminates C st st1 -> mach_terminates C st st2 -> st1 = st2.
Proof.
  unfold mach_terminates; firstorder; det.
Qed.

Lemma terminates_goeswrong_exclusive:
  forall C st st', mach_terminates C st st' -> mach_goes_wrong C st -> False.
Proof.
  unfold mach_terminates; firstorder; det.
Qed.

Hint Resolve infseq_finseq_excl stop_irred.

Lemma terminates_diverges_exclusive:
  forall C st st', mach_terminates C st st' -> mach_diverges C st -> False.
Proof.
  unfold mach_terminates; firstorder; eauto.
Qed.

Lemma goeswrong_diverges_exclusive:
  forall C st, mach_goes_wrong C st -> mach_diverges C st -> False.
Proof.
  unfold mach_goes_wrong; firstorder; eauto.
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

Hint Resolve codeseq_at_head codeseq_at_tail codeseq_at_app_left codeseq_at_app_right codeseq_at_app_right2.

Hint Rewrite app_length plus_assoc plus_0_r.

Ltac normalize := do 2 (autorewrite with core in *; simpl in *).

(** ** Correctness of generated code for expressions. *)

(** Remember the informal specification we gave for the code generated
  for an arithmetic expression [a].  It should
- execute in sequence (no branches)
- deposit the value of [a] at the top of the stack
- preserve the variable state.

We now prove that the code [compile_aexp a] fulfills this contract.
The proof is a nice induction on the structure of [a]. *)

Hint Extern 1 (star (transition _) _ _) =>
  match goal with
  | [ H : forall pc stk, codeseq_at _ pc _ -> _ |- _ ] =>
    eapply star_trans; [ apply H; solve [ eauto ] |]
  end.
(* General transitivity makes the proof-search space explode,
 * but hints like this one are safer. *)

Lemma compile_aexp_correct:
  forall C st a pc stk,
  codeseq_at C pc (compile_aexp a) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_aexp a), aeval st a :: stk, st).
Proof.
  induction a; simpl; intros; normalize; eauto 15.
Qed.

(** Here is a similar proof for the compilation of boolean expressions. *)

Hint Extern 1 (@eq nat _ _) => omega.

Hint Extern 1 (star _ _ _) => eapply star_trans; [ eapply compile_aexp_correct; solve [ eauto ] | ].

Lemma rearrange_final : forall C y q q' e f,
    star (transition C) y (q', e, f) ->
    q' = q ->
    star (transition C) y (q, e, f).
Proof.
  intros; subst; auto.
Qed.

Hint Extern 1 (star _ _ _) => eapply rearrange_final; [ eassumption | omega ].

Ltac fwd1 :=
  match goal with
  | [ |- context[if ?E then _ else _] ] =>
    match E with
    | eqb ?E' _ => case_eq E'
    | _ => case_eq E
    end; simpl; intros; auto
  | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; simpl in *
  | [ H : negb _ = true |- _ ] => apply negb_true_iff in H
  | [ H : negb _ = false |- _ ] => apply negb_false_iff in H
  | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H; destruct H
  | [ H : ?A && ?B = false |- _ ] =>
    let H1 := fresh in let H2 := fresh in
      case_eq A; case_eq B; intros H1 H2; rewrite H1, H2 in H; discriminate || clear H
  | [ IH : forall a b, codeseq_at _ _ _ -> _, H : codeseq_at _ _ _ |- _ ] =>
    specialize (fun a => IH a _ H)
  | [ H : codeseq_at _ _ (_ ++ _) |- _ ] =>
    specialize (codeseq_at_app_left _ _ _ _ H);
    specialize (codeseq_at_app_right _ _ _ _ H);
    clear H; intros
  | [ H : codeseq_at _ _ (_ :: _) |- _ ] =>
    specialize (codeseq_at_head _ _ _ _ H);
    specialize (codeseq_at_tail _ _ _ _ H);
    clear H; intros
  end.

Ltac fwd := repeat fwd1; subst; normalize; try discriminate.

Ltac use_eq :=
  match goal with
  | [ H : ?X = _ |- context[?X] ] => rewrite H; normalize
  end.

Ltac jump_step rule :=
  econstructor; [ eapply rule; [ eassumption | reflexivity ]
                | use_eq ].

Hint Extern 1 (star (transition _) _ _) => jump_step trans_beq.
Hint Extern 1 (star (transition _) _ _) => jump_step trans_bne.
Hint Extern 1 (star (transition _) _ _) => jump_step trans_ble.
Hint Extern 1 (star (transition _) _ _) => jump_step trans_bgt.

Hint Extern 1 (star (transition _) _ _) =>
  match goal with
  | [ H : forall cond ofs pc stk, codeseq_at _ pc _ -> _ |- _ ] =>
    eapply star_trans; [ apply H; solve [ eauto ] | use_eq ]
  end.

Lemma done_omega : forall C pc stk st pc',
    pc = pc' ->
    star (transition C) (pc, stk, st) (pc', stk, st).
Proof.
  intros; subst; eauto.
Qed.

Hint Resolve done_omega.

Lemma compile_bexp_correct:
  forall C st b cond ofs pc stk,
  codeseq_at C pc (compile_bexp b cond ofs) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_bexp b cond ofs) + if eqb (beval st b) cond then ofs else 0, stk, st).
Proof.
  induction b; simpl; intros; normalize; fwd; eauto.
Qed.

Lemma star_match_hyp : forall C pc' stk st x pc,
    star (transition C) (pc', stk, st) x ->
    pc' = pc ->
    star (transition C) (pc, stk, st) x.
Proof.
  congruence.
Qed.

Hint Extern 1 (star _ _ _) =>
  match goal with
  | [ H : _ |- _ ] =>
    eapply star_match_hyp; [ solve [ apply H ] | omega ]
  end.

(** ** Correctness of generated code for commands: terminating case. *)

Hint Extern 1 (star _ _ _) =>
  eapply star_trans; [ apply compile_bexp_correct; solve [ eauto ] | use_eq ].

Hint Extern 1 (star (transition _) (?pc, _, _) _) =>
  match goal with
  | [ H : forall stk, star (transition _) (pc, stk, _) _ |- _ ] =>
    eapply star_trans; [ apply H | ]
  end.

Hint Extern 1 (star (transition _) (?pc, _, _) _) =>
  match goal with
  | [ H : forall stk pc, codeseq_at _ _ _ -> _ |- _ ] =>
    eapply star_trans; [ apply H; solve [ eauto ] | ]
  end.

Lemma compile_com_correct_terminating:
  forall C st c st',
  c / st \\ st' ->
  forall stk pc,
  codeseq_at C pc (compile_com c) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_com c), stk, st').
Proof.
  induction 1; intros; subst; normalize; fwd; eauto 8.
Qed.

Lemma codeseq_start : forall ls ls',
    codeseq_at (ls ++ ls') 0 ls.
Proof.
  intros.
  change (ls ++ ls') with (nil ++ ls ++ ls').
  constructor; auto.
Qed.

Hint Resolve code_at_app codeseq_start.

Lemma compile_com_correct_terminating0:
  forall C st c st',
  c / st \\ st' ->
  forall stk,
  codeseq_at C 0 (compile_com c) ->
  star (transition C)
       (0, stk, st)
       (length (compile_com c), stk, st').
Proof.
  intros.
  eapply compile_com_correct_terminating in H0; eauto.
Qed.

Hint Resolve compile_com_correct_terminating0.

Theorem compile_program_correct_terminating:
  forall c st st',
  c / st \\ st' ->
  mach_terminates (compile_program c) st st'.
Proof.
  unfold compile_program, mach_terminates.
  eauto.
Qed.


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
  intros; dependent induction H; firstorder eauto.
Qed.

Lemma compile_cont_Kseq_inv:
  forall C c k pc m,
  compile_cont C (Kseq c k) pc ->
  exists pc',
  star (transition C) (pc, nil, m) (pc', nil, m)
  /\ codeseq_at C pc' (compile_com c)
  /\ compile_cont C k (pc' + length(compile_com c)).
Proof.
  intros; dependent induction H; firstorder eauto.
Qed.

Lemma compile_cont_Kwhile_inv:
  forall C b c k pc m,
  compile_cont C (Kwhile b c k) pc ->
  exists pc',
  plus (transition C) (pc, nil, m) (pc', nil, m)
  /\ codeseq_at C pc' (compile_com (WHILE b DO c END))
  /\ compile_cont C k (pc' + length(compile_com (WHILE b DO c END))).
Proof.
  intros; dependent induction H; firstorder eauto 7 using plus_star.
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
    change (compile_com c) with (nil ++ compile_com c) in H. eauto.
    eapply code_at_codeseq; eauto.
    eapply code_at_codeseq; eauto.
  intros. constructor. simpl. eauto. simpl. rewrite plus_0_r; auto.
Qed.

(** At long last, we can state and prove the right simulation diagram. *)

Hint Resolve match_config_skip.
Hint Extern 1 (_ < _) => omega.
Hint Constructors compile_cont match_config.

Lemma compile_cont_eq : forall C k pc pc',
    compile_cont C k pc ->
    pc = pc' ->
    compile_cont C k pc'.
Proof.
  congruence.
Qed.

Hint Extern 1 (compile_cont _ _ _) =>
  normalize; eapply compile_cont_eq; [ eassumption | omega ].

Lemma codeseq_at_eq : forall C pc pc' ls,
    codeseq_at C pc ls ->
    pc = pc' ->
    codeseq_at C pc' ls.
Proof.
  congruence.
Qed.

Hint Extern 1 (codeseq_at _ _ _) =>
  eapply codeseq_at_eq; [ eassumption | omega ].

Lemma code_at_eq : forall C pc pc' v,
    code_at C pc = Some v ->
    pc = pc' ->
    code_at C pc' = Some v.
Proof.
  congruence.
Qed.

Hint Extern 1 (code_at _ _ = Some _) =>
  eapply code_at_eq; [ eassumption | omega ].

Lemma appsplit_len : forall A (ls2 ls2' ls1 ls1' : list A),
    length ls1 = length ls1'
    -> ls1 ++ ls2 = ls1' ++ ls2'
    -> ls1 = ls1' /\ ls2 = ls2'.
Proof.
  induction ls1; destruct ls1'; simpl; intuition.
  injection H0; intros; subst.
  apply IHls1 in H1.
  intuition congruence.
  congruence.
  injection H0; intros; subst.
  apply IHls1 in H1.
  intuition congruence.
  congruence.
Qed.

Lemma codeseq_at_app : forall C pc ls1 ls2,
    codeseq_at C pc ls1 ->
    codeseq_at C (pc + length ls1) ls2 ->
    codeseq_at C pc (ls1 ++ ls2).
Proof.
  inversion 1; inversion 1; subst.
  rewrite H5.
  rewrite (app_assoc C1) in H5.
  eapply appsplit_len in H5.
  intuition subst.
  rewrite (app_assoc ls1).
  constructor; reflexivity.
  normalize; auto.
Qed.

Lemma codeseq_at_cons' : forall ls2 x ls1 pc,
    code_at (ls1 ++ ls2) pc = Some x ->
    pc + 1 = length ls1 ->
    exists ls1', ls1 = ls1' ++ x :: nil.
Proof.
  induction ls1; destruct pc; simpl; intuition.
  injection H; clear H; intros; subst.
  injection H0; clear H0; intros.
  destruct ls1; simpl in *; try discriminate.
  exists nil; auto.
  apply IHls1 in H; auto.
  firstorder subst.
  exists (a :: x0).
  auto.
Qed.

Lemma codeseq_at_cons : forall C pc x ls,
    code_at C pc = Some x
    -> codeseq_at C (pc + 1) ls
    -> codeseq_at C pc (x :: ls).
Proof.
  inversion 2; subst; intros.
  eapply codeseq_at_cons' in H; auto.
  firstorder subst.
  rewrite <- app_assoc.
  rewrite (app_assoc (x :: nil)).
  constructor.
  normalize.
  auto.
Qed.

Hint Extern 1 (codeseq_at _ _ (_ ++ _)) =>
  apply codeseq_at_app; fold compile_com.
Hint Extern 1 (codeseq_at _ _ (_ :: _)) =>
  apply codeseq_at_cons; fold compile_com.

Hint Extern 1 (compile_cont _ (Kwhile _ _ _) _) =>
  econstructor; normalize.

Hint Extern 1 (plus _ _ _) =>
  eapply star_plus_trans; [ eapply compile_aexp_correct; solve [ eauto ] | ].

Lemma simulation_step:
  forall C impstate1 impstate2 machstate1,
  kstep impstate1 impstate2 ->
  match_config C impstate1 machstate1 ->
  exists machstate2,
      (plus (transition C) machstate1 machstate2
       \/ (star (transition C) machstate1 machstate2 /\ measure impstate2 < measure impstate1))
   /\ match_config C impstate2 machstate2.
Proof.
  inversion_clear 1; subst; inversion_clear 1; subst; normalize;
    try match goal with
        | [ H : _ |- _ ] => eapply compile_cont_Kseq_inv in H; firstorder
        | [ H : _ |- _ ] => eapply compile_cont_Kwhile_inv in H; firstorder
        | [ c : com |- _ ] => generalize (com_size_nonzero c); intro
        end; fwd; eauto 12.
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

Ltac simulation := match goal with
                   | [ H1 : step1 _ _, H2 : match_states _ _ |- _ ] =>
                     specialize (simulation _ _ _ H1 H2)
                   end.

Lemma simulation_star:
  forall S1 S1', star step1 S1 S1' ->
  forall S2, match_states S1 S2 ->
  exists S2', star step2 S2 S2' /\ match_states S1' S2'.
Proof.
  induction 1; intros; try simulation; firstorder eauto using star_trans, plus_star.
Qed.

(** Turning to infinite sequences, we first show that the target program
  can always make progress, while preserving the [match_states] relation,
  if the source diverges.  The proof is an induction on the maximal number
  [N] of stutterings the target can make before performing at least one transition. *)

Hint Extern 1 (exists x, _) => omega.

Lemma simulation_infseq_productive:
  forall N S1 S2,
  infseq step1 S1 ->
  match_states S1 S2 ->
  measure S1 < N ->
    (* NOTE: moved this hypothesis last, so that, in proof search, we tend to
     * reach it _after_ determining some unification variables!  That way,
     * [omega] can be more effective as a hint. *)
  exists S1', exists S2',
      plus step2 S2 S2'
   /\ infseq step1 S1'
   /\ match_states S1' S2'.
Proof.
  induction N; intros; eauto;
    match goal with
    | [ H : infseq _ _ |- _ ] => invert H; simulation; firstorder
    end;
    match goal with
    | [ H : star _ _ _ |- _ ] => invert H; eauto 6
    end.
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
  as [S1' [S2' [P [Q R]]]]; auto.
  eauto.
  eauto.
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
  eapply simulation_star; eauto. intros; eapply simulation_step; eauto. apply match_config_initial.
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
  intros; eapply simulation_step; eauto. apply match_config_initial.
Qed.
