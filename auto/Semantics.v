(* Copied and modified from Xavier Leroy's lectures. *)

Require Import Coq.Program.Equality.
Require Import Maps Imp.
Require Import Sequences.

(** In this chapter: various styles of semantics for the Imp language
  from "Software Foundations", and equivalence results between these
  semantics. *)

(** * 1. Big-step semantics for termination. *)

(** The starting point is the big-step semantics defined in file [sf/Imp.v],
  recalled here for reference.
<<
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').
>>

[ c / st \\ st' ] means "executed in initial state [st], command [c]
terminates in final state [st']".

*)


(** * 2. Small-step semantics.  *)

Reserved Notation " c '/' st '==>' c' '/' st' " (at level 40, st at level 39, c' at level 39).

(** In small-step style, the semantics is presented as a one-step reduction
  relation [ c / st --> c' / st' ], meaning that the command [c],
  executed in initial state [st'], performs one elementary step of computation.
  [st'] is the updated state after this step.
  [c'] is the residual command, capturing all the computations that
  remain to be done.

  A small-step semantics for Imp is given in file [sf/Smallstep.v], where
  not only the execution of commands is broken in individual steps,
  but also the evaluation of arithmetic and boolean expressions.
  We depart from this semantics by still treating the evaluation
  of arithmetic and boolean expressions as one atomic "big-step"
  (cf. rules [CS_Ass], [CS_IfTrue] and [CS_IfFalse] below).
  Non-atomic evaluation of expressions makes a difference in the case
  of parallel (interleaved) execution of several commands.  In a purely
  sequential setting, it is equivalent (and much simpler) to
  evaluate expressions in one atomic step, since their evaluations
  always terminate.
*)

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_Ass : forall st i a n,
      aeval st a = n ->
      (i ::= a) / st ==> SKIP / (t_update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st b c1 c2,
      beval st b = true ->
      IFB b THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st b c1 c2,
      beval st b = false ->
      IFB b THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_While : forall st b c1,
      (WHILE b DO c1 END) / st
       ==> (IFB b THEN (c1 ;; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " c '/' st '==>' c' '/' st' " := (cstep (c,st) (c',st')).

(** An important property of this reduction relation is that it is functional,
  in the sense that a given configuration can reduce to at most one configuration. *)

Ltac invert0 H := inversion H; fail.
Ltac invert H := inversion H; clear H; subst.
Ltac invert1 H := invert0 H || (invert H; []).
Ltac invert2 H := invert1 H || (invert H; [|]).
Ltac invert3 H := invert2 H || (invert H; [| |]).
Ltac invert4 H := invert3 H || (invert H; [| | |]).

Lemma cstep_functional:
  forall cs cs1, cstep cs cs1 -> forall cs2, cstep cs cs2 -> cs1 = cs2.
Proof.
  induction 1; intros;
    repeat match goal with
           | [ H : cstep _ _ |- _ ] =>
             (* There is a step fact whose inversion leaves at most 2 cases,
              * so let's do that inversion. *)
             invert2 H

           | [ IH : forall cs2 : com * state, cstep ?pre cs2 -> ?post = cs2,
                H : cstep ?pre ?post' |- _ ] =>
             (* We have an IH that is good to instantiate in any useful way.
              * What's not useful?  When the conclusion matches a fact we
              * already know!  The dance below catches that case. *)
             match post with
             | post' => fail 1
             | _ => specialize (IH _ H)
             end
           end; try congruence.
Qed.

(** In small-step style, the semantics of a command [c] in a state [st]
  is determined by forming sequences of reductions starting from [c, st].
- Finite sequences: zero, one or several reductions (reflexive transitive closure)
- Infinite sequences: infinitely many reductions.

These sequences are defined using the generic [star] and [infseq] operators
over binary relations, which are defined in module [Sequences], along
with useful lemmas. *)

Definition terminates (c: com) (st: state) (st': state) : Prop :=
  star cstep (c, st) (SKIP, st').

Definition diverges (c: com) (st: state) : Prop :=
  infseq cstep (c, st).

(** *** Exercise (2 stars, optional) *)
(** Show that the final state of a terminating program is unique,
  and that a program cannot both terminate and diverge.
  Hint: use the generic determinism properties found at the end of module [Sequence],
  plus the following useful remark. *)

Remark irred_SKIP:
  forall st, irred cstep (SKIP, st).
Proof.
  unfold irred; intros st st' STEP.
  (* FILL IN HERE *)
Admitted.

Lemma terminates_unique:
  forall c st st1 st2, terminates c st st1 -> terminates c st st2 -> st1 = st2.
Proof.
  unfold terminates; intros. 
  (* FILL IN HERE *)
Admitted.

Lemma terminates_diverges_exclusive:
  forall c st st', terminates c st st' -> diverges c st -> False.
Proof.
  (* FILL IN HERE *)
Admitted.

(** *** Exercise (3 stars, recommended) *)
(** Show that Imp programs cannot go wrong.  Hint: first prove the following
  "progress" result for non-[SKIP] commands. *)

Lemma cstep_progress:
  forall c st, c = SKIP \/ exists c', exists st', c / st ==> c' / st'.
Proof.
  induction c; intros.
  (* FILL IN HERE *)
Admitted.

Definition goes_wrong (c: com) (st: state) : Prop :=
  exists c', exists st',
  star cstep (c, st) (c', st') /\ irred cstep (c', st') /\ c' <> SKIP.

Lemma not_goes_wrong:
  forall c st, ~(goes_wrong c st).
Proof.
  unfold not, goes_wrong, irred; intros.
  (* FILL IN HERE *)
Admitted.

(** As a corollary, using the [infseq_or_finseq] theorem from module [Sequence], we obtain that any IMP program either terminates safely or diverges. *)

Lemma terminates_or_diverges:
  forall c st, (exists st', terminates c st st') \/ diverges c st.
Proof.
  (* FILL IN HERE *)
Admitted.

(** Sequences of reductions can go under a sequence context, generalizing
  rule [CS_SeqStep]. *)

Hint Constructors star cstep.
(* [Hint Constructors]: add all rules of a predicate(s) to the list of hints. *)

Lemma star_CS_SeqStep:
  forall c2 st c st' c',
  star cstep (c, st) (c', st') -> star cstep ((c;;c2), st) ((c';;c2), st').
Proof.
  intros; dependent induction H;
    try match goal with
        | [ x : (_ * _)%type |- _ ] => destruct x
        end; eauto.
  (* Why [%type]?  That's a _notation scope_, to distinguish product types from
   * multiplication of numbers. *)
Qed.

(** We now recall the equivalence result between 
- termination according to the big-step semantics
- existence of a finite sequence of reductions to [SKIP]
  according to the small-step semantics.

We start with the implication big-step ==> small-step, which is
a straightforward induction on the big-step evaluation derivation. *)

Local Hint Resolve star_one star_CS_SeqStep.
(* [Hint Resolve]: add a particular lemma to the list of hints. *)

Theorem ceval_to_csteps:
  forall c st st',
  c / st \\ st' -> star cstep (c, st) (SKIP, st').
Proof.
  induction 1; eauto 7 using star_trans.
  (* Why not just add [star_trans] as a hint?  Transitivity can lead to
   * exponential search spaces, so we only invoke it where we know it pays off. *)
Qed.

(** The reverse implication, from small-step to big-step, is more subtle.
The key lemma is the following, showing that one step of reduction
followed by a big-step evaluation to a final state can be collapsed
into a single big-step evaluation to that final state. *)

Hint Constructors ceval.

Lemma cstep_append_ceval:
  forall c1_st1 c2_st2,
  cstep c1_st1 c2_st2 ->
  forall st3,
  ceval (fst c2_st2) (snd c2_st2) st3 ->
  ceval (fst c1_st1) (snd c1_st1) st3.
Proof.
  induction 1; simpl; intros; eauto;
  repeat (match goal with
          | [ H : ceval _ _ _ |- _ ] => invert2 H
          end; eauto).
Qed.

(** As a consequence, a term that reduces to [SKIP] evaluates in big-step
  with the same final state. *)

Hint Resolve cstep_append_ceval.

Lemma csteps_append_ceval:
  forall c1_st1 c2_st2,
  star cstep c1_st1 c2_st2 ->
  forall st3,
  ceval (fst c2_st2) (snd c2_st2) st3 ->
  ceval (fst c1_st1) (snd c1_st1) st3.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve csteps_append_ceval.

Theorem csteps_to_ceval:
  forall st c st',
  star cstep (c, st) (SKIP, st') -> c / st \\ st'.
Proof.
  intros.
  change c with (fst (c, st)).
  change st at 2 with (snd (c, st)).
  eauto.
Qed.

(** * 3. Small-step semantics with continuations. *)

(** We now introduce an alternate form of the small-step semantics above
  where the command to be reduced is explicitly decomposed into:
- a sub-command under focus, where computation takes place;
- a continuation (or context) describing the position of this sub-command
  in the whole command, or, equivalently, describing the parts of the
  whole command that remain to be reduced once the sub-command is done.

As a consequence, the small-step semantics is presented as a transition relation
between triples (subcommand-under-focus, continuation, state).
Previously, we had transitions between pairs (whole-command, state).

The syntax of continuations is as follows:
*)

Inductive cont : Type :=
  | Kstop : cont
  | Kseq : com -> cont -> cont
  | Kwhile : bexp -> com -> cont -> cont.

(** Intuitive meaning of these constructors:
- [Kstop] means that, after the sub-command under focus terminates, nothing remains to
  be done, and execution can stop.  In other words, the sub-command under
  focus is the whole command.
- [Kseq c k] means that, after the sub-command terminates, we still need
  to execute command [c] in sequence, then continue as described by [k].
- [Kwhile b c k] means that, after the sub-command terminates, we still need
  to execute a loop [WHILE b DO c END], then continue as described by [k].
*)

(** Another way to forge intuitions about continuations is to ponder the following
  [apply_cont k c] function, which takes a sub-command [c] under focus
  and a continuation [k], and rebuilds the whole command.  It simply
  puts [c] in lefmost position in a nest of sequences as described by [k].
*)

Fixpoint apply_cont (k: cont) (c: com) : com :=
  match k with
  | Kstop => c
  | Kseq c1 k1 => apply_cont k1 (c ;; c1)
  | Kwhile b1 c1 k1 => apply_cont k1 (c ;; WHILE b1 DO c1 END)
  end.

(** Transitions between (subcommand-under-focus, continuation, state) triples
  perform conceptually different kinds of actions:
- Computation: evaluate an arithmetic expression or boolean expression
  and modify the triple according to the result of the evaluation.
- Focusing: replace the sub-command by a sub-sub-command that is to be
  evaluated next, possibly enriching the continuation as a consequence.
- Resumption: when the sub-command is [SKIP] and therefore fully executed,
  look at the head of the continuation to see what to do next.

Here are the transition rules, classified by the kinds of actions they implement.
*)

Inductive kstep : (com * cont * state) -> (com * cont * state) -> Prop :=

  | KS_Ass : forall st i a k n,            (**r Computation for assignments *)
      aeval st a = n ->
      kstep ((i ::= a), k, st) (SKIP, k, t_update st i n)

  | KS_Seq : forall st c1 c2 k,  (**r Focusing on the left part of a sequence *)
      kstep ((c1 ;; c2), k, st) (c1, Kseq c2 k, st)

  | KS_IfTrue : forall st b c1 c2 k,  (**r Computation for conditionals *)
      beval st b = true ->
      kstep (IFB b THEN c1 ELSE c2 FI, k, st) (c1, k, st)
  | KS_IfFalse : forall st b c1 c2 k,
      beval st b = false ->
      kstep (IFB b THEN c1 ELSE c2 FI, k, st) (c2, k, st)

  | KS_WhileTrue : forall st b c k,  (**r Computation and focusing for loops *)
      beval st b = true ->
      kstep (WHILE b DO c END, k, st) (c, Kwhile b c k, st)
  | KS_WhileFalse : forall st b c k,
      beval st b = false ->
      kstep (WHILE b DO c END, k, st) (SKIP, k, st)

  | KS_SkipSeq: forall c k st,  (**r Resumption on [SKIP] *)
      kstep (SKIP, Kseq c k, st) (c, k, st)
  | KS_SkipWhile: forall b c k st,
      kstep (SKIP, Kwhile b c k, st) (WHILE b DO c END, k, st).

(** Note: the [kstep] relation is not inductive, in the sense that the premises
  of the rules never involve the [kstep] relation itself.  Contrast with
  the [cstep] relation, which is recursive in the [CS_SeqStep] case:
<<
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ; c2) / st ==> (c1' ; c2) / st'
>>
  For [cstep], this rule enables us to reduce "deep" within a sequence.
  In contrast, [kstep] always reduce at the top of the given [(c,k,st)] triple.
  Reducting within a sequence is achieved by first focusing on the left
  part of the sequence (rule [KS_Seq]), bringing it to the top of the triple,
  then working on this left part.
*)

(** As in section 2, we can define the behavior of a command in terms of
  sequences of [kstep] reductions.  
  Initial configurations are of the form (whole-command, [Kstop], initial-state).
  Final configurations are ([SKIP], [Kstop], final-state).  *)

Definition kterminates (c: com) (st: state) (st': state) : Prop :=
  star kstep (c, Kstop, st) (SKIP, Kstop, st').

Definition kdiverges (c: com) (st: state) : Prop :=
  infseq kstep (c, Kstop, st).

(** ** Extensions to other control structures *)

(** A remarkable feature of continuation semantics is that they extend very easily
  to other control structures besides "if-then-else" and "while" loops.
  Consider for instance the "break" construct of C, C++ and Java, which
  immediately terminates the nearest enclosing "while" loop.  Assume we
  extend the type of commands with a [BREAK] constructor.  Then, all we need
  to give "break" a semantics is to add two resumption rules:
<<
  | KS_BreakSeq: forall c k st,
      kstep (BREAK, Kseq c k, st) (BREAK, k, st)
  | KS_BreakWhile: forall b c k st,
      kstep (BREAK, Kwhile b c k, st) (SKIP, k, st)
>>
  The first rule says that a [BREAK] statement "floats up" pending sequences,
  skipping over the computations they contain.  Eventually, a [Kwhile]
  continuation is encountered, meaning that the [BREAK] found its enclosing
  loop.  Then, the second rule discards the [Kwhile] continuation and
  turns the [BREAK] into a [SKIP], effectively terminating the loop.
  That's all there is to it!
**)

(** If you're curious about adding "break" to the big-step semantics of
  section 1, see exercise [BreakImp] in the [Imp] module of 
  Software Foundations. *)

(** *** Exercise (2 stars, recommended) *)
(** Besides "break", C, C++ and Java also have a "continue" statement
  that terminates the current iteration of the enclosing loop,
  then resumes the loop at its next iteration (instead of stopping
  the loop like "break" does). Give the transition rules
  for the "continue" statement. *)

(** *** Exercise (3 stars, optional) *)
(** In Java, loops as well as "break" and "continue" statements carry
  an optional label.  "break" without a label exits out of the immediately
  enclosing loop, but "break lbl" exits out of the first enclosing loop
  that carries the label "lbl".  Similarly for "continue".
  Give the transition rules for "break lbl" and "continue lbl". *)

(** ** Relating the continuation semantics with the other semantics *)

(** As in section 2, we show that termination according to the continuation semantics
  (predicate [kterminates]) is equivalent to big-step evaluation.
  The first implication, from big-step evaluation to termination, is a
  straightforward induction on the structure of the big-step
  evaluation derivation. *)

Hint Constructors kstep.

Theorem ceval_to_ksteps:
  forall c st st',
  c / st \\ st' ->
  forall k, star kstep (c, k, st) (SKIP, k, st').
Proof.
  induction 1; eauto using star_trans.
Qed.

(** For the reverse implication, we adapt lemma [cstep_append_ceval] to show
  that one step of reduction [kstep (c1, k1, st1) (c2, k2, st2)] 
  followed by big-step evaluation of [(c2, k2, st2)] is equivalent to
  big-step evaluation of [(c1, k1, st1)].  However, we now need to define
  big-step evaluation of a pair [(c, k)] of a subcommand and a continuation.
  We define this notion as first evaluating [c], obtaining a modified state,
  then performing the latent computations described by [k], obtaining the final
  state. *)

Inductive keval : cont -> state -> state -> Prop :=
  | KE_stop: forall st,
      keval Kstop st st
  | KE_seq: forall c k st1 st2 st3,
      ceval c st1 st2 -> keval k st2 st3 ->
      keval (Kseq c k) st1 st3
  | KE_while: forall b c k st1 st2 st3,
      ceval (WHILE b DO c END) st1 st2 -> keval k st2 st3 ->
      keval (Kwhile b c k) st1 st3.

Inductive ckeval: com -> cont -> state -> state -> Prop :=
  | CKE_intro: forall c k st1 st2 st3,
      ceval c st1 st2 -> keval k st2 st3 ->
      ckeval c k st1 st3.

Hint Constructors keval ckeval.

Hint Extern 1 ((_ ::= _) / _ \\ _) => eapply E_Ass; reflexivity.

Ltac inverter1 :=
  match goal with
  | [ H : ckeval _ _ _ _ |- _ ] => invert H
  | [ H : ceval _ _ _ |- _ ] => invert2 H
  | [ H : keval _ _ _ |- _ ] => invert1 H
  end; eauto.

Ltac inverter := intros; repeat inverter1.

Lemma kstep_append_ckeval:
  forall c1 k1 st1 c2 k2 st2,
  kstep (c1, k1, st1) (c2, k2, st2) ->
  forall st3,
  ckeval c2 k2 st2 st3 ->
  ckeval c1 k1 st1 st3.
Proof.
  intros until st2; intro STEP; dependent induction STEP; intros; eauto; inverter.
Qed.

(** We can, then, extend this result to sequences of [kstep] transitions, 
  and conclude. *)

Hint Resolve kstep_append_ckeval.

Lemma ksteps_append_ckeval:
  forall c1 k1 st1 c2 k2 st2 st3,
  star kstep (c1, k1, st1) (c2, k2, st2) ->
  ckeval c2 k2 st2 st3 ->
  ckeval c1 k1 st1 st3.
Proof.
  intros; dependent induction H;
    repeat match goal with
           | [ x : (_ * _)%type |- _ ] => destruct x
           end; eauto.
Qed.

Lemma ckeval_done : forall c st1 st2,
    ckeval c Kstop st1 st2
    -> ceval c st1 st2.
Proof.
  intros; inverter.
Qed.

Hint Resolve ksteps_append_ckeval ckeval_done.

Theorem kterminates_to_ceval:
  forall c st st',
  kterminates c st st' -> c / st \\ st'.
Proof.
  eauto.
Qed.

(** From the theorems above, it follows that the two small-step semantics
  capture the same notion of termination. *)

Hint Resolve kterminates_to_ceval ceval_to_csteps ceval_to_ksteps csteps_to_ceval.

Theorem kterminates_iff_terminates:
  forall c st st', kterminates c st st' <-> terminates c st st'.
Proof.
  unfold terminates, kterminates; intuition eauto.
Qed.

(** For additional confidence, we can show that the two small-step semantics
  (with and without continuations) capture the same notion of divergence.
  The proof is surprisingly involved and consists in relating infinite
  sequences of [kstep] transitions from an initial state [(c, k, st)]
  with infinite sequences of [cstep] transitions from the corresponding
  initial state [(apply_cont k c, st)].  The proofs are included below
  for completeness, but can be skipped on first reading. *)

Remark cstep_apply_cont:
  forall k c1 st1 c2 st2,
  cstep (c1, st1) (c2, st2) ->
  cstep (apply_cont k c1, st1) (apply_cont k c2, st2).
Proof.
  induction k; eauto.
Qed.

Hint Constructors plus.
Local Hint Resolve cstep_apply_cont plus_one.

Ltac inverter1 ::=
  match goal with
  | [ H : ckeval _ _ _ _ |- _ ] => invert H
  | [ H : ceval _ _ _ |- _ ] => invert2 H
  | [ H : keval _ _ _ |- _ ] => invert1 H
  | [ H : kstep _ _ |- _ ] => invert2 H
  | [ H : infseq kstep _ |- _ ] => invert H;
    match goal with
    | [ H : kstep _ _ |- _ ] => invert4 H
    end
  end; simpl in *; eauto 10.

Hint Constructors infseq.

(* It's a bit mysterious why existing hints don't already have the effect of this one. *)
Hint Extern 1 ((_ ::= _) / _ ==> _ / _) => apply CS_Ass; reflexivity.

(* Here we suggest a pattern for a quantifier instantiation, so that [simpl] can
 * reduce calls to [apply_cont] within the quantifier body. *)
Hint Extern 1 (exists k : cont, _) => eexists (Kwhile _ _ _); simpl.

Lemma kinfseq_cinfseq:
  forall c k st,
  infseq kstep (c, k, st) ->
  exists c', exists k', exists st',
  plus cstep (apply_cont k c, st) (apply_cont k' c', st')
  /\ infseq kstep (c', k', st').
Proof.
  induction c; inverter; firstorder.
Qed.

(** We now prepare for the reverse diagram: decomposing infinite sequences of
  [cstep] transitions in terms of [kstep] transitions.  First, a technical
  inversion lemma on [cstep] reductions over commands of the form [apply_cont k c]. *)

Inductive cstep_apply_cont_cases: cont -> com -> state -> com -> state -> Prop :=
  | cacc_base: forall c1 st1 c2 st2 k,
      cstep (c1, st1) (c2, st2) ->
      cstep_apply_cont_cases k c1 st1 (apply_cont k c2) st2
  | cacc_skip_seq: forall c k st,
      cstep_apply_cont_cases (Kseq c k) SKIP st (apply_cont k c) st
  | cacc_skip_while: forall b c k st,
      cstep_apply_cont_cases (Kwhile b c k) SKIP st (apply_cont k (WHILE b DO c END)) st.

Hint Constructors cstep_apply_cont_cases.

Lemma cacc_base': forall c1 st1 c2 st2 k app_k_c2,
    cstep (c1, st1) (c2, st2) ->
    app_k_c2 = apply_cont k c2 ->
    cstep_apply_cont_cases k c1 st1 app_k_c2 st2.
Proof.
  intros; subst; eauto.
Qed.

Lemma cacc_skip_seq': forall c k st app_k_c,
    app_k_c = apply_cont k c ->
    cstep_apply_cont_cases (Kseq c k) SKIP st app_k_c st.
Proof.
  intros; subst; eauto.
Qed.

Lemma cacc_skip_while': forall b c k st app_k_while,
    app_k_while = apply_cont k (WHILE b DO c END)
    -> cstep_apply_cont_cases (Kwhile b c k) SKIP st app_k_while st.
Proof.
  intros; subst; eauto.
Qed.

Local Hint Resolve cacc_base' cacc_skip_seq' cacc_skip_while' plus_star.

Ltac inverter1 ::=
  match goal with
  | [ H : ckeval _ _ _ _ |- _ ] => invert H
  | [ H : ceval _ _ _ |- _ ] => invert2 H
  | [ H : keval _ _ _ |- _ ] => invert1 H
  | [ H : kstep _ _ |- _ ] => invert2 H
  | [ H : cstep _ _ |- _ ] => invert2 H
  | [ H : cstep_apply_cont_cases _ _ _ _ _ |- _ ] => invert H
  | [ H : infseq kstep (apply_cont _ _, _) |- _ ] => invert H
  | [ H : infseq kstep _ |- _ ] => invert H;
    match goal with
    | [ H : kstep _ _ |- _ ] => invert2 H
    end
  end; simpl in *; eauto 10.

Lemma invert_cstep_apply_cont:
  forall k c st c' st',
  cstep (apply_cont k c, st) (c', st') ->
  cstep_apply_cont_cases k c st c' st'.
Proof.
  induction k; simpl; intros; eauto;
    try match goal with
        | [ IH : forall c st c' st', apply_cont _ c / st ==> c' / st' -> _,
              H : _ / _ ==> _ / _ |- _ ] =>
          specialize (IH _ _ _ _ H)
        end; inverter.
Qed.

Hint Extern 1 (kstep (_ ::= _, _, _) _) => apply KS_Ass; reflexivity.

Ltac inverter1 ::=
  match goal with
  | [ H : ckeval _ _ _ _ |- _ ] => invert H
  | [ H : ceval _ _ _ |- _ ] => invert2 H
  | [ H : keval _ _ _ |- _ ] => invert1 H
  | [ H : kstep _ _ |- _ ] => invert2 H
  | [ H : cstep _ _ |- _ ] => invert2 H
  | [ H : cstep_apply_cont_cases _ _ _ _ _ |- _ ] => invert2 H
  | [ H : cstep (apply_cont _ _, _) ?x |- _ ] =>
    (apply invert_cstep_apply_cont in H
     || (destruct x; apply invert_cstep_apply_cont in H))
  | [ H : infseq _ (apply_cont _ _, _) |- _ ] => invert H
  | [ H : infseq kstep _ |- _ ] => invert H;
    match goal with
    | [ H : kstep _ _ |- _ ] => invert4 H
    end
  | [ H : plus kstep _ _ |- _ ] => invert H
  end; simpl in *; eauto 10.

Lemma cinfseq_kinfseq' : forall c st c2 st',
    c / st ==> c2 / st' ->
    forall k, infseq cstep (apply_cont k c2, st') ->
      exists c' k',
        plus kstep (c, k, st) (c', k', st') /\ infseq cstep (apply_cont k' c', st').
Proof.
  intros until st'; intro H; dependent induction H; simpl; intros; eauto 6;
    try match goal with
        | [ IH : forall c : com, _, H : infseq _ _ |- _ ] =>
          evar (c' : com); evar (k' : cont); specialize (IH _ _ _ _ eq_refl eq_refl (Kseq c' k'));
            simpl in IH; subst c' k'; specialize (IH H); firstorder
        end; inverter.
Qed.

Lemma infseq_cstep : forall s k c c' s',
    infseq cstep (apply_cont k c, s)
    -> c / s ==> c' / s'
    -> infseq cstep (apply_cont k c', s').
Proof.
  induction k; simpl; intros; eauto;
    match goal with
    | [ H : infseq _ _ |- _ ] => invert H
    end;
    match goal with
    | [ H1 : cstep ?X _, H2 : cstep ?X _ |- _ ] =>
      eapply cstep_functional in H2; try apply H1; congruence
    end.
Qed.

Lemma cinfseq_kinfseq:
  forall c k st,
  infseq cstep (apply_cont k c, st) ->
  exists c', exists k', exists st',
  plus kstep (c, k, st) (c', k', st')
  /\ infseq cstep (apply_cont k' c', st').
Proof.
  inverter.
  invert H0; eauto 10.
  eapply cinfseq_kinfseq' in H; eauto; firstorder.
Qed.

(** The desired equivalence between the two notions of divergence then follows
  from the coinduction principles given in module [Sequence]. *)

Theorem kdiverges_iff_diverges:
  forall c st, kdiverges c st <-> diverges c st.
Proof.
  specialize kinfseq_cinfseq; specialize cinfseq_kinfseq.
  intros; split; intros.
- (* kdiverges -> diverges *)
  apply infseq_coinduction_principle_2 with
    (X := fun c_st => exists c, exists k, exists st,
                      c_st = (apply_cont k c, st) /\ infseq kstep (c, k, st));
    firstorder (subst; eauto 10).
- (* diverges -> kdiverges *)
  apply infseq_coinduction_principle_2 with
    (X := fun c_k_st =>
            match c_k_st with (c, k, st) => infseq cstep (apply_cont k c, st) end);
    intros; repeat match goal with
                   | [ x : (_ * _)%type |- _ ] => destruct x
                   end; firstorder eauto.
Qed.
