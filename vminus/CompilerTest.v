(** * CompilerTest: Testing Vminus: QuickChick in the Large *)

Require Import List.
Import ListNotations.
Require Import String.
Require Import Arith.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.QC.
Require Import Vminus.Classes.
Require Import Vminus.Vminus.
Require Import Vminus.Atom.
Require Import Vminus.CFG.
Require Import Vminus.ListCFG.
Require Import Vminus.Imp.
Require Import Vminus.Compiler.
Require Import Vminus.VminusOpSem.
Import V.Opsem.

Require Import Vminus.AtomGen.
Require Import Vminus.ImpGen.
Require Import Vminus.OpSemGen.

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-extraction-logical-axiom".
Set Warnings "-large-nat,-numbers".

(* ################################################################# *)
(** * QuickChick and Vellvm *)
(** One might expect a compiler (and correctness proof) for a language
    as simple as IMP to be relatively straightforward.
    
    However, LLVM -- even in its simplified Vminus form -- is a
    somewhat complex IR, and a faithful formalization is necessarily
    somewhat involved.  Moreover, when a compiler is under
    development, even _stating_ its correctness can be difficult, much
    less proving it.

    Fortunately, _testing_ the compiler and its correctness properties
    is a much simpler affair, as we will see. *)

(** Our target language is the simplified SSA language Vminus defined
    in the other files in this directory, and we use a variant of Imp
    whose names are just memory addresses which can be interpreted in
    the memory of Vminus states. Imp states and Vminus memory are
    hence essentially the same, and this makes it easy to state
    correct compilation: after running the source program and its
    compiled version, every Imp variable/address is mapped to the same
    [nat] by both the final Imp state and the final Vminus memory. *)

(** A Vminus state consists of a memory (mapping addresses to [nat]),
    a program counter, an environment (mapping "locals" to [nat]), a
    "previous" program counter, and a "previous" environment; the
    latter two are used for executing phi nodes. A configuration
    consists of a Vminus state and a CFG, which holds Vminus
    instructions organized in basic blocks. *)

(* ################################################################# *)
(** * Vminus Review *)

(** To make this case study chapter self contained, we begin with a
    very brief review of the relevant parts of the Vminus intermediate
    language and compiler.  If you're already familiar with
    Vminus (e.g., from reading the other files and working exercises),
    you can safely skip to the next section.

    A Vminus program in concrete syntax vs abstract syntax looks like
    this (warning: program is meant to only show syntax, and is not
    meant to make sense):


block #1:
 %1 = add 0 0 
  (* binary operations can work on numeric literals, i.e. [nat] *) 
 %2 = add %1 5 (* also, on variables *) 
 %3 = sub %2 %1 
 %4 = store @1 %3 
  (* store the value held by %3 into memory at address @1 *)


    Looking ahead a bit:
    - The Imp store and Vminus memory are the same;
    - Vminus addresses and Imp variables are the same (modulo the
      [AId] constructor).
      
    Hence Imp programs have direct access to Vminus memory, and
    assignment statements correspond directly to such a store
    instruction.

    Also note that %%4 is redundant here; the reason is to make the
    abstract syntax uniform


 %5 = store @1 1 (* We can store literals too *) 
 %6 = load @1 
 %7 = cbr %6 #2 #3 
  (* conditional branch based on value held in %6, again with %7 being 
     redundant; we can also branch on [nat] *)

block #2:
 %8 = load @1 
 %9 = jmp #4 (* unconditional jump *)

block #3:
 %10 = load @1 
 %11 = jmp #4

block #4:
 %12 = phi [(#2, %8) ; (#3, %10)] 
  (* %12 takes the value held by %8 if control came from block #2, 
     or the value held by %10 if control came from #3 *) 
 %13 = jmp #5

block #5:
 %14 = ret (* again, variable %14 is unnecessary *)


In the abstract syntax, every instruction is defined as:

[Definition insn := (uid * cmd)%type.]

In the above, the [uid] is the number on the left of the equal sign,
and [cmd] is defined as follows:


Inductive cmd : Set :=
| cmd_bop : bop -> val -> val -> cmd cmd_phi : list phiarg -> cmd
| cmd_tmn : tmn -> cmd cmd_load : addr -> cmd cmd_store : addr ->
| val -> cmd.


Each individual command is either a binary operation like add, a
phi-node that joins a list of blocks, a terminator, a load, or a
store; all of these are illustrated in the program above.

Moreover, a program is represented as a control flow graph (see
[ListCFG] for implementation and [CFG] for the interface). 
A CFG is just a list of blocks, with one of
them distinguished (via [lbl]) as the entry block.


Definition t := (lbl * list block)%type. 
Local Notation cfg := t.


A program counter is a block label [lbl] with an offset n within the
block.

[ Definition pc := (lbl * nat)%type. ]

A block has its label [lbl] and contains a list of instructions.

[ Definition block := (lbl * list insn)%type. ]

As the concrete syntax shows, there are 3 forms of identifiers, and
they are all implemented as Atoms with the fresh interface.
- [uid]: The %% prefix, e.g. %%7.
- [addr]: The @ prefix, e.g @1.
- [lbl]: The # prefix, e.g. #3.  A potential point of confusion would
be that [Check], [Print], etc. shows [addr] instead of [lbl] or [uid], because
[addr] is last-defined.
*)

(* ################################################################# *)
(** * Overview of the Compiler *)

(**
One key part of compilation to Vminus, as an SSA form, is the need to generate
fresh labels as we go along. Hence the compiler is implemented as a Writer 
monad, specifically as a CMD (and EXP) following the definitions below:

In [Classes.v]: 

[ Definition ST (M:Type) (A:Type) := M -> (M * A).] 

In [Compiler.v]:

Notation EXP := (ST (list uid)).
Definition cstate := (list lbl * list uid * list block)%type.
Notation CMD := (ST cstate).


The [CMD] monad is the compiler monad at the top level, handling in particular 
control flow (that is why the block labels are threaded through). The [EXP]
monad is for compilation within basic blocks. A subtlety: the compiler compiles 
every Imp assignment statement to its own basic block, so basic blocks in the 
compilation result are not maximal in the usual sense. 

For both, [list uid] is the set of uids already generated thus far; similar
interpretation for [list lbl]. The [list block] part holds the compilation 
result thus far (recall that each block contains its own block label). 

Compilation is hence activated by running the function [CMD] on appropriate
initial (empty) lists:


Definition compile (c:com) : ListCFG.t * lbl * lbl :=
  let '(_, _, bs, (le, lr)) := comp_prog c ([], [], []) in
    ((le, bs), le, lr).

Definition comp_prog (c:com) : CMD (lbl * lbl) :=
  do r <- fresh_lbl;
  do x <- liftF fresh;
  do _ <- add_insns r [(x, cmd_tmn tmn_ret)];
  do e <- comp_com c r;
  ret (e, r).


Looking at just [compile] and the signature of [comp_prog], the compiler 
instantiates the value part of the state monad [A] in [S * A] as [lbl * lbl].
The first component is the entry (block) label that can be used to start 
executing the compilation result; the second component is the label for the 
block that control goes to -after- executing the compilation result. 

Note: [le] and [lr] are used consistently to mean as such. 

*)

(**
This is why the CFG (i.e. compiled program) returned has its entry label as 
[le], and the compilation result is just [bs]. 

For [comp_prog] itself: 
- [fresh_label] creates a new block with no instructions in the compilation 
  result, gives it a fresh label, and returns this as its value [r]
- it generates a fresh [uid] (%%<number>) via [fresh], and returns this [x]
- it sets, in the compilation result, the block labeled [r] to hold a 
  return terminator instruction. To see this concretely, look at 
  [block #5: %14 = ret] above.
- it compiles the program [c] via [comp_com]. Note that the desired 
  return-of-control [lbl r] is passed to it. The [lbl e] returned by [comp_com] 
  is in turn the entry-of-control label [e].

As the documentation for [comp_com] states:
  The input [lr] is the "continuation" label of the block to which control
  should return after the command is done.  The output is the label of the
  entry block for the command. 
  
  Note how compiling a sequence [[c1;;c2]] threads the control through the 
  commands in reverse order.
*)


(* ################################################################# *)
(** * Overview of Relevant Files *)
(**
   - \CHAP{Vminus] defines the syntax of Vminus.
   - [VminusOpSem] defines its semantics.   

     [Inductive step (g:Cfg.t) : state -> state -> Prop] summarizes everything. 
     A Vminus state is described below, but concretely for now:
*)
(**

     Record state := mkst { st_mem  : mem
                          ; st_pc   : pc
                          ; st_loc  : loc
                          ; st_ppc  : pc     (* predecessor pc *)
                          ; st_ploc : loc    (* predecessor "locals" *) 
                          }.
*)
(**
   - [Compiler] shows the compiler. 
   - [CFG] is the interface for CFGs; [ListCFG] is the implementation.
   - [CompilerProp] holds the relevant content for what follows, and is 
     described in-line.
*)

(* ################################################################# *)
(** * Testing Whole-Program Compiler Correctness *)

(** Here's a property we'd like to test (from [CompilerProp]):

    Theorem compile_program_correct_terminating:
      forall c m m' g le lr,
      (g, le, lr) = compile c ->
      imp_terminates c m m' ->
      vminus_terminates g m m'.
*)

(** This is one of the top-level correctness theorems for the
    compiler: for any initial memory [m], if the source program [c]
    terminates with memory (Imp state) [m'], running the compilation
    result [g] (a control flow graph holding the instructions) on the
    same initial memory [m] also results in termination, and with its
    final (Vminus) memory also being [m']. *)

(** (This is where the coincidence of Imp states and Vminus
    memory comes into play.) *)
    

(** Recall: An Imp program takes memory [m] to memory [m'], written
    [imp_terminates c m m'] if, when started in [m], it multi-steps to
    just [SKIP], with new memory [m']. *)
(** 

    Definition imp_terminates (c: com) (m m': mem) : Prop :=
      star Imp.step (c, m) (SKIP, m').
*)

(** For Vminus programs [g], on the other hand, running on an initial
    memory [m] leads to with memory [m'], written [vminus_terminates g
    m m'] if execution starting from [m] reaches a return terminator
    [tmn_ret]. *)
(** 

    Definition vminus_terminates 
                  (g: ListCFG.t) (m m': mem) : Prop :=
      exists x st',
        insns_at_pc g st'.(st_pc) [(x, cmd_tmn tmn_ret)] /\
        st'.(st_mem) = m' /\
        star (step g) (init_state g m) st'.
*)

(** The variables [x] and [st'] here are determined by the evaluation
    relation, as indicated by [star (step g) (init_state g m) st']. So
    checking for their existence can be thought of as verifying that
    an evaluation function yields some [x] and [st'] satisfying the
    constraints. *)

(** Let us try to write a [Checker] for the property

    Theorem compile_program_correct_terminating:
      forall c m m' g le lr,
      (g, le, lr) = compile c ->
      imp_terminates c m m' ->
      vminus_terminates g m m'.

    Looking naively at these "for all" quantifiers, it would appear that 
    we need generators for Imp commands ([c]), Imp states / Vminus
    memories ([m], [m']), control flow graphs ([g]) and labels ([le],
    [lr]). *)

(** However, [g], [le], and [lr] are computed by [compile c], so we
    don't actually need generators for them. Moreover, we do not want
    just any [m']; rather, [m'] should be obtained by running an Imp
    evaluator (which we have) on [m]. Hence for generation, we only
    need
    (1) a generator for [mem] and
    (2) a generator for Imp programs. *)

(** And for checking that the property holds, we need
    (1) an evaluator for Vminus that repeatedly steps until it reaches a
        return terminator and
    (2) a way to check that the final state [st'] from the Vminus
        evaluator has the desired memory contents. *)

(** One small technical issue with all of this is that memories are
    total maps on an infinite domain, so we cannot actually check that
    two memories are equal.

    Fortunately, for compiler testing, we only care about variables
    that appear in the source program. So as a simplification, we fix
    a domain of variables from which we draw when generating Imp
    programs, and we use the same set when checking memories. *)

(** The domain is fixed up front in [ImpGen] like this: *)

Print id_store.
(* ===> 
    id_store = get_fresh_atoms 5 []
 *)

(** The generator [gen_id] generates fresh identifiers (atoms) by sampling from 
    this fixed domain. *)

Print gen_id.
(* ===> 
    gen_id = gen_fresh id_store
 *)

(** Given the generator for [id]s, we can generate [aexp], [bexp], and
    [com] as follows. *)

Instance gen_aexp : GenSized aexp :=
  {
    arbitrarySized :=
       let base_gen := oneOf [(n <- arbitrary ;; ret (ANum n)) ;
                              (id <- gen_id ;; ret (AId id))] in
       fix gen_aexp_func n :=
         match n with
         | 0 => base_gen
         | S n' =>
           let binop_gen op := liftGen2 op
                                        (gen_aexp_func n')
                                        (gen_aexp_func n') in
           oneOf [binop_gen APlus ;
                  binop_gen AMinus ;
                  binop_gen AMult;
                  base_gen]
         end
  }.

Derive Arbitrary for bexp.
Derive Arbitrary for com.

(** For convenience, [Show] instances for [aexp], [bexp], and [com]
    have already been defined (in [ImpGen]). These give more
    compact output than the ones that would automatically be
    derived. *)

(** We also need a generator for [mem].  Given the (global) list
    [id_store] of "interesting variables", we generate a list of
    numeric values of the same length and use it to build a function
    from atoms to values; other variables are set to 0. *)

Definition gen_mem : G mem :=
  nat_list <- vectorOf (List.length id_store) arbitrary ;; 
  ret (fun (a : Atom.t) =>
               match (index_of_atom_in_list a id_store) with
               | None => 0
               | Some i =>
                 List.nth i nat_list 0
               end).

Definition show_memory (mem: mem) : string :=
  show_memory_on_domain mem id_store.

(** Next let's define an evaluator for Vminus that stops when a return
    terminator is reached (or when it gets stuck or runs out of
    fuel -- we'll return different results in these cases so that we can
    tell what happened later). *)

Inductive vminus_eval_result :=
| Terminates (st: state): vminus_eval_result
| GoesWrong (s: string): vminus_eval_result
| Timeout : vminus_eval_result.

Fixpoint vminus_eval (g: ListCFG.t) (st : state) (fuel: nat) :
  vminus_eval_result :=
  match fuel with
  | 0 => Timeout
  | S n' =>
    match (ListCFG.fetch g (st_pc st)) with
    | Some instr =>
      if eq_dec_cmd (snd instr) (cmd_tmn tmn_ret) then Terminates st
      else
        match eval_step g st with
        | inr st' => vminus_eval g st' n'
        | inl err => GoesWrong err
        end
    | None => GoesWrong "no instr to fetch"
    end
  end.

(** With generation out of the way, we can now return to checking.
    First, a checker for equality of memories on "interesting
    variables": *)

Fixpoint memory_equal_checker_on_domain
         (dom: list addr) (mem1 mem2 : mem) : Checker :=
  match dom with
  | [] => checker true
  | (a :: l) =>
    if Nat.eqb (mem1 a) (mem2 a) then
      memory_equal_checker_on_domain l mem1 mem2
    else
      whenFail
        ("memory_equal: memory at " ++ (show a)
          ++ " not equal:" ++ " mem1 has " ++ (show_nat (mem1 a))
                           ++ "; mem2 has " ++ (show_nat (mem2 a))
        )%string
        false
  end.

Definition memory_equal_checker := memory_equal_checker_on_domain id_store.

(** Note that we define this operation to return a [Checker] rather
    than a [bool], so that, if we find that the two memories are _not_
    equal, we can stash away a useful error message. *)

(** Now we can assemble the equal-final-state checker for Vminus. *)

Axiom vminus_fuel : nat.
Extract Constant vminus_fuel => "1000".

Definition vminus_final_state_checker
           (g: ListCFG.t) (m m': mem) : Checker :=
  match vminus_eval g (init_state g m) vminus_fuel with
  | Terminates final_state =>
    whenFail "vminus_final_state_checker: memories not equal"
             (memory_equal_checker (st_mem final_state) m')
  | GoesWrong err => 
      whenFail ("vminus_final_state_checker: " ++ err) false
  | Timeout =>
      checker tt  (* discard *)
  end.

(** And now, the [Checker] for the whole correctness property. *)

Definition compile_program_correct_terminating_checker': Checker :=
  forAllShrink arbitrary shrink (fun (c : Imp.com) =>
  forAllShrinkShow gen_mem
                   (fun x => []) 
                   (fun m => show_memory m) 
                   (fun m => 
    let '(g, le, lr) := compile c in
      match imp_eval c m 100 with
      | Some s' =>
        whenFail
          ("cfg is: " ++ show g)
          (vminus_final_state_checker g m s')
      | None => checker tt (* discard the test *)
      end)).


(** There are a few things to note here. *)

(** Firstly, note the use of [forAllShrinkShow] here, which lets us
    choose the specific [Show] we want to use; it is needed here
    because we don't have a [Show] instance for total maps (which are
    essentially functions) like [mem]. *)

(** Secondly, note the use of [checker tt]: This counts the test case
    as a discard, for which we can see the count later. We could have
    used [checker true] to treat the test as a "pass," but then we
    might be falsely reassured if most tests succeed because they just
    hold vacuously. *)

(** And now, let's check it! *)

(*! Extract Constant Test.defNumTests => "20".
    QuickChick compile_program_correct_terminating_checker'. *)

(* ===> 
     +++ Passed 20 tests (7 discards)
*)

(** One thing to note is that we are generating non-terminating Imp
    programs about 1/3 of the time, but the ones that are not
    discarded all pass.
    
    If we start getting too many discards, one way to find out why is
    to change [checker tt] above to fail, so that we can examine the
    counterexamples.

    But for now we can live with the discard rate. *)

(** However, we also notice something else that's more problematic: Running
    20 tests takes 15 seconds!

    On reflection, this is not too surprising, as the grammar contains
    a number of binary nodes and the [size] parameter is treated as a
    bound on _depth_, not total number of nodes.  So our generated
    tests are _huge_.  
    
    Let's see how huge... *)

(** We quickly whack together some functions for calculating
    the sizes of Imp code. *)

Fixpoint size_aexp (a : aexp) :=
  match a with
  | ANum _ => 1
  | AId _ => 1
  | APlus a1 a2 
  | AMinus a1 a2 
  | AMult a1 a2 => size_aexp a1 + size_aexp a2 + 1
  end.

Fixpoint size_bexp (b : bexp) :=
  match b with
  | BTrue | BFalse => 1
  | BEq a1 a2
  | BLe a1 a2 => size_aexp a1 + size_aexp a2 + 1
  | BAnd b1 b2 => size_bexp b1 + size_bexp b2 + 1
  | BNot b => size_bexp b + 1
  end.

Fixpoint size_com (c : com) :=
  match c with
  | SKIP =>
      1
  | (x ::= a) =>
      1 + size_aexp a
  | (c1 ;; c2) =>
      size_com c1 + size_com c2
  | (IFB b THEN c1 ELSE c2 FI) =>
      size_bexp b + size_com c1 + size_com c2
  | (WHILE b DO c END) =>
      size_bexp b + size_com c
  end.
  
(** Now add a [collect]: *)

Definition compile_program_correct_terminating_checker_collect: Checker :=
  forAllShrink arbitrary shrink (fun (c : Imp.com) =>
  collect (size_com c) (
  forAllShrinkShow gen_mem
                   (fun x => []) 
                   (fun m => show_memory m)
                   (fun m => 
    let '(g, le, lr) := compile c in
      match imp_eval c m 100 with
      | Some s' =>
        whenFail
          ("cfg is: " ++ show g)
          (vminus_final_state_checker g m s')
      | None => checker tt 
      end))).

(** Now test: *)

(*! Extract Constant Test.defNumTests => "20".
    QuickChick compile_program_correct_terminating_checker_collect. *)
(* ===>
     6 : 1
     1 : 90
     1 : 8
     1 : 578
     1 : 34
     1 : 322
     1 : 307
     1 : 3
     1 : 2264
     1 : 208
     1 : 2
     1 : 171
     1 : 115
     1 : 11
     1 : 10
     +++ Passed 20 tests (6 discards)
*)

(** Yep, some of these look too big *)

(** To fix this, we can use the [resize] combinator to change the
    maximum size that will be passed to sized generators to something
    other than the default (which is 10). *)

Check resize.
(* ===> 
        resize
         : nat -> G ?A -> G ?A
        where
        ?A : [ |- Type] 
*)

(** Let's set it to 3. *)

Definition compile_program_correct_terminating_checker: Checker :=
  forAllShrink (resize 3 arbitrary) shrink (fun (c : Imp.com) =>
  forAllShrinkShow gen_mem
                   (fun x => []) 
                   (fun m => show_memory m) 
                   (fun m => 
    let '(g, le, lr) := compile c in
      match imp_eval c m 100 with
      | Some s' =>
        whenFail
          ("cfg is: " ++ show g)
          (vminus_final_state_checker g m s')
      | None => checker tt (* discard the test *)
      end)).

(** Now we can run 10000 tests in a few seconds: *)

(*! QuickChick compile_program_correct_terminating_checkers. *)
(* ===>
    +++ Passed 10000 tests (2841 discards)
*)

(** EX2 (GenComWithSmallExpr) *)
(** Add a [collect] to the checker that collects the exact Imp command
    for each test.  Set [defNumTests] to 20 to avoid looking at too
    many examples, and use QuickChick to take a look.  Notice that the
    generated programs tend to be quite short but that they tend to
    involve quite large arithmetic and/or boolean expressions.  This
    distribution may not be giving us the most effective testing.

    Write a generator for [com] that takes a size bound [n] and
    generates commands in which [bexp] and [aexp] expressions have
    size at most [n]. *)
(* FILL IN HERE *)
(** [] *)

(** EX1 (IdentifyDiscards) *)
(** By design of the Checker, we expect discards to be due to non-terminating 
    programs. To investigate this, change the Checker so that "out of fuel" 
    is treated as a failure. Is the counterexample what you expect? Can you 
    be absolutely sure that such counterexamples are due to "out of fuel" 
    rather than because of a genuine bug? *)

(* FILL IN HERE *)
(** [] *)

(* ################################################################# *)
(** * Mutation Testing *)

(** Beyond discarded tests, we are also interested in the tests that
    _pass_.  In particular, we want to make sure that they are passing
    because the property really holds, rather than some oversight in
    generation or formulation of the Checker. To do that, we can
    _mutate_ the compiler to falsify the property and check that the
    Checker fails in this case.

    _Mutation testing_ is a powerful technique for increasing
    confidence in the quality of our tests.  QuickChick comes with a
    command-line tool for mutation testing, but it isn't quite able
    yet to handle the Vminus development.  So for the moment we'll
    just play with mutants manually. *)

(** We've left a suggested mutant in a comment in the [APlus] case of the
    [comp_aexp] function in [Compiler].
    
    Inserting this mutant gives us the following. *)

(*! QuickChick compile_program_correct_terminating_checker. *)
(** ===> 

    QuickChecking compile_program_correct_terminating_checker
    Id 4 := (ANum 60 + ANum 25)
    mem: [(addr 5, 77) (addr 4, 73) (addr 3, 34) 
          (addr 2, 21) (addr 1, 59) ]
    cfg is: (entry 2, blks: lbl 1: []
    vminus_final_state_checker: memories not equal
    memory_equal: memory at Id 4 not equal: mem1 has 35; mem2 has 85
    *** Failed after 67 tests and 31 shrinks. (40 discards)
*)

(** **** Exercise: 2 stars (comp_aexp_minus_mutant)  *)
(** Do the same for the suggested mutant for the [AMinus] case in [comp_aexp].
    Repeat the experiment for a few times. Are the results what you expect? 
    Investigate why. *)

(*! QuickChick compile_program_correct_terminating_checker. *)

(* FILL IN HERE *)
(** [] *)

(** This finishes the testing of the top-level compiler correctness
    property.

    Compare the relative ease of developing this testing
    infrastructure with what's involved in proving the theorem!

    The key part of that proof involves defining a [match_states]
    relation very carefully, and it can take many iterations to get it
    right, both in terms of correctness and sufficiency for the proof
    to go through.  This is on top of making sure that the compiler
    has no bugs.
 
    Testing can help us to quickly pin down bugs in the compiler
    itself, so that we can focus on the proof.  In contrast to the
    proof development, our generators have all been automatically
    derived, and writing the Checker for this is considerably
    simpler. *)

(* ################################################################# *)
(** * Testing Lemmas for Compiler Correctness *)

(** Next, let's look at a property for which the infrastructure needed
    for testing is a bit more elaborate: one of the lemmas that is
    used in proving the top-level correctness theorem... *)

(**

    Lemma comp_aexp_correct : forall (a:aexp),
        comp_correct (comp_aexp a) (aeval a).

where [comp_correct] is Vminus's generic "expression compilation correctness" 
property (used for both arithmetic and boolean expressions)... *)
(**

    Definition comp_correct (comp : FRESH (val * list insn))
               (eval : mem -> nat) : Prop :=
      forall (cs cs': list uid) (g: ListCFG.t) (st: V.Opsem.state)
             (is k: list insn) (v: val), 
   
        (cs', (v, is)) = comp cs ->
        insns_at_pc g (st_pc st) (is ++ k) ->

        exists st',
          (* interesting part: *)
          st_mem st' = st_mem st /\
          insns_at_pc g (st_pc st') k /\
          star (step g) st st' /\ 
          eval_val (st_loc st') v = Some (eval (st_mem st)) /\

          (* details: *)
          ids_preserved cs st st' /\
          good_return cs' v /\
          ctx_incr cs cs'.
*)

(** That is, compiling Imp [aexp] is correct if:
        - for _any compilation_ of some expression run on an initial
          list of [uid]s,
        - wherever we place the compilation _result_ [is] in the
          _CFG_, with the program counter pointing to it ([insns_at_pc
          g (st_pc) (is ++ k)]),
        - _we can run to the end_ of the compiled code and reach a
          state [st'] ([insns_at_pc g (st_pc st') k]), and
        - in this state [st'], the _memory is the same_ as
          above ([st_mem st' = st_mem st]), and
        - _evaluating the result_ of the expression in this
          state ([eval_val (st_loc st') v]) is _exactly the same_ as
          evaluating it according to the Imp state ([eval (st_mem
          st)]).
    
    This last fact may not be obvious from the body of
    [comp_correct]. But note [comp_aexp_correct], which passes Imp's
    [aeval] as the evaluation function.  (This is where the
    coincidence of Imp states and Vminus memory comes into play.)

    There are a few other details that are needed for proving correct
    compilation for [com].  But the above is the crux. *)

(** Looking at [comp_correct], it is clear that we need to generate
    more than just the things we had before. In particular, it would
    seem at first that we need several new generators:
      - [uid]
      - CFG ([ListCFG.t])
      - Vminus states
      - values ([val])

    But note that the only value here, [v], is computed by [comp], so
    we don't actually need a generator for [val].  Moreover, the CFG
    [g] _cannot_ be generated randomly, since it has to satisfy
    [insns_at_pc] -- something that a random CFG is very unlikely to
    do. *)

(** **** Exercise: 2 stars (GenUidInsn)  *)
(** Derive generators and write [Show] instances for [uid] and Vminus [insn].
    Note that it is useful to have custom [Show] instances that are more 
    descriptive than the default ones. *)
(** [] *)

(** For Vminus states, we already have a generator for the [mem]
    component.  A generator and Show for [loc] are defined in
    [OpSemGen], with the following types: *)

Check gen_loc.
(* ===> 
    gen_loc
     : G loc *)

Check show_locals.
(* ===> 
    show_locals
     : loc -> list uid -> string *)

(** We can then define a generator and a [show] function for Vminus
    states, on the fixed domains for [mem] and [loc]. *)

Definition gen_vminus_state : G state :=
  mem <- gen_mem ;;
  pc <- arbitrary ;;
  loc <- gen_loc ;;
  ppc <- arbitrary ;;
  prev_loc <- gen_loc ;;
  ret (mkst mem pc loc ppc prev_loc).

Definition show_vminus_state (st: state) : string :=
  (show_memory (st_mem st) ++ ", " ++
   "pc: " ++ show (st_pc st) ++ ", " ++
   show_locals (st_loc st) ++ ", " ++
   "ppc: " ++ show (st_ppc st) ++ ", " ++
   "prev_loc: " ++ show_locals (st_ploc st))%string.

(** One deficiency of this function is that it only shows [mem] and 
    [loc] on their respective fixed domains. You may find it more useful 
    to have a general one that takes respective domains as input. *) 

(** With these out of the way, we can address the remaining gaps.
       - Firstly, some of the quantities are computed by a function,
         so it is unnecessary to generate them.
       - Secondly, the CFG [g] cannot be just _any_ CFG, but one that
         satisfies [insns_at_pc] for the compilation result.  (Random
         generation in the usual way is extremely unlikely to meet
         this condition, so most checks would end up being vacuously
         true.)
       - Thirdly, a [Checker] for the existence of [st'] really
         needs to compute it.
*)

(** Firstly, let us drop the unnecessary quantified variables.

    Definition comp_correct (comp : FRESH (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (g: ListCFG.t) (k: list insn),
      forall (st: state),

      let (cs', (v, is)) := comp cs in
      insns_at_pc g (st_pc st) (is ++ k) ->

      exists st',
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\ 
        eval_val (st_loc st') v = Some (eval (st_mem st)) /\

        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs'.

    (This is, of course, not accepted by Coq yet.) *)

(** Secondly, we need to write a custom generator that generates CFGs
    satisfying [insns_at_pc]. An easy option is to just construct a
    CFG that places the instructions at a given pc.

    Let us call this [wrap_code_in_cfg' pc is k], in accordance with
    [insns_at_pc g (st_pc st) (is ++ k)].  It returns a CFG with a
    single block containing [is ++ k] placed at (position) [pc]. *)

Definition wrap_code_in_cfg'
              (p: pc) (instrs instrs_after: list insn)
         : ListCFG.t :=
  let empty_cfg := [] in
  let '(lbl, offset) := p in
  let blocks :=
      ListCFG.update empty_cfg lbl
                     ((generate_dummy_insns offset)
                        ++ instrs ++ instrs_after) in
  (lbl, blocks).

(** One fine point is that, because [pc] may have a positive offset
    into the block, we also need [wrap_code_in_cfg'] to fill the
    initial instructions with some dummy instructions (that won't be
    executed). *)

(** Our checkable-lemma-in-progress now looks like this:

    Definition comp_correct (comp : FRESH (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (k: list insn), forall (st: state),

      let (cs', (v, is)) := comp cs in
      let g := wrap_code_in_cfg' (st_pc st) is k in

      exists st',
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\
        eval_val (st_loc st') v = Some (eval (st_mem st)) /\

        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs'.
*)

(** Thirdly, we know that [st'] is given by executing the compilation
    result; this is the point of "loading" the compilation result at
    the current [pc] in [g], and is of course also stated by
    [star (Opsem.step g) st st']. So we need an executable evaluator
    for Vminus. The state [st'] is obtained by running this evaluator
    until we reach (the start of) [k].
    
    The simplest way of doing so is to stop at the program counter
    that begins [k], and this is actually determined by the CFG that
    loaded [is ++ k].

    Hence we change [wrap_code_in_cfg'] to return [(g, pc)], where the
    latter is the [pc] that begins [k]... *)

Definition wrap_code_in_cfg (p: pc) (instrs instrs_after: list insn)
  : ListCFG.t * pc :=
  let empty_cfg := [] in
  let '(lbl, offset) := p in
  let blocks :=
      ListCFG.update
        empty_cfg lbl
        ((generate_dummy_insns offset)
         ++ instrs ++ instrs_after) in
  ((lbl, blocks), (lbl, offset + List.length instrs)).

(** Next we need the evaluator itself (the definitions are in
    [VminusOpSem]). *)

Check eval_until_pc.
(* ===> 
    eval_until_pc
      : ListCFG.t -> state -> pc -> nat -> err state *)

Check eval_step.
(* ===>
    eval_step
     : ListCFG.t -> state -> err state *)

(** Now the lemma is:

    Definition comp_correct (comp : FRESH (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (k: list insn),
      forall (st: state),

      let (cs', (v, is)) := comp cs in
      let (g, endpoint) := wrap_code_in_cfg (st_pc st) is k in

      match eval_until_pc g st cutpoint 1000 with
      | inl err => false (* either out of fuel or no st' *)
      | inr st' => 
          st_mem st' = st_mem st /\
          insns_at_pc g (st_pc st') k /\
          star (Opsem.step g) st st' /\
          eval_val (st_loc st') v = Some (eval (st_mem st)) /\
          ids_preserved cs st st' /\
          good_return cs' v /\
          ctx_incr cs cs' 
      end.
*)

(** At this point, the major obstacles are out of the way; we just
    have to write a [Checker] for the big conjunction. Because it is
    big, it is easier to write a [Checker] for each conjunct rather
    than one monolithic checker.

    That is, we need to define:
      - A [Checker] that checks that two memories are the same. This
        has already been done.
      - A [Checker] that checks for [insns_at_pc].
      - A [Checker] for [ids_preserved].
      - A [Checker] for [good_return].
      - A [Checker] for [ctxt_incr].
      - A [Checker] that checks for equality between the two results
        of evaluation. *)

(** (Note that [star (Opsem.step g) st st'] doesn't need
    checking, because it is implicit in [eval_until_pc].) *)

(** The remaining ones are defined below.  All are fairly
    straightforward. *)

Fixpoint loc_on_domain_checker
         (dom: list uid) (loc1 loc2 : loc) : Checker :=
  match dom with
  | [] => checker true
  | (a :: l) =>
    match loc1 a, loc2 a with
    | Some n1, Some n2 =>
      if Nat.eqb n1 n2 then loc_on_domain_checker l loc1 loc2
      else whenFail "loc_equal: locs disagree" false
    | None, None => loc_on_domain_checker l loc1 loc2
    | _, _ => whenFail "loc_equal: locs disagree" false
    end
  end.

Fixpoint insns_at_pc_checker `{Show pc}
         (g: ListCFG.t) (p: pc) (k : list insn) : Checker :=
  match k with
  | [] => checker true
  | (uid, cmd) :: instrs =>
    match ListCFG.fetch g p with
    | Some (uid', cmd') =>
      if eq_dec_uid uid uid' then
        if eq_dec_cmd cmd cmd' then insns_at_pc_checker g (incr_pc p) instrs
        else whenFail ("insns_at_pc: cmd at pc "
                         ++ (show p) ++ " not equal") false
      else whenFail ("insns_at_pc: uid at pc "
                       ++ (show p) ++ "not equal") false
    | None => whenFail "insns_at_pc: cannot fetch" false
    end
  end.

Definition ids_preserved_checker (cs : list uid) (st st': state)
  : Checker :=
  loc_on_domain_checker cs (st_loc st) (st_loc st').

Definition good_return_checker (cs: list uid) (v: val) : Checker :=
  match v with
  | val_uid uid =>
    whenFail "good_return: cannot find value" 
             (List.existsb
                (fun uid' => if eq_dec_uid uid uid' then true else false) cs)
  | val_nat n => checker true
  end.

Fixpoint ctx_incr_checker (cs cs': list uid) : Checker :=
  match cs with
  | [] => checker true
  | (uid :: uids) =>
    if (List.existsb
          (fun uid' => if eq_dec_uid uid uid' then true else false) cs') then
      ctx_incr_checker uids cs'
    else whenFail ("ctx_incr: " ++ show uid ++ " not found") false
  end.

Definition eval_equal_checker (eval: mem -> nat) (st: state) (v: val)
  : Checker :=
  let run_result := eval_val (st_loc st) v in
  let expected_result := eval (st_mem st) in
  match run_result with
  | Some n =>
    whenFail "eval_equal: evaluation value not the same"
             (Nat.eqb n expected_result)
  | None => whenFail "eval_equal: run did not obtain any value" false
  end.

(** We can now compose all these checkers using QuickChick's [conjoin]
    combinator. *)

Definition expression_step_checker
           (eval: mem -> nat)
           (g: ListCFG.t)
           (initial_state final_state: state)
           (k: list insn) (end_of_expr: pc)
           (cs cs': list uid)
           (v : val) : Checker :=
  conjoin [
      ids_preserved_checker cs initial_state final_state;
      insns_at_pc_checker g end_of_expr k;
      good_return_checker cs' v;
      ctx_incr_checker cs cs';
      eval_equal_checker eval final_state v
    ].

(** At last, we can assemble a checker for [comp_correct] as follows. *)

(** (It is convenient to split the [Checker] into a part that does
    only the generation and a second part that does the checking,
    because a type error can cause the typechecker to get stuck trying
    to resolve the issue by looking for typeclass instances that don't
    exist.) *)

Definition comp_correct_checker_inner
             (comp: FRESH (val * list insn)) (eval: mem -> nat)
             (cs : list uid) (st: state) (k: list insn)
         : Checker :=
  let '(cs', (v, instrs)) := comp cs in
  let '(g, endpoint) := wrap_code_in_cfg (st_pc st) instrs k in
  match eval_until_pc g st endpoint 1000 with
  | inl err => whenFail ("comp_correct_checker: " ++ err) false
  | inr st' => 
    expression_step_checker eval g st st' k endpoint cs cs' v
  end.

Definition comp_correct_checker
             (comp: FRESH (val * list insn)) (eval: mem -> nat)
         : Checker :=
  forAll arbitrary (fun (cs : list uid) =>
  forAll arbitrary (fun (extra_insn : list insn) =>
  forAllShrinkShow gen_vminus_state
                   (fun x => [])
                   show_vminus_state
                   (fun (start_state: state) => 
    comp_correct_checker_inner
      comp eval
      cs start_state extra_insn))).

(** The [comp_aexp] checker is now just a simple wrapper. *)


Definition comp_aexp_correct_checker :=
  forAllShrink (resize 3 arbitrary) shrink (fun a: aexp =>
    comp_correct_checker (comp_aexp a) (aeval a)).

(*! QuickChick comp_aexp_correct_checker. *)
(* ===> 
    QuickChecking comp_aexp_correct_checker
    +++ Passed 10000 tests (0 discards)
*)

(** **** Exercise: 2 stars (add_aexp_mutants)  *)
(** Since the compiler has already been proven correct, we'd expect
    the above test to succeed. However, it could be succeeding for
    silly reasons (because our test-case generation is bad or the
    distribution of tests is skewed in some way), so we'd also like to
    know that the [Checker] indeed fails when the compiler is wrong.

    Change the definition of [compile_aexp] in [Compiler] to
    misbehave in some way (two suggestions can be found in a comment
    there), recompile that file, then come back here and check that
    the QuickChick command above can find the bug. *)

(** **** Exercise: 2 stars (compBopCorrect)  *)
(** Write a Checker for [comp_bop_correct] in [CompilerProp.v], and
    make sure that all tests pass. Next, mutate [comp_bop] in
    [Compiler.v] to do something wrong (a suggestion is provided, but
    again you can make up your own as well), and use QuickChick to
    test the Checker again. Do you get a nice-looking counterexample,
    and can you explain why it fails? *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars (compBexpCorrect)  *)
(** Write a Checker for [comp_bexp_correct] in [CompilerProp.v], and
    make sure that all tests pass. Next, mutate [comp_bexp] in
    [Compiler.v] to do something wrong, and QuickChick your checker
    again. Do you get a useful counterexammple? *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (compStoreCorrect)  *)
(** Write a Checker for [comp_store_correct] in [CompilerProp.v], and
    make sure that all tests pass. Next, mutate [comp_store] in
    [Compiler.v] to do something wrong and QuickChick your Checker
    again.  Are you happy? *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (compCondCorrect)  *)
(** Write a Checker for [comp_cond_correct] in [CompilerProp.v], and
    make sure that all tests pass. Next, mutate [comp_cond] in
    [Compiler.v] to do something wrong and QuickChick your checker
    again. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars (check_type_safety)  *)
(* Build checkers corresponding to the [progress] and [preservation]
   properties in [VminusStatics].  Mutate some of the definitions
   to introduce bugs and see if you can find them. *)
(* FILL IN HERE *)
(** [] *)

