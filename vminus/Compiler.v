(* * Compiler: An Imp to Vminus Compiler *)
(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


(** Imports, instantiated with the list implementation of 
    control-flow graphs. *)

Require Import List.
Import ListNotations.

Require Import Vminus.Classes Vminus.Imp Vminus.Vminus.
Require Import Vminus.CFG.
Require Import Vminus.ListCFG.
Import ListCFG.


(* ################################################################# *)
(** * Imp to Vminus Compiler *)

(** This file implements a compiler from a (slight variant of) the Software
Foundations Imp language (see [Imp.v]) to Vminus.  Importantly, this variant of
Imp and the Vminus language share the same notion of global, mutable memory
states, so the compilation of Imp identifiers into Vminus addresses is trivial.
*)

(** The compiler and its correctness proof demonstrate the use of
_monotonic state_---essentially the idea that the compiler only "extends" the
state, either by generating new fresh identifiers.

For the sake of simplicity, this compiler doesn't perform any optimizations.  It
uses a straightforward strategy of translating each Imp assignment command to a
separate Vminus block, which makes stating the correctness invariants easier, at
the expense of generating poor straight-line code.

The compiler will also serve as a vehicle for exploring QuickChick testing.

*)

(**  ------------------------------------------------------------------------- *)
(** *** An example of translating Imp to Vminus:

An Imp program:

[IFZ Z THEN X ::= 1;; Y ::= 2 ELSE SKIP]

And one possible translation to Vminus:


l0:
  %z = load Z
  cbr %z l1 l3

l1:           // block for X ::= 1
  store X 1
  br l2

l2:           // block for Y ::= 2
  store Y 2
  br l3

l3:
  ret


*)


(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * The Compilation Monad *)

(** One issue in building a compiler that targets an SSA language like
Vminus is generating the identifiers used for labels and local variables.  A key
part of the correctness proof will be establishing the freshness and uniqueness
properties of these identifiers.
 *)
(** The [FRESH] monad provides a compilation context for expressions and commands.
    [FRESH] is just a state monad in which the state keeps track of the list of
    generated uids so that we can generate fresh names.  *)

Notation FRESH := (ST (list uid)).

(** A monad operation that generates a unique identifer [uid]. Note that the the
[Atom] library guarantees that [uid] is distinct from any element of [ids]. *)

Definition fresh : FRESH uid :=
  fun ids =>
  let uid := Uid.fresh ids in
  (uid::ids, uid).

(** We can _run_ the monad computation starting from any initial list of uids
that should be avoided. *)

Definition strun {A:Set} (m:FRESH A) (l:list uid) : A :=
  snd (m l).

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Compiling binops. *)

(** The result of compiling an expression is a Vminus value that stores the
result, plus a sequence of intructions (if any) needed to compute that value.  *)

(** We can factor all of the shared code for compiling binary operations into a
monadic combinator. It first compiles the left expression, then the right
expression. Then it generates a fresh local identifier that will hold the
computed result.  The instruction sequence concatenates the code for the two
subexpressions and appends the instruction that performs the binary
operation. *)


Definition comp_bop
             (b:bop) (e1 e2: FRESH (val * list insn))
           : FRESH (val * list insn) :=
  '(v1, c1) <- e1;
  '(v2, c2) <- e2;
  'r <- fresh;
(*!*)
  mret (val_uid r, (c1 ++ c2 ++ [(r, cmd_bop b v1 v2)])) 
(*!
  mret (val_uid r, (c2 ++ c1 ++ [(r, cmd_bop b v2 v1)])) 
*)
.

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Compiling arithmetic expressions. *)

(** The translation of an Imp [aexp] is mostly handled by [comp_bop].

The only interesting case is that for compiling Imp identifiers.
However, since the Imp global state and Vminus global state are the
same, we simply translate a reference to an Imp identifier into a load
from that identifier, treated as an address. *)

Fixpoint comp_aexp (a:aexp) : FRESH (val * list insn) :=
  match a with
    | ANum n => mret (val_nat n, [])
    | AId i => 'r <- fresh; mret (val_uid r, [(r, cmd_load i)])
(*!*)
    | APlus a1 a2 => comp_bop bop_add (comp_aexp a1) (comp_aexp a2)
    (*! | APlus a1 a2 => comp_bop bop_sub (comp_aexp a1) (comp_aexp a2) *)
(*!*)
    | AMinus a1 a2 => comp_bop bop_sub (comp_aexp a1) (comp_aexp a2) 
    (*! | AMinus a1 a2 => comp_bop bop_sub (comp_aexp a1) (comp_aexp a1) *)
    | AMult a1 a2 => comp_bop bop_mul (comp_aexp a1) (comp_aexp a2)
  end.

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Compiling boolean expressions. *)


(** Vminus doesn't have booleans, it has only natural numbers, so we have
to translate Imp values [BTrue] and [BFalse] to [val_nat 1] and [val_nat 0]
respectively.

Vminus does not have any unary operations, so logical negation translates into a
comparison with [0].
*)

Fixpoint comp_bexp (b:bexp) : FRESH (val * list insn) :=
  match b with
    | BTrue => mret (val_nat 1, [])
    | BFalse => mret (val_nat 0, [])
    | BEq a1 a2 => comp_bop bop_eq (comp_aexp a1) (comp_aexp a2)
    | BLe a1 a2 => comp_bop bop_le (comp_aexp a1) (comp_aexp a2)
    | BAnd b1 b2 => comp_bop bop_and (comp_bexp b1) (comp_bexp b2)
(*!*)
    | BNot b1 => comp_bop bop_eq (comp_bexp b1) (mret (val_nat 0, []))

    (*! | BNot b1 => comp_bop bop_eq (comp_bexp b1) (mret (val_nat 1, [])) *)

  end.

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Command compilation strategy *)

(** To compile Imp commands to Vminus, observe that a single Imp command
such as [IFZ] or [WHILE] will translate into a collection of Vminus basic
blocks.  Therefore the command compiler will need to produce that list of
blocks, as well as have the infrastructure provide a mechanism for indicating
how the blocks should be connected to form a control-flow graph.

For this compiler, we've chosen to follow the invariant that when translating an
Imp command [c], the compiler receives the label of the _continuation block_ to
which control should pass after executing the code corresponding to [c].  The
_output_ of the command compiler is a label that designates the entry block of
the command.  These choices inform the structure of the compiler, which
traverses the Imp program from right-to-left, threading the control as required.

Another consequence of this decision is that the easiest way to compile
assignment commands is to place each such command into its own basic block.
This simplifies the compiler invariants (since we don't have to keep track of
"partially completed" blocks, and (as we will see) makes relating the Imp
operational semantics to the Vminus semantics of the compiler output.

There are alternatives that could produce "nicer" Vminus code (e.g. by placing
sequences of assignment commands into the same basic block, or by traversing the
Imp program left-to-right), but those alternatives would have a significant
impact on the simulation relation between the source Imp and target Vminus code.

Note: This compilation strategy also does not introduce phi nodes into the
generated code.  This design is in-line with the usual way of compiling an
imperative language to a language like Vminus (or LLVM).  Introduction of phi
nodes is done as a later phase in the compiler, sometimes called "register
promotion".

*)

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Compiling [store] commands and conditional branches *)

(** Before diving into the full compiler, it is useful to create two helper
functions, each of which is responsible for generating code that corresponds to
the last half of a basic block.
*)

(** [comp_store] emits code that computes an arithmetic expression [a] and
stores the result into the address [v].  The [k] argument is the "continuation
label" that is jumped to following the [store].  *)

Definition comp_store (a:aexp) (v:addr) (k:lbl) : FRESH (list insn) :=
  'x <- fresh;
  'y <- fresh;
  '(i, is) <- comp_aexp a; 
(*!*)
  mret (is ++ [ (x, cmd_store v i); 
                  (y, cmd_tmn (tmn_jmp k)) ])
(*! mret (is ++ [ (x, cmd_store v i); 
                (y, cmd_tmn (tmn_jmp x)) ]) *)
.

(** Similarly, [comp_cond] generates the instructions leading up to a
conditional branch.  It takes two continuation labels, one for each branch.  *)

Definition comp_cond (b:bexp) (l1 l2:lbl) : FRESH (list insn) :=
  '(v, is) <- comp_bexp b;
  'x <- fresh;
(*!*)
  mret (is ++ [ (x, cmd_tmn (tmn_cbr v l1 l2)) ] )
(*!  mret (is ++ [ (x, cmd_tmn (tmn_cbr v l2 l1)) ] ) *)
.

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Compiling Imp Commands *)

(** Just as we needed to thread the list of generated identifiers through the
expression compiler, we also need to maintain some state when compiling
commands.
  
  - list of used block labels

  - list of used uids

  - list of blocks making up the "current" control-flow graph, to which new
    blocks will be added

 *)

(** We define another monad, called [CMD] that, in addition to letting us
generate fresh local identifiers, also keeps track of block labels and generated
blocks.  *)

Definition cstate := (list lbl * list uid * list block)%type.
Notation CMD := (ST cstate).

(** Generate a fresh block label *)

Definition fresh_lbl : CMD lbl :=
  fun cs =>
  let '(ls, is, bs) := cs in
  let l := Lbl.fresh ls in 
  (l::ls, is, update bs l [], l).

(** Lift a computation from the [FRESH] monad into the [CMD] monad. *)

Definition liftF {T} (ec:FRESH T) : CMD T :=
  fun cs =>
  let '(ls, is, cfg) := cs in
  let (is', r) := ec is in
  (ls, is', cfg, r).

(** Update the instructions at the block with lbl [l] to have the list of instructions [b] *)

Definition add_insns (l:lbl) (b:list insn) : CMD unit :=
  fun cs =>
  let '(ls, is, cfg) := cs in
  (ls, is, update cfg l b, tt).

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Compiling Imp Commands *)

(** The input [lr] is the "continuation" label of the block to which control
    should return after the command is done.  The output is the label of the
    entry block for the command. 

    Note how compiling a sequence [[c1;;c2]] threads the control through the 
    commands in reverse order.
*)

Fixpoint comp_com (c:Imp.com) (lr:lbl) : CMD lbl :=
  match c with
    | CSkip => mret lr
    | CAss i a => 
        'l <- fresh_lbl;
        'b <- liftF (comp_store a i lr);
        '_ <- add_insns l b;
        mret l
    | CSeq c1 c2 =>
        'l <- comp_com c2 lr; comp_com c1 l
    | CIf b c1 c2 =>
        'l1 <- comp_com c1 lr;
        'l2 <- comp_com c2 lr;
        'lh <- fresh_lbl;
        'b  <- liftF (comp_cond b l1 l2);
        '_  <- add_insns lh b;
        mret lh
    | CWhile b c => 
        'lh <- fresh_lbl;
        'lb <- comp_com c lh;
        'b  <- liftF (comp_cond b lb lr);
        '_  <- add_insns lh b;
        mret lh
  end.

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Top-level Compiler *)

(** To turn an Imp command into a full Vminus program, we need to provide the
command compiler with the label of the "initial continuation", which is just the
label of a block that immediately halts the program by executing the [tmn_ret]
instruction.  The result of the program is a pair of labels, [e] for the entry
point (obtained by compiling the command [c]), and the exit label [r].

*)

Definition comp_prog (c:com) : CMD (lbl * lbl) :=
  'r <- fresh_lbl;
  'x <- liftF fresh;
  '_ <- add_insns r [(x, cmd_tmn tmn_ret)];
  'e <- comp_com c r;
  mret (e, r).

(** We can "run" a computation the [CMD] monad by supplying it with empty lists
of uids, labels, and blocks.  The result is easy to package up as ListCFG
control-flow graph.  *)

Definition compile (c:com) : ListCFG.t * lbl * lbl :=
  let '(_, _, bs, (le, lr)) := comp_prog c ([], [], []) in
    ((le, bs), le, lr).
