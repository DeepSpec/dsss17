(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


(* ################################################################# *)
(** * Imp to Vminus Compiler *)

(** Imports, instantiated with the list implementation of
    control-flow graphs. *)

Require Import List.
Import ListNotations.

Require Import Vminus.Classes Vminus.Imp Vminus.Vminus.
Require Import Vminus.CFG.
Require Import Vminus.ListCFG.
Import ListCFG.

(* ################################################################# *)
(** * Compiling Expressions *)

(** Compilation context for expressions.  The state monad keeps track
    of the list of generated uids so that we can generate fresh names. *)

Notation ectmon := (ST (list uid)).

(** Generate a fresh uid. *)

Definition fresh : ectmon uid :=
  fun is =>
  let i := Uid.fresh is in
  (i::is, i).

Definition strun {A:Set} (m:ectmon A) (l:list uid) : A :=
  snd (m l).

(* ================================================================= *)
(** ** Compiling binops. *)

(** Compile a general binary operation. *)

(*! Section comp_bop *)

Definition comp_bop (b:bop) (e1 e2: ectmon (val * list insn)) : ectmon (val * list insn) :=
  '(v1, c1) <- e1;
  '(v2, c2) <- e2;
  'r <- fresh;
  mret (val_uid r, (c1 ++ c2 ++ [(r, cmd_bop b v1 v2)])).

(** Compile an arithmetic expression. *)

(*! Section comp_aexp *)

Fixpoint comp_aexp (a:aexp) : ectmon (val * list insn) :=
  match a with
    | ANum n => mret (val_nat n, [])
    | AId i => 'r <- fresh; mret (val_uid r, [(r, cmd_load i)])
    | APlus a1 a2 => (*!*)comp_bop bop_add (comp_aexp a1) (comp_aexp a2)
                    (*! comp_bop bop_add (comp_aexp a1) (comp_aexp a1) *)
    | AMinus a1 a2 => (*! *) comp_bop bop_sub (comp_aexp a1) (comp_aexp a2)
                     (*! comp_bop bop_sub (comp_aexp a1) (comp_aexp a1) *)
    | AMult a1 a2 => (*! *) comp_bop bop_mul (comp_aexp a1) (comp_aexp a2)
                    (*! comp_bop bop_mul (comp_aexp a1) (comp_aexp a1) *)
  end.

(* ================================================================= *)
(** ** Compiling boolean expressions. *)

(*! Section comp_bexp *)
Fixpoint comp_bexp (b:bexp) : ectmon (val * list insn) :=
  match b with
    | BTrue => (*! *) mret (val_nat 1, []) (*! ret (val_nat 0, []) *)
    | BFalse => mret (val_nat 0, [])
    | BEq a1 a2 => comp_bop bop_eq (comp_aexp a1) (comp_aexp a2)
    | BLe a1 a2 => (*! *) comp_bop bop_le (comp_aexp a1) (comp_aexp a2)
                  (*! comp_bop bop_le (comp_aexp a1) (comp_aexp a1) *)
    | BAnd b1 b2 => (*!*) comp_bop bop_and (comp_bexp b1) (comp_bexp b2)
                   (*! comp_bop bop_and (comp_bexp b1) (comp_bexp b1) *)
    | BNot b1 => (*!*) comp_bop bop_eq (comp_bexp b1) (mret (val_nat 0, []))
                (*! comp_bop bop_eq (comp_bexp b1) (ret (val_nat 1, [])) *)
  end.



Definition comp_store (a:aexp) (v:addr) (lr:lbl) : ectmon (list insn) :=
  'x <- fresh;
  'y <- fresh;
  '(i, is) <- comp_aexp a;
  mret (is ++ [ (x, cmd_store v i);
               (y, cmd_tmn (tmn_jmp lr)) ]).

Definition comp_cond (b:bexp) (l1 l2:lbl) : ectmon (list insn) :=
  '(v, is) <- comp_bexp b;
  'x <- fresh;
  mret (is ++ [ (x, cmd_tmn (tmn_cbr v l1 l2)) ] ).

(* ================================================================= *)
(* ** Compiling Commands *)

(** State:
    - list of used block labels
    - list of used uids
    - current cfg *)

Definition cstate := (list lbl * list uid * list block)%type.
Notation ctmon := (ST cstate).

Definition fresh_lbl : ctmon lbl :=
  fun cs =>
  let '(ls, is, bs) := cs in
  let l := Lbl.fresh ls in
  (l::ls, is, update bs l [], l).

Definition raise_ectmon {T} (ec:ectmon T) : ctmon T :=
  fun cs =>
  let '(ls, is, cfg) := cs in
  let (is', r) := ec is in
  (ls, is', cfg, r).

Definition add_insns (l:lbl) (b:list insn) : ctmon unit :=
  fun cs =>
  let '(ls, is, cfg) := cs in
  (ls, is, update cfg l b, tt).

(** The input [lr] is the label of the block to which
    control should return after the command is done.
    The output is the label of the entry block for the
    command. *)

Fixpoint comp_com (c:Imp.com) (lr:lbl) : ctmon lbl :=
  match c with
    | CSkip => mret lr
    | CAss i a =>
        'l <- fresh_lbl;
        'b <- raise_ectmon (comp_store a i lr);
        '_ <- add_insns l b;
        mret l
    | CSeq c1 c2 =>
        'l <- comp_com c2 lr; comp_com c1 l
    | CIf b c1 c2 =>
        'l1 <- comp_com c1 lr;
        'l2 <- comp_com c2 lr;
        'lh <- fresh_lbl;
        'b  <- raise_ectmon (comp_cond b l1 l2);
        '_  <- add_insns lh b;
        mret lh
    | CWhile b c =>
        'lh <- fresh_lbl;
        'lb <- comp_com c lh;
        'b  <- raise_ectmon (comp_cond b lb lr);
        '_  <- add_insns lh b;
        mret lh
  end.

Definition comp_prog (c:com) : ctmon (lbl * lbl) :=
  'r <- fresh_lbl;
  'x <- raise_ectmon fresh;
  '_ <- add_insns r [(x, cmd_tmn tmn_ret)];
  'e <- comp_com c r;
  mret (e, r).

(* TODO: le is redundant ... fix up match_config *)
Definition compile (c:com) : ListCFG.t * lbl * lbl :=
  let '(_, _, bs, (le, lr)) := comp_prog c ([], [], []) in
    ((le, bs), le, lr).
