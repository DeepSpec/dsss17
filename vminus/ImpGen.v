(** * ImpGen: QuickChick infrastructure for Imp *)

(* ################################################################# *)
(** * In Progress *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import String.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.QC.
Require Import Vminus.Atom.
Require Import Vminus.Imp.

Require Import Vminus.AtomGen.

Generalizable All Variables.

(** ** id **)
Definition id_store := get_fresh_atoms 5 [].

Definition gen_id := gen_fresh id_store.

Instance shrink_id : Shrink id := {| shrink x := [] |}.

Instance show_id: Show id :=
  {| show x :=
       ("Id "%string ++ (show (Atom.nat_of x)) ++ "")%string |}.

(* Sample (@arbitrary id _). *)

(** ** aexp **)

Instance show_aexp: Show aexp :=
  {| show := (
       fix show_aexp_func a :=
           match a with
           | ANum n => "ANum " ++ (show_nat n)
           | AId ident => "Id " ++ show_nat (Atom.nat_of ident)
           | APlus a1 a2 => "(" ++ (show_aexp_func a1) ++ " + " ++
                               (show_aexp_func a2) ++ ")"
           | AMinus a1 a2 => "(" ++ (show_aexp_func a1) ++ " - " ++
                                (show_aexp_func a2) ++ ")"
           | AMult a1 a2 => "(" ++ (show_aexp_func a1) ++ " * " ++
                               (show_aexp_func a2) ++ ")"
           end)%string
  |}.

Derive Arbitrary for aexp.

(** ** bexp **)

Derive Show for bexp.

Instance show_bexp: Show bexp :=
  {| show :=
       fix show_bexp_func b := (
         match b with
         | BTrue => "true" 
         | BFalse => "false"
         | BEq a1 a2 => (show a1) ++ " = " ++ (show a2)
         | BLe a1 a2 => (show a1) ++ " <= " ++ (show a2)
         | BNot b => "~(" ++ (show_bexp_func b) ++ ")"
         | BAnd b1 b2 => (show_bexp_func b1) ++ " /\ " ++ (show_bexp_func b2)
         end)%string
  |}.

Derive Arbitrary for bexp.

(** ** com **)

Open Scope imp_scope.
Instance show_com `{Show aexp} `{Show bexp} : Show com :=
  {| show :=
       fix show_com_func c := (
         match c with
         | CSkip => "SKIP"
         | x ::= a => "Id " ++ show_nat (Atom.nat_of x) ++ " := " ++ (show a)
         | CSeq c1 c2 =>
           (show_com_func c1) ++ "; " ++ (show_com_func c2)
         | CIf b c1 c2 => "IFB " ++ (show b) ++ " THEN "
                                ++ (show_com_func c1) ++ " ELSE "
                                ++ (show_com_func c2) ++ " FI "
         | CWhile b c => "WHILE " ++ (show b) ++ " DO "
                                  ++ (show_com_func c) ++ " END"
         end)%string
  |}.

Remove Hints genSaexp : typeclass_instances.
Remove Hints genSbexp : typeclass_instances.