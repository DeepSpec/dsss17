(** * OpSemGen: Testing Operational Semantics *)

(* ################################################################# *)
(** * Placeholder *)

Require Import List.
Import ListNotations.
Require Import String.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.QC.

Require Import Vminus.Atom.
Require Import Vminus.Vminus.
Require Import Vminus.CFG.
Require Import Vminus.ListCFG.

Require Import Vminus.AtomGen.
Require Import Vminus.VminusGen.

Require Import Vminus.VminusOpSem. (* More refactoring work to do *)
Import V.Opsem.

Generalizable All Variables.

Definition show_image_given_domain `{Show A}
           (f: Atom.t -> A) (l: list Atom.t) 
           (prefix: string) : string := 
  ((List.fold_left
      (fun accum atom =>
         accum ++ "(" ++ prefix ++ " " ++ (show atom) ++ ", "
               ++ show (f atom) ++ ") ")
      l "[") ++ "]")%string.
                   
(** Opsem **)
Definition locals_store := get_fresh_atoms 10 [].

Definition show_memory_on_domain
           (mem: mem) (dom: list Atom.t) : string :=
  "mem: " ++ (show_image_given_domain mem dom "addr").

Definition show_locals_on_domain
           (loc: loc) (dom: list Atom.t): string :=
  "locals: " ++ (show_image_given_domain loc dom "uid").

Definition show_locals
           (loc: loc): string := show_locals_on_domain loc locals_store.

Definition gen_loc_with_domain
           (atom_list : list Atom.t) : G loc :=
  nat_list <- vectorOf (List.length atom_list) arbitrary ;;
  ret (fun (a : Atom.t) =>
         match (index_of_atom_in_list a atom_list) with
         | None => None
         | Some i =>
           List.nth_error nat_list i
         end).

Definition gen_loc := gen_loc_with_domain locals_store.

Definition gen_mem_with_domain
           (atom_list : list Atom.t) : G mem :=
  nat_list <- vectorOf (List.length atom_list) arbitrary ;;
  ret (fun (a : Atom.t) =>
         match (index_of_atom_in_list a atom_list) with
         | None => 0
         | Some i =>
           List.nth i nat_list 0
         end).

Definition generate_dummy_insns n: list insn :=
  let atoms := (get_fresh_atoms n []) in
  let nth_atom n := nth n atoms (Atom.fresh []) in
  let fix helper k :=
      match k with
      | 0 => []
      | S k' =>
        (nth_atom k, cmd_load (nth_atom k)) :: (helper k')
      end
  in List.rev (helper n).

(* Returns a CFG with a single block containing instrs ++ instrs_after, 
    and the pc in that block that begins at instrs_after *)
Definition wrap_code_in_cfg (p: pc) (instrs instrs_after: list insn)
  : ListCFG.t * pc :=
  let empty_cfg := [] in
  let '(lbl, offset) := p in
  let blocks :=
      ListCFG.update empty_cfg lbl
                     ((generate_dummy_insns offset)
                        ++ instrs ++ instrs_after) in
  ((lbl, blocks), (lbl, offset + List.length instrs)).