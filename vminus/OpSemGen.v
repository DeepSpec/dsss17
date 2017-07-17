Require Import List.
Import ListNotations.
Require Import String.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

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

Definition show_memory
           (mem: mem) (dom: list Atom.t) : string :=
  "mem: " ++ (show_image_given_domain mem dom "addr").

Definition show_locals
           (loc: loc) (dom: list Atom.t): string :=
  "locals: " ++ (show_image_given_domain loc dom "uid").


(*
Record vminus_state : Type :=
  mk_vminus_state {
    vst_mem: mem;
    vst_mem_dom: list Atom.t;
    vst_pc: pc;
    vst_loc: loc;
    vst_loc_dom: list Atom.t;
    vst_ppc: pc;
    vst_ploc: loc;
    vst_ploc_dom: list Atom.t
  }.
*)

Definition gen_loc_from_atom_list
           (atom_list : list Atom.t) : G loc :=
  bindGen (vectorOf (List.length atom_list) arbitrary) (fun nat_list =>
  returnGen (fun (a : Atom.t) =>
               match (index_of_atom_in_list a atom_list) with
               | None => None
               | Some i =>
                 List.nth_error nat_list i
               end)).

Definition gen_mem_from_atom_list
           (atom_list : list Atom.t) : G mem :=
  bindGen (vectorOf (List.length atom_list) arbitrary) (fun nat_list =>
  returnGen (fun (a : Atom.t) =>
               match (index_of_atom_in_list a atom_list) with
               | None => 0
               | Some i =>
                 List.nth i nat_list 0
               end)).

(*
Definition gen_opsem_vminus_state: GenSized vminus_state :=
  {| arbitrarySized n :=
       let mem_dom := get_fresh_atoms n [] in
       let loc_dom := get_fresh_atoms n [] in
       let gmem := gen_mem_from_atom_list mem_dom in
       let gloc := gen_loc_from_atom_list mem_dom in

       bindGen gmem (fun mem =>
       bindGen arbitrary (fun pc =>
       bindGen gloc (fun loc =>
       bindGen arbitrary (fun ppc =>
       bindGen gloc (fun prev_loc =>
         returnGen
           (mk_vminus_state mem mem_dom
                            pc
                            loc loc_dom
                            ppc
                            prev_loc loc_dom))))))
  |}.

Instance show_vminus_state `{Show pc} : Show vminus_state :=
  {| show st :=
       let 'mk_vminus_state mem mem_dom
                            pc
                            loc loc_dom
                            ppc
                            prev_loc prev_loc_dom := st in
       (show_memory mem mem_dom ++ ", " ++
        "pc: " ++ show pc ++ ", " ++
        show_locals loc loc_dom ++ ", " ++
        "ppc: " ++ show ppc ++ ", " ++
        "prev_loc: " ++
        show_locals prev_loc prev_loc_dom)%string
  |}.

Definition vst_to_state (vst: vminus_state) :=
  mkst (vst_mem vst) (vst_pc vst) (vst_loc vst)
               (vst_ppc vst) (vst_ploc vst).
*)

(*
Fixpoint generate_dummy_insns (n : nat) : list insn :=
  let fixed_addr := Atom.fresh [] in
  let fixed_uid := Atom.fresh [] in
  match n with
  | 0 => []
  | S n' =>
    (fixed_uid, cmd_load fixed_addr) :: generate_dummy_insns n'
  end.
 *)

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

(* TODO: proper generator *)
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