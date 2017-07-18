(** * ImpGen: QuickChick infrastructure for Imp *)

(* ################################################################# *)
(** * In Progress *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import String.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.Atom.
Require Import Vminus.Imp.

Require Import Vminus.AtomGen.

Generalizable All Variables.

(** ** id **)
Definition id_store := get_fresh_atoms 5 [].

Instance gen_id: Gen id :=
  {| arbitrary := gen_fresh id_store |}.

Instance gen_ids: GenSized (list id) :=
  {| arbitrarySized n := returnGen (get_fresh_atoms n []) |}.

Instance shrink_id : Shrink id := {| shrink x := [] |}.

Instance show_id: Show id :=
  {| show x :=
       ("Id "%string ++ (show x) ++ "")%string |}.

(* Sample (@arbitrary id _). *)

(** ** aexp **)

Instance show_aexp: Show aexp :=
  {| show := (
       fix show_aexp_func a :=
           match a with
           | ANum n => "ANum " ++ (show n)
           | AId ident => show ident
           | APlus a1 a2 => "(" ++ (show_aexp_func a1) ++ " + " ++
                               (show_aexp_func a2) ++ ")"
           | AMinus a1 a2 => "(" ++ (show_aexp_func a1) ++ " - " ++
                                (show_aexp_func a2) ++ ")"
           | AMult a1 a2 => "(" ++ (show_aexp_func a1) ++ " * " ++
                               (show_aexp_func a2) ++ ")"
           end)%string
  |}.

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

(*
Instance gen_bexp_with_small_aexp `{GenSized aexp} : GenSized bexp :=
  {| arbitrarySized :=
       fix gen_bexp_func n :=
         match n with
         | 0 => elems [BTrue ; BFalse]
         | S n' =>
           let beq_gen := liftGen2 BEq (arbitrarySized 1) (arbitrarySized 1) in
           let ble_gen := liftGen2 BLe (arbitrarySized 1) (arbitrarySized 1) in
           let bnot_gen := liftGen BNot (gen_bexp_func n') in
           let band_gen := liftGen2 BAnd (gen_bexp_func n') (gen_bexp_func n')
           in
           oneOf [ beq_gen ; ble_gen ; bnot_gen ; band_gen ]
         end
  |}.
*)

(** ** com **)

Open Scope imp_scope.
Instance show_com `{Show aexp} `{Show bexp} : Show com :=
  {| show :=
       fix show_com_func c := (
         match c with
         | CSkip => "Skip"
         | x ::= a => show_nat (Atom.nat_of x) ++ " := " ++ (show a)
         | CSeq c1 c2 => (show_com_func c1) ++ ";" ++ newline ++ (show_com_func c2)
         | CIf b c1 c2 => "If (" ++ (show b) ++ ") then "
                                ++ (show_com_func c1) ++ " else "
                                ++ (show_com_func c2) ++ " endIf"
         | CWhile b c => "While (" ++ (show b) ++ ") do "
                                  ++ (show_com_func c) ++ " endWhile"
         end)%string
  |}.

(*
Instance gen_seq_and_assgn_com `{Gen id} `{Gen aexp} `{Gen bexp} : GenSized com :=
  {| arbitrarySized :=
       fix com_gen_func n :=
         match n with
         | 0 => liftGen2 CAss arbitrary arbitrary
         | S n' =>
           let gen := com_gen_func n' in
           liftGen2 CSeq gen gen
         end
  |}.
*)

(*
Instance gen_if_com `{Gen id} `{Gen aexp} `{Gen bexp} : GenSized com :=
  {| arbitrarySized :=
       fix com_gen_func n :=
         match n with
         | 0 => freq [(2, returnGen CSkip) ;
                       (6, liftGen2 CAss arbitrary arbitrary)]
         | S n' =>
           let gen := com_gen_func n' in
           oneOf [liftGen3 CIf arbitrary gen gen; liftGen2 CSeq gen gen]
         end
  |}.
 *)

(** EX: Write a generator that generates only IF-THEN-ELSE ... *)

(* Sample (@arbitrarySized com gen_if_com 2). *)

(** ** imp_state **)

Record imp_state : Type := mk_imp_state { imp_st: state; imp_dom: list Atom.t }.

Definition gen_state_from_atom_list
           `{Gen nat}
           (atom_list : list Atom.t) : G state :=
  bindGen (vectorOf (List.length atom_list) arbitrary) (fun nat_list => 
  returnGen (fun (a : Atom.t) =>
               match (index_of_atom_in_list a atom_list) with
               | None => 0
               | Some i =>
                 List.nth i nat_list 0
               end)).
 
Instance gen_imp_state : GenSized imp_state :=
  {| arbitrarySized n :=
       let mem_dom := get_fresh_atoms n [] in
       let gmem := gen_state_from_atom_list mem_dom in
       bindGen gmem (fun mem =>
         returnGen (mk_imp_state mem mem_dom))
  |}.

Definition show_image_given_domain `{Show A}
           (f: Atom.t -> A) (l: list Atom.t) 
           (prefix: string) : string := 
  ((List.fold_left
      (fun accum atom =>
         accum ++ "(" ++ prefix ++ " " ++ (show atom) ++ ", "
               ++ show (f atom) ++ ") ")
      l "[") ++ "]")%string.
                   
Instance show_imp_state: Show imp_state :=
  {| show x :=
     "imp_state: " ++ (show_image_given_domain (imp_st x)
                                               (imp_dom x) "")
  |}.
