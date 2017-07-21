Require Import Arith.
Require Import List.
Import ListNotations.

Require Import Vminus.Classes.
Require Import Vminus.Util.
Require Import Vminus.Atom.
Require Import Vminus.Env.
Require Import Vminus.Imp.
Require Import Vminus.Vminus.
Require Import Vminus.CFG.
Require Import Vminus.ListCFG.
Require Import Vminus.Dom.
Require Import Vminus.VminusOpSem.
Require Import Vminus.VminusStatics.
Require Import Vminus.Compiler.
Require Import Vminus.VminusGen.
Import V.Opsem.
Set Bullet Behavior "Strict Subproofs".

Module VS := MakeStatics(ListCFG).
Import VS.Typing.

Open Scope imp_scope.

Notation X := (Atom.fresh []).
Notation Y := (Atom.fresh [X]).
Notation Z := (Atom.fresh [Y;X]).
Notation id1 := (Atom.fresh [Z;Y;X]).
Notation id2 := (Atom.fresh [id1;Z;Y;X]).
Notation id3 := (Atom.fresh [id2;id1;Z;Y;X]).
Notation id4 := (Atom.fresh [id3;id2;id1;Z;Y;X]).
Notation id5 := (Atom.fresh [id4;id3;id2;id1;Z;Y;X]).

Eval compute in (Atom.nat_of X).

Require Import QuickChick.QuickChick.

Example imp_ex1 := IFB (BEq (AId Z) (ANum 0)) THEN X ::= (ANum 1) ;; Y ::= (ANum 2) ELSE SKIP FI.

Eval compute in (compile imp_ex1).

Example imp_ex2 := WHILE BTrue DO SKIP END.
Eval compute in (compile imp_ex2).


(** **** Exercise: 2 stars (Example Compiler Output)  *)
(**   Define a ListCFG program that corresponds to the following Vminus code.
Vminus code:


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

Definition l0 := Atom.fresh [].
Definition l1 := Atom.fresh [l0].
Definition l2 := Atom.fresh [l0; l1].
Definition l3 := Atom.fresh [l0; l1; l2].
Definition z := Atom.fresh [l0; l1; l2; l3].
Definition Z' := Atom.fresh [l0; l1; l2; l3; z].
Definition X' := Atom.fresh [l0; l1; l2; l3; z; Z'].
Definition Y' := Atom.fresh [l0; l1; l2; l3; z; Z'; X'].
Definition temp1 := Atom.fresh [l0; l1; l2; l3; z; Z'; X'; Y'].
Definition temp2 := Atom.fresh [l0; l1; l2; l3; z; Z'; X'; Y'; temp1].
Definition temp3 := Atom.fresh [l0; l1; l2; l3; z; Z'; X'; Y'; temp1;
                                  temp2].
Definition temp4 := Atom.fresh [l0; l1; l2; l3; z; Z'; X'; Y'; temp1;
                                  temp2; temp3].
Definition temp5 := Atom.fresh [l0; l1; l2; l3; z; Z'; X'; Y'; temp1;
                                  temp2; temp3; temp4].
Definition temp6 := Atom.fresh [l0; l1; l2; l3; z; Z'; X'; Y'; temp1;
                                  temp2; temp3; temp4; temp5].

(** Replace the [ ] in the definition below to create the Vminus representation
of the CFG above: *)

Definition vm_code : ListCFG.t :=
(* FILL IN HERE *)
(l0, []).

(** **** Exercise: 4 stars (vm_code_wf)  *)
(** Prove the following lemmas to show that your definition 
    of [vm_code] is a well-formed Program. *)

(** Prove that the code is a well formed CFG. *)
Lemma vm_code_wf_cfg : ListCFG.wf_cfg vm_code.
Proof.
  (* FILL IN HERE *) Admitted.
      

(** Prove that the instructions are well formed. *)
Lemma vm_code_wf_insn : forall (p : pc) (i : insn),
    ListCFG.insn_at_pc vm_code p i -> wf_insn vm_code i p.
Proof.
  (* FILL IN HERE *) Admitted.


(** Prove that the terminators are well formed. *)
Lemma vm_code_wf_tmn : forall (p' : pc) (i : insn),
    ListCFG.tmn_pc vm_code p' -> ListCFG.insn_at_pc vm_code p' i -> is_tmn i.
Proof.
  (* FILL IN HERE *) Admitted.


(** Prove that the entry block is well formed. *)
Lemma vm_code_wf_entry : forall (p :pc),
    ~ succ_pc vm_code p (block_entry (ListCFG.entry_block vm_code)).
Proof.
  (* FILL IN HERE *) Admitted.

Print ListCFG.

Lemma wf_insn_induct :
  forall l1 bls i p a,
  wf_insn (l1, bls) i p -> wf_insn (l1, a) i p -> wf_insn (l1, bls ++ a) i p.
Proof.
  Admitted.
    
Lemma wf_prog_induct :
  forall l1 bls a
    (Hwfl: wf_prog (l1, bls))
    (Hwfcfg: ListCFG.wf_cfg (l1, bls++a)) 
    (Hwfins: forall (p : pc) (i : insn), ListCFG.insn_at_pc (l1, a) p i -> wf_insn (l1, a) i p)
    (Hwftmn: forall (p' : pc) (i : insn),
        ListCFG.tmn_pc (l1, a) p' -> ListCFG.insn_at_pc (l1, a) p' i -> is_tmn i),
    wf_prog (l1, bls++a).
Proof.
  intros l1 bls a Hwfl Hwfcfg Hwfins Hwftmn.
  inversion Hwfl.
  constructor; auto; admit.
Admitted.      

(** Given the lemmas above, we can prove the program is well formed. *)
Lemma vm_code_wf_prog : wf_prog vm_code.
Proof.
  constructor.
  - apply vm_code_wf_cfg.
  - apply vm_code_wf_insn.
  - apply vm_code_wf_tmn.
  - apply vm_code_wf_entry.
Qed. 



