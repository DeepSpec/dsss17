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

Notation id0 := (Atom.fresh []).
Notation Y := (Atom.fresh [id0]).
Notation Z := (Atom.fresh [Y;id0]).
Notation id1 := (Atom.fresh [Z;Y;id0]).
Notation id2 := (Atom.fresh [id1;Z;Y;id0]).
Notation id3 := (Atom.fresh [id2;id1;Z;Y;id0]).
Notation id4 := (Atom.fresh [id3;id2;id1;Z;Y;id0]).
Notation id5 := (Atom.fresh [id4;id3;id2;id1;Z;Y;id0]).

Definition X : addr := id0.

Eval compute in (Atom.nat_of id0).

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
Definition entry_lbl := Atom.fresh [].

Definition l0 := Atom.fresh [entry_lbl].
Definition blk := Atom.fresh [l0; entry_lbl].
Definition x := Atom.fresh [blk; l0; entry_lbl].
Definition l1 := Atom.fresh [x;blk;l0;entry_lbl].


Definition cyclic_phi : ListCFG.t :=
  (entry_lbl ,
   [(entry_lbl,
     [(l0, cmd_tmn (tmn_jmp blk))]) ;
    (blk,
     [(x, cmd_phi [(entry_lbl, val_nat 0); (x, val_uid x)]) ;
      (l1, cmd_tmn (tmn_jmp blk))])]
  ).

(** **** Exercise: 2 stars (cyclic_phi)  *)
(**
  Define a ListCFG program that corresponds to the following Vminus code.

[[ 
entry:
  br %blk

blk:
  %x = phi [%entry: 0] [%blk : %x]
  br blk


 *)

Lemma NoDup_fresh : forall l, NoDup l -> NoDup ((Atom.fresh l) :: l).
Proof.
  intros. apply NoDup_cons. apply Atom.fresh_not_in. exact H.
Qed.

Lemma nodups_names: NoDup [l1;x;blk;l0;entry_lbl].
Proof.
  repeat (apply NoDup_fresh). apply NoDup_nil.
Qed.  



(** **** Exercise: 4 stars (cyclic_phi_wf)  *)
(** Prove that your definition of [cyclic_phi] is a well-formed CFG. *)
Lemma cyclic_phi_wf : wf_prog cyclic_phi.
Proof.
Admitted.