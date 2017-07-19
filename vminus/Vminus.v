(** * Vminus: A Simple SSA Intermediate Representation *)

(** This file defines the syntax and semantics for Vminus, an
    intermediate representation that is intended to capture the
    essence of LLVM's IR.  In particular, this language represents
    code as a _control flow graph_ whose blocks contain instructions
    in _static single assignment_ form.  This means that each
    instruction _defines_ (at most) one local identifier and that
    those identifiers are _immutable_.  To make this work in practice,
    SSA representations introduce the notation of _phi functions_,
    whose value is determined by the run-time control flow of the
    program.

    To support mutable state, Vminus also has Imp-style global
    identifiers.
*)

Require Import Arith List.
Import ListNotations.

Require Import Vminus.Classes Vminus.Atom Vminus.Util.


Instance eq_dec_atom : eq_dec Atom.t := Atom.eq_dec.
Hint Resolve eq_dec_atom.
Hint Resolve Atom.eq_dec.
Hint Resolve eq_nat_dec.

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Vminus labels, identifiers, and addresses.  *)


(** Basic block labels *)

Module Lbl := Atom.
Notation lbl := Lbl.t.

(** Local unique identifiers *)

Module Uid := Atom.
Notation uid := Uid.t.

(** Addresses of mutable state *)

Module Addr := Atom. 
Notation addr := Addr.t.

(** All come equipped with decidable equality. *)

Definition eq_dec_lbl : forall l1 l2, {l1 = l2} + {l1 <> l2} := Atom.eq_dec.
Hint Resolve eq_dec_lbl.

Definition eq_dec_uid : forall u1 u2, {u1 = u2} + {u1 <> u2} := Atom.eq_dec.
Hint Resolve eq_dec_uid.

Definition eq_dec_addr : forall a1 a2, {a1 = a2} + {a1 <> a2} := Atom.eq_dec.
Hint Resolve eq_dec_addr.


(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Values and Binary Operations *)

(** Values are just local identifiers or natural numbers *)

Inductive val : Set :=
 | val_uid  : uid -> val
 | val_nat : nat -> val.

Definition eq_dec_val : forall (v1 v2:val) , {v1 = v2} + {v1 <> v2}.
Proof.
  decide equality.
Defined.
Instance eq_val : eq_dec val := eq_dec_val.
Hint Resolve eq_dec_val.


(** All Vminus operations are binary arithmetic forms.  There are no unary
    operations, nor are there assembly-language-like [move] instructions.  *)

Inductive bop : Set := 
 | bop_add   (* addition *)
 | bop_sub   (* subtraction *)
 | bop_mul   (* multiplication *)
 | bop_eq    (* equality *)
 | bop_le    (* less-than-or-equal *)
 | bop_and   (* both non-zero *)
.  

Definition eq_dec_bop : forall (b1 b2:bop), {b1 = b2} + {b1 <> b2}.
Proof.
  decide equality.
Defined.
Instance eq_bop : eq_dec bop := eq_dec_bop.
Hint Resolve eq_dec_bop.


(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Basic block terminators *)

(** Each basic block is a sequence of commands (defined next) ending in a
    _terminator_, which is just a control flow operation.  Terminators cannot
    appear in the middle of a well-formed basic block.  (We will define
    well-formed Vminus programs later.)  *)

Inductive tmn : Set :=
| tmn_jmp : lbl -> tmn                  (* unconditional jump *)
| tmn_cbr : val -> lbl -> lbl -> tmn    (* conditional branch *)
| tmn_ret : tmn.                        (* return *)

Definition eq_dec_tmn : forall (t1 t2:tmn), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.
Instance eq_tmn : eq_dec tmn := eq_dec_tmn.
Hint Resolve eq_dec_tmn.

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Commands *)

(** Vminus has only a few commands: binary operations, 
    terminators, phi nodes, and [load] and [store] operations. *)

(** Each [phiarg] associates a value with a predessor block, given by
    a [lbl]. *)

Definition phiarg := (lbl * val)%type.

Definition eq_dec_phiarg:
  forall phiarg1 phiarg2: phiarg, {phiarg1 = phiarg2} + {phiarg1 <> phiarg2}.
Proof.
  decide equality.
Defined.  
Instance eq_phiarg : eq_dec phiarg := eq_dec_phiarg.
Hint Resolve eq_dec_phiarg.

Definition eq_dec_list_phiarg:
  forall l1 l2 : list phiarg, {l1 = l2} + {~(l1 = l2)}.
Proof.
  decide equality.
Defined.
Hint Resolve eq_dec_list_phiarg.
    
(** Vminus Commands *)

Inductive cmd : Set :=
| cmd_bop   : bop -> val -> val -> cmd
| cmd_phi   : list phiarg -> cmd
| cmd_tmn   : tmn -> cmd
| cmd_load  : addr -> cmd
| cmd_store : addr -> val -> cmd.

Definition eq_dec_cmd: forall cmd1 cmd2: cmd, {cmd1 = cmd2} + {~(cmd1 = cmd2)}.
Proof.
  decide equality.
Defined.  
Instance eq_cmd : eq_dec cmd := eq_dec_cmd.
Hint Resolve eq_dec_cmd.

(** An instruction associates a unique local identifier with one of the
    above commands. The local identifier serves two purposes:

    - it uniquely identifies this occurrence of the command 
    - it serves as the value 


*)

Definition insn := (uid * cmd)%type.

Definition eq_dec_insn:
  forall insn1 insn2: insn, {insn1 = insn2} + {~(insn1 = insn2)}.
Proof.
  decide equality.
Defined. 
Instance eq_insn : eq_dec insn := eq_dec_insn.
Hint Resolve eq_dec_insn.

(**  ------------------------------------------------------------------------- *)
(* ----------------------------------------------------------------- *)
(** *** Useful predicates about instructions *)

(** Which values are used by an instruction? *)
Definition insn_uses (i:insn) : list val :=
  match i with
    | (_, cmd_bop _ v1 v2) => [v1; v2]
    | (_, cmd_phi pas) => map (@snd _ _) pas
    | (_, cmd_tmn (tmn_cbr v _ _)) => [v]
    | (_, cmd_store _ v) => [v]
    | (_, _) => []
  end.

(** Which labels appear in an instruction? *)
Definition insn_lbls (i:insn) : list lbl :=
  match i with 
    | (_, cmd_tmn (tmn_jmp l)) => [l]
    | (_, cmd_tmn (tmn_cbr _ l1 l2)) => [l1; l2]
    | _ => []
  end.

(** Which phi arguments appear in an instruction? *)
Definition insn_phis (i:insn) : list phiarg :=
  match i with
    | (_, cmd_phi pas) => pas
    | _ => []
  end.

(** Is it a terminator? *)
Definition is_tmn (i:insn) : Prop := 
  match i with (_, cmd_tmn _) => True | _ => False end.

(** Is is a phi node? *)
Definition is_phi (i:insn) : Prop := 
  match i with (_, cmd_phi _) => True | _ => False end.

Lemma is_phi_decidable : forall i, {is_phi i} + {~is_phi i}.
Proof.
  intros [? c].
  destruct c; simpl; tauto.
Qed.  

(** Does it define its uid? *)
Definition defs_uid (i:insn) : Prop :=
  match i with
    | (_, cmd_tmn _) | (_, cmd_store _ _) => False | _ => True
  end.


