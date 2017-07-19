(** * CFG: Control-flow Graphs *)

Require Import Arith.
Require Import Vminus.Util.
Require Import Vminus.Classes.
Require Import Vminus.Vminus.

(** Vminus programs are structured into _control-flow graphs_
    (CFG), which, conceptually, are graphs whose _nodes_ are
    instructions and whose _edges_ are determined by the control
    structure of the program.

    To characterize this structure abstractly, we define a notion of
    _program point_ [pc], which is a location of an instruction in the
    control-flow graph (i.e. each program point is a node of the
    graph).

    The program points are themselves organized into _basic blocks_.
    A basic block consists of a non-empty sequence of program points 
    ending in a terminator instruction.
 *)

(* ################################################################# *)
(** * Program points *)

(** Program points (a.k.a. "program counters").
    Concretely, a [pc] is given by a block label and offset.

    (We could make this more abstract, but this is a simple, easy-to-work with definition.)
 *)

Definition pc := (lbl * nat)%type.

(** Each [pc] has a label, corresponding to its block *)

Definition lbl_of : pc -> lbl       := @fst _ _.

(** Increment a [pc] _within_ a block. *)

Definition incr_pc (p:pc) : pc :=
  let (l, n) := p in (l, S n).

(** (Total) Ordering on [pc]s within the same block *)

Inductive le_pc : pc -> pc -> Prop :=
| let_pc_intro : forall l n1 n2,
    n1 <= n2 -> le_pc (l, n1) (l, n2).

Definition lt_pc (p1 p2:pc) : Prop :=
  le_pc p1 (incr_pc p2).

Definition eq_dec_pc: forall p1 p2: pc, {p1 = p2} + {~(p1 = p2)}.
Proof.
  intros (lbl1, offset1) (lbl2, offset2).
  destruct (eq_dec_lbl lbl1 lbl2) as [lbl_eq | lbl_neq];
    try solve [right; intros H; inversion H;
               exfalso; apply lbl_neq; trivial];
  destruct (Nat.eq_dec offset1 offset2) as [offset_eq | offset_neq];
    try solve [right; intros H; inversion H; apply offset_neq; trivial];
    left; subst; reflexivity.
Defined.

(** The entry point of a block is offset [0]. *)

Definition block_entry (l:lbl) : pc := (l, 0).
Definition entry_of_pc (p:pc)  : pc := block_entry (fst p).


(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Interface for syntactically well-formed CFGs *)

(** Given the abstract characterization of program points, we need to
    relate them to the control-flow instructions of the program's CFG.
    We do this via a collection of well-formedness predicates that
    ensure that each program point maps to a single instruction and
    that the instruction defines a unique local identifier.  (Thus
    satisfying the 'single static assignment' part of the SSA
    representation.)
 *)

(** 
    In this interface, we establish the basic syntactic properties of 
    control-flow-graphs:

    - A CFG [g] is a (partial) function from program points to instructions.
    - Each program point belongs to a basic block.
    - Each basic block is non-empty
    - Each basic block consists of a contiguous sequence of program points,
      ending in a terminator.

    We will impose stronger well-formedness constraints (i.e. the SSA 
    conditions) on CFGs later.
*)


Module Type CFG.
  Parameter t : Type.
  Local Notation cfg := t.

(* ----------------------------------------------------------------- *)
(** *** Basic parameters of the model *)

  (** Well-formed control-flow-graphs. *)

  Parameter wf_cfg : cfg -> Prop.

  (** Well-formed program points. *)

  Parameter wf_pc : cfg -> pc -> Prop.

  (** *** *)

  (** The entry block of the control-flow graph. *)

  Parameter entry_block : cfg -> lbl.

  (** Is the program point a block terminator? *)

  Parameter tmn_pc : cfg -> pc -> Prop.

  (** *** Program point properties *)

  (** Program points are associated with unique instructions. *)

  (** Relational specification: *)

  Parameter insn_at_pc : cfg -> pc -> insn -> Prop.

  Axiom insn_at_pc_func : forall g, wf_cfg g ->
    functional (insn_at_pc g).
  
  (** Executable specification: *)
  
  Parameter fetch : cfg -> pc -> option insn.

  (** Correspondence of the two specs: *)
  
  Axiom insn_at_pc_fetch :
    forall g pc i, wf_cfg g ->
              insn_at_pc g pc i <-> fetch g pc = Some i.

  (** Each [pc] defines a unique [uid] *)
  
  Definition uid_at_pc (g:cfg) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c).

  Axiom uid_at_pc_inj : forall g, wf_cfg g ->
                             injective (uid_at_pc g).

  Axiom uid_at_pc_func : forall g, wf_cfg g ->
    functional (uid_at_pc g).
  
  Axiom pc_at_uid_inj : forall g, wf_cfg g ->
                             injective (fun x p => uid_at_pc g p x).

  Axiom eq_pc_uid : forall g pc id1 id2 c1 c2,
    wf_cfg g ->
    insn_at_pc g pc (id1, c1) ->
    insn_at_pc g pc (id2, c2) ->
    id1 = id2.

  
  (** If [g] is well-formed, each of its program points
      maps to an instruction. *)  
  
  Axiom wf_pc_insn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists i, insn_at_pc g p i.

  
  (** *** Block properties *)

  (** There is an instruction in the entry block. *)

  Axiom wf_entry : forall g, wf_cfg g ->
    wf_pc g (block_entry (entry_block g)).

  (** Every block has a terminator. *)

  Axiom wf_pc_tmn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists p', tmn_pc g p' /\ le_pc p p'.

  (** There are no "gaps" in the pc labels. *)

  Axiom wf_pc_le_tmn : forall g, wf_cfg g ->
    forall p', tmn_pc g p' -> forall p, le_pc p p' -> wf_pc g p.

End CFG.
