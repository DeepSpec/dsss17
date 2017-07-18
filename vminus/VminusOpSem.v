(** VminusOpSem: Operational Semantics for Vminus *)

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import String.

Require Import Vminus.Classes.
Require Import Vminus.Util.
Require Import Vminus.Env.
Require Import Vminus.Vminus.
Require Import Vminus.CFG.



(* ################################################################# *)
(** * Vminus Operational Semantics *)

(** This file provides both relational and executable definitions of
    the Vminus operational semantics and proves them equivalent.

    We can reason about the semantics of Vminus programs using only
    the relational specification, but if we want to _test_ them or
    extract an interpreter, we need to have the executable version
    too.  Once we have established that the two semantics correspond,
    it is easy to prove that the relational semantics is deterministic
    because it is equivalent to the executable semantics, which is
    given by a function.  
    
    The development is parameterized by a control-flow graph, making
    the operational semantics independent of its representation.

    Later, as a demonstration of using these semantics, we will prove
    the correctness of an Imp to Vminus compiler and some program  
    transformations as the Vminus level.
*)



Module Make (Cfg:CFG).
Import Cfg.

Module Opsem.
  (**  ------------------------------------------------------------------------- *)
  (** *** The state of a Vminus program: *)

  (** The local environment is a _partial_ map from [uid]s to 
      natural numbers. *)
  
  Module Locals := Make_Env(Uid).
  Notation loc := (Locals.t (option nat)).
  Notation update := Locals.update.

  (** The Vminus memory is a _total_ map from addresses to 
      natural numbers.  (This is a bit artificial, but is a simplification 
      that aligns with the variant of Imp we use in this development.)
  *)

  Module Memory := Make_Env(Addr).
  Notation mem := (Memory.t nat).

  (** The state packages together the memory, local environment,
      current program counter.  It also remembers the environment
      in effect at the end of the of the predecessor block, for
      use in phi instructions (see below). *)
  
  Record state := mkst { st_mem  : mem
                       ; st_pc   : pc
                       ; st_loc  : loc
                       ; st_ppc  : pc     (* predecessor pc *)
                       ; st_ploc : loc    (* predecessor locals *) 
                       }.

  (**  ------------------------------------------------------------------------- *)
  (** *** Evaluating values. *)

  (** Simply look up the uid in the local environment. (May fail!) *)
  
  Definition eval_val (loc:loc) (v:val) : option nat :=
    match v with
      | val_nat n => Some n
      | val_uid i => loc i
    end.

  (**  ------------------------------------------------------------------------- *)
  (** *** Evaluating binary operations. *)

  Definition b2n (b:bool) := if b then 1 else 0.
  Definition n2b (n:nat) := if n then false else true.

  Definition bop_denote (bop:bop) : nat -> nat -> nat :=
    match bop with
      | bop_add => plus
      | bop_sub => minus
      | bop_mul => mult
      | bop_eq => fun n m => b2n (beq_nat n m)
      | bop_le => fun n m => b2n (leb n m)
      | bop_and => fun n m => b2n (n2b n && n2b m)
    end.

  Definition eval_bop (loc:loc) (bop:bop) (v1 v2:val) : option nat :=
    match eval_val loc v1, eval_val loc v2 with
      | Some n1, Some n2 => Some (bop_denote bop n1 n2) 
      | _, _ => None
    end.

  (**  ------------------------------------------------------------------------- *)
  (** *** Evaluating phi nodes *)
  (** To evaluate a phi instruction, we need to know from which 
      predecessor block control reached this phi node, as well as
      the local environment in effect at the end of that block.
      
      We look up the value associated with the predecessor label 
      in the phi arg list, and interpret it in the predecessor's 
      local environment, which are supplied to [eval_phi].
  *)

  Definition eval_phi (ploc:loc) (pl:lbl) (pas:list phiarg) 
    : option nat :=
    match assoc Lbl.eq_dec pl pas with
      | Some v => eval_val ploc v
      | None => None
    end.

  (**  ------------------------------------------------------------------------- *)
  (** *** Control transfers *)
  
  (** Given the current locals and the terminator, determine
      the label of the next block to jump to (if any). *)

  Definition eval_tmn (loc:loc) (t:tmn) : option lbl :=
    match t with
      | tmn_jmp l => Some l
      | tmn_cbr v l1 l2 =>
          match eval_val loc v with
            | Some n => Some (if n then l2 else l1)
            | None => None
          end
      | _ => None
    end.

  (**  ------------------------------------------------------------------------- *)
  (** *** Small-step, relational operational semantics *)

  Inductive step (g:Cfg.t) : state -> state -> Prop :=

  | step_bop : forall mem pc loc bop v1 v2 uid n ppc ploc,
      insn_at_pc g pc (uid, cmd_bop bop v1 v2) ->
      Some n = eval_bop loc bop v1 v2 ->
      step g (mkst mem pc loc ppc ploc) 
             (mkst mem (incr_pc pc) 
                       (update loc uid (Some n)) ppc ploc)

  (** Evaluate the right-hand side in the predecessor's 
     local environment. [lbl_of ppc] is the source block of the 
     control-flow edge that we jumped from to reach the current block. *)

  | step_phi : forall mem pc loc pas uid n ppc ploc,
      insn_at_pc g pc (uid, cmd_phi pas) ->
      Some n = eval_phi ploc (lbl_of ppc) pas ->
      step g (mkst mem pc loc ppc ploc)
             (mkst mem (incr_pc pc) 
                       (update loc uid (Some n)) ppc ploc)

  (** Find the successor block (if any), update the pc. 
      Record the current pc and locals as the "predecessor" state
      for use by any [phi] nodes in the successor block. *)

  | step_tmn : forall mem pc l' loc tmn uid ppc ploc, 
      insn_at_pc g pc (uid, cmd_tmn tmn) ->
      Some l' = eval_tmn loc tmn ->
      step g (mkst mem pc loc ppc ploc)
             (mkst mem (block_entry l') loc pc loc)

  (** Loads and stores simply read from/write to the memory component of the state. **)

  | step_load : forall mem pc loc uid addr ppc ploc,
      insn_at_pc g pc (uid, cmd_load addr) ->
      step g (mkst mem pc loc ppc ploc)
             (mkst mem (incr_pc pc) 
                       (update loc uid (Some (mem addr))) ppc ploc)

  | step_store : forall mem pc loc uid addr v n ppc ploc,
      insn_at_pc g pc (uid, cmd_store addr v) ->
      Some n = eval_val loc v ->
      step g (mkst mem pc loc ppc ploc)
             (mkst (Memory.update mem addr n) 
                   (incr_pc pc) loc ppc ploc).


 (**  ------------------------------------------------------------------------- *)
 (** *** Definition of the initial state. *)

 (** The initial state starts with the program counter at the beginning of the
     entry block in an empty environment.  The "predecessor state" can be 
     set arbitrarily -- we will prove that in any well-formed CFG, the 
     entry block cannot have any phi nodes. *)
  
  Definition init_state (g:Cfg.t) (m: mem) : state :=
    (mkst m
          (block_entry (entry_block g))
          (Locals.empty None)
          (block_entry (entry_block g))
          (Locals.empty None)).


  (**  ------------------------------------------------------------------------- *)  
  (** * Small-step, executable operational semantics *)

  (** This version of the semantics is just a straight forward interpreter, 
      implemented monadically in an error monad to deal with partiality. 
       
      It uses [fetch] where the relational specification uses [insn_at_pc], but
      is otherwise a fairly direct transliteration of the relational version.

      Note: the monad notation and definitions come from [Classes.v], a 
      general purpose library that collects together some commonly used
      typeclasses and instances.

      - [mret] is the "return" of a monad    
      - the notation  ['x <- e1; e2] is the "bind"
      - [trywith] lifts the [option] monad into the [err] monad
  *)
  (**  ------------------------------------------------------------------------- *)  
  
  Fixpoint eval_step (g : Cfg.t) (s : state) : err state :=
    let 'mkst mem pc loc ppc ploc := s in
    '(uid, insn) <- trywith "no instruction fetched" (Cfg.fetch g pc); 
    match insn with
    | cmd_bop bop v1 v2 =>    
      'n <- trywith "cannot evalute binop command"  (eval_bop loc bop v1 v2);
      mret (mkst mem (incr_pc pc) (update loc uid (Some n)) ppc ploc)

    | cmd_phi pas =>
      'n <- trywith "cannot evaluate phi" (eval_phi ploc (lbl_of ppc) pas);
      mret (mkst mem (incr_pc pc) (update loc uid (Some n)) ppc ploc)
           
    | cmd_tmn tmn =>
      'l' <- trywith "cannot evaluate terminator" (eval_tmn loc tmn);
      mret (mkst mem (block_entry l') loc pc loc)

    | cmd_load addr =>
      mret (mkst mem (incr_pc pc) (update loc uid (Some (mem addr))) ppc ploc)

    | cmd_store addr v =>
      'n <- trywith "cannot evaluate address to store to" (eval_val loc v);
        mret (mkst (Memory.update mem addr n) (incr_pc pc) loc ppc ploc)
    end.
  
  (**  ------------------------------------------------------------------------- *)  
  (** *** Helper functions for many-steps of evaluation *)

  Fixpoint eval_until_pc (g : Cfg.t) (s : state)
           (target_pc: pc)
           (fuel : nat): err state :=
    match fuel with
    | 0 => raise "eval out of fuel"
    | S n' =>
      if (eq_dec_pc (st_pc s) target_pc) then mret s
      else
      's' <- (eval_step g s);
      eval_until_pc g s' target_pc n'
    end.

  Definition eval_past_pc (g : Cfg.t) (s : state)
             (target_pc : pc) (fuel : nat) : err state :=
    's' <- eval_until_pc g s target_pc fuel;
    eval_step g s'.

  Definition eval_once_and_until_pc (g : Cfg.t) (s : state)
             (target_pc: pc)
             (fuel: nat) : err state :=
    's' <- eval_step g s;
    eval_until_pc g s' target_pc fuel.


  (**  ------------------------------------------------------------------------- *)  
  (** ** Correspondence between relational and executable definitions *)

  (** Given that the relational and executable semantics share most of their "core"
      functionality, it is pretty easy to prove that the two are equivalent.  
   *)
  
  (** This tactic helps drive the evaluator by looking for a hypothesis that is 
      "stuck" on a [trywith] because it can't be simplified without further case
      analysis.  The tactic destructs the blocking expression, and is able to 
      automatically discharge the goal by applying one of the [step] constructors,
      which is provided as an argument.
  *)
  
  Ltac eval_step_with_step next_state constructor_rule
       cfg_well_formed fetched :=
    match goal with
    | H: match trywith _ ?X with _ => _ end = inr ?next_state |-
      step ?cfg ?curr_state next_state =>
      destruct X eqn:Heval;
      inversion H;
      eapply constructor_rule;
      try rewrite Cfg.insn_at_pc_fetch;
      try apply fetched;
      try apply cfg_well_formed;
      rewrite Heval;
      reflexivity
    | H : _ = inr next_state |-
      step ?cfg ?curr_state next_state =>
      inversion H;
      eapply constructor_rule;
      try rewrite Cfg.insn_at_pc_fetch;
      try apply fetched;
      try apply cfg_well_formed;
      reflexivity
    end.

  Lemma evaluator_sound: forall g s s',
      Cfg.wf_cfg g -> eval_step g s = inr s' -> step g s s'.
  Proof.
    intros g s s' wf_g; unfold eval_step;
      destruct s as [mem curr_pc curr_loc previous_pc previous_loc];
      destruct (Cfg.fetch g curr_pc) as 
          [[uid [bop v1 v2 | pas | term | addr | addr v]] | ] eqn:fetched; simpl;
      intros H;
      [eval_step_with_step s' step_bop wf_g fetched |
       eval_step_with_step s' step_phi wf_g fetched |
       eval_step_with_step s' step_tmn wf_g fetched |
       eval_step_with_step s' step_load wf_g fetched |
       eval_step_with_step s' step_store wf_g fetched | inversion H].
  Qed.
  
  Lemma evaluator_complete: forall g s s',
      Cfg.wf_cfg g -> step g s s' -> eval_step g s = inr s'.
  Proof.
    intros g s s' wf_g step_rel; unfold eval_step;
      inversion step_rel as
        [mem pc loc bop v1 v2 uid n ppc ploc insn_at_pc_is eval_insn_ok s_eq s'_eq |
         mem pc loc pas uid n ppc ploc insn_at_pc_is eval_insn_ok s_eq s'_eq |
         mem pc label loc term uid ppc ploc insn_at_pc_is eval_insn_ok s_eq s'_eq |
         mem pc loc uid addr ppc ploc insn_at_pc_is eval_insn_ok s'_eq |
         mem pc loc uid addr v n ppc ploc insn_at_pc_is eval_insn_ok s_eq s'_eq];
      simpl;
    rewrite Cfg.insn_at_pc_fetch in insn_at_pc_is; try solve [apply wf_g];
    try rewrite insn_at_pc_is; simpl;
    try rewrite <- eval_insn_ok; try reflexivity.
  Qed.
  
  Theorem evaluator_correct: forall g s s',
      Cfg.wf_cfg g -> eval_step g s = inr s' <-> step g s s'.
  Proof.
    intros g s s' wf_g; split;
      revert g s s' wf_g.
    apply evaluator_sound.
    apply evaluator_complete.
  Qed.

(** ------------------------------------------------------------------------- *)  
(* ################################################################# *)
(** * Determinism of [step] *)

(** A direct consequence of the equivalence between the relational and 
    functional specifications is that we can prove that [step] is 
    deterministic.  

    Note: one can prove that [step] is deterministic _without_ using the
    correspondence with the evaluator, but it requires significantly more work!
    It might be informative to try doing that proof. *)
  
Lemma step_deterministic : forall g s s1 s2, wf_cfg g ->
  step g s s1 -> step g s s2 -> s1 = s2.
Proof.
  intros g s s1 s2 Hwfcfg Hs1 Hs2.
  rewrite <- evaluator_correct in Hs1; auto.
  rewrite <- evaluator_correct in Hs2; auto.
  rewrite Hs1 in Hs2. inversion Hs2. reflexivity.
Qed.


  
End Opsem.
End Make.

(**  ------------------------------------------------------------------------- *)  
(* ================================================================= *)
(** ** Instantiating the operational semantics to ListCFG *)

(** For interesting applications of the operational semantics, such as building
    a compiler or writing program transformations, we need to pick a concrete
    representation of the CFG module.  For this development, we use the 
    [ListCFG] definition.
 *)

Require Vminus.ListCFG.
Module Import V := Make ListCFG.ListCFG.

(**  ------------------------------------------------------------------------- *)  