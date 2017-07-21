Require Cexec.
Require Memimpl.

(** * Instantiate Cexec with a memory model and external functions.

   NOTE: This file poses axioms that differ from [Compilerimpl].
   The axioms posed here are valid only for the verified C interpreter,
   not for the compiler.

   Contrary to [Compilerimpl], this file is extracted, for use with
   driver/Interp.ml.
 *)

(** ** Memory model. *)

Local Existing Instance Memimpl.Mem.memory_model_ops.
Local Existing Instance Memimpl.Mem.memory_model_prf.

(** ** External function semantics.

    In Interp.ml, do_external_function is used for all three of
    externals, builtins, and runtime. We axiomatize it here.
  *)

Parameter do_external_function:
  String.string -> AST.signature -> Globalenvs.Senv.t ->
  Determinism.world -> list Values.val -> Memimpl.Mem.mem ->
  option (Determinism.world * Events.trace * Values.val * Memimpl.Mem.mem).

Axiom do_external_function_possible_trace:
  forall id sg ge w vargs m w' t vres m',
    do_external_function id sg ge w vargs m = Some (w', t, vres, m') ->
    Determinism.possible_trace w t w' /\
    forall w_ w'_,
      Determinism.possible_trace w_ t w'_ ->
      do_external_function id sg ge w_ vargs m = Some (w'_, t, vres, m').

(** Then, we use this axiomatization to instantiate the actual
    semantics of external functions. *)

Definition external_functions_sem:
  String.string -> AST.signature -> Events.extcall_sem :=
  fun id sg ge vargs m t vres m' =>
    exists w w',
      do_external_function id sg ge w vargs m = Some (w', t, vres, m').

Lemma do_external_function_sound:
   forall (id : String.string) (sg : AST.signature) 
     (ge0 : Globalenvs.Senv.t) (vargs : list Values.val)
     (m : Memimpl.Mem.mem) (t : Events.trace) (vres : Values.val)
     (m' : Memimpl.Mem.mem) (w w' : Determinism.world),
   do_external_function id sg ge0 w vargs m = Some (w', t, vres, m') ->
   external_functions_sem id sg ge0 vargs m t vres m' /\
   Determinism.possible_trace w t w'.
Proof.
  intros id sg ge0 vargs m t vres m' w w' H.
  split.
  + red. eauto.
  + eapply do_external_function_possible_trace; eauto.
Qed.

Lemma do_external_function_complete:
   forall (id : String.string) (sg : AST.signature) 
     (ge0 : Globalenvs.Senv.t) (vargs : list Values.val)
     (m : Memimpl.Mem.mem) (t : Events.trace) (vres : Values.val)
     (m' : Memimpl.Mem.mem) (w w' : Determinism.world),
   external_functions_sem id sg ge0 vargs m t vres m' ->
   Determinism.possible_trace w t w' ->
   do_external_function id sg ge0 w vargs m = Some (w', t, vres, m').
Proof.
  intros id sg ge0 vargs m t vres m' w w' H H0.
  destruct H as (w_ & w'_ & H).
  eapply do_external_function_possible_trace; eauto.
Qed.

Local Existing Instance Events.symbols_inject_instance.

Axiom external_functions_properties:
  forall id sg, Events.extcall_properties (external_functions_sem id sg) sg.

(** Previously, do_inline_assembly was set to None in Interp.ml. Now we set it here,
    directly from within Coq.   *)

Definition do_inline_assembly:
  String.string -> AST.signature -> Globalenvs.Senv.t ->
  Determinism.world -> list Values.val -> Memimpl.Mem.mem ->
  option (Determinism.world * Events.trace * Values.val * Memimpl.Mem.mem)
  :=
    fun _ _ _ _ _ _ => None.

Definition inline_assembly_sem:
  String.string -> AST.signature -> Events.extcall_sem :=
  fun id sg ge vargs m t vres m' =>
    exists w w',
      do_inline_assembly id sg ge w vargs m = Some (w', t, vres, m').

Lemma inline_assembly_sem_empty
      id sg ge vargs m t vres m':
  inline_assembly_sem id sg ge vargs m t vres m' ->
  False.
Proof.
  destruct 1 as (w & w' & INL); discriminate.
Qed.

Lemma do_inline_assembly_sound:
   forall (txt : String.string) (sg : AST.signature)
     (ge0 : Globalenvs.Senv.t) (vargs : list Values.val)
     (m : Memimpl.Mem.mem) (t : Events.trace) (vres : Values.val)
     (m' : Memimpl.Mem.mem) (w w' : Determinism.world),
   do_inline_assembly txt sg ge0 w vargs m = Some (w', t, vres, m') ->
   inline_assembly_sem txt sg ge0 vargs m t vres m' /\
   Determinism.possible_trace w t w'.
Proof.
  intros; discriminate.
Qed.

Lemma do_inline_assembly_complete:
 forall (txt : String.string) (sg : AST.signature) 
   (ge0 : Globalenvs.Senv.t) (vargs : list Values.val) 
   (m : Memimpl.Mem.mem) (t : Events.trace) (vres : Values.val)
   (m' : Memimpl.Mem.mem) (w w' : Determinism.world),
   inline_assembly_sem txt sg ge0 vargs m t vres m' ->
   Determinism.possible_trace w t w' ->
   do_inline_assembly txt sg ge0 w vargs m = Some (w', t, vres, m').
Proof.
  intros; edestruct inline_assembly_sem_empty; eauto.
Qed.

Local Instance external_calls_ops: Events.ExternalCallsOps Memimpl.Mem.mem.
Proof.
  split.
  + apply external_functions_sem.
  + apply external_functions_sem.
  + apply external_functions_sem.
  + apply inline_assembly_sem.
Defined.

Local Instance external_calls_prf: Events.ExternalCallsProps Memimpl.Mem.mem.
Proof.
  constructor.
  + apply external_functions_properties.
  + apply external_functions_properties.
  + apply external_functions_properties.
  + split; intros; edestruct inline_assembly_sem_empty; eauto.
Qed.

Local Instance enable_builtins_instance: Events.EnableBuiltins Memimpl.Mem.mem.
Proof.
  constructor.
  exact true.
Qed.

Local Instance external_calls_instance: Events.ExternalCalls Memimpl.Mem.mem.


(** ** Instantiate Cexec. *)

(** Force [Cexec] to be extracted with the memory model instantiated. *)

Definition state := Csem.state.
Definition do_step ge := Cexec.do_step ge do_external_function do_external_function do_external_function do_inline_assembly.
Definition do_initial_state := Cexec.do_initial_state.
Definition at_final_state := Cexec.at_final_state.
Definition step_expr ge := Cexec.step_expr ge do_external_function do_external_function do_external_function do_inline_assembly.
(* the following is needed because Mem.MemoryModelOps is after F, V. *)
Definition init_mem F V := Globalenvs.Genv.init_mem (F := F) (V := V).
Arguments init_mem [_ _] _.

Theorem do_step_sound ge:
  forall w S rule t S',
  List.In (Cexec.TR rule t S') (do_step ge w S) ->
  Csem.step ge S t S' \/ (t = Events.E0 /\ S' = Csem.Stuckstate /\ Cexec.can_crash_world ge w S).
Proof.
  apply Cexec.do_step_sound;
  eauto using
    do_external_function_sound, do_external_function_complete,
    do_inline_assembly_sound, do_inline_assembly_complete.
Qed.

Theorem do_step_complete ge:
  forall w S t S' w',
  Determinism.possible_trace w t w' ->
  Csem.step ge S t S' ->
  exists rule, List.In (Cexec.TR rule t S') (do_step ge w S).
Proof.
  apply Cexec.do_step_complete;
  eauto using
    do_external_function_sound, do_external_function_complete,
    do_inline_assembly_sound, do_inline_assembly_complete.
Qed.
