Require Compiler.
Require Memimpl.
Require Unusedglobproofimpl.

(** * Instantiate the compiler correctness proofs
      with a memory model and external functions.

   NOTE: This file poses axioms that differ from [Cexecimpl].
   The axioms posed here are valid only for the verified compiler,
   not for the C interpreter.

   Anyway, since the verified compiler defined in [Compiler] itself does
   not depend on the memory model or the external functions, this file
   does not need to be extracted.
 *)

(** Instantiate the memory model. *)

Local Existing Instance Memimpl.Mem.memory_model_ops.
Local Existing Instance Memimpl.Mem.memory_model_prf.
Local Existing Instance Unusedglobproofimpl.Mem.memory_model_x_prf.

(** Axiomatize over external function calls. *)

Local Existing Instance Events.symbols_inject_instance.
Parameter external_calls_ops: Events.ExternalCallsOps Memimpl.Mem.mem.
Axiom external_calls_props: Events.ExternalCallsProps Memimpl.Mem.mem.
Axiom enable_builtins_instance: Events.EnableBuiltins Memimpl.Mem.mem.
Axiom external_calls_prf: Events.ExternalCalls Memimpl.Mem.mem.
Axiom i64_helpers_correct_prf:
  SplitLongproof.I64HelpersCorrect Memimpl.Mem.mem.

(** * Correctness of the CompCert compiler *)

Theorem transf_c_program_correct:
  forall p tp,
  Compiler.transf_c_program p = Errors.OK tp ->
  Smallstep.backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  apply Compiler.transf_c_program_correct.
Qed.

(** Here is the separate compilation case.  Consider a nonempty list [c_units]
  of C source files (compilation units), [C1 ,,, Cn].  Assume that every
  C compilation unit [Ci] is successfully compiled by CompCert, obtaining
  an Asm compilation unit [Ai].  Let [asm_unit] be the nonempty list
  [A1 ... An].  Further assume that the C units [C1 ... Cn] can be linked
  together to produce a whole C program [c_program].  Then, the generated
  Asm units can be linked together, producing a whole Asm program
  [asm_program].  Moreover, [asm_program] preserves the semantics of
  [c_program], in the sense that there exists a backward simulation of
  the dynamic semantics of [asm_program] by the dynamic semantics of [c_program].
*)

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  Coqlib.nlist_forall2 (fun cu tcu => Compiler.transf_c_program cu = Errors.OK tcu) c_units asm_units ->
  Linking.link_list c_units = Some c_program ->
  exists asm_program, 
      Linking.link_list asm_units = Some asm_program
   /\ Smallstep.backward_simulation (Csem.semantics c_program) (Asm.semantics asm_program).
Proof.
  apply Compiler.separate_transf_c_program_correct.
Qed.
