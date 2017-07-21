Require compcert.cfrontend.Cshmgenproof.
Require ClightX.
Require CsharpminorX.
Require SmallstepX.

Import Coqlib.
Import Errors.
Import Integers.
Import Values.
Import Globalenvs.
Import Events.
Import SmallstepX.
Import Cshmgen.
Export Cshmgenproof.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let MATCH_PROG: match_prog prog tprog.
Proof. apply transf_program_match; auto.
Qed.

Let ge := Clight.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma transl_initial_states:
  forall i init_m sg args,
  forall S, ClightX.initial_state prog i init_m sg args S ->
  exists R, CsharpminorX.initial_state tprog i init_m sg args R /\ match_states prog S R.
Proof.
 inversion 1; subst.
  exploit function_ptr_translated; eauto.
  destruct 1 as (? & ? & FIND & MATCH & LINKORDER).
  esplit.
  split.
  econstructor.
  erewrite symbols_preserved; eauto.
  eassumption.
  eassumption.
  symmetry. eapply transl_fundef_sig2; eauto.
  econstructor; eauto.
  constructor.
  constructor.
Grab Existential Variables.
  eapply Ctypes.prog_comp_env.
  eassumption.
Qed.

Lemma transl_final_states:
  forall sg,
  forall S R r,
  match_states prog S R -> ClightX.final_state sg S r -> CsharpminorX.final_state sg R r.
Proof.
  inversion 2; subst. inv H. inv MK. constructor.
Qed.

Theorem transl_program_correct:
  forall i init_m sg args,
    forward_simulation
      (ClightX.semantics prog i init_m sg args)
      (CsharpminorX.semantics tprog i init_m sg args)
.
Proof.
  intros.
  eapply forward_simulation_plus.
  apply senv_preserved; auto.
  apply transl_initial_states.
  apply transl_final_states.
  apply transl_step; auto.
Qed.

End WITHCONFIG.
