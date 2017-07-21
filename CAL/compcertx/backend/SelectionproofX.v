Require compcert.backend.Selectionproof.
Require CminorSelX.
Require CminorX.
Require SmallstepX.
Require EventsX.

Import Coqlib.
Import Errors.
Import AST.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import SelectLong.
Export Selectionproof.

Section WITHCONFIG.
Context `{ external_calls_prf: ExternalCalls }.
Context `{i64_helpers_correct: !SplitLongproof.I64HelpersCorrect mem}.

Section TRANSF.

Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Hypothesis TRANF: Selection.sel_program prog = OK tprog.

Let MATCH_PROG: match_prog prog tprog.
Proof. apply transf_program_match; auto. Qed.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Variable m: mem.

Lemma sel_initial_states:
  forall i sg args,
  forall S, CminorX.initial_state prog i m sg args S ->
  exists R, CminorSelX.initial_state tprog i m sg args R /\ match_states prog tprog S R.
Proof.
  inversion 1; subst.
  exploit function_ptr_translated; eauto.
  destruct 1 as (? & ? & FIND & FMATCH & FLINK).
  esplit. split. econstructor.
   erewrite symbols_preserved; eauto.
   eassumption.
   symmetry. eapply sig_function_translated; eauto.
  econstructor; eauto.
  constructor.
  refine (val_lessdef_refl _).
  apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall sg,
  forall S R r,
  match_states prog tprog S R -> CminorX.final_state sg S r -> final_state_with_extends (CminorSelX.final_state sg) R r.
Proof.
  intros. inv H0. inv H.
  apply match_call_cont_cont in MC.
  destruct MC as (? & ? & MC).
  inv MC.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forall i sg args,
  forward_simulation
    (CminorX.semantics prog i m sg args)
    (semantics_with_extends (CminorSelX.semantics tprog i m sg args))
.
Proof.
  intros.
  eapply forward_simulation_opt; simpl.
  apply senv_preserved; auto.
  apply sel_initial_states.
  apply sel_final_states.
  apply sel_step_correct. 
  assumption.
Qed.

End TRANSF.

End WITHCONFIG.
