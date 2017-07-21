Require compcert.cfrontend.Cminorgenproof.
Require CminorX.
Require CsharpminorX.
Require SmallstepX.
Require EventsX.

Import Coqlib.
Import Errors.
Import Values.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Cminorgen.
Export Cminorgenproof.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: Csharpminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
Let tge: Cminor.genv := Genv.globalenv tprog.

Let MATCH_PROG: match_prog prog tprog.
Proof. apply transf_program_match; auto. Qed.

Variable init_m: mem.
Hypothesis init_m_inject_neutral: Mem.inject_neutral (Mem.nextblock init_m) init_m.
Hypothesis genv_next_init_m: Ple (Genv.genv_next ge) (Mem.nextblock init_m).

Variable args: list val.
Hypothesis args_inj: Val.inject_list (Mem.flat_inj (Mem.nextblock init_m)) args args.

Lemma transl_initial_states:
  forall i sg,
  forall S, CsharpminorX.initial_state prog i init_m sg args S ->
  exists R, CminorX.initial_state tprog i init_m sg args R /\ match_states prog init_m S R.
Proof.
  intros.
  inv H.
  exploit function_ptr_translated; eauto.
  destruct 1 as [? [? ?]].
  esplit.
  split.
  econstructor; eauto.
  erewrite symbols_preserved; eauto.
  symmetry. eapply sig_preserved; eauto.
  econstructor; eauto.
  eapply Mem.neutral_inject; eauto.
  econstructor.
  econstructor.
  apply Ple_refl.
  intros. unfold Mem.flat_inj. destruct (plt b0 (Mem.nextblock init_m)); try contradiction. reflexivity.
  unfold Mem.flat_inj. intros. destruct (plt b1 (Mem.nextblock init_m)); congruence.
  intros. exploit Genv.genv_symb_range; eauto. unfold ge in *; xomega.
  intros. apply Genv.find_funct_ptr_iff in H1. exploit Genv.genv_defs_range; eauto. unfold ge in *; xomega.
  intros. apply Genv.find_var_info_iff in H1. exploit Genv.genv_defs_range; eauto. unfold ge in *; xomega.
  apply Ple_refl.
  apply Ple_refl.
  econstructor.
  constructor.
  Grab Existential Variables. constructor.
Qed.

Lemma transl_final_states:
  forall sg,
  forall S R r,
  match_states prog init_m S R -> CsharpminorX.final_state sg S r -> final_state_with_inject (CminorX.final_state sg) init_m R r.
Proof.
  inversion 2; subst. inv H. inv MK. inv MCS.
  econstructor.
  econstructor.
  eapply match_globalenvs_inject_incr; eassumption.
  eapply match_globalenvs_inject_separated; eassumption.
  assumption.
  assumption.
Qed. 

Theorem transl_program_correct:
  forall i sg,
  forward_simulation
    (CsharpminorX.semantics prog i init_m sg args)
    (semantics_with_inject (CminorX.semantics tprog i init_m sg args) init_m).
Proof.
  intros.
  eapply forward_simulation_star; eauto.
  apply senv_preserved; auto.
  apply transl_initial_states.
  apply transl_final_states.
  instantiate (1 := measure).
  intros. exploit transl_step_correct; eauto.
Qed.

End WITHCONFIG.
