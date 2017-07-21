Require compcert.backend.CleanupLabelsproof.
Require LinearX.

Import Coqlib.
Import Globalenvs.
Import Events.
Import Smallstep.
Import LinearX.
Import CleanupLabels.
Export CleanupLabelsproof.

Section WITHCONFIG.
  Context `{external_calls_prf: ExternalCalls}.

  Variable prog: program.
  Let tprog := transf_program prog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Let MATCH_PROG: match_prog prog tprog.
  Proof.
    apply transf_program_match.
  Qed.

  Lemma transf_initial_states:
    forall init_ls i sg args m,
    forall st1, initial_state init_ls prog i sg args m st1 ->
           exists st2, initial_state init_ls tprog i sg args m st2 /\ match_states st1 st2.
  Proof.
    intros. inv H.
    econstructor; split.
    eapply initial_state_intro with (f0 := transf_fundef f).
    unfold tprog. erewrite symbols_preserved; eauto.
    eapply function_ptr_translated; eauto.
    erewrite sig_function_translated. auto.
    reflexivity.
    constructor; auto. constructor.
  Qed.

  Lemma transf_final_states:
    forall init_ls,
    forall sg,
    forall st1 st2 r, 
      match_states st1 st2 -> final_state init_ls sg st1 r -> final_state init_ls sg st2 r.
  Proof.
    intros. inv H0. inv H. inv H4. econstructor; eauto.
  Qed.

  Theorem transf_program_correct:
    forall init_ls i sg args m,
      forward_simulation (semantics init_ls prog i sg args m) (semantics init_ls tprog i sg args m).
  Proof.
    intros.
    eapply forward_simulation_opt.
    apply senv_preserved; auto.
    apply transf_initial_states.
    apply transf_final_states.
    apply transf_step_correct; auto.
  Qed.

End WITHCONFIG.
