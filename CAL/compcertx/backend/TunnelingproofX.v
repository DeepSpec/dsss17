Require compcert.backend.Tunnelingproof.
Require LTLX.

Import Coqlib.
Import Globalenvs.
Import Events.
Import Smallstep.
Import LTLX.
Import Tunneling.
Export Tunnelingproof.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: program.
Let tprog := tunnel_program prog.
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
  intros. inversion H.
  econstructor; split.
  econstructor.
  unfold tprog. erewrite symbols_preserved; eauto.
  unfold tprog. erewrite function_ptr_translated; eauto.
  subst. rewrite sig_preserved. auto. 
  assumption.
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
  eapply senv_preserved; eauto.
  apply transf_initial_states.
  apply transf_final_states.
  apply tunnel_step_correct; auto.
Qed.

End WITHCONFIG.
