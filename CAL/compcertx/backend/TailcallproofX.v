Require compcert.backend.Tailcallproof.
Require RTLX.
Require SmallstepX.

Import Coqlib.
Import Errors.
Import AST.
Import Values.
Import Memory.
Import Events.
Import SmallstepX.
Import Globalenvs.
Import Tailcall.
Export Tailcallproof.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: RTL.program.
Let tprog := transf_program prog.

Let MATCH_PROG: match_prog prog tprog.
Proof. apply transf_program_match; auto. Qed.

Let ge : RTL.genv := Genv.globalenv prog.
Let tge: RTL.genv := Genv.globalenv tprog.

Lemma transf_initial_states:
  forall i init_m sg args,
  forall S, RTLX.initial_state prog i init_m sg args S ->
  exists R, RTLX.initial_state tprog i init_m sg args R /\ match_states S R.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intros.
  exists (RTL.Callstate nil (transf_fundef f) args init_m); split.
  econstructor; eauto.
  unfold tprog. erewrite symbols_preserved; eauto.
  symmetry. eapply sig_preserved; eauto.
  econstructor.
  econstructor.
  exact (val_lessdef_refl _).
  apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall sg,
  forall st1 st2 r, 
  match_states st1 st2 -> RTLX.final_state sg st1 r ->
  final_state_with_extends (RTLX.final_state sg) st2 r.
Proof.
  intros. inv H0. inv H.
  inv H3.
  econstructor; eauto.
  constructor.
Qed.

Theorem transf_program_correct:
  forall init_m args,
  forall i sg,
  forward_simulation 
    (RTLX.semantics prog i init_m sg args)
    (semantics_with_extends (RTLX.semantics tprog i init_m sg args)).
Proof.
  intros.
  eapply forward_simulation_opt with (measure := measure); eauto.
  apply senv_preserved; auto.
  apply transf_initial_states.
  apply transf_final_states.
  apply transf_step_correct; auto.
Qed.

End WITHCONFIG.
