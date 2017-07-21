Require compcert.backend.Allocproof.
Require LTLX.
Require RTLX.
Require SmallstepX.
Require EventsX.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Locations.
Import Conventions.
Import RTLX.
Import RTLtyping.
Import LTLX.
Import Allocation.
Export Allocproof.

Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: RTL.program.
Variable tprog: LTL.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let MATCH_PROG: match_prog prog tprog.
Proof.
  apply transf_program_match; auto.
Qed.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Variable init_m: mem.
Variable init_ltl_ls: LTL.locset.

Variable sg: signature.
Variable args: list val.
Hypothesis Hargs: args = map (fun r => Locmap.getpair r init_ltl_ls) (loc_arguments sg).


Hypothesis wt_args: Val.has_type_list args (sig_args sg).


Lemma initial_states_simulation:
  forall i,
  forall st1, 
    RTLX.initial_state prog i init_m sg args st1 ->
    exists st2, LTLX.initial_state init_ltl_ls tprog i sg args init_m st2 /\ match_states tprog init_ltl_ls (sig_res sg) st1 st2.
Proof.  
  inversion 1; subst.
  exploit function_ptr_translated; eauto.
  destruct 1 as [? [? ?]].
  esplit.
  split.
  - econstructor.
    erewrite symbols_preserved; eauto.
    eassumption.
    symmetry. eapply sig_function_translated; eauto.
    reflexivity.
  - econstructor.
    constructor.
    f_equal. f_equal. eapply sig_function_translated; eauto.
    assumption.
    erewrite sig_function_translated; eauto.
    apply (val_lessdef_refl (ValLessdefInject := val_lessdef_inject_list)).
    constructor.
    apply Mem.extends_refl.
    erewrite sig_function_translated; eauto.
Qed.

Lemma final_states_simulation:
  forall st1 st2 r
    (MATCH: match_states tprog init_ltl_ls (sig_res sg) st1 st2)
    (FINAL: RTLX.final_state sg st1 r),
    final_state_with_extends (LTLX.final_state init_ltl_ls sg) st2 r.
Proof.
  intros.
  inv FINAL.
  inv MATCH.
  inv STACKS.
  econstructor.
  econstructor.
  reflexivity.
  symmetry. apply AG.
  {
    unfold callee_save_loc.
    unfold destroyed_at_call in H0.
    Opaque all_mregs.
    rewrite filter_In in H0.
    generalize (all_mregs_complete r). intros.
    assert (negb (is_callee_save r) <> true) as EQ by tauto.
    rewrite <- (negb_involutive (is_callee_save r)).
    destruct (negb (is_callee_save r)); auto.
  }
  assumption.
  inv H.
  rewrite LocationsX.getpair_prop.
  erewrite loc_result_exten; eauto.
Qed.

Lemma wt_initial_state: 
  forall i,
  forall st, 
    RTLX.initial_state prog i init_m sg args st ->
    wt_state (sig_res sg) st.
Proof.
  inversion 1; subst.
  exploit Genv.find_funct_ptr_inversion; eauto.
  destruct 1.
  econstructor.
  constructor.
  reflexivity.
  eapply wt_prog; eauto.
  assumption.
Qed.

Theorem transf_program_correct:
  forall i,
  forward_simulation
    (RTLX.semantics prog i init_m sg args)
    (semantics_with_extends (LTLX.semantics init_ltl_ls tprog i sg args init_m)).
Proof.
  intros.
  set (ms := fun s s' => wt_state (sig_res sg) s /\ match_states tprog init_ltl_ls (sig_res sg) s s').
  eapply forward_simulation_plus with (match_states := ms). 
- apply senv_preserved; auto.
- simpl. intros. exploit initial_states_simulation; eauto. intros [st2 [A B]]. 
  exists st2; split; auto. split; auto.
  eapply wt_initial_state; eauto.
- intros. destruct H. simpl in *.
  eapply final_states_simulation; eauto. 
- intros. destruct H0. 
  simpl in *.
  exploit step_simulation; eauto. intros [s2' [A B]].
  exists s2'; split. exact A. split.
  refine (subject_reduction _ _ _ _ _ _ H H0).
  eapply wt_prog; eauto.
  assumption.
Qed.

End PRESERVATION.
