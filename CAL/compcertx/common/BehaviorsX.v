Require compcertx.common.SmallstepX.
Require compcert.common.Behaviors.

Import Classical.
Import ClassicalEpsilon.
Import Coqlib.
Import Events.
Import Globalenvs.
Import Integers.
Import SmallstepX.

Set Implicit Arguments.

Export Behaviors.

(* A behavior is wrong both in a semantics and its erased version *)

Lemma semantics_without_retval_state_goes_wrong_intro {RETVAL: Type} (S: Smallstep.semantics RETVAL) (s: Smallstep.state S) (t: trace):
  state_behaves S s (Goes_wrong t) ->
  state_behaves (semantics_without_retval S) s (Goes_wrong t).
Proof.
  inversion 1; subst.
  econstructor; eauto.
  intros r.
  intro ABSURD.
  inversion ABSURD; subst.
  firstorder.
Qed.

Lemma semantics_without_retval_state_goes_wrong_elim {RETVAL: Type} (S: Smallstep.semantics RETVAL) (s: Smallstep.state S) (t: trace):
  state_behaves (semantics_without_retval S) s (Goes_wrong t) ->
  state_behaves S s (Goes_wrong t).
Proof.
  inversion 1; subst.
  econstructor; eauto.
  intros r.
  intro ABSURD.
  apply (H3 tt).
  econstructor; eauto.
Qed.

(* Strong safety *)

Section WITHRETVAL.
Context {RETVAL: Type}.

Definition strongly_safe_state (S: Smallstep.semantics RETVAL) (s: Smallstep.state S) :=
  forall t1 s1,
    Smallstep.star (Smallstep.step S) (Smallstep.globalenv S) s t1 s1 ->
    (exists r, Smallstep.final_state S s1 r) \/
    (exists t2 s2, Smallstep.step S (Smallstep.globalenv S) s1 t2 s2).

Definition strongly_safe_state_beh (S: Smallstep.semantics RETVAL) (s: Smallstep.state S) :=
  ~ exists t, state_behaves S s (Goes_wrong t).

Lemma strongly_safe_state_beh_intro (S: Smallstep.semantics RETVAL) (s: Smallstep.state S):
  strongly_safe_state S s ->
  strongly_safe_state_beh S s.
Proof.
  unfold strongly_safe_state, strongly_safe_state_beh.
  intros H.
  intro ABSURD.
  destruct ABSURD as (t & Ht).
  inversion Ht; subst.
  unfold nostep in H2.
  apply H in H1.
  firstorder.
Qed.

Lemma strongly_safe_state_beh_elim (S: Smallstep.semantics RETVAL) (s: Smallstep.state S):
  strongly_safe_state_beh S s ->
  strongly_safe_state S s.
Proof.
  unfold strongly_safe_state, strongly_safe_state_beh.
  intros H t1 s1 H0.
  destruct (Classical_Prop.classic (exists r, Smallstep.final_state S s1 r)); auto.
  right.
  destruct (Classical_Prop.classic (exists t2 s2, Step S s1 t2 s2)); auto.
  destruct H.
  exists t1.
  econstructor; eauto.
  unfold nostep.
  firstorder.
Qed.

Definition strongly_safe (S: Smallstep.semantics RETVAL) :=
  ~ exists t, program_behaves S (Goes_wrong t).


End WITHRETVAL.

Lemma strongly_safe_without_retval {RETVAL: Type} (S: Smallstep.semantics RETVAL):
  strongly_safe (semantics_without_retval S) <-> strongly_safe S.
Proof.
  unfold strongly_safe.
  split.
  * intros H.
    intro ABSURD.
    apply H; clear H.
    destruct ABSURD as (t & Ht).
    inversion Ht; subst.
    + exists t.
      econstructor; eauto.
      apply semantics_without_retval_state_goes_wrong_intro; auto.
    + exists E0.
      right; auto.
  * intros H.
    intro ABSURD.
    destruct ABSURD as (t & Ht).
    apply H; clear H.
    inversion Ht; subst.
    + exists t.
      econstructor; eauto.
      apply semantics_without_retval_state_goes_wrong_elim; auto.
    + exists E0.
      right; auto.
Qed.

(* If the target language of a forward simulation is weakly determinate,
   and if the source is strongly safe, then the target is strongly safe. *)

Theorem forward_simulation_strongly_safe {RETVAL: Type} (S1 S2: Smallstep.semantics RETVAL):
  receptive S1 ->
  weak_determ S2 ->
  forward_simulation S1 S2 ->
  strongly_safe S1 ->
  strongly_safe S2.
Proof.
  intros H H0 X H1.
  rewrite <- strongly_safe_without_retval in H1.
  rewrite <- strongly_safe_without_retval.
  apply semantics_without_retval_forward_to_backward in X; auto.
  unfold strongly_safe in H1 |- * .
  intro ABSURD.
  destruct ABSURD as (t & BEH).
  apply (backward_simulation_same_safe_behavior X) in BEH.
  * firstorder.
  * unfold not_wrong.
    intros beh H2.
    destruct beh; auto.
    firstorder.
Qed.

Section WITHMEMORYMODELOPS.
Context `{memory_model_ops: Mem.MemoryModelOps}.

Lemma strongly_safe_with_inject_elim val `{VLIO: ValLessdefInjectOps val} (S: semantics (val * mem)) m:
  strongly_safe (semantics_with_inject S m) ->
  strongly_safe S.
Proof.
  unfold strongly_safe.
  intros H.
  intro ABSURD.
  destruct ABSURD as (t & ABSURD).
  apply H; clear H.
  inversion ABSURD; subst.
  {
    inversion H0; subst.
    esplit.
    eleft.
    eassumption.
    econstructor; eauto.
    intros r.
    intro ABSURD' .
    inversion ABSURD' .
    subst.
    eapply H4; eauto.
  }
  esplit.
  eright.
  assumption.
Qed.

End WITHMEMORYMODELOPS.
