Require compcert.common.Smallstep.
Require compcertx.common.MemoryX.
Require compcertx.common.ValuesX.

Import Coqlib.
Import AST.
Import MemoryX.
Import Globalenvs.
Import Events.
Export Smallstep.


(* Weak determinacy: a determinate semantics except that the result of a final state may vary. *)

Record weak_determ {RETVAL: Type} (L: semantics RETVAL) : Prop :=
  WeakDeterm {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall s1 s2,
      initial_state L s1 -> initial_state L s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s
  }.

Lemma determinate_weak_determ {RETVAL: Type} (L: semantics RETVAL):
  determinate L -> weak_determ L.
Proof.
  inversion 1; constructor; auto.
Qed.

Lemma match_states_app {F V: Type} (ge: _ F V) (t0 t1 t2: trace):
  match_traces ge t0 (t1 ** t2) ->
  t1 = E0 \/ t2 = E0.
Proof.
  inversion 1; subst;
  unfold E0, Eapp in * |- * ; destruct t1 as [ |  ? [ | ] ] ; simpl in * ;
  intuition congruence.
Qed.


(** Language semantics up to memory extension or injection for final states. *)

(** We create those two classes because we need to have two instances of extends and inject, one for values, another for lists of values (for low-level languages where functions may return lists of values encoding int64) *)

Class ValLessdefInjectOps (val: Type): Type :=
  {
    val_lessdef: val -> val -> Prop;
    val_inject:  Values.meminj -> val -> val -> Prop
  }.

Class ValLessdefInject (val: Type) `{val_ops: ValLessdefInjectOps val}: Prop := 
  {
    val_lessdef_refl: forall v, val_lessdef v v;
    val_lessdef_trans: forall v1 v2 v3, val_lessdef v1 v2 -> val_lessdef v2 v3 -> val_lessdef v1 v3;
    val_inject_compose: forall i12 i23 v1 v2 v3, val_inject i12 v1 v2 -> val_inject i23 v2 v3 -> val_inject (Values.compose_meminj i12 i23) v1 v3;
    val_inject_lessdef_compose: forall i12 v1 v2 v3, val_inject i12 v1 v2 -> val_lessdef v2 v3 -> val_inject i12 v1 v3;
    val_lessdef_inject_compose: forall i23 v1 v2 v3, val_lessdef v1 v2 -> val_inject i23 v2 v3 -> val_inject i23 v1 v3
  }.

Instance val_lessdef_inject_val_ops: ValLessdefInjectOps Values.val.
Proof.
  constructor.
  exact Values.Val.lessdef.
  exact Values.Val.inject.
Defined.

Instance val_lessdef_inject_val: ValLessdefInject Values.val.
Proof.
  constructor.
  apply Values.Val.lessdef_refl.
  apply Values.Val.lessdef_trans.
  apply Values.val_inject_compose.
  intros; eapply ValuesX.val_inject_lessdef_compose; eauto.
  intros; eapply ValuesX.val_lessdef_inject_compose; eauto.
Qed.

Instance val_lessdef_inject_list_ops: ValLessdefInjectOps (list Values.val).
Proof.
  constructor.
  exact Values.Val.lessdef_list.
  exact Values.Val.inject_list.
Defined.

Instance val_lessdef_inject_list: ValLessdefInject (list Values.val).
Proof.
  constructor; simpl.
  induction v; constructor; auto.
  intros until 1; revert v3; induction H; inversion 1; subst; constructor; eauto using Values.Val.lessdef_trans.
  intros until 1; revert i23 v3; induction H; inversion 1; subst; constructor; eauto using Values.val_inject_compose.
  intros until 1; revert v3; induction H; inversion 1; subst; constructor; eauto using ValuesX.val_inject_lessdef_compose.
  intros until 1; revert i23 v3; induction H; inversion 1; subst; constructor; eauto using ValuesX.val_lessdef_inject_compose.
Qed.

Section WITHMEM.
Context `{memory_model_x: Mem.MemoryModelX}.

Section WITHVAL.
Context `{val_lessdef_inject: ValLessdefInject}.

Section FinalStates.
  Context {state: Type} (final_state: state -> (val * mem) -> Prop).

Inductive final_state_with_extends (s: state): val * mem -> Prop :=
| final_state_extends_intro
    v' m'
    (Hfinal: final_state s (v', m'))
    m (MEXT: Mem.extends m m')
    v (LESSDEF: val_lessdef v v')
  :
    final_state_with_extends s (v, m)
.

Lemma final_state_extends_strict: 
  forall s v,
    final_state s v ->
    final_state_with_extends s v.
Proof.
  destruct v. econstructor. eassumption. apply Mem.extends_refl. apply val_lessdef_refl.
Qed.

Lemma final_state_extends_weak:
  forall s v' m'
    (Hfinal: final_state_with_extends s (v', m'))
    m (MEXT: Mem.extends m m')
    v (LESSDEF: val_lessdef v v')
  ,
    final_state_with_extends s (v, m)
.
Proof.
  inversion 1; subst. econstructor; eauto using Mem.extends_extends_compose, val_lessdef_trans.
Qed.

Inductive final_state_with_inject (m_init: mem) (s: state): val * mem -> Prop :=
| final_state_inject_intro
    v' m'
    (Hfinal: final_state s (v', m'))
    j (Hincr: Values.inject_incr (Mem.flat_inj (Mem.nextblock m_init)) j)
    (Hsep: inject_separated (Mem.flat_inj (Mem.nextblock m_init)) j m_init m_init)
    m (MINJ: Mem.inject j m m')
    v (VINJ: val_inject j v v')
  :
    final_state_with_inject m_init s (v, m)
.

Lemma final_state_inject_from_extends:
  forall
    s v' m'
    (Hfinal: final_state_with_extends s (v', m'))
    m_init j (Hincr: Values.inject_incr (Mem.flat_inj (Mem.nextblock m_init)) j)
    (Hsep: inject_separated (Mem.flat_inj (Mem.nextblock m_init)) j m_init m_init)
    m (MINJ: Mem.inject j m m')
    v (VINJ: val_inject j v v')
  ,
    final_state_with_inject m_init s (v, m)
.
Proof.
  intros. inv Hfinal.
  econstructor.
  eassumption.
  eassumption.
  assumption.
  eapply Mem.inject_extends_compose.
  eassumption.
  assumption.
  eapply val_inject_lessdef_compose.
  eassumption.
  assumption.
Qed.

Lemma final_state_inject_weak:
  forall
    s v' m_init m'
    (Hfinal: final_state_with_inject m_init s (v', m'))
    j (Hincr: Values.inject_incr (Mem.flat_inj (Mem.nextblock m_init)) j)
    (Hsep: inject_separated (Mem.flat_inj (Mem.nextblock m_init)) j m_init m_init)
    m (MINJ: Mem.inject j m m')
    v (VINJ: val_inject j v v')
  ,
    final_state_with_inject m_init s (v, m)
.
Proof.
  inversion 1; subst.
  intros.
  econstructor.
  eassumption.
  3: eapply Mem.inject_compose; eauto.
  unfold Values.inject_incr in *.
  unfold Values.compose_meminj.
  intros until delta.
  intros.
  generalize H.
  unfold Mem.flat_inj.
  destruct (plt b (Mem.nextblock m_init)); try discriminate.
  intro. inv H0.
  erewrite Hincr0; eauto.
  erewrite Hincr; eauto.
  reflexivity.
  unfold inject_separated, Values.inject_incr, Values.compose_meminj in *. intros.
  destruct (j0 b1) eqn:?; try discriminate.
  destruct p.
  destruct (j b) eqn:?; try discriminate.
  destruct p.
  inv H0.
  exploit Hsep0; eauto.
  destruct 1.
  split; auto.
  assert (Mem.flat_inj (Mem.nextblock m_init) b = None).
   unfold Mem.flat_inj. destruct (plt b (Mem.nextblock m_init)). contradiction. reflexivity.
  exploit Hsep; eauto.
  tauto.   
  eapply val_inject_compose; eauto.
Qed.

End FinalStates.

Section FinalStatesMatch.

Context {state1: Type} (final_state1: state1 -> (val * mem) -> Prop)
        {state2: Type} (final_state2: state2 -> (val * mem) -> Prop)
        (match_states: state1 -> state2 -> Prop).

Lemma match_final_states_extends_right:
  (forall S R r,
     match_states S R -> final_state1 S r -> final_state_with_extends final_state2 R r) ->
  (forall S R r,
     match_states S R -> final_state_with_extends final_state1 S r -> final_state_with_extends final_state2 R r).
Proof.
  inversion 3; subst; eauto using final_state_extends_weak.
Qed.

Corollary match_final_states_extends:
  (forall S R r,
     match_states S R -> final_state1 S r -> final_state2 R r) ->
  (forall S R r,
     match_states S R -> final_state_with_extends final_state1 S r -> final_state_with_extends final_state2 R r).
Proof.
  intros; eauto using match_final_states_extends_right, final_state_extends_strict.
Qed.

Lemma match_final_states_extends_inject:
  (forall S R r,
     match_states S R -> final_state_with_extends final_state1 S r -> final_state_with_extends final_state2 R r) ->
  (forall j S R r,
     match_states S R -> final_state_with_inject final_state1 j S r -> final_state_with_inject final_state2 j R r)
.
Proof.
  intros.
  inv H1.
  eauto using final_state_inject_from_extends, final_state_extends_strict.
Qed.

Lemma match_final_states_extends_right_inject:
  (forall S R r,
     match_states S R -> final_state1 S r -> final_state_with_extends final_state2 R r) ->
  (forall j S R r,
     match_states S R -> final_state_with_inject final_state1 j S r -> final_state_with_inject final_state2 j R r)
.
Proof.
  eauto using match_final_states_extends_inject, match_final_states_extends_right.
Qed.

Lemma match_final_states_inject:
  (forall S R r,
     match_states S R -> final_state1 S r -> final_state2 R r) ->
  (forall j S R r,
     match_states S R -> final_state_with_inject final_state1 j S r -> final_state_with_inject final_state2 j R r)
.
Proof.
  intros; eauto using match_final_states_extends_right_inject, final_state_extends_strict.
Qed.

Lemma match_final_states_inject_right:
  forall m_init,
  (forall S R r,
     match_states S R -> final_state1 S r -> final_state_with_inject final_state2 m_init R r) ->
  (forall S R r,
     match_states S R -> final_state_with_inject final_state1 m_init S r -> final_state_with_inject final_state2 m_init R r).
Proof.
  inversion 3; subst; eauto using final_state_inject_weak.
Qed.

Lemma match_final_states_extends_left_inject:
  forall m,
    (forall S R r,
       match_states S R -> final_state1 S r -> final_state_with_inject final_state2 m R r) ->
    (forall S R r,
       match_states S R -> final_state_with_extends final_state1 S r -> final_state_with_inject final_state2 m R r)
.
Proof.
  intros.
  inv H1.
  exploit H; eauto.
  inversion 1; subst.
  econstructor.
  eassumption.
  eassumption.
  assumption.
  eapply Mem.extends_inject_compose.
  eassumption.
  assumption.
  eapply val_lessdef_inject_compose; eauto.
Qed.

End FinalStatesMatch.

Definition semantics_with_extends (sem: semantics (val * mem)%type) : semantics (val * mem).
Proof.
  econstructor.
   eexact (step sem).
   exact (initial_state sem).
   apply final_state_with_extends. exact (final_state sem).
   apply (globalenv sem).
   apply (symbolenv sem).
Defined.

Lemma forward_simulation_extends_right:
  forall s1 s2,
    forward_simulation s1 (semantics_with_extends s2) ->
    forward_simulation (semantics_with_extends s1) (semantics_with_extends s2)
.
Proof.
  inversion 1; subst.
  econstructor.
  inv props. econstructor.
  eassumption.
  eassumption.
  intro i. apply match_final_states_extends_right. apply fsim_match_final_states.
  assumption.
  assumption.
Defined.

Lemma forward_simulation_extends:
  forall s1 s2,
    forward_simulation s1 s2 ->
    forward_simulation (semantics_with_extends s1) (semantics_with_extends s2)
.
Proof.
  inversion 1; subst.
  econstructor.
  inv props; econstructor.
  eassumption.
  eassumption.
  intro i. apply match_final_states_extends. apply fsim_match_final_states.
  assumption.
  assumption.
Defined.

Definition semantics_with_inject (sem: semantics (val * mem)%type) (m_init: mem) : semantics (val * mem).
Proof.
  econstructor.
   eexact (step sem).
   exact (initial_state sem).
   apply final_state_with_inject. exact (final_state sem). assumption.
   apply (globalenv sem).
   apply (symbolenv sem).
Defined.

Lemma forward_simulation_extends_inject:
  forall s1 s2,
    forward_simulation (semantics_with_extends s1) (semantics_with_extends s2) ->
    forall m_init,
      forward_simulation (semantics_with_inject s1 m_init) (semantics_with_inject s2 m_init).
Proof.
  inversion 1; subst.
  econstructor.
  inv props; econstructor.
  eassumption.
  eassumption.
  intro i. apply match_final_states_extends_inject. apply fsim_match_final_states.
  assumption.
  assumption.
Defined.  

Corollary forward_simulation_extends_right_inject:
  forall s1 s2,
    forward_simulation s1 (semantics_with_extends s2) ->
    forall m_init,
      forward_simulation (semantics_with_inject s1 m_init) (semantics_with_inject s2 m_init).
Proof.
  eauto using forward_simulation_extends_inject, forward_simulation_extends_right.
Defined.

Corollary forward_simulation_inject:
  forall s1 s2,
    forward_simulation s1 s2 ->
    forall m_init,
      forward_simulation (semantics_with_inject s1 m_init) (semantics_with_inject s2 m_init).
Proof.
  eauto using forward_simulation_extends_inject, forward_simulation_extends.
Defined.

Lemma forward_simulation_inject_right:
  forall s1 s2 m_init,
    forward_simulation s1 (semantics_with_inject s2 m_init) ->
    forward_simulation (semantics_with_inject s1 m_init) (semantics_with_inject s2 m_init).
Proof.
  inversion 1; subst.
  econstructor.
  inv props; econstructor.
  eassumption.
  eassumption.
  intro i. apply match_final_states_inject_right; eauto.
  apply fsim_match_final_states.
  assumption.
  assumption.
Defined.

Lemma forward_simulation_extends_left_inject:
  forall m_init s1 s2,
    forward_simulation s1 (semantics_with_inject s2 m_init) ->
    forward_simulation (semantics_with_extends s1) (semantics_with_inject s2 m_init).
Proof.
  inversion 1; subst.
  econstructor.
  inv props; econstructor.
  eassumption.
  eassumption.
  intros. eapply match_final_states_extends_left_inject.
  intros. eapply fsim_match_final_states. 2: eassumption. eassumption. eassumption. assumption.
  assumption.
  assumption.
Defined.

(* Compatibility with weak determinism *)

Lemma semantics_with_extends_weak_determ s:
  weak_determ s ->
  weak_determ (semantics_with_extends s).
Proof.
  inversion 1; constructor; auto.
  inversion 1; subst; eauto.
Qed.

Lemma semantics_with_inject_weak_determ m_init s:
  weak_determ s ->
  weak_determ (semantics_with_inject s m_init).
Proof.
  inversion 1; constructor; auto.
  inversion 1; subst; eauto.
Qed.

End WITHVAL.

End WITHMEM.
(* Erasure of return values, to show that a weakly-determinate
semantics can be transformed into a determinate semantics for the
purpose of showing that, forward simulation between a receptive and a
weakly-determinate semantics preserves strong safety. *)

Inductive final_state_without_retval {RETVAL: Type} (S: Smallstep.semantics RETVAL) (s: Smallstep.state S) (dummy_retval: unit): Prop :=
| final_state_without_retval_intro (r: RETVAL) (FINAL: Smallstep.final_state S s r)
.

Definition semantics_without_retval
           {RETVAL: Type}
           (S: Smallstep.semantics RETVAL):
  Smallstep.semantics unit :=
  Smallstep.Semantics_gen
    (Smallstep.step S)
    (Smallstep.initial_state S)
    (final_state_without_retval S)
    (Smallstep.globalenv S)
    (Smallstep.symbolenv S).

Lemma semantics_without_retval_receptive {RETVAL: Type} (S: Smallstep.semantics RETVAL):
  receptive S ->
  receptive (semantics_without_retval S).
Proof.
  inversion 1; subst.
  constructor; auto.
Qed.

Lemma semantics_without_retval_determ {RETVAL: Type} (S: Smallstep.semantics RETVAL):
  weak_determ S ->
  determinate (semantics_without_retval S).
Proof.
  inversion 1; subst.
  constructor; auto.
  * inversion 1; subst; eauto.
  * intros s r1 r2 H0 H1; destruct r1; destruct r2; auto.
Qed.

Lemma semantics_without_retval_forward_simulation {RETVAL: Type} (S1 S2: Smallstep.semantics RETVAL):
  Smallstep.forward_simulation S1 S2 ->
  Smallstep.forward_simulation (semantics_without_retval S1) (semantics_without_retval S2).
Proof.
  inversion 1; subst.
  inversion props.
  econstructor; eauto.
  econstructor; eauto.
  inversion 2; subst; econstructor; eauto.
Qed.

Lemma semantics_without_retval_forward_to_backward {RETVAL: Type} (S1 S2: Smallstep.semantics RETVAL):
  receptive S1 ->
  weak_determ S2 ->
  Smallstep.forward_simulation S1 S2 ->
  Smallstep.backward_simulation (semantics_without_retval S1) (semantics_without_retval S2).
Proof.
  intros H H0 X.
  apply forward_to_backward_simulation.
  * apply semantics_without_retval_forward_simulation; auto.
  * apply semantics_without_retval_receptive; auto.
  * apply semantics_without_retval_determ; auto.
Qed.