Require Import LogicalRelations.
Require Import CompcertStructures.
Require Import SimulationRelation.
Require Import SimValues.
Require Import SimEvents.
Require Import compcert.common.Events.
Require Import compcertx.driver.CompCertBuiltins.

Section COMPCERTBUILTINS.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  Global Instance builtin_functions_sem_match {F V} p:
    Monotonic
      builtin_functions_sem
      (- ==> - ==> rforall Rf, @senv_le F V Rf ++>
       list_rel (match_val R p) ++>
       match_mem R p ++>
       - ==>
       rel_curry (set_rel (incr p (match_val R p * match_mem R p))))%rel.
  Proof.
    intros id sg Rf ge1 ge2 Hge.
    intros vargs1 vargs2 Hvargs m1 m2 Hm t [m1' vres1] H1.
    simpl in *.
    deconstruct H1 ltac:(fun c => inverse_hyps; eexpair; split; [ eapply c; eauto | rauto ]).
  Qed.

  Instance longoffloat_params: Params Val.longoffloat 1.

  Global Instance runtime_functions_sem_match {F V} p:
    Monotonic
      runtime_functions_sem
      (- ==> - ==> rforall Rf, @senv_le F V Rf ++>
       list_rel (match_val R p) ++>
       match_mem R p ++>
       - ==>
       rel_curry (set_rel (incr p (match_val R p * match_mem R p))))%rel.
  Proof.
    intros id sg Rf ge1 ge2 Hge.
    intros vargs1 vargs2 Hvargs m1 m2 Hm t [m1' vres1] H1.
    simpl in *.
    deconstruct H1 ltac:(fun c => inverse_hyps; transport_hyps; eexpair; split; [eapply c; eauto | rauto ]).
    (* PW: This is slow, is there anything we can do? *)
  Qed.

  Context `{Hec1: !ExternalCallsOpsX (mwd D1)}.
  Context `{Hec2: !ExternalCallsOpsX (mwd D2)}.

  Context `{cc1_ops: !EnableBuiltins (mwd D1)}.
  Context `{cc2_ops: !EnableBuiltins (mwd D2)}.

  Global Instance builtin_external_call_x_match {F V} p ef:
    cc_enable_external_as_builtin (mem := mwd D1) = false ->
    builtin_enabled (mem := mwd D1) ef ->
    Monotonic
      (external_call ef)
      (rforall Rf, @senv_le F V Rf ++>
                             list_rel (match_val R p) ++>
                             match_mem R p ++>
                    - ==>
                        rel_curry (set_rel (incr p (match_val R p * match_mem R p))))%rel
  .
  Proof.
    intros.
    eapply builtin_external_call_match.
    - assumption.
    - tauto.
    - assumption.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.
End COMPCERTBUILTINS.
