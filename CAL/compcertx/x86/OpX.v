Require Op.

Import Coqlib.
Import AST.
Import Integers.
Import Floats.
Import Values.
Import Memory.
Import Globalenvs.
Import Events.
Export Op.

Set Implicit Arguments.

Section WITHMEM.
Context `{memory_model_prf: Mem.MemoryModel}.

Variable F V: Type.
Variable genv: Genv.t F V.

Lemma eval_operation_lessdef_strong:
  forall sp1 sp2,
    Val.lessdef sp1 sp2 ->
    forall op vl1 vl2 v1 m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_operation genv sp1 op vl1 m1 = Some v1 ->
  exists v2, eval_operation genv sp2 op vl2 m2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros sp1 sp2 HSP.
  intros. rewrite val_inject_list_lessdef in H.
  assert (exists v2 : val,
          eval_operation genv sp2 op vl2 m2 = Some v2
          /\ Val.inject (fun b => Some(b, 0)) v1 v2).
  {
    eapply eval_operation_inj.
    - apply valid_pointer_extends. eassumption.
    - apply weak_valid_pointer_extends; auto.
    - apply weak_valid_pointer_no_overflow_extends.
    - apply valid_different_pointers_extends; auto.
    - intros. rewrite <- val_inject_lessdef; auto.
    - rewrite <- val_inject_lessdef. eassumption.
    - eauto.
    - auto. 
  }
  destruct H2 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto.
Qed.

Lemma eval_addressing_lessdef_strong:
  forall sp1 sp2,
    Val.lessdef sp1 sp2 ->
  forall addr vl1 vl2 v1,
  Val.lessdef_list vl1 vl2 ->
  eval_addressing genv sp1 addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp2 addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros sp1 sp2 HSP.
  intros. rewrite val_inject_list_lessdef in H.
  assert (exists v2 : val,
          eval_addressing genv sp2 addr vl2 = Some v2
          /\ Val.inject (fun b => Some(b, 0)) v1 v2).
  eapply eval_addressing_inj with (sp1 := sp1).
  intros. rewrite <- val_inject_lessdef; auto.
  rewrite <- val_inject_lessdef; auto.
  eauto. auto. 
  destruct H1 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto. 
Qed.

End WITHMEM.
