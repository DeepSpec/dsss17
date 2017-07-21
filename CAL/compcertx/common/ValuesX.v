Require Export compcert.common.Values.
Import Coqlib.

Lemma val_inject_lessdef_compose: 
  forall j v1 v2, Val.inject j v1 v2 -> forall v3, Val.lessdef v2 v3 -> Val.inject j v1 v3.
Proof.
  inversion 1; subst; inversion 1; subst; auto.
Qed.

Lemma val_lessdef_inject_compose: 
  forall v1 v2, Val.lessdef v1 v2 -> forall j v3, Val.inject j v2 v3 -> Val.inject j v1 v3.
Proof.
  inversion 1; subst; inversion 1; subst; auto.
Qed.

Lemma val_inject_incr_recip :
  forall j1 v v1,
    Val.inject j1 v v1 ->
    forall j2 v2,
      Val.inject j2 v v2 ->
      inject_incr j2 j1 ->
      Val.inject j2 v v1.
Proof.
  inversion 1; subst; try (constructor; fail).
  inversion 1; subst.
  intro INCR. exploit INCR; eauto. intro.
  econstructor.
  2: reflexivity.
  congruence.
Qed.
