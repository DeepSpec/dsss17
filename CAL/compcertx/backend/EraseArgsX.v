Require Export compcert.backend.EraseArgs.
Require Import MemoryX.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Locations.

Section WITHMEMORYMODELX.
Context `{memory_model_x: Mem.MemoryModelX}.

Lemma free_extcall_arg_inject_neutral sp m e m' :
  free_extcall_arg sp m e = Some m' ->
  Mem.inject_neutral (Mem.nextblock m) m ->
  Mem.inject_neutral (Mem.nextblock m') m' .
Proof.
  unfold free_extcall_arg.
  destruct e; try congruence.
  destruct sl; try congruence.
  destruct sp; try congruence.
  intros H H0.
  erewrite Mem.nextblock_free by eauto.
  eapply Mem.free_inject_neutral; eauto.
  generalize (size_chunk_pos (chunk_of_type ty)).
  intros H1.
  apply Mem.free_range_perm in H.
  eapply Mem.perm_valid_block.
  eapply H.
  split.
  {
    reflexivity.
  }
  omega.
Qed.

Corollary free_extcall_args_inject_neutral sp l:
  forall m m',
  free_extcall_args sp m l = Some m' ->
  Mem.inject_neutral (Mem.nextblock m) m ->
  Mem.inject_neutral (Mem.nextblock m') m' .
Proof.
  induction l; simpl; try congruence.
  intros m m' H H0.
  destruct (free_extcall_arg sp m a) eqn:EQ; try discriminate.
  eapply IHl.
  {
    eassumption.
  }
  eapply free_extcall_arg_inject_neutral; eauto.
Qed.

Lemma free_extcall_args_no_perm l:
  forall init_sp m m',
    free_extcall_args init_sp m l = Some m' ->
    forall of ty,
      In (S Outgoing of ty) l ->
      (forall (b : block) (so : ptrofs),
         init_sp = Vptr b so ->
         let ofs :=
             Ptrofs.unsigned (Ptrofs.add so (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * of))) in
         forall o : Z,
           ofs <= o < ofs + size_chunk (chunk_of_type ty) ->
           ~ Mem.perm m' b o Max Nonempty).
Proof.
  induction l; try contradiction.
  unfold free_extcall_args. fold free_extcall_args.
  unfold free_extcall_arg.
  simpl In.
  destruct a.
  {
    intros; eapply IHl; eauto;
    intuition congruence.
  }
  destruct sl; try (intros; eapply IHl; eauto; intuition congruence).
  intros init_sp m m' H of ty0 H0 b so H1 o H2.
  rewrite H1 in H.
  match type of H with
      match ?z with Some _ => _ | _ => _ end = _ =>
      destruct z eqn:FREE; try discriminate
  end.
  inversion H0; eauto.
  inversion H3; subst.
  apply free_extcall_args_extends in H.
  intro ABSURD.
  eapply Mem.perm_extends in ABSURD; eauto.
  revert ABSURD.
  eapply Mem.perm_free_2; eauto.
Qed.

End WITHMEMORYMODELX.
