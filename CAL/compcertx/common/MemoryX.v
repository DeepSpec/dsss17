Require compcert.common.Memory.

Import Coqlib.
Import Values.
Export Memory.

Module Mem.
Export Memtype.Mem.

(** General-purpose properties on the existing memory model *)

Lemma val_inject_flat_inj_lessdef:
  forall n v1 v2,
    Val.inject (flat_inj n) v1 v2 ->
    Val.lessdef v1 v2.
Proof.
  inversion 1; subst; try (constructor; fail).
  unfold flat_inj in H0. destruct (plt b1 n); try discriminate. inv H0.
  rewrite Integers.Ptrofs.add_zero. constructor.
Qed.

Section WITHMEM.
Context `{memory_model: MemoryModel}.

Lemma load_inject_neutral:
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall chunk b o v,
      Mem.load chunk m b o = Some v ->
      Val.inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  intros.
  apply Mem.neutral_inject in H.
  assert (Mem.flat_inj (Mem.nextblock m) b = Some (b, 0)).
  {
    unfold Mem.flat_inj.
    destruct (plt b (Mem.nextblock m)); eauto.
    destruct n.
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies.
    eapply Mem.load_valid_access.
    eassumption.
    constructor.
  }
  exploit Mem.load_inject; eauto.
  replace (o + 0) with o by omega.
  destruct 1 as [? [? ?]].
  congruence.
Qed.

Lemma loadv_inject_neutral:
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall chunk a v,
      Mem.loadv chunk m a = Some v ->
      Val.inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  intros.
  destruct a; try discriminate.
  eapply load_inject_neutral; eauto.
Qed.

Lemma loadbytes_inject_neutral:
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall b o n l,
      Mem.loadbytes m b o n = Some l ->
      Mem.valid_block m b ->
      list_forall2 (memval_inject (Mem.flat_inj (Mem.nextblock m))) l l.
Proof.
  intros.
  apply Mem.neutral_inject in H.
  exploit Mem.loadbytes_inject; eauto.
  unfold flat_inj. destruct (plt b (nextblock m)); try reflexivity.
  contradiction.
  destruct 1 as (bytes2 & LOAD2 & INJ).
  replace (o + 0) with o in * by omega.
  congruence.
Qed.

End WITHMEM.

(** Additional properties on the memory model required by CompCertX *)

Class MemoryModelX
      (mem: Type)
      `{memory_model_ops: MemoryModelOps mem}
: Prop :=
{
  memory_model_x_memory_model :> MemoryModel mem;

  (** The following are needed by [SmallstepX] *)
  extends_extends_compose:
    forall m1 m2 m3,
      extends m1 m2 -> extends m2 m3 -> extends m1 m3
  ;

  inject_extends_compose:
  forall f m1 m2 m3,
    inject f m1 m2 -> extends m2 m3 -> inject f m1 m3
  ;

  inject_compose:
    forall f f' m1 m2 m3,
      inject f m1 m2 -> inject f' m2 m3 ->
      inject (compose_meminj f f') m1 m3
  ;

  extends_inject_compose:
  forall f m1 m2 m3,
    extends m1 m2 -> inject f m2 m3 -> inject f m1 m3
  ;

  (** The following are needed by [AsmX], to prove the preservation of [inject_neutral_invariant] *)
  
  inject_neutral_incr:
    forall m thr, inject_neutral thr m -> forall thr', Ple thr thr' -> inject_neutral thr' m
  ;

  free_inject_neutral:
    forall m b lo hi m' thr,
      free m b lo hi = Some m' ->
      inject_neutral thr m ->
      Plt b thr ->
      inject_neutral thr m'
  ;

  (** The following are needed by [CertiKOS], to prove Mem.extends between initial memories *)

  drop_perm_right_extends:
    forall m1 m2 b lo hi p m2',
      extends m1 m2 ->
      drop_perm m2 b lo hi p = Some m2' ->
      (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
      extends m1 m2'
  ;

  drop_perm_parallel_extends:
    forall m1 m2 b lo hi p m1',
      extends m1 m2 ->
      drop_perm m1 b lo hi p = Some m1' ->
      exists m2',
        drop_perm m2 b lo hi p = Some m2'
        /\ extends m1' m2'
  ;

  (** The following is needed by [CertiKOS], to prove that LAsm preserves [inject_neutral] for [memcpy] *)
  storebytes_inject_neutral:
    forall m b o l m' thr,
      storebytes m b o l = Some m' ->
      list_forall2 (memval_inject (Mem.flat_inj thr)) l l ->
      Plt b thr ->
      inject_neutral thr m ->
      inject_neutral thr m'
  ;

  (** The following is needed by [CertiKOS], to prove LAsm.exec_instr *)
  free_range:
    forall m1 m1' b lo hi,
      free m1 b lo hi = Some m1' ->
      (lo < hi)%Z \/ m1' = m1
  ;

  (** Idem *)
  storebytes_empty:
  forall m b ofs m',
    storebytes m b ofs nil = Some m' ->
    m' = m
  ;

  (** The following is needed by LayerLib, to prove transitivity of
      ec_mem_extends *)
  unchanged_on_trans_strong (P Q: _ -> _ -> Prop) m1 m2 m3:
    (forall b, Mem.valid_block m1 b -> forall o, P b o -> Q b o) ->
    unchanged_on P m1 m2 ->
    unchanged_on Q m2 m3 ->
    unchanged_on P m1 m3
}.

End Mem.
