(** In this file, we repackage an instance for
[compcert.backend.magree] for the concrete memory
model implemented in [compcertx.common.MemimplX]. 

Indeed, those two memory models are different as they use different
implementations of [inject_neutral].

Fortunately, [magree] does not use [inject_neutral], so we have nothing to prove. We just need to unpack/repack.
*)

Require compcert.backend.DeadcodeproofImpl.
Require MemimplX.

Export Deadcodeproof.
Export MemimplX.

Import Coqlib.

Lemma magree_storebytes_parallel:
   forall (m1 m2 : Memimpl.mem) (P Q : locset) (b : Values.block) 
     (ofs : Z) (bytes1 : list memval) (m1' : Memimpl.mem)
     (bytes2 : list memval),
   magree m1 m2 P ->
   Mem.storebytes m1 b ofs bytes1 = Some m1' ->
   (forall (b' : Values.block) (i : Z),
    Q b' i ->
    b' <> b \/ i < ofs \/ ofs + Z.of_nat (length bytes1) <= i -> P b' i) ->
   list_forall2 memval_lessdef bytes1 bytes2 ->
   exists m2' : Memimpl.mem,
     Mem.storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q.
Proof.
  unfold Mem.storebytes.
  unfold memory_model_ops. unfold storebytes.
  intros.
  destruct (is_empty bytes1); destruct (is_empty bytes2); eauto using DeadcodeproofImpl.magree_storebytes_parallel. 
  * inv H0. simpl in *.
    esplit. split. reflexivity.
    eapply DeadcodeproofImpl.magree_monotone; eauto.
    intros. destruct (zle ofs ofs0); eapply H1; eauto; intuition omega.
  * apply is_empty_list_forall2 in H2. tauto.
  * apply is_empty_list_forall2 in H2. tauto.
Qed.

Lemma magree_free:
  forall m1 m2 (P Q: locset) b lo hi m1',
  DeadcodeproofImpl.magree m1 m2 P ->
  MemimplX.free m1 b lo hi = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ ~(lo <= i < hi) ->
                P b' i) ->
  exists m2', MemimplX.free m2 b lo hi = Some m2' /\ DeadcodeproofImpl.magree m1' m2' Q.
Proof.
  unfold MemimplX.free. intros.
  destruct (zle hi lo); eauto using DeadcodeproofImpl.magree_free.
  inv H0.
  esplit. split. reflexivity.
  eapply DeadcodeproofImpl.magree_monotone; eauto.
  intros. eapply H1; eauto. right. omega.
Qed.

Global Instance magree_ops
: Deadcodeproof.MAgreeOps Memimpl.mem (memory_model_ops := MemimplX.memory_model_ops)
:= {|
    magree := DeadcodeproofImpl.magree
  |}.

Global Instance magree_prf
: Deadcodeproof.MAgree Memimpl.mem (memory_model_ops := MemimplX.memory_model_ops).
Proof.
  constructor.
  exact DeadcodeproofImpl.ma_perm.
  exact DeadcodeproofImpl.magree_monotone.
  exact DeadcodeproofImpl.mextends_agree.
  exact DeadcodeproofImpl.magree_extends.
  exact DeadcodeproofImpl.magree_loadbytes.
  exact DeadcodeproofImpl.magree_load.
  exact magree_storebytes_parallel.
  exact DeadcodeproofImpl.magree_store_parallel.
  now storebytes_tac DeadcodeproofImpl.magree_storebytes_left.
  exact DeadcodeproofImpl.magree_store_left.
  exact magree_free.
Qed.
