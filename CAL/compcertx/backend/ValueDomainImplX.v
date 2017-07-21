(** In this file, we repackage an instance for
[compcert.backend.ValueDomain.MMatch] for the concrete memory
model implemented in [compcertx.common.MemimplX]. 

Indeed, those two memory models are different as they use different
implementations of [inject_neutral].

Fortunately, [MMatch] does not use [inject_neutral], so we have nothing to prove. We just need to unpack/repack.
*)

Require compcert.backend.ValueDomainImpl.
Require MemimplX.

Import Coqlib.
Export ValueDomain.
Export MemimplX.
Import ValueDomainImpl.

Lemma mmatch_inj:
   forall (bc : block_classification) (m : Memimpl.mem) (am : amem),
   ValueDomain.mmatch bc m am ->
   bc_below bc (Mem.nextblock m) -> Mem.inject (inj_of_bc bc) m m.
Proof.
  intros. eapply ValueDomainImpl.mmatch_inj; eauto.
  instantiate (1 := am). inversion H; constructor; auto.
Qed.

Global Instance mmatch_prf: MMatch Memimpl.mem (memory_model_ops := MemimplX.memory_model_ops).
Proof.  
  econstructor.
  exact mmatch_stack.
  exact mmatch_glob.
  exact mmatch_nonstack.
  exact mmatch_top.
  exact mmatch_below.
  exact load_sound.
  exact store_sound.
  exact loadbytes_sound.
  exact storebytes_sound.
  exact mmatch_ext.
  exact mmatch_free.
  exact mmatch_top'.
  exact mbeq_sound.
  exact mmatch_lub_l.
  exact mmatch_lub_r.
  exact mmatch_inj.
  exact mmatch_inj_top.
Qed.
