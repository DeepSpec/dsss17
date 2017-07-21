Require compcert.common.Events.

Import Coqlib.
Import Values.
Import Memory.
Import Globalenvs.
Export Events.

Section WITHMEM.
Context `{memory_model_ops: Mem.MemoryModelOps}.

Lemma protect_inject:
  forall (m_init: mem) f
         (Hincr: inject_incr (Mem.flat_inj (Mem.nextblock m_init)) f)
         (Hsep: inject_separated (Mem.flat_inj (Mem.nextblock m_init)) f m_init m_init)
         b1 b2 o
         (Hf: f b1 = Some (b2, o))
         n
         (Hn: Ple n (Mem.nextblock m_init))
  ,
        ((Ple n b1 /\ Plt b1 (Mem.nextblock m_init)) <-> (Ple n b2 /\ Plt b2 (Mem.nextblock m_init))).
Proof.
  intros.
  case_eq (Mem.flat_inj (Mem.nextblock m_init) b1).
   intros ? Hinj.
   generalize Hinj.
   unfold Mem.flat_inj. destruct (plt b1 (Mem.nextblock m_init)); try discriminate.
   injection 1; intros; subst.
   apply Hincr in Hinj.
   replace b2 with b1  in * by congruence.
   tauto.
  intro.
  exploit Hsep; eauto.
  unfold Mem.valid_block.
  xomega.
Qed.

End WITHMEM.

