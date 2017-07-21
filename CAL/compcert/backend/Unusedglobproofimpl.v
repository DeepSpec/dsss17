Require Import Memory Memimpl.
Require Import Unusedglobproof.

Module Mem.
Export Memimpl.Mem.
Export Unusedglobproof.Mem.

Local Existing Instances memory_model_ops memory_model_prf.

Local Instance memory_model_x_prf:
  MemoryModelX mem.
Proof.
  split.
  exact Memimpl.Mem.zero_delta_inject.
Qed.

End Mem.
