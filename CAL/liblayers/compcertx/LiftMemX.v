Require Import Coq.Program.Basics.
Require Import Coq.Classes.Morphisms.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcertx.common.MemoryX.
Require Import liblayers.lib.Functor.
Require Import liblayers.lib.Monad.
Require Import liblayers.lib.Lens.
Require Export liblayers.lib.Lift.
Require Export liblayers.compcertx.LiftMem.

(** * Prerequisites *)

(** We're going to lift the memory operations and theorems from a base
  type [bmem] to a "richer" type [mem], which contains [bmem] as a
  component. Formally, this means that we have a [Lens mem bmem] which
  provides us with well-behaved accessors to the [bmem] component
  inside of [mem]. While this is enough to lift most of the memory
  operations and theorems, we also need to know the value of
  the empty memory state of the richer type [mem]; indeed there's no
  way we would be able to construct that just from [empty : bmem].
  However, the simpler memory state contained within this empty [mem]
  should correspond to the empty [bmem] from the base memory states. *)

Section LIFTMEM.
  Context mem bmem `{Hmem: LiftMemoryModel mem bmem}.

  Local Arguments fmap : simpl never.

  Global Instance liftmemx_spec:
    Mem.MemoryModelX bmem -> Mem.MemoryModelX mem.
  Proof.
    intros Hbmem; split.
    typeclasses eauto.
    lift π Mem.extends_extends_compose.
    lift π Mem.inject_extends_compose.
    lift π Mem.inject_compose.
    lift π Mem.extends_inject_compose.
    lift π Mem.inject_neutral_incr.
    lift π Mem.free_inject_neutral.
    lift π Mem.drop_perm_right_extends.
    lift π Mem.drop_perm_parallel_extends.
    lift π Mem.storebytes_inject_neutral.
    {
      lift_partial π Mem.free_range.
      destruct Hf; try tauto.      
      right; eauto using lens_same_context_eq, eq_sym.
    }
    {
      lift_partial π Mem.storebytes_empty.
      eauto using lens_same_context_eq, eq_sym.
    }      
    lift π Mem.unchanged_on_trans_strong.
  Qed.
End LIFTMEM.
