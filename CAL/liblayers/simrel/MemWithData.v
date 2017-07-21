Require Import LiftMem.
Require Import AbstractData.


(** * Memory with abstract data *)

(** Our own code always mentions abstract data and manipulates
  abstract states explicitely. This is especially important in
  relational contexts where two or more [layerdata] are involved:
  manipulating two full memory models is annoying; among other things
  it causes the resolution of [Mem.MemoryModelOps] instances to be
  rather fragile (because often the context holds multiple instances,
  which must be correctly assigned to multiple constraints, which
  requires backtracking until we hit the right combination).

  However, in order to seemlessly reuse Compcert, we sometimes *do*
  need to construct derived memory models which package the underlying
  concrete memory states together with our abstract states. This is so
  that the abstract state can be manipulated by Compcert as a
  transparent component of its memory states. *)

(** ** Base memory model *)

(** For convenience, and to avoid confusion, typeclass resolution
  loops, etc. we package everything we need for the base memory model
  into the single class below, and use that class everywhere in our
  development. We could go further and directly use Compcert's
  concrete implementation as our base and eliminate that class
  altogether, but for now we keep it. *)

Class BaseMemoryModel :=
  {
    mem : Type;
    base_mem_ops :> Mem.MemoryModelOps mem;
    base_mem_prf :> Mem.MemoryModelX mem
  }.

(** ** Memory with data *)

(** Given a base memory model, we introduce the type [mwd D] of
  "memory states with abstract data of type [D]", constructed as pairs
  of a base memory state together with an abstract state of abstract
  data type [D]. *)

Section MEM_WITH_DATA.
  Context `{Hmem: BaseMemoryModel}.
  Context (D: layerdata).

  Definition mwd := (mem * D)%type.

  (** We can now instantiate a memory model for [mwd D], by using the
    lens [fst] to lift the base memory model to such pairs. *)

  Local Instance mwd_liftmem_ops: LiftMemoryModelOps (@fst mem D) :=
    {
      liftmem_empty := (Mem.empty, init_data)
    }.

  Local Instance mwd_liftmem_prf `{Mem.MemoryModelX}:
    LiftMemoryModel (@fst mem D).
  Proof.
    split.
    typeclasses eauto.
    reflexivity.
  Qed.

  Global Instance mwd_ops: Mem.MemoryModelOps mwd | 5 := _.
  Global Instance mwd_prf: Mem.MemoryModelX mwd | 5 := _.
End MEM_WITH_DATA.

(** The following rewriting rule is useful when using the [lens_unfold]
  tactic to reduce Compcert memory operations applied to our composite
  memory states. *)

Lemma mwd_same_context_mem_eq_data `{BaseMemoryModel} D (m1 m2: mwd D):
  same_context (S := mwd D) fst m1 m2 <->
  snd m1 = snd m2.
Proof.
  apply fst_same_context_eq_snd.
Qed.

Hint Rewrite @mwd_same_context_mem_eq_data using typeclasses eauto : lens_simpl.
