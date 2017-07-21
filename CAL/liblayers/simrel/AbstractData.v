Require Export compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.common.Values.
Require Export compcert.common.Memdata.
Require Export compcert.common.Memtype.
Require Export compcertx.common.MemoryX.
Require Export liblayers.lib.Lens.
Require Export liblayers.lib.Lift.
Require Import liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.LiftMemX.


(** * Types of abstract data *)

(** To use [data] as a layer's abstract data, we need the associated
  initial abstract [init_data], and an invariant [data_inv] that hold
  on the initial data and is to be preserved by all primitives.

  Additionally, since the data may contain pointers, we need a
  relation [data_inject] that tells us what it means for one abstract
  state to inject to another, by analogy to Compcert's [Val.inject]
  and friends. It is not yet entierly clear what properties will be
  required of [data_inject] besides [data_inject_compose], but I list
  a few things that make sense. *)

Class AbstractDataOps data :=
  {
    init_data : data;
    data_inv: data -> Prop;
    data_inject (ι: meminj): relation data
  }.

(*
data_inv d /\
data_inject (Mem.flat_inj (Mem.nextblock m)) d d
*)

Class AbstractData data `{data_ops: AbstractDataOps data}: Prop :=
  {
    init_data_inv:
      data_inv init_data;
    init_data_inject:
      Monotonic init_data (data_inject (Mem.flat_inj glob_threshold));
    (** May need when [Mem.inject] uses [data_inject] <<<
    data_inject_compose ι ι' d1 d2 d3:
      data_inject ι d1 d2 ->
      data_inject ι' d2 d3 ->
      data_inject (compose_meminj ι ι') d1 d3;
    >>>
    By contrast this is already used for inject-neutral properties: *)
    data_inject_incr :>
      Monotonic data_inject (inject_incr ++> subrel)
  }.

Global Instance data_inject_incr_params:
  Params (@data_inject) 3.

(** Once we have this extra information, we can package it into a
  [layerdata] object. From then on, you should only use the packaged
  version (including as a type through the [ldata_type] coercion).
  You should use the underlying type directly. *)

Record layerdata :=
  ldata {
    ldata_type :> Type;
    ldata_ops : AbstractDataOps ldata_type;
    ldata_prf : AbstractData ldata_type
  }.

Global Arguments ldata _ {_ _}.
Existing Instance ldata_ops.
Existing Instance ldata_prf.
