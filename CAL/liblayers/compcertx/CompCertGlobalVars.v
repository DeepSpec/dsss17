Require Export liblayers.lib.Decision.
Require Export compcert.common.AST.
Require Export liblayers.logic.GlobalVars.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.

Class CompCertGlobalVarsOps (T: Type): Type :=
  {
    compcert_globalvar_eq_dec :> EqDec T
  }.

Global Instance compcert_globalvar_to_globalvar
       {T}
       {compcert_globalvar_ops: CompCertGlobalVarsOps T}:
  GlobalVarsOps (globvar T).
Proof.
  constructor.
  intros [] [].
  intros.
  red.
  repeat decide equality;
    auto using Int.eq_dec, Int64.eq_dec, Ptrofs.eq_dec, Float.eq_dec, Float32.eq_dec.
  apply compcert_globalvar_eq_dec.
Defined.
