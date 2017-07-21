Require Export liblayers.compcertx.CompcertStructures.
Require Export liblayers.compcertx.CompCertGlobalVars.
Require Export compcert.cfrontend.Ctypes.

Global Instance c_global_vars_ops:
  CompCertGlobalVarsOps Ctypes.type.
Proof.
  constructor.
  apply type_eq_dec.
Defined.
