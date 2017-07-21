Require compcert.backend.Constprop.
Require ValueDomainX.

Import AST.
Import ValueDomainX.
Export Constprop.

(** Here we define per-function/module constant propagation, without any proof. *)

(** As said in [ValueDomainX], we do not consider any optimization on
    `const' global variables, so the read-only memory abstraction will
    be empty.  
*)

Definition transf_function := transf_function rmtop.

Definition transf_fundef := transf_fundef rmtop.

Definition transf_program: RTL.program -> RTL.program :=
  transform_program transf_fundef.
