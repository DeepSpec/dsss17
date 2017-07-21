Require compcert.backend.CSE.
Require ValueDomainX.

(** In this file, we define per-function/module common subexpression
elimination, without any proof. *)

(** As said in [ValueDomainX], we do not consider any optimization on
    `const' global variables, so the read-only memory abstraction will
    be empty.  
*)

Import Errors.
Import AST.
Import ValueDomainX.
Export CSE.

Definition transf_function := transf_function rmtop.

Definition transf_fundef := transf_fundef rmtop.

Definition transf_program: RTL.program -> res RTL.program :=
  transform_partial_program transf_fundef.
