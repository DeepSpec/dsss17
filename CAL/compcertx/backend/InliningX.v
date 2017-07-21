Require compcert.backend.Inlining.

Import AST.
Export Inlining.

(** In this file, we define per-module function inlining, without any proof. 

The module transformation takes an inlining function environment as a
parameter. We do not care here how it is constructed. It may very well
be [PTree.empty _] to disable any function inlining. *)

Definition transf_program (fenv: funenv):
  RTL.program -> _
  := transform_partial_program (transf_fundef fenv).
