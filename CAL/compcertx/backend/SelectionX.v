Require compcert.backend.Selection.

Import AST.
Export Selection.

(** In this file, we define per-function/module instruction selection,
without any proof. *)

Definition sel_function dm hf f := sel_function dm hf f.

Definition sel_fundef dm hf f := sel_fundef dm hf f. 

Definition sel_program dm hf p := transform_program (V := unit) (sel_fundef dm hf) p.

