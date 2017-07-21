Require Export liblayers.logic.Modules.
Require Export liblayers.logic.PTreeModules.
Require Export compcert.common.AST.
Require Export liblayers.compcertx.CGlobalVars.
Require Export compcert.cfrontend.Clight. (* Very important to have this imported AFTER AST AND CGlobalVars, to hide AST.Internal *)
Require Export compcert.cfrontend.Ctypes.

(* Functions now carry an annotation for inlining. *)

(* Also, functions whose return type is void must not return any
argument, otherwise their semantics will not be well-typed. *)

Fixpoint no_return_value_statement
         (s: statement): bool :=
  match s with
    | Sreturn (Some _) => false
    | Ssequence s1 s2 => no_return_value_statement s1 && no_return_value_statement s2
    | Sifthenelse _ s1 s2 => no_return_value_statement s1 && no_return_value_statement s2
    | Sloop s1 s2 => no_return_value_statement s1 && no_return_value_statement s2
    | Sswitch _ ls => no_return_value_labeled_statements ls
    | Slabel _ s => no_return_value_statement s
    | _ => true
  end
with no_return_value_labeled_statements
       (ls: labeled_statements): bool :=
       match ls with
         | LScons _ s ls =>
           no_return_value_statement s && no_return_value_labeled_statements ls
         | _ => true
       end.

Module InlinableFunction.

  Record t: Type :=
    make
      {
        should_inline: bool;
        function: Clight.function;
        no_return_void: fn_return function = Tvoid ->
                        no_return_value_statement (fn_body function) = true
      }.

End InlinableFunction.

Notation function := InlinableFunction.t.

(* The following coercion is very important in practice, since
   should_inline is never used in the semantics of ClightX. *)

Global Coercion InlinableFunction.function: function >-> Clight.function.

(* By contrast, we do not define either of the following two as
   coercions, since we want to have the user explicitly choose
   their inlining strategy on a per-function basis. *)

Definition inline := InlinableFunction.make true.
Definition noinline := InlinableFunction.make false.

Notation cmodule := (ptree_module function (globvar Ctypes.type)).

Global Instance cmodule_ops : ModuleOps ident function (globvar type) cmodule :=
  ptree_module_ops.

Global Instance cmodule_prf : Modules ident function (globvar type) cmodule :=
  ptree_module_prf.
