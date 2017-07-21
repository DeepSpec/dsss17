(** * QC: QuickChick Utilities *)

Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Instance gMonad : `{Monad G} | 3 :=
  {
    ret := @returnGen;
    bind := @bindGen
  }.
