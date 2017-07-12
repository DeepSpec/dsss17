(** * AtomGen: Generators for Atoms *)

Require Import List.
Import ListNotations.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Atom.

Instance show_atom : Show Atom.t :=
  {| show x := show (Atom.nat_of x) |}.

Fixpoint get_fresh_atoms n l :=
  match n with
  | 0 => l
  | S n' => get_fresh_atoms n' ((Atom.fresh l) :: l)
  end.

