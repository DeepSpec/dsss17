Require Export Coq.Classes.RelationClasses.
Require Export RelDefinitions.


(** * More classes for relation properties *)

(** In the following we introduce more typeclasses for characterizing
  properties of relations, in the spirit of the [RelationClasses]
  standard library. *)

(** ** Coreflexive relations *)

Class Coreflexive {A} (R: relation A) :=
  coreflexivity: forall x y, R x y -> x = y.

Global Instance eq_corefl {A}:
  Coreflexive (@eq A).
Proof.
  firstorder.
Qed.

Global Instance subrel_eq {A} (R: relation A):
  Coreflexive R ->
  Related R eq subrel.
Proof.
  firstorder.
Qed.
