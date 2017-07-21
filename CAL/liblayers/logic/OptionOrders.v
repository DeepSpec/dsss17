Require Import liblayers.lib.Functor.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.logic.Structures.
Require Import liblayers.logic.LayerData.


(** * Discussion *)

(** From a pre-existing order on type [A], we can build two different
  orders on the type [option A] depending on whether we interpret
  the new element [None] as ⊥ or ⊤. For our purposes both are useful.

  Indeed consider modules for example. We say that [M1 ≤ M2] if all of
  the definitions in [M1] are present in [M2]. This means that when we
  inerpret [None] as the absence of a definition, we should think of
  it as a ⊥ element: any definition is bigger than no definition.

  But for a given symbol defined in [M1], in addition to providing the
  same definition, a larger module [M2] is also allowed to associate
  the special value [magic] with that symbol. This means that the
  symbol is "overdefined": [magic] is the result of linking two
  conflicting modules, for instance [i ↦ τ ⊕ i ↦ τ = i ↦ magic].
  Since we want [⊕] to be monotonic, and an upper bound of its
  arguments, it is natural to interpret [magic] as a top element.

  Of course, attempting to construct an actual program from a module
  containing [magic] will fail. But this failure fits right in as ⊤,
  since it results from a module that is in some sense too large.
  We like to use the option monad to express the program construction
  process, and if in this context we interpret [None] as a ⊤ element,
  then we do not need any special side-conditions when stating the
  monotonicity of program construction. *)


(** * Simple order *)

Section OPTION_LE_BOT.
  Inductive option_le {A B} (R: rel A B): rel (option A) (option B) :=
    | option_le_none:
        LowerBound (option_le R) None
    | option_le_some_def:
        (R ++> option_le R)%rel (@Some _) (@Some _).

  Global Existing Instance option_le_none.

  Global Instance option_le_subrel A B:
    Monotonic (@option_le A B) (subrel ++> subrel).
  Proof.
    intros R1 R2 HR x y Hxy.
    destruct Hxy; constructor; eauto.
  Qed.

  Global Instance option_le_subrel_params:
    Params (@option_le) 3.

  Global Instance option_le_rel {A B} (R: rel A B):
    Related (option_rel R) (option_le R) subrel.
  Proof.
    intros _ _ []; constructor; eauto.
  Qed.

  Local Instance option_le_op `(Ale: Le): Le (option A) :=
    { le := option_le (≤) }.

  Lemma option_le_refl {A} (R: relation A):
    Reflexive R -> Reflexive (option_le R).
  Proof.
    intros H.
    intros [x|]; constructor; reflexivity.
  Qed.

  Lemma option_le_trans {A} (R: relation A):
    Transitive R -> Transitive (option_le R).
  Proof.
    intros H.
    intros _ _ z [x | x y Hxy] Hz; inversion Hz; subst; clear Hz.
    - constructor.
    - constructor.
    - constructor.
      etransitivity; eassumption.
  Qed.

  Global Instance option_le_htrans {A B C} RAB RBC RAC:
    HTransitive (A:=A) (B:=B) (C:=C) RAB RBC RAC ->
    HTransitive (option_le RAB) (option_le RBC) (option_le RAC).
  Proof.
    intros HR x y z Hxy Hyz.
    destruct Hxy as [ | x y Hxy ]; try constructor.
    inversion Hyz as [ | y' z' Hyz' ]; subst; try constructor.
    htransitivity y; assumption.
  Qed.

  Global Instance option_le_rtrans {A B C} RAB RBC RAC:
    RTransitive (A:=A) (B:=B) (C:=C) RAB RBC RAC ->
    RTransitive (option_le RAB) (option_le RBC) (option_le RAC).
  Proof.
    intros HR x z Hxz.
    destruct Hxz as [ | a c Hac].
    * exists None.
      split; constructor.
    * apply rtransitivity in Hac.
      destruct Hac as (b & Hab & Hbc).
      exists (Some b).
      split; constructor; assumption.
  Qed.

  Global Instance option_le_transport_eq_some {A B} (R: rel A B) x y a:
    Transport (option_le R) x y (x = Some a) (exists b, y = Some b /\ R a b).
  Proof.
    intros Hxy Hx.
    subst; inversion Hxy; eauto.
  Qed.
End OPTION_LE_BOT.

Hint Extern 1 (Reflexive (option_le ?R)) =>
  not_evar R; apply option_le_refl : typeclass_instances.

Hint Extern 1 (Transitive (option_le ?R)) =>
  not_evar R; apply option_le_trans : typeclass_instances.


(** ** Option predicates *)

Global Instance isSome_le:
  Monotonic (@isSome) (forallr R, option_le R ++> impl).
Proof.
  intros A1 A2 RA x1 x2 Hx H.
  destruct Hx.
  * inversion H.
    discriminate.
  * exists y.
    reflexivity.
Qed.

Global Instance isNone_le:
  Monotonic (@isNone) (forallr R, option_le R --> impl).
Proof.
  intros A1 A2 RA x1 x2 Hx H.
  destruct Hx.
  * reflexivity.
  * inversion H.
Qed.

(** ** Monad operations *)

Global Instance option_map_le:
  Monotonic
    (@option_map)
    (forallr RA, forallr RB, (RA ++> RB) ++> option_le RA ++> option_le RB).
Proof.
  unfold option_map.
  rauto.
Qed.

(** FIXME: We probably want to make one of those have and explicitely
  higher priority, but it's not clear yet which one would be best.
  Contexts where [transport] is used will be particularly telling. *)

Global Instance option_rel_monad:
  MonadRel (@option_rel).
Proof.
  split; simpl; rauto.
Qed.

Global Instance option_le_monad:
  MonadRel (@option_le).
Proof.
  split; simpl; rauto.
Qed.
