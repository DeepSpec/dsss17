(** * TImp: Case Study: a Typed Imperative Language *)

(* BCP: Some random things to do soon:
     - 80-column-ify
     - Turn exercises into SF-style using EX tags
     - Start producing a TERSE version that we can use for lecturing
*)

Set Warnings "-notation-overridden,-parsing".
Set Warnings "-extraction-opaque-accessed,-extraction".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

From QuickChick Require Import QuickChick Tactics.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

Require Import Equalities.
Require Import QC.


(** Having seen a basic overview of QuickChick in the previous
    chapter, we can now dive into a more realistic case study: a typed
    variant of Imp, the simple imperative language introduced in
    _Logical Foundations_.  The original Imp variant presented in the
    first volume of Software Foundations syntactically separates
    boolean and arithmetic expressions: [bexp] ranges over boolean
    expressions, while [aexp] ranges over arithmetic ones.  Moreover,
    variables are only allowed in [aexp] and only take arithmetic
    values.

    In typed Imp (TImp) we collapse the expression syntax and allow
    variables to range over both numbers and booleans. With the
    unified syntax, we introduce the notion of well-typed Imp
    expressions and programs: where every variable only ranges over
    values of a single type throughout the whole program.  We then
    give an operational semantics to TImp in the form of a partial
    evaluation function; partial, since in the unified syntax one
    could attempt to write expressions such as [0 + True].

    A common mantra in functional programming is "well-typed programs
    cannot go wrong"; TImp is no exception to that rule. The soundness
    property for TImp will state that evaluating well-typed
    expressions and programs always succeeds. This is another example
    of a _conditional_ property. As we saw in the previous chapter,
    testing such properties requires custom generators.  In this
    chapter, we will show how to scale the techniques for writing
    generators to more realistic generators for well-typed expressions
    and programs. In addition, we will also demonstrate the notion and
    necessity of custom shrinkers preserving invariants, a problem
    dual to that of custom generators. *)

(* ################################################################# *)
(** * Atoms, Types and Contexts *)

(* ================================================================= *)
(** ** Atoms *)

(* Leo: How can we cite things in SF-style? *)
(* BCP: Do you mean bibliographic citations?  Or URLs?  Urls are
   http://likethis and bib stuff is \Bib{Like This, 2017}, plus add
   it to Bib.v (following the style of SF) and make sure Bib.v is in
   the Makefile. *)
(* Leo: Decide: atoms, [Atom]s or [Atoms]? *)
(* BCP: I think switching back and forth between the first and second is fine. *)
(** For the type of identifiers of TImp we are going to borrow (a simplified
    version of) [Atom] from Penn's Metatheory library. [Atom] is essentially a
    wrapper around [nat] which supports decidable equality and [fresh]: given
    any finite set of atoms, one can produce one that is distinct from all of
    the atoms in the set. *)

(* BCP: Say what UsualDecidableType means *)
Module Type ATOM <: UsualDecidableType.

  Parameter t : Set.
  Parameter eq_dec : forall (x y:t), {x = y} + {x <> y}.
  Parameter fresh : list t -> t.
  Parameter nat_of: t -> nat.

(* BCP: Say what this means.  Remember HIDEFROMHTML still leaves it in
   the .v where people will want to understand it. *)
  Include HasUsualEq <+ UsualIsEq.
End ATOM.

Module Atom : ATOM.

(** Internally, an [Atom] is just a natural number... *)

  Definition t := nat.

(** ...which means decidable equality comes for free from the standard library: *)

  Definition eq_dec := eq_nat_dec.

(** To compute a fresh natural number given a list of natural numbers,
    we can just produce the number that is 1 larger than the maximum
    element: *)

  Fixpoint max_elt (al:list t) : t :=
    match al with
      | nil => 0
      | n'::al' => max n' (max_elt al')
    end.

  Definition fresh (al:list t) : t :=
    S (max_elt al).

  Include HasUsualEq <+ UsualIsEq.

(** We also need a way of printing atoms. To support that, we include a
    [nat_of] function that exposes the internal natural number. *)

  Definition nat_of (a : nat) := a.

End Atom.

(** We can take advantage of the [nat_of] function of [Atom]s, as well
    as the [Show] instance of [nat] to print [Atom]s. *)

Instance show_atom : Show Atom.t :=
  {| show x := show (Atom.nat_of x) |}.

(** To generate identifiers for TImp, we will use a recursive functions
    that generates [n] fresh [Atom]s starting from the empty list. *)

Fixpoint get_fresh_atoms n l :=
  match n with
  | 0 => l
  | S n' => get_fresh_atoms n' ((Atom.fresh l) :: l)
  end.

(* ================================================================= *)
(** ** Types *)

(** To continue, here is the type of types in TImp, [ty]: *)

Inductive ty := TBool | TNat.

(** TImp has two types of expressions: booleans and natural numbers. *)

(** As with all user-defined datatypes, in order to use [ty] in testing
    we will need [Arbitrary], [Show] and an equality [Dec] instance.

    In QC.v, we saw how one can go about writing such generators by hand.
    However, that process can largely be automated, especially for
    simple inductive types (like [ty], [nat], [list], [tree], etc.).
    QuickChick provides a top-level vernacular command to derive
    such instances.
 *)

Derive (Arbitrary, Show) for ty.

(* LEO: Show output? (xxx is defined). Print the derived ones as well? *)
(* BCP: My convention is to show the output only if it's interesting. *)

(** The decidable equality instances are not yet derived fully automatically.
    However, the boilerplate for it is largely straightforward. *)

(* Leo: they've already seen the Dec = boilerplate right? *)
(* BCP: No, I don't think so. And I guess I'd rather keep it here, to
   avoid making Typeclases depend on SSR. *)

Instance eq_dec_ty (x y : ty) : Dec (x = y).
Proof. constructor; unfold ssrbool.decidable; decide equality. Defined.

(* ================================================================= *)
(** ** List Map with Decidable Equality *)

(** To encode typing environments and, later on, states, we will need
    maps from atoms to values. The function-based representation in base
    Imp is not suited for testing: we will need to be able to access the
    domain of the map, fold over it and test for equality; all operations
    not supported by (Coq) functions. Therefore, we introduce a small
    list-based map that takes usual decidable types (like [Atom]) as input.

    The operations we need are:

       - [empty] : To create the empty map.
       - [get]   : To look up the binding of an element, if any.
       - [set]   : To update the binding of an element.
       - [dom]   : To get the list of keys in the map.
  *)

Module Type Map (K:UsualDecidableType).

 Section withv.
   Variable V : Type.

   Parameter t : Type -> Type.
   Parameter empty : t V.
   Parameter get : t V -> K.t -> option V.
   Parameter set : t V -> K.t -> V -> t V.
      Parameter dom : t V -> list K.t.
       End withv.

End Map.

(** The implementation of the map is a simple association list.
    If a list contains multiple tuples with the same key, then
    the binding of the key in the map is the one that appears firt
    in the list; that is, bindings can be shadowed.
  *)

Module ListMap (K:UsualDecidableType) <: Map K.

 Section withv.
   Context {V : Type}.

   Definition t := list (K.t * V).

   Definition empty : t := [].

   Fixpoint get m k : option V :=
     match m with
       | [] => None
       | (k', v) :: m' => if K.eq_dec k k'
                          then Some v
                          else get m' k
     end.

   Definition set (m:t) (k:K.t) (v:V) : t :=
     (k, v) :: m.

   Fixpoint dom (m:t) : list K.t :=
     match m with
       | [] => []
       | (k', v) :: m' => k' :: dom m'
     end.

 End withv.

End ListMap.

(** We instantiate this functor with [Atom], yielding [AtomMap] our
    map with [Atom] as the key type. *)

Module AtomMap := ListMap (Atom).

(** We introduce a simple inductive proposition, [bind_in m x a], that
    holds precisely when the binding of some [Atom] [x] is equal to [a] in
    [m]
  *)
(* BCP: My usual convention is to put ending comment brackets on the
   same line as the end of the comment... *)

(* bound_in? *)
(* BCP: bound_to? *)
Inductive bind_in {A} : @AtomMap.t A -> Atom.t -> A -> Prop :=
  | Bind : forall x m a, AtomMap.get m x = Some a -> bind_in m x a.

(** We can now decide whether [bind_in m x a] holds for a given
    arrangement of [m], [x] and [a]. In a first reading, you can
    skip the next few paragraphs that deal with partially automating
    the proofs for such instances.
  *)
(* BCP: Be explicit about where to skip to.  (Or perhaps break it up
   into subsections so that people can just skip the whole
   subsection?)  [Ah, I see that it's already done this way,
   basically.] *)

Instance dec_bind_in {A : Type} Gamma x (T : A)
         `{D : forall (x y : A), Dec (x = y)}
  : Dec (bind_in Gamma x T) := {}.
Proof.
  unfold ssrbool.decidable.
  destruct (AtomMap.get Gamma x) eqn:Get.

(** After unfolding [decidable] and destructing [AtomMap.get Gamma x], we are
    left with two subgoals. In the first, we know that [AtomMap.get Gamma x =
    Some a] and effectively want to decide whether [AtomMap.get Gamma x = Some
    T] or not. Which means we need to decide whether [a = T]. Thankfully,
    we can decide that using our hypothesis [D].
  *)

  - destruct (D a T) as [[Eq | NEq]]; subst.

(** At this point, the first goal can be immediately decided positevely
    using constructor.
  *)

    + left. constructor. auto.

(** In the second subgoal, we can show that [bind_in] doesn't hold. *)

    + right; intro Contra; inversion Contra; subst; clear Contra.
      congruence.

(** Both of these tactic patterns are very common in non-trival [Dec]
    instances. For that reason, we automate them a bit using LTac.
  *)

Abort.

(** A lot of the time, we can immediately decide a property positevly
    using constructor applications. That is captured in [solve_left]. *)

Ltac solve_left  := try solve [left; econstructor; eauto].

(** Much of the time, we can also immediately decide that a property
    doesn't hold by assuming it, doing inversion and using [congruence].
  *)

Ltac solve_right :=
  let Contra := fresh "Contra" in
  try solve [right; intro Contra; inversion Contra; subst; clear Contra;
             eauto; congruence].

(** We group both in a single tactic, which does nothing at all if
    it fails to solve a goal, thanks to [try solve]. *)

Ltac solve_sum := solve_left; solve_right.

(** We can now prove the [Dec] instance more concisely. *)

Instance dec_bind_in {A : Type} Gamma x (T : A)
         `{D : forall (x y : A), Dec (x = y)}
  : Dec (bind_in Gamma x T) := {}.
Proof.
  unfold ssrbool.decidable.
  destruct (AtomMap.get Gamma x) eqn:Get; solve_sum.
  destruct (D a T) as [[Eq | NEq]]; subst; solve_sum.
Defined.

(* ================================================================= *)
(** ** Contexts *)

(** Typing contexts in TImp are just maps from atoms to types. *)

Definition context := @AtomMap.t ty.

(** Given a context [Gamma] and a type [T], we can try to generate
    a random [Atom] whose binding in [Gamma] is [T].

    We filter out all of the elements in [Gamma] whose type is
    equal to [T] and then, for each [(a,T')] that remains we
    return the binding [a]. We use the [oneof] combinator to
    pick an generator from that list at random.

    However, the filtered list might be empty; to facilitate
    that case, [oneof] also takes a default generator, here [ret None].
  *)

Definition gen_typed_atom_from_context (Gamma : context) (T : ty)
                                     : G (option Atom.t) :=
  oneof (ret None)
        (List.map (fun '(a,T') => ret (Some a))
                  (List.filter (fun '(a,T') => T = T'?) Gamma)).

(** We also need to generate a typing context to begin with. Given
    some natural number [n] to serve as the size of the context,
    we first create its domain, [n] fresh atoms.

    We then create [n] arbitrary types with [vectorOf], using the
    [Gen] instance for [ty] we derived earlier.

    Finally, we zip ([List.combine]) the domain with the ranges and
    fold over the resulting, inserting each binding into a map.
  *)

Definition gen_context (n : nat) : G context :=
  let domain := get_fresh_atoms n [] in
  range <- vectorOf n arbitrary ;;
  ret (List.fold_left (fun m '(k, v) => AtomMap.set m k v)
                      (List.combine domain range) AtomMap.empty).

(* ################################################################# *)
(** * Expressions *)

(** We are now ready to introduce the syntax of expressions in TImp.
    The original Imp had two distinct types of expressions: arithmetic
    and boolean expressions, while variables were only allowed to
    range over natural numbers. In TImp, we extend variables to range
    over boolean values as well, collapsing the expressions into a single
    type [exp].

 *)

Inductive exp : Type :=
  | EVar : Atom.t -> exp
  | ENum : nat -> exp
  | EPlus : exp -> exp -> exp
  | EMinus : exp -> exp -> exp
  | EMult : exp -> exp -> exp
  | ETrue : exp
  | EFalse : exp
  | EEq : exp -> exp -> exp
  | ELe : exp -> exp -> exp
  | ENot : exp -> exp
  | EAnd : exp -> exp -> exp.

(* BCP: This comment is kind of a no-op.  Fine to just omit it and similar ones. *)
(** To be able to print expressions we can derive [Show] *)

Derive Show for exp.

(** If we tried to derive [Arbitrary] for expressions we would
    encounter an error message:

    ==> Unable to satisfy the following constraints:
        [Gen Atom.t]

    Indeed, we don't have an arbitrary instance for [Atom.t].

  *)

(* EX 3 : Write an instance for [Gen] for [Atom.t], using
   [elements] and [get_fresh_atoms].
 *)

(* FILL IN HERE *)

(* ================================================================= *)
(** ** Typed Expressions *)

(** The following inductive relation characterizes well-typed expressions
    of a particular type. It is rather unsurprising, using [bind_in] to
    access the typing context in the variable case *)

(* BCP: Maybe define a Notation for this to lighten the presentation? *)

Inductive has_type : context -> exp -> ty -> Prop :=
| Ty_Var : forall x T Gamma,
    bind_in Gamma x T ->
    has_type Gamma (EVar x) T
| Ty_Num : forall Gamma n,
    has_type Gamma (ENum n) TNat
| Ty_Plus : forall Gamma e1 e2,
    has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
    has_type Gamma (EPlus e1 e2) TNat
| Ty_Minus : forall Gamma e1 e2,
    has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
    has_type Gamma (EMinus e1 e2) TNat
| Ty_Mult : forall Gamma e1 e2,
    has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
    has_type Gamma (EMult e1 e2) TNat
| Ty_True : forall Gamma,
    has_type Gamma ETrue TBool
| Ty_False : forall Gamma,
    has_type Gamma EFalse TBool
| Ty_Eq : forall Gamma e1 e2,
    has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
    has_type Gamma (EEq e1 e2) TBool
| Ty_Le : forall Gamma e1 e2,
    has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
    has_type Gamma (ELe e1 e2) TBool
| Ty_Not : forall Gamma e,
    has_type Gamma e TBool ->
    has_type Gamma (ENot e) TBool
| Ty_And : forall Gamma e1 e2,
    has_type Gamma e1 TBool -> has_type Gamma e2 TBool ->
    has_type Gamma (EAnd e1 e2) TBool.

(* Move to Tactics.v *)
(* BCP: And we may need to hack sf/Common.Makefile a bit so that we
   can leave this file out of the TOC. *)
Ltac solve_inductives Gamma :=
  repeat (match goal with
      [ IH : forall _ _, _ |- _ ] =>
      let H1 := fresh "H1" in
      pose proof (IH TNat Gamma) as H1;
      let H2 := fresh "H2" in
      pose proof (IH TBool Gamma) as H2;
      clear IH;
      destruct H1; destruct H2; solve_sum
    end).

(** Typing in TImp is decidable: given an expression [e], a context [Gamma]
    and a type [T], we can decide whether [has_type Gamma e T] holds.
    We implement that in a [Dec] instance. *)

Instance dec_has_type (e : exp) (Gamma : context) (T : ty)
  : Dec (has_type Gamma e T) :=
  { dec := _ }.
Proof with solve_sum.
  (* I need move: *)
  generalize dependent Gamma.
  generalize dependent T.
  induction e; intros T Gamma; unfold ssrbool.decidable;
    try solve [destruct T; solve_sum];
    try solve [destruct T; solve_inductives Gamma].
  (* bind_in case *)
  destruct (dec_bind_in Gamma t T); destruct dec; solve_sum.
Defined.

(* EX 4 : Derive [Arbitrary] for expressions and write a conditional
    property that is always true if an expression is well-typed. Try to
    check that property. What happens?

    (You will need to provide a [Shrink] instance for [Atom]. The
    result of shrinking an atom can be empty for now)
  *)

(* FILL IN HERE *)

(* ================================================================= *)
(** ** Generator for Typed expressions *)

(** Instead of generating expressions and filtering them using
    has_type, we can be smarter and generate well typed expressions
    for a given context directly. It is common for conditional
    generators to return [option]s of the underlying type, allowing
    the possibility of failure if a wrong choice is made. For example,
    if we wanted to generate an expression of type [TNat] and chose to
    do that by generating a variable, then we might not be able to
    actually do that (e.g. if the context is empty).

*)

(** To chain two different generetors with type [G (option A)], we need to
    execute the first generator, match on its result, and, when it is a [Some],
    apply the second generator.
  *)

Definition bindGenOpt {A B : Type} (gma : G (option A)) (k : A -> G (option B))
  : G (option B) :=
  ma <- gma ;;
  match ma with
  | Some a => k a
  | None => ret None
  end.

(** This pattern is common enough that QuickChick provides explicit monadic
    notation support *)

Definition GOpt A := G (option A).

Instance gOptMonad : `{Monad GOpt} :=
  {
    ret A x := returnGen (Some x);
    bind A B m k := bindGenOpt m k
  }.

(** Which brings us to our first large sized generator for typed expressions.
    We asumme that [Gamma] and [T] are inputs to the generation process. We also
    use a [size] parameter to control the depth of generated expressions.

    For the shape of the generator we turn to [has_type], the relation we are
    trying to satisfy. First of all, we need to identify which cases can be
    "base cases" and which need to be recursive. In the case of has_type,
    [Ty_Var], [Ty_Num], [Ty_True] and [Ty_False] are the only cases where
    [has_type] doesn't appear as a side-condition, and are therefore
    base cases.

    We will use the [backtrack] combinator

      [ backtrack : list (nat * G (option ?A)) -> G (option ?A) ]

    which operates similarly to frequency for optional generators.
    However, unlike frequency, if the generator that was selected
    first fails (returns [None]), then [backtrack] proceeds to pick
    one of the remaining ones until it runs out or one succeeds.

  *)

(** We will break the generator into smaller bits.

    Let's start with the first derivation of [has_type], [Ty_Var].

    [Ty_Var : forall (x : Atom.t) (T : ty) (Gamma : AtomMap.t),
              bind_in Gamma x T -> has_type Gamma (EVar x) T]

    Since we want to generate expressions such that [has_type Gamma e
    T] holds given [Gamma] and [T], following this rule we would need
    to generate an expression of the form [EVar x] for some atom
    [x]. The side condition [bind_in Gamma x T] informs what that atom
    must be: it must be an [Atom] from the context with the
    appropriate type. That's exactly what [gen_typed_atom_from_context] did.

  *)

Definition gen_typed_evar (Gamma : context) (T : ty) : G (option exp) :=
  x <- gen_typed_atom_from_context Gamma T;;
  ret (EVar x).

(** For the rest of the base cases, we need to pattern match on the
    input type [T]: if it is [TNat], then we need to generate an arbitrary
    integer [n] and wrap it in an [ENum]; if it is [TBool], we need to pick
    between [ETrue] and [EFalse].

    Since [base] will be the input to [backtrack], we need to add natural numbers
    as weights. Since this example is simple enough, we selected [1] for
    all weights. In larger applications, we would need to fine tune these
    weights to obtain a desired distribution.
  *)

Definition base Gamma T :=
      (2, gen_typed_evar Gamma T) ::
      match T with
      | TNat  => [ (2, n <- arbitrary;; ret (Some (ENum n)))]
      | TBool => [ (1, ret ETrue)
                 ; (1, ret EFalse) ]
      end.

(** In the recursive branches, we also need to pattern match on [T].
    If, for example, [T = TNat], then we can only satisfy typing
    derivations whose conclusion is of the form [has_type Gamma _ TNat],
    i.e. [Ty_Plus], [Ty_Minus] and [Ty_Mult].

    Consider [Ty_Plus]: we will need to recursively generate
    expressions [e1] and [e2] that have type [TNat], with potentially smaller
    sizes to ensure termination.

    We put everything together in the following generator *)

Fixpoint gen_exp_typed_sized (size : nat) (Gamma : context) (T : ty) : G (option exp) :=
  let base := base Gamma T in
  let recs size' :=
      match T with
      | TNat => [ (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;;
                      e2 <- gen_exp_typed_sized size' Gamma TNat ;;
                      ret (EPlus e1 e2))
                ; (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;;
                      e2 <- gen_exp_typed_sized size' Gamma TNat ;;
                      ret (EMinus e1 e2))
                ; (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;;
                      e2 <- gen_exp_typed_sized size' Gamma TNat ;;
                      ret (EMult e1 e2)) ]
      | TBool => [ (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;;
                       e2 <- gen_exp_typed_sized size' Gamma TNat ;;
                       ret (EEq e1 e2))
                 ; (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;;
                       e2 <- gen_exp_typed_sized size' Gamma TNat ;;
                       ret (ELe e1 e2))
                 ; (size, e1 <- gen_exp_typed_sized size' Gamma TBool ;;
                       ret (ENot e1))
                 ; (size, e1 <- gen_exp_typed_sized size' Gamma TBool ;;
                       e2 <- gen_exp_typed_sized size' Gamma TBool ;;
                       ret (EAnd e1 e2)) ]
      end in
  match size with
  | O =>
    backtrack base
  | S size' =>
    backtrack (base ++ recs size')
  end.

(** When writing such complex generators, it's good to have small tests
    that ensure that you are generating what you expect. For example, we
    would expect [gen_exp_typed_sized] to always return expressions that are
    well typed.

    We can use [forAll] to encode such a property.
  *)

Definition gen_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in
  forAll (gen_context num_vars) (fun Gamma =>
  forAll arbitrary (fun T =>
  forAll (gen_exp_typed_sized top_level_size Gamma T) (fun me =>
  match me with
  | Some e => (has_type Gamma e T)?
  | _ => false (* this should NEVER fail *)
  end))).

(* QuickChick gen_typed_has_type. *)

(* ################################################################# *)
(** * Values and States *)

(* ================================================================= *)
(** ** Values *)

(** In original Imp, variables range over natural numbers, so states were just
    maps from identifiers to [nat]. Since we wanted to extend this to also
    include booleans, we introduce the type of [value]s which includes both.
  *)


Inductive value := VNat : nat -> value | VBool : bool -> value.

Derive Show for value.

(** We can also quickly define a typing relation for values, a Dec instance
    for it and a generator for values of a given type. *)

Inductive has_type_value : value -> ty -> Prop :=
  | TyVNat  : forall n, has_type_value (VNat  n) TNat
  | TyVBool : forall b, has_type_value (VBool b) TBool.

Instance dec_has_type_value v T : Dec (has_type_value v T).
Proof. constructor; unfold ssrbool.decidable.
destruct v; destruct T; solve_sum.
Defined.

Definition gen_typed_value (T : ty) : G value :=
  match T with
  | TNat  => n <- arbitrary;; ret (VNat n)
  | TBool => b <- arbitrary;; ret (VBool b)
  end.

(* ================================================================= *)
(** ** States *)

(** States in TImp are just maps from atoms to values *)

Definition state := @AtomMap.t value.

(** We introduce an inductive relation that specifies when a state
    is well-typed according to a context: that is, when all of
    its variables are mapped to values of appropriate types.

    We encode this in an element-by-element style inductive relation:
    empty states are only well-typed with respect to an empty context,
    while non-empty states need to map their head atom to a value of the
    appropriate type and their tails must also be well typed.
  *)

Inductive typed_state : context -> state -> Prop :=
| TS_Empty : typed_state AtomMap.empty AtomMap.empty
| TS_Elem  : forall x v T st Gamma,
    has_type_value v T -> typed_state Gamma st ->
    typed_state ((x,T)::Gamma) ((x,v)::st).

Instance dec_typed_state Gamma st : Dec (typed_state Gamma st).
Proof.
constructor; unfold ssrbool.decidable.
generalize dependent Gamma.
induction st; intros; destruct Gamma; solve_sum.
destruct a as [a v]; destruct p as [a' T].
destruct (Atom.eq_dec a a'); solve_sum.
subst; specialize (IHst Gamma); destruct IHst; solve_sum.
destruct (dec_has_type_value v T); destruct dec; solve_sum.
Defined.

(** To write a generator for well typed states given a context [Gamma],
    we use the combinator [sequenceGen : list (G A) -> G (list A)], that
    receives a list of generators and produces a generator of lists.
    This is what Haskell's [sequence] combinator would do for the monad [G].

    We just need to iterate ([map]) through the context, producing
    an arbitrary value of the appropriate type for each pair [(x,T)]. The
    [sequenceGen] combinator will then chain all those generators in sequence,
    producing a generator for well-typed states *)

Definition gen_typed_state (Gamma : context) : G state :=
  sequenceGen (List.map (fun '(x, T) =>
                           v <- gen_typed_value T;;
                           ret (x, v)) Gamma).

(* ################################################################# *)
(** * Evaluation *)

(** Our evaluation function, takes a state and an expression and returns
    an optional value, assuming that the expression has a type
    with respect to the state.
  *)

Fixpoint eval (st : state) (e : exp) : option value :=
  match e with
  | EVar x => AtomMap.get st x
  | ENum n => Some (VNat n)
  | EPlus e1 e2 =>
    match eval st e1, eval st e2 with
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 + n2))
    | _, _ => None
    end
  | EMinus e1 e2 =>
    match eval st e1, eval st e2 with
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 - n2))
    | _, _ => None
    end
  | EMult e1 e2 =>
    match eval st e1, eval st e2 with
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 * n2))
    | _, _ => None
    end
  | ETrue       => Some (VBool true  )
  | EFalse      => Some (VBool false )
  | EEq e1 e2 =>
    match eval st e1, eval st e2 with
    | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 =? n2))
    | _, _ => None
    end
  | ELe e1 e2 =>
    match eval st e1, eval st e2 with
    | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 <? n2))
    | _, _ => None
    end
  | ENot e =>
    match eval st e with
    | Some (VBool b) => Some (VBool (negb b))
    | _ => None
    end
  | EAnd e1 e2  =>
    match eval st e1, eval st e2 with
(* Leo: Stupidest bug possible *)
    | Some (VBool b), Some (VNat n2) => Some (VBool (negb b))
(*    | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2)) *)
    | _, _ => None
    end
  end.

(** Type Soundness states that if we have an expression [e] of a given type [T],
    as well as a well-typed state [st], then evaluating [e] in [st] will
    never fail.*)

Definition isNone {A : Type} (m : option A) :=
  match m with
  | None => true
  | _ => false
  end.

Conjecture expression_soundness :
  forall Gamma st e T,
    typed_state Gamma st ->
    has_type Gamma e T ->
    isNone (eval st e) = false.

(** To test that property, we construct an appropriate checker *)

Definition expression_soundness_exec :=
  let num_vars := 4 in
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>
  forAll (gen_exp_typed_sized 3 Gamma T) (fun me =>
  match me with
  | Some e => negb (isNone (eval st e))
  | _ => false
  end)))).

(* QuickChick expression_soundness_exec. *)

(** But where is the bug? :o
    We need shrinking. *)

(* ================================================================= *)
(** ** Shrinking for Expressions *)

(** We not only need to shrink expressions, we need to shrink them
    so that their type is preserved! To accomplish that we need to follow
    a reverse procedure than with the generators: look at a typing derivation
    and see what parts of it we can shrink to appropriate types so that
    the entire thing is preserved.

    For example, to shrink [EPlus e1 e2], we could shrink [e1] or [e2] preserving
    their [TNat] type, or shrink to [e1] or [e2] themselves. However, for
    [EEq e1 e2], we could to shrink [e1] or [e2] again preserving their [TNat]
    types, but we couldn't shrink to [e1] or [e2] as their type is wrong.
 *)

Fixpoint shrink_exp_typed (T : ty) (e : exp) : list exp :=
  match e with
  | EVar _ =>
    match T with
    | TNat => [ENum 0]
    | TBool => [ETrue ; EFalse]
    end
  | ENum _ => []
  | ETrue => []
  | EFalse => [ETrue]
  | EPlus e1 e2 =>
    e1 :: e2
       :: (List.map (fun e1' => EPlus e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EPlus e1 e2') (shrink_exp_typed T e2))
  | EMinus e1 e2 =>
    e1 :: e2 :: (EPlus e1 e2)
       :: (List.map (fun e1' => EMinus e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EMinus e1 e2') (shrink_exp_typed T e2))
  | EMult e1 e2 =>
    e1 :: e2 :: (EPlus e1 e2)
       :: (List.map (fun e1' => EMult e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EMult e1 e2') (shrink_exp_typed T e2))
  | EEq e1 e2 =>
    ETrue :: EFalse
       :: (List.map (fun e1' => EEq e1' e2) (shrink_exp_typed TNat e1))
       ++ (List.map (fun e2' => EEq e1 e2') (shrink_exp_typed TNat e2))
  | ELe e1 e2 =>
    ETrue :: EFalse :: (EEq e1 e2)
       :: (List.map (fun e1' => ELe e1' e2) (shrink_exp_typed TNat e1))
       ++ (List.map (fun e2' => ELe e1 e2') (shrink_exp_typed TNat e2))
  | ENot e =>
    ETrue :: EFalse :: e :: (List.map ENot (shrink_exp_typed T e))
  | EAnd e1 e2 =>
    ETrue :: EFalse :: e1 :: e2
       :: (List.map (fun e1' => EAnd e1' e2) (shrink_exp_typed TBool e1))
       ++ (List.map (fun e2' => EAnd e1 e2') (shrink_exp_typed TBool e2))
  end.

(** Similarly with generators, we can have a sanity check for our shrinking:
    Given a random expression of a given type, all of the results of [shrink]
    should have the same type. *)

Definition shrink_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in
  forAll (gen_context num_vars) (fun Gamma =>
  forAll arbitrary (fun T =>
  forAll (gen_exp_typed_sized top_level_size Gamma T) (fun me =>
  match me with
  | Some e =>
    List.forallb (fun e' => (has_type Gamma e' T)?) (shrink_exp_typed T e)
  | _ => false (* this should NEVER fail *)
  end))).

(* QuickChick shrink_typed_has_type. *)

(* ================================================================= *)
(** ** Back to Soundness *)

(** To lift the shrinker to optional expressions, QuickChick provides a [lift]
    function. *)

Definition lift_shrink {A : Type} (shr : A -> list A) (m : option A) : list (option A) :=
  match m with
  | Some x => List.map Some (shr x)
  | _ => []
  end.

(** Armed with shrinking we can pinpoint the bug in the [EAnd] branch
    and remove the obvious bug. *)

Definition expression_soundness_exec' :=
  let num_vars := 4 in
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>
  forAllShrink (gen_exp_typed_sized 3 Gamma T) (lift_shrink (shrink_exp_typed T)) (fun me =>
  match me with
  | Some e => negb (isNone (eval st e))
  | _ => false
  end)))).

(* QuickChick expression_soundness_exec'. *)

(* ################################################################# *)
(** * Well-typed programs *)

(** We now introduce TImp commands, exactly like the ones in Imp *)

Inductive com : Type :=
  | CSkip  : com
  | CAss   : Atom.t -> exp -> com
  | CSeq   : com    -> com -> com
  | CIf    : exp    -> com -> com -> com
  | CWhile : exp    -> com -> com.

Derive Show for com.

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  To avoid conflicts with Coq's built-in notations,
    we keep this light -- in particular, we don't introduce any
    notations for [exps] and [exps] to avoid confusion with the
    numeric and boolean operators we've already defined. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(* ================================================================= *)
(** ** Well-typed commands *)

Inductive well_typed_com : context -> com -> Prop :=
  | TSkip : forall Gamma, well_typed_com Gamma CSkip
  | TAss  : forall Gamma x e T,
      bind_in Gamma x T -> has_type Gamma e T ->
      well_typed_com Gamma (CAss x e)
  | TSeq  : forall Gamma c1 c2,
      well_typed_com Gamma c1 -> well_typed_com Gamma c2 ->
      well_typed_com Gamma (CSeq c1 c2)
  | TIf : forall Gamma b c1 c2,
      has_type Gamma b TBool ->
      well_typed_com Gamma c1 -> well_typed_com Gamma c2 ->
      well_typed_com Gamma (CIf b c1 c2)
  | TWhile : forall Gamma b c,
      has_type Gamma b TBool -> well_typed_com Gamma c ->
      well_typed_com Gamma (CWhile b c).

(** Decidable instance for well-typed *)

(** A couple of theorems to help the decidability proof *)

Theorem bind_deterministic Gamma x (T1 T2 : ty) :
  bind_in Gamma x T1 -> bind_in Gamma x T2 ->
  T1 = T2.
Proof.
  destruct T1; destruct T2; intros H1 H2; eauto;
    inversion H1; inversion H2; congruence.
Qed.

Theorem has_type_deterministic Gamma e (T1 T2 : ty) :
  has_type e Gamma T1 -> has_type e Gamma T2 ->
  T1 = T2.
Proof.
  destruct T1; destruct T2; intros H1 H2; eauto;
    inversion H1; inversion H2; subst; eauto; try congruence;
  inversion H7; subst;
    eapply bind_deterministic; eauto.
Qed.

(* More tactic magic *)
Ltac solve_det :=
  match goal with
  | [ H1 : bind_in _ _ ?T1 ,
      H2 : bind_in _ _ ?T2 |- _ ] =>
    assert (T1 = T2) by (eapply bind_deterministic; eauto)
  | [ H1 : has_type _ _ ?T1 ,
      H2 : has_type _ _ ?T2 |- _ ] =>
    assert (T1 = T2) by (eapply bind_deterministic; eauto)
  end.

(* We also provide a (brute-force) decidability procedure for well typed
   programs *)
Instance dec_well_typed_com (Gamma : context) (c : com) : Dec (well_typed_com Gamma c) := {}.
Proof with eauto.
  unfold ssrbool.decidable.
  induction c; solve_sum.
  - destruct (dec_bind_in Gamma t TNat); destruct dec;
    destruct (dec_has_type e Gamma TNat); destruct dec;
    destruct (dec_bind_in Gamma t TBool); destruct dec;
    destruct (dec_has_type e Gamma TBool); destruct dec; solve_sum;
    try solve_det; try congruence;
    right; intro Contra; inversion Contra; subst; clear Contra;
    try solve_det; try congruence;
    destruct T; eauto.
  - destruct IHc1; destruct IHc2; subst; eauto; solve_sum.
  - destruct IHc1; destruct IHc2; subst; eauto; solve_sum.
    destruct (dec_has_type e Gamma TBool); destruct dec; solve_sum.
  - destruct IHc;
    destruct (dec_has_type e Gamma TBool); destruct dec; solve_sum.
Qed.

(** Exercise 4 : Write a generator and a shrinker for well_typed programs
    given some context [Gamma]. Write sanity checks to check your work. *)

(* FILL IN HERE *)

(** To complete the tour of TImp, here is a (buggy?) evaluation function for
    commands given a state. To ensure termination, we include an
    additional fuel parameter: if that runs out we return [OutOfGas], signifying
    that we're not sure if evaluation would have succeeded or failed later.
  *)

Inductive result :=
| Success : state -> result
| Fail : result
| OutOfGas : result.

(* State monad like fuel, or depth-like? *)
Fixpoint ceval (fuel : nat) (st : state) (c : com) : result :=
  match fuel with
  | O => OutOfGas
  | S fuel' =>
    match c with
    | SKIP =>
        Success st
    | x ::= e =>
        match eval st e with
        | Some v => Success (AtomMap.set st x v)
        | _ => Fail
        end
    | c1 ;;; c2 =>
        match ceval fuel' st c1 with
        | Success st' =>  ceval fuel' st' c2
        (* Bug : On OutOfGas should out of Gas :
        | r => r
        *)
        | _ => Fail
        end
    | IFB b THEN c1 ELSE c2 FI =>
      match eval st b with
      | Some (VBool b) =>
        ceval fuel' st (if b then c1 else c2)
      | _ => Fail
      end
    | WHILE b DO c END =>
      match eval st b with
      | Some (VBool b') =>
        if b' then ceval fuel' st (c ;;; WHILE b DO c END) else Success st
      | _ => Fail
      end
    end
  end.

Definition isFail r :=
  match r with
  | Fail => true
  | _ => false
  end.

(** Our type soundness property is that well_typed commands never fail *)
Conjecture well_typed_state_never_stuck :
  forall Gamma st, typed_state Gamma st ->
  forall c, well_typed_com Gamma c ->
  forall fuel, isFail (ceval fuel st c) = false.

(* Exercise 4: Write a checker for the above property, find any bugs
   and fix them *)

(* FILL IN HERE *)

