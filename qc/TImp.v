(** * TImp: Case Study: a Typed Imperative Language *)

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
From QC Require Import QC.
Import QcNotation.


(** Having seen a basic overview of QuickChick in the previous
    chapter, we can now dive into a more realistic case study: a typed
    variant of Imp, the simple imperative language introduced in
    _Logical Foundations_.  The original Imp variant presented in the
    first volume of Software Foundations enforces a syntactic
    separation between boolean and arithmetic expressions: [bexp] just
    ranges over boolean expressions, while [aexp] ranges over
    arithmetic ones.  Moreover, variables are only allowed in [aexp]
    and hence only take numeric values.
    
    In _Typed Imp_ (TImp) we collapse the expression syntax and allow
    variables to range over both numbers and booleans. With the
    unified syntax, we introduce the notion of _well-typed_ Imp
    expressions and programs (where every variable only ranges over
    values of a single type throughout the whole program).  We then
    give an operational semantics to TImp in the form of a (partial)
    evaluation function -- partial since, in the unified syntax, we
    can write nonsensical expressions such as [0 + True].

    A common mantra in functional programming is "well-typed programs
    cannot go wrong," and TImp is no exception. The _soundness_
    property for TImp will state that evaluating well-typed
    expressions and programs always succeeds.

    From the point of view of testing, soundness is interesting
    because it is a _conditional_ property. As we saw in the previous
    chapter, testing such properties effectively requires custom
    generators.  In this chapter, we show how to scale the techniques
    for writing generators explained in [QC] to more realistic
    generators for well-typed expressions and programs. In addition,
    we dicuss the need for custom shrinkers preserving invariants, a
    problem dual to that of custom generators. *)

(* ################################################################# *)
(** * Atoms, Types and Contexts *)

(* ================================================================= *)
(** ** Atoms *)

(** For the type of identifiers of TImp we are going to borrow (a
    cut-down version of) the [Atom] type from Penn's Metatheory
    library. [Atom] is essentially a wrapper around [nat] that
    supports decidable equality plus an operator [fresh]: given any
    finite set of atoms, one can produce one that is distinct from all
    of the atoms in the set. *)

(** The signature ([Module Type]) of atoms extends the signature
    [UsualDecidableType].  The force of this is that the standard Coq
    equality [(=)] is decidable for atoms. *)

Module Type ATOM <: UsualDecidableType.

  Parameter t : Set.
  Parameter eq_dec : forall (x y:t), {x = y} + {x <> y}.
  Parameter fresh : list t -> t.
  Parameter nat_of: t -> nat.

  Include HasUsualEq. 
  Include UsualIsEq.
End ATOM.

Module Atom : ATOM.

(** Internally, an [Atom] is just a natural number... *)

  Definition t := nat.

(** ...which means decidable equality comes for free from the standard
    library: *)

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

(** To generate identifiers for TImp, we will use a recursive function
    that generates [n] fresh [Atom]s starting from the empty list. *)

Fixpoint get_fresh_atoms n l :=
  match n with
  | 0 => l
  | S n' => get_fresh_atoms n' ((Atom.fresh l) :: l)
  end.

(** **** Exercise: 2 stars (genAtom)  *)
(** Write a [Gen] instance for [Atom.t], using the [elements]
    combinator and [get_fresh_atoms].  *)

(* FILL IN HERE *)   

(* ================================================================= *)
(** ** Types *)

(** Here is the type of TImp types: *)

Inductive ty := TBool | TNat. 

(** That is, TImp has two kinds of values: booleans and natural
    numbers. *)

(** To use [ty] in testing, we will need [Arbitrary], [Show] and an
    equality [Dec] instance. *)

(** In QC.v, we saw how one can go about writing such generators
    by hand.  However, that process can largely be automated,
    especially for simple inductive types (like [ty], [nat], [list],
    [tree], etc.).  QuickChick provides a top-level vernacular command
    to derive such instances. *)

Derive (Arbitrary, Show) for ty.
(* ==>
    genSty is defined
    shrty is defined
    showty is defined
*)

Check genSty.
(* ==> genSty : GenSized ty *)
Check shrty.
(* ==> shrty  : Shrink ty   *)
Check showty.
(* ==> showty : Show ty     *)

(** Decidable equality instances are not yet derived fully
    automatically by QuickChick.  However, the boilerplate we have to
    write is largely straightforward. As we saw in the previous
    chapters, [Dec] is a typeclass wrapper around ssreflect's
    [decidable]; we just unfold the wrapper and use the [decide
    equality] tactic. *)

Instance eq_dec_ty (x y : ty) : Dec (x = y).
Proof. 
  apply Build_Dec. unfold ssrbool.decidable. decide equality.
Defined.

(* ================================================================= *)
(** ** List Map with Decidable Equality *)

(** To encode typing environments (and, later on, states), we will
    need maps from atoms to values. However, the function-based
    representation in the _Software Foundations_ version of Imp is not
    well suited for testing: we will need to be able to access the
    domain of the map, fold over it and test for equality; these are
    all awkward to define for (Coq) functions. Therefore, we introduce
    a simple list-based map representation that takes usual decidable
    types (like [Atom]) as input.

    The operations we need are:
       - [empty] : To create the empty map.
       - [get] : To look up the binding of an element, if any.
       - [set] : To update the binding of an element.
       - [dom] : To get the list of keys in the map. *)
    
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

(** The implementation of the map is a simple association list.  If a
    list contains multiple tuples with the same key, then the binding
    of the key in the map is the one that appears first in the list;
    that is, later bindings can be shadowed. *)

Module ListMap (K:UsualDecidableType) <: Map K.

 Section withv.
   Context {V : Type}.
    
   Definition t := list (K.t * V).
    
   Definition empty : t := [].
    
   Fixpoint get m k : option V := 
     match m with
       | [] => None
       | (k', v) :: m' => if K.eq_dec k k' then Some v else get m' k
     end.
    
   Definition set (m:t) (k:K.t) (v:V) : t := (k, v) :: m.
    
   Fixpoint dom (m:t) : list K.t :=
     match m with
       | [] => []
       | (k', v) :: m' => k' :: dom m'
     end.

 End withv.

End ListMap.

(** We then instantiate the [ListMap] functor with [Atom], yielding
    [AtomMap], our desired map with [Atom] as the key type. *)

Module AtomMap := ListMap (Atom).

(** We next introduce a simple inductive relation, [bound_to m x a], that 
    holds precisely when the binding of some [Atom] [x] is equal to [a] in 
    [m] *)

Inductive bound_to {A} : @AtomMap.t A -> Atom.t -> A -> Prop :=
  | Bind : forall x m a, AtomMap.get m x = Some a -> bound_to m x a.

(** We can now decide whether [bound_to m x a] holds for a given
    arrangement of [m], [x] and [a].  On a first reading, you may
    prefer to skip the next few paragraphs (until the start of the
    [Context] subsection), which deal with partially automating the
    proofs for such instances. *)

Instance dec_bound_to {A : Type} Gamma x (T : A) 
         `{D : forall (x y : A), Dec (x = y)} 
          : Dec (bound_to Gamma x T).
Proof. 
  constructor. unfold ssrbool.decidable. 
  destruct (AtomMap.get Gamma x) eqn:Get.
      
(** After unfolding [decidable] and destructing [AtomMap.get Gamma x], we are
    left with two subgoals. In the first, we know that [AtomMap.get Gamma x =
    Some a] and effectively want to decide whether [AtomMap.get Gamma x = Some
    T] or not. Which means we need to decide whether [a = T]. Thankfully,
    we can decide that using our hypothesis [D]. *)
  
  - destruct (D a T) as [[Eq | NEq]]; subst.

(** At this point, the first goal can be immediately decided positevely
    using constructor. *)

    + left. constructor. auto.

(** In the second subgoal, we can show that [bound_to] doesn't hold. *)

    + right; intro Contra; inversion Contra; subst; clear Contra.
      congruence.

(** Both of these tactic patterns are very common in non-trival [Dec] 
    instances. It is worth we automating them a bit using LTac. *)

Abort.

(** A lot of the time, we can immediately decide a property positivly 
    using constructor applications. That is captured in [solve_left]. *)

Ltac solve_left  := try solve [left; econstructor; eauto].

(** Much of the time, we can also immediately decide that a property
    _doesn't_ hold by assuming it, doing inversion, and using
    [congruence]. *)

Ltac solve_right := 
  let Contra := fresh "Contra" in
  try solve [right; intro Contra; inversion Contra; subst; clear Contra; 
             eauto; congruence].

(** We group both in a single tactic, which does nothing at all if 
    it fails to solve a goal, thanks to [try solve]. *)

Ltac solve_sum := solve_left; solve_right.

(** We can now prove the [Dec] instance quite concisely. *)

Instance dec_bound_to {A : Type} Gamma x (T : A) 
         `{D : forall (x y : A), Dec (x = y)}
  : Dec (bound_to Gamma x T).
Proof. 
  constructor. unfold ssrbool.decidable. 
  destruct (AtomMap.get Gamma x) eqn:Get; solve_sum.
  destruct (D a T) as [[Eq | NEq]]; subst; solve_sum.
Defined.

(* ================================================================= *)
(** ** Contexts *)

(** Typing contexts in TImp are just maps from atoms to types. *)

Definition context := @AtomMap.t ty.

(** Given a context [Gamma] and a type [T], we can try to generate a
    random [Atom] whose binding in [Gamma] is [T].

    We use [List.filter] to extract all of the elements in [Gamma]
    whose type is equal to [T] and then, for each [(a,T')] that
    remains, return the name [a]. We use the [oneof] combinator to
    pick an generator from this list at random.
    
    Since the filtered list might be empty we return an [option]. *)
    
Definition gen_typed_atom_from_context (Gamma : context) (T : ty)
                                     : G (option Atom.t) :=
  oneof (ret None) 
        (List.map (fun '(a,T') => ret (Some a))
                  (List.filter (fun '(a,T') => T = T'?) Gamma)).

(** We also need to generate typing contexts.

    Given some natural number [n] to serve as the size of the context,
    we first create its domain, [n] fresh atoms. *)
    
Definition gen_context (n : nat) : G context := 
  let domain := get_fresh_atoms n [] in
  range <- vectorOf n arbitrary ;;
  ret (List.fold_left (fun m '(k, v) => AtomMap.set m k v) 
                      (List.combine domain range) AtomMap.empty).

(** We then create [n] arbitrary types with [vectorOf], using the
    [Gen] instance for [ty] we derived earlier.
  
    Finally, we zip ([List.combine]) the domain with the ranges and
    fold over the result to insert each binding into a map. *)

(* ################################################################# *)
(** * Expressions *)

(** We are now ready to introduce the syntax of expressions in TImp.
    The original Imp had two distinct types of expressionsm,
    arithmetic and boolean expressions, and variables were only
    allowed to range over natural numbers. In TImp, we extend
    variables to range over boolean values as well, and we collaps
    expressions into a single type [exp]. *)

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

(** To print expressions we derive [Show] *)

Derive Show for exp.

(* ================================================================= *)
(** ** Typed Expressions *)

(** The following inductive relation characterizes well-typed
    expressions of a particular type. It is straightforward, using
    [bound_to] to access the typing context in the variable case *)

Reserved Notation "Gamma '||-' e '\IN' T" (at level 40).

Inductive has_type : context -> exp -> ty -> Prop := 
| Ty_Var : forall x T Gamma, 
    bound_to Gamma x T -> Gamma ||- EVar x \IN T
| Ty_Num : forall Gamma n, 
    Gamma ||- ENum n \IN TNat
| Ty_Plus : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- EPlus e1 e2 \IN TNat                                    
| Ty_Minus : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- EMinus e1 e2 \IN TNat                                    
| Ty_Mult : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- EMult e1 e2 \IN TNat                                    
| Ty_True : forall Gamma, Gamma ||- ETrue \IN TBool
| Ty_False : forall Gamma, Gamma ||- EFalse \IN TBool
| Ty_Eq : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- EEq e1 e2 \IN TBool
| Ty_Le : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- ELe e1 e2 \IN TBool
| Ty_Not : forall Gamma e, 
    Gamma ||- e \IN TBool ->  Gamma ||- ENot e \IN TBool
| Ty_And : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TBool -> Gamma ||- e2 \IN TBool ->
    Gamma ||- EAnd e1 e2 \IN TBool

where "Gamma '||-' e '\IN' T" := (has_type Gamma e T).

(** Once again, we need a decidable instance for the typing relation of
    TImp. You can skip to the next exercise if you are not interested in
    specific proof details. *)

(** We will need a bit more automation for this proof. We will
    have a lot of hypotheses of the form: 

   IH : forall (T : ty) (Gamma : context),
          ssrbool.decidable (Gamma ||- e1 \IN T)

 
    Using a brute-force approach, we instantiate such [IH]
    with both [TNat] and [TBool], destruct them and then 
    call [solve_sum]. 
     
    The [pose proof] tactic introduces a new hypothesis 
    in our context, while [clear IH] removes it so that 
    we don't try the same instantiations again and 
    again.
*)

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
    and a type [T], we can decide whether [has_type Gamma e T] holds. *)

Instance dec_has_type (e : exp) (Gamma : context) (T : ty) 
  : Dec (Gamma ||- e \IN T).
Proof with solve_sum.
  constructor.
  generalize dependent Gamma.
  generalize dependent T.
  induction e; intros T Gamma; unfold ssrbool.decidable;
    try solve [destruct T; solve_sum];
    try solve [destruct T; solve_inductives Gamma].
  (* bound_to case: *)
  destruct (dec_bound_to Gamma t T); destruct dec; solve_sum.
Defined.

Instance shrink_atom : Shrink Atom.t := 
  { shrink := fun _ => [] }.

(** **** Exercise: 3 stars (arbitraryExp)  *)
(** Derive [Arbitrary] for expressions.  To see how good it is at
    generating _well-typed_ expressions, write a conditional property [cond_prop] that is (trivially) always true, with the precondition that some
    expression is well-typed. Try to check that property like this:

    QuickChickWith (updMaxSize stdArgs 3) cond_prop.

    This idiom sets the maximum-size parameter for all generators to
    [3], rather the default, which is something larger like 10.  When
    generating examples, QuickChick will start with size 0, gradually
    increase the size until the maximum size is reached, and then
    start over.)  What happens when you vary the size bound? *)

(* FILL IN HERE *)

(* ================================================================= *)
(** ** Generating Typed Expressions *)

(** Instead of generating expressions and filtering them using
    [has_type], we can be smarter and generate _well-typed_
    expressions for a given context directly.

    It is common for conditional generators to return [option]s of the
    underlying type, allowing the possibility of failure if a wrong
    choice is made internally. For example, if we wanted to generate
    an expression of type [TNat] and chose to try to do so by
    generating a variable, then we might not be able to finish (if the
    context only binds booleans). *)

(** To chain together two generators with types of the form 
    [G (option ...)], we need to execute the first generator, match 
    on its result, and, when it is a [Some], apply the second generator. *)

Definition bindGenOpt {A B : Type} 
             (gma : G (option A)) (k : A -> G (option B))
           : G (option B) :=
  ma <- gma ;;
  match ma with 
  | Some a => k a 
  | None => ret None
  end.

(** This pattern is common enough that it's worth using explicit monadic 
    notations. *)

Definition GOpt A := G (option A).

Instance gOptMonad : `{Monad GOpt} :=
  {
    ret A x := returnGen (Some x);
    bind A B m k := bindGenOpt m k
  }.

(** This brings us to our first interesting generator -- one for typed
    expressions.  We asumme that [Gamma] and [T] are inputs to the
    generation process.  We also use a [size] parameter to control the
    depth of generated expressions (i.e., we'll define a sized
    generator). *)

(** Let's start with a much smaller relation: [has_type_1] (which
    consists of just the first constructor of [has_type]), to
    demonstrate how to build up complex generators for typed
    expressions from smaller parts. *)

Inductive has_type_1 : context -> exp -> ty -> Prop := 
  | Ty_Var1 : forall x T Gamma, 
      bound_to Gamma x T -> has_type_1 Gamma (EVar x) T.

(** To generate [e] such that for [has_type_1 Gamma e T] holds, we
    need to pick one of its constructors (there is only one choice,
    here) and then try to satisfy its preconditions by generating more
    things.  To satisfy [Ty_Var1] (given [Gamma] and [T]), we need to
    generate [x] such that [bound_to Gamma x T]. But we already have
    such a generator!  We just need to wrap it in an [EVar].  *)

Definition gen_typed_evar (Gamma : context) (T : ty) : GOpt exp :=
  x <- gen_typed_atom_from_context Gamma T;;
  ret (EVar x).

(** (Note that this is the [ret] of the [GOpt] monad.) *)

(** Now let's consider a typing relation [has_type_2], extending
    [has_type_1] with all of the constructors of [has_type] that do
    not recursively require [has_type] as a side-condition. These will
    be the _base cases_ for our final generator. *)
  
Inductive has_type_2 : context -> exp -> ty -> Prop :=
| Ty_Var2 : forall x T Gamma, 
    bound_to Gamma x T -> has_type_2 Gamma (EVar x) T
| Ty_Num2 : forall Gamma n, 
    has_type_2 Gamma  (ENum n) TNat
| Ty_True2 : forall Gamma, has_type_2 Gamma ETrue TBool
| Ty_False2 : forall Gamma, has_type_2 Gamma EFalse TBool.

(** We can already generate values satisfying [Ty_Var2] using
    [gen_typed_evar].  For the rest of the rules, we will need to
    pattern match on the input [T], since [Ty_Num] can only be used if
    [T = TNat], while [Ty_True] and [Ty_False] can only be used if [T
    = TBool].  *)

Definition base' Gamma T : list (GOpt exp) := 
      gen_typed_evar Gamma T ::
      match T with 
      | TNat  => [ n <- arbitrary;; ret (Some (ENum n))]
      | TBool => [ ret ETrue ; ret EFalse ]
      end.

(** We now need to go from a list of (optional) generators to a 
    single generator. We could do that using the [oneOf] combinator (which
    chooses uniformly), or the [frequency] combinator (by adding weights).

    Instead, we will introduce a new one, called [backtrack]:

       backtrack : list (nat * GOpt ?A) -> GOpt ?A
*)

(** Just like [frequency], [backtrack] selects one of the generators
    according to the input weights. Unlike frequency, if the chosen
    generator fails (i.e. produces [None]), [backtrack] will
    immediately choose another and keep going until one succeeds or
    all options are exhausted. Our base case generator could then be
    like this: *)
    
Definition base Gamma T := 
      (2, gen_typed_evar Gamma T) ::
      match T with 
      | TNat  => [ (2, n <- arbitrary;; ret (Some (ENum n)))]
      | TBool => [ (1, ret ETrue)
                 ; (1, ret EFalse) ]
      end.

Definition gen_has_type_2 Gamma T := backtrack (base Gamma T).

(** To see how we handle recursive rules, let's consider a third
    sub-relation [has_type_3]: *)

Inductive has_type_3 : context -> exp -> ty -> Prop :=
 | Ty_Var3 : forall x T Gamma, 
     bound_to Gamma x T -> has_type_3 Gamma (EVar x) T
 | Ty_Plus3 : forall Gamma e1 e2, 
    has_type_3 Gamma e1 TNat -> has_type_3 Gamma e2 TNat ->
    has_type_3 Gamma (EPlus e1 e2) TNat.

(** Typing derivations involving [EPlus] nodes are binary trees, so we
    need to add a [size] parameter to enforce termination. The base
    case ([Ty_Var3]) is handled using [gen_typed_evar] just like
    before.  The non-base case can choose between trying to generate
    [Ty_Var3] and trying to generate [Ty_Plus3]. For the latter, the
    input type [T] must be [TNat], otherwise it is not
    applicable. Once again, this leads to a match on [T]: *)

Fixpoint gen_has_type_3 size Gamma T : GOpt exp := 
  match size with 
  | O => gen_typed_evar Gamma T
  | S size' => 
    backtrack ([ (1, gen_typed_evar Gamma T) ] 
               ++ match T with 
                  | TNat => 
                    [ (size, e1 <- gen_has_type_3 size' Gamma TNat;;
                             e2 <- gen_has_type_3 size' Gamma TNat;;
                             ret (EPlus e1 e2)) ]
                  | _ => []
                  end)
  end.

(** Putting all this together, we get the full generator for
    well-typed expressions. *)

Fixpoint gen_exp_typed_sized
            (size : nat) (Gamma : context) (T : ty) 
       : GOpt exp :=
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

(** When writing such complex generators, it's good to have some tests
    to verify that we are generating what we expect. For example, here
    we would expect [gen_exp_typed_sized] to always return expressions
    that are well typed.
    
    We can use [forAll] to encode such a property. *)

Definition gen_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in 
  forAll (gen_context num_vars) (fun Gamma =>
  forAll arbitrary (fun T =>                                   
  forAll (gen_exp_typed_sized top_level_size Gamma T) (fun me =>
  match me with 
  | Some e => (has_type Gamma e T)?
  | None => false 
  end))).

(* QuickChick gen_typed_has_type. *)

(* ################################################################# *)
(** * Values and States *)

(* ================================================================= *)
(** ** Values *)

(** In original Imp, variables range over natural numbers, so states were just
    maps from identifiers to [nat]. Since we wanted to extend this to also 
    include booleans, we need a type of [value]s that includes both. *)

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

(** _States_ in TImp are just maps from atoms to values *)

Definition state := @AtomMap.t value.

(** We introduce an inductive relation that specifies when a state is
    welltyped in a context (that is, when all of its variables are
    mapped to values of appropriate types).
  
    We encode this in an element-by-element style inductive relation:
    empty states are only well typed in respect to an empty context,
    while non-empty states need to map their head atom to a value of
    the appropriate type and their tails must also be well typed. *)

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

(** To write a generator for well-typed states given a context [Gamma], 
    we use the combinator [sequenceGen : list (G A) -> G (list A)], which
    receives a list of generators and produces a generator of lists. 
  
    We just need to iterate ([map]) through the context, producing
    an arbitrary value of the appropriate type for each pair [(x,T)]. The 
    [sequenceGen] combinator will then chain all those generators in 
    sequence, producing a generator for well-typed states *)
    
Definition gen_typed_state (Gamma : context) : G state := 
  sequenceGen (List.map (fun '(x, T) =>
                           v <- gen_typed_value T;;
                           ret (x, v)) Gamma).

(* ################################################################# *)
(** * Evaluation *)

(** The evaluation function takes a state and an expression and
    returns an optional value, which can be [None] if the expression
    encounters a dynamic type error. *)

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
(* Let's include a silly bug here! *)
    | Some (VBool b), Some (VNat n2) => Some (VBool (negb b))
(*  | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2)) *)
    | _, _ => None
    end
  end.

(** _Type soundness_ states that, if we have an expression [e] of a
    given type [T] as well as a well-typed state [st], then evaluating
    [e] in [st] will never fail.*)

Definition isNone {A : Type} (m : option A) :=
  match m with 
  | None => true
  | Some _ => false
  end.

Conjecture expression_soundness : forall Gamma st e T,  
    typed_state Gamma st ->  Gamma ||- e \IN T ->
    isNone (eval st e) = false.

(** To test this property, we construct an appropriate checker: *)

Definition expression_soundness_exec := 
  let num_vars := 4 in 
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>                                    
  forAll (gen_exp_typed_sized 3 Gamma T) (fun me => 
  match me with  
  | Some e => negb (isNone (eval st e))
  | _ => true
  end)))).   

(* QuickChick expression_soundness_exec. *)
(** 

===>
       QuickChecking expression_soundness_exec
       [(1,TNat), (2,TNat), (3,TBool), (4,TNat)]
       [(1,VNat 0), (2,VNat 0), (3,VBool true), (4,VNat 0)]
       TBool
       Some EAnd (EAnd (EEq (EVar 4) (EVar 1)) (EEq (ENum 0) (EVar 4))) EFalse
       *** Failed after 8 tests and 0 shrinks. (0 discards)
*)
(** But where is the bug? Why we need shrinking! *)

(* ================================================================= *)
(** ** Shrinking for Expressions *)

(** Let's see what happens if we use the default shrinker for
    expressions carelessly. *)

Derive Shrink for exp.

Definition expression_soundness_exec_firstshrink := 
  let num_vars := 4 in 
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>                                    
  forAllShrink (gen_exp_typed_sized 3 Gamma T) shrink (fun me => 
  match me with  
  | Some e => negb (isNone (eval st e))
  | _ => true
  end)))).   

(* QuickChick expression_soundness_exec_firstshrink. *)
(** 
<< 
===> 
  QuickChecking expression_soundness_exec_firsttry
  [(1,TBool), (2,TNat), (3,TBool), (4,TBool)]
  [(1,VBool false), (2,VNat 0), (3,VBool true), (4,VBool false)]
  TBool
  Some EAnd (ENum 0) ETrue
  *** Failed after 28 tests and 7 shrinks. (0 discards)
*)

(** The expression shrank to something ill-typed! Since it causes the
    checker to fail, QuickChick views this as a succesfull shrink, even 
    though this could not actually be produced by our generator and 
    doesn't satisfy our preconditions!  One solution would be to check 
    the preconditions in the Checker, filtering out shrinks.  But that 
    would be inefficient. *)

(** We not only need to shrink expressions, we need to shrink them so
    that their type is preserved! To accomplish this, we need to
    intuitively follow the opposite of the procedure we did for
    generators: look at a typing derivation and see what parts of it
    we can shrink to while maintaining their types so that the type of
    the entire thing is preserved.
  
    As in the case of [gen_exp_typed], we are going to build up the
    full shrinker in steps. Let's begin with shrinking constants.

    - If [e = ENum x] for some [x], all we can do is try to shrink
      [x].
    - If [e = ETrue] or [e = EFalse], we could shrink it to the other.
      But remember, we don't want to do both, as this would lead to an
      infinite loop in shrinking!  We choose to shrink [EFalse] to
      [ETrue]. *)

Definition shrink_base (e : exp) : list exp :=
  match e with 
  | ENum n => map ENum (shrink n)
  | ETrue => []
  | EFalse => [ETrue] 
  | _ => []
  end.

(** The next case, [EVar], must take the type [T] to be preserved into
    account. To shrink an [EVar] we could try shrinking the inner
    atom, but the shrinking instance we have for atoms is a no-op, so
    that does nothing.  Or, better, we can try to shrink the [EVar] to
    a constant of the appropriate type. *)

Definition shrink_evar (T : ty) (e : exp) : list exp :=
  match e with 
  | EVar x => 
    match T with 
    | TNat => [ENum 0]
    | TBool => [ETrue ; EFalse]
    end
  | _ => []
  end.

(** Finally, we need to be able to shrink the recursive cases. Consider 
    [EPlus e1 e2]: 
      - We could try (recursively) shrinking [e1] or [e2] preserving their 
        [TNat] type.
      - We could try to shrink directly to [e1] or [e2] since their type 
        is the same as [EPlus e1 e2]. *)

(** On the other hand, consider [EEq e1 e2]:
      - Again, we could recursively shrink [e1] or [e2].
      - But we can't shrink _to_ [e1] or [e2] since they are of a
        different type.
      - For faster shrinking, we also try to shrink such expressions
        to boolean constants directly. *)

Fixpoint shrink_rec (T : ty) (e : exp) : list exp := 
  match e with 
  | EPlus e1 e2 => 
    e1 :: e2 
       :: (List.map (fun e1' => EPlus e1' e2) (shrink_rec T e1))
       ++ (List.map (fun e2' => EPlus e1 e2') (shrink_rec T e2))
  | EEq e1 e2 => 
    ETrue :: EFalse 
       :: (List.map (fun e1' => EEq e1' e2) (shrink_rec TNat e1))
       ++ (List.map (fun e2' => EEq e1 e2') (shrink_rec TNat e2))
  | _ => []
  end.

(** Putting it all together yields the following smart shrinker: *)
   
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

(** As we saw for generators, we can also perform sanity checks on our
    shrinkers.  Here, when the shrinker is applied to an expression of
    a given type, all of its results should have the same type. *)
    
Definition shrink_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in 
  forAll (gen_context num_vars) (fun Gamma =>
  forAll arbitrary (fun T =>                                   
  forAll (gen_exp_typed_sized top_level_size Gamma T) (fun me =>
  match me with 
  | Some e => 
    List.forallb (fun e' => (has_type Gamma e' T)?) (shrink_exp_typed T e)
  | _ => false 
  end))).

(* QuickChick shrink_typed_has_type. *)

(* ================================================================= *)
(** ** Back to Soundness *)
(** To lift the shrinker to optional expressions, QuickChick provides
    the following function. *)

Definition lift_shrink {A}
              (shr : A -> list A) (m : option A) 
           : list (option A) :=
  match m with 
  | Some x => List.map Some (shr x)
  | _ => []
  end.

(** Armed with shrinking, we can pinpoint the bug in the [EAnd] branch
    of the evaluator. *)

Definition expression_soundness_exec' := 
  let num_vars := 4 in 
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>                                    
  forAllShrink (gen_exp_typed_sized 3 Gamma T) 
               (lift_shrink (shrink_exp_typed T)) 
               (fun me =>  
  match me with  
  | Some e => negb (isNone (eval st e))
  | _ => true
  end)))).   

(* QuickChick expression_soundness_exec'. *)
(** 

===>
        QuickChecking expression_soundness_exec'
        [(1,TNat), (2,TNat), (3,TNat), (4,TBool)]
        [(1,VNat 0), (2,VNat 0), (3,VNat 0), (4,VBool false)]
        TBool
        Some EAnd ETrue ETrue
        *** Failed after 8 tests and 1 shrinks. (0 discards)
*)

(* ################################################################# *)
(** * Well-Typed Programs *)

(** Now we're ready to introduce TImp commands; they are just like the
    ones in Imp. *)

Inductive com : Type :=
  | CSkip  : com
  | CAss   : Atom.t -> exp -> com
  | CSeq   : com    -> com -> com
  | CIf    : exp    -> com -> com -> com
  | CWhile : exp    -> com -> com.

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

Derive Show for com.

(** (Of course, the derived [Show] instance is not going to use these
    notations!) *)

(* ================================================================= *)
(** ** Well-typed commands *)

Inductive well_typed_com : context -> com -> Prop :=
  | TSkip : forall Gamma, well_typed_com Gamma CSkip
  | TAss  : forall Gamma x e T, 
      bound_to Gamma x T -> 
      Gamma ||- e \IN T ->
      well_typed_com Gamma (CAss x e)
  | TSeq  : forall Gamma c1 c2, 
      well_typed_com Gamma c1 -> well_typed_com Gamma c2 ->
      well_typed_com Gamma (CSeq c1 c2)
  | TIf : forall Gamma b c1 c2, 
      Gamma ||- b \IN TBool ->
      well_typed_com Gamma c1 -> well_typed_com Gamma c2 ->
      well_typed_com Gamma (CIf b c1 c2)
  | TWhile : forall Gamma b c,
      Gamma ||- b \IN TBool -> well_typed_com Gamma c -> 
      well_typed_com Gamma (CWhile b c).

(** Decidable instance for well-typed. *)

(** A couple of lemmas and a custom tactic will help the decidability
    proof... *)

Lemma bind_deterministic Gamma x (T1 T2 : ty) :
  bound_to Gamma x T1 -> bound_to Gamma x T2 -> 
  T1 = T2.
Proof.
  destruct T1; destruct T2; intros H1 H2; eauto; 
    inversion H1; inversion H2; congruence.
Qed.

Lemma has_type_deterministic Gamma e (T1 T2 : ty) : 
  has_type e Gamma T1 -> has_type e Gamma T2 -> 
  T1 = T2.
Proof.
  destruct T1; destruct T2; intros H1 H2; eauto;
    inversion H1; inversion H2; subst; eauto; try congruence;
  inversion H7; subst;
    eapply bind_deterministic; eauto.
Qed.

Ltac solve_det := 
  match goal with 
  | [ H1 : bound_to _ _ ?T1 ,
      H2 : bound_to _ _ ?T2 |- _ ] =>
    assert (T1 = T2) by (eapply bind_deterministic; eauto)
  | [ H1 : has_type _ _ ?T1 ,
      H2 : has_type _ _ ?T2 |- _ ] =>
    assert (T1 = T2) by (eapply bind_deterministic; eauto)
  end.

(** Now, here is a brute-force decision procedure for the typing
    relation (which amounts to a simple typechecker). *) 

Instance dec_well_typed_com (Gamma : context) (c : com) 
  : Dec (well_typed_com Gamma c).
Proof with eauto.
  constructor. unfold ssrbool.decidable.
  induction c; solve_sum.
  - destruct (dec_bound_to Gamma t TNat); destruct dec;
    destruct (dec_has_type e Gamma TNat); destruct dec; 
    destruct (dec_bound_to Gamma t TBool); destruct dec;
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

(** **** Exercise: 4 stars (arbitrary_well_typed_com)  *)
(** Write a generator and a shrinker for well_typed programs given
    some context [Gamma].  Write some appropriate sanity checks and
    make sure they give expected results. *)

(* FILL IN HERE *)

(** To complete the tour of testing for TImp, here is a (buggy??)
    evaluation function for commands given a state. To ensure
    termination, we've included a "fuel" parameter: if it gets to zero
    we return [OutOfGas], signifying that we're not sure if evaluation
    would have succeeded, failed, or diverged if we'd gone on
    evaluating. *)
  
Inductive result := 
| Success : state -> result
| Fail : result 
| OutOfGas : result. 

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

(** _Type soundness_: well-typed commands never fail. *)

Conjecture well_typed_state_never_stuck : 
  forall Gamma st, typed_state Gamma st ->
  forall c, well_typed_com Gamma c ->
  forall fuel, isFail (ceval fuel st c) = false.

(** **** Exercise: 4 stars (well_typed_state_never_stuck)  *)
(** Write a checker for the above property, find any bugs, and fix them. *)

(* FILL IN HERE *)                  

(* ################################################################# *)
(** * Automation (Revisited) *)

(** QuickChick is under very active development.  Our vision is that
    it should automate most of the tedious parts of testing, while
    retaining full customizability.

    We close this case study with a brief demo of some things it can
    do now. *)

(** Recall the [has_type_value] property and its corresponding generator:

  Inductive has_type_value : value -> ty -> Prop :=
    | TyVNat  : forall n, has_type_value (VNat  n) TNat
    | TyVBool : forall b, has_type_value (VBool b) TBool.

  Definition gen_typed_value (T : ty) : G value :=
    match T with 
    | TNat  => n <- arbitrary;; ret (VNat n)
    | TBool => b <- arbitrary;; ret (VBool b)
    end.

    QuickChick includes a derivation mechanism that can _automatically_
    produces such generators -- i.e., generators for data structures 
    satisfying inductively defined properties! *)

Derive ArbitrarySizedSuchThat for (fun v => has_type_value v T).
(** ==> GenSizedSuchThathas_type_value is defined. *)

(** Let's take a closer look at what is being generated (after 
    doing some renaming and reformatting). *)

Print GenSizedSuchThathas_type_value.
(** 
===>
  GenSizedSuchThathas_type_value = fun T : ty =>
  {| arbitrarySizeST := 
     let fix aux_arb (size0 : nat) (T : ty) {struct size0} 
           : G (option value) :=
       match size0 with
       | 0 => backtrack [(1, match T with
                             | TBool => ret None
                             | TNat => n <- arbitrary;;
                                       ret (Some (VNat n))
                             end)
                        ;(1, match T with
                             | TBool => b <- arbitrary;;
                                        ret (Some (VBool b)))
                             | TNat => ret None
                             end)]
       | S _ => backtrack [(1, match T with
                               | TBool => ret None
                               | TNat => n <- arbitrary;;
                                         ret (Some (VNat n))
                               end)
                          ;(1, match T with
                               | TBool => b <- arbitrary;;
                                          ret (Some (VBool b)))
                               | TNat => ret None
                               end)]
       end in
       fun size0 : nat => aux_arb size0 T |}

  : forall T : ty,
      GenSizedSuchThat value 
          (fun v => has_type_value v T)
*)

(* ================================================================= *)
(** ** (More) Typeclasses for Generation *)

(** QuickChick provides typeclasses for automatic the generation 
    for data satisfying predicates. *)

Module GenSTPlayground.

(** A variant that takes a size. *)

Class GenSizedSuchThat (A : Type) (P : A -> Prop) := 
  { arbitrarySizeST : nat -> G (option A) }.

(** An unsized variant. *)

Class GenSuchThat (A : Type) (P : A -> Prop) := 
  { arbitraryST : G (option A) }.

(** Convenient notation: *)

Notation "'genST' x" := (@arbitraryST _ x _) (at level 70).

(** And a coercion between the two. *)

Instance GenSuchThatOfBounded (A : Type) (P : A -> Prop) 
         (H : GenSizedSuchThat A P)
  : GenSuchThat A P := 
  { arbitraryST := sized arbitrarySizeST }.

End GenSTPlayground.

(* ================================================================= *)
(** ** Using "SuchThat" Typeclasses *)

(** QuickChick can now (ab)use the typeclass resolution mechanism to 
    perform black magic: *)

Conjecture conditional_prop_example : 
  forall (x y : nat), x = y -> x = y.

(* QuickChick conditional_prop_example. *)
(** 
  ==>
    QuickChecking conditional_prop_example
    +++ Passed 10000 tests (0 discards)
*)

(** Notice the "0 discards": that means that quickchick is using
    generators that produce [x] and [y] such that [x = y]! *)
