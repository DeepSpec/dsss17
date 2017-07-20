(** A nominal representation of STLC terms.

    This version looks a lot like we expect a representation of
    the lambda calculus to look like. Unlike the LN version,
    the syntax does not distinguish between bound and free
    variables and abstractions include the name of binding
    variables.  *)

(*************************************************************)
(** * Imports                                                *)
(*************************************************************)

(** Some of our proofs are by induction on the *size* of
    terms. We'll use Coq's [omega] tactic to easily dispatch
    reasoning about natural numbers. *)
Require Export Omega.

(** We will use the [atom] type from the metatheory library to
    represent variable names. *)
Require Export Metalib.Metatheory.

(** Although we are not using LNgen, some of the tactics from
    its library are useful for automating reasoning about
    names (i.e. atoms).  *)
Require Export Metalib.LibLNgen.


(** Some fresh atoms *)
Notation X := (fresh nil).
Notation Y := (fresh (X :: nil)).
Notation Z := (fresh (X :: Y :: nil)).

Lemma YneX : Y <> X.
Proof.
  pose proof Atom.fresh_not_in (X :: nil) as H.
  apply elim_not_In_cons in H.
  auto.
Qed.


(*************************************************************)
(** * A nominal representation of terms                      *)
(*************************************************************)

Inductive n_exp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_exp)
 | n_app (t1:n_exp) (t2:n_exp).

(** For example, we can encode the expression [(\X.Y X)] as below.  *)

Definition demo_rep1 := n_abs X (n_app (n_var Y) (n_var X)).

(** For example, we can encode the expression [(\Z.Y Z)] as below.  *)

Definition demo_rep2 := n_abs Z (n_app (n_var Y) (n_var Z)).


(** As usual, the free variable function needs to remove the
    bound variable in the [n_abs] case. *)
Fixpoint fv_nom (n : n_exp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => remove x (fv_nom n)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  end.

(** The tactics for reasoning about lists and sets of atoms are useful here
    too. *)

Example fv_nom_rep1 : fv_nom demo_rep1 [=] {{ Y }}.
Proof.
  pose proof YneX.
  simpl.
  fsetdec.
Qed.

(** What makes this a *nominal* representation is that our
    operations are based on the following swapping function for
    names.  Note that this operation is symmetric: [x] becomes
    [y] and [y] becomes [x]. *)

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

(** The main insight of nominal representations is that we can
    rename variables, without capture, using a simple
    structural induction. Note how in the [n_abs] case we swap
    all variables, both bound and free.

    For example:

      (swap x y) (\z. (x y)) = \z. (y x))

      (swap x y) (\x. x) = \y.y

      (swap x y) (\y. x) = \x.y

*)
Fixpoint swap (x:atom) (y:atom) (t:n_exp) : n_exp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  end.


(** Because swapping is a simple, structurally recursive
    function, it is highly automatable using the [default_simp]
    tactic from LNgen library.

    This tactic "simplifies" goals using a combination of
    common proof steps, including case analysis of all disjoint
    sums in the goal. Because atom equality returns a sumbool,
    this makes this tactic useful for reasoning by cases about
    atoms.

    For more information about the [default_simp] tactic, see
    [metalib/LibDefaultSimp.v].

    WARNING: this tactic is not always safe. It's a power tool
    and can put your proof in an irrecoverable state. *)

Example swap1 : forall x y z, x <> z -> y <> z ->
    swap x y (n_abs z (n_app (n_var x)(n_var y))) = n_abs z (n_app (n_var y) (n_var x)).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.

Example swap2 : forall x y, x <> y ->
    swap x y (n_abs x (n_var x)) = n_abs y (n_var y).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.

Example swap3 : forall x y, x <> y ->
     swap x y (n_abs y (n_var x)) = n_abs x (n_var y).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.


(** We define the "alpha-equivalence" relation that declares
    when two nominal terms are equivalent (up to renaming of
    bound variables).

    Note the two different rules for [n_abs]: either the
    binders are the same and we can directly compare the
    bodies, or the binders differ, but we can swap one side to
    make it look like the other.  *)

Inductive aeq : n_exp -> n_exp -> Prop :=
 | aeq_var : forall x,
     aeq (n_var x) (n_var x)
 | aeq_abs_same : forall x t1 t2,
     aeq t1 t2 -> aeq (n_abs x t1) (n_abs x t2)
 | aeq_abs_diff : forall x y t1 t2,
     x <> y ->
     x `notin` fv_nom t2 ->
     aeq t1 (swap y x t2) ->
     aeq (n_abs x t1) (n_abs y t2)
 | aeq_app : forall t1 t2 t1' t2',
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_app t1 t2) (n_app t1' t2').

Hint Constructors aeq.


Example aeq1 : forall x y, x <> y -> aeq (n_abs x (n_var x)) (n_abs y (n_var y)).
Proof.
  intros.
  eapply aeq_abs_diff; auto.
  simpl; unfold swap_var; default_simp.
Qed.

Lemma aeq_refl : forall n, aeq n n.
Proof.
  induction n; auto.
Qed.

(*************************************************************)
(** ** Properties about swapping                             *)
(*************************************************************)


(** Now let's look at some simple properties of swapping. *)

Lemma swap_id : forall n x,
    swap x x n = n.
Proof.
  induction n; simpl; unfold swap_var;  default_simp.
Qed.

(** Demo: We will need the next two properties later in the tutorial,
    so we show that even though there are many cases to consider,
    [default_simp] can find these proofs. *)

Lemma fv_nom_swap : forall z y n,
  z `notin` fv_nom n ->
  y `notin` fv_nom (swap y z n).
Proof.
  (* WORKED IN CLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. 
Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  (* WORKED IN CLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. 
(*************************************************************)
(** ** Exercises                                             *)
(*************************************************************)


(** *** Recommended Exercise: [swap] properties

    Prove the following properties about swapping, either
    explicitly (by destructing [x == y]) or automatically
    (using [default_simp]).  *)

Lemma swap_symmetric : forall t x y,
    swap x y t = swap y x t.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma swap_involutive : forall t x y,
    swap x y (swap x y t) = t.
Proof.
  (* FILL IN HERE *) Admitted.

(** *** Challenge exercises: equivariance

    Equivariance is the property that all functions and
    relations are preserved under swapping.  Show that this
    holds for the various functions and relations below.

    (Hint: [default_simp] will be slow and sometimes
    ineffective on *some* of these properties. If it puts
    you in an dead-end state, you'll need to prove the
    lemm another way. *)

Lemma swap_var_equivariance : forall v x y z w,
    swap_var x y (swap_var z w v) =
    swap_var (swap_var x y z) (swap_var x y w) (swap_var x y v).
Proof.
  (* FILL IN HERE *) Admitted.

Lemma swap_equivariance : forall t x y z w,
    swap x y (swap z w t) = swap (swap_var x y z) (swap_var x y w) (swap x y t).
Proof.
  (* FILL IN HERE *) Admitted.

Lemma notin_fv_nom_equivariance : forall x0 x y t ,
  x0 `notin` fv_nom t ->
  swap_var x y x0  `notin` fv_nom (swap x y t).
Proof.
  (* FILL IN HERE *) Admitted.

(* HINT: For a helpful fact about sets of atoms, check AtomSetImpl.union_1 *)

Lemma in_fv_nom_equivariance : forall x y x0 t,
  x0 `in` fv_nom t ->
  swap_var x y x0 `in` fv_nom (swap x y t).
Proof.
  (* FILL IN HERE *) Admitted.



(*************************************************************)
(** * An abstract machine for cbn evaluation                 *)
(*************************************************************)

(** The advantage of named terms is an efficient operational
    semantics! Compared to LN or de Bruijn representation, we
    don't need always need to modify terms (such as via open or
    shifting) as we traverse binders. Instead, as long as the
    binder is "sufficiently fresh" we can use the name as is,
    and only rename (via swapping) when absolutely
    necessary. *)

(** Below, we define an operational semantics based on an
    abstract machine. As before, it will model execution as a
    sequence of small-step transitions. However, transition
    will be between _machine configurations_, not just
    expressions.

    Our abstract machine configurations have three components

    - the current expression being evaluated the heap (aka
    - environment): a mapping between variables and expressions
    - the stack: the evaluation context of the current
    - expression

    Because we have a heap, we don't need to use substitution
    to define our semantics. To implement [x ~> e] we add a
    definition that [x] maps to [e] in the heap and then look
    up the definition when we get to [x] during evaluation.  *)


Definition heap := list (atom * n_exp).

Inductive frame : Set := | n_app2 : n_exp -> frame.
Notation  stack := (list frame).

Definition configuration := (heap * n_exp * stack)%type.

(** The (small-step) semantics is a _function_ from
    configurations to configurations, until completion or
    error. *)

Inductive Step a := Error    : Step a
                  | Done     : Step a
                  | TakeStep : a -> Step a.

Definition isVal (t : n_exp) :=
  match t with
  | n_abs _ _ => true
  | _         => false
  end.

Definition machine_step (avoid : atoms) (c : configuration) : Step configuration :=
  match c with
    (h, t, s) =>
    if isVal t then
      match s with
      | nil => Done _
      | n_app2 t2 :: s' =>
        match t with
        | n_abs x t1 =>
          (* if the bound name [x] is not fresh, we need to rename it *)
          if AtomSetProperties.In_dec x avoid  then
            let (y,_) := atom_fresh avoid in
             TakeStep _ ((y,t2)::h, swap x y t1, s')
          else
            TakeStep _ ((x,t2)::h, t1, s')
        | _ => Error _ (* non-function applied to argument *)
        end
      end
    else match t with
         | n_var x => match get x h with
                     | Some t1 => TakeStep _ (h, t1, s)
                     | None    => Error _ (* Unbound variable *)
                     end
         | n_app t1 t2 => TakeStep _ (h, t1, n_app2 t2 :: s)
         | _ => Error _ (* unreachable (value in nonValueStep) *)
         end
  end.

Definition initconf (t : n_exp) : configuration := (nil,t,nil).


(** Example: evaluation of  "(\y. (\x. x) y) 3"

<<
     machine                                       corresponding term

      {}, (\y. (\x. x) y) 3, nil                   (\y. (\x. x) y) 3
  ==> {}, (\y. (\x. x) y), n_app2 3 :: nil         (\y. (\x. x) y) 3
  ==> {y -> 3}, (\x.x) y, nil                      (\x. x) 3
  ==> {y -> 3}, (\x.x), n_app2 y :: nil            (\x. x) 3
  ==> {x -> y, y -> 3}, x, nil                     3
  ==> {x -> y, y -> 3}, y, nil                     3
  ==> {x -> y, y -> 3}, 3, nil                     3
  ==> Done
>>

(Note that the machine takes extra steps compared to the
substitution semantics.)

We will prove that this machine implements the substitution
semantics in the next section.

*)

(** ** Recommended Exercise [values_are_done]

    Show that values don't step using this abstract machine.
    (This is a simple proof.)
*)

Lemma values_are_done : forall D t,
    isVal t = true -> machine_step D (initconf t) = Done _.
Proof.
(* FILL IN HERE *) Admitted.


(*************************************************************)
(** * Size based reasoning                                   *)
(*************************************************************)


(** Some properties about nominal terms require calling the
    induction hypothesis not on a direct subterm, but on one
    that has first had a swapping applied to it.

    However, swapping names does not change the size of terms,
    so that means we can prove such properties by induction on
    that size.  *)

Fixpoint size (t : n_exp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  end.

Lemma swap_size_eq : forall x y t,
    size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

Hint Rewrite swap_size_eq.

(** ** Capture-avoiding substitution *)

(** We need to use size to define capture avoiding
    substitution. Because we sometimes swap the name of the
    bound variable, this function is _not_ structurally
    recursive. So, we add an extra argument to the function
    that decreases with each recursive call. *)

Fixpoint subst_rec (n:nat) (t:n_exp) (u :n_exp) (x:atom)  : n_exp :=
  match n with
  | 0 => t
  | S m => match t with
          | n_var y =>
            if (x == y) then u else t
          | n_abs y t1 =>
            if (x == y) then t
            else
              (* rename to avoid capture *)
              let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
                 n_abs z (subst_rec m (swap y z t1) u x)
          | n_app t1 t2 =>
            n_app (subst_rec m t1 u x) (subst_rec m t2 u x)
          end
  end.

(** Our real substitution function uses the size of the size of the term
    as that extra argument. *)
Definition subst (u : n_exp) (x:atom) (t:n_exp) :=
  subst_rec (size t) t u x.

(** This next lemma uses course of values induction [lt_wf_ind] to prove that
    the size of the term [t] is enough "fuel" to completely calculate a
    substitution. Providing larger numbers produces the same result. *)
Lemma subst_size : forall n (u : n_exp) (x:atom) (t:n_exp),
    size t <= n -> subst_rec n t u x = subst_rec (size t) t u x.
Proof.
  intro n. eapply (lt_wf_ind n). clear n.
  intros n IH u x t SZ.
  destruct t; simpl in *; destruct n; try omega.
  - default_simp.
  - default_simp.
    rewrite <- (swap_size_eq x0 x1).
    rewrite <- (swap_size_eq x0 x1) in SZ.
    apply IH. omega. omega.
  - simpl.
    rewrite (IH n); try omega.
    rewrite (IH n); try omega.
    rewrite (IH (size t1 + size t2)); try omega.
    rewrite (IH (size t1 + size t2)); try omega.
    auto.
Qed.

(** ** Challenge Exercise [subst]

    Use the definitions above to prove the following results about the
    nominal substitution function.  *)

Lemma subst_eq_var : forall u x,
    subst u x (n_var x) = u.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma subst_neq_var : forall u x y,
    x <> y ->
    subst u x (n_var y) = n_var y.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma subst_app : forall u x t1 t2,
    subst u x (n_app t1 t2) = n_app (subst u x t1) (subst u x t2).
Proof. (* FILL IN HERE *) Admitted.

Lemma subst_abs : forall u x y t1,
    subst u x (n_abs y t1) =
       if (x == y) then (n_abs y t1)
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t1) `union` {{x}}) in
       n_abs z (subst u x (swap y z t1)).
Proof. (* FILL IN HERE *) Admitted.


(** ** Challenge Exercise [subst properties]

    Now show the following property by induction on the size of terms. *)

Lemma subst_same_aux : forall n, forall t y, size t <= n -> aeq (subst (n_var y) y t)  t.
Proof.
  intro n. induction n.
  intros t y SZ. destruct t; simpl in SZ; omega.
  intros t y SZ. destruct t; simpl in SZ.
(* FILL IN HERE *) Admitted.

Lemma subst_same : forall t y, aeq (subst (n_var y) y t)  t.
Proof.
  intros.
  apply subst_same_aux with (n := size t). auto.
Qed.


Lemma subst_fresh_eq_aux : forall n, forall (x : atom) t u, size t <= n ->
  x `notin` fv_nom t -> aeq (subst u x t) t.
Proof. (* FILL IN HERE *) Admitted.

Lemma subst_fresh_eq : forall (x : atom) t u,  x `notin` fv_nom t -> aeq (subst u x t) t.
Proof.
  intros. apply subst_fresh_eq_aux with (n := size t). omega. auto.
Qed.



