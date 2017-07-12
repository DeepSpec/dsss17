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

Require Import Atom AtomGen Maps QC.
(* /IMPORTS *)

(* The G (option...) monad *)

Definition GOpt A := G (option A).

Instance gOptMonad : `{Monad GOpt} :=
  {
    ret A x := returnGen (Some x);
    bind A B m k := bindGenOpt m k
  }.

(* Types *)

Inductive ty := TBool | TNat. 

(* TODO: Actual Generators? Derived? How much have we said at this point? *)
Derive (Arbitrary, Show) for ty.

Instance eq_dec_ty (x y : ty) : Dec (x = y).
Proof. constructor; unfold ssrbool.decidable; decide equality. Defined.

Module AtomMap := ListMap (Atom).

Definition context := @AtomMap.t ty.

(* Wrapper - helpful for automation purposes later *)
(* bound_in? *)
Inductive bind_in {A} : @AtomMap.t A -> Atom.t -> A -> Prop :=
  | Bind : forall x Gamma T, AtomMap.get Gamma x = Some T -> bind_in Gamma x T.

(* Automation stuff for proofs - don't need to show?  Or maybe put it
   in a magic Tactics.v *)
Ltac solve_left  := try solve [left; constructor; eauto].
Ltac solve_right := 
  let Contra := fresh "Contra" in
  try solve [right; intro Contra; inversion Contra; subst; clear Contra; eauto; congruence].
Ltac solve_sum := solve_left; solve_right.

Instance dec_bind_in {A : Type} Gamma x (T : A) `{D : forall (x y : A), Dec (x = y)}
  : Dec (bind_in Gamma x T).
Proof. 
constructor; unfold ssrbool.decidable.
destruct (AtomMap.get Gamma x) eqn:Get; solve_sum.
destruct (D a T) eqn:Eq; destruct dec; simpl in *; subst; solve_sum.
Defined.

Definition gen_typed_atom_from_context (Gamma : context) (T : ty)
                                     : G (option Atom.t) :=
  oneof (ret None) 
        (List.map (fun '(a,T) => ret (Some a))
                  (List.filter (fun '(a,T') => T = T'?) Gamma)).

(* Hide for lecture? -- explain later *)
Instance genST_bind_in (Gamma : context) (T : ty) 
  : GenSuchThat Atom.t (fun x => bind_in Gamma x T) :=
  { arbitraryST := gen_typed_atom_from_context Gamma T }.

(* Too many sigs *)
Definition gen_context (n : nat) : G context := 
  let domain := get_fresh_atoms n [] in
  range <- vectorOf n arbitrary ;;
  ret (List.fold_left (fun (m : context) (kv : Atom.t * ty) => 
                         let (k,v) := kv in 
                         AtomMap.set m k v) 
                      (List.combine domain range) AtomMap.empty).

(* Expressions *)

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
Derive Show for exp.

(* Reformat for 70 columns *)
Inductive has_type : context -> exp -> ty -> Prop := 
| Ty_Var : forall x T Gamma, bind_in Gamma x T -> has_type Gamma (EVar x) T
| Ty_Num : forall Gamma n, has_type Gamma (ENum n) TNat
| Ty_Plus : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                                has_type Gamma (EPlus e1 e2) TNat
| Ty_Minus : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                                has_type Gamma (EMinus e1 e2) TNat
| Ty_Mult : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                                has_type Gamma (EMult e1 e2) TNat
| Ty_True : forall Gamma, has_type Gamma ETrue TBool
| Ty_False : forall Gamma, has_type Gamma EFalse TBool
| Ty_Eq : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                              has_type Gamma (EEq e1 e2) TBool
| Ty_Le : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                              has_type Gamma (ELe e1 e2) TBool
| Ty_Not : forall Gamma e, has_type Gamma e TBool ->
                              has_type Gamma (ENot e) TBool
| Ty_And : forall Gamma e1 e2, has_type Gamma e1 TBool -> has_type Gamma e2 TBool ->
                               has_type Gamma (EAnd e1 e2) TBool.

(* Show this later *)
Derive ArbitrarySizedSuchThat for (fun e => has_type Gamma e T).

(* This is so pedantic I want to derive it :) *)
Fixpoint gen_exp_typed_sized (size : nat) (Gamma : context) (T : ty) : G (option exp) :=
  let gen_typed_evar : G (option exp) := 
      x <- gen_typed_atom_from_context Gamma T;;
      ret (EVar x) in
  let base :=
      (2, gen_typed_evar) ::
      match T with 
      | TNat  => [ (2, n <- arbitrary;; ret (Some (ENum n)))]
      | TBool => [ (1, ret ETrue)
                 ; (1, ret EFalse) ]
      end in 
  let recs size' := 
      match T with 
      | TNat => [ (1, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
                      e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
                      ret (EPlus e1 e2)) 
                ; (1, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
                      e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
                      ret (EMinus e1 e2)) 
                ; (1, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
                      e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
                      ret (EMult e1 e2)) ]
      | TBool => [ (1, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
                       e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
                       ret (EEq e1 e2)) 
                 ; (1, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
                       e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
                       ret (ELe e1 e2)) 
                 ; (1, e1 <- gen_exp_typed_sized size' Gamma TBool ;; 
                       ret (ENot e1))
                 ; (1, e1 <- gen_exp_typed_sized size' Gamma TBool ;; 
                       e2 <- gen_exp_typed_sized size' Gamma TBool ;; 
                       ret (EAnd e1 e2)) ]
      end in
  match size with 
  | O => 
    backtrack base 
  | S size' => 
    backtrack (base ++ recs size')
  end.

(* Move to after the first bug *)
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

(* Move to Tactics.v *)
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

(* Too much automation? *)
Instance dec_has_type (e : exp) (Gamma : context) (T : ty) : Dec (has_type Gamma e T) :=
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

(* Sanity checks *)
(* Generation sanity check *)
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

(* Shrinking sanity check *)
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

Inductive value := VNat : nat -> value | VBool : bool -> value.

Derive Show for value.
  
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

Definition state := @AtomMap.t value.

(* Similar structure *)
Inductive typed_state : context -> state -> Prop :=
| TS_Empty : typed_state AtomMap.empty AtomMap.empty
| TS_Elem  : forall x v T st Gamma, 
    has_type_value v T -> typed_state Gamma st ->
    typed_state ((x,T)::Gamma) ((x,v)::st).

Instance dec_typed_state Gamma st : Dec (typed_state Gamma st).
(* TODO: Fold all such stuff, like this: *)
Proof. 
constructor; unfold ssrbool.decidable.
generalize dependent Gamma.
induction st; intros; destruct Gamma; solve_sum.
destruct a as [a v]; destruct p as [a' T].
destruct (Atom.eq_dec a a'); solve_sum.
subst; specialize (IHst Gamma); destruct IHst; solve_sum.
destruct (dec_has_type_value v T); destruct dec; solve_sum.
Defined.

Definition gen_typed_state (Gamma : context) : G state := 
  sequenceGen (List.map (fun '(x, T) =>
                           v <- gen_typed_value T;;
                           ret (x, v)) Gamma).
(* Use typeclasses? *)

Instance genST_typed_state (Gamma : context) : 
  GenSuchThat state (fun st => typed_state Gamma st) :=
  { arbitraryST := liftGen Some (gen_typed_state Gamma) }.

(* Monadify *)
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
    | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2))
    | _, _ => None
    end
  end.

Definition isNone {A : Type} (m : option A) :=
  match m with 
  | None => true
  | _ => false
  end.

(* Soundness for expressions *)
Conjecture expression_soundness : 
  forall Gamma st e T,
    typed_state Gamma st ->
    has_type Gamma e T ->
    isNone (eval st e) = false.

Definition lift_shrink {A : Type} (shr : A -> list A) (m : option A) : list (option A) :=
  match m with 
  | Some x => List.map Some (shr x)
  | _ => []
  end.

Definition expression_soundness_exec := 
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

(* QuickChick expression_soundness_exec. *)
(* Try adding a bug and see if we can find it

Do it first with forAll, not forAllShrink, then observe that the bug
is hard to see.  Show shrinking, redo the property,  *)


(* Start exercise here *)

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

(* This is so pedantic I want to derive it :) *)
Fixpoint gen_com_typed_sized (size : nat) (Gamma : context) : G (option com) :=
  let assgn := 
                (List.map (fun '(x,T) =>
                             (1, e <- gen_exp_typed_sized size Gamma T;;
                                ret (CAss x e)))
                          Gamma)
  in 
  let skip :=
      ret SKIP in
  let recs size' := 
      [ (1, c1 <- gen_com_typed_sized size' Gamma;;
            c2 <- gen_com_typed_sized size' Gamma;;
            ret (CSeq c1 c2))
      ; (1, c <- gen_com_typed_sized size' Gamma;;
            b <- gen_exp_typed_sized size' Gamma TBool;;
            ret (CWhile b c))
      ; (1, b <- gen_exp_typed_sized size' Gamma TBool;;
            c1 <- gen_com_typed_sized size' Gamma;;
            c2 <- gen_com_typed_sized size' Gamma;;
            ret (CIf b c1 c2))
      ] in
  match size with 
  | O => backtrack ((1, skip) :: assgn)
  | S size' => backtrack ((1, skip) :: (assgn ++ recs size'))
  end.

Fixpoint shrink_com_typed (Gamma : context) (c : com) : list com := 
  match c with 
  | SKIP => []
  | CAss x e => 
    match AtomMap.get Gamma x with
    | Some T => SKIP :: List.map (fun e' => CAss x e) (shrink_exp_typed T e)
    | _ => []
    end
  | CSeq c1 c2 =>
    c1 :: c2 
       :: (List.map (fun c1' => CSeq c1' c2) (shrink_com_typed Gamma c1))
       ++ (List.map (fun c2' => CSeq c1 c2') (shrink_com_typed Gamma c2))
  | CIf b c1 c2 =>
    c1 :: c2 
       :: (List.map (fun c1' => CIf b c1' c2) (shrink_com_typed Gamma c1))
       ++ (List.map (fun c2' => CIf b c1 c2') (shrink_com_typed Gamma c2))
       ++ (List.map (fun b' => CIf b' c1 c2) (shrink_exp_typed TBool b))
  | CWhile b c =>
    c :: (CIf b c c) 
      :: (List.map (fun b' => CWhile b' c) (shrink_exp_typed TBool b))
      ++ (List.map (fun c' => CWhile b c') (shrink_com_typed Gamma c))
  end.
  
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
        | _ => Fail 
        *)
        | r => r
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

Conjecture well_typed_state_never_stuck : 
  forall Gamma st, typed_state Gamma st ->
  forall fuel c, isFail (ceval fuel st c) = false.

Definition well_typed_state_never_stuck_exec := 
  let num_vars := 4 in 
  let top_level_size := 5 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_typed_state Gamma) (fun st =>
  forAllShrink arbitrary shrink (fun fuel =>
  forAllShrink (gen_com_typed_sized 3 Gamma) (lift_shrink (shrink_com_typed Gamma)) (fun mc => 
  match mc with 
  | Some c => negb (isFail (ceval fuel st c))
  | _ => false
  end)))).                      

(* QuickChick well_typed_state_never_stuck_exec. *)
  
(* Unreadable bug? 
QuickChecking well_typed_state_never_stuck_exec
[(1,TBool), (2,TBool), (3,TNat), (4,TBool)]
[(1,VBool false), (2,VBool false), (3,VNat 5), (4,VBool true)]
6
Some CWhile (EAnd (EEq (EPlus (ENum 2) (ENum 3)) (ENum 5)) (ENot EFalse)) (CIf (ELe (EMinus (ENum 2) (EMinus (EVar 3) (EVar 3))) (ENum 1)) (CAss 1 (EVar 4)) (CAss 2 (EVar 1)))
*** Failed after 7 tests and 0 shrinks
*)

(* Really motivates shrinking... 
QuickChecking well_typed_state_never_stuck_exec
[(1,TBool), (2,TBool), (3,TNat), (4,TBool)]
[(1,VBool false), (2,VBool true), (3,VNat 0), (4,VBool false)]
1
Some CSeq CSkip CSkip
*)

(* LEO: Fix in SF: it should be c ;; WHILE ... (double ;) *)
(** In a traditional functional programming language like OCaml or
    Haskell we could add the [WHILE] case as follows:

  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (eval st b)
            then ceval_fun st (c; WHILE b DO c END)
            else st
    end.
*)
  
