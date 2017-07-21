Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.common.AST. (* For ident. *)
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PseudoJoin.
Require Import liblayers.logic.OptionOrders.
Require Import liblayers.logic.PTrees.
Require Export liblayers.logic.Modules.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.logic.GlobalVars.

(** * Construction of modules *)

(** Modules are maps from identifiers to definitions, extended with an
  extra element [id], which represents the module that passes along
  all of the primitives in the underlying layer. *)

Definition ptree_module F V :=
  (PTree.t (res F) * PTree.t (res V))%type.

Local Existing Instance ptree_le_op.
Local Existing Instance ptree_emptyset.
Local Existing Instance ptree_oplus.
Local Existing Instance ptree_mapsto.

(** ** Querying functions *)

Definition ptree_module_conflict i: errmsg :=
  MSG "duplicate symbol in module: " :: CTX i :: nil.

Section PTREE_MODULE_QUERY.
  Context {F V : Type}.

  Definition ptree_module_function i (M: ptree_module F V) :=
    option_res_flip ((fst M) ! i).

  Definition ptree_module_variable i (M: ptree_module F V): res (option V) :=
    option_res_flip ((snd M) ! i).

  Lemma ptree_module_function_mapsto (i: ident) (f: F):
    ptree_module_function i (i ↦ OK f, @PTree.empty _) = OK (Some f).
  Proof.
    unfold ptree_module_function.
    repeat (unfold mapsto, ptree_mapsto; simpl).
    rewrite PTree.gss.
    reflexivity.
  Qed.

  Global Instance ptree_module_function_monotonic:
    Monotonic
      ptree_module_function
      (- ==>
       ptree_rel (option_le (res_le eq)) * ptree_rel (option_le (res_le eq)) ++>
       res_le (option_le eq)).
  Proof.
    intros i M1 M2 HM.
    unfold ptree_module_function.
    solve_monotonic.
  Qed.

  Lemma ptree_module_variable_mapsto (i: ident) (τ: V):
    ptree_module_variable i (@PTree.empty _, i ↦ OK τ) = OK (Some τ).
  Proof.
    unfold ptree_module_variable.
    repeat (unfold mapsto, ptree_mapsto; simpl).
    rewrite PTree.gss.
    reflexivity.
  Qed.

  Global Instance ptree_module_variable_monotonic:
    Monotonic
      ptree_module_variable
      (- ==>
       ptree_rel (option_le (res_le eq)) * ptree_rel (option_le (res_le eq)) ++>
       res_le (option_le eq)).
  Proof with eauto 10 with liblayers.
    unfold ptree_module_variable.
    solve_monotonic.
  Qed.
End PTREE_MODULE_QUERY.

(** ** Instance of [Modules] *)

(** A work around for code extraction.  The extracted OCaml code is not
  polymorphic enough if these two are not declared at top level as functions. *)

Local Instance ptree_module_le F V: Le (ptree_module F V) :=
  {
    le := ptree_rel (option_le (res_le eq)) * ptree_rel (option_le (res_le eq))
  }.

Local Instance ptree_module_empty F V: Emptyset (ptree_module F V) :=
  {
    emptyset := (@PTree.empty _, @PTree.empty _)
  }.

Local Instance ptree_module_oplus {F V} {gv_ops: GlobalVarsOps V}: Oplus (ptree_module F V) :=
  {
    oplus M1 M2 := oplus (Oplus := prod_oplus) M1 M2
  }.

Local Instance ptree_module_ops {F V} {gv_ops: GlobalVarsOps V}: ModuleOps ident F V (ptree_module F V) :=
  {
    module_mapsto_fundef := {| mapsto i κ := (i ↦ OK κ, @PTree.empty _) |};
    module_mapsto_vardef := {| mapsto i τ := (@PTree.empty _, i ↦ OK τ) |};
    get_module_function := ptree_module_function;
    get_module_variable := ptree_module_variable
  }.
Proof.
 * intros.
   unfold ptree_module_function.
   refine (_
             (ptree_forall_decision_strong
                (fun i def => P (option_res_flip (Some def)))
                (P (OK None))
                _ _ (fst L))).
   apply decide_rewrite.
   split.
   + intros J i.
     generalize (J i).
     destruct ((fst L) ! i); simpl; monad_norm; auto.
   + intros J i.
     generalize (J i).
     destruct ((fst L) ! i); simpl; monad_norm; auto.
 * intros P DP M.
   refine (_
             (ptree_forall_decision
                (fun i _ => ptree_module_function i M = OK None \/ P i) 
                _ (fst M))).
   + apply decide_rewrite.
     unfold ptree_module_function.
     unfold ptree_forall.
     split.
     - intros J i.
       destruct ((fst M) ! i) eqn:HM; try (compute; congruence).
       rewrite <- HM.
       intro.
       destruct (J _ _ HM); try contradiction.
       assumption.
     - intros.
       destruct (decide (option_res_flip (fst M) ! i = OK None)); auto.
 * intros.
   unfold ptree_module_variable.
   refine (_
             (ptree_forall_decision_strong
                (fun _ def => P (option_res_flip (Some def)))
                (P (OK None))
                _ _ (snd L))).
   apply decide_rewrite.
   split.
   + intros J i.
     generalize (J i).
     destruct ((snd L) ! i); simpl; monad_norm; auto.
   + intros J i.
     generalize (J i).
     destruct ((snd L) ! i); simpl; monad_norm; auto.
 * intros P DP M.
   refine (_
             (ptree_forall_decision
                (fun i _ => ptree_module_variable i M = OK None \/ P i) 
                _ (snd M))).
   + apply decide_rewrite.
     unfold ptree_module_variable.
     unfold ptree_forall.
     split.
     - intros J i.
       destruct ((snd M) ! i) eqn:HM; try (compute; congruence).
       rewrite <- HM.
       intro.
       destruct (J _ _ HM); try contradiction.
       assumption.
     - intros.
       destruct (decide (option_res_flip (snd M) ! i = OK None)); auto.
Defined.

(** Now to prove the assoiated properties. *)

Local Existing Instance ptree_le_op.
Local Existing Instance option_le_op.
Local Existing Instance res_le_op.
Local Hint Extern 10 (Le _) => eapply trivial_le : typeclass_instances.

Local Instance: forall F V
                       {gv_ops: GlobalVarsOps V},
                  PseudoJoin (ptree_module F V) (∅, ∅).
Proof.
  intros.
  change (@ptree_module_oplus F V gv_ops)
    with (@prod_oplus (PTree.t (res F)) _ (PTree.t (res V)) _).
  change (@ptree_module_le F V)
    with (@prod_le_op (PTree.t (res F)) _ (PTree.t (res V)) _).
  eapply @prod_pjoin.
  * apply ptree_pseudojoin.
    + reflexivity.
    + typeclasses eauto.
  * apply ptree_pseudojoin.
    + reflexivity.
    + typeclasses eauto.
Qed.

Local Instance ptree_module_prf {F V} {gv_ops: GlobalVarsOps V}: Modules ident F V (ptree_module F V) :=
  {
    get_module_function_mapsto := ptree_module_function_mapsto;
    get_module_variable_mapsto := ptree_module_variable_mapsto
  }.
Proof.
  * intros i.
    simpl; unfold ptree_module_function; simpl.
    rewrite PTree.gempty; simpl.
    reflexivity.
  * intros i j κ Hij.
    simpl; unfold ptree_module_function; simpl.
    rewrite PTree.gso by assumption; simpl.
    rewrite PTree.gempty; simpl.
    reflexivity.
  * intros i j τ.
    simpl; unfold ptree_module_function; simpl.
    rewrite PTree.gempty.
    reflexivity.

  * intros i [M1f M1v] [M2f M2v].
    simpl; unfold ptree_module_function; simpl.
    rewrite PTree.gcombine by reflexivity.
    destruct (M1f ! i) as [[σ1|]|];
    destruct (M2f ! i) as [[σ2|]|];
    simpl;
    monad_norm;
    simpl;
    unfold ret; simpl;
    solve_monotonic.

  * intros i.
    simpl; unfold ptree_module_variable; simpl.
    rewrite PTree.gempty; simpl.
    reflexivity.
  * intros i j κ Hij.
    simpl; unfold ptree_module_variable; simpl.
    rewrite PTree.gso by assumption; simpl.
    rewrite PTree.gempty; simpl.
    reflexivity.
  * intros i j τ.
    simpl; unfold ptree_module_variable; simpl.
    rewrite PTree.gempty; simpl.
    reflexivity.

  * intros i [M1f M1v] [M2f M2v].
    simpl; unfold ptree_module_variable; simpl.
    rewrite PTree.gcombine by reflexivity.
    destruct (M1v ! i) as [[τ1|]|];
    destruct (M2v ! i) as [[τ2|]|];
    simpl;
    monad_norm;
    simpl;
    solve_monotonic.
Qed.

(** * Enumeration of module functions and variables.

      TODO: generalize to a fold?
 *)

Definition get_module_functions {F V} (m: ptree_module F V):
  PTree.t (res F) :=
  fst m.

Definition get_module_variables {F V} (m: ptree_module F V):
  PTree.t (res V) :=
  snd m.

Lemma get_module_functions_spec {F V} {gv_ops: GlobalVarsOps V} (m: ptree_module F V) i:
  (get_module_functions m) ! i = res_option_flip (get_module_function i m).
Proof.
  unfold get_module_function. 
  simpl.
  unfold ptree_module_function.
  rewrite option_res_flip_inv.
  reflexivity.
Qed.

Lemma get_module_variables_spec {F V} {gv_ops: GlobalVarsOps V} (m: ptree_module F V) i:
  (get_module_variables m) ! i = res_option_flip (get_module_variable i m).
Proof.
  unfold get_module_variable.
  simpl.
  unfold ptree_module_variable.
  rewrite option_res_flip_inv.
  reflexivity.
Qed.

Global Opaque ptree_module.
Global Opaque ptree_module_ops.

Global Opaque get_module_functions get_module_variables.
