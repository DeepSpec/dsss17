(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Tahina Ramananandro, Reservoir Labs Inc.                   *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The Linear2 intermediate language: abstract syntax and semantics *)

(** The Linear2 language is a variant of Linear where two executions
    of the same code happen "in parallel" on two different memory
    states. It is needed in some verified separate compilation
    contexts where the source code has to run on the memory state
    without argument locations at the module boundary, when the
    initial memory state is provided by arbitrary assembly code.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.

Require Import Linear.
Require Import Morphisms.

Inductive invar_stackframe: stackframe -> stackframe -> Prop :=
| invar_stackframe_intro
    fh sph rsh ch
    fl spl rsl cl
    (f_eq: fh = fl)
    (sp_lessdef: Val.lessdef sph spl)
    (rs_lessdef: forall l, Val.lessdef (rsh l) (rsl l))
    (c_eq: ch = cl)
  :
    invar_stackframe
      (Stackframe fh sph rsh ch)
      (Stackframe fl spl rsl cl)
.

Global Instance invar_stackframe_refl:
  Reflexive invar_stackframe.
Proof.
  red. intro x.
  destruct x.
  econstructor; eauto.
Qed.

Definition invar_stack := list_forall2 invar_stackframe.

Global Instance invar_stack_refl: Reflexive invar_stack.
Proof.
  red. intro x.
  induction x; econstructor; eauto.
  reflexivity.
Qed.

Section WITHMEMORYMODELOPS.
Context  `{memory_model_ops: Mem.MemoryModelOps}.

Inductive invar: state -> state -> Prop :=
| invar_state
    stackh fh sph ch rsh mh
    stackl fl spl cl rsl ml
    (stack_inv: invar_stack stackh stackl)
    (f_eq: fh = fl)
    (sp_lessdef: Val.lessdef sph spl)
    (c_eq: ch = cl)
    (rs_lessdef: forall l, Val.lessdef (rsh l) (rsl l))
    (m_ext: Mem.extends mh ml)
  :
    invar
      (State stackh fh sph ch rsh mh)
      (State stackl fl spl ch rsl ml)
| invar_callstate
    stackh fh rsh mh
    stackl fl rsl ml
    (stack_inv: invar_stack stackh stackl)
    (f_eq: fh = fl)
    (rs_lessdef: forall l, Val.lessdef (rsh l) (rsl l))
    (m_ext: Mem.extends mh ml)
  :
    invar
      (Callstate stackh fh rsh mh)
      (Callstate stackl fl rsl ml)
| invar_returnstate
    stackh rsh mh
    stackl rsl ml
    (stack_inv: invar_stack stackh stackl)
    (rs_lessdef: forall l, Val.lessdef (rsh l) (rsl l))
    (m_ext: Mem.extends mh ml)
  :
    invar
      (Returnstate stackh rsh mh)
      (Returnstate stackl rsl ml)
.

Context `{memory_model: !Mem.MemoryModel mem}.

Global Instance invar_refl: Reflexive invar.
Proof.
  red.
  intro x. destruct x.
  {
    econstructor; eauto; try reflexivity.
    apply Mem.extends_refl.
  }
  {
    econstructor; eauto; try reflexivity.
    apply Mem.extends_refl.
  }
  {
    econstructor; eauto; try reflexivity.
    apply Mem.extends_refl.
  }
Qed.

End WITHMEMORYMODELOPS.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Record state: Type := State
  {
    state_higher: Linear.state;
    state_lower:  Linear.state;
    state_ge: Linear.genv;
    state_init_ls: locset;
    state_invariant: invar state_higher state_lower
  }.

Record step (ge: genv) (before: state) (t: trace) (after: state): Prop :=
  {
    step_ge_eq_before: ge = state_ge before;
    step_ge_eq_after: ge = state_ge after;
    step_init_ls_eq: state_init_ls after = state_init_ls before;
    step_high: Linear.step (state_init_ls before) ge (state_higher before) t (state_higher after);
    step_low: Linear.step (state_init_ls before) ge (state_lower before) t (state_lower after)
  }.

(* Whole-program case *)

Inductive initial_state (p: program) (s: state): Prop :=
| initial_state_intro
    (init_higher: Linear.initial_state p (state_higher s))
    (init_lower: Linear.initial_state p (state_lower s))
    (init_ls: state_init_ls s = Locmap.init Vundef)
.

Inductive final_state (s: state) (i: int): Prop :=
| final_state_intro
    j (fin_higher: Linear.final_state (state_higher s) j)
    (fin_lower: Linear.final_state (state_lower s) i)
.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(* Whole-program Linear trivially forward-simulates into Linear2:
   the two executions are actually the same as the Linear one.
*)

Record whole_program_invariant (ge: genv) (u: unit) (s: Linear.state) (s2: state): Prop :=
{
  wp_inv_state_higher_eq:
    state_higher s2 = s;
  wp_inv_state_lower_eq:
    state_lower s2 = s;
  wp_inv_ge_eq:
    state_ge s2 = ge;
  wp_inv_init_ls_eq:
    state_init_ls s2 = Locmap.init Vundef
}.

Theorem whole_program_linear_to_linear2 p:
  forward_simulation
    (Linear.semantics p)
    (semantics p)
.
Proof.
  apply Forward_simulation with
    (order := fun _ _ => False)
      (match_states := whole_program_invariant (Genv.globalenv p)).
  constructor.
  * constructor. contradiction.
  * intros s1 H.
    exists tt.
    eexists (State s1 s1 (Genv.globalenv p) (Locmap.init Vundef) _).
    split.
    { econstructor; eauto. }
    econstructor; eauto.
  * inversion 1; subst.
    simpl.
    intros.
    econstructor; eauto.
    congruence.
  * simpl.
    intros s1 t s1' H i s2 H0.
    inversion H0; subst.
    exists tt.
    eexists (State s1' s1' (Genv.globalenv p) (Locmap.init Vundef) _).
    split.
    {
      left.
      eapply plus_one.
      econstructor; simpl; eauto; congruence.
    }
    econstructor; eauto.
  * reflexivity.
Grab Existential Variables.
eauto.
reflexivity.
eauto.
reflexivity.
Defined.

End WITHCONFIG.