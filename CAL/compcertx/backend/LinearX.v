Require compcert.backend.Linear.
Require EventsX.
Require SmallstepX.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Locations.
Import Conventions.
Export Linear.

Require Import LocationsX.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

(** Execution of Linear functions with Asm-style arguments (long long 64-bit integers NOT allowed) *)

Inductive initial_state
          (lm: locset) (p: Linear.program) (i: ident)
          (sg: signature) (args: list val) (m: mem): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (Hsig: sg = funsig f)
    (Hargs: args = map (fun r => Locmap.getpair r lm) (loc_arguments sg))
  :
    initial_state lm p i sg args m (Callstate nil f lm m).

Inductive final_state (lm: locset) (sg: signature): state -> (val * mem) -> Prop :=
| final_state_intro
    rs
    v
    (Hv: v = getpair (loc_result sg) rs)
    (** Callee-save registers *)
    (CALLEE_SAVE: forall r,
       ~ In r destroyed_at_call ->
       rs (R r) = lm (R r))
    m :
    final_state lm sg (Returnstate nil rs m) (v, m)
.

Definition semantics
           (lm: locset) (p: Linear.program) (i: ident)
           (sg: signature) (args: list val) (m: mem) : Smallstep.semantics _ :=
  Semantics (Linear.step lm) (initial_state lm p i sg args m) (final_state lm sg) (Genv.globalenv p).

(* Single events *)

Lemma semantics_single_events lm p i sg args m:
  single_events (semantics lm p i sg args m).
Proof.
  red.
  intros s t s' H.
  inversion H; subst; simpl; auto;
  eapply external_call_trace_length; eauto.
Qed.

(* Receptiveness *)

Lemma semantics_receptive lm p i sg args m:
  receptive (semantics lm p i sg args m).
Proof.
  split; auto using semantics_single_events.
  inversion 1; subst; try now (inversion 1; subst; eauto).
  * (* builtin *)
    intros.
    eapply external_call_receptive in H1; eauto.
    destruct H1 as (vres2 & m2 & EXEC).
    intros; esplit.
    econstructor; eauto.
  * (* annot *)
    intros H2.
    eapply external_call_receptive in H1; eauto.
    destruct H1 as (vres2 & m2 & EXEC).
    esplit.
    econstructor; eauto.
Qed.

(* Weak determinacy *)

Lemma semantics_weak_determ lm p i sg args m:
  weak_determ (semantics lm p i sg args m).
Proof.
  split; auto using semantics_single_events.
  - (* step determ *)
    inversion 1; subst; inversion 1; subst; try now intuition (auto using match_traces_E0 || congruence).
    + (* builtin *)
      exploit eval_builtin_args_determ. eexact H0. eexact H14. intros; subst.
      exploit external_call_determ. eexact H1. eexact H15.
      destruct 1 as (MATCH & EQ).
      split; auto.
      intros ->. intuition subst.
      congruence.
    + (* annot *)
      exploit external_call_determ. eexact H1. eexact H9.
      destruct 1 as (MATCH & EQ).
      split; auto. intros ->. intuition subst; congruence.
  - (* init determ *)
    inversion 1; inversion 1; congruence.
  - (* final no step *)
    unfold nostep.
    inversion 1; subst.
    inversion 1.
Qed.

End WITHCONFIG.
