
(** We do NOT import compcert.driver.Compiler, because we do NOT want
to depend on passes that are unsupported (e.g. CompCert C) *)

(** Also, we separate code generation from proofs. In this file, we
define the compiler without any proof, so it depends on no proof of
any compiler pass. *)

(** I can list the passes of CompCert backwards by heart! *)

Require compcert.x86.Asmgen.
Require compcert.backend.Stacking.
Require compcert.backend.CleanupLabels.
Require compcert.backend.Linearize.
Require compcert.backend.Tunneling.
Require compcert.backend.Allocation.
Require DeadcodeX.
Require ConstpropX.
Require CSEX.
Require compcert.backend.Renumber.
Require InliningX.
Require compcert.backend.Tailcall.
Require compcert.backend.RTLgen.
Require SelectionX.
Require compcert.cfrontend.Cminorgen.
Require compcert.cfrontend.Cshmgen.
Require ComposePasses.

Import Coqlib.
Import String.
Import Errors.
Import AST.
Import ComposePasses.

Local Open Scope string_scope.

(** * Composing the translation passes *)

Definition transf_clight_program_to_rtl (p: Clight.program) : res RTL.program :=
  OK p
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ Selection.sel_program
  @@@ RTLgen.transl_program
   @@ Tailcall.transf_program.

Definition transf_rtl_program (fenv: Inlining.funenv) (p: RTL.program): res Asm.program :=
  OK p
  @@@ (InliningX.transf_program fenv)
   @@ Renumber.transf_program
   @@ ConstpropX.transf_program
   @@ Renumber.transf_program
  @@@ CSEX.transf_program
  @@@ DeadcodeX.transf_program
  @@@ Allocation.transf_program
   @@ Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ CleanupLabels.transf_program
  @@@ Stacking.transf_program
  @@@ Asmgen.transf_program.

Opaque SelectionX.sel_program.

(** Now, let's prove that our compiler is a per-function compiler
    (given an inlining parameter, which we do not care about how
    it is computed). *)

Definition transf_clight_fundef_to_rtl (ce: Ctypes.composite_env) (dm : Maps.PTree.t (globdef Cminor.fundef unit))
           (hf: SplitLong.helper_functions)
  :
  forall (i : ident) (p: Clight.fundef), res RTL.fundef.
Proof.
  intros i p.
  refine ((Cshmgen.transl_fundef ce >> _) i p).
  intro i'.
  refine ((Cminorgen.transl_fundef ;;; _)).
  refine (SelectionX.sel_fundef dm hf ;;; _).
  refine (RTLgen.transl_fundef ;> _).
  apply Tailcall.transf_fundef.
Defined.

Definition transf_rtl_fundef (fenv: Inlining.funenv): forall (p: RTL.fundef), res Asm.fundef :=
  (Inlining.transf_fundef fenv)
    ;> Renumber.transf_fundef
    ;> ConstpropX.transf_fundef
    ;> Renumber.transf_fundef
  ;;; CSEX.transf_fundef
  ;;; DeadcodeX.transf_fundef
  ;;; Allocation.transf_fundef
  ;> Tunneling.tunnel_fundef
  ;;; Linearize.transf_fundef
  ;> CleanupLabels.transf_fundef
  ;;; Stacking.transf_fundef
  ;;; Asmgen.transf_fundef
.

(** Auxiliary functions. These functions should be used only in proofs, and should not be extracted,
    because if the computation of [fenv] is based on [transf_clight_fundef_to_rtl], then
    using [transf_clight_fundef'] will call [transf_clight_fundef_to_rtl] twice. *)

(** In other words, we can consider those functions as the "syntactic
    specification" of the CompCertX compiler. *)

Definition transf_clight_fundef'
           (ce: Ctypes.composite_env) dm hf
           (fenv: Inlining.funenv): forall (i: ident) (p: Clight.fundef), res Asm.fundef :=
  (transf_clight_fundef_to_rtl ce dm hf)
    >> (fun _ => transf_rtl_fundef fenv).

Definition transf_clight_program'
           (fenv: Inlining.funenv) (p: Clight.program): res Asm.program :=
  OK p
     @@@ transf_clight_program_to_rtl
     @@@ (transf_rtl_program fenv)
.

Ltac apply_elim :=
  ComposePasses.apply_elim idtac.

Ltac compose_elim :=
  match goal with
    | [ H : transform_partial_program
              (?f1 ;;; ?f2) _ = OK _ |- _ ] =>
      apply transform_partial_program_compose_in_out in H;
        ComposePasses.compose_elim idtac
    | [ H : transform_partial_program
              (?f1 ;> ?f2) _ = OK _ |- _ ] =>
      apply transform_partial_program_compose_right_in_out in H;
        ComposePasses.compose_elim idtac
    | _ => ComposePasses.compose_elim idtac
  end.


Definition clight_helpers (p: Clight.program) :=
  OK p
     @@@
     (Cshmgen.transl_program
        ;;; Cminorgen.transl_program
        ;> (@prog_defmap Cminor.fundef unit)).

Lemma transf_clight_fundef_to_rtl_program:
  forall (p: Clight.program) (tp: RTL.program) dm hf,
    clight_helpers p = OK dm ->
    Selection.get_helpers dm = OK hf ->
    transform_partial_program2 (transf_clight_fundef_to_rtl (Ctypes.prog_comp_env p) dm hf) Cshmgen.transl_globvar (Ctypes.program_of_program p) = OK tp ->
    transf_clight_program_to_rtl p = OK tp.
Proof.
  unfold transf_clight_program_to_rtl, transf_clight_fundef_to_rtl, clight_helpers.
  intros p tp dm hf DM HELPERS H.
  simpl in *.
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar >> (fun i v => OK v)) in H by reflexivity.
  eapply transform_partial_program2_compose_in_out in H.
  compose_elim.
  match type of Hbc with
    | transform_partial_program2 (fun _ => ?tf) ?tv ?b = _ =>
      change (transform_partial_program2 (fun _ => tf) tv b) with (transform_partial_program tf b) in Hbc
  end.
  repeat compose_elim.
  eapply apply_partial_intro; eauto.
  eapply apply_partial_intro; eauto.
  eapply apply_partial_intro; eauto.
  eapply apply_partial_intro; eauto.
  unfold Cshmgen.transl_program in Hab4. assert (b = b4) by congruence. subst.
  unfold Cminorgen.transl_program in Hbc. assert (b0 = b3) by congruence. subst.
  unfold SelectionX.sel_fundef in Hab1.
  eapply apply_partial_intro; eauto.
Qed.

Lemma transf_rtl_fundef_to_program:
  forall fenv p tp,
    transform_partial_program (transf_rtl_fundef fenv) p = OK tp ->
    transf_rtl_program fenv p = OK tp.
Proof.
  unfold transf_rtl_program, transf_rtl_fundef. intros.
  repeat compose_elim.
  repeat (eapply apply_partial_intro; eauto).
Qed.

Lemma transf_clight_fundef_to_program':
  forall fenv p tp dm hf,
    clight_helpers p = OK dm ->
    Selection.get_helpers dm = OK hf ->
    transform_partial_program2 (transf_clight_fundef' (Ctypes.prog_comp_env p) dm hf fenv) Cshmgen.transl_globvar
                               (Ctypes.program_of_program p) = OK tp ->
    transf_clight_program' fenv p = OK tp.
Proof.
  unfold transf_clight_program', transf_clight_fundef'.
  intros fenv p tp dm hf DM HELPERS H.
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar >> (fun _ v => OK v)) in H by reflexivity.
  eapply transform_partial_program2_compose_in_out in H.  compose_elim.
  match type of Hbc with
    | transform_partial_program2 (fun _ => ?tf) ?tv ?b = _ =>
      change (transform_partial_program2 (fun _ => tf) tv b) with (transform_partial_program tf b) in Hbc
  end.
  simpl.
  unfold apply_partial.
  erewrite transf_clight_fundef_to_rtl_program; eauto.
  eapply transf_rtl_fundef_to_program; eauto.
Qed.

Ltac compose_intro :=
  match goal with
    | [ |- transform_partial_program (?f1 ;> ?f2) _ = OK _ ] =>
      eapply transform_partial_program_compose_right_out_in; eapply compose_partial_intro; eauto
    | [ |- transform_partial_program (?f1 ;;; ?f2) _ = OK _ ] =>
      eapply transform_partial_program_compose_out_in; eapply compose_partial_intro; eauto
  end.

Lemma transf_clight_program_to_rtl_fundef:
  forall p tp dm hf
    (DM: clight_helpers p = OK dm)
    (HELPERS: Selection.get_helpers dm = OK hf),
    transf_clight_program_to_rtl p = OK tp ->
    transform_partial_program2 (transf_clight_fundef_to_rtl
                                  (Ctypes.prog_comp_env p) dm hf)
                               Cshmgen.transl_globvar
                               (Ctypes.program_of_program p) = OK tp.
Proof.
  unfold transf_clight_program_to_rtl, transf_clight_fundef_to_rtl.
  intros.
  repeat apply_elim.
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar >> (fun i v => OK v)) by reflexivity.
  eapply transform_partial_program2_compose_out_in.
  eapply compose_partial_intro; eauto.
  eapply transform_partial_program_compose_out_in.
  eapply compose_partial_intro; eauto.
  repeat compose_intro.
  revert Har0.
  unfold Selection.sel_program.
  revert DM; unfold clight_helpers.
  simpl.
  unfold compose_total_right, compose_partial; simpl. rewrite Har2.
  simpl. rewrite Har1; simpl. intro A; inv A.
  rewrite HELPERS. simpl. tauto.
Qed.

Lemma transf_rtl_program_to_fundef:
  forall fenv p tp,
    transf_rtl_program fenv p = OK tp ->
    transform_partial_program (transf_rtl_fundef fenv) p = OK tp.
Proof.
  unfold transf_rtl_program, transf_rtl_fundef.
  intros.
  repeat apply_elim.
  repeat compose_intro.
Qed.

Lemma transf_clight_program_to_fundef':
  forall fenv p tp dm hf
    (DM: clight_helpers p = OK dm)
    (HELPERS: Selection.get_helpers dm = OK hf),
    transf_clight_program' fenv p = OK tp ->
    transform_partial_program2 (transf_clight_fundef' (Ctypes.prog_comp_env p) dm hf fenv)
                               Cshmgen.transl_globvar (Ctypes.program_of_program p) = OK tp.
Proof.
  unfold transf_clight_program', transf_clight_fundef'.
  intros.
  repeat apply_elim.
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar >> (fun _ v => OK v)) by reflexivity.
  eapply transform_partial_program2_compose_out_in.
  eapply compose_partial_intro.
  eapply transf_clight_program_to_rtl_fundef; eauto.
  eapply transf_rtl_program_to_fundef; eauto.
Qed.

(** Now, let's prove that our compiler does not change well-typed external functions *)

Theorem transf_clight_fundef_external:
  forall cenv dm hf fenv i ef tl ty cc,
    ef_sig ef = Ctypes.signature_of_type tl ty cc ->
    transf_clight_fundef' cenv dm hf fenv i (Ctypes.External ef tl ty cc) = OK (AST.External ef).
Proof.
  unfold transf_clight_fundef'. unfold transf_clight_fundef_to_rtl, transf_rtl_fundef.
  simpl. intros.
  unfold compose_partial, apply_partial.
  unfold compose_partial'. simpl.
  destruct (signature_eq (ef_sig ef) (Ctypes.signature_of_type tl ty cc)); try contradiction.
  reflexivity.
Qed.

(** Now, let's prove that our compiler is a per-function compiler for internal functions. *)

Definition transf_clight_function_to_rtl (ce: Ctypes.composite_env)(dm : Maps.PTree.t (globdef Cminor.fundef unit))
           (hf: SplitLong.helper_functions):
  forall (p: Clight.function), res RTL.function :=
  (Cshmgen.transl_function ce
    ;;;
    (Cminorgen.transl_function
       ;;; SelectionX.sel_function dm hf
       ;;; RTLgen.transl_function ;>
       Tailcall.transf_function)).

Definition transf_rtl_function fenv: forall (p: RTL.function), res Asm.function :=
(Inlining.transf_function fenv)
  ;> Renumber.transf_function
  ;> ConstpropX.transf_function
  ;> Renumber.transf_function
  ;;; CSEX.transf_function
  ;;; DeadcodeX.transf_function
      ;;; Allocation.transf_function
      ;> Tunneling.tunnel_function
      ;;; Linearize.transf_function
      ;> CleanupLabels.transf_function
      ;;; Stacking.transf_function
      ;;; Asmgen.transf_function
.

Definition transf_clight_function' cenv (dm : Maps.PTree.t (globdef Cminor.fundef unit))
           (hf: SplitLong.helper_functions) fenv: forall (p: Clight.function), res Asm.function :=
  transf_clight_function_to_rtl cenv dm hf
    ;;; (transf_rtl_function fenv).

Ltac rewrite_step :=
  match goal with
    | [ H : ?x = OK ?y |- context [ bind ?x _ ] ] =>
      rewrite H; simpl
  end.

Theorem transf_clight_fundef_internal:
  forall cenv dm hf fenv f tf i,
    transf_clight_function' cenv dm hf fenv f = OK tf ->
    transf_clight_fundef' cenv dm hf fenv i (Ctypes.Internal f) = OK (AST.Internal tf).
Proof.
  intros.
  unfold transf_clight_function', transf_clight_function_to_rtl, transf_rtl_function in H.
  repeat compose_elim.
  unfold transf_clight_fundef', transf_clight_fundef_to_rtl, transf_rtl_fundef.
  unfold compose_partial, apply_partial, compose_total_right, apply_total, compose_partial'.
  unfold SelectionX.sel_function in *.
  unfold CSEX.transf_function in *.
  unfold ConstpropX.transf_function in *.
  unfold DeadcodeX.transf_function in *.
  simpl.
  repeat rewrite_step.
  reflexivity.
Qed.

Theorem transf_clight_function_to_rtl_internal:
  forall f tf cenv dm hf i,
    transf_clight_function_to_rtl cenv dm hf f = OK tf ->
    transf_clight_fundef_to_rtl cenv dm hf i (Ctypes.Internal f) = OK (Internal tf).
Proof.
  unfold transf_clight_function_to_rtl, transf_clight_fundef_to_rtl.
  intros.
  repeat compose_elim.
  unfold compose_partial, apply_partial, compose_total_right, apply_total, compose_partial'.
  simpl.
  unfold SelectionX.sel_function in *.
  repeat rewrite_step.
  reflexivity.
Qed.

(** An alternative splitting for the compiler: from Clight to Linear,
   then from Linear to Asm. *)

Definition transf_rtl_program_to_linear  (fenv: Inlining.funenv) (p: RTL.program) : res Linear.program :=
  OK p
  @@@ (InliningX.transf_program fenv)
   @@ Renumber.transf_program
   @@ ConstpropX.transf_program
   @@ Renumber.transf_program
  @@@ CSEX.transf_program
  @@@ DeadcodeX.transf_program
  @@@ Allocation.transf_program
   @@ Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ CleanupLabels.transf_program
.

Definition transf_linear_program (p: Linear.program): res Asm.program :=
  OK p
  @@@ Stacking.transf_program
  @@@ Asmgen.transf_program.

Lemma transf_rtl_program_to_linear_to_asm_correct fenv p:
  OK p
 @@@ (transf_rtl_program_to_linear fenv)
 @@@ transf_linear_program
=
  transf_rtl_program fenv p.
Proof.
  simpl.
  unfold transf_rtl_program, transf_rtl_program_to_linear, transf_linear_program.
  simpl.
  destruct (InliningX.transf_program fenv p); simpl; auto.
  destruct (CSEX.transf_program
              (Renumber.transf_program
                 (ConstpropX.transf_program (Renumber.transf_program p0)))); simpl; auto.
  destruct (DeadcodeX.transf_program p1); simpl; auto.
  destruct (Allocation.transf_program p2); simpl; auto.
  destruct (Linearize.transf_program (Tunneling.tunnel_program p3)); simpl; auto.
Qed.
