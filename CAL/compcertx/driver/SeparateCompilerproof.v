
(** We do NOT import compcert.driver.Compiler, because we do NOT want
to depend on passes that are unsupported (e.g. CompCert C) *)

(** I can list the passes of CompCert backwards by heart! *)

Require SeparateCompiler.
Require AsmgenproofX.
Require StackingproofX.
Require CleanupLabelsproofX.
Require LinearizeproofX.
Require TunnelingproofX.
Require AllocproofX.
Require DeadcodeproofX.
Require ConstpropproofX.
Require CSEproofX.
Require RenumberproofX.
Require InliningproofX.
Require TailcallproofX.
Require RTLgenproofX.
Require SelectionproofX.
Require CminorgenproofX.
Require CshmgenproofX.
Require RTLtypingX.

Import Coqlib.
Import String.
Import Errors.
Import AST.
Import Values.
Import MemoryX.
Import Globalenvs.
Import ComposePasses.
Import Events.
Import SmallstepX.
Import Conventions1.
Import Asm.
Import SeparateCompiler.

Local Open Scope string_scope.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Cminor] / [RTL] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).

These results establish the correctness of the whole compiler! *)

Section WITHCONFIG.
Context mem `{external_calls_prf : ExternalCalls mem}
        `{memory_model_x: !Mem.MemoryModelX mem}.

Context {i64_helpers: SplitLongproof.I64HelpersCorrect mem}.

Variables
  (p: Clight.program) (p2: RTL.program)
  (TRANSL_TO_RTL: transf_clight_program_to_rtl p = OK p2)

  (** For Inlining, we need a parameter which contains functions to inline. We do not care here
      how it is computed, as long as it is sound with the intermediate representation p2.
      It can be very well instantiated with [PTree.empty _] to disable function inlining. *)
  (fenv: Inlining.funenv)
  (FENV_COMPAT: fenv = Inlining.funenv_program p2)  (* Inliningspec.fenv_compat p2 fenv) *)
.

  Definition ltyp_of_typ t :=
    match t with
      Tint | Tany32 | Tsingle => Tany32
    | _ => Tany64
    end.

  Definition low_sig sg :=
    mksignature (map ltyp_of_typ (sig_args sg))
                (option_map ltyp_of_typ (sig_res sg))
                (sig_cc sg).


  Lemma transf_clight_to_linear_correct:
    forall
      (tp: Linear.program)
      (TRANSL_TO_LINEAR: transf_rtl_program_to_linear fenv p2 = OK tp)
      m
      (INJECT_NEUTRAL: Mem.inject_neutral (Mem.nextblock m) m)
      (GENV_NEXT: Ple (Genv.genv_next (Genv.globalenv tp)) (Mem.nextblock m))
      (* NOTE: arguments here are considered as *assembly* arguments,
         i.e. longs encoded as two ints. *)
      args
      (args_inj: Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args)
      sg
      init_linear_rs
      (Hargs_val:   args = map (fun r : rpair Locations.loc => Locations.Locmap.getpair r init_linear_rs) (loc_arguments sg))
 
      (Hargs_type:
         Val.has_type_list
           (map (fun r : rpair Locations.loc => Locations.Locmap.getpair r init_linear_rs) (loc_arguments sg))
           (sig_args sg))
      i
    ,
      forward_simulation
        (ClightX.semantics p i m sg args)
        (semantics_with_inject (LinearX.semantics init_linear_rs tp i sg args m) m).
  Proof.
    intros.
    revert TRANSL_TO_RTL; unfold transf_clight_program_to_rtl; simpl.
    caseEq (Cshmgen.transl_program p); simpl; try congruence; intros p01 EQ01.
    caseEq (Cminorgen.transl_program p01); simpl; try congruence; intros p02 EQ02.
    caseEq (Selection.sel_program p02); simpl; try congruence; intros p1 EQ03.
    caseEq (RTLgen.transl_program p1); simpl; try congruence; intros p11 EQ11.
    intro.
    inv TRANSL_TO_RTL.
    set (p2 := Tailcall.transf_program p11) in *.
    revert TRANSL_TO_LINEAR; unfold transf_rtl_program_to_linear; simpl.
    caseEq (InliningX.transf_program (Inlining.funenv_program p2) p2); simpl; try congruence; intros p3 EQ3.
    set (p31 := Renumber.transf_program p3) in *.
    set (p32 := ConstpropX.transf_program p31) in *.
    set (p33 := Renumber.transf_program p32) in *.
    caseEq (CSEX.transf_program p33); simpl; try congruence; intros p34 EQ34.
    caseEq (DeadcodeX.transf_program p34); simpl; try congruence; intros p35 EQ35.
    caseEq (Allocation.transf_program p35); simpl; try congruence; intros p4 EQ4.
    set (p5 := Tunneling.tunnel_program p4) in *.
    caseEq (Linearize.transf_program p5); simpl; try congruence; intros p6 EQ6.
    set (p7 := CleanupLabels.transf_program p6) in *.
    intro EQTP.
    inv EQTP.
    eapply compose_forward_simulations.
    apply CshmgenproofX.transl_program_correct. eassumption.
    eapply compose_forward_simulations.
    apply CminorgenproofX.transl_program_correct. eassumption.
    assumption.
    {
      erewrite <- Cminorgenproof.genv_next_preserved; eauto using Cminorgenproof.transf_program_match.
      erewrite <- Selectionproof.genv_next_preserved; eauto using Selectionproof.transf_program_match.
      erewrite <- RTLgenproof.genv_next_preserved; eauto using RTLgenproof.transf_program_match.
      erewrite <- Tailcallproof.genv_next_preserved; eauto using Tailcallproof.transf_program_match.
      erewrite <- Inliningproof.genv_next_preserved; eauto using Inliningproof.transf_program_match.
      erewrite <- Renumberproof.genv_next_preserved; eauto using Renumberproof.transf_program_match. fold p31.
      rewrite <- ConstpropproofX.genv_next_preserved. fold p32.
      erewrite <- Renumberproof.genv_next_preserved; eauto using Renumberproof.transf_program_match. fold p33.
      erewrite <- CSEproofX.genv_next_preserved; eauto.
      erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
      erewrite <- Allocproof.genv_next_preserved; eauto using Allocproof.transf_program_match.
      erewrite <- Tunnelingproof.genv_next_preserved; eauto using Tunnelingproof.transf_program_match. fold p5.
      erewrite <- Linearizeproof.genv_next_preserved.
      erewrite <- CleanupLabelsproof.genv_next_preserved; eauto using CleanupLabelsproof.transf_program_match.
      eapply Linearizeproof.transf_program_match. eauto.
    }
    assumption.
    eapply compose_forward_simulations.
    {
      apply forward_simulation_extends_right_inject.
      apply SelectionproofX.transf_program_correct. eauto.
    }
    eapply compose_forward_simulations.
    {
      apply forward_simulation_extends_right_inject.
      apply RTLgenproofX.transf_program_correct. eassumption.
    }
    eapply compose_forward_simulations.
    {
      eapply forward_simulation_extends_right_inject.
      apply TailcallproofX.transf_program_correct.
    }
    eapply compose_forward_simulations.
    {
      eapply forward_simulation_inject_right.
      eapply InliningproofX.transf_program_correct; eauto.
      erewrite <- Inliningproof.genv_next_preserved; eauto using Inliningproof.transf_program_match.
      erewrite <- Renumberproof.genv_next_preserved; eauto using Renumberproof.transf_program_match. fold p31.
      rewrite <- ConstpropproofX.genv_next_preserved. fold p32.
      erewrite <- Renumberproof.genv_next_preserved; eauto using Renumberproof.transf_program_match. fold p33.
      erewrite <- CSEproofX.genv_next_preserved; eauto.
      erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
      erewrite <- Allocproof.genv_next_preserved; eauto using Allocproof.transf_program_match.
      erewrite <- Tunnelingproof.genv_next_preserved; eauto using Tunnelingproof.transf_program_match. fold p5.
      erewrite <- Linearizeproof.genv_next_preserved.
      erewrite <- CleanupLabelsproof.genv_next_preserved; eauto using CleanupLabelsproof.transf_program_match.
      eapply Linearizeproof.transf_program_match. eauto.
    }
    eapply forward_simulation_extends_right_inject.
    eapply compose_forward_simulations.
    eapply RenumberproofX.transf_program_correct.
    eapply compose_forward_simulations.
    eapply ConstpropproofX.transf_program_correct; eauto.
    {
        fold p31.
        rewrite <- ConstpropproofX.genv_next_preserved. fold p32.
        erewrite <- Renumberproof.genv_next_preserved; eauto using Renumberproof.transf_program_match. fold p33.
        erewrite <- CSEproofX.genv_next_preserved; eauto.
        erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
        erewrite <- Allocproof.genv_next_preserved; eauto using Allocproof.transf_program_match.
        erewrite <- Tunnelingproof.genv_next_preserved; eauto using Tunnelingproof.transf_program_match. fold p5.
        erewrite <- Linearizeproof.genv_next_preserved. 2: eauto using Linearizeproof.transf_program_match.
        erewrite <- CleanupLabelsproof.genv_next_preserved; eauto.
        subst. eapply CleanupLabelsproof.transf_program_match.
    }
    eapply forward_simulation_extends_right.
    eapply compose_forward_simulations.
    eapply RenumberproofX.transf_program_correct.
    eapply compose_forward_simulations.
    {
      eapply CSEproofX.transf_program_correct; eauto.
      {
        fold p31. fold p32. fold p33.
        erewrite <- CSEproofX.genv_next_preserved; eauto.
        erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
        erewrite <- Allocproof.genv_next_preserved; eauto using Allocproof.transf_program_match.
        erewrite <- Tunnelingproof.genv_next_preserved; eauto using Tunnelingproof.transf_program_match. fold p5.
        erewrite <- Linearizeproof.genv_next_preserved. 2: eauto using Linearizeproof.transf_program_match.
        erewrite <- CleanupLabelsproof.genv_next_preserved; eauto.
        subst. eapply CleanupLabelsproof.transf_program_match.
      }
    }
    eapply compose_forward_simulations.
    eapply forward_simulation_extends_right.
    eapply DeadcodeproofX.transf_program_correct; eauto.
    {
      erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
      erewrite <- Allocproof.genv_next_preserved; eauto using Allocproof.transf_program_match.
      erewrite <- Tunnelingproof.genv_next_preserved; eauto using Tunnelingproof.transf_program_match. fold p5.
      erewrite <- Linearizeproof.genv_next_preserved. 2: eauto using Linearizeproof.transf_program_match.
      erewrite <- CleanupLabelsproof.genv_next_preserved; eauto.
      subst. eapply CleanupLabelsproof.transf_program_match.
    }
    eapply forward_simulation_extends_right.
    eapply compose_forward_simulations.
    {
      apply AllocproofX.transf_program_correct. eassumption.
      reflexivity.
      eassumption.
    }
    eapply compose_forward_simulations.
    {
      apply forward_simulation_extends.
      apply TunnelingproofX.transf_program_correct.
    }
    eapply compose_forward_simulations.
    {
      apply forward_simulation_extends.
      apply LinearizeproofX.transf_program_correct. eassumption.
    }
    apply forward_simulation_extends.
    apply CleanupLabelsproofX.transf_program_correct.
  Qed.


  Lemma plt_eq_eq:
    forall a b, (forall c, Plt c a <-> Plt c b) -> a = b.
  Proof.
    intros.
    destruct (plt a b). specialize (H a). rewrite <- H in p0. xomega.
    destruct (plt b a). specialize (H b). rewrite H in p0. xomega. xomega.
  Qed.


Theorem transf_clight_program_correct:
  forall
         tp
         (TRANSL_TO_ASM: transf_rtl_program fenv p2 = OK tp)
         m init_asm_rs
         (ASM_INVARIANT: AsmX.asm_invariant (Genv.globalenv tp) init_asm_rs m)

         (** Arguments and so on, given by the local condition on Asm external call *)
         args sg
         (EXTCALL_ARGS: Asm.extcall_arguments init_asm_rs m sg args)
         i b
         (Hsymb:  Genv.find_symbol (Genv.globalenv tp) i = Some b)
         (PC_VAL: init_asm_rs PC = Values.Vptr b Integers.Ptrofs.zero)
         (SP_NOT_VUNDEF: init_asm_rs RSP <> Vundef)
         (TYP_SP: Val.has_type (init_asm_rs RSP) Tptr)
         (RA_NOT_VUNDEF: init_asm_rs RA <> Vundef)
         (TYP_RA: Val.has_type (init_asm_rs RA) Tptr)
         (ARGSSIZE: 4 * size_arguments sg <= Integers.Ptrofs.max_unsigned)

         (ARGSTYPE:  Val.has_type_list
                       (map
                          (fun r =>
                             Locations.Locmap.getpair
                               r
                               (StackingproofX.init_linear_rs
                                  (AsmgenproofX.init_mach_rs init_asm_rs)
                                  (init_asm_rs RSP) m))
                          (loc_arguments sg))
                       (sig_args sg))


         (* The C program has to be safe on the memory without arguments *)
         mh
         (FREE_ARGS: EraseArgs.free_extcall_args (init_asm_rs RSP) m (regs_of_rpairs (loc_arguments sg)) = Some mh)
         (SAFE: BehaviorsX.strongly_safe (ClightX.semantics p i mh sg args))
  ,
  forward_simulation
    (ClightX.semantics p i m sg args)
    (semantics_with_inject (AsmX.semantics init_asm_rs tp i sg args m) m).
Proof.
  intros.
  rewrite <- transf_rtl_program_to_linear_to_asm_correct in TRANSL_TO_ASM.
  simpl in TRANSL_TO_ASM.
  destruct (transf_rtl_program_to_linear fenv p2) as [p7 | ] eqn:LINEAR; try discriminate.
  simpl in TRANSL_TO_ASM.
  unfold transf_linear_program in TRANSL_TO_ASM.
  simpl in TRANSL_TO_ASM.
  revert TRANSL_TO_ASM.
  caseEq (Stacking.transf_program p7); simpl; try congruence; intros p8 EQ8.
  intro EQTP.
  revert FENV_COMPAT.
  inv ASM_INVARIANT.
  inv inv_inject_neutral.
  assert
    (Ple (Genv.genv_next (Genv.globalenv p7)) (Mem.nextblock m))
    as LE.
  {
    erewrite <- StackingproofX.genv_next_preserved; eauto.
    erewrite <- AsmgenproofX.genv_next_preserved; eauto.
  }
  assert (Mem.extends mh m) as EXTENDS.
  {
    eapply EraseArgs.free_extcall_args_extends; eauto.
  }
  exploit plt_eq_eq.
  intros. apply Mem.valid_block_extends. eauto. intro NEXT_mh.
  intro.
  (* from C to linear *)
  assert (forward_simulation
            (ClightX.semantics p i m sg args)
            (semantics_with_inject (LinearX.semantics (StackingproofX.init_linear_rs (AsmgenproofX.init_mach_rs init_asm_rs) (init_asm_rs RSP) m) p7 i sg args m) m))
         as C_to_linear.
  {
    eapply transf_clight_to_linear_correct.
    assumption.
    assumption.
    assumption.
    eapply AsmX.extcall_args_inject_neutral; eauto.
    eapply StackingproofX.extcall_args_eq. eapply AsmgenproofX.extcall_args_match_inv. eassumption.
    assumption.
  }

  (* from C to linear, BUT with the memory without arguments. *)

  assert (forward_simulation
            (ClightX.semantics p i mh sg args)
            (semantics_with_inject (LinearX.semantics (StackingproofX.init_linear_rs (AsmgenproofX.init_mach_rs init_asm_rs) (init_asm_rs RSP) m) p7 i sg args mh) mh))
         as C_to_linear_mh.
  {
    eapply transf_clight_to_linear_correct.
    assumption.
    eapply EraseArgsX.free_extcall_args_inject_neutral; eauto.
    congruence.
    rewrite NEXT_mh. eapply AsmX.extcall_args_inject_neutral; eauto.
    eapply StackingproofX.extcall_args_eq. eapply AsmgenproofX.extcall_args_match_inv. eassumption.
    assumption.
  }

  (* now, transport strong safety and go to Linear2 *)
  apply BehaviorsX.forward_simulation_strongly_safe in C_to_linear_mh; auto using ClightX.semantics_receptive, LinearX.semantics_weak_determ,  semantics_with_inject_weak_determ.
  apply BehaviorsX.strongly_safe_with_inject_elim in C_to_linear_mh.
  eapply Linear2X.per_module_linear_to_linear2 in C_to_linear_mh; eauto.
  rename C_to_linear_mh into linear_to_linear2.
  clear EXTENDS NEXT_mh.

  (* finally, connect with the remaining part *)
  eapply compose_forward_simulations.
  eassumption.
  eapply SmallstepX.forward_simulation_inject_right.
  eapply compose_forward_simulations.
  eassumption.
  eapply compose_forward_simulations.
  {
    apply StackingproofX.transf_program_correct. eassumption.
    apply AsmgenproofX.extcall_args_match_inv. assumption.
    assumption.
    erewrite <- AsmgenproofX.genv_next_preserved; eauto.
    intros; eapply inv_reg_inject_neutral.
    assumption.
    assumption.
    assumption.
    {
      intros ? ? VAL.
      generalize (inv_reg_inject_neutral RSP).
      rewrite VAL.
      inversion 1.
      clear H5.
      subst.
      unfold Mem.flat_inj in *.
      unfold Mem.valid_block.
      destruct (plt b0 (Mem.nextblock m)); congruence.
    }
    assumption.
    eapply AsmgenproofX.machregs_type; eauto.
    apply Asmgenproof.return_address_exists.
    eassumption.
  }
  apply forward_simulation_extends_right_inject.
  eapply AsmgenproofX.transf_program_correct. assumption.
  eassumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  eapply semantics_with_inject_weak_determ.
  eapply LinearX.semantics_weak_determ.
Qed.

End WITHCONFIG.
