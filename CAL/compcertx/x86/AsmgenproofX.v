Require Asmgenproof.
Require SmallstepX.
Require EventsX.
Require AsmX.
Require MachX.

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
Import MachX.
Import AsmX.
Import Asmgen.
Export Asmgenproof.

Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls}.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Let MATCH_PROG := transf_program_match _ _ TRANSF.

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  apply senv_preserved. auto.
Qed.

Variables
   (init_asm_rs: Asm.regset)
   (i: ident)
   (b: block)
   (Hsymb: Genv.find_symbol (Genv.globalenv tprog) i = Some b)
   (HPC: init_asm_rs PC = Vptr b Ptrofs.zero)
   (HSP_NOT_VUNDEF: init_asm_rs SP <> Vundef)
   (HRA_NOT_VUNDEF: init_asm_rs RA <> Vundef)
.

Definition init_mach_rs: Mach.regset := (fun r => init_asm_rs (preg_of r)).
Let init_sp := init_asm_rs SP.
Let init_ra := init_asm_rs RA.

Lemma extcall_arg_match:
  forall m l v,
  Mach.extcall_arg init_mach_rs m init_sp l v ->
  Asm.extcall_arg init_asm_rs m l v.
Proof.
  intros. inv H.
  constructor.
  unfold load_stack in H0.
  econstructor. eauto. assumption.
Qed.

Lemma extcall_arg_pair_match:
  forall m l v,
  Mach.extcall_arg_pair init_mach_rs m init_sp l v ->
  Asm.extcall_arg_pair init_asm_rs m l v.
Proof.
  intros. inv H; constructor; eauto using extcall_arg_match.
Qed.

Lemma extcall_args_match:
  forall m ll vl,
  list_forall2 (Mach.extcall_arg_pair init_mach_rs m init_sp) ll vl ->
  list_forall2 (Asm.extcall_arg_pair init_asm_rs m) ll vl.
Proof.
  induction 1; intros; constructor; auto using extcall_arg_pair_match.
Qed.

Lemma extcall_arguments_match:
  forall m sg args,
  Mach.extcall_arguments init_mach_rs m init_sp sg args ->
  Asm.extcall_arguments init_asm_rs m sg args.
Proof.
  unfold Mach.extcall_arguments, Asm.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
Qed.

Lemma extcall_arg_match_inv:
  forall m,
  forall l v,
  Asm.extcall_arg init_asm_rs m l v ->
  Mach.extcall_arg init_mach_rs m (init_asm_rs RSP) l v.
Proof.
  intros. inv H.
  constructor.
  econstructor. eauto.
Qed.

Lemma extcall_arg_pair_match_inv:
  forall m,
  forall l v,
  Asm.extcall_arg_pair init_asm_rs m l v ->
  Mach.extcall_arg_pair init_mach_rs m (init_asm_rs RSP) l v.
Proof.
  intros. inv H; constructor; eauto using extcall_arg_match_inv.
Qed.

Lemma extcall_args_match_inv:
  forall m ll vl,
  list_forall2 (Asm.extcall_arg_pair init_asm_rs m) ll vl ->
  list_forall2 (Mach.extcall_arg_pair init_mach_rs m (init_asm_rs RSP)) ll vl.
Proof.
  induction 1; intros; constructor; auto using extcall_arg_pair_match_inv.
Qed.

Lemma machregs_type:
  AsmX.wt_regset init_asm_rs ->
  forall r,
    Val.has_type (init_mach_rs r)
                 (Machregs.mreg_type r).
Proof.
  unfold AsmX.wt_regset. intros.
  unfold init_mach_rs.
  generalize (H (preg_of r)).
  destruct r; simpl; tauto.
Qed.

Hypothesis init_sp_type: Val.has_type (init_asm_rs RSP) Tptr.

Lemma transf_initial_states:
  forall sg args m,
  forall st1, MachX.initial_state init_mach_rs init_sp prog i sg args m st1 ->
  exists st2, AsmX.initial_state init_asm_rs tprog i sg args m st2 /\ match_states prog init_sp init_ra st1 st2.
Proof.
  inversion 1; subst.
  generalize Hb.
  esplit. split. econstructor.
   eassumption.
   assumption.
   apply extcall_arguments_match; eauto.
  constructor.
  constructor.
  apply Mem.extends_refl.
  constructor. reflexivity.
  assumption.
  assumption.
  intro. apply Val.lessdef_refl.
  erewrite symbols_preserved in Hsymb; eauto. congruence.
  reflexivity.
Qed.

Lemma transf_final_states:
  forall sg,
  forall st1 st2 r
    (MATCH: match_states prog init_sp init_ra st1 st2)
    (FINAL: MachX.final_state init_mach_rs sg st1 r),
    final_state_with_extends (AsmX.final_state init_asm_rs sg) st2 r.
Proof.
  intros.
  inv FINAL.
  inv MATCH.
  inv STACKS.
  inv AG.
  econstructor.
  econstructor.
  symmetry; assumption.
  symmetry; assumption.
  reflexivity.
  assumption.
  intros. eapply Val.lessdef_trans. eapply CALLEE_SAVE. assumption. auto.
  assumption.
  unfold loc_external_result.
  generalize (loc_result sg). induction r; simpl; auto.
  apply Val.longofwords_lessdef; auto.
Qed.

Hypothesis init_ra_type: Val.has_type (init_asm_rs RA) Tptr.

Theorem transf_program_correct:
  forall sg args m,
  forward_simulation
    (MachX.semantics Asmgenproof0.return_address_offset init_mach_rs init_sp init_ra prog i sg args m)
    (semantics_with_extends (AsmX.semantics init_asm_rs tprog i sg args m)).
Proof.
  intros.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved.
  assumption.
  apply transf_initial_states.
  apply transf_final_states.
  apply step_simulation.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

End PRESERVATION.
