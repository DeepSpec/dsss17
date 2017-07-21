Require EraseArgsX.
Require compcert.backend.Stackingproof.
Require MachX.
Require Linear2X.
Require SmallstepX.

Import Coqlib.
Import Integers.
Import AST.
Import ValuesX.
Import MemoryX.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Locations.
Import LinearX.
Import Lineartyping.
Import MachX.
Import Stacking.
Import EraseArgsX.
Export Stackingproof.

Section WITHMEMORYMODEL.
Context `{memory_model: Mem.MemoryModelX}.

Lemma free_extcall_args_out_of_bounds init_sp m sg m' :
  free_extcall_args init_sp m (regs_of_rpairs (Conventions1.loc_arguments sg)) = Some m' ->
  init_args_out_of_bounds init_sp sg m'.
Proof.
  unfold init_args_out_of_bounds.
  intros H b o H0 of ty H1 o0 H2.
  unfold loc_out_of_bounds.
  intro ABSURD.
  eapply free_extcall_args_no_perm; eauto.
Qed.

End WITHMEMORYMODEL.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.
Variable (return_address_offset : function -> code -> ptrofs -> Prop).

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let MATCH_PROG : match_prog prog tprog.
Proof.
  apply transf_program_match; auto.
Qed.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  eapply senv_preserved; eauto.
Qed.

Variables
  (init_mach_rs: Mach.regset)
  (init_sp: val)
  (init_m: mem)
.

Definition init_linear_rs: Locations.Locmap.t :=
    fun ros =>
      match ros with
        | R r => init_mach_rs r
        | S Outgoing ofs ty =>
          match load_stack init_m init_sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) with
            | Some v => v
            | None => Vundef
          end
        | _ => Vundef
      end.

Lemma extcall_arg_eq l v:
  Mach.extcall_arg init_mach_rs init_m init_sp l v ->
  v = init_linear_rs l.
Proof.
  intro H.
  inv H; auto.
  unfold init_linear_rs.
  rewrite H0.
  reflexivity.
Qed.

Lemma extcall_arg_pair_eq l v:
  Mach.extcall_arg_pair init_mach_rs init_m init_sp l v ->
  v = Locmap.getpair l init_linear_rs.
Proof.
  inversion 1; subst; eauto using extcall_arg_eq.
  simpl.
  f_equal; auto using extcall_arg_eq.
Qed.

Lemma extcall_args_eq:
  forall ll vl,
    list_forall2 (Mach.extcall_arg_pair init_mach_rs init_m init_sp) ll vl
  -> vl = map (fun r => Locmap.getpair r init_linear_rs) ll.
Proof.
  induction 1; simpl.
   reflexivity.
  f_equal; eauto using extcall_arg_pair_eq.
Qed.

Lemma extcall_arg_init_linear_rs:
  forall la,
    list_forall2 (extcall_arg_pair init_mach_rs init_m init_sp) la (map (fun r => Locmap.getpair r init_linear_rs) la) ->
    forall l, In l (regs_of_rpairs la) ->
    extcall_arg init_mach_rs init_m init_sp l (init_linear_rs l).
Proof.
  induction la; simpl; inversion 1; subst.
   tauto.
  intros l H0.
  apply in_app_iff in H0.
  destruct H0 as [ H0 | ] ; auto.
  inv H3.
  + destruct H0; try contradiction.
    subst.
    auto.
  + simpl in H0.
    destruct H0.
    - subst. auto.
      inv H2; constructor; auto.
      unfold init_linear_rs. rewrite H0. reflexivity.
    - destruct H0; try contradiction.
      subst.
      inv H6; constructor; auto.
      unfold init_linear_rs. rewrite H0. reflexivity.
Qed.

Variables
  (init_ra: val)
  (sg: signature)
  (args: list val)
  (Hargs: extcall_arguments init_mach_rs init_m init_sp sg args)
  (Hinject_neutral: Mem.inject_neutral (Mem.nextblock init_m) init_m)
  (Hgenv_next: Ple (Genv.genv_next tge) (Mem.nextblock init_m))
.

Hypothesis init_mach_rs_inj:
  forall r, Val.inject (Mem.flat_inj (Mem.nextblock init_m)) (init_mach_rs r) (init_mach_rs r).

Variable init_linear_m: mem.
Hypothesis init_linear_free_extcall_arg: free_extcall_args init_sp init_m (regs_of_rpairs (Conventions1.loc_arguments sg)) = Some init_linear_m.

Hypothesis init_sp_int: Val.has_type init_sp Tptr.

Context `{memory_model_x: !Mem.MemoryModelX mem}.
Hypothesis init_sp_valid:
  forall (b : block) (o : ptrofs),
    init_sp = Vptr b o -> Mem.valid_block init_m b.

Lemma extcall_arg_slot_change_reg:
  forall rs rs' m sl o t sp v,
    extcall_arg rs m sp (S sl o t) v ->
    extcall_arg rs' m sp (S sl o t) v.
Proof.
  intros rs rs' m sl o t sp v EA; inv EA; constructor; auto.
Qed.

Hypothesis args_bnds:   4 * Conventions1.size_arguments sg <= Ptrofs.max_unsigned.

Lemma transf_initial_states:
  forall i,
  forall s
         (INIT: Linear2X.initial_state init_linear_rs prog i sg args init_linear_m init_m s),
    exists s',
      MachX.initial_state init_mach_rs init_sp tprog i sg args init_m s' /\
      match_states
        return_address_offset
        prog tprog
        init_sp init_ra
        init_linear_rs sg
        init_sp_int
        init_m
        s s'.
Proof.
  inversion 1; subst.
  inversion init_lower; subst.
  exploit function_ptr_translated; eauto.
  destruct 1 as [tf [Htf TRANS]].
  esplit.
  split.
  - econstructor.
    erewrite symbols_preserved; eauto.
    assumption.
  - econstructor; eauto.
    + econstructor; eauto.
    + unfold init_linear_rs. red. eauto.
    + red. destruct l; simpl; auto.
    + red; congruence.
    + apply Ple_refl.
    + apply Ple_refl.
    + red. intros b0 o H of ty H1 o0 H2.
      inv init_higher. simpl.
      red; intros.
      eapply free_extcall_args_no_perm; eauto.
    + congruence.
    + red; red. eauto.
    + destruct init_sp eqn:?; simpl; auto.
      unfold Mem.flat_inj. destruct (plt b0 (Mem.nextblock init_m)); eauto.
      exfalso; apply n. eapply init_sp_valid. eauto.
    + red. unfold Mem.flat_inj.
      intros b' o' EQ b1 b2 delta1 delta2.
      destruct (plt b1 (Mem.nextblock init_m)); try discriminate.
      destruct (plt b2 (Mem.nextblock init_m)); try discriminate. congruence.
    + destruct init_sp; simpl in *; eauto.
    +
      Require Import Separation.
      Open Scope sep_scope.

      unfold stack_contents. rewrite Separation.sep_pure. split; auto.
      repeat split.
      * eapply Mem.neutral_inject. assumption.
      * simpl.
        red; intros.
        red in Hargs.
        exploit extcall_arg_init_linear_rs; eauto.
        intros.
        eexists; split.
        eapply extcall_arg_slot_change_reg. eauto.
        Opaque Z.mul.
        simpl.
        destruct sl; auto.
        unfold load_stack.
        destruct (Mem.loadv (chunk_of_type ty) init_m
                            (Val.offset_ptr init_sp (Ptrofs.repr (4 * of)))) eqn:?.
        destruct init_sp; try discriminate.
        exploit Mem.loadv_inject.
        eapply Mem.neutral_inject. eassumption.
        eassumption.
        simpl. econstructor.
        unfold Mem.flat_inj. destruct (plt b0 (Mem.nextblock init_m)). reflexivity.
        destruct n.
        eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies.
        eapply Mem.load_valid_access. unfold load_stack, Val.offset_ptr in Heqo. eexact Heqo.
        constructor.
        rewrite Ptrofs.add_zero.
        reflexivity.
        destruct 1 as [? [? ?]].
        unfold load_stack, Val.offset_ptr in Heqo.
        rewrite Heqo in H2. inv H2.
        assumption.
        auto.
      * simpl.
        exists (Mem.nextblock init_m).
        split; auto using Ple_refl.
        constructor.
        -- intros b0 H.
           unfold Mem.flat_inj.
           destruct (plt _ _); auto; contradiction.
        -- intros b1 b2 delta H H1.
           unfold Mem.flat_inj in H.
           destruct (plt _ _); congruence.
        -- intros id b0 H.
           apply Genv.genv_symb_range in H.
           fold ge in H.
           rewrite <- genv_next_preserved in H.
           xomega.
        -- intros id b0 H.
           apply Genv.find_funct_ptr_iff in H.
           apply Genv.genv_defs_range in H.
           fold ge in H.
           rewrite <- genv_next_preserved in H.
           xomega.
        -- intros id b0 H.
           apply Genv.find_var_info_iff in H.
           apply Genv.genv_defs_range in H.
           fold ge in H.
           rewrite <- genv_next_preserved in H.
           xomega.
      * red. simpl. easy.
    + constructor.
Qed.

Lemma transf_final_states:
  forall s s' r
    (MATCH: match_states
              return_address_offset
              prog tprog
              init_sp init_ra
              init_linear_rs sg
              init_sp_int
              init_m
              s s')
    (FIN: Linear2X.final_state init_linear_rs sg s r),
    final_state_with_inject (MachX.final_state init_mach_rs sg) init_m s' r.
Proof.
  intros.
  inv FIN.
  inversion fin_lower; subst.
  inv MATCH; try congruence.
  inv STACKS; try congruence.
  econstructor.
  econstructor.
  reflexivity.
  { (* Callee-save registers. *)
    intros.
    refine (_ (AGLOCS (R r) _)).
    simpl. intro REW.
    eapply Mem.val_inject_flat_inj_lessdef.
    eapply val_inject_incr_recip.
    rewrite <- REW.
    eapply AGREGS. 
    eapply init_mach_rs_inj.
    auto.
    unfold Conventions1.destroyed_at_call in H.
    Opaque all_mregs.
    rewrite filter_In in H.
    generalize (all_mregs_complete r). intro.
    destruct (Conventions1.is_callee_save r); tauto.
  }
  apply INCR_init. apply INCR_sep.
  apply sep_proj2 in SEP. apply mconj_proj1 in SEP.
  apply sep_proj1 in SEP; simpl in SEP; eauto.
  assert (m = m0) by congruence. subst. auto.
  generalize (Conventions1.loc_result sg).
  replace ls with rs in * by congruence.
  destruct r; simpl; eauto using Val.longofwords_inject.
Qed.

Hypothesis wt_init_mach_rs:
  forall r, Val.has_type (init_mach_rs r) (mreg_type r).

Lemma wt_init_linear_rs:
  wt_locset init_linear_rs.
Proof.
  red.
  destruct l.
  simpl; auto.
  destruct sl; try (constructor; fail).
  unfold init_linear_rs, load_stack.
  case_eq (
      Mem.loadv (chunk_of_type ty) init_m
                (Val.offset_ptr init_sp
                                (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos)))
    ); try (constructor; fail).
  destruct init_sp; try discriminate.
  unfold Val.offset_ptr, Mem.loadv.
  intros.
  exploit Mem.load_type; eauto.
  destruct ty; simpl; tauto.
Qed.

Theorem wt_initial_state:
  forall i,
  forall S, LinearX.initial_state init_linear_rs prog i sg args init_m S ->
            Lineartyping.wt_state init_linear_rs S.
Proof.
  induction 1.
  exploit Genv.find_funct_ptr_inversion; eauto.
  destruct 1.
  econstructor.
  apply wt_callstack_nil.
  eapply wt_init_linear_rs.
  eapply wt_prog. eassumption. eassumption.
  apply wt_init_linear_rs.
Qed.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Hypothesis init_ra_int:
  Val.has_type init_ra Tptr.

Theorem transf_program_correct:
  forall i,
  forward_simulation
    (Linear2X.semantics init_linear_rs prog i sg args init_linear_m init_m)
    (semantics_with_inject (MachX.semantics return_address_offset init_mach_rs init_sp init_ra tprog i sg args init_m) init_m)
.
Proof.
  set (ms :=
         fun s s' =>
           Lineartyping.wt_state init_linear_rs (Linear2.state_lower s) /\
           match_states return_address_offset prog tprog init_sp init_ra init_linear_rs sg init_sp_int init_m s s').
  intros.
  eapply forward_simulation_plus with (match_states := ms).
  - apply senv_preserved; auto.
  - intros. simpl in *.
    exploit transf_initial_states; eauto. intros [st2 [A B]].
    exists st2; split; auto. split; auto.
    inversion H; subst.
    eapply wt_initial_state; eauto.
  - intros. destruct H. eapply transf_final_states; eauto.
  - intros. destruct H0.
    exploit transf_step_correct.
    eassumption.
    eassumption.
    apply init_ra_int.
    simpl in H. eassumption.
    eexact H0.
    eexact H1.
    intros [s2' [A B]].
    inversion H; subst.
    assert (init_linear_rs = Linear2.state_init_ls s1) as INIT_LS.
    {
      inversion B; congruence.
    }
    exists s2'; split. exact A. split.
    eapply step_type_preservation; eauto.
    eapply wt_prog. eassumption.
    simpl in *. rewrite INIT_LS. eassumption.
    assumption.
Qed.

End WITHCONFIG.
