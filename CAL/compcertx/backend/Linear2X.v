Require LinearX.
Require EraseArgs.
Require compcert.backend.Linear2.
Require BehaviorsX.
Require OpX.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import MemoryX.
Import Globalenvs.
Import EventsX.
Import Smallstep.
Import Locations.
Import Conventions.
Import EraseArgs.
Export Linear2.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Inductive initial_state
          (lm: Linear.locset) (p: Linear.program) (i: ident)
          (sg: signature) (args: list val) (mh ml: mem) (s: Linear2.state): Prop :=
| initial_state_intro
    (init_higher: LinearX.initial_state lm p i sg args mh (state_higher s))
    (init_lower: LinearX.initial_state lm p i sg args ml (state_lower s))
    (init_ls: state_init_ls s = lm).

Inductive final_state
          (lm: Linear.locset) (sg: signature)
          (s: state) (vl: val * mem): Prop :=
| final_state_intro
    vh
    (fin_higher: LinearX.final_state lm sg (state_higher s) vh)
    (fin_lower: LinearX.final_state lm sg (state_lower s) vl).

Definition semantics
           (lm: Linear.locset)
           (p: Linear.program) (i: ident) (sg: signature) (args: list val) (mh ml: mem) :=
  Semantics (
      Linear2.step
    ) (initial_state lm p i sg args mh ml) (final_state lm sg) (Genv.globalenv p).


(* Preservation of Linear2 state invariant *)

Lemma lessdef_set r1 r2:
  (forall r, Val.lessdef (r1 r) (r2 r)) ->
  forall v1 v2,
    Val.lessdef v1 v2 ->
    forall i r,
      Val.lessdef (Locmap.set i v1 r1 r) (Locmap.set i v2 r2 r).
Proof.
  intros H v1 v2 H0 i r.
  unfold Locmap.set.
  destruct (Loc.eq i r).
  { subst. destruct r; auto. apply Val.load_result_lessdef. auto. }
  destruct (Loc.diff_dec i r); auto.
Qed.

Lemma lessdef_undef_regs rl:
  forall r1 r2,
    (forall r, Val.lessdef (r1 r) (r2 r)) ->
    forall r,
      Val.lessdef (LTL.undef_regs rl r1 r) (LTL.undef_regs rl r2 r).
Proof.
  induction rl; simpl; auto using lessdef_set.
Qed.

Lemma lessdef_list_reglist r1 r2
      (H: forall r, Val.lessdef (r1 r) (r2 r))
      l:
  Val.lessdef_list (LTL.reglist r1 l) (LTL.reglist r2 l).
Proof.
  induction l; simpl; auto.
Qed.

Lemma find_function_lessdef ge ros rs1 rs2 f':
  (forall r, Val.lessdef (rs1 r) (rs2 r)) ->
  Linear.find_function ge ros rs1 = Some f' ->
  Linear.find_function ge ros rs2 = Some f'.
Proof.
  unfold Linear.find_function.
  intros H H0.
  destruct ros; auto.
  exploit Genv.find_funct_inv; eauto.
  destruct 1 as (b & Hb).
  specialize (H (R m)).
  rewrite Hb in H.
  inversion H.
  congruence.
Qed.

Lemma return_regs_lessdef caller1 caller2 callee1 callee2:
  (forall r, Val.lessdef (caller1 r) (caller2 r)) ->
  (forall r, Val.lessdef (callee1 r) (callee2 r)) ->
  forall r,
    Val.lessdef (LTL.return_regs caller1 callee1 r) (LTL.return_regs caller2 callee2 r).
Proof.
  intros H H0 r.
  unfold LTL.return_regs.
  destruct r; auto.
  destruct (is_callee_save r); auto.
Qed.

Lemma parent_locset_lessdef lm stack1 stack2:
  invar_stack stack1 stack2 ->
  forall r, Val.lessdef (Linear.parent_locset lm stack1 r) (Linear.parent_locset lm stack2 r).
Proof.
  inversion 1; subst; simpl; auto.
  inversion H0; subst; auto.
Qed.

Lemma lessdef_map (rs1 rs2: Locmap.t)
      (H: forall r, Val.lessdef (rs1 r) (rs2 r))
      args:
  Val.lessdef_list (map rs1 args) (map rs2 args).
Proof.
  induction args; simpl; auto.
Qed.

Lemma lessdef_call_regs rs rsl:
  (forall r : loc, Val.lessdef (rs r) (rsl r)) ->
  forall r : loc, Val.lessdef (LTL.call_regs rs r) (LTL.call_regs rsl r).
Proof.
  intros H r.
  unfold LTL.call_regs.
  destruct r; auto.
  destruct sl; auto.
Qed.

Context `{memory_model_x: !Mem.MemoryModelX mem}.

Lemma lessdef_list_refl:
  forall l,
    Val.lessdef_list l l.
Proof.
  induction l; simpl; intros;  auto.
Qed.

Lemma lessdef_setres:
  forall res vres vres2 l rs rs2,
    Val.lessdef vres vres2 ->
    (forall r, Val.lessdef (rs r) (rs2 r)) ->
    Val.lessdef (Locmap.setres res vres rs l)
                (Locmap.setres res vres2 rs2 l).
Proof.
  induction res; simpl; intros; eauto.
  apply lessdef_set; auto.
  eapply IHres2. apply Val.loword_lessdef; auto.
  intros.
  eapply IHres1; eauto.
  apply Val.hiword_lessdef; auto.
Qed.


Lemma lessdef_setpair:
  forall res vres vres2 l rs rs2,
    Val.lessdef vres vres2 ->
    (forall r, Val.lessdef (rs r) (rs2 r)) ->
    Val.lessdef (Locmap.setpair res vres rs l)
                (Locmap.setpair res vres2 rs2 l).
Proof.
  destruct res; simpl; intros; eauto;
    repeat apply lessdef_set; auto.
  apply Val.hiword_lessdef; auto.
  apply Val.loword_lessdef; auto.
Qed.


Lemma lessdef_map':
  forall args rs1 rs2,
    (forall x, Val.lessdef (rs1 x) (rs2 x)) ->
    Val.lessdef_list
      (map (fun p : rpair loc => Locmap.getpair p rs1) args)
      (map (fun p : rpair loc => Locmap.getpair p rs2) args).
Proof.
  induction args; simpl; intros; eauto.
  constructor; eauto.
  destruct a; simpl; auto.
  eapply Val.longofwords_lessdef; eauto.
Qed.

Lemma match_states_step lm ge s1 s2:
  invar s1 s2 ->
  forall t s1',
    Linear.step lm ge s1 t s1' ->
    exists s2',
      Linear.step lm ge s2 t s2' /\
      invar s1' s2'.
Proof.
  intros H t s1' H0.
  inversion H0; subst; inversion H; subst.
  * (* getstack *)
    esplit.
    split.
    econstructor; eauto.
    econstructor; eauto.
    apply lessdef_set; auto.
    apply lessdef_undef_regs.
    assumption.
  * (* setstack *)
    esplit.
    split.
    econstructor; eauto.
    econstructor; eauto.
    apply lessdef_set; auto.
    apply lessdef_undef_regs.
    assumption.
  * (* eval_operation *)
    exploit OpX.eval_operation_lessdef_strong; try eassumption.
    { eapply lessdef_list_reglist. eassumption. }
    destruct 1 as (v2 & OP2 & LESS2).
    esplit.
    split.
    econstructor; eauto.
    econstructor; eauto.
    apply lessdef_set; auto.
    apply lessdef_undef_regs; auto.
  * (* load *)
    exploit OpX.eval_addressing_lessdef_strong; try eassumption.
    { eapply lessdef_list_reglist. eassumption. }
    destruct 1 as (v2 & OP2 & LESS2).
    exploit Mem.loadv_extends; try eassumption.
    destruct 1 as (v3 & LOAD3 & LESS3).
    esplit.
    split.
    econstructor; eauto.
    econstructor; eauto.
    apply lessdef_set; auto.
  * (* store *)
    exploit OpX.eval_addressing_lessdef_strong; try eassumption.
    { eapply lessdef_list_reglist. eassumption. }
    destruct 1 as (v2 & OP2 & LESS2).
    exploit Mem.storev_extends; try eassumption.
    { eapply rs_lessdef. }
    destruct 1 as (m2' & STORE2 & EXT2).
    esplit.
    split.
    econstructor; eauto.
    econstructor; eauto.
    apply lessdef_undef_regs; auto.
  * (* call *)
    esplit.
    split.
    econstructor; eauto.
    { eapply find_function_lessdef; eauto. }
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
  * (* tailcall *)
    inversion sp_lessdef; subst.
    exploit Mem.free_parallel_extends; try eassumption.
    destruct 1 as (m2' & FREE2 & EXT2).
    esplit.
    split.
    econstructor; eauto.
    eapply find_function_lessdef.
    instantiate (1 := LTL.return_regs (Linear.parent_locset lm s) rs).
    eapply return_regs_lessdef.
    eapply parent_locset_lessdef.
    eassumption.
    eassumption.
    assumption.
    econstructor; eauto.
    apply return_regs_lessdef.
    apply parent_locset_lessdef.
    assumption.
    assumption.
  * (* builtin *)
    exploit eval_builtin_args_lessdef''; try eassumption.
    intros (vl2 & EBA & LLIST).
    exploit external_call_mem_extends; eauto.
    intros (vres2' & m2' & CALL' & LESSDEF' & EXT' & _).
    esplit.
    split.
  - econstructor; eauto.
  - econstructor; eauto.
    intros; apply lessdef_setres; auto.
    apply lessdef_undef_regs; auto.
    * (* label *)
      esplit.
      split.
      econstructor; eauto.
      econstructor; eauto.
    * (* goto *)
      esplit.
      split.
      econstructor; eauto.
      econstructor; eauto.
    * (* cond true *)
      exploit Op.eval_condition_lessdef; try eassumption.
      apply lessdef_list_reglist. eassumption.
      intro OP2.
      esplit.
      split.
      econstructor; eauto.
      econstructor; eauto.
    * (* cond false *)
      exploit Op.eval_condition_lessdef; try eassumption.
      apply lessdef_list_reglist. eassumption.
      intro OP2.
      esplit.
      split.
      eapply Linear.exec_Lcond_false; eauto.
      econstructor; eauto.
    * (* jumptable *)
      esplit.
      split.
      econstructor; eauto.
      specialize (rs_lessdef (R arg)). inversion rs_lessdef; congruence.
      econstructor; eauto.
      apply lessdef_undef_regs. auto.
    * (* return *)
      inversion sp_lessdef; subst.
      exploit Mem.free_parallel_extends; try eassumption.
      destruct 1 as (m2' & FREE' & EXT').
      esplit.
      split.
      econstructor; eauto.
      econstructor; eauto.
      apply return_regs_lessdef; auto.
      apply parent_locset_lessdef; auto.
    * (* call internal *)
      exploit Mem.alloc_extends; try eassumption; try reflexivity.
      destruct 1 as (m2' & ALLOC' & EXT').
      esplit.
      split.
      econstructor; eauto.
      econstructor; eauto.
      apply lessdef_undef_regs. 
      apply lessdef_call_regs.
      assumption.
    * (* call external *)
      exploit external_call_mem_extends; try eassumption.
      eapply lessdef_map'. eassumption.
      destruct 1 as (vres' & m2' & CALL' & LESSDEF' & EXT' & _).
      esplit.
      split.
      econstructor; eauto.
      econstructor; try eassumption.
      intros.
      apply lessdef_setpair; auto.
    * (* returnstate *)
      inversion stack_inv ; subst.
      inversion H3; subst.
      esplit.
      split.
      econstructor; eauto.
      econstructor; eauto.
Qed.


(* If LinearX is safe on the memory without arguments, then LinearX forward-simulates to Linear2X. *)

Variables
  (lm: Linear.locset)
  (p: Linear.program) (i: ident) (sg: signature) (args: list val) (mh ml: mem)
  (init_sp: val)
  (Hmh: Mem.extends mh ml).
(* free_extcall_args init_sp ml (regs_of_rpairs (Conventions1.loc_arguments sg)) = Some mh) *)
(* . *)

Record match_states (s1: Linear.state) (s2: Linear2.state): Prop :=
  {
    match_lower:
      state_lower s2 = s1;
    match_ge:
      state_ge s2 = Genv.globalenv p;
    match_init_ls:
      state_init_ls s2 = lm;
    match_higher_safe:
      BehaviorsX.strongly_safe_state (LinearX.semantics lm p i sg args mh) (state_higher s2)
  }.  
  

Theorem per_module_linear_to_linear2
        (SAFE: BehaviorsX.strongly_safe (LinearX.semantics lm p i sg args mh))
:
  forward_simulation
    (LinearX.semantics lm p i sg args ml)
    (semantics lm p i sg args mh ml)
.
Proof.
  apply forward_simulation_step with (match_states := match_states); auto.
  * (* initial state *)
    intros s1 H.
    inversion H.
    eexists (State (Linear.Callstate nil f lm mh) s1 (Genv.globalenv p) lm _).
    split.
    { subst; econstructor; eauto.
      econstructor; eauto.
    }
    econstructor; eauto.
    apply BehaviorsX.strongly_safe_state_beh_elim.
    intro ABSURD.
    destruct ABSURD as (t & ABSURD).
    eapply SAFE.
    exists t.
    eleft; eauto.
    econstructor; eauto.

  * (* final state. Due to the condition on callee-save registers, we
       need to use safety here: the corresponding higher state is a
       Returnstate with empty stack, so it is Nostep, so it is
       necessarily final. *)
    inversion 1.
    subst s1.
    intros H0.
    destruct (match_higher_safe0 _ _ (star_refl _ _ _)).
    {
      destruct H1 as (resh & FINALh).
      econstructor; eauto.
    }
    exfalso.
    destruct H1 as (? & ? & ABSURD).
    inversion H0.
    subst v r. 
    generalize (Linear2.state_invariant s2).
    inversion 1; try congruence.
    assert (stackl = nil) by congruence.
    subst stackl.
    inversion stack_inv.
    subst stackh.
    rewrite <- H4 in ABSURD.
    inversion ABSURD.

  * (* step *)    
    intros s1 t s1' H s2 H0.
    inversion H0.
    subst s1.
    destruct (match_higher_safe0 _ _ (star_refl _ _ _)).
    {
      exfalso.
      destruct H1 as (v1 & ABSURD).
      inversion ABSURD.
      subst v v1 .
      generalize (Linear2.state_invariant s2).
      inversion 1; try congruence.
      assert (stackh = nil) by congruence.
      subst stackh.
      inversion stack_inv.
      subst stackl.
      rewrite <- H5 in H.
      inversion H.
    }
    destruct H1 as (t2 & s0 & STEPh).
    simpl in STEPh.
    exploit match_states_step; try eassumption.
    eapply Linear2.state_invariant.
    destruct 1 as (s2' & STEP2' & _).
    exploit (SmallstepX.sd_determ _ (LinearX.semantics_weak_determ lm p i sg args ml)).
    eexact STEP2'.
    eexact H.
    destruct 1 as (TRACES & _).
    clear s2' STEP2'.
    simpl in TRACES.
    exploit (Smallstep.sr_receptive (LinearX.semantics_receptive lm p i sg args mh)).
    eassumption.
    simpl. eassumption.
    destruct 1 as (s3 & STEP3).
    clear t2 s0 STEPh TRACES.
    simpl in STEP3.
    exploit match_states_step; try eassumption.
    eapply Linear2.state_invariant.
    destruct 1 as (s2' & STEP2' & INVAR').
    exploit (SmallstepX.sd_determ _ (LinearX.semantics_weak_determ lm p i sg args ml)).
    eexact H.
    eexact STEP2'.
    destruct 1 as (_ & EQ).
    specialize (EQ (eq_refl _)).
    subst s1'.
    exists (State _ _ (Genv.globalenv p) lm INVAR').
    split.
    {
      constructor; simpl; auto; congruence.
    }
    constructor; auto.
    red. intros.
    eapply match_higher_safe0.
    eapply star_step.
    eassumption.
    eassumption.
    reflexivity.

(* invariant for initial state *)
Grab Existential Variables.
    inversion H; subst.
    constructor.
    reflexivity.
    congruence.
    auto.
    auto.
    (* eapply free_extcall_args_extends; eauto. *)

Qed.

End WITHCONFIG.
