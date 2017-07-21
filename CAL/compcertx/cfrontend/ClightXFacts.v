Require compcert.cfrontend.Clight.
Require EventsX.

Import Coqlib.
Import AST.
Import Maps.
Import Memory.
Import Globalenvs.
Import Events.
Import Smallstep.
Export Clight.

(** Missing lemma from Smallstep *)

Lemma star_plus:
  forall {genv state: Type}
         {step: genv -> state -> trace -> state -> Prop}
         ge s t s',
    star step ge s t s' ->
    s <> s' ->
    plus step ge s t s'.
Proof.
  inversion 1; subst.
   destruct 1; reflexivity.
  intros. econstructor; eauto.
Qed.

(** Missing lemma from Globalenvs. *)

Module Genv.
Export Globalenvs.Genv.
Theorem find_funct_ptr_strong_inversion_aux:
  forall {F V} l2,
    list_norepet (map fst l2) ->
    forall (ge: _ F V),
      (forall b f,
         find_funct_ptr ge b = Some f ->
         exists id, find_symbol ge id = Some b /\ ~ In id (map fst l2)) ->
      forall b f,
        find_funct_ptr (add_globals ge l2) b = Some f ->
        exists id, find_symbol (add_globals ge l2) id = Some b.
Proof.
  induction l2; simpl; inversion 1; subst.
  { intros. apply H0 in H1. destruct H1 as [? [? ?]]; eauto. }
  intros.
  apply IHl2 in H1; eauto.
  unfold add_global, find_funct_ptr, find_symbol; simpl.
  destruct a; simpl in *.
  destruct o; simpl.
  * destruct g; simpl.
    intros ? ?.
    unfold find_def; simpl.
    rewrite PTree.gsspec.
    destruct (peq b0 (genv_next ge)).
    + inversion 1; subst.
      esplit. split.
      eapply PTree.gss.
      assumption.
    + intros. apply H0 in H4.
      destruct H4 as [? [? ?]].
      exists x.
      split.
      rewrite PTree.gso. assumption. intuition congruence.
      tauto.
    + unfold find_def; simpl. intros. rewrite PTree.gso in H4. apply H0 in H4.
      destruct H4 as [? [? ?]].
      exists x.
      split.
      rewrite PTree.gso. assumption. intuition congruence.
      tauto. intro; subst. rewrite PTree.gss in H4. congruence.
  * intros. apply H0 in H4.
    destruct H4 as [? [? ?]].
    exists x.
    split.
    rewrite PTree.gso. assumption. intuition congruence.
    tauto.
Qed.

Theorem find_funct_ptr_strong_inversion:
  forall {F V} (p: _ F V),
  list_norepet (prog_defs_names p) ->
  forall b f,
    find_funct_ptr (globalenv p) b = Some f ->
    exists id, find_symbol (globalenv p) id = Some b.
Proof.
  intros.
  eapply find_funct_ptr_strong_inversion_aux.
  * assumption.
  * unfold find_funct_ptr, find_def; simpl. intros.
    rewrite PTree.gempty in H1. discriminate.
  * eassumption.
Qed.

End Genv.

(** Framing over a control stack *)

Function frame_cont (kframe: cont) (k: cont) :=
  match k with
    | Kstop => kframe
    | Kseq s k => Kseq s (frame_cont kframe k)
    | Kloop1 s1 s2 k => Kloop1 s1 s2 (frame_cont kframe k)
    | Kloop2 s1 s2 k => Kloop2 s1 s2 (frame_cont kframe k)
    | Kswitch k => Kswitch (frame_cont kframe k)
    | Kcall oi f e t k => Kcall oi f e t (frame_cont kframe k)
  end.

Lemma call_cont_is_call_cont:
  forall kframe, is_call_cont kframe ->
                 call_cont kframe = kframe.
Proof.
  induction kframe; eauto; inversion 1; subst; eauto.
Qed.

Lemma call_cont_frame:
  forall kframe, is_call_cont kframe ->
                 forall k, call_cont (frame_cont kframe k) = frame_cont kframe (call_cont k).
Proof.
  induction k; simpl; eauto using call_cont_is_call_cont.
Qed.

Lemma is_call_cont_frame:
  forall kframe, is_call_cont kframe ->
                 forall k, is_call_cont k ->
                           is_call_cont (frame_cont kframe k).
Proof.
  induction k; simpl; eauto.
Qed.

Section WITHKFRAME.
  Variables (kframe: cont).

Lemma find_label_frame:
  forall s l k,
    (forall s' k',
       find_label l s k = Some (s', k') ->
       find_label l s (frame_cont kframe k) = Some (s', frame_cont kframe k'))
    /\
    (find_label l s k = None ->
     find_label l s (frame_cont kframe k) = None)
with find_label_ls_frame:
  forall ls l k,
    (forall s' k',
       find_label_ls l ls k = Some (s', k') ->
       find_label_ls l ls (frame_cont kframe k) = Some (s', frame_cont kframe k'))
    /\ (
      find_label_ls l ls k = None ->
      find_label_ls l ls (frame_cont kframe k) = None
    ).
Proof with (try discriminate;
            try (
                try (apply find_label_frame in Heqo;
                     simpl in Heqo;
                     rewrite Heqo);
                try (apply find_label_ls_frame in Heqo;
                     simpl in Heqo;
                     rewrite Heqo);
                try reflexivity;
                try apply find_label_frame;
                try apply find_label_ls_frame
              )
           ).
  {
    destruct s; simpl; split; try discriminate; eauto...
    * destruct (find_label l s1 (Kseq s2 k)) eqn:Heqo...
      inversion 1; subst...
    * destruct (find_label l s1 (Kseq s2 k)) eqn:Heqo...
    * destruct (find_label l s1 k) eqn:Heqo...
      inversion 1; subst...
    * destruct (find_label l s1 k) eqn:Heqo...
    * destruct (find_label l s1 (Kloop1 s1 s2 k)) eqn:Heqo...
      inversion 1; subst...
    * destruct (find_label l s1 (Kloop1 s1 s2 k)) eqn:Heqo...
    * destruct (AST.ident_eq l0 l); try congruence...
    * destruct (AST.ident_eq l0 l); try congruence...
  }
  destruct ls; simpl; split; try discriminate; eauto.
  * destruct (find_label l s (Kseq (seq_of_labeled_statement ls) k)) eqn:Heqo...
    inversion 1; subst...
  * destruct (find_label l s (Kseq (seq_of_labeled_statement ls) k)) eqn:Heqo...
Qed.

End WITHKFRAME.

Section WITHCONFIGOPS.

Context `{external_calls_prf:  EnableBuiltins}.

Function state_cont (s: state) :=
  match s with
    | State _ _ k _ _ _ => k
    | Callstate _ _ k _ => k
    | Returnstate _ k _ => k
  end.

Function frame_state_cont  (kframe: cont) (s: state) :=
  match s with
    | State f s k e t m => State f s (frame_cont kframe k) e t m
    | Callstate fd args k m => Callstate fd args (frame_cont kframe k) m
    | Returnstate v k m => Returnstate v (frame_cont kframe k) m
  end.

Lemma frame_state_cont_frame_cont:
  forall kframe s,
    state_cont (frame_state_cont kframe s) = frame_cont kframe (state_cont s).
Proof.
  destruct s; reflexivity.
Qed.

Theorem step_frame_cont:
  forall kframe,
    is_call_cont kframe ->
  forall ge fe s t s',
    step ge fe s t s' ->
    step ge fe (frame_state_cont kframe s) t (frame_state_cont kframe s').
Proof.
  inversion 2; subst; simpl; try rewrite <- call_cont_frame; eauto; try (econstructor; eauto using is_call_cont_frame; fail).
  (* goto *)
  econstructor. rewrite call_cont_frame; eauto. eapply find_label_frame; eauto.
Qed.

Corollary star2_frame_cont:
  forall kframe,
    is_call_cont kframe ->
    forall ge s t s',
      star step2 ge s t s' ->
      star step2 ge (frame_state_cont kframe s) t (frame_state_cont kframe s').
Proof.
  induction 2; econstructor; eauto.
  eapply step_frame_cont; eauto.
Qed.

End WITHCONFIGOPS.

Section WITHMEMORYMODEL.

Context mem `{memory_model_prf: Mem.MemoryModel mem}
        `{external_calls_ops: !ExternalCallsOps mem}
        `{symbols_inject_instance: SymbolsInject}
        `{enable_builtins_instance: !EnableBuiltins mem}.

(** Now, we assume that we *do not* have [ExternalCalls], and that
[extcall_properties] only hold for builtin functions and inline
assembly. *)

Hypothesis disable_external_as_builtin:
  cc_enable_external_as_builtin = false.

Hypothesis builtin_functions_properties:
  forall name sg,
    extcall_properties (builtin_functions_sem name sg) sg.

Hypothesis runtime_functions_properties:
  forall name sg,
    extcall_properties (runtime_functions_sem name sg) sg.

Hypothesis inline_functions_properties:
  forall text sg,
    extcall_properties (inline_assembly_sem text sg) sg.

Lemma external_call_spec:
  forall ef,
    builtin_enabled ef ->
    extcall_properties (external_call ef) (ef_sig ef).
Proof.
  destruct ef; simpl; intros.
  * rewrite disable_external_as_builtin in H. contradiction.
  * auto.
  * auto.
  * apply volatile_load_ok.
  * apply volatile_store_ok.
  * apply extcall_malloc_ok.
  * apply extcall_free_ok.
  * apply extcall_memcpy_ok.
  * apply extcall_annot_ok.
  * apply extcall_annot_val_ok.
  * auto.
  * apply extcall_debug_ok.
Qed.

Definition builtin_is_enabled (ef: external_function) :
  {builtin_enabled ef} + {~ builtin_enabled ef}.
Proof.
  unfold builtin_enabled.
  destruct ef; try (left; exact I).
  rewrite disable_external_as_builtin.
  right. clear. tauto.
Defined.

(** We first prove that [valid_block] is preserved by the semantics of a Clight module,
    provided its external functions also do. *)

Section WITHVALIDBLOCK.

  Hypothesis external_functions_sem_valid_block:
    forall i sg,
    forall (ge: Senv.t) vargs m1 t vres m2 b,
      external_functions_sem i sg ge vargs m1 t vres m2 ->
      Mem.valid_block m1 b -> Mem.valid_block m2 b.

  Lemma external_call_valid_block:
    forall ef,
    forall (ge: Senv.t) vargs m1 t vres m2 b,
      external_call ef ge vargs m1 t vres m2 ->
      Mem.valid_block m1 b -> Mem.valid_block m2 b.
  Proof.
    intro.
    destruct (builtin_is_enabled ef).
    * (* enabled *)
      eapply ec_valid_block.
      eapply external_call_spec.
      assumption.
    * (* EF_external *)
      destruct ef; simpl in n; try (destruct n; clear; tauto).
      apply external_functions_sem_valid_block.
  Qed.

  Function state_mem (s: state): mem :=
    match s with
    | State _ _ _ _ _ m => m
    | Callstate _ _ _ m => m
    | Returnstate _ _ m => m
    end.

  Lemma assign_loc_valid_block
    :
      forall ge ty m loc ofs v m',
        assign_loc ge ty m loc ofs v m' ->
        forall b,
          Mem.valid_block m b ->
          Mem.valid_block m' b.
  Proof.
    inversion 1; subst; eauto using Mem.storebytes_valid_block_1, Mem.store_valid_block_1.
  Qed.

  Lemma valid_block_freelist:
    forall l m m',
      Mem.free_list m l = Some m' ->
      forall b,
        Mem.valid_block m b ->
        Mem.valid_block m' b.
  Proof.
    induction l; simpl.
    congruence.
    destruct a. destruct p. intro.
    destruct (Mem.free m b z0 z) eqn:?; try discriminate.
    eauto using Mem.valid_block_free_1.
  Qed.

  Lemma alloc_variables_valid_block:
    forall ge e m lv e' m',
      alloc_variables ge e m lv e' m' ->
      forall b,
        Mem.valid_block m b ->
        Mem.valid_block m' b.
  Proof.
    induction 1; intros; eauto using Mem.valid_block_alloc.
  Qed.

  Theorem step2_valid_block
    :
      forall ge s t s',
        step2 ge s t s' ->
        forall b,
          Mem.valid_block (state_mem s) b ->
          Mem.valid_block (state_mem s') b.
  Proof.
    inversion 1; subst; simpl; eauto using assign_loc_valid_block, external_call_valid_block, valid_block_freelist.
    inv H0; eauto using alloc_variables_valid_block.
  Qed.

  Corollary step2_nextblock
    :
      forall ge s t s',
        step2 ge s t s' ->
        Ple (Mem.nextblock (state_mem s)) (Mem.nextblock (state_mem s')).
  Proof.
    intros.
    generalize (step2_valid_block _ _ _ _ H).
    unfold Mem.valid_block.
    generalize (Mem.nextblock (state_mem s)). intro low.
    generalize (Mem.nextblock (state_mem s')). intro high.
    intro H0.
    destruct (Psucc_pred low).
    + subst. xomega.
    + assert (H2: Plt (Pos.pred low) low) by xomega. apply H0 in H2. xomega.
  Qed.

End WITHVALIDBLOCK.

End WITHMEMORYMODEL.

Section WITHMEMORYMODELOPS.

Context `{memory_model_ops: Mem.MemoryModelOps} .

Function is_external_state (s: state): bool :=
  match s with
    | Callstate (Ctypes.External ef targs tres tcc) args k m => true
    | _ => false
  end.

End WITHMEMORYMODELOPS.

(** Now, we are going to replace the semantics of external functions
in a global environment [ge1] with the execution of some Clight code
in another global environment [ge2], and we are going to prove that
code executing in [ge1] can execute in [ge2] as well. *)

Section WITH2CONFIGOPS.

Context {mem} `{compiler_config_ops1: ExternalCalls mem}
        `{external_calls_ops2: !ExternalCallsOps mem}
        `{compiler_config_ops2: !EnableBuiltins mem}.

Variables (ge1 ge2: genv)
          (senv_preserved: Senv.equiv ge1 ge2)
          (cenv_preserved: forall i, (genv_cenv ge2) ! i = (genv_cenv ge1) ! i).

Ltac destr :=
  match goal with
    |- context [match ?A with _ => _ end] => destruct A eqn:?; simpl in *
  | |- context [if ?A then _ else _] => destruct A eqn:?; simpl in *
  end.
Ltac destr_in H :=
  match type of H with
  | context [match ?A with _ => _ end] => destruct A eqn:?; simpl in *
  | context [if ?A then _ else _] => destruct A eqn:?; simpl in *
  end.

Ltac auto_inv :=
  repeat match goal with
           H : Some _ = Some _ |- _ => inv H
         | H : None = Some _ |- _ => inv H
         | H : Some _ = None |- _ => inv H
         end.

Lemma sizeof_symbols_preserved:
  forall t, Ctypes.sizeof ge2 t = Ctypes.sizeof ge1 t.
Proof.
  induction t; simpl; intros; try destr; auto. congruence.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
Qed.

Lemma alignof_symbols_preserved:
  forall t, Ctypes.alignof ge2 t = Ctypes.alignof ge1 t.
Proof.
  induction t; simpl; intros; try destr; auto. congruence.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
Qed.


Lemma field_offset_symbols_preserved:
  forall t m, Ctypes.field_offset ge2 t m = Ctypes.field_offset ge1 t m.
Proof.
  unfold Ctypes.field_offset.
  intros t m. generalize 0.
  revert m t; induction m; simpl; intros; eauto.
  destruct a. destr. rewrite alignof_symbols_preserved. eauto.
  rewrite alignof_symbols_preserved, sizeof_symbols_preserved; eauto.
Qed.

Lemma cop_binary_operation_symbols_preserved:
  forall op v1 a1 v2 a2 m v,
    Cop.sem_binary_operation ge1 op v1 a1 v2 a2 m = Some v ->
    Cop.sem_binary_operation ge2 op v1 a1 v2 a2 m = Some v.
Proof.
  Ltac t := repeat destr; subst; auto_inv;
            repeat rewrite sizeof_symbols_preserved in *; try intuition congruence.
  destruct op; simpl; intros; auto.
  unfold Cop.sem_add in *;
  unfold Cop.sem_add_ptr_long in *;
  unfold Cop.sem_add_ptr_int in *.
  repeat destr; subst; auto_inv;
    repeat rewrite sizeof_symbols_preserved in *; try intuition congruence.
  unfold Cop.sem_sub in *;
  repeat destr; subst; auto_inv;
    repeat rewrite sizeof_symbols_preserved in *; try intuition congruence.
  destr_in H. eauto. discriminate.
  destr_in H; eauto. discriminate.
Qed.

Lemma eval_expr_lvalue_symbols_preserved:
  forall ve le m,
  (forall e v,
    eval_expr ge1 ve le m e v ->
    eval_expr ge2 ve le m e v)
  /\
  (forall e b i,
    eval_lvalue ge1 ve le m e b i ->
    eval_lvalue ge2 ve le m e b i).
Proof.
  intros.
  apply eval_expr_lvalue_ind; try (econstructor; eauto; fail).
  - intros. econstructor; eauto. eapply cop_binary_operation_symbols_preserved; eauto.
  - intros. rewrite <- sizeof_symbols_preserved. eapply eval_Esizeof.
  - intros. rewrite <- alignof_symbols_preserved. eapply eval_Ealignof.
  - (** Evar global *)
    intros until 1. destruct senv_preserved as (A&B&C&D).
    unfold Senv.find_symbol in B. unfold Genv.to_senv in *. simpl in *.
    rewrite <- B. intros.
    eapply eval_Evar_global; eauto.
  - intros.
    econstructor; eauto. rewrite <- H2. auto.
    rewrite field_offset_symbols_preserved; auto.
  - intros.
    econstructor; eauto. rewrite <- H2; eauto.
Qed.

Lemma eval_expr_symbols_preserved:
  forall ve le m,
  (forall e v,
    eval_expr ge1 ve le m e v ->
    eval_expr ge2 ve le m e v).
Proof.
  intros until le. apply eval_expr_lvalue_symbols_preserved.
Qed.

Lemma eval_lvalue_symbols_preserved:
  forall ve le m,
  (forall e b i,
    eval_lvalue ge1 ve le m e b i ->
    eval_lvalue ge2 ve le m e b i).
Proof.
  intros until le. apply eval_expr_lvalue_symbols_preserved.
Qed.

Lemma eval_exprlist_symbols_preserved:
  forall ve le m al tyargs vargs,
    eval_exprlist ge1 ve le m al tyargs vargs ->
    eval_exprlist ge2 ve le m al tyargs vargs.
Proof.
  induction 1; econstructor; eauto using eval_expr_symbols_preserved.
Qed.

Hypothesis disable_external_as_builtin1:
  cc_enable_external_as_builtin (EnableBuiltins := enable_builtins_instance) = false.

Lemma builtin_enabled_preserved:
  forall ef,
    builtin_enabled (enable_builtin_instance := enable_builtins_instance) ef ->
    builtin_enabled (enable_builtin_instance := compiler_config_ops2) ef.
Proof.
  destruct ef; simpl; try tauto.
  rewrite disable_external_as_builtin1. tauto.
Qed.

Hypothesis builtin_functions_properties1:
  forall name sg,
    extcall_properties (builtin_functions_sem (ExternalCallsOps := external_calls_ops) name sg) sg.

Hypothesis runtime_functions_properties1:
  forall name sg,
    extcall_properties (runtime_functions_sem (ExternalCallsOps := external_calls_ops) name sg) sg.

Hypothesis inline_functions_properties1:
  forall text sg,
    extcall_properties (inline_assembly_sem (ExternalCallsOps := external_calls_ops) text sg)
                       sg.

Hypothesis internal_calls_preserved:
  forall b f,
    Genv.find_funct_ptr ge1 b = Some (Ctypes.Internal f) ->
    Genv.find_funct_ptr ge2 b = Some (Ctypes.Internal f).

Hypothesis builtin_enabled_sem_preserved:
  forall ef,
    builtin_enabled (enable_builtin_instance := enable_builtins_instance) ef ->
    forall vargs m1 t vres m2,
      external_call (external_calls_ops := external_calls_ops) ef ge1 vargs m1 t vres m2 ->
      external_call (external_calls_ops := external_calls_ops2) ef ge2 vargs m1 t vres m2.

Lemma alignof_blockcopy_symbols_preserved:
  forall t, Ctypes.alignof_blockcopy ge2 t = Ctypes.alignof_blockcopy ge1 t.
Proof.
  induction t; simpl; intros; try destr; auto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
  erewrite <- cenv_preserved; eauto. rewrite Heqo; eauto.
Qed.

Lemma assign_loc_symbols_preserved:
  forall ty m b o v m',
    assign_loc ge1 ty m b o v m' ->
    assign_loc ge2 ty m b o v m'.
Proof.
  intros ty m b o v m' A; inv A.
  - eapply assign_loc_value; eauto.
  - eapply assign_loc_copy; eauto.
    all: rewrite sizeof_symbols_preserved;
      try rewrite alignof_blockcopy_symbols_preserved; eauto.
Qed.

Lemma blocks_of_env_symbols_preserved e:
  blocks_of_env ge2 e = blocks_of_env ge1 e.
Proof.
  unfold blocks_of_env.
  apply map_ext.
  unfold block_of_binding.
  intros.
  destruct a. destruct p. f_equal.
  apply sizeof_symbols_preserved.
Qed.


Lemma alloc_variables_symbols_preserved:
  forall e m l e' m',
    alloc_variables ge1 e m l e' m' ->
    alloc_variables ge2 e m l e' m'.
Proof.
  induction 1; simpl; intros; eauto.
  constructor.
  econstructor; eauto. rewrite sizeof_symbols_preserved; auto.
Qed.

Theorem step2_not_external_symbols_preserved:
  forall
    s
    (NOT_EXTERNAL: is_external_state s = false)
    t s'
    (STEP: step2 (enable_builtins_instance := enable_builtins_instance) ge1 s t s')
    (NOT_EXTERNAL': is_external_state s' = false)
  ,
    step2 (enable_builtins_instance := compiler_config_ops2) ge2 s t s'.
Proof.
  intros.
  inversion STEP; subst; simpl in *; try discriminate;
    try (econstructor;
         try rewrite  blocks_of_env_symbols_preserved;
       eauto using eval_expr_symbols_preserved,
       eval_lvalue_symbols_preserved,
       eval_exprlist_symbols_preserved,
       assign_loc_symbols_preserved
      ).
  * destruct vf; try discriminate.
    unfold Genv.find_funct.
    simpl in H2. destr. 
    destruct fd; try discriminate.
    eauto. inv H2.
  * apply builtin_enabled_preserved. assumption.
  * inv H. constructor; auto.
    apply alloc_variables_symbols_preserved; auto.
Qed.

Hypothesis external_functions_sem1_valid_block:
  forall i sg,
  forall (ge: Senv.t) vargs m1 t vres m2 b,
    external_functions_sem (ExternalCallsOps := external_calls_ops) i sg ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b.

Hypothesis external_calls_replaced_syntax:
  forall b ef targs tres tcc,
    Genv.find_funct_ptr ge1 b = Some (Ctypes.External ef targs tres tcc) ->
    exists f, Genv.find_funct_ptr ge2 b = Some f /\
              type_of_fundef f = Ctypes.Tfunction targs tres tcc.

Variable m_init: mem.

Hypothesis external_calls_replaced_semantics:
  forall b ef targs tres tcc,
    Genv.find_funct_ptr ge1 b = Some (Ctypes.External ef targs tres tcc) ->
      forall args m t res m',
        external_call (external_calls_ops := external_calls_ops) ef ge1 args m t res m' ->
        forall f, Genv.find_funct_ptr ge2 b = Some f ->
                  star (step2
                          (enable_builtins_instance := compiler_config_ops2)
                       )
                       ge2 (Callstate f args Kstop m) t (Returnstate res Kstop m').

Hypothesis disable_external_as_builtin2:
  cc_enable_external_as_builtin (EnableBuiltins := compiler_config_ops2) = false.

Hypothesis builtin_functions_properties2:
  forall name sg,
    extcall_properties (builtin_functions_sem (ExternalCallsOps := external_calls_ops2) name sg) sg.

Hypothesis runtime_functions_properties2:
  forall name sg,
    extcall_properties (runtime_functions_sem (ExternalCallsOps := external_calls_ops2) name sg) sg.


Hypothesis inline_functions_properties2:
  forall text sg,
    extcall_properties (inline_assembly_sem (ExternalCallsOps := external_calls_ops2) text sg) sg.

Inductive match_states: state -> state -> Prop :=
  | match_states_not_external
      s
      (Hs_not_external: is_external_state s = false)
      (Hnextblock: Ple (Mem.nextblock m_init) (Mem.nextblock (state_mem mem s)))
       :
      match_states s s
  | match_states_callstate_external
      b ef targs tres tcc
      (Hge1: Genv.find_funct_ptr ge1 b = Some (Ctypes.External ef targs tres tcc))
      f
      (Hge2: Genv.find_funct_ptr ge2 b = Some f)
      k
      (IS_CALL_CONT: is_call_cont k)
      m
      (Hnextblock: Ple (Mem.nextblock m_init) (Mem.nextblock m))
      args
    :
      match_states (Callstate (Ctypes.External ef targs tres tcc) args k m)
                   (Callstate f args k m)
.

Theorem step2_replace_external:
  forall
    s1 t s1',
    step2 (enable_builtins_instance := enable_builtins_instance) ge1 s1 t s1' ->
    forall s2,
      match_states s1 s2 ->
      exists s2',
        plus (step2 (enable_builtins_instance := compiler_config_ops2)) ge2 s2 t s2' /\
        match_states s1' s2'.
Proof.
  inversion 2; subst.
  { (* not external *)
    case_eq (is_external_state s1').
    * (* destination external *)
      intro EXT. functional inversion EXT; subst.
      inversion H; subst.
      generalize H10. unfold Genv.find_funct. destruct vf; try discriminate.
      destr.
      intros.
      generalize H1.
      intro F.
      apply external_calls_replaced_syntax in F.
      destruct F as [? [? ?]].
      simpl in H11. inv H11.
      esplit. split.
      + apply plus_one. econstructor.
        - eassumption.
        - eapply eval_expr_symbols_preserved; eauto.
        - eapply eval_exprlist_symbols_preserved; eauto.
        - unfold Genv.find_funct. rewrite Heqs. eassumption.
        - assumption.
      + econstructor.
        - eassumption.
        - assumption.
        - simpl. auto.
        - assumption.
      + discriminate.
    * (* destination not external *)
      intro.
      esplit. split.
      + eapply plus_one.
        eapply step2_not_external_symbols_preserved.
        - assumption.
        - eassumption.
        - assumption.
      + constructor.
        - assumption.
        - eapply Ple_trans. eassumption.
          eapply step2_nextblock in H; eauto.
  }
  (* external *)
  inversion H; subst.
  eapply external_calls_replaced_semantics in H10; eauto.
  eapply star2_frame_cont in H10; eauto.
  simpl in H10.
  apply star_plus in H10; try congruence.
  esplit. split.
  eassumption.
  constructor. reflexivity.
  eapply Ple_trans. eassumption.
  eapply step2_nextblock in H; eauto.
Qed.

End WITH2CONFIGOPS.

(** Now we instantiate the theorem above with our new
[ExternalCallsOpsX] class (fixing the CompCert builtins and inline assembly.

This is to know which properties we really need on external functions
of each side. *)

Require CompCertBuiltins.

Section WITHCOMPCERTBUILTINS.

(* Context `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet}. *)

Context {mem} `{memory_model_prf: Mem.MemoryModel mem}.

Context `{external_calls_ops_x_1: !CompCertBuiltins.ExternalCallsOpsX mem}
        `{external_calls_ops_x_2: !CompCertBuiltins.ExternalCallsOpsX mem}.

Context `{SymbolsInject}.

Let external_calls_ops_1 := CompCertBuiltins.external_calls_ops_x_to_external_calls_ops _
                              (external_calls_ops_x := external_calls_ops_x_1).

Let external_calls_ops_2 := CompCertBuiltins.external_calls_ops_x_to_external_calls_ops _
                              (external_calls_ops_x := external_calls_ops_x_2).


Let compiler_config_ops_1 : EnableBuiltins _ (memory_model_ops :=memory_model_ops)
  (H:= external_calls_ops_1) :=
  {|
    cc_enable_external_as_builtin := false
  |}.

Let compiler_config_ops_2 : EnableBuiltins _ (memory_model_ops :=memory_model_ops)
                                           (H:= external_calls_ops_2):=
  {|
    cc_enable_external_as_builtin := false
  |}.

Variables (ge1 ge2: genv)
          (senv_preserved: Senv.equiv ge1 ge2)
          (cenv_preserved: forall i, (genv_cenv ge2) ! i = (genv_cenv ge1) ! i).

Variable m_init: mem.

(** The following can now be proved, since the two sides use the same
external calls with the only exception of external functions, which
are not [builtin_enabled]. *)

Let builtin_enabled_sem_preserved:
  forall ef,
    builtin_enabled (enable_builtin_instance := compiler_config_ops_1) ef ->
    forall vargs m1 t vres m2,
      external_call (external_calls_ops := external_calls_ops_1) ef ge1 vargs m1 t vres m2 ->
      external_call (external_calls_ops := external_calls_ops_2) ef ge2 vargs m1 t vres m2.
Proof.
  intros.
  assert (
      external_call (external_calls_ops := external_calls_ops_1) ef ge2 vargs m1 t vres m2
    ).
  {
    eapply ec_symbols_preserved; eauto.
    eapply external_call_spec; eauto.
    reflexivity.
    apply CompCertBuiltins.builtin_functions_properties.
    apply CompCertBuiltins.runtime_functions_properties.
    constructor; simpl; intros; try contradiction.
  }
  destruct ef; try assumption.
  contradiction.
Qed.

Section EXTCALL_REPLACED.

Hypothesis external_functions_sem1_valid_block:
  forall i sg,
  forall (ge: Senv.t) vargs m1 t vres m2 b,
    Events.external_functions_sem (ExternalCallsOps := external_calls_ops_1) i sg ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b.

Hypothesis external_functions_sem2_writable_block_weak:
  forall m, Ple (Mem.nextblock m_init) (Mem.nextblock m) ->
  forall i sg,
  forall vargs m1 t vres m2,
    external_functions_sem (ExternalCallsOps := external_calls_ops_2) i sg ge2 vargs m1 t vres m2 ->
    external_functions_sem (ExternalCallsOps := external_calls_ops_2)  i sg ge2 vargs m1 t vres m2.

Hypothesis internal_calls_preserved:
forall b f,
  Genv.find_funct_ptr ge1 b = Some (Ctypes.Internal f) ->
              Genv.find_funct_ptr ge2 b = Some (Ctypes.Internal f).

Hypothesis external_calls_replaced_syntax:
  forall b ef targs tres tcc,
    Genv.find_funct_ptr ge1 b = Some (Ctypes.External ef targs tres tcc) ->
    exists f, Genv.find_funct_ptr ge2 b = Some f /\
              type_of_fundef f = Ctypes.Tfunction targs tres tcc.

Hypothesis external_calls_replaced_semantics:
  forall b ef targs tres tcc,
    Genv.find_funct_ptr ge1 b = Some (Ctypes.External ef targs tres tcc) ->
      forall args m t res m',
        external_call (external_calls_ops := external_calls_ops_1) ef ge1 args m t res m' ->
        forall f, Genv.find_funct_ptr ge2 b = Some f ->
                  star (step2 (enable_builtins_instance := compiler_config_ops_2)
                       )
                       ge2 (Callstate f args Kstop m) t (Returnstate res Kstop m').

Lemma step2_replace_external':
  forall
    s1 t s1',
    step2 (enable_builtins_instance := compiler_config_ops_1) ge1 s1 t s1' ->
    forall s2,
      match_states ge1 ge2 m_init s1 s2 ->
      exists s2',
        plus (step2 (enable_builtins_instance := compiler_config_ops_2)) ge2 s2 t s2' /\
        match_states ge1 ge2 m_init s1' s2'.
Proof.
  apply step2_replace_external; auto.
  * apply CompCertBuiltins.builtin_functions_properties.
  * apply CompCertBuiltins.runtime_functions_properties.
  * constructor; simpl; contradiction.
Qed.

Corollary star2_replace_external':
  forall
    s1 t s1',
    star (step2 (enable_builtins_instance := compiler_config_ops_1)) ge1 s1 t s1' ->
    forall s2,
      match_states ge1 ge2 m_init s1 s2 ->
      exists s2',
        star (step2 (enable_builtins_instance := compiler_config_ops_2)) ge2 s2 t s2' /\
        match_states ge1 ge2 m_init s1' s2'.
Proof.
  induction 1.
  * intros. esplit. split. eleft. assumption.
  * intros. exploit step2_replace_external'; eauto. destruct 1 as [? [PLUS MATCH]].
    apply plus_star in PLUS.
    apply IHstar in MATCH. destruct MATCH as [? [? ?]].
    esplit. split; eauto using star_trans.
Qed.

Theorem star2_replace_external:
  forall i b1 f1 t args res m'
         (SYMB1: Genv.find_symbol ge1 i = Some b1)
         (FUNCT1: Genv.find_funct_ptr ge1 b1 = Some f1)
         (STAR1: star (step2 (enable_builtins_instance := compiler_config_ops_1)) ge1 (Callstate f1 args Kstop m_init) t (Returnstate res Kstop m')),
  exists b2 f2,
    Genv.find_symbol ge2 i = Some b2 /\
    Genv.find_funct_ptr ge2 b2 = Some f2 /\
    star (step2 (enable_builtins_instance := compiler_config_ops_2)) ge2 (Callstate f2 args Kstop m_init) t (Returnstate res Kstop m').
Proof.
  intros.
  destruct senv_preserved as (A&B&C&D).
  unfold Senv.find_symbol in *. unfold Genv.to_senv in *; simpl in *. rewrite ! B.
  destruct f1.
  * (* internal *)
    exploit internal_calls_preserved; eauto.
    intro FUNCT2.
    exploit star2_replace_external'.
    { eassumption. }
    { eleft; eauto using Ple_refl. }
    destruct 1 as [? [? MATCH']].
    inv MATCH'.
    eauto.
  * (* external *)
    exploit external_calls_replaced_syntax; eauto.
    destruct 1 as [? [? ?]].
    exploit star2_replace_external'.
    { eassumption. }
    { eright; simpl; eauto using Ple_refl. }
    destruct 1 as [? [? MATCH']].
    inv MATCH'.
    eauto.
Qed.

End EXTCALL_REPLACED.

(** Now we study the case where the external functions of
the "higher" side are included in the external functions of the
"lower" side. (This is to prove so-called "monotonicity".) *)

Section EXTCALL_PRESERVED.

Hypothesis functions_preserved:
forall b f,
  Genv.find_funct_ptr ge1 b = Some f ->
              Genv.find_funct_ptr ge2 b = Some f.

Hypothesis external_calls_preserved:
  forall ef args m t res m',
    external_call (external_calls_ops := external_calls_ops_1) ef ge1 args m t res m' ->
    external_call (external_calls_ops := external_calls_ops_2) ef ge2 args m t res m'.

Lemma step2_mono:
  forall
    s t s'
    (STEP: step2 (enable_builtins_instance := compiler_config_ops_1) ge1 s t s'),
    step2 (enable_builtins_instance := compiler_config_ops_2) ge2 s t s'.
Proof.
  intros.
  case_eq (is_external_state s).
  { (* external *)
    intro EXT. functional inversion EXT; subst.
    inversion STEP; subst.
    econstructor; eauto.
  }
  (* not external *)
  intro INT.
  case_eq (is_external_state s').
  * (* destination external *)
    intro EXT. functional inversion EXT; subst.
    inversion STEP; subst.
    generalize H9. unfold Genv.find_funct. destruct vf; try discriminate.
    destruct (Integers.Ptrofs.eq_dec i Integers.Ptrofs.zero) eqn:Heqs; try discriminate.
    intros.
    apply functions_preserved in H0.
    econstructor; eauto using eval_expr_symbols_preserved, eval_exprlist_symbols_preserved.
    unfold Genv.find_funct. rewrite Heqs. assumption.
  * (* destination not external *)
    intro.
    eapply step2_not_external_symbols_preserved; eauto; try eassumption; try reflexivity; eauto; typeclasses eauto.
Qed.

Theorem star2_mono:
  forall
    s t s'
    (STAR: star (step2 (enable_builtins_instance := compiler_config_ops_1)) ge1 s t s'),
    star (step2 (enable_builtins_instance := compiler_config_ops_2)) ge2 s t s'.
Proof.
  induction 1; econstructor; eauto using step2_mono.
Qed.

End EXTCALL_PRESERVED.

End WITHCOMPCERTBUILTINS.
