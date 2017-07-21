Require Asm.
Require MemoryX.

Import Coqlib.
Import Integers.
Import Floats.
Import AST.
Import Values.
Import MemoryX.
Import Globalenvs.
Import Events.
Import Smallstep.
Import Locations.
Import Conventions.
Export Asm.
Require Import LocationsX.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

(** Execution of Asm functions with Asm-style arguments (long long 64-bit integers NOT allowed) *)

Inductive initial_state
          (lm: regset) (p: Asm.program) (i: ident)
          (sg: signature) (args: list val) (m: mem): state -> Prop :=
| initial_state'_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    (Hpc: lm PC = Vptr b Ptrofs.zero)
    (Hargs: extcall_arguments lm m sg args)    
  :
      initial_state lm p i sg args m (State lm m)
.

Definition get_pair (p: rpair preg) (rs:regset) : val :=
  match p with
    One l => rs l
  | Twolong l1 l2 => Val.longofwords (rs l1) (rs l2)
  end.

Inductive final_state (lm: regset) (sg: signature) : state -> (val * mem) -> Prop :=
  | final_state_intro:
      forall rs,
        eq (lm # RA) (rs # PC) ->
        eq (lm # RSP) (rs # RSP) ->
        forall v,
          v = get_pair (loc_external_result sg) rs ->
          (** We need the following condition to make sure that Asm takes at least one step. *)
          forall
            RA_VUNDEF: rs # RA = Vundef,
            (** Callee-save registers.
                We use Val.lessdef instead of eq because the Stacking and Asmgen passes do not exactly preserve their values. *)
          forall
            (CALLEE_SAVE: forall r,
                            ~ In r destroyed_at_call ->
                            Val.lessdef (lm (preg_of r)) (rs (preg_of r))),
          forall m_,
            final_state lm sg (State rs m_) (v, m_)
.

Section WITH_MEM_ACCESSORS_DEFAULT.
  Local Existing Instance mem_accessors_default.

  Definition semantics  (lm: regset) (p: Asm.program) (i: ident) (sg: signature) (args: list val) (m: mem) :=
    Semantics (step) (initial_state lm p i sg args m) (final_state lm sg) (Genv.globalenv p).

End WITH_MEM_ACCESSORS_DEFAULT.

(** Properties of arguments *)

Lemma extcall_args_64_inject_neutral `{Hmem: !Mem.MemoryModel mem}:
  forall rs,
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)),
    forall tl ir fr ofs vl,
      list_forall2 (Asm.extcall_arg_pair rs m) (loc_arguments_64 tl ir fr ofs) vl ->
      Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl.
Proof.
  Opaque int_param_regs float_param_regs.
  induction tl; simpl.
  - inversion 4; subst. constructor.
  -
    assert ( forall ir fr ofs (vl : list val),
               list_forall2 (extcall_arg_pair rs m)
                            (One (S Outgoing ofs a) :: loc_arguments_64 tl ir fr (ofs + typesize a)) vl ->
               Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl).
    {
      inversion 1; subst.
      inv H3. inv H2.
      constructor.
      eapply Mem.loadv_inject_neutral; eauto.
      eauto.
    }
    assert ( forall ty (ir fr ofs : Z) (vl : list val),
  list_forall2 (extcall_arg_pair rs m)
    match list_nth_z int_param_regs ir with
    | Some ireg => One (R ireg) :: loc_arguments_64 tl (ir + 1) fr ofs
    | None => One (S Outgoing ofs ty) :: loc_arguments_64 tl ir fr (ofs + 2)
    end vl -> Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl). {
      inversion 1; subst.
      constructor.
      inv H3.
      - inv H5.
        + destruct (list_nth_z int_param_regs ir); inv H2.
          constructor; eauto.
        + destruct (list_nth_z int_param_regs ir); inv H2.
          constructor; eauto.
          eapply Mem.loadv_inject_neutral; eauto.
      - destruct (list_nth_z int_param_regs ir); inv H2.
    }
    assert (forall ty (ir fr ofs : Z) (vl : list val),
               list_forall2 (extcall_arg_pair rs m)
                            match list_nth_z float_param_regs fr with
                            | Some freg => One (R freg) :: loc_arguments_64 tl ir (fr + 1) ofs
                            | None => One (S Outgoing ofs ty) :: loc_arguments_64 tl ir fr (ofs + 2)
                            end vl -> Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl).
    {
      inversion 1; subst.
      constructor.
      inv H4.
      - inv H6. constructor; eauto.
        + destruct (list_nth_z float_param_regs fr); inv H3. eauto. 
        + destruct (list_nth_z float_param_regs fr); inv H3.
          inv H2. constructor; eauto.
          eapply Mem.loadv_inject_neutral; eauto.
      - destruct (list_nth_z float_param_regs fr); inv H3.
    }
    destruct a; eauto.
Qed.

Lemma extcall_args_32_inject_neutral `{Hmem: !Mem.MemoryModel mem}:
  forall rs,
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)),
    forall tl ofs vl,
      list_forall2 (Asm.extcall_arg_pair rs m) (loc_arguments_32 tl ofs) vl ->
      Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl.
Proof.
  induction tl; simpl.
  - inversion 2; subst. constructor.
  -
    assert ( forall ofs (vl : list val),
               list_forall2 (extcall_arg_pair rs m)
                            (One (S Outgoing ofs a) :: loc_arguments_32 tl (ofs + typesize a)) vl ->
               Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl).
    {
      inversion 1; subst.
      inv H3. inv H2.
      constructor.
      eapply Mem.loadv_inject_neutral; eauto.
      eauto.
    }
    assert ( forall ty (ofs : Z) (vl : list val),
  list_forall2 (extcall_arg_pair rs m)
               (One (S Outgoing ofs ty) :: loc_arguments_32 tl (ofs + typesize ty))
               vl ->
  Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl). {
      inversion 1; subst.
      constructor.
      inv H4.
      inv H3.
      eapply Mem.loadv_inject_neutral; eauto.
      eauto. 
    }
    destruct a; eauto.
    intros. inv H2. constructor; eauto.
    inv H5.
    eapply Val.longofwords_inject.
    inv H4. eapply Mem.loadv_inject_neutral; eauto.
    inv H8. eapply Mem.loadv_inject_neutral; eauto.
Qed.

Lemma extcall_args_inject_neutral `{Gmem: !Mem.MemoryModel mem}:
  forall rs,
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)),
    forall tl vl,
      list_forall2 (Asm.extcall_arg_pair rs m) (loc_arguments tl) vl ->
      Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl.
Proof.
  intros rs m MINJ Hinj_reg tl vl.
  unfold loc_arguments. destruct Archi.ptr64.
  eapply extcall_args_64_inject_neutral; eauto.
  eapply extcall_args_32_inject_neutral; eauto.
Qed.


(** Invariants *)

Function typ_of_preg (r: preg): typ :=
  match r with
    | FR _ => Tany64
    | ST0 => Tany64
    | _ => Tany64
  end.

Definition wt_regset (rs: regset) :=
  forall r, Val.has_type (rs # r) (typ_of_preg r).

Record inject_neutral_invariant {F V: Type} (ge: Genv.t F V) (rs: regset) (m: mem): Prop :=
  {
    inv_mem_valid:
      (Genv.genv_next ge <= Mem.nextblock m)%positive;
    inv_mem_inject_neutral:
      Mem.inject_neutral (Mem.nextblock m) m;
    inv_reg_inject_neutral r:
      Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs # r) (rs # r)
  }.

Record asm_invariant {F V: Type} (ge: Genv.t F V) (rs: regset) (m: mem): Prop :=
  {
    inv_inject_neutral :> inject_neutral_invariant ge rs m;
    inv_reg_wt: wt_regset rs
  }.

(** Proof that the invariants are preserved by Asm steps. *)

(** For the proof of [exec_instr_inject_neutral] below, we need
[MemoryX.inject_neutral_incr] for [Pallocframe]. *)
Context `{memory_model_x: !Mem.MemoryModelX mem}.


(** Typing invariant on registers *)

Lemma set_reg_wt: 
 forall v r',
   Val.has_type v (typ_of_preg r') ->
   forall rs,
     wt_regset rs ->
     wt_regset (rs # r' <- v)
.
Proof.
  red. intros. destruct (preg_eq r r').
   subst. repeat rewrite Pregmap.gss. assumption.
  repeat rewrite Pregmap.gso; eauto.
Qed.

Lemma undef_reg_wt:
  forall rs,
    wt_regset rs ->
    forall r',
    wt_regset (rs # r' <- Vundef).
Proof.
  intros; eapply set_reg_wt; simpl; eauto.
Qed.

Lemma undef_regs_wt:
  forall rs,
    wt_regset rs ->
    forall l, wt_regset (undef_regs l rs).
Proof.
  intros until l. revert rs H. induction l; simpl; eauto using undef_reg_wt.
Qed.

Lemma nextinstr_wt:
  forall rs,
    wt_regset rs ->
    wt_regset (nextinstr rs).
Proof.
  unfold nextinstr.  intros.
  apply set_reg_wt; eauto.
  simpl. generalize (H PC); simpl.
  destruct (rs PC); simpl; clear; tauto.
Qed.

Lemma nextinstr_nf_wt:
  forall rs,
    wt_regset rs ->
    wt_regset (nextinstr_nf rs).
Proof.
  unfold nextinstr_nf.
  intros.
  apply nextinstr_wt.
  apply undef_regs_wt.
  assumption.
Qed.


(** Inject_neutral *)

Lemma set_reg_inject: 
 forall j v v',
   Val.inject j v v' ->
   forall rs rs',
     (forall r, Val.inject j (rs#r) (rs'#r)) ->
     forall r' r, Val.inject j ((rs#r' <- v)#r) ((rs'#r' <- v')#r)
.
Proof.
  intros. destruct (preg_eq r r').
   subst. repeat rewrite Pregmap.gss. assumption.
  repeat rewrite Pregmap.gso; eauto.
Qed.

Lemma undef_reg_inject:
  forall j rs rs',
    (forall r, Val.inject j (rs#r) (rs'#r)) ->
    forall r' r, Val.inject j ((rs#r' <- Vundef)#r) ((rs'#r' <- Vundef)#r).
Proof.
  intros; apply set_reg_inject; auto.
Qed.

Lemma undef_regs_inject:
  forall j rs rs',
    (forall r, Val.inject j (rs#r) (rs'#r)) ->
    forall l r, Val.inject j ((undef_regs l rs)#r) ((undef_regs l rs')#r).
Proof.
  intros until l. revert rs rs' H. induction l; simpl; eauto using undef_reg_inject.
Qed.

Lemma nextinstr_inject:
  forall j rs rs',
    (forall r, Val.inject j (rs#r) (rs'#r)) ->
    forall r, Val.inject j ((nextinstr rs)#r) ((nextinstr rs')#r).
Proof.
  unfold nextinstr.  intros.
  apply set_reg_inject; eauto.
  eapply Val.offset_ptr_inject; eauto.
Qed.

Lemma nextinstr_nf_inject:
  forall j rs rs',
    (forall r, Val.inject j (rs#r) (rs'#r)) ->
    forall r, Val.inject j ((nextinstr_nf rs)#r) ((nextinstr_nf rs')#r).
Proof.
  unfold nextinstr_nf.
  intros.
  apply nextinstr_inject.
  apply undef_regs_inject.
  assumption.
Qed.

Lemma regs_inject_map:
  forall j rs rs',
    (forall r: preg, Val.inject j (rs#r) (rs'#r)) ->
    forall args,
  list_forall2 (Val.inject j) (map rs args) (map rs' args).
Proof.
  induction args; simpl; constructor; auto.
Qed.

Lemma val_inject_neutral_incr: forall thr v, Val.inject (Mem.flat_inj thr) v v -> forall thr', Ple thr thr' -> Val.inject (Mem.flat_inj thr') v v.
Proof.
  inversion 1; try constructor.
  clear H4. subst. unfold Mem.flat_inj in *. destruct (plt b1 thr); try discriminate. inv H3.
  econstructor. destruct (plt b1 thr'); try xomega. reflexivity. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma extcall_arg_inject_neutral':
  forall m rs
         (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         l v,
    extcall_arg rs m l v ->
    Val.inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  induction 3; auto.
  generalize H0. unfold Mem.loadv. case_eq (rs RSP); try discriminate. simpl.
  intros. eapply Mem.loadv_inject_neutral; eauto.
Qed.

Lemma extcall_arg_pair_inject_neutral':
  forall m rs
         (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         l v,
    extcall_arg_pair rs m l v ->
    Val.inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  destruct l; simpl; intros v H; inv H;
  repeat match goal with
           H: extcall_arg _ _ _ _ |- _ => 
           eapply extcall_arg_inject_neutral' in H; eauto
         end.
  eapply Val.longofwords_inject; eauto.
Qed.

Lemma extcall_args_inject_neutral':
  forall m rs
         (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         sg args,
    extcall_arguments rs m sg args ->
    list_forall2 (Val.inject (Mem.flat_inj (Mem.nextblock m))) args args.
Proof.
  unfold extcall_arguments. intros until sg. generalize (loc_arguments sg). clear sg.
  induction 1; constructor; eauto using extcall_arg_pair_inject_neutral'.
Qed.

Lemma shl_inject_neutral:
  forall f v1 v2,
    Val.inject f (Val.shl v1 v2) (Val.shl v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shr_inject_neutral:
  forall f v1 v2,
    Val.inject f (Val.shr v1 v2) (Val.shr v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shru_inject_neutral:
  forall f v1 v2,
    Val.inject f (Val.shru v1 v2) (Val.shru v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma ror_inject_neutral:
  forall f v1 v2,
    Val.inject f (Val.ror v1 v2) (Val.ror v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
Qed.

Lemma of_bool_inject_neutral:
  forall f b,
    Val.inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  destruct b; simpl; constructor.
Qed.

Lemma compare_floats_inject_neutral:
  forall f rs,
    (forall r: preg, Val.inject f (rs r) (rs r)) ->
    forall a b r,
      Val.inject f (compare_floats a b rs r) (compare_floats a b rs r).
Proof with (simpl;
            repeat apply undef_reg_inject;
            auto using of_bool_inject_neutral).
  intros. unfold compare_floats. destruct a...
  destruct b...
  repeat apply set_reg_inject...
Qed.

Lemma cmpu_inject_neutral:
  forall f p c a b,
    Val.inject f (Val.cmpu p c a b) (Val.cmpu p c a b).
Proof.
  intros.
  unfold Val.cmpu. destruct (Val.cmpu_bool p c a b); simpl; auto.
  destruct b0; constructor.
Qed.

Lemma cmp_inject_neutral:
  forall f p c a,
    Val.inject f (Val.cmp p c a) (Val.cmp p c a).
Proof.
  intros.
  unfold Val.cmp. destruct (Val.cmp_bool p c a); simpl; auto.
  destruct b; constructor.
Qed.

Lemma sub_overflow_inject_neutral:
  forall f a b,
    Val.inject f (Val.sub_overflow a b) (Val.sub_overflow a b).
Proof.
  intros.
  unfold Val.sub_overflow.
  destruct a; destruct b; constructor.
Qed.

Lemma negative_inject_neutral:
  forall f a,
    Val.inject f (Val.negative a) (Val.negative a).
Proof.
  unfold Val.negative.
  destruct a; constructor.
Qed.

Lemma compare_ints_inject_neutral:
  forall f rs,
    (forall r: preg, Val.inject f (rs r) (rs r)) ->
    forall a b m r,
      Val.inject f (compare_ints a b rs m r) (compare_ints a b rs m r).
Proof.
  unfold compare_ints.
  intros.
  apply undef_reg_inject.
  eauto using set_reg_inject, cmpu_inject_neutral, undef_reg_inject, negative_inject_neutral, sub_overflow_inject_neutral.
Qed.

Lemma symbol_address_inject_neutral_gen
      se i ofs j:
  (forall (id : ident) (b : block),
      Senv.find_symbol se id = Some b -> j b = Some (b, 0)) ->
  Val.inject j (Senv.symbol_address se i ofs) (Senv.symbol_address se i ofs).
Proof.
  intros.
  unfold Senv.symbol_address.
  destruct (Senv.find_symbol se i) eqn:SYMB; auto.
  econstructor; eauto.
  rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma symbol_address_inject_neutral_preserves_global
      {F V}
      ge i ofs j:
  meminj_preserves_globals (F := F) (V := V) ge j ->
  Val.inject j (Senv.symbol_address ge i ofs) (Senv.symbol_address ge i ofs).
Proof.
  unfold meminj_preserves_globals.
  destruct 1 as (H & _ & _).
  eapply symbol_address_inject_neutral_gen; eauto.
Qed.

Lemma symbol_address_inject_neutral_le_nextblock
      se n i ofs:
  Ple (Senv.nextblock se) n ->
  Val.inject (Mem.flat_inj n) (Senv.symbol_address se i ofs) (Senv.symbol_address se i ofs).
Proof.
  intros H.
  eapply symbol_address_inject_neutral_gen; eauto.
  intros id0 b H0.
  unfold Mem.flat_inj.
  destruct (plt _ _) as [ | N ] ; auto.
  destruct N.
  apply Senv.find_symbol_below in H0.
  xomega.
Qed.

Lemma symbol_address_inject_neutral_le_nextblock_genv
      {F V} (ge: Genv.t F V) n i ofs:
  Ple (Genv.genv_next ge) n ->
  Val.inject (Mem.flat_inj n) (Genv.symbol_address ge i ofs) (Genv.symbol_address ge i ofs).
Proof.
  intro.
  replace (Genv.symbol_address ge) with (Senv.symbol_address ge) by reflexivity.
  eapply symbol_address_inject_neutral_le_nextblock; eauto.
Qed.

Lemma eval_addrmode_inject_neutral:
  forall {F V} (ge: Genv.t F V) m,
    Ple (Genv.genv_next ge) (Mem.nextblock m) ->
    forall rs,
      (forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)) ->
    forall a,
    Val.inject (Mem.flat_inj (Mem.nextblock m)) (eval_addrmode ge a rs) (eval_addrmode ge a rs).
Proof.
  intros.
  unfold eval_addrmode.
  destruct Archi.ptr64.
  - destruct a.
    simpl. apply Val.addl_inject. destruct base; auto.
    apply Val.addl_inject. destruct ofs; auto.
    destruct p; auto. destruct zeq; auto.
    destruct (rs i) eqn:?; simpl; auto.
    destruct const; auto. destruct p; auto.
    eapply symbol_address_inject_neutral_le_nextblock_genv; eauto.
  - destruct a.
    simpl. apply Val.add_inject. destruct base; auto.
    apply Val.add_inject. destruct ofs; auto.
    destruct p; auto. destruct zeq; auto.
    destruct (rs i) eqn:?; simpl; auto.
    destruct const; auto. destruct p; auto.
    eapply symbol_address_inject_neutral_le_nextblock_genv; eauto.
Qed.

(** Proofs related to CertiKOS *)
Section VAL_INJ_OPS.

Variable f: meminj.

Remark val_and_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.and v1 v2) (Val.and v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_or_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.or v1 v2) (Val.or v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_xor_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.xor v1 v2) (Val.xor v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_ror_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.ror v1 v2) (Val.ror v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_shl_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.shl v1 v2) (Val.shl v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
Qed.

Remark val_shr_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.shr v1 v2) (Val.shr v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
Qed.

Remark val_shru_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.shru v1 v2) (Val.shru v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
Qed.

Remark val_mul_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.mul v1 v2) (Val.mul v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_mulhs_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.mulhs v1 v2) (Val.mulhs v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_mulhu_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.mulhu v1 v2) (Val.mulhu v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_zero_ext_inject:
  forall v1 v1' n,
    Val.inject f v1 v1' ->
    Val.inject f (Val.zero_ext n v1) (Val.zero_ext n v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_sign_ext_inject:
  forall v1 v1' n,
    Val.inject f v1 v1' ->
    Val.inject f (Val.sign_ext n v1) (Val.sign_ext n v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_singleoffloat_inject:
  forall v1 v1',
    Val.inject f v1 v1' ->
    Val.inject f (Val.singleoffloat v1) (Val.singleoffloat v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_neg_inject:
  forall v1 v1',
    Val.inject f v1 v1' ->
    Val.inject f (Val.neg v1) (Val.neg v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_notint_inject:
  forall v1 v1',
    Val.inject f v1 v1' ->
    Val.inject f (Val.notint v1) (Val.notint v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_addf_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.addf v1 v2) (Val.addf v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto.
Qed.

Remark val_subf_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.subf v1 v2) (Val.subf v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_mulf_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mulf v1 v2) (Val.mulf v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_divf_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.divf v1 v2) (Val.divf v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_negf_inject:
  forall v1 v1',
    Val.inject f v1 v1' ->
    Val.inject f (Val.negf v1) (Val.negf v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_absf_inject:
  forall v1 v1',
    Val.inject f v1 v1' ->
    Val.inject f (Val.absf v1) (Val.absf v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_intoffloat_inject:
  forall v1 v1',
    Val.inject f v1 v1' ->
    Val.inject f (Val.maketotal (Val.intoffloat v1))  (Val.maketotal (Val.intoffloat v1')).
Proof.
  intros. inv H; simpl; auto.
  destruct (Float.to_int f0); simpl; auto.
Qed.

Remark val_floatofint_inject:
  forall v1 v1',
    Val.inject f v1 v1' ->
    Val.inject f (Val.maketotal (Val.floatofint v1))  (Val.maketotal (Val.floatofint v1')).
Proof.
  intros. inv H; simpl; auto.
Qed.

Lemma val_compare_floats_inject_neutral:
  forall rs rs',
    (forall r: preg, Val.inject f (Pregmap.get r rs) (Pregmap.get r rs')) ->
    forall v1 v2 v1' v2', 
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    forall r,
      Val.inject f (compare_floats v1 v2 rs r) (compare_floats v1' v2' rs' r).
Proof.
  unfold compare_floats. intros.
  inv H0; inv H1; simpl; eauto;
  repeat match goal with
           | [|- context[match ?a with |_ => _ end]] => destruct a
         end;
  repeat apply undef_reg_inject; eauto 1;
  repeat eapply set_reg_inject; eauto;
  auto using of_bool_inject_neutral.
Qed.

Lemma val_compare_ints_inject_neutral:
  forall rs rs' m m',
    (forall r: preg, Val.inject f (Pregmap.get r rs) (Pregmap.get r rs')) ->
    Mem.inject f m m' ->
    forall v1 v2 v1' v2', 
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    forall r,
      Val.inject f (compare_ints v1 v2 rs m r) (compare_ints v1' v2' rs' m' r).
Proof.
  unfold compare_ints.
  intros; apply undef_reg_inject.
  repeat eapply set_reg_inject; eauto.
  - inv H1; inv H2; simpl; auto.
  - exploit (Val.sub_inject f v1 v1' v2); eauto.
    intros Hinv. inv Hinv; simpl; auto.
  - unfold Val.cmpu.
    caseEq (Val.cmpu_bool (Mem.valid_pointer m) Clt v1 v2); intros; try constructor.
    assert (HW: (Val.cmpu_bool (Mem.valid_pointer m') Clt v1' v2' = Some b)).
    {
      eapply Val.cmpu_bool_inject; eauto 1; intros.
      - eapply Mem.valid_pointer_inject_val; eauto.
      - eapply Mem.weak_valid_pointer_inject_val; eauto.
      - eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
      - eapply Mem.different_pointers_inject; eauto.
    }
    rewrite HW. simpl.
    destruct b; constructor.
  - unfold Val.cmpu.
    caseEq (Val.cmpu_bool (Mem.valid_pointer m) Ceq v1 v2); intros; try constructor.
    assert (HW: (Val.cmpu_bool (Mem.valid_pointer m') Ceq v1' v2' = Some b)).
    {
      eapply Val.cmpu_bool_inject; eauto 1; intros.
      - eapply Mem.valid_pointer_inject_val; eauto.
      - eapply Mem.weak_valid_pointer_inject_val; eauto.
      - eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
      - eapply Mem.different_pointers_inject; eauto.
    }
    rewrite HW. simpl.
    destruct b; constructor.
Qed.

Remark val_divu_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    forall v,
      Val.divu v1 v2 = Some v ->
      exists v', Val.divu v1' v2' = Some v'
                 /\ Val.inject f v v'.
Proof.
  intros. inv H; inv H0; simpl in *; try discriminate; eauto.
  destruct (Int.eq i0 Int.zero).
  discriminate.
  inv H1. eauto.
Qed.

Remark val_modu_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    forall v,
      Val.modu v1 v2 = Some v ->
      exists v', Val.modu v1' v2' = Some v'
                 /\ Val.inject f v v'.
Proof.
  intros. inv H; inv H0; simpl in *; try discriminate; eauto.
  destruct (Int.eq i0 Int.zero).
  discriminate.
  inv H1. eauto.
Qed.

Remark val_divs_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    forall v,
      Val.divs v1 v2 = Some v ->
      exists v', Val.divs v1' v2' = Some v'
                 /\ Val.inject f v v'.
Proof.
  intros. inv H; inv H0; simpl in *; try discriminate; eauto.
  destruct (Int.eq i0 Int.zero
                   || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone).
  discriminate.
  inv H1; eauto.
Qed.

Remark val_mods_inject:
  forall v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    forall v,
      Val.mods v1 v2 = Some v ->
      exists v', Val.mods v1' v2' = Some v'
                 /\ Val.inject f v v'.
Proof.
  intros. inv H; inv H0; simpl in *; try discriminate; eauto.
  destruct (Int.eq i0 Int.zero
                   || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone).
  discriminate.
  inv H1; eauto.
Qed.

Remark val_negl_inject:
  forall f v1 v1',
    Val.inject f v1 v1' ->
    Val.inject f (Val.negl v1) (Val.negl v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_addl_inject:
  forall f v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.addl v1 v2) (Val.addl v1' v2').
Proof.
  intros. apply Val.addl_inject; auto. 
Qed.

Remark val_subl_inject:
  forall f v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.subl v1 v2) (Val.subl v1' v2').
Proof.
  intros. apply Val.subl_inject; auto.
Qed.

Remark val_mull'_inject:
  forall f v1 v1' v2 v2',
    Val.inject f v1 v1' ->
    Val.inject f v2 v2' ->
    Val.inject f (Val.mull' v1 v2) (Val.mull' v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto.
Qed.

End VAL_INJ_OPS.

Class MemAccessorsInvariant
      (exec_load: forall {F V}, Genv.t F V -> memory_chunk -> mem -> addrmode -> regset -> preg -> outcome)
      (exec_store: forall {F V}, Genv.t F V -> memory_chunk -> mem -> addrmode -> regset -> preg -> list preg -> outcome)
  :=
  {
    exec_load_invariant {F V : Type} (ge: Genv.t F V) chunk m a rs rv rs' m':
      exec_load ge chunk m a rs rv = Next rs' m' ->
      subtype (type_of_chunk chunk) (typ_of_preg rv) = true ->
      asm_invariant ge rs m ->
      asm_invariant ge rs' m'
    ;

    exec_store_invariant {F V} (ge: Genv.t F V) chunk m a rs rv rvl rs' m':
      exec_store ge chunk m a rs rv rvl = Next rs' m' ->
      asm_invariant ge rs m ->
      asm_invariant ge rs' m'
  }.

Section WITHMEMACCESSORSINVARIANT.

  Context {exec_load exec_store}
          `{mem_acc: @MemAccessors _ memory_model_ops exec_load exec_store}
          `{mem_acc_inv: MemAccessorsInvariant exec_load exec_store}.

  Section WITHFINDLABELS.
    Context `{find_labels_prf: FindLabels}.


Lemma goto_label_wt:
  forall rs,
    wt_regset rs ->
    forall {F V} (ge: Genv.t F V) m c lbl rs' m',
      Next rs' m' = goto_label ge c lbl rs m ->
      wt_regset rs'.
Proof.
  unfold goto_label. intros until m'. destruct (label_pos lbl 0 (fn_code0 c)); try discriminate.
  case_eq (rs PC); try discriminate.
  intros b i EQ.
  case_eq (Genv.find_funct_ptr ge b); try discriminate.
  injection 2; intros -> -> .
  apply set_reg_wt; simpl; auto.
Qed.

Lemma goto_label_inject_neutral:
  forall {F V} (ge: Genv.t F V) rs m,
    inject_neutral_invariant ge rs m ->
    forall c lbl rs' m',
      Next rs' m' = goto_label ge c lbl rs m ->
      inject_neutral_invariant ge rs' m'.
Proof.
  inversion 1; subst.
  unfold goto_label. intros until m'. destruct (label_pos lbl 0 (fn_code0 c)); try discriminate.
  case_eq (rs PC); try discriminate.
  intros b i EQ.
  case_eq (Genv.find_funct_ptr ge b); try discriminate.
  injection 2; intros; subst.
  split; auto.
  apply set_reg_inject; auto.
  generalize (inv_reg_inject_neutral0 PC).
  rewrite EQ. 
  inversion 1.
  clear H8. subst. econstructor. eassumption.
  unfold Mem.flat_inj in H6. destruct (plt b (Mem.nextblock m)); try discriminate.
  inv H6. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma compare_floats32_inject_neutral:
  forall f rs,
    (forall r: preg, Val.inject f (rs r) (rs r)) ->
    forall a b r,
      Val.inject f (compare_floats32 a b rs r) (compare_floats32 a b rs r).
Proof with (simpl;
            repeat apply undef_reg_inject;
            auto using of_bool_inject_neutral).
  intros. unfold compare_floats32. destruct a...
  destruct b...
  repeat apply set_reg_inject...
Qed.

Lemma inject_neutral_invariant_set_undef {F V} (ge:Genv.t F V) rs m r:
  inject_neutral_invariant ge rs m ->
  inject_neutral_invariant ge (rs # r <- Vundef) m.
Proof.
  intro A; inv A; constructor; auto.
  intros.
  apply undef_reg_inject. auto.
Qed.

Theorem exec_instr_inject_neutral:
    forall {F V} (ge: Genv.t F V) rs m,
      asm_invariant ge rs m ->
      forall c rs' m' i,
        Next rs' m' = exec_instr ge c i rs m ->
        inject_neutral_invariant ge rs' m'
  .
  Proof.
    inversion 1; subst.
    inversion inv_inject_neutral0; subst.
    intros until i.
    destruct i; simpl;
      repeat match goal with
             | |- Next rs' m' = exec_load ge ?chunk m ?a rs ?rd ->
                 inject_neutral_invariant ge rs' m' =>
               let J := fresh in
               intro J; symmetry in J;
                 eapply inv_inject_neutral;
                 eapply exec_load_invariant; eauto
             | |- Next rs' m' = exec_store ge ?chunk m ?a rs ?rd ?l ->
                                          inject_neutral_invariant ge rs' m' =>
               let J := fresh in
               intro J; symmetry in J;
                 eapply inv_inject_neutral;
                 eapply exec_store_invariant; eauto
             | |- Next rs' m' = match eval_testcond ?c rs with Some _ => _ | None => _ end -> _ => destruct (eval_testcond c rs) as [[|]|]
             | |- Next rs' m' = goto_label _ ?c ?lbl rs m -> _ =>
               eapply goto_label_inject_neutral; eauto
             | |- Next rs' m' = (if ?b then _ else _) -> _ => destruct b
             | |- Next rs' m' = Next _ m -> _ =>
               injection 1; intros; subst; constructor; auto;
                 repeat match goal with 
                        | |- forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (nextinstr ?rs r) (nextinstr ?rs r) => apply nextinstr_inject
                        | |- forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (nextinstr_nf ?rs r) (nextinstr_nf ?rs r) => apply nextinstr_inject
                        | |- forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (undef_regs ?l ?rs r) (undef_regs ?l ?rs r) => apply undef_regs_inject
                        | |- forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (?rs # ?r' <- Vundef r) (?rs # ?r' <- Vundef r) => apply undef_reg_inject
                        | |- forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (?rs # ?r' <- ?v r) (?rs # ?r' <- ?v r) => apply set_reg_inject
                        | |- Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs ?r) (rs ?r) => now auto
                        | |- forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r) => now auto
                        | |- Val.inject (Mem.flat_inj (Mem.nextblock m)) (Genv.symbol_address ge ?sy ?of) (Genv.symbol_address ge ?sy ?of) =>
                          eapply symbol_address_inject_neutral_le_nextblock_genv; eauto
                        | |- Val.inject (Mem.flat_inj (Mem.nextblock m)) (eval_addrmode ge ?sy ?of) (eval_addrmode ge ?sy ?of) =>
                          eapply eval_addrmode_inject_neutral
                        | |- Ple (Genv.genv_next ge) (Mem.nextblock m) => assumption
                        | |- Val.inject _ (Vint ?i) (Vint ?i) => constructor
                        | |- Val.inject _ (Vfloat ?i) (Vfloat ?i) => constructor
                        | |- Val.inject _ (Vlong ?i) (Vlong ?i) => constructor
                        | |- Val.inject _ (Vsingle ?i) (Vsingle ?i) => constructor
                        | |- forall r, Val.inject _ (compare_ints ?a ?b rs m r) (compare_ints ?a ?b rs m r) => apply compare_ints_inject_neutral
                        | |- forall r, Val.inject _ (compare_floats ?a ?b rs r) (compare_floats ?a ?b rs r) => apply compare_floats_inject_neutral
                        | |- Val.inject _ (Val.add ?i ?g) (Val.add ?i ?g) => apply Val.add_inject
                        | |- Val.inject _ (Val.sub ?i ?g) (Val.sub ?i ?g) => apply Val.sub_inject
                        | |- Val.inject _ (Val.zero_ext ?n ?v) (Val.zero_ext ?n ?v) => destruct v; simpl; constructor
                        | |- Val.inject _ (Val.sign_ext ?n ?v) (Val.sign_ext ?n ?v) => destruct v; simpl; constructor
                        | |- Val.inject _ (Val.singleoffloat ?v) (Val.singleoffloat ?v) => destruct v; simpl; constructor
                        | |- Val.inject _ (Val.maketotal (Val.floatofint ?v)) (Val.maketotal (Val.floatofint ?v)) => destruct v; simpl; constructor
                        | |- Val.inject _ (Val.neg ?v) (Val.neg ?v) => destruct v; simpl; constructor
                        | |- Val.inject _ (Val.negl ?v) (Val.negl ?v) => apply val_negl_inject; auto
                        | |- Val.inject _ (Val.notint ?v) (Val.notint ?v) => destruct v; simpl; constructor
                        | |- Val.inject _ (Val.negf ?v) (Val.negf ?v) => destruct v; simpl; constructor
                        | |- Val.inject _ (Val.absf ?v) (Val.absf ?v) => destruct v; simpl; constructor
                        | |- Val.inject _ (Val.mul ?v1 ?v2) (Val.mul ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.mull ?v1 ?v2) (Val.mull ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.mullhu ?v1 ?v2) (Val.mullhu ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.mullhs ?v1 ?v2) (Val.mullhs ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.mulf ?v1 ?v2) (Val.mulf ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.and ?v1 ?v2) (Val.and ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.andl ?v1 ?v2) (Val.andl ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.orl ?v1 ?v2) (Val.orl ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.addf ?v1 ?v2) (Val.addf ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.subf ?v1 ?v2) (Val.subf ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.mulhs ?v1 ?v2) (Val.mulhs ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.mulhu ?v1 ?v2) (Val.mulhu ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.divf ?v1 ?v2) (Val.divf ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.or ?v1 ?v2) (Val.or ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ (Val.shl ?v1 ?v2) (Val.shl ?v1 ?v2) => apply shl_inject_neutral
                        | |- Val.inject _ (Val.shr ?v1 ?v2) (Val.shr ?v1 ?v2) => apply shr_inject_neutral
                        | |- Val.inject _ (Val.shrl ?v1 ?v2) (Val.shrl ?v1 ?v2) => destruct v1;  simpl; constructor
                        | |- Val.inject _ (Val.shru ?v1 ?v2) (Val.shru ?v1 ?v2) => apply shru_inject_neutral
                        | |- Val.inject _ (Val.ror ?v1 ?v2) (Val.ror ?v1 ?v2) => apply ror_inject_neutral
                        | |- Val.inject _ (Val.xor ?v1 ?v2) (Val.xor ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
                        | |- Val.inject _ Vzero Vzero => constructor
                        | |- Val.inject _ Vone Vone => constructor
                        | |- Val.inject _ (Val.of_optbool ?v) (Val.of_optbool ?v) => destruct v as [[|] |]; simpl; constructor
                        | |- Val.inject _ Vundef Vundef => constructor
                        | |- Val.inject _ (Val.maketotal ?v) (Val.maketotal ?v) => case_eq v; simpl; auto
                        | |- forall r, Val.inject _ (compare_ints ?a ?b rs m r) (compare_ints ?a ?b rs m r) => apply compare_ints_inject_neutral
                        | |- forall r, Val.inject _ (compare_floats ?a ?b rs r) (compare_floats ?a ?b rs r) => apply compare_floats_inject_neutral
                        | |- forall r, Val.inject _ (compare_floats32 ?a ?b rs r) (compare_floats32 ?a ?b rs r) => apply compare_floats32_inject_neutral
                        | |- Val.inject _ (Val.addl ?a ?b) (Val.addl ?c ?d) =>
                          apply Val.addl_inject; auto
                        | |- Val.inject _ (Val.subl ?a ?b) (Val.subl ?c ?d) =>
                          apply Val.subl_inject; auto
                        end
             | |- Next _ _ = Stuck -> _ => discriminate
             end.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * destruct (rs rs0); simpl; auto.
    * destruct (rs rs0); simpl; auto.
    * destruct (rs rd); simpl; auto.
    * (* floatofsingle *)
      destruct (rs r1); simpl; auto.
    * (* intoffloat *)
      destruct (rs r1); simpl; try discriminate.
      destruct (Float.to_int _); try discriminate.
      inversion 1; subst; auto.
    * (* intofsingle *)
      destruct (rs r1); simpl; try discriminate.
      destruct (Float32.to_int _); try discriminate.
      inversion 1; subst; auto.
    * (* singleofint *)
      destruct (rs r1); simpl; try discriminate.
      inversion 1; subst; auto.
    * (* longoffloat *)
      destruct (rs r1); simpl; try discriminate.
      destruct (Float.to_long f); simpl; inversion 1; subst; auto.
    * (* floatoflong *)
      destruct (rs r1); simpl; try discriminate.
      destruct (Float.of_long i); simpl; inversion 1; subst; auto.
    * (* longofsingle *)
      destruct (rs r1); simpl; try discriminate.
      destruct (Float32.to_long f); simpl; inversion 1; subst; auto.
    * (* singleoflong *)
      destruct (rs r1); simpl; try discriminate.
      destruct (Float32.of_long i); simpl; inversion 1; subst; auto.
    * (* addrmode32 *)
      destruct a.
      simpl. apply Val.add_inject. destruct base; auto.
      apply Val.add_inject. destruct ofs; auto.
      destruct p; auto. destruct zeq; auto.
      destruct (rs i) eqn:?; simpl; auto.
      destruct const; auto. destruct p; auto.
      eapply symbol_address_inject_neutral_le_nextblock_genv; eauto.
    * (* addrmode64 *)
      destruct a.
      simpl. apply Val.addl_inject. destruct base; auto.
      apply Val.addl_inject. destruct ofs; auto.
      destruct p; auto. destruct zeq; auto.
      destruct (rs i) eqn:?; simpl; auto.
      destruct const; auto. destruct p; auto.
      eapply symbol_address_inject_neutral_le_nextblock_genv; eauto. 
    * (* unsigned division *)

      Ltac destr_all :=
        repeat match goal with
                 |- context [match ?g with _ => _ end] =>
                 (destruct g eqn:?; try discriminate)
               | |- context [if ?g then _ else _] =>
                 (destruct g eqn:?; try discriminate)
               end.
      Ltac solve_reg_inj :=
        repeat
          match goal with
          | |- forall r, Val.inject _ (nextinstr_nf _ _) (nextinstr_nf _ _) => apply set_reg_inject; auto
          | |- forall r, Val.inject _ (_ # _ <- _ _) (_ # _ <- _ _) => apply set_reg_inject; auto
          | |- Val.inject _ (Val.offset_ptr _ _) (Val.offset_ptr _ _) => apply Val.offset_ptr_inject; auto
          | |- Val.inject _ (undef_regs _ _ _) (undef_regs _ _ _) => apply undef_regs_inject; auto
          | |- _ => intros
          end.
      
      destr_all.
      injection 1; intros; subst.
      constructor; auto.
      solve_reg_inj.
    * (* unsigned long division *)
      destr_all.
      injection 1; intros; subst.
      constructor; auto.
      solve_reg_inj.

    * (* signed division *)
      destr_all.
      injection 1; intros; subst.
      constructor; auto.
      solve_reg_inj.
    * (* signed long division *)
      destr_all.
      injection 1; intros; subst.
      constructor; auto.
      solve_reg_inj.
      
    * destruct (rs rd), (rs r1); simpl; auto.
    * destruct (rs rd); simpl; auto.
    * destruct (rs rd); simpl; auto.
    * destruct (rs rd), (rs RCX); simpl; auto.
      destruct (Int.ltu); auto.
    * destruct (rs rd); simpl; destruct Int.ltu; auto.
    * destruct (rs rd), (rs RCX); simpl; auto. destruct Int.ltu; auto.
    * destruct (rs rd); simpl; destruct Int.ltu; auto.
    * destruct (rs rd), (rs RCX); simpl; auto. destruct Int.ltu; auto.
    * destruct (rs rd); simpl; destruct Int.ltu; auto.
    * destruct (rs rd); simpl; destruct Int.ltu; auto.
    * unfold compare_longs.
      solve_reg_inj; destruct (rs r1), (rs r2); simpl; auto;
        destr_all; simpl; auto;
          unfold Val.cmplu; simpl; destr_all; simpl; auto;
            try apply of_bool_inject_neutral;
      constructor.
    * unfold compare_longs.
      solve_reg_inj; destruct (rs r1); simpl; auto;
        destr_all; simpl; auto;
          unfold Val.cmplu; simpl; destr_all; simpl; auto;
            try apply of_bool_inject_neutral;
      constructor.
    * unfold compare_longs.
      solve_reg_inj; destruct (rs r1), (rs r2); simpl; auto;
        destr_all; simpl; auto;
          unfold Val.cmplu; simpl; destr_all; simpl; auto;
            try apply of_bool_inject_neutral;
      constructor.
    * unfold compare_longs.
      solve_reg_inj; destruct (rs r1); simpl; auto;
        destr_all; simpl; auto;
          unfold Val.cmplu; simpl; destr_all; simpl; auto;
            try apply of_bool_inject_neutral;
      constructor.
    * destruct (rs rd), (rs r1); simpl; auto.
    * destruct (rs rd), (rs r1); simpl; auto.
    * destruct (rs rd), (rs r1); simpl; auto.
    * destruct (rs rd), (rs r1); simpl; auto.
    * destruct (rs rd); simpl; auto.
    * destruct (rs rd); simpl; auto.
    * destruct (rs r) eqn:?; try discriminate.
      destruct (list_nth_z tbl (Int.unsigned i)); try discriminate. 
      eapply goto_label_inject_neutral.
      repeat apply inject_neutral_invariant_set_undef; eauto.
    * apply Val.offset_ptr_inject; auto.
    * apply Val.offset_ptr_inject; auto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * intros. eapply exec_load_invariant; eauto.
    * intros. eapply exec_store_invariant; eauto.
    * (* Pallocframe *)
      destr_all.
      exploit @Mem.nextblock_alloc; eauto.
      intro NEXTBLOCK.
      exploit @Mem.alloc_result; eauto.
      intro; subst.
      exploit @Mem.alloc_inject_neutral.
      eassumption.
      eapply Mem.inject_neutral_incr. eassumption. instantiate (1 := Psucc (Mem.nextblock m)). xomega. xomega.
      rewrite <- NEXTBLOCK.
      intro.
      exploit Mem.store_inject_neutral. apply Heqo. all: eauto.
      unfold block in *; xomega.
      eapply val_inject_neutral_incr; eauto. unfold block in *; xomega.
      intro.
      exploit Mem.nextblock_store. apply Heqo. 
      intro.
      exploit Mem.store_inject_neutral; eauto.
      unfold block in *; xomega.
      eapply val_inject_neutral_incr; eauto. unfold block in *; xomega.
      intro.
      exploit Mem.nextblock_store; eauto.
      intro.
      injection 1; intros; subst.
      split.
      unfold block in *; xomega.
      congruence.
      apply nextinstr_inject.
      apply set_reg_inject.
      econstructor. unfold Mem.flat_inj.
      destruct (plt (Mem.nextblock m) (Mem.nextblock m2)); try (unfold block in *; exfalso; xomega).
      reflexivity. reflexivity.
      intro. eapply val_inject_neutral_incr; eauto using set_reg_inject.
      unfold block in *; xomega.
    * (* Pfreeframe *)
      destr_all. 
      injection 1; intros; subst.
      simpl in *.
      assert (Plt b (Mem.nextblock m)).
      {
        eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies. eapply Mem.load_valid_access. eassumption. constructor.
      } 
      split;
        erewrite Mem.nextblock_free; eauto.
      eapply Mem.free_inject_neutral; eauto.
      apply nextinstr_inject.
      apply set_reg_inject.
      eapply Mem.load_inject_neutral; eauto. 
      apply set_reg_inject; auto.
      eapply Mem.load_inject_neutral; eauto. 
  Qed.

     (** Well-typed state *)

 Ltac wt_solve :=
      match goal with
        | |- Next _ _ = Stuck -> _ => discriminate
        | |- Next _ _ = Next _ _ -> _ =>
          let H := fresh in (intro H; injection H; clear H; intros; subst)
        | |- wt_regset (nextinstr_nf _) => apply nextinstr_nf_wt
        | |- wt_regset (nextinstr _) => apply nextinstr_wt
        | |- wt_regset (undef_regs _ _) => apply undef_regs_wt
        | |- wt_regset (_ # _ <- Vundef) => apply undef_reg_wt
        | |- wt_regset (_ # _ <- _) => apply set_reg_wt; simpl
        | [ H : wt_regset ?rs |- Val.has_type (?rs _) _ ] => apply H
        | |- True => exact I
        | |- ?x = ?x => reflexivity
        | |- Next ?rs' _ = exec_store _ _ _ _ _ _ _ -> wt_regset ?rs' =>
          let K := fresh in
          intro K;
            symmetry in K;
            eapply inv_reg_wt;
            eapply exec_store_invariant; eauto
        | |- Next ?rs' _ = exec_load _ _ _ _ _ _ -> wt_regset ?rs' =>
          let K := fresh in
          intro K;
            symmetry in K;
            eapply inv_reg_wt;
            eapply exec_load_invariant; eauto
        | |- Val.has_type (Val.zero_ext _ ?v) Tany32 => destruct v; simpl
        | |- Val.has_type (Val.sign_ext _ ?v) Tany32 => destruct v; simpl
        | |- Val.has_type (Val.singleoffloat ?v) Tany64 => destruct v; simpl
        | |- Val.has_type (Val.maketotal (Val.intoffloat ?v)) Tany32 => destruct v; simpl
        | |- Val.has_type (Val.maketotal (option_map Vint ?v)) Tany32 => destruct v; simpl
        | |- Val.has_type (Val.maketotal (Val.floatofint ?v)) Tany64 => destruct v; simpl
        | |- Val.has_type (Val.neg ?v) Tany32 => destruct v; simpl
        | |- Val.has_type (Val.notint ?v) Tany32 => destruct v; simpl
        | |- Val.has_type (Val.negative ?v) Tany32 => destruct v; simpl
        | |- Val.has_type (Val.mul ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.and ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.add ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.sub ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.or ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.xor ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.shl ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.shru ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.shr ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.sub_overflow ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.ror ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.addf ?v1 ?v2) Tany64 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.mulf ?v1 ?v2) Tany64 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.divf ?v1 ?v2) Tany64 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.subf ?v1 ?v2) Tany64 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.negf ?v) Tany64 => destruct v; simpl
        | |- Val.has_type (Val.absf ?v) Tany64 => destruct v; simpl
        | |- Val.has_type (Val.mulhs ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.mulhu ?v1 ?v2) Tany32 => destruct v1; destruct v2; simpl
        | |- Val.has_type (if ?cond then _ else _) _ => destruct cond; simpl
        | |- Val.has_type match ?opt with Some _ => _ | None => _ end _ => destruct opt; simpl
        | |- Val.has_type match ?addr with Addrmode _ _ _ => _ end _ => destruct addr; simpl
        | |- Val.has_type (Genv.symbol_address _ _ _) _ => unfold Genv.symbol_address
        | |- Val.has_type (eval_addrmode _ _ _) _ => unfold eval_addrmode
        | |- Val.has_type (Val.cmp _ _ _) _ => unfold Val.cmp
        | |- Val.has_type (Val.cmpu _ _ _ _) _ => unfold Val.cmpu
        | |- Val.has_type (Val.of_optbool ?v) Tany32 => destruct v; simpl
        | |- Val.has_type (Val.of_bool ?v) Tany32 => destruct v; simpl
        | |- Next ?rs' _ = goto_label _ _ _ _ -> wt_regset ?rs' => eapply goto_label_wt
        | |- Next ?rs' _ = match eval_testcond ?c ?r with Some _ => _ | None => _ end -> _ => destruct (eval_testcond c r); simpl
        | |- (Next _ _ = if ?b then _ else _) -> _ => destruct b; simpl
        | |- wt_regset (compare_ints _ _ _ _) => unfold compare_ints
        | |- Val.has_type ?v Tany64 => destruct v; exact I
        | _ => assumption
      end.
    
    Theorem exec_instr_wt:
      forall {F V} (ge: Genv.t F V) rs m,
        (* asm_invariant ge rs m -> *)
        forall c rs' m' i,
          Next rs' m' = exec_instr ge c i rs m ->
          wt_regset rs'
    .
    Proof with (repeat wt_solve).
      red; intros.
      destruct (rs' r), r; simpl; auto.
    Qed.

    Theorem exec_instr_invariant:
      forall {F V} (ge: Genv.t F V) rs m,
        asm_invariant ge rs m ->
        forall c rs' m' i,
          exec_instr ge c i rs m = Next rs' m' ->
          asm_invariant ge rs' m'
    .
    Proof.
      intros. symmetry in H0. constructor; eauto using exec_instr_wt, exec_instr_inject_neutral.
    Qed.

  End WITHFINDLABELS.

End WITHMEMACCESSORSINVARIANT.

(** Extensionality properties over [exec_load] and [exec_store] *)

Section WITH2MEMACCESSORS.

  Context {exec_load1 exec_store1}
          `{mem_accessors1: @MemAccessors _ _ exec_load1 exec_store1}
          `{mem_acc1: !MemAccessorsInvariant exec_load1 exec_store1}
          {exec_load2 exec_store2}
          `{mem_accessors2: @MemAccessors _ _ exec_load2 exec_store2}
          `{mem_acc2: !MemAccessorsInvariant exec_load2 exec_store2}.

  Theorem exec_instr_mem_accessors_ext:
    forall {F V} (ge: Genv.t F V) m rs
           (EXEC_LOAD_EXT:
              forall chunk a rd rs' m',
                exec_load1 _ _ ge chunk m a rs rd = Next rs' m' ->
                exec_load2 _ _ ge chunk m a rs rd = Next rs' m')
           (EXEC_STORE_EXT:
              forall chunk a rd rl rs' m',
                exec_store1 _ _ ge chunk m a rs rd rl = Next rs' m' ->
                exec_store2 _ _ ge chunk m a rs rd rl = Next rs' m')
           f i rs' m'
           (EXEC_INSTR1:
              exec_instr (exec_load := exec_load1) (exec_store := exec_store1)
                         ge f i rs m = Next rs' m')
    ,
      exec_instr (exec_load := exec_load2)
                 (exec_store := exec_store2)
                 ge f i rs m = Next rs' m'
  .
  Proof.
    destruct i; simpl; intros; eauto.
  Qed.

End WITH2MEMACCESSORS.

(** Extensionality over [ge] *)

Section WITH2GE.

   Context
     {exec_load:
        forall {F V},
          Genv.t F V ->
       memory_chunk ->
       mem -> addrmode -> regset -> preg -> outcome }
    {exec_store:
        forall {F V},
          Genv.t F V ->
       memory_chunk ->
       mem -> addrmode -> regset -> preg -> list preg -> outcome }
   .

   Local Instance: @MemAccessors _ _ exec_load exec_store.

  Context {F V} (ge1 ge2: Genv.t F V)
          (genv_symbols_preserved: forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i).

  Lemma symbol_address_symbols_preserved:
    forall i o,
      Genv.symbol_address ge2 i o = Genv.symbol_address ge1 i o.
  Proof.
    unfold Genv.symbol_address. intros. rewrite genv_symbols_preserved. reflexivity.
  Qed.

  Lemma eval_addrmode32_symbols_preserved:
    forall a rs,
      eval_addrmode32 ge2 a rs = eval_addrmode32 ge1 a rs.
  Proof.
    intros. destruct a.
    unfold eval_addrmode32.
    f_equal. f_equal. destruct const; try reflexivity.
    destruct p.
    apply symbol_address_symbols_preserved.
  Qed.

  Lemma eval_addrmode64_symbols_preserved:
    forall a rs,
      eval_addrmode64 ge2 a rs = eval_addrmode64 ge1 a rs.
  Proof.
    intros. destruct a.
    simpl. f_equal. f_equal.
    destruct const; auto. destruct p; auto.
    apply symbol_address_symbols_preserved.
  Qed.

  (** [CompCertiKOS:sim-asm] The following requirement becomes necessary for
      goto_label. *)

  Hypothesis genv_functions_preserved:
    forall b,
      Genv.find_funct_ptr ge2 b = None <->
      Genv.find_funct_ptr ge1 b = None.

  Lemma goto_label_symbols_preserved f l r m:
    goto_label ge2 f l r m =
    goto_label ge1 f l r m.
  Proof.
    unfold goto_label.
    destruct (label_pos l 0 (fn_code f)); auto.
    destruct (r PC); auto.
    specialize (genv_functions_preserved b).
    destruct (Genv.find_funct_ptr ge1 b) eqn:FF1;
      destruct (Genv.find_funct_ptr ge2 b) eqn:FF2;
      intuition congruence.
  Qed.

  Theorem exec_instr_symbols_preserved:
    forall
      rs m
      (exec_load_symbols_preserved:
         forall chunk a rd,
                exec_load _ _ ge2 chunk m a rs rd =
                exec_load _ _ ge1 chunk m a rs rd)
      (exec_store_symbols_preserved:
         forall chunk a rd rl,
           exec_store _ _ ge2 chunk m a rs rd rl =
           exec_store _ _ ge1 chunk m a rs rd rl)
      f i,
      exec_instr ge2 f i rs m =
      exec_instr ge1 f i rs m.
  Proof.
    destruct i; try reflexivity; simpl; eauto;
      try rewrite eval_addrmode32_symbols_preserved; eauto;
        try rewrite eval_addrmode64_symbols_preserved; eauto;
          try rewrite symbol_address_symbols_preserved; eauto;
            try erewrite goto_label_symbols_preserved; eauto.
    destruct (rs r); auto.
    destruct (list_nth_z _ _); auto.
    apply goto_label_symbols_preserved. 
  Qed.

End WITH2GE.

End WITHCONFIG.

(** Proof of invariants for default accessors *)

Section WITHMEM.
  Context `{Hmem: Mem.MemoryModel}.

  Local Instance mem_accessors_default_invariant:
    @MemAccessorsInvariant _ _ (@Asm.exec_load _ _) (@Asm.exec_store _ _).
  Proof.
    constructor.
    * unfold exec_load. intros.
      destruct (eval_addrmode ge a rs); try discriminate.
      simpl in H.
      destruct (Mem.load chunk m b (Ptrofs.unsigned i)) eqn:?; try discriminate.
      inv H.
      inversion H1.
      inversion inv_inject_neutral0.
      constructor; auto.
      constructor; auto.
      apply nextinstr_nf_inject.
      apply set_reg_inject; auto.
      eapply Mem.load_inject_neutral; eauto.
      apply nextinstr_nf_wt; auto.
      apply set_reg_wt; auto.
      eapply Val.has_subtype; eauto. eapply Mem.load_type; eauto.
    * unfold exec_store. intros.
      destruct (eval_addrmode ge a rs); try discriminate.
      simpl in H.
      destruct (Mem.store chunk m b (Ptrofs.unsigned i) (rs rv)) eqn:?; try discriminate.
      inv H.
      inversion H0.
      inversion inv_inject_neutral0.
      constructor.
      constructor.
    + erewrite Mem.nextblock_store; eauto.
    + erewrite Mem.nextblock_store; eauto. eapply Mem.store_inject_neutral; eauto.
      eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies.
    - eapply Mem.store_valid_access_3; eauto.
    - constructor.
      + apply nextinstr_nf_inject; auto.
        apply undef_regs_inject; auto.
        erewrite Mem.nextblock_store; eauto.
      + apply nextinstr_nf_wt.
        apply undef_regs_wt; auto.
  Qed.

End WITHMEM.

(* Step maintains well-typed invariant *)

Section WITHCONFIG2.
  Context `{compiler_config: ExternalCalls}
          `{Hmemx: !Mem.MemoryModelX mem}.

  Fixpoint builtin_preg_wt (r: builtin_res preg) (v: val) :=
    match r with
      BR r => Val.has_type v (typ_of_preg r)
    | BR_none => True
    | BR_splitlong hi lo => builtin_preg_wt hi (Val.hiword v) /\ builtin_preg_wt lo (Val.loword v)
    end.

  Lemma set_res_wt res:
    forall vres rs,
    builtin_preg_wt res vres ->
    wt_regset rs ->
    wt_regset (set_res res vres rs).
  Proof.
    induction res; simpl; intros; auto.
    - apply set_reg_wt; auto.
    - apply IHres2. apply H.
      apply IHres1. apply H. auto.
  Qed.

  Definition pair_wt p v :=
    match p with
      One r => Val.has_type v (typ_of_preg r)
    | Twolong rhi rlo =>
      Val.has_type (Val.hiword v) (typ_of_preg rhi) /\
      Val.has_type (Val.loword v) (typ_of_preg rlo)
    end.

  Lemma set_pair_wt:
    forall p res rs,
      wt_regset rs ->
      pair_wt p res ->
      wt_regset (set_pair p res rs).
  Proof.
    destruct p; simpl; intros.
    apply set_reg_wt; auto. destruct H0.
    apply set_reg_wt; auto. 
    apply set_reg_wt; auto.
  Qed.


  Context {exec_load exec_store}
          `{mem_acc: @MemAccessors _ _ exec_load exec_store}.

  Theorem step_wt ge rs m t rs' m':
    step ge (State rs m) t (State rs' m') ->
    wt_regset rs ->
    wt_regset rs'.
  Proof.
    intros H H0.
    inversion H; subst.
    + (* exec_instr *)
      eapply exec_instr_wt; eauto.
    + (* builtin *)
      apply nextinstr_nf_wt.
      apply set_res_wt.
      {
        generalize res vres. induction res0; simpl.
        destruct x, vres0; simpl; auto.  auto.
        split; auto.
      }
      apply undef_regs_wt.
      assumption.
    + (* external *)
      apply undef_reg_wt.
      apply set_reg_wt.
      {
        replace (typ_of_preg PC) with (typ_of_preg RA) by reflexivity.
        auto.
      }
      apply set_pair_wt; auto.
      apply external_call_well_typed in H9.
      revert H9.
      destruct (ef_sig ef). unfold proj_sig_res. simpl.
      unfold loc_external_result. unfold loc_result.
      destruct Archi.ptr64.
    - unfold loc_result_64. simpl.
      destruct sig_res; simpl.
      destruct t0; simpl; apply Val.has_subtype; reflexivity.
      apply Val.has_subtype; reflexivity.
    - unfold loc_result_32. simpl.
      destruct sig_res; simpl.
      destruct t0; simpl; try (apply Val.has_subtype; reflexivity).
      intro A; split; destruct res; simpl; auto.
      apply Val.has_subtype; reflexivity.
  Qed.

  Theorem star_wt ge s t s':
    star step ge s t s' ->
    forall rs m,
      s = State rs m ->
      wt_regset rs ->
      forall rs' m',
        s' = State rs' m' ->
        wt_regset rs'.
  Proof.
    induction 1.
    * intros rs m H H0 rs' m' H1.
      subst.
      inv H1.
      assumption.
    * intros rs m H2 H3 rs' m' H4.
      destruct s2.
      eapply IHstar; eauto.
      subst.
      eapply step_wt; eauto.
  Qed.

  Theorem plus_wt ge rs m t rs' m' :
    plus step ge (State rs m) t (State rs' m') ->
    wt_regset rs ->
    wt_regset rs'.
  Proof.
    intros H H0.
    inversion H; subst.
    destruct s2.
    match goal with
        K: step _ _ _ _ |- _ =>
        eapply step_wt in K; eauto
    end.
    match goal with
        K: star _ _ _ _ _ |- _ =>
        eapply star_wt in K; eauto
    end.
  Qed.

End WITHCONFIG2.