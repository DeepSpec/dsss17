Require Import LogicalRelations.
Require Import CompcertStructures.
Require Import OptionOrders.
Require Import SimulationRelation.
Require Import SimValues.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Local Opaque mwd_ops.

Global Instance leb_transport_eq_true x y:
  Transport Bool.leb x y (x = true) (y = true).
Proof.
  clear.
  destruct x, y; firstorder.
Qed.

Lemma volatile_block_is_global {F V} (ge: Genv.t F V) b:
  stencil_matches ge ->
  Genv.block_is_volatile ge b = Some true ->
  block_is_global b.
Proof.
  intros Hge.
  unfold Genv.block_is_volatile.
  destruct (Genv.find_var_info ge b) eqn:Hvi; try discriminate.
  intros _.
  eapply find_var_info_block_is_global; eauto.
Qed.

(* Some rewritings: explicitly use Mem.loadv, etc. *)

Module REWRITE.

  Inductive volatile_load {mem : Type}
            {memory_model_ops : Mem.MemoryModelOps mem}
            (ge : Senv.t)
  : memory_chunk -> mem -> block -> ptrofs -> trace -> val -> Prop :=
    volatile_load_vol : forall (chunk : memory_chunk)
                          (m : mem) (b : block) (ofs : ptrofs)
                          (id : ident) (ev : eventval)
                          (v : val),
      Senv.block_is_volatile ge b = Some true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_load ge chunk m b ofs
                    (Event_vload chunk id ofs ev :: nil)
                    (Val.load_result chunk v)
  | volatile_load_nonvol : forall (chunk : memory_chunk)
                             (m : mem) (b : block)
                             (ofs : ptrofs) (v : val),
      Senv.block_is_volatile ge b = Some false ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      volatile_load ge chunk m b ofs E0 v
  .
  
  Tactic Notation "funext_intro" ident(x) :=
    apply FunctionalExtensionality.functional_extensionality; intro x.

  Lemma volatile_load_eq: @Events.volatile_load = @volatile_load.
  Proof.
    apply (FunctionalExtensionality.functional_extensionality_dep
             (B := fun mem =>
                     Mem.MemoryModelOps mem ->
                     Senv.t -> memory_chunk -> mem ->
                     block -> ptrofs -> trace -> val -> Prop)).
    intro mem.
    (* TODO: find the good Ltac magic to enable `funext_intros ops ge chunk m b ofs t v.` *)
    funext_intro ops.
    funext_intro ge.
    funext_intro chunk.
    funext_intro m.
    funext_intro b.
    funext_intro ofs.
    funext_intro t.
    funext_intro v.
    apply ExtensionalityAxioms.prop_ext.
    split; inversion 1; subst; econstructor; eauto.
  Qed.

  Inductive extcall_memcpy_sem {mem : Type}
            {memory_model_ops : Mem.MemoryModelOps mem}
            (sz al : Z) (ge : Senv.t)
  : list val -> mem -> trace -> val -> mem -> Prop :=
    extcall_memcpy_sem_intro : forall vsrc vdst (m : mem)
                                      (bytes : list memval)
                                      (m' : mem),
                                 Mem.aligned_areav al sz m vsrc ->
                                 Mem.aligned_areav al sz m vdst ->
                                 Mem.disjoint_or_equalv sz m vsrc vdst ->
                                 Mem.loadbytesv m vsrc sz =
                                 Some bytes ->
                                 Mem.storebytesv m vdst bytes =
                                 Some m' ->
                                 extcall_memcpy_sem sz al ge
                                                    (vdst :: vsrc :: nil) m
                                                    E0 Vundef m'
  .

  Section WITHMEM.
    Context `{memory_model_prf: Mem.MemoryModelX}.

    Lemma extcall_memcpy_sem_eq:
      Events.extcall_memcpy_sem = extcall_memcpy_sem.
    Proof.
      funext_intro sz.
      funext_intro al.
      funext_intro ge.
      funext_intro chunk.
      funext_intro m.
      funext_intro t.
      funext_intro v.
      funext_intro m'.
      apply ExtensionalityAxioms.prop_ext.
      split; inversion 1; subst.
      {
        assert (Mem.range_perm m bsrc (Ptrofs.unsigned osrc)
                               (Ptrofs.unsigned osrc + sz) Cur Nonempty)
          as PERMSRC.
        {
          eapply Mem.range_perm_implies.
          { eapply Mem.loadbytes_range_perm; eauto. }
          constructor.
        }
        assert (Mem.range_perm m bdst (Ptrofs.unsigned odst)
                               (Ptrofs.unsigned odst + sz) Cur Nonempty)
          as PERMDST.
        {
          assert (sz = Z.of_nat (length bytes)).
          {
            exploit Mem.loadbytes_length; eauto.
            intro LEN. rewrite LEN.
            rewrite nat_of_Z_eq; auto.
          }
          subst sz.
          eapply Mem.range_perm_implies.
          { eapply Mem.storebytes_range_perm; eauto. }
          constructor.
        }
        econstructor; eauto.
        + unfold Mem.aligned_areav, Mem.aligned_area. auto.
        + unfold Mem.aligned_areav, Mem.aligned_area. auto.
        + unfold Mem.disjoint_or_equalv, Mem.disjoint_or_equal. auto.
      }
      destruct vsrc as [ | | | | | bsrc osrc ] ; try contradiction.
      destruct vdst as [ | | | | | bdst odst ] ; try contradiction.
      destruct H0 as (AL & AL_SZ & _ & ALIGNSRC).
      destruct H1 as (_ & _ & _ & ALIGNDST).
      destruct H2 as (NONNEG & _ & _ & DISJ_OR_EQ).
      econstructor; eauto.
      destruct (Z_eq_dec sz 0).
      {
        subst. exists 0. omega.
      }
      apply AL_SZ. omega.
    Qed.

  End WITHMEM.

End REWRITE.


Section EVENTS_REL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  Context `{ec1_ops: !ExternalCallsOps (mwd D1)}.
  Context `{ec2_ops: !ExternalCallsOps (mwd D2)}.

  Context `{cc1_ops: !EnableBuiltins (mwd D1)}.
  Context `{cc2_ops: !EnableBuiltins (mwd D2)}.

Lemma match_global_block_eq p b1 b2:
  block_is_global b1 ->
  match_block R p b1 b2 ->
  b1 = b2.
Proof.
  intros Hb1 Hb.
  eapply match_block_functional; eauto.
  eapply match_global_block; eauto.
Qed.

Lemma match_global_ptrbits_eq p b1 ofs1 b2 ofs2:
  block_is_global b1 ->
  match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
  (b1, ofs1) = (b2, ofs2).
Proof.
  intros Hb1 Hptr.
  eapply (match_ptrbits_functional p); eauto.
  eapply match_ptr_ptrbits_unsigned.
  eapply match_global_ptr.
  assumption.
Qed.

Definition senv_le {F V} Rf :=
  ((genv_le Rf) !! (@Genv.to_senv F V))%rel.

Global Instance genv_to_senv_le {F V} Rf:
  Monotonic (@Genv.to_senv F V) (@genv_le F V Rf ++> @senv_le F V Rf).
Proof.
  unfold senv_le; rauto.
Qed.

Global Instance genv_to_senv_le_params:
  Params (@Genv.to_senv) 1.

Global Instance senv_public_symbol_leb {F V} R0:
  Monotonic (@Senv.public_symbol) (@senv_le F V R0 ++> - ==> Bool.leb).
Proof.
  intros. rstep. rstep. inv H. simpl. rauto.
Qed.

Global Instance senv_find_symbol_le {F V} R0:
  Monotonic (@Senv.find_symbol) (@senv_le F V R0 ++> - ==> option_le eq).
Proof.
  intros. rstep. rstep. inv H. simpl. rauto.
Qed.

Global Instance eventval_match_match F V Rf p:
  Monotonic
    (@eventval_match)
    (@senv_le F V Rf ++> - ==> - ==> set_rel (match_val R p)).
Proof.
  intros x y GLE v v0.
  intros v' EM.
  inv EM; try (eexists; split; constructor; auto).
  - eapply leb_transport_eq_true. eapply senv_public_symbol_leb. rauto. auto.
  - eapply senv_find_symbol_le  in GLE.
    specialize (GLE id). rewrite H0 in GLE. inv GLE. eauto. 
  - eapply match_ptr_ptrbits_unsigned.
    eapply match_global_ptr; eauto.
    inv GLE. simpl in H0. rewrite stencil_matches_symbols in H0; eauto.
Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @eventval_match : typeclass_instances.

  (** Occasionally, we obtain the target value through some other
    mean, and transporting an [eventval_match] property would produce
    a duplicate. In these cases we use [revert] to exclude the
    hypothesis in question from [transport_hyps], then use the
    following properties instead to show that the hypothesis on the
    old value implies the conclusion on the new one. *)

  Global Instance eventval_match_match' F V Rf p:
    Monotonic
      (@eventval_match)
      (@senv_le F V Rf ++> - ==> - ==> match_val R p ++> impl).
  Proof.
    intros x y GLE ev t v v0 MV EM.
    destruct GLE as [ge1 ge2 GLE].
    inv EM; inv MV; try (econstructor; eauto).
    eapply match_global_ptrbits_eq in H4; eauto.
    inversion H4; clear H4; subst.
    constructor; eauto.
    - transport H.
      assumption.
    - simpl in *.
      eapply genv_find_symbol_le  in GLE.
      specialize (GLE id). rewrite H0 in GLE. inv GLE. eauto.
  Qed.

  Global Instance eventval_list_match_match' F V Rf p:
    Monotonic
      (@eventval_list_match)
      (@senv_le F V Rf ++> - ==> - ==> list_rel (match_val R p) ++> impl).
  Proof.
    intros ge1 ge2 Hge evl tyl vl1 vl2 Hvl H.
    revert vl2 Hvl.
    induction H; intros vl2 Hvl.
    - inverse_hyps.
      constructor.
    - inverse_hyps.
      constructor; eauto.
      revert H. eapply eventval_match_match'; eauto.
  Qed.

  (** We replace the property for [block_is_volatile] declared in
    [CompcertStructures] by the following one, which uses
    [match_block]. Should this be in [SimulationRelation]? *)

  Global Instance block_is_volatile_match F V Rf p:
    Monotonic
      (@Senv.block_is_volatile)
      (@senv_le F V Rf ++> match_block R p ++> option_le eq).
  Proof.
    intros x y Hge b1 b2 Hb.
    destruct Hge as [ge1 ge2 Hge]. simpl.
    unfold Genv.block_is_volatile in *.
    generalize (genv_find_var_info_le _ _ _ Hge b1).
    destruct (Genv.find_var_info ge1 b1) eqn:VAR.
    - intro A; inv A. inv H0.
      assert (b1 = b2).
      exploit (find_var_info_block_is_global ge1); eauto.
      intro GLOB.
      exploit (match_global_block p b1); eauto.
      intro Hb_.
      generalize (match_block_functional _ _ _ _ Hb Hb_).
      intro; subst; auto. subst; rewrite <- H1; constructor. auto.
    - constructor.
  Qed.

  (** ** Semantics of volatile memory accesses *)

  Global Instance match_ptrbits_block' p:
    Related ((match_ptrbits R p) !! fst)%rel (match_block R p) subrel.
  Proof.
    rstep. red. intros. inv H. destruct x0, y0; simpl; eapply match_ptrbits_block; eauto.
  Qed.

  Hint Extern 0 (Transport _ _ _ (eventval_match _ _ _ _) _) =>
    eapply impl_transport : typeclass_instances.

  Lemma senv_find_symbol_block_is_global {F V} R0 (ge ge': Senv.t) i b:
    @senv_le F V R0 ge ge' ->
    Senv.find_symbol ge i = Some b ->
    block_is_global b.
  Proof.
    intros Hge Hb. inv Hge. simpl in *.
    simpl in Hb; rewrite stencil_matches_symbols in Hb; eauto.
  Qed.

  Lemma senv_find_symbol_block_is_global2 {F V} R0 (ge ge': Senv.t) i b:
    @senv_le F V R0 ge ge' ->
    Senv.find_symbol ge' i = Some b ->
    block_is_global b.
  Proof.
    intros Hge Hb. inv Hge. simpl in *.
    simpl in Hb; rewrite stencil_matches_symbols in Hb; eauto.
  Qed.

  
  Global Instance volatile_load_match F V Rf p:
    Monotonic
      volatile_load
      (@senv_le F V Rf ++> - ==> match_mem R p ++> % match_ptrbits R p ++> - ==>
       set_rel (match_val R p)).
  Proof.
    intros ge1 ge2 Hge chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr t.
    simpl.
    assert (match_block R p b1 b2) by eauto using match_ptrbits_block.
    intros a VLOAD.
    inv VLOAD.
    - eapply match_global_ptrbits_eq in Hptr; eauto.
      inversion Hptr; clear Hptr; subst.
      simpl in *.
      transport H1. subst. transport H0. subst.
      transport H2.
      eexists; split.
      + eapply volatile_load_vol; eauto. 
      + rauto.
      + eapply senv_find_symbol_block_is_global in H1; eauto.
    - transport H0. subst.
      assert (PERM : Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur Readable).
      generalize (Mem.load_valid_access _ _ _ _ _ H1). intros (RP & _).
      apply RP. destruct chunk; simpl; omega.
      (* automatize? *)
      eapply transport in H1. Focus 2.
      rstep. rauto. rauto.
      apply (match_ptrbits_ptr _ _ _ _ _ _ _ Readable Hm Hptr PERM).
      split_hyp H1.
      eexists; split.
      eapply volatile_load_nonvol; eauto.
      assumption.
  Qed.

  Instance volatile_load_match_params: Params (@volatile_load) 7.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @Events.volatile_load : typeclass_instances.
  
  Hint Resolve senv_find_symbol_block_is_global
       senv_find_symbol_block_is_global2.
  
  Global Instance volatile_store_match {F V} p:
    Monotonic volatile_store
      (rel_all (fun Rf => @senv_le F V Rf ++>
       - ==> match_mem R p ++> rel_curry (match_ptrbits R p ++> match_val R p ++> - ==>
       set_rel (incr p (match_mem R p))))).
  Proof.
    intros RF ge1 ge2 Hge.
    intros chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv t.
    simpl.
    intros m1' Hm1'.
    destruct Hm1'.
    - simpl in *.
      transport H0. subst.
      transport H. subst.
      transport H1.
      eapply match_global_ptrbits_eq in Hptr; eauto.
      inversion Hptr; clear Hptr; subst.
      assert (match_block R p b2 b2) by (eapply match_global_block; eauto).
      eexists; split.
      + constructor; eauto.
      + rauto.
    - assert (match_block R p b b2) by eauto using match_ptrbits_block.
      eapply match_ptrbits_ptr in Hptr; eauto.
      + simpl in *. transport H. subst.
        transport H0.
        eexists; split.
        * constructor; eauto.
        * reexists; rauto.
      + eapply Mem.store_valid_access_3; eauto.
        pose proof (size_chunk_pos chunk).
        omega.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @volatile_store : typeclass_instances.

  (** * Semantics of external functions *)

  Definition extcall_sem_match {F V} p:
    rel (extcall_sem (mem := mwd D1)) (extcall_sem (mem := mwd D2)) :=
    (
      rforall Rf, @senv_le F V Rf ++>
     list_rel (match_val R p) ++> match_mem R p ++>
     - ==>
     rel_curry (set_rel (incr p (match_val R p * match_mem R p))))%rel.

  (** A dedicated [RElim] instance might be better than the following
    hint (in that it would accelerate the resolution and reduce the
    size of the generated proof terms), but it would be messy to declare. *)
  Hint Extern 1 (RElim (extcall_sem_match _) _ _ _ _) =>
    unfold extcall_sem_match : typeclass_instances.

  Global Instance volatile_load_sem_match {F V} p:
    Monotonic volatile_load_sem
      (- ==> @extcall_sem_match F V p).
  Proof.
    intros chunk Rf ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t.
    intros [vres1 m1'] H; simpl in H.
    destruct H.
    inverse_hyps.
    transport_hyps.
    eexpair; split.
    - econstructor; eauto.
    - rauto.
  Qed.

  Instance volatile_store_match_params: Params (@volatile_store) 8.
  
  Global Instance volatile_store_sem_match {F V} p:
    Monotonic
      volatile_store_sem
      (- ==> @extcall_sem_match F V p).
  Proof.
    intros chunk Rf ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t.
    intros [vres1 m1'] H; simpl in H.
    destruct H.
    inverse_hyps.
    transport_hyps.
    eexpair; split.
    - econstructor; eauto.
    - eexists; split; rauto.
  Qed.

  Lemma match_val_vptrofs_inv:
    forall p ofs y,
      match_val R p (Vptrofs ofs) y ->
      y = Vptrofs ofs.
  Proof.
    unfold Vptrofs.
    destruct Archi.ptr64 eqn:?; inversion 1; auto.
  Qed.

  Global Instance extcall_malloc_sem_match {F V} p:
    Monotonic
      extcall_malloc_sem
      (@extcall_sem_match F V p).
  Proof.
    intros Rf ge1 ge2 _ vargs1 vargs2 Hvargs m1 m2 Hm t.
    intros [vres1 m1'] H; simpl in H.
    destruct H.
    edestruct (simrel_alloc p _ _ Hm) as (p' & Hp & Halloc).
    inverse_hyps. transport H.
    assert (match_ptr R p' (b, -size_chunk Mptr) (x0, -size_chunk Mptr)).
    {
      eapply match_block_sameofs_ptr; eauto.
    }
    transport H0.
    eexpair; split.
    - eapply match_val_vptrofs_inv in H3. subst. econstructor; eauto.
    - exists p'';split; auto.
      rauto.
      split; simpl; auto.
      constructor. apply match_block_sameofs_ptrbits; rauto.
  Qed.

  Global Instance extcall_free_sem_match {F V} p:
    Monotonic
      extcall_free_sem
      (@extcall_sem_match F V p).
  Proof.
    intros Rf ge1 ge2 _ vargs1 vargs2 Hvargs m1 m2 Hm t.
    intros [vres1 m1'] H; simpl in H.
    destruct H.
    inverse_hyps.
    assert (match_ptr R p (b, Ptrofs.unsigned lo - size_chunk Mptr) (b2, Ptrofs.unsigned ofs2 - size_chunk Mptr)).
    {
      eapply match_ptr_shift.
      eapply match_ptrbits_ptr; eauto.
      eapply Mem.free_range_perm; eauto.
      generalize (size_chunk_pos Mptr); omega.
    }

    Ltac t H tac :=
      match type of H with
        ?A -> ?B =>
        let x := fresh in
        assert (x: A); [ clear H; tac | specialize (H x); clear x ]
      end.

    transport H.
    generalize (match_ptr_ptrrange
                  p b
                  (Ptrofs.unsigned lo - size_chunk Mptr)
                  (Ptrofs.unsigned lo + Ptrofs.unsigned sz)
                  b2
                  (Ptrofs.unsigned ofs2 - size_chunk Mptr)
                  (Ptrofs.unsigned ofs2 + Ptrofs.unsigned sz)
                  H2).
    intro A.
    t A omega.
    transport H1.
    eexpair; split.
    - econstructor; eauto.
      apply match_val_vptrofs_inv in H4; subst. auto.
    - rauto.
  Qed.

  Global Instance extcall_memcpy_sem_match {F V} p:
    Monotonic
      extcall_memcpy_sem
      (- ==> - ==> @extcall_sem_match F V p).
  Proof.
    repeat rewrite REWRITE.extcall_memcpy_sem_eq.
    intros sz al Rf ge1 ge2 _ vargs1 vargs2 Hvargs m1 m2 Hm t.
    intros [vres1 m1'] H; simpl in H.
    destruct H.
    inverse_hyps.
    (* why the following are not automatic? *)
     eapply simrel_aligned_areav in H; eauto.
     eapply simrel_aligned_areav in H0; eauto.
     eapply simrel_disjoint_or_equalv in H1; eauto.
     transport H2. transport H3.
    eexpair; split.
    - econstructor; eauto.
    - solve_monotonic.
  Qed.

  Global Instance extcall_annot_sem_match {F V} p:
    Monotonic
      extcall_annot_sem
      (- ==> - ==> @extcall_sem_match F V p).
  Proof.
    intros text targs Rf ge1 ge2 Hge vs1 vs2 Hvs m1 m2 Hm t.
    intros [vres1 m1'] H; simpl in H.
    destruct H.
    eexpair; split.
    - econstructor; eauto.
      revert H.
      eapply eventval_list_match_match'; eauto.
    - reexists; rauto.
  Qed.

  Global Instance extcall_annot_val_sem_match {F V} p:
    Monotonic
      extcall_annot_val_sem
      (- ==> - ==> @extcall_sem_match F V p).
  Proof.
    intros text targs Rf ge1 ge2 Hge vs1 vs2 Hvs m1 m2 Hm t.
    intros [vres1 m1'] H; simpl in H.
    destruct H.
    inverse_hyps.
    eexpair; split.
    - econstructor; eauto.
      revert H.
      eapply eventval_match_match'; eauto.
    - solve_monotonic.
  Qed.

  Global Instance extcall_debug_sem_match {F V} p:
    Monotonic
      extcall_debug_sem
      (@extcall_sem_match F V p).
  Proof.
    intros Rf ge1 ge2 Hge vs1 vs2 Hvs m1 m2 Hm t.
    intros [vres1 m1'] H; simpl in H.
    destruct H.
    eexpair; split.
    - econstructor; eauto.
    - solve_monotonic.
  Qed.

  Lemma builtin_external_call_match {F V} p ef:
    cc_enable_external_as_builtin (mem := mwd D1) = false ->
    (forall id sg (ge: Senv.t) vargs m t vres m',
       ~ inline_assembly_sem (mem := mwd D1) id sg ge vargs m t vres m') ->
    builtin_enabled (mem := mwd D1) ef ->
    Monotonic
      builtin_functions_sem
      (- ==> - ==> @extcall_sem_match F V p) ->
    Monotonic
      runtime_functions_sem
      (- ==> - ==> @extcall_sem_match F V p) ->
    Monotonic (external_call ef)
      (@extcall_sem_match F V p).
  Proof.
    intros Hbd Hinl Hef Hbf Hrf.
    destruct ef; simpl in *.
    - rewrite Hbd in Hef. elim Hef.
    - eapply Hbf.
    - eapply Hrf.
    - apply volatile_load_sem_match. (* solve_monotonic. *)
    - apply volatile_store_sem_match. (* solve_monotonic. *)
    - apply extcall_malloc_sem_match. (* solve_monotonic. *)
    - apply extcall_free_sem_match. (* solve_monotonic. *)
    - apply extcall_memcpy_sem_match. (* solve_monotonic. *)
    - apply extcall_annot_sem_match. (* solve_monotonic. *)
    - apply extcall_annot_val_sem_match. (* solve_monotonic. *)
    - repeat intro.
      destruct a0; simpl in *.
      eelim Hinl; eauto.
    - apply extcall_debug_sem_match.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    rel_curry_set_rel_transport @external_call : typeclass_instances.

  (* TODO: move in SimValues *)
  Global Instance val_offset_ptr_match p:
    Monotonic Val.offset_ptr (match_val R p ++> - ==> match_val_of_type R p Tptr).
  Proof.
    repeat rstep. unfold Tptr, Val.offset_ptr.
    repeat rstep.
    destruct Archi.ptr64 eqn:?; constructor; auto.
    eapply match_ptrbits_shift; eauto.
    eapply match_ptrbits_shift; eauto.
    destruct Archi.ptr64 eqn:?; constructor; auto.
  Qed.

  Global Instance offset_ptr_params: Params Val.offset_ptr 2.

  Global Instance symbol_offset_match {F V} Rf p:
    Monotonic
      (@Genv.symbol_address F V)
      (@genv_le F V Rf ++> - ==> - ==> match_val_of_type R p Tptr).
  Proof.
    unfold Genv.symbol_address.
    pose proof (genv_find_symbol_match (F:=F) (V:=V) (Rf:=Rf) p).
    Set Printing Coercions.
    repeat red. intros.
    repeat rstep.
    unfold Tptr.
    destruct Archi.ptr64 eqn:ARCHI; constructor; auto;
      eapply match_block_sameofs_ptrbits; eauto.
  Qed.

  Global Instance senv_find_symbol_match {F V Rf} p:
    Monotonic
      (@Senv.find_symbol)
      (@senv_le F V Rf ++> - ==> option_rel (match_block_sameofs R p)).
  Proof.
    intros ge1 ge2 Hge i.
    inv Hge. simpl. rewrite !stencil_matches_symbols by eauto.
    destruct (find_symbol i) eqn:Hi.
    - constructor.
      eapply match_global_block_sameofs.
      eapply find_symbol_block_is_global.
      eassumption.
    - constructor.
  Qed.

  Global Instance senv_symbol_address_match {F V} Rf p:
    Monotonic
      (@Senv.symbol_address)
      (@senv_le F V Rf ++> - ==> - ==> match_val_of_type R p Tptr).
  Proof.
    unfold Senv.symbol_address.
    repeat red. intros.
    repeat rstep.
    unfold Tptr.
    destruct Archi.ptr64 eqn:ARCHI; constructor; auto;
      eapply match_block_sameofs_ptrbits; eauto.
  Qed.

  Lemma eval_builtin_arg_rel {A F V} Rf:
    Related
      (eval_builtin_arg (mem := mwd D1) (A:=A))
      (eval_builtin_arg (mem := mwd D2) (A:=A))
      (rforall p, senv_le (F:=F) (V:=V) Rf
                          ++> ( - ==> match_val R p)
                          ++> match_val R p
                          ==> match_mem R p
                          ==> -
                  ==> set_rel (match_val R p)).
  Proof.
    repeat red.
    intros c ge1 ge2 Hge rs1 rs2 Hrs sp1 sp2 Hsp m1 m2 Hm.
    induction 1; intros; try (eexists; split; [constructor| rauto]).
    - transport H.
      eexists; split. constructor. eauto. auto.
    - transport H. 
      eexists; split. constructor. eauto. auto.
    - split_hyp IHeval_builtin_arg1. split_hyp IHeval_builtin_arg2.
      eexists; split. constructor. eauto. eauto. 
      rauto.
  Qed.

  Global Instance eval_builtin_arg_params:
    Params (@eval_builtin_arg) 6.

  Lemma eval_builtin_args_rel {A F V} Rf:
    Related
      (eval_builtin_args (mem := mwd D1) (A:=A))
      (eval_builtin_args (mem := mwd D2) (A:=A))
      (rforall p, senv_le (F:=F) (V:=V) Rf
                          ++> ( - ==> match_val R p)
                          ++> match_val R p
                          ++> match_mem R p
                          ++> list_rel eq
                          ==> set_rel (list_rel (match_val R p))).
  Proof.
    repeat red.
    intros c ge1 ge2 Hge rs1 rs2 Hrs sp1 sp2 Hsp m1 m2 Hm.
    induction 1.
    simpl. inversion 1. subst. eexists; split; constructor.
    subst. inversion 1. subst.
    eapply eval_builtin_arg_rel in H3; eauto. split_hyp H3.
    eapply IHlist_rel in H5. split_hyp H5.
    eexists; split; econstructor; eauto.
  Qed.

  Global Instance eval_builtins_args_params:
    Params (@eval_builtin_args) 6.

End EVENTS_REL.

Hint Extern 10 (Transport _ _ _ _) =>
  eapply impl_transport : typeclass_instances.

Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry_set_rel_transport @external_call : typeclass_instances.
