Require Import Coqlib.
Require Export liblayers.compcertx.CompcertStructures.
Require Export compcertx.common.MemoryX. (* for storebytes_empty *)
Require Import LogicalRelations.
Require Import PTrees.
Require Import SimulationRelation.
Require Import Ctypes.
Require Import Clight.

Require Import Globalenvs.
Require Import Events.
Require Import OptionOrders.
Require Import SimEvents.
Require Import SimCompCertBuiltins.
Require Import SimCop.

Require Import Program.Basics.

Local Opaque mwd_ops.

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

Lemma call_cont_is_call_cont_id:
  forall kframe, is_call_cont kframe ->
                 call_cont kframe = kframe.
Proof.
  induction kframe; eauto; inversion 1; subst; eauto.
Qed.

Lemma call_cont_frame:
  forall kframe, is_call_cont kframe ->
                 forall k, call_cont (frame_cont kframe k) = frame_cont kframe (call_cont k).
Proof.
  induction k; simpl; eauto using call_cont_is_call_cont_id.
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

Context {mem} `{ec_ops: ExternalCallsOps mem}.
Context `{eb_ops: !EnableBuiltins mem}.

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
      Smallstep.star step2 ge s t s' ->
      Smallstep.star step2 ge (frame_state_cont kframe s) t (frame_state_cont kframe s').
Proof.
  induction 2; econstructor; eauto.
  eapply step_frame_cont; eauto.
Qed.

Corollary plus2_frame_cont:
  forall kframe,
    is_call_cont kframe ->
    forall ge s t s',
      Smallstep.plus step2 ge s t s' ->
      Smallstep.plus step2 ge (frame_state_cont kframe s) t (frame_state_cont kframe s').
Proof.
  inversion 2; subst; econstructor; eauto using star2_frame_cont.
  apply step_frame_cont; auto.
Qed.

End WITHCONFIGOPS.

Section CLIGHT_REL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  Inductive clight_genv_le Rf: rel genv genv :=
    | Build_genv_le:
        Monotonic
          (@Build_genv)
          (genv_le Rf ++> - ==> clight_genv_le Rf).

  Global Existing Instance Build_genv_le.

  Global Instance genv_genv_le Rf:
    Monotonic
      (@genv_genv)
      (clight_genv_le Rf ++> genv_le Rf).
  Proof.
    unfold genv_genv.
    rauto.
  Qed.

  Global Instance genv_cenv_le Rf:
    Monotonic
      (@genv_cenv)
      (clight_genv_le Rf ++> eq).
  Proof.
    unfold genv_cenv.
    rauto.
  Qed.

  (* May be needed:
  Global Instance clight_globalenv_le Rf:
    Monotonic
      (@globalenv)
      (program_le Rf ==> clight_genv_le Rf).
  *)

  (** NB: we have to use [option_rel] here not [option_le], because
    otherwise it is difficult to state the monotonicity property of
    [blocks_of_env] (we would have to introduce some kind of "subset"
    list relator) *)
  Definition env_match p: rel env env :=
    ptree_rel (option_rel (match_block_sameofs R p * @eq type))%rel.

  (** FIXME: need general theorem about ptree_rel *)
  Global Instance empty_env_match p:
    Monotonic (@empty_env) (env_match p).
  Proof.
    solve_monotonic.
    unfold env_match, empty_env.
    intros i.
    rewrite PTree.gempty.
    constructor.
  Qed.

  Global Instance env_match_le:
    Monotonic
      (@env_match)
      ((≤) ++> subrel).
  Proof.
    unfold env_match.
    solve_monotonic.
  Qed.

  Definition temp_env_match p: rel temp_env temp_env :=
    ptree_rel (option_le (match_val R p)).

  Global Instance temp_env_match_le:
    Monotonic
      temp_env_match
      ((≤) ++> subrel).
  Proof.
    unfold temp_env_match.
    solve_monotonic.
  Qed.

  Global Instance: Params (@temp_env_match) 3.

  Global Instance deref_loc_match p:
    Monotonic
      deref_loc
      (- ==> match_mem R p ++> % match_ptrbits R p ++> set_rel (match_val R p)).
  Proof.
    solve_monotonic.
    intros a H1.
    assert (match_val R p (Vptr (fst x1) (snd x1)) (Vptr (fst y0) (snd y0))) as VAL.
    {
      econstructor.
      destruct x1; destruct y0; assumption.
    }
    inversion H0; subst.
    repeat red.
    simpl in * |- * .
    inversion H1; subst; eauto using @deref_loc_reference, @deref_loc_copy.
    generalize (simrel_loadv _ chunk _ _ H _ _ VAL).
    rewrite H4.
    inversion 1; subst.
    symmetry in H7.
    eauto using @deref_loc_value.
  Qed.

  Global Instance: Params (@deref_loc) 5.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @deref_loc : typeclass_instances.

  (** [assign_loc] is somewhat involved. *)

  Lemma assign_loc_match_alignof_blockcopy p m1 m2 b1 ofs1 b2 ofs2 env ty:
    match_mem R p m1 m2 ->
    match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
    sizeof env ty > 0 ->
    Mem.range_perm m1 b1 (Ptrofs.unsigned ofs1) (Ptrofs.unsigned ofs1 + sizeof env ty) Cur Nonempty ->
    (alignof_blockcopy env ty | Ptrofs.unsigned ofs1) ->
    (alignof_blockcopy env ty | Ptrofs.unsigned ofs2).
  Proof.
    intros Hm Hptr Hsz Hperm H.
    inv Hptr.
    erewrite (simrel_address_inject p); eauto.
    eapply (simrel_aligned_area_inject p); eauto.
    + eapply alignof_blockcopy_1248.
    + eapply sizeof_alignof_blockcopy_compat.
    + eapply Hperm.
      omega.
  Qed.

  Global Instance assign_loc_match Rf p:
    @Monotonic
      (forall ge : genv, let ce := genv_cenv ge in _)
      assign_loc
      (clight_genv_le Rf ++>
       - ==> match_mem R p ++> % match_ptrbits R p ++> match_val R p ++>
       set_rel (incr p (match_mem R p))).
  Proof.
    intros ge1 ge2 Hge ty m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv m1' Hm1'.
    destruct Hm1' as [b1 ofs1 v1 m1' | b1 ofs1 b1' ofs1' bytes1 m1'].
    - transport_hyps.
      eexists; split; [ | rauto].
      eapply assign_loc_value; eauto.
    - assert
        (sizeof ge1 ty > 0 ->
         Mem.range_perm m1 b1
           (Ptrofs.unsigned ofs1)
           (Ptrofs.unsigned ofs1 + sizeof ge1 ty)
           Cur Nonempty).
      {
        intro.
        eapply Mem.range_perm_implies.
        + replace (sizeof _ _) with (Z.of_nat (length bytes1)).
          * eapply Mem.storebytes_range_perm; eauto.
          * erewrite (Mem.loadbytes_length m1) by eauto.
            apply nat_of_Z_eq.
            omega.
        + constructor.
      }
      assert
        (sizeof ge1 ty > 0 ->
         Mem.range_perm m1 b1'
           (Ptrofs.unsigned ofs1')
           (Ptrofs.unsigned ofs1' + sizeof ge1 ty)
           Cur Nonempty).
      {
        intro.
        eapply Mem.range_perm_implies.
        + eapply Mem.loadbytes_range_perm; eauto.
        + constructor.
      }
      simpl.
      destruct Hge; simpl in *.
      inv Hv.
      change (Mem.loadbytesv m1 (Vptr b1' ofs1') (sizeof a ty) = Some bytes1) in H3.
      change (Mem.storebytesv m1 (Vptr b1 ofs1) bytes1 = Some m1') in H4.
      transport_hyps.
      eexists; split; [eapply assign_loc_copy | ]; simpl.
      + assumption.
      + eauto using assign_loc_match_alignof_blockcopy.
      + eauto using assign_loc_match_alignof_blockcopy.
      + destruct (decide (sizeof a ty = 0)) as [Hsz | Hsz].
        {
          rewrite Hsz.
          right.
          omega.
        }
        assert (Hsz' : sizeof a ty > 0).
        {
          pose proof (sizeof_pos a ty).
          omega.
        }
        inv Hptr.
        inv H11.
        erewrite !(simrel_address_inject p); eauto.
        eapply (simrel_disjoint_or_equal_inject p); eauto.
        * intros ofs Hofs.
          eapply Mem.perm_cur_max.
          eapply H6; eauto.
        * intros ofs Hofs.
          eapply Mem.perm_cur_max.
          eapply H5; eauto.
        * eapply H5; eauto.
          omega.
        * eapply H6; eauto.
          omega.
      + eassumption.
      + eassumption.
      + rauto.
  Qed.

  Global Instance: Params (@assign_loc) 7.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @assign_loc : typeclass_instances.

  Global Instance alloc_variables_match Rf p:
    Monotonic
      alloc_variables
      (clight_genv_le Rf ++>
       env_match p ++>
       match_mem R p ++>
       - ==>
       % set_rel (incr p (env_match p * match_mem R p))).
  Proof.
    intros ge1 ge2 Hge e1 e2 Henv m1 m2 Hm vars [e1' m1'] H.
    revert H p e2 m2 Henv Hm.
    simpl.
    induction 1 as [e1 m1 | e1 m1 id ty vars m1' b1 m1'' e1'' Hm1' Hm1'' IH].
    - intros.
      exists (e2, m2).
      split.
      + constructor.
      + exists p.
        split; [ reflexivity | ].
        split; eauto.
    - intros.
      edestruct (simrel_alloc p m1 m2 Hm 0 (sizeof ge1 ty)) as (p' & Hp' & Hm' & Hb); eauto.
      destruct (Mem.alloc m2 0 (sizeof ge1 ty)) as [m2' b2] eqn:Hm2'.
      rewrite Hm1' in *; simpl in *.
      specialize (IH p' (PTree.set id (b2, ty) e2) m2').
      edestruct IH as ((e2'' & m2'') & Hvars & p'' & He'' & Hm''); eauto.
      {
        (** We only have [ptree_set_le], we would need support for
          multiple instances to declare [ptree_set_rel] as well. *)
        unfold env_match in *.
        intro j.
        destruct (Decision.decide (j = id)); subst.
        - rewrite !PTree.gss.
          constructor.
          split; eauto.
        - rewrite !PTree.gso by assumption.
          rauto.
      }
      eexists (e2'', m2'').
      split.
      + simpl.
        econstructor; eauto.
        destruct Hge; simpl in *.
        assumption.
      + exists p''.
        split.
        * etransitivity; eauto.
        * assumption.
  Qed.

  Global Instance: Params (@alloc_variables) 6.

  Global Instance bind_parameters_match Rf p:
    Monotonic
      bind_parameters
      (clight_genv_le Rf ++>
       env_match p ++>
       match_mem R p ++>
       - ==>
       list_rel (match_val R p) ++>
       set_rel (incr p (match_mem R p))).
  Proof.
    intros ge1 ge2 Hge e1 e2 He m1 m2 Hm vars vl1 vl2 Hvl m1' H.
    revert H p He vl2 m2 Hvl Hm.
    induction 1 as [m1 | m1 id ty params v1 vl1 b1 m1' m1'' Hb1 Hm1' Hm1'' IH].
    - intros.
      exists m2.
      split; eauto; try now solve_monotonic.
      inversion Hvl; subst.
      constructor.
    - intros.
      generalize He. intro He_.
      specialize (He id).
      pose proof (fun m: mwd D2 => bind_parameters_cons ge2 e2 m id) as Hbp_cons.
      destruct He as [[xb1 xty] [b2 yty] [Hb Hty] | ]; try discriminate.
      simpl in *.
      inversion Hb1; clear Hb1.
      repeat subst.
      inversion Hvl as [ | xv1 v2 Hv xvl1 vl2' Hvl']; subst.
      generalize (match_block_sameofs_ptrbits _ _ Ptrofs.zero _ _ Hb Logic.eq_refl). intro PTR.
      transport_hyps.
      subst.
      edestruct (IH p') as (m2'' & Hm2'' & Hm''); eauto.
      (* TODO: incr, transitivity *)
      + eapply env_match_le; eauto.
      + eapply list_subrel; eauto.
        solve_monotonic.
      + destruct Hm'' as (? & ? & ?).
        esplit.
        split; eauto.
        solve_monotonic.
  Qed.

  Global Instance: Params (@bind_parameters) 6.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @bind_parameters : typeclass_instances.

  Global Instance create_undef_temps_match p:
    Monotonic
      (@create_undef_temps)
      (- ==> temp_env_match p).
  Proof.
    intros temps.
    induction temps as [ | [id t] temps IHtemps]; simpl; solve_monotonic.
  Qed.

  Global Instance bind_parameter_temps_match p:
    Monotonic
      (@bind_parameter_temps)
      (- ==>
       list_rel (match_val R p) ++>
       temp_env_match p ++>
       option_rel (temp_env_match p)).
  Proof.
    intros formals args1 args2 Hargs.
    revert formals.
    induction Hargs as [ | v1 v2 Hv args1 args2 Hargs IH].
    - intros [|]; simpl; intros; solve_monotonic.
    - intros [| [id t] formals]; simpl; solve_monotonic.
      eapply IH.
      solve_monotonic.
  Qed.

  Global Instance block_of_binding_match Rf p:
    Monotonic
      (@block_of_binding)
      (clight_genv_le Rf ++> eq * (match_block_sameofs R p * eq) ++>
       match_block_sameofs R p * eq * eq).
  Proof.
    intros ge1 ge2 Hge (id1 & b1 & ty1) (id2 & b2 & ty2) (Hid & Hb & Hty).
    simpl in *.
    solve_monotonic.
    destruct Hge; simpl; congruence.
  Qed.

  Section LOCALS.
    Local Instance blocks_of_env_match_strong Rf p:
      Monotonic
        (@blocks_of_env)
        (clight_genv_le Rf ++> env_match p ++>
         list_rel (match_block_sameofs R p * eq * eq)).
    Proof.
      unfold blocks_of_env.
      solve_monotonic.
    Qed.

    Local Instance match_blocks_sameofs_ptrrange p:
      Related
        (match_block_sameofs R p * eq * eq)%rel
        (match_ptrrange R p)
        subrel.
    Proof.
      repeat red.
      inversion 1; subst.
      inversion H0; subst.
      destruct x as [ [ ? ? ] ? ].
      destruct y as [ [ ? ? ] ? ].
      simpl in * |- * .
      subst.
      replace z2 with (z1 + (z2 - z1))%Z by omega.
      constructor.
      apply match_block_sameofs_ptr; auto.
    Qed.

    Global Instance blocks_of_env_match_weak Rf p:
      Monotonic
        (@blocks_of_env)
        (clight_genv_le Rf ++> env_match p ++> list_rel (match_ptrrange R p)).
    Proof.
      solve_monotonic.
    Qed.
  End LOCALS.

  Global Instance set_opttemp_match p:
    Monotonic
      (@set_opttemp)
      (- ==>
       match_val R p ++>
       temp_env_match p ++>
       temp_env_match p).
  Proof.
    unfold set_opttemp.
    solve_monotonic.
  Qed.

  (** [select_switch_default], [select_switch_case], [select_switch]
    and [seq_of_label_statement] are entierly about syntax. *)
  Lemma eval_expr_lvalue_match Rf p:
    forall ge1 ge2, clight_genv_le Rf ge1 ge2 ->
    forall e1 e2, env_match p e1 e2 ->
    forall le1 le2, temp_env_match p le1 le2 ->
    forall m1 m2, match_mem R p m1 m2 ->
    (forall expr v1,
       eval_expr ge1 e1 le1 m1 expr v1 ->
       exists v2,
         eval_expr ge2 e2 le2 m2 expr v2 /\
         match_val R p v1 v2) /\
    (forall expr b1 ofs,
       eval_lvalue ge1 e1 le1 m1 expr b1 ofs ->
       exists b2 ofs2,
         eval_lvalue ge2 e2 le2 m2 expr b2 ofs2 /\
         match_ptrbits R p (b1, ofs) (b2, ofs2)).
  Proof.
    intros ge1 ge2 Hge e1 e2 He le1 le2 Hle m1 m2 Hm.
    apply eval_expr_lvalue_ind.

    - eexists; repeat (solve_monotonic; constructor).
    - eexists; repeat (solve_monotonic; constructor).
    - eexists; repeat (solve_monotonic; constructor).
    - eexists; repeat (solve_monotonic; constructor).

    - intros.
      transport_hyps.
      eexists; split; eauto; repeat rstep.
      constructor; eauto.

    - intros expr ty loc ofs H IH.
      destruct IH as (b2 & ofs2 & Hb2 & Hptr).
      eexists; repeat (solve_monotonic; constructor).

    - intros op expr ty v1 v1' Hv1 IHv1 Hv1'.
      destruct IHv1 as (v2 & Hv2 & Hv).
      pose proof (sem_unary_operation_match R). (* necessary to transport Hv1' *)
      transport_hyps.
      eexists; repeat (solve_monotonic; econstructor).

    - intros op expra exprb ty va1 vb1 v1 Hva1 IHva Hvb1 IHvb Hv1.
      destruct IHva as (va2 & Hva2 & Hva).
      destruct IHvb as (vb2 & Hvb2 & Hvb).
      transport_hyps.
      eexists; repeat (solve_monotonic; econstructor).

    - intros expr ty v1 v1' Hv1 IHv1 Hv1'.
      destruct IHv1 as (v2 & Hv2 & Hv).
      pose proof (sem_cast_match R). (* necessary to transport Hv1' *)
      transport_hyps.
      eexists; repeat (solve_monotonic; econstructor).

    - eexists; repeat (solve_monotonic; constructor).
      destruct Hge; simpl.
      solve_monotonic.

    - eexists; repeat (solve_monotonic; constructor).
      destruct Hge; simpl.
      solve_monotonic.

    - intros expr b1 ofs1 v1 Hptr1 (b2 & ofs2 & Hptr & Hptr2) Hv1.
      transport_hyps.
      eexists; repeat (solve_monotonic; econstructor).

    - intros id b1 ty Hb1.
      specialize (He id).
      (** XXX: need transport to try both option_le and option_rel *)
      eapply option_rel_some_inv in Hb1; [ | solve_monotonic].
      destruct Hb1 as ((b2 & ty') & Hb2 & Hb & Hty).
      simpl in *; subst.
      eexists.
      repeat (solve_monotonic; econstructor).
      apply match_block_sameofs_ptrbits; auto.

    - intros id b1 ty He1 Hb1.
      transport_hyps.
      subst.
      eexists.
      eexists.
      split.
      + eapply eval_Evar_global; eauto.
      + apply match_block_sameofs_ptrbits; auto.
        apply match_global_block_sameofs.
        rewrite stencil_matches_symbols in H
          by (eapply genv_le_stencil_matches_r; rauto).
        eapply find_symbol_block_is_global.
        eassumption.

    - intros expr ty b1 ofs H1 IH.
      destruct IH as (ptr2 & H2 & Hptr).
      inversion Hptr; clear Hptr; subst.
      eexists.
      eexists.
      split; eauto.
      constructor; eauto.

    - intros expr fid ty b1 ofs1 sid sflist satt delta H1 IH Hs Hf Hdelta.
      destruct IH as (ptr2 & H2 & Hptr).
      inversion Hptr; clear Hptr; subst.
      destruct Hge; simpl in *.
      eauto 6 using @eval_Efield_struct, match_ptrbits_shift.

    - intros expr fid ty b1 ofs1 uid uflist uatt H1 IH Hu.
      destruct IH as (ptr2 & H2 & Hptr).
      inversion Hptr; clear Hptr; subst.
      destruct Hge; simpl in *.
      eauto using @eval_Efield_union.
  Qed.

  Global Instance eval_expr_match Rf p:
    Monotonic
      eval_expr
      (clight_genv_le Rf ++>
       env_match p ++>
       temp_env_match p ++>
       match_mem R p ++>
       - ==>
       set_rel (match_val R p)).
  Proof.
    intros ge1 ge2 Hge e1 e2 He le1 le2 Hle m1 m2 Hm expr v1 Hv1.
    edestruct eval_expr_lvalue_match; eauto.
  Qed.

  Global Instance: Params (@eval_expr) 6.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @eval_expr : typeclass_instances.

  Global Instance eval_lvalue_match Rf p:
    Monotonic
      eval_lvalue
      (clight_genv_le Rf ++>
       env_match p ++>
       temp_env_match p ++>
       match_mem R p ++>
       - ==>
       % set_rel (match_ptrbits R p)).
  Proof.
    intros ge1 ge2 Hge e1 e2 He le1 le2 Hle m1 m2 Hm expr [b1 ofs] Hp1.
    simpl in *.
    edestruct eval_expr_lvalue_match as [_ H]; eauto.
    edestruct H as (b2 & ofs2 & H'); eauto.
    exists (b2, ofs2).
    split_hyps.
    split; eauto.
  Qed.

  Global Instance: Params (@eval_lvalue) 7.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    rel_curry_set_rel_transport @eval_lvalue : typeclass_instances.

  Global Instance eval_exprlist_match Rf p:
    Monotonic
      eval_exprlist
      (clight_genv_le Rf ++>
       env_match p ++>
       temp_env_match p ++>
       match_mem R p ++>
       - ==> - ==>
       set_rel (list_rel (match_val R p))).
  Proof.
    intros ge1 ge2 Hge e1 e2 He le1 le2 Hle m1 m2 Hm exprlist tys vs1 Hvs1.
    induction Hvs1 as [|expr exprs ty tys v1 v1' v1s Hv1 Hv1' Hv1s IHv1s]; simpl.
    - exists nil.
      split; constructor.
    - split_hyps.
      pose proof (sem_cast_match R). (* necessary to transport Hv1' *)
      transport_hyps.
      eexists.
      split; econstructor; eauto.
  Qed.

  Global Instance: Params (@eval_exprlist) 7.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @eval_exprlist : typeclass_instances.

  Inductive cont_match (p: simrel_world R): rel cont cont :=
    | Kstop_match:
        Monotonic (@Kstop) (cont_match p)
    | Kseq_match:
        Monotonic (@Kseq) (- ==> cont_match p ++> cont_match p)
    | Kloop1_match:
        Monotonic (@Kloop1) (- ==> - ==> cont_match p ++> cont_match p)
    | Kloop2_match:
        Monotonic (@Kloop2) (- ==> - ==> cont_match p ++> cont_match p)
    | Kswitch_match:
        Monotonic (@Kswitch) (cont_match p ++> cont_match p)
    | Kcall_match:
        Monotonic
          (@Kcall)
          (- ==> - ==>
           env_match p ++>
           temp_env_match p ++>
           cont_match p ++>
           cont_match p).

  Global Existing Instance Kstop_match.
  Global Existing Instance Kseq_match.
  Global Existing Instance Kloop1_match.
  Global Existing Instance Kloop2_match.
  Global Existing Instance Kswitch_match.
  Global Existing Instance Kcall_match.

  Global Instance cont_match_le:
    Monotonic (@cont_match) ((≤) ++> subrel).
  Proof.
    repeat red.
    intros x y H x0 y0 H0.
    revert y H.
    induction H0; constructor; auto; solve_monotonic.
  Qed.

  Global Instance call_cont_match p:
    Monotonic (@call_cont) (cont_match p ++> cont_match p).
  Proof.
    intros k1 k2 Hk.
    induction Hk; simpl; solve_monotonic.
  Qed.

  Section LOCALS2.
    Local Instance is_call_cont_match_strong p:
      Monotonic (@is_call_cont) (cont_match p ++> iff).
    Proof.
      intros k1 k2 Hk.
      destruct Hk; solve_monotonic.
    Qed.

    Global Instance is_call_cont_match_weak p:
      Monotonic (@is_call_cont) (cont_match p ++> impl).
    Proof.
      solve_monotonic.
    Qed.
  End LOCALS2.

  Inductive state_match Rf p: rel (state (mem := mwd D1)) (state (mem := mwd D2)) :=
    | State_rel:
        Monotonic
          State
          (- ==> - ==>
           cont_match p ++>
           env_match p ++>
           temp_env_match p ++>
           match_mem R p ++>
           state_match Rf p)
    | Callstate_rel:
        Monotonic
          Callstate
          (Rf ++>
           list_rel (match_val R p) ++>
           (cont_match p /\ lsat is_call_cont) ++>
           match_mem R p ++>
           state_match Rf p)
    | Returnstate_rel:
        Monotonic
          Returnstate
          (match_val R p ++>
           (cont_match p /\ lsat is_call_cont) ++>
           match_mem R p ++>
           state_match Rf p).

  Global Existing Instance State_rel.
  Global Existing Instance Callstate_rel.
  Global Existing Instance Returnstate_rel.

  Global Instance: Params (@State) 6.
  Global Instance: Params (@Callstate) 4.
  Global Instance: Params (@Returnstate) 3.

  Scheme statement_ind_mutual := Induction for statement Sort Prop
    with ls_ind_mutual := Induction for labeled_statements Sort Prop.

  Global Instance find_label_match p:
    Monotonic
      (@find_label)
      (- ==> - ==> cont_match p ++> option_rel (eq * cont_match p)).
  Proof.
    intros lbl s.
    pattern s.
    pose proof Some_rel.
    eapply statement_ind_mutual with
      (P0 := fun ls =>
                 (cont_match p ++> option_rel (eq * cont_match p))%rel
                 (find_label_ls lbl ls)
                 (find_label_ls lbl ls));
    simpl; intros;
    solve_monotonic.
    destruct (ident_eq _ _); rauto. (* XXX coqrel *)
  Qed.

  Global Instance function_entry2_match Rf p:
    Monotonic
      function_entry2
      (clight_genv_le Rf ++>
       - ==>
       list_rel (match_val R p) ++>
       match_mem R p ++>
       % % set_rel (incr p (env_match p * temp_env_match p * match_mem R p))).
  Proof.
    intros ge1 ge2 Hge f vargs1 vargs2 Hvargs m1 m2 Hm [[e1 le1] m1'] H.
    simpl in *.
    destruct H as [Hfvnr Hfpnr Hfvpd Hm1' Hle1].
    pose proof (empty_env_match p) as Hee.
    destruct (alloc_variables_match Rf p _ _ Hge _ _ Hee _ _ Hm _ (e1, m1') Hm1')
      as ((e2 & m2') & Hm2' & p' & Hp' & He & Hm').
    transport Hle1.
    exists (e2, x, m2').
    simpl in *.
    split.
    - constructor; eauto.
    - exists p'.
      split; eauto.
      solve_monotonic.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    rel_curry2_set_rel_transport @function_entry2 : typeclass_instances.

  (** Special case for [Genv.find_funct] *)

  Global Instance find_funct_transfer {F V} Rf p ge1 ge2 v1 v2 f1:
    Transport
      (genv_le (F:=F) (V:=V) Rf * match_val R p)%rel
      (ge1, v1)
      (ge2, v2)
      (Genv.find_funct ge1 v1 = Some f1)
      (exists f2,
         Genv.find_funct ge2 v2 = Some f2 /\
         exists b, v1 = Vptr b Ptrofs.zero /\ Rf b f1 f2).
  Proof.
    repeat red.
    intros [Hge Hv].
    simpl in Hge, Hv.
    intros H.
    inversion Hv; subst; try discriminate.
    generalize H. intro H_.
    simpl in H_.
    destruct (Ptrofs.eq_dec _ _); try discriminate.
    subst.
    generalize H0. intro H0_.
    assert (block_is_global b1) as GLOBAL by eauto.
    apply (match_global_ptrbits p _ Ptrofs.zero) in GLOBAL.
    generalize (match_ptrbits_functional _ _ _ _ H0 GLOBAL).
    inversion 1; subst.
    simpl.
    destruct (Ptrofs.eq_dec _ _); try congruence.
    clear H.
    transport H_.
    eauto.
  Qed.

  Definition state_sim Rf := (rexists p, state_match Rf p)%rel.

  Require Import CompCertBuiltins.
  Context `{ec1_ops: !ExternalCallsOpsX (mwd D1)}.
  Context `{ec2_ops: !ExternalCallsOpsX (mwd D2)}.
  Context `{eb1: !EnableBuiltins (mwd D1)}.
  Context `{eb2: !EnableBuiltins (mwd D2)}.

  (*Context `{res_id: I64helpers.ReservedId}.
  Context `{cc1_ops: !CompilerConfigOps mem1}.
  Context `{cc2_ops: !CompilerConfigOps mem2}.*)

  Class ClightFunrel (Rf: block -> rel fundef fundef) ge1 ge2 :=
    {
      clight_funrel_type b :>
        Proper (Rf b ++> eq) type_of_fundef;
      clight_funrel_builtin_disabled:
        cc_enable_external_as_builtin (mem := mwd D1) = false;
      clight_funrel_callstate_sim p b t :>
        clight_genv_le Rf ge1 ge2 ->
        Related
          (fun f1 vargs1 k1 m1 s1' =>
             step2 ge1 (Callstate f1 vargs1 k1 m1) t s1')
          (fun f2 vargs2 k2 m2 s2' =>
             Smallstep.plus step2 ge2 (Callstate f2 vargs2 k2 m2) t s2')
          (Rf b ++>
           list_rel (match_val R p) ++>
           (cont_match p /\ lsat is_call_cont) ++>
           match_mem R p ++>
           set_rel (incr p (state_match (rexists b, Rf b) p)))
    }.

  Require EventsX.
  Import Smallstep.

  Definition genv_sim Rf (ge1 ge2: genv) :=
    (rforall p,
       state_match Rf p ++>
       - ==>
       set_rel (incr p (state_match Rf p)))%rel
    (Clight.step2 ge1)
    (plus Clight.step2 ge2).

  Lemma genv_sim_plus Rf:
    (rforall p,
       genv_sim Rf ++>
       state_match Rf p ++>
       - ==>
       set_rel (incr p (state_match Rf p)))%rel
    (plus Clight.step2)
    (plus Clight.step2).
  Proof.
    intros p ge1 ge2 Hge s1 s2 Hs t s1' Hs1'.
    revert p s2 Hs.
    pattern s1, t, s1'.
    eapply plus_ind2; try eassumption; clear s1 t s1' Hs1'.
    - intros s1 t s1' Hstep p s2 Hs.
      eapply (Hge p); eauto.
    - intros s1 t s1' u s1'' tu H1 H1' IH Htu.
      intros p1 s2 Hs.
      eapply Hge in H1; eauto.
      destruct H1 as (s2' & H2 & p' & (INCR' & Hs')).
      edestruct IH as (s2'' & H2' & p'' & (INCR'' & Hs'')); eauto.
      exists s2''.
      split.
      + eapply plus_trans; eauto.
      + exists p''.
        split; eauto.
        etransitivity; eauto.
  Qed.

  Lemma call_cont_is_call_cont k:
    is_call_cont (call_cont k).
  Proof.
    induction k; simpl; try constructor; eauto.
  Qed.

  Lemma clight_sim `{HRf: ClightFunrel}:
    clight_genv_le Rf ge1 ge2 ->
    genv_sim (rexists b, Rf b) ge1 ge2.
  Proof.
    intros Hge.
    intros p s1 s2 Hs t s1' H1.
    pose proof (assign_loc_match Rf p) as Hal.
    pose proof (sem_cast_match R) as Hcast.
    pose proof (bool_val_match R) as Hbv.

    deconstruct H1 ltac:(fun x => pose (c := x)); inversion Hs; clear Hs; subst.

    -
    transport_hyps; subst.
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; solve_monotonic ].
    erewrite <- clight_funrel_type; eassumption.
    split.
    { reflexivity. }
    solve_monotonic.

    -
    pose proof (builtin_external_call_x_match (F:=fundef) (V:=type) R p ef) as Hbc.
    specialize (Hbc clight_funrel_builtin_disabled BUILTIN_ENABLED).
    assert (Hecp: Params (@external_call) 6) by constructor.
    transport_hyps.
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; solve_monotonic ].
    {
      destruct ef; try reflexivity.
      simpl in BUILTIN_ENABLED.
      rewrite clight_funrel_builtin_disabled in BUILTIN_ENABLED.
      elim BUILTIN_ENABLED.
    }
    split.
    {
      eassumption.
    }
    solve_monotonic.

    -
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst.
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst;
    (transport_hyps; subst;
     eexists;
     split;
     [ eapply Smallstep.plus_one; eapply c; eauto |
       eexists; split; solve_monotonic ]).

    -
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    transport_hyps; subst.    
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].
    split.
    + eapply cont_match_le; eauto.
      solve_monotonic.
    + apply call_cont_is_call_cont.

    -
    transport_hyps; subst.
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].
    + split.
      * eapply cont_match_le; eauto.
        solve_monotonic.
      * apply call_cont_is_call_cont.

    -
    transport_hyps; subst.
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].
    +
    eapply @is_call_cont_match_weak; eauto. (* TODO: this step should be automatic *)
    + split.
      * eapply cont_match_le; eauto.
      * assumption.

    -
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    inversion H7; clear H7; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    transport e0.
    destruct x.
    inversion H0; clear H0; simpl in *; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].

    -
    destruct H4.
    eapply clight_funrel_callstate_sim in H1; eauto.

    -
    destruct H4.
    eapply clight_funrel_callstate_sim in H1; eauto.

    -
    destruct H5 as [H5 ?].
    inversion H5; clear H5; subst.
    transport_hyps; subst;
    eexists;
    split;
    [ eapply Smallstep.plus_one; eapply c; eauto |
      eexists; split; solve_monotonic ].
  Qed.
End CLIGHT_REL.

(** Redeclare the [set_rel_transport] instances. *)
Hint Extern 1 (Transport _ _ _ _ _) =>
  set_rel_transport @deref_loc : typeclass_instances.
Hint Extern 1 (Transport _ _ _ _ _) =>
  set_rel_transport @assign_loc : typeclass_instances.
Hint Extern 1 (Transport _ _ _ _ _) =>
  set_rel_transport @bind_parameters : typeclass_instances.
Hint Extern 1 (Transport _ _ _ _ _) =>
  set_rel_transport @eval_expr : typeclass_instances.
Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry_set_rel_transport @eval_lvalue : typeclass_instances.
Hint Extern 1 (Transport _ _ _ _ _) =>
  set_rel_transport @eval_exprlist : typeclass_instances.
Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry2_set_rel_transport @function_entry2 : typeclass_instances.
Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry_set_rel_transport @external_call : typeclass_instances.
