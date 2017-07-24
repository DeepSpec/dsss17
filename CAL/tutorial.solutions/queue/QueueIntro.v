(**
 * QueueIntro.v
 *
 * Queue getter/setters.
 *)

(** Compcert helper lib *)
Require Import Coqlib.
Require Import Maps.
(** Compcert types and semantics *)
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Clight.
Require Import Ctypes.
Require Import Cop.
Require Import Smallstep.
(** CertiKOS layer library *)
Require Import Semantics.
Require Import Structures.
Require Import GenSem.
Require Import CGenSem.
Require Import CPrimitives.
Require Import SimulationRelation.
Require Import ClightModules.
Require Import ClightXSemantics.
Require Import MakeProgramSpec.
Require Import AbstractData.
Require Import AbstractionRelation.

Require Import TutoLib.
Require Import QueueData.

(** This file implements the getters and setters for the queue fields. If you
  have already looked through [ContainerIntro] then there is not much new
  here. *)

Open Scope Z_scope.

Definition init_queue : ident := 19%positive.
Definition get_head : ident := 20%positive.
Definition get_tail : ident := 21%positive.
Definition set_head : ident := 22%positive.
Definition set_tail : ident := 23%positive.
Definition QUEUE : ident := QueueData.QUEUE.

Section QueueIntro.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.

  (** ** High Level Specifications *)
  Section HighSpec.

    Definition init_queue_high_spec (abs: intro_layerdata)
        : option intro_layerdata :=
      if decide (init_flag abs = false)
        then let q := Queue MAX_NODES MAX_NODES in
          Some abs {init_flag: true} {queue: q}
        else None.

    Definition init_queue_high_sem : cprimitive intro_layerdata :=
      cgensem _ init_queue_high_spec.

    Global Instance init_queue_pres_inv :
      GenSemPreservesInvariant intro_layerdata init_queue_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold init_queue_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct Hinv.
      constructor; cbn; intros; auto; try discriminate.
      pose proof MAX_NODES_range as Hmn_range.
      constructor; omega.
    Qed.

    Definition get_head_high_spec (abs: intro_layerdata) : option Z :=
      if init_flag abs
        then match queue abs with
          | Queue hd _ => Some hd
          | _ => None
        end
        else None.

    Definition get_head_high_sem : cprimitive intro_layerdata :=
      cgensem _ get_head_high_spec.

    Global Instance get_head_pres_inv :
      GenSemPreservesInvariant intro_layerdata get_head_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      assumption.
    Qed.

    Definition get_tail_high_spec (abs: intro_layerdata) : option Z :=
      if init_flag abs
        then match queue abs with
          | Queue _ tl => Some tl
          | _ => None
        end
        else None.

    Definition get_tail_high_sem : cprimitive intro_layerdata :=
      cgensem _ get_tail_high_spec.

    Global Instance get_tail_pres_inv :
      GenSemPreservesInvariant intro_layerdata get_tail_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      assumption.
    Qed.

    Definition set_head_high_spec (hd: Z) (abs: intro_layerdata)
        : option intro_layerdata :=
      if init_flag abs
        then if decide (0 <= hd <= MAX_NODES)
          then match queue abs with
            | Queue _ tl => Some abs {queue: Queue hd tl}
            | _ => None
          end
          else None
        else None.

    Definition set_head_high_sem : cprimitive intro_layerdata :=
      cgensem _ set_head_high_spec.

    Global Instance set_head_pres_inv :
      GenSemPreservesInvariant intro_layerdata set_head_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold set_head_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct Hinv.
      constructor; cbn; intros; auto; try congruence.
      constructor; try omega.
      specialize (q_valid H1). rewrite Heqq in q_valid.
      inv q_valid; auto.
    Qed.

    Definition set_tail_high_spec (tl: Z) (abs: intro_layerdata)
        : option intro_layerdata :=
      if init_flag abs
        then if decide (0 <= tl <= MAX_NODES)
          then match queue abs with
            | Queue hd _ => Some abs {queue: Queue hd tl}
            | _ => None
          end
          else None
        else None.

    Definition set_tail_high_sem : cprimitive intro_layerdata :=
      cgensem _ set_tail_high_spec.

    Global Instance set_tail_pres_inv :
      GenSemPreservesInvariant intro_layerdata set_tail_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold set_tail_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct Hinv.
      constructor; cbn; intros; auto; try congruence.
      constructor; try omega.
      specialize (q_valid H1). rewrite Heqq in q_valid.
      inv q_valid; auto.
    Qed.

  End HighSpec.

  (** ** Module Implementation *)
  Section Code.

    Definition f_init_queue' :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Ssequence
           (Sassign (Efield (Evar QUEUE queue_t_struct) queue_t_head tuint)
             (Econst_int (Int.repr MAX_NODES) tint))
           (Sassign (Efield (Evar QUEUE queue_t_struct) queue_t_tail tuint)
             (Econst_int (Int.repr MAX_NODES) tint))
      |}.

    Program Definition f_init_queue : function :=
      inline f_init_queue' _.

    Definition f_get_head' :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sreturn (Some (Efield (Evar QUEUE queue_t_struct) queue_t_head tuint))
      |}.

    Program Definition f_get_head : function :=
      inline f_get_head' _.

    Definition f_get_tail' :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sreturn (Some (Efield (Evar QUEUE queue_t_struct) queue_t_tail tuint))
      |}.

    Program Definition f_get_tail : function :=
      inline f_get_tail' _.

    Definition sh_hd : ident := 28%positive.

    Definition f_set_head' :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := (sh_hd, tuint) :: nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sassign (Efield (Evar QUEUE queue_t_struct) queue_t_head tuint)
           (Etempvar sh_hd tuint)
      |}.

    Program Definition f_set_head : function :=
      inline f_set_head' _.

    Definition st_tl : ident := 29%positive.

    Definition f_set_tail' :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := (st_tl, tuint) :: nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sassign (Efield (Evar QUEUE queue_t_struct) queue_t_tail tuint)
           (Etempvar st_tl tuint)
      |}.

    Program Definition f_set_tail : function :=
      inline f_set_tail' _.

  End Code.

  (** ** Low Level Specifications *)
  Section LowSpec.

    Definition init_queue_csig :=
      mkcsig (type_of_list_type nil) tvoid.

    Inductive init_queue_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | init_queue_step_intro m d qb m1 m':
        forall (Hqb: find_symbol QUEUE = Some qb),
        Mem.store Mint32 m qb head_off (Vint (Int.repr MAX_NODES)) = Some m1 ->
        Mem.store Mint32 m1 qb tail_off (Vint (Int.repr MAX_NODES)) = Some m' ->
        init_queue_step init_queue_csig
                        (nil, (m, d))
                        (Vundef, (m', d)).

    Definition get_head_csig :=
      mkcsig (type_of_list_type nil) tuint.

    Inductive get_head_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | get_head_step_intro m d qb hd:
        forall (Hqb: find_symbol QUEUE = Some qb),
        Mem.load Mint32 m qb head_off = Some (Vint hd) ->
        get_head_step get_head_csig
                      (nil, (m, d))
                      (Vint hd, (m, d)).

    Definition get_tail_csig :=
      mkcsig (type_of_list_type nil) tuint.

    Inductive get_tail_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | get_tail_step_intro m d qb tl:
        forall (Hqb: find_symbol QUEUE = Some qb),
        Mem.load Mint32 m qb tail_off = Some (Vint tl) ->
        get_tail_step get_tail_csig
                      (nil, (m, d))
                      (Vint tl, (m, d)).

    Definition set_head_csig :=
      mkcsig (type_of_list_type (tuint :: nil)) tvoid.

    Inductive set_head_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | set_head_step_intro m d qb hd m':
        forall (Hqb: find_symbol QUEUE = Some qb),
        Mem.store Mint32 m qb head_off (Vint hd) = Some m' ->
        set_head_step set_head_csig
                      (Vint hd :: nil, (m, d))
                      (Vundef, (m', d)).

    Definition set_tail_csig :=
      mkcsig (type_of_list_type (tuint :: nil)) tvoid.

    Inductive set_tail_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | set_tail_step_intro m d qb tl m':
        forall (Hqb: find_symbol QUEUE = Some qb),
        Mem.store Mint32 m qb tail_off (Vint tl) = Some m' ->
        set_tail_step set_tail_csig
                      (Vint tl :: nil, (m, d))
                      (Vundef, (m', d)).

    Program Definition init_queue_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ init_queue_step init_queue_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition get_head_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ get_head_step get_head_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition get_tail_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ get_tail_step get_tail_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition set_head_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ set_head_step set_head_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition set_tail_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ set_tail_step set_tail_csig _.
    Next Obligation.
      now inv H0.
    Qed.

  End LowSpec.

  (** ** Code Proofs *)
  Section CodeLowSpecSim.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce :
      build_composite_env (node_t_comp :: queue_t_comp :: nil) = OK ce.

    Lemma init_queue_code :
      boot_L ⊢ (id, init_queue ↦ f_init_queue) : (init_queue ↦ init_queue_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step.
      repeat step_tac; unfold lift; cbn;
      erewrite queue_fields_store_ok; unfold_queue_fields; try omega; eauto.
      reflexivity.
    Qed.

    Lemma get_head_code :
      boot_L ⊢ (id, get_head ↦ f_get_head) : (get_head ↦ get_head_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
    Qed.

    Lemma get_tail_code :
      boot_L ⊢ (id, get_tail ↦ f_get_tail) : (get_tail ↦ get_tail_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
    Qed.

    Lemma set_head_code :
      boot_L ⊢ (id, set_head ↦ f_set_head) : (set_head ↦ set_head_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      unfold lift; cbn.
      erewrite queue_fields_store_ok; unfold_queue_fields; try omega; eauto.
      reflexivity.
    Qed.

    Lemma set_tail_code :
      boot_L ⊢ (id, set_tail ↦ f_set_tail) : (set_tail ↦ set_tail_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      unfold lift; cbn.
      erewrite queue_fields_store_ok; unfold_queue_fields; try omega; eauto.
      reflexivity.
    Qed.

  End CodeLowSpecSim.

  (** ** Refinement Proofs *)
  Section LowHighSpecSim.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce :
      build_composite_env (node_t_comp :: queue_t_comp :: nil) = OK ce.

    Local Ltac node_destr_match H :=
      destruct H as (?dat & ?nxt & ?prv &
                     ?HLdat & ?HLnxt & ?HLprv &
                     ?HVdat & ?HVnxt & ?HVprv &
                     ?Hnode_match).

    Local Ltac queue_intro_destr_match H :=
      destruct H as (?hd & ?tl &
                     ?HLhd & ?HLtl &
                     ?HVhd & ?HVtl &
                     ?Hqueue_match).

    Lemma init_queue_refine :
      (init_queue ↦ init_queue_cprim) ⊢ (intro_R, ∅) : (init_queue ↦ init_queue_high_sem).
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold init_queue_high_spec in H1.
      repeat destr_in H1; inv H1.
      destruct H0, H2.
      queue_intro_destr_match H1.
      pose proof HVhd as HVhd'.
      pose proof HVtl as HVtl'.
      eapply Mem.valid_access_store in HVhd; destruct HVhd as (m1 & HShd).
      eapply Mem.store_valid_access_1 in HVtl; eauto.
      eapply Mem.valid_access_store in HVtl; destruct HVtl as (m2 & HStl).
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + constructor.
        + cbn; split.
          * eapply (Mem.store_outside_extends _ _ m1); eauto.
            eapply (Mem.store_outside_extends _ _ m); eauto.
            all: intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
          * constructor.
            -- split; auto.
            -- split.
               { (** Node match_data *)
                 econstructor; eauto.
                 intros.
                 specialize (H0 _ H1). node_destr_match H0.
                 assert (Hbneq: qb <> npb) by
                   (red; intros; subst; rewrite <- Hnpb in Hqb; inv Hqb).
                 (** dat, nxt, and prv are not written to *)
                 exists dat, nxt, prv.
                 repeat match goal with
                 | |- _ /\ _ => split
                 | |- Mem.load _ _ _ _ = Some _ =>
                   rewrite (Mem.load_store_other _ _ _ _ _ _ HStl); auto;
                   rewrite (Mem.load_store_other _ _ _ _ _ _ HShd); eauto
                 | |- Mem.valid_access _ _ _ _ _ =>
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HStl);
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HShd);
                   assumption
                 end.
                 assumption.
               }
               { (** QueueIntro match_data *)
                 econstructor; eauto.
                 unfold_queue_fields; cbn.
                 do 2 eexists.
                 repeat match goal with
                 | |- _ /\ _ => split
                 | |- Mem.valid_access _ _ _ _ _ =>
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HStl);
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HShd);
                   assumption
                 end.
                 { (** Load head *)
                   rewrite (Mem.load_store_other _ _ _ _ _ _ HStl).
                   apply (Mem.load_store_same _ _ _ _ _ _ HShd).
                   right; cbn; omega.
                 }
                 { (** Load tail *)
                   apply (Mem.load_store_same _ _ _ _ _ _ HStl).
                 }
                 constructor.
               }
            -- cbn; intros.
               specialize (abrel_match_mem_perms _ _ _ ofs k p H1 H2).
               destruct abrel_match_mem_perms as (NP & P).
               split; auto.
               red; intros. repeat (eapply Mem.perm_store_1; eauto).
            -- rewrite (Mem.nextblock_store _ _ _ _ _ _ HStl).
               rewrite (Mem.nextblock_store _ _ _ _ _ _ HShd).
               eauto.
    Qed.

    Lemma get_head_refine :
      (get_head ↦ get_head_cprim) ⊢ (intro_R, ∅) : (get_head ↦ get_head_high_sem).
    Proof.
      Opaque Z.mul.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold get_head_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct H1.
      queue_intro_destr_match H1.
      assert (z = hd).
      { inv Hqueue_match; try congruence.
        rewrite <- H2 in Heqq; inv Heqq.
        rewrite Int.repr_unsigned; reflexivity.
      }
      subst.
      do 3 eexists; split.
      - econstructor; eauto.
      - repeat (constructor; auto).
    Qed.

    Lemma get_tail_refine :
      (get_tail ↦ get_tail_cprim) ⊢ (intro_R, ∅) : (get_tail ↦ get_tail_high_sem).
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold get_tail_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct H1.
      queue_intro_destr_match H1.
      assert (z = tl).
      { inv Hqueue_match; try congruence.
        rewrite <- H2 in Heqq; inv Heqq.
        rewrite Int.repr_unsigned; reflexivity.
      }
      subst.
      do 3 eexists; split.
      - econstructor; eauto.
      - repeat (constructor; auto).
    Qed.

    Lemma set_head_refine :
      (set_head ↦ set_head_cprim) ⊢ (intro_R, ∅) : (set_head ↦ set_head_high_sem).
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold set_head_high_spec in H1.
      repeat destr_in H1; inv H1.
      destruct H0, H2.
      queue_intro_destr_match H1.
      pose proof HVhd as HVhd'.
      eapply Mem.valid_access_store in HVhd; destruct HVhd as (m' & HShd).
      do 3 eexists; split.
      - econstructor; eauto.
      - split; constructor; cbn.
        + eapply Mem.store_outside_extends; eauto.
          intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
        + constructor.
          * split; constructor.
          * split.
            { (** Node match_data *)
              econstructor; eauto.
              intros.
              specialize (H0 _ H1). node_destr_match H0.
              assert (Hbneq: qb <> npb) by
                (red; intros; subst; rewrite <- Hnpb in Hqb; inv Hqb).
              exists dat, nxt, prv.
              repeat match goal with
              | |- _ /\ _ => split
              | |- Mem.load _ _ _ _ = Some _ =>
                rewrite (Mem.load_store_other _ _ _ _ _ _ HShd); eauto
              | |- Mem.valid_access _ _ _ _ _ =>
                eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HShd); assumption
              end.
              assumption.
            }
            { (** QueueIntro match_data *)
              econstructor; eauto.
              unfold_queue_fields; cbn.
              do 2 eexists.
              repeat match goal with
              | |- _ /\ _ => split
              | |- Mem.load _ _ _ _ = Some _ =>
                try (rewrite (Mem.load_store_other _ _ _ _ _ _ HShd);
                [eassumption | right; cbn; omega])
              | |- Mem.valid_access _ _ _ _ _ =>
                eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HShd); assumption
              end.
              rewrite (Mem.load_store_same _ _ _ _ _ _ HShd); reflexivity.
              inv Hqueue_match; try congruence.
              rewrite Heqq in H2; inv H2.
              replace i with (Int.repr (Int.unsigned i)) by
                (apply Int.repr_unsigned).
              rewrite Int.unsigned_repr;
              [constructor | apply Int.unsigned_range_2].
            }
         * cbn; intros.
           specialize (abrel_match_mem_perms _ _ _ ofs k p H1 H2).
           destruct abrel_match_mem_perms as (NP & P).
           split; auto.
           red; intros. repeat (eapply Mem.perm_store_1; eauto).
         * rewrite (Mem.nextblock_store _ _ _ _ _ _ HShd); eauto.
      Qed.

    Lemma set_tail_refine :
      (set_tail ↦ set_tail_cprim) ⊢ (intro_R, ∅) : (set_tail ↦ set_tail_high_sem).
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold set_tail_high_spec in H1.
      repeat destr_in H1; inv H1.
      destruct H0, H2.
      queue_intro_destr_match H1.
      pose proof HVtl as HVtl'.
      eapply Mem.valid_access_store in HVtl; destruct HVtl as (m' & HStl).
      do 3 eexists; split.
      - econstructor; eauto.
      - split; constructor; cbn.
        + eapply Mem.store_outside_extends; eauto.
          intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
        + constructor.
          * split; constructor.
          * split.
            { (** Node match_data *)
              econstructor; eauto.
              intros.
              specialize (H0 _ H1). node_destr_match H0.
              assert (Hbneq: qb <> npb) by
                (red; intros; subst; rewrite <- Hnpb in Hqb; inv Hqb).
              exists dat, nxt, prv.
              repeat match goal with
              | |- _ /\ _ => split
              | |- Mem.load _ _ _ _ = Some _ =>
                rewrite (Mem.load_store_other _ _ _ _ _ _ HStl); eauto
              | |- Mem.valid_access _ _ _ _ _ =>
                eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HStl); assumption
              end.
              assumption.
            }
            { (** QueueIntro match_data *)
              econstructor; eauto.
              unfold_queue_fields; cbn.
              do 2 eexists.
              repeat match goal with
              | |- _ /\ _ => split
              | |- Mem.load _ _ _ _ = Some _ =>
                try (rewrite (Mem.load_store_other _ _ _ _ _ _ HStl);
                [eassumption | right; cbn; omega])
              | |- Mem.valid_access _ _ _ _ _ =>
                eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HStl); assumption
              end.
              rewrite (Mem.load_store_same _ _ _ _ _ _ HStl); reflexivity.
              inv Hqueue_match; try congruence.
              rewrite Heqq in H2; inv H2.
              replace i with (Int.repr (Int.unsigned i)) by
                (apply Int.repr_unsigned).
              rewrite Int.unsigned_repr;
              [constructor | apply Int.unsigned_range_2].
            }
         * cbn; intros.
           specialize (abrel_match_mem_perms _ _ _ ofs k p H1 H2).
           destruct abrel_match_mem_perms as (NP & P).
           split; auto.
           red; intros. repeat (eapply Mem.perm_store_1; eauto).
         * rewrite (Mem.nextblock_store _ _ _ _ _ _ HStl); eauto.
      Qed.

  End LowHighSpecSim.

  (** ** Linking *)
  Section Linking.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce :
      build_composite_env (node_t_comp :: queue_t_comp :: nil) = OK ce.

    Definition queue_intro_L : clayer intro_layerdata :=
      init_queue ↦ init_queue_high_sem
      ⊕ get_head ↦ get_head_high_sem
      ⊕ get_tail ↦ get_tail_high_sem
      ⊕ set_head ↦ set_head_high_sem
      ⊕ set_tail ↦ set_tail_high_sem.

    Definition queue_intro_Σ : clayer boot_layerdata :=
      init_queue ↦ init_queue_cprim
      ⊕ get_head ↦ get_head_cprim
      ⊕ get_tail ↦ get_tail_cprim
      ⊕ set_head ↦ set_head_cprim
      ⊕ set_tail ↦ set_tail_cprim.

    Definition queue_intro_M : cmodule :=
      init_queue ↦ f_init_queue
      ⊕ get_head ↦ f_get_head
      ⊕ get_tail ↦ f_get_tail
      ⊕ set_head ↦ f_set_head
      ⊕ set_tail ↦ f_set_tail.

    Hint Resolve init_queue_code init_queue_refine
                 get_head_code get_head_refine
                 get_tail_code get_tail_refine
                 set_head_code set_head_refine
                 set_tail_code set_tail_refine : linking.

    Theorem queue_intro_link :
      boot_L ⊢ (intro_R, queue_intro_M) : queue_intro_L.
    Proof. link_tac queue_intro_Σ. Qed.

    Lemma queue_intro_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) queue_intro_L.
    Proof. unfold queue_intro_L. typeclasses eauto. Qed.

  End Linking.

End QueueIntro.
