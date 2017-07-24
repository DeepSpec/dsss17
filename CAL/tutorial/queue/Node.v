(**
 * Node.v
 *
 * Node getter/setters.
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

(** This file implements the getters and setters for the node fields. If you
  have already looked through [ContainerIntro] then there is not much new
  here. *)

Open Scope Z_scope.

Definition init_node : ident := 1%positive.
Definition get_next : ident := 2%positive.
Definition get_prev : ident := 3%positive.
Definition set_next : ident := 4%positive.
Definition set_prev : ident := 5%positive.
Definition NODE_POOL : ident := QueueData.NODE_POOL.

Section Node.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.

  (** ** High Level Specifications *)
  Section HighSpec.

    Definition init_node_high_spec (node: Z) (data: Z) (abs: intro_layerdata)
        : option intro_layerdata :=
      if decide (0 <= node < MAX_NODES)
        then match ZMap.get node (npool abs) with
          | NodeUndef =>
              let n := Node data MAX_NODES MAX_NODES in
              Some abs {npool: ZMap.set node n (npool abs)}
          | _ => None
        end
        else None.

    Definition init_node_high_sem : cprimitive intro_layerdata :=
      cgensem _ init_node_high_spec.

    Global Instance init_node_pres_inv :
      GenSemPreservesInvariant intro_layerdata init_node_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold init_node_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct Hinv.
      constructor; cbn; auto.
      intros. destr_eq node (Int.unsigned i); [subst |].
      - rewrite ZMap.gss; right. constructor; omega.
      - rewrite ZMap.gso; auto.
    Qed.

    Definition get_next_high_spec (node: Z) (abs: intro_layerdata) : option Z :=
      if decide (0 <= node < MAX_NODES)
        then match ZMap.get node (npool abs) with
          | Node _ nxt _ => Some nxt
          | _ => None
        end
        else None.

    Definition get_next_high_sem : cprimitive intro_layerdata :=
      cgensem _ get_next_high_spec.

    Global Instance get_next_pres_inv :
      GenSemPreservesInvariant intro_layerdata get_next_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      assumption.
    Qed.

    Definition get_prev_high_spec (node: Z) (abs: intro_layerdata) : option Z :=
      if decide (0 <= node < MAX_NODES)
        then match ZMap.get node (npool abs) with
          | Node _ _ prv => Some prv
          | _ => None
        end
        else None.

    Definition get_prev_high_sem : cprimitive intro_layerdata :=
      cgensem _ get_prev_high_spec.

    Global Instance get_prev_pres_inv :
      GenSemPreservesInvariant intro_layerdata get_prev_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      assumption.
    Qed.

    Definition set_next_high_spec (node: Z) (nxt: Z) (abs: intro_layerdata)
        : option intro_layerdata :=
      if decide (0 <= node < MAX_NODES)
        then if decide (0 <= nxt <= MAX_NODES)
          then match ZMap.get node (npool abs) with
            | Node dat _ prv =>
                let n := Node dat nxt prv in
                Some abs {npool: ZMap.set node n (npool abs) }
            | _ => None
          end
          else None
        else None.

    Definition set_next_high_sem : cprimitive intro_layerdata :=
      cgensem _ set_next_high_spec.

    Global Instance set_next_pres_inv :
      GenSemPreservesInvariant intro_layerdata set_next_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold set_next_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct Hinv.
      constructor; cbn; auto.
      intros. destr_eq node (Int.unsigned i); [subst |].
      - rewrite ZMap.gss; right.
        specialize (npool_valid _ H1). rewrite Heqn in npool_valid.
        destruct npool_valid as [npool_valid | npool_valid]; inv npool_valid.
        constructor; omega.
      - rewrite ZMap.gso; auto.
    Qed.

    Definition set_prev_high_spec (node: Z) (prv: Z) (abs: intro_layerdata)
        : option intro_layerdata :=
      if decide (0 <= node < MAX_NODES)
        then if decide (0 <= prv <= MAX_NODES)
          then match ZMap.get node (npool abs) with
            | Node dat nxt _ =>
                let n := Node dat nxt prv in
                Some abs {npool: ZMap.set node n (npool abs) }
            | _ => None
          end
          else None
        else None.

    Definition set_prev_high_sem : cprimitive intro_layerdata :=
      cgensem _ set_prev_high_spec.

    Global Instance set_prev_pres_inv :
      GenSemPreservesInvariant intro_layerdata set_prev_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold set_prev_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct Hinv.
      constructor; cbn; auto.
      intros. destr_eq node (Int.unsigned i); [subst |].
      - rewrite ZMap.gss; right.
        specialize (npool_valid _ H1). rewrite Heqn in npool_valid.
        destruct npool_valid as [npool_valid | npool_valid]; inv npool_valid.
        constructor; omega.
      - rewrite ZMap.gso; auto.
    Qed.

  End HighSpec.

  (** ** Module Implementation *)
  Section Code.

    Definition in_node : ident := 11%positive.
    Definition in_data : ident := 12%positive.

    Definition f_init_node' :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := (in_node, tuint) :: (in_data, tuint) :: nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Ssequence
           (Sassign
             (Efield
               (Ederef
                 (Ebinop Oadd (Evar NODE_POOL (tarray node_t_struct MAX_NODES))
                   (Etempvar in_node tuint) (tptr node_t_struct))
                 node_t_struct) node_t_data tuint) (Etempvar in_data tuint))
           (Ssequence
             (Sassign
               (Efield
                 (Ederef
                   (Ebinop Oadd
                     (Evar NODE_POOL (tarray node_t_struct MAX_NODES))
                     (Etempvar in_node tuint) (tptr node_t_struct))
                   node_t_struct) node_t_next tuint)
               (Econst_int (Int.repr MAX_NODES) tint))
             (Sassign
               (Efield
                 (Ederef
                   (Ebinop Oadd
                     (Evar NODE_POOL (tarray node_t_struct MAX_NODES))
                     (Etempvar in_node tuint) (tptr node_t_struct))
                   node_t_struct) node_t_prev tuint)
               (Econst_int (Int.repr MAX_NODES) tint)))
      |}.

    Program Definition f_init_node : function :=
      inline f_init_node' _.

    Definition gn_node : ident := 13%positive.

    Definition f_get_next' :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := (gn_node, tuint) :: nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sreturn (Some (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Evar NODE_POOL (tarray node_t_struct MAX_NODES))
                              (Etempvar gn_node tuint) (tptr node_t_struct))
                            node_t_struct) node_t_next tuint))
      |}.

    Program Definition f_get_next : function :=
      inline f_get_next' _.

    Definition gp_node : ident := 14%positive.

    Definition f_get_prev' :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := (gp_node, tuint) :: nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sreturn (Some (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Evar NODE_POOL (tarray node_t_struct MAX_NODES))
                              (Etempvar gp_node tuint) (tptr node_t_struct))
                            node_t_struct) node_t_prev tuint))
      |}.

    Program Definition f_get_prev : function :=
      inline f_get_prev' _.

    Definition sn_node : ident := 15%positive.
    Definition sn_nxt : ident := 16%positive.

    Definition f_set_next' :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := (sn_node, tuint) :: (sn_nxt, tuint) :: nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sassign
           (Efield
             (Ederef
               (Ebinop Oadd (Evar NODE_POOL (tarray node_t_struct MAX_NODES))
                 (Etempvar sn_node tuint) (tptr node_t_struct))
               node_t_struct) node_t_next tuint) (Etempvar sn_nxt tuint)
      |}.

    Program Definition f_set_next : function :=
      inline f_set_next' _.

    Definition sp_node : ident := 17%positive.
    Definition sp_prv : ident := 18%positive.

    Definition f_set_prev' :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := (sp_node, tuint) :: (sp_prv, tuint) :: nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sassign
           (Efield
             (Ederef
               (Ebinop Oadd (Evar NODE_POOL (tarray node_t_struct MAX_NODES))
                 (Etempvar sp_node tuint) (tptr node_t_struct))
               node_t_struct) node_t_prev tuint) (Etempvar sp_prv tuint)
      |}.

    Program Definition f_set_prev : function :=
      inline f_set_prev' _.

  End Code.

  (** ** Low Level Specifications *)
  Section LowSpec.

    Notation node_off := (fun nd off => node_sz * Int.unsigned nd + off).

    Definition init_node_csig :=
      mkcsig (type_of_list_type (tuint :: tuint :: nil)) tvoid.

    Inductive init_node_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | init_node_step_intro m d npb nd dat m1 m2 m':
        forall (Hnpb: find_symbol NODE_POOL = Some npb),
        0 <= Int.unsigned nd < MAX_NODES ->
        Mem.store Mint32 m npb (node_off nd data_off)
                         (Vint dat) = Some m1 ->
        Mem.store Mint32 m1 npb (node_off nd next_off)
                         (Vint (Int.repr MAX_NODES)) = Some m2 ->
        Mem.store Mint32 m2 npb (node_off nd prev_off)
                         (Vint (Int.repr MAX_NODES)) = Some m' ->
        init_node_step init_node_csig
                       (Vint nd :: Vint dat :: nil, (m, d))
                       (Vundef, (m', d)).

    Definition get_next_csig :=
      mkcsig (type_of_list_type (tuint :: nil)) tuint.

    Inductive get_next_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | get_next_step_intro m d npb nd nxt:
        forall (Hnpb: find_symbol NODE_POOL = Some npb),
        0 <= Int.unsigned nd < MAX_NODES ->
        Mem.load Mint32 m npb (node_off nd next_off) = Some (Vint nxt) ->
        get_next_step get_next_csig
                      (Vint nd :: nil, (m, d))
                      (Vint nxt, (m, d)).

    Definition get_prev_csig :=
      mkcsig (type_of_list_type (tuint :: nil)) tuint.

    Inductive get_prev_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | get_prev_step_intro m d npb nd prv:
        forall (Hnpb: find_symbol NODE_POOL = Some npb),
        0 <= Int.unsigned nd < MAX_NODES ->
        Mem.load Mint32 m npb (node_off nd prev_off) = Some (Vint prv) ->
        get_prev_step get_prev_csig
                      (Vint nd :: nil, (m, d))
                      (Vint prv, (m, d)).

    Definition set_next_csig :=
      mkcsig (type_of_list_type (tuint :: tuint :: nil)) tvoid.

    Inductive set_next_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | set_next_step_intro m d npb nd nxt m':
        forall (Hnpb: find_symbol NODE_POOL = Some npb),
        0 <= Int.unsigned nd < MAX_NODES ->
        0 <= Int.unsigned nxt <= MAX_NODES ->
        Mem.store Mint32 m npb (node_off nd next_off) (Vint nxt) = Some m' ->
        set_next_step set_next_csig
                      (Vint nd :: Vint nxt :: nil, (m, d))
                      (Vundef, (m', d)).

    Definition set_prev_csig :=
      mkcsig (type_of_list_type (tuint :: tuint :: nil)) tvoid.

    Inductive set_prev_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | set_prev_step_intro m d npb nd prv m':
        forall (Hnpb: find_symbol NODE_POOL = Some npb),
        0 <= Int.unsigned nd < MAX_NODES ->
        0 <= Int.unsigned prv <= MAX_NODES ->
        Mem.store Mint32 m npb (node_off nd prev_off) (Vint prv) = Some m' ->
        set_prev_step set_prev_csig
                      (Vint nd :: Vint prv :: nil, (m, d))
                      (Vundef, (m', d)).

    Program Definition init_node_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ init_node_step init_node_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition get_next_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ get_next_step get_next_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition get_prev_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ get_prev_step get_prev_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition set_next_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ set_next_step set_next_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition set_prev_cprim : cprimitive boot_layerdata :=
      mkcprimitive _ set_prev_step set_prev_csig _.
    Next Obligation.
      now inv H0.
    Qed.

  End LowSpec.

  (** ** Code Proofs *)
  Section CodeLowSpecSim.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce :
      build_composite_env (node_t_comp :: queue_t_comp :: nil) = OK ce.

    (** Like in the container examples, the code proofs for the getter/setters
      mostly consist of convincing Coq of the equality between the [Ptrofs]
      version of the field offset and the [Z] one. *)

    Lemma init_node_code :
      boot_L ⊢ (id, init_node ↦ f_init_node) : (init_node ↦ init_node_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step.
      repeat step_tac; unfold lift; cbn;
        erewrite node_fields_store_ok; unfold_node_fields; try omega; eauto.
      reflexivity.
    Qed.

    Lemma get_next_code :
      boot_L ⊢ (id, get_next ↦ f_get_next) : (get_next ↦ get_next_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      - unfold lift; cbn.
        erewrite node_fields_load_ok; unfold_node_fields; try omega; eauto.
      - reflexivity.
    Qed.

    Lemma get_prev_code :
      boot_L ⊢ (id, get_prev ↦ f_get_prev) : (get_prev ↦ get_prev_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      - unfold lift; cbn.
        erewrite node_fields_load_ok; unfold_node_fields; try omega; eauto.
      - reflexivity.
    Qed.

    Lemma set_next_code :
      boot_L ⊢ (id, set_next ↦ f_set_next) : (set_next ↦ set_next_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      unfold lift; cbn.
      erewrite node_fields_store_ok; unfold_node_fields; try omega; eauto.
      reflexivity.
    Qed.

    Lemma set_prev_code :
      boot_L ⊢ (id, set_prev ↦ f_set_prev) : (set_prev ↦ set_prev_cprim).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      unfold lift; cbn.
      erewrite node_fields_store_ok; unfold_node_fields; try omega; eauto.
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

    Lemma init_node_refine :
      (init_node ↦ init_node_cprim) ⊢ (intro_R, ∅) : (init_node ↦ init_node_high_sem).
    Proof.
      Opaque Z.mul.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold init_node_high_spec in H1.
      repeat destr_in H1; inv H1.
      destruct H0, H2.
      pose proof H0 as Hmatch.
      specialize (H0 (Int.unsigned i) a).
      node_destr_match H0.
      queue_intro_destr_match H1.
      assert (Hbneq: qb <> npb) by
        (red; intros; subst; rewrite <- Hnpb in Hqb; inv Hqb).
      pose proof HVdat as HVdat'.
      pose proof HVnxt as HVnxt'.
      pose proof HVprv as HVprv'.
      eapply Mem.valid_access_store in HVdat; destruct HVdat as (m1 & HSdat).
      eapply Mem.store_valid_access_1 in HVnxt; eauto.
      eapply Mem.valid_access_store in HVnxt; destruct HVnxt as (m2 & HSnxt).
      eapply Mem.store_valid_access_1 in HVprv; eauto.
      eapply Mem.store_valid_access_1 in HVprv; eauto.
      eapply Mem.valid_access_store in HVprv; destruct HVprv as (m3 & HSprv).
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + constructor.
        + cbn; split.
          * eapply (Mem.store_outside_extends _ _ m2); eauto.
            eapply (Mem.store_outside_extends _ _ m1); eauto.
            eapply (Mem.store_outside_extends _ _ m); eauto.
            all: intros ? Hperm;
              eapply abrel_match_mem_perms with (i := NODE_POOL) in Hperm;
              eauto.
          * constructor.
            -- constructor; auto.
            -- split.
               { (** Node match_data *)
                 econstructor; eauto.
                 intros ? Hnode. unfold_node_fields.
                 destr_eq node (Int.unsigned i).
                 ++ subst; cbn. rewrite ZMap.gss.
                    do 3 eexists.
                    repeat match goal with
                    | |- _ /\ _ => split
                    | |- Mem.valid_access _ _ _ _ _ =>
                      eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSprv);
                      eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSnxt);
                      eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSdat); assumption
                    end.
                    { (** Load data *)
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HSprv).
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HSnxt).
                      apply (Mem.load_store_same _ _ _ _ _ _ HSdat).
                      all: right; cbn; omega.
                    }
                    { (** Load next *)
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HSprv).
                      apply (Mem.load_store_same _ _ _ _ _ _ HSnxt).
                      right; cbn; omega.
                    }
                    { (** Load prev *)
                      apply (Mem.load_store_same _ _ _ _ _ _ HSprv).
                    }
                    replace i0 with (Int.repr (Int.unsigned i0)) by
                      (apply Int.repr_unsigned).
                    rewrite Int.unsigned_repr;
                    [constructor | apply Int.unsigned_range_2].
                 ++ specialize (Hmatch node Hnode).
                    node_destr_match Hmatch.
                    cbn. rewrite ZMap.gso; auto.
                    do 3 eexists.
                    repeat match goal with
                    | |- _ /\ _ => split
                    | |- Mem.load _ _ _ _ = Some _ =>
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HSprv);
                        [| right; cbn; omega];
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HSnxt);
                        [| right; cbn; omega];
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HSdat);
                        [eassumption | right; cbn; omega]
                    | |- Mem.valid_access _ _ _ _ _ =>
                      eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSprv);
                      eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSnxt);
                      eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSdat);
                      assumption
                    end.
                    assumption.
               }
               { (** QueueIntro match_data *)
                 econstructor; eauto.
                 (** hd and tl are not written to *)
                 exists hd, tl.
                 repeat match goal with
                 | |- _ /\ _ => split
                 | |- Mem.load _ _ _ _ = Some _ =>
                   rewrite (Mem.load_store_other _ _ _ _ _ _ HSprv); auto;
                   rewrite (Mem.load_store_other _ _ _ _ _ _ HSnxt); auto;
                   rewrite (Mem.load_store_other _ _ _ _ _ _ HSdat); auto
                 | |- Mem.valid_access _ _ _ _ _ =>
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSprv);
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSnxt);
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSdat);
                   assumption
                 end.
                 assumption.
               }
            -- cbn; intros.
               specialize (abrel_match_mem_perms _ _ _ ofs k p H0 H1).
               destruct abrel_match_mem_perms as (NP & P).
               split; auto.
               red; intros. repeat (eapply Mem.perm_store_1; eauto).
            -- rewrite (Mem.nextblock_store _ _ _ _ _ _ HSprv).
               rewrite (Mem.nextblock_store _ _ _ _ _ _ HSnxt).
               rewrite (Mem.nextblock_store _ _ _ _ _ _ HSdat).
               eauto.
    Qed.

    Lemma get_next_refine :
      (get_next ↦ get_next_cprim) ⊢ (intro_R, ∅) : (get_next ↦ get_next_high_sem).
    Proof.
      Opaque Z.mul.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold get_next_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct H0.
      specialize (H0 _ a).
      node_destr_match H0.
      assert (z = nxt).
      { inv Hnode_match; try congruence.
        rewrite Heqn in H2. inv H2. rewrite Int.repr_unsigned; constructor.
      }
      subst.
      do 3 eexists; split.
      - econstructor; eauto.
      - repeat (constructor; auto).
    Qed.

    Lemma get_prev_refine :
      (get_prev ↦ get_prev_cprim) ⊢ (intro_R, ∅) : (get_prev ↦ get_prev_high_sem).
    Proof.
      Opaque Z.mul.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold get_prev_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct H0.
      specialize (H0 _ a).
      node_destr_match H0.
      assert (z = prv).
      { inv Hnode_match; try congruence.
        rewrite Heqn in H2. inv H2. rewrite Int.repr_unsigned; constructor.
      }
      subst.
      do 3 eexists; split.
      - econstructor; eauto.
      - repeat (constructor; auto).
    Qed.

    Lemma set_next_refine :
      (set_next ↦ set_next_cprim) ⊢ (intro_R, ∅) : (set_next ↦ set_next_high_sem).
    Proof.
      Opaque Z.mul.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold set_next_high_spec in H1.
      repeat destr_in H1; inv H1.
      destruct H0, H2.
      pose proof H0 as Hmatch.
      specialize (H0 _ a).
      node_destr_match H0.
      queue_intro_destr_match H1.
      assert (Hbneq: qb <> npb) by
        (red; intros; subst; rewrite <- Hnpb in Hqb; inv Hqb).
      pose proof HVnxt as HVnxt'.
      eapply Mem.valid_access_store in HVnxt; destruct HVnxt as (m' & HSnxt).
      do 3 eexists; split.
      - econstructor; eauto; try congruence.
      - split; constructor; cbn.
        + eapply Mem.store_outside_extends; eauto.
          intros ? Hperm.
          eapply abrel_match_mem_perms with (i := NODE_POOL) in Hperm; eauto.
        + constructor.
          * split; constructor.
          * split.
            { (** Node match_data *)
              econstructor; eauto.
              intros ? Hnode. unfold_node_fields.
              destr_eq node (Int.unsigned i); [subst |]; cbn.
              -- rewrite ZMap.gss.
                 do 3 eexists.
                 repeat match goal with
                 | |- _ /\ _ => split
                 | |- Mem.load _ _ _ _ = Some _ =>
                     try (rewrite (Mem.load_store_other _ _ _ _ _ _ HSnxt);
                     [eassumption | right; cbn; omega])
                 | |- Mem.valid_access _ _ _ _ _ =>
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSnxt);
                   assumption
                 end.
                 rewrite (Mem.load_store_same _ _ _ _ _ _ HSnxt); reflexivity.
                 rewrite Heqn in Hnode_match. inv Hnode_match.
                 replace i0 with (Int.repr (Int.unsigned i0)) by
                   (apply Int.repr_unsigned).
                 rewrite Int.unsigned_repr;
                 [constructor | apply Int.unsigned_range_2].
              -- rewrite ZMap.gso; auto.
                 specialize (Hmatch _ Hnode). node_destr_match Hmatch.
                 do 3 eexists.
                 repeat match goal with
                 | |- _ /\ _ => split
                 | |- Mem.load _ _ _ _ = Some _ =>
                     rewrite (Mem.load_store_other _ _ _ _ _ _ HSnxt);
                     [eassumption | right; cbn; omega]
                 | |- Mem.valid_access _ _ _ _ _ =>
                     eapply Mem.store_valid_access_1; eauto
                 end.
                 assumption.
            }
            { (** QueueIntro match_data *)
              econstructor; eauto.
              exists hd, tl.
              repeat match goal with
              | |- _ /\ _ => split
              | |- Mem.load _ _ _ _ = Some _ =>
                rewrite (Mem.load_store_other _ _ _ _ _ _ HSnxt); auto
              | |- Mem.valid_access _ _ _ _ _ =>
                eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSnxt); auto
              end.
              assumption.
            }
         * cbn; intros.
           specialize (abrel_match_mem_perms _ _ _ ofs k p H0 H1).
           destruct abrel_match_mem_perms as (NP & P).
           split; auto.
           red; intros. repeat (eapply Mem.perm_store_1; eauto).
         * rewrite (Mem.nextblock_store _ _ _ _ _ _ HSnxt); eauto.
      Qed.

    Lemma set_prev_refine :
      (set_prev ↦ set_prev_cprim) ⊢ (intro_R, ∅) : (set_prev ↦ set_prev_high_sem).
    Proof.
      Opaque Z.mul.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold set_prev_high_spec in H1.
      repeat destr_in H1; inv H1.
      destruct H0, H2.
      pose proof H0 as Hmatch.
      specialize (H0 _ a).
      node_destr_match H0.
      queue_intro_destr_match H1.
      assert (Hbneq: qb <> npb) by
        (red; intros; subst; rewrite <- Hnpb in Hqb; inv Hqb).
      pose proof HVprv as HVprv'.
      eapply Mem.valid_access_store in HVprv; destruct HVprv as (m' & HSprv).
      do 3 eexists; split.
      - econstructor; eauto; try congruence.
      - split; constructor; cbn.
        + eapply Mem.store_outside_extends; eauto.
          intros ? Hperm.
          eapply abrel_match_mem_perms with (i := NODE_POOL) in Hperm; eauto.
        + constructor.
          * split; constructor.
          * split.
            { (** Node match_data *)
              econstructor; eauto.
              intros ? Hnode. unfold_node_fields.
              destr_eq node (Int.unsigned i); [subst |]; cbn.
              -- rewrite ZMap.gss.
                 do 3 eexists.
                 repeat match goal with
                 | |- _ /\ _ => split
                 | |- Mem.load _ _ _ _ = Some _ =>
                     try (rewrite (Mem.load_store_other _ _ _ _ _ _ HSprv);
                     [eassumption | right; cbn; omega])
                 | |- Mem.valid_access _ _ _ _ _ =>
                   eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSprv);
                   assumption
                 end.
                 rewrite (Mem.load_store_same _ _ _ _ _ _ HSprv); reflexivity.
                 rewrite Heqn in Hnode_match. inv Hnode_match.
                 replace i0 with (Int.repr (Int.unsigned i0)) by
                   (apply Int.repr_unsigned).
                 rewrite Int.unsigned_repr;
                 [constructor | apply Int.unsigned_range_2].
              -- rewrite ZMap.gso; auto.
                 specialize (Hmatch _ Hnode). node_destr_match Hmatch.
                 do 3 eexists.
                 repeat match goal with
                 | |- _ /\ _ => split
                 | |- Mem.load _ _ _ _ = Some _ =>
                     rewrite (Mem.load_store_other _ _ _ _ _ _ HSprv);
                     [eassumption | right; cbn; omega]
                 | |- Mem.valid_access _ _ _ _ _ =>
                     eapply Mem.store_valid_access_1; eauto
                 end.
                 assumption.
            }
            { (** QueueIntro match_data *)
              econstructor; eauto.
              exists hd, tl.
              repeat match goal with
              | |- _ /\ _ => split
              | |- Mem.load _ _ _ _ = Some _ =>
                rewrite (Mem.load_store_other _ _ _ _ _ _ HSprv); auto
              | |- Mem.valid_access _ _ _ _ _ =>
                eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSprv); auto
              end.
              assumption.
            }
         * cbn; intros.
           specialize (abrel_match_mem_perms _ _ _ ofs k p H0 H1).
           destruct abrel_match_mem_perms as (NP & P).
           split; auto.
           red; intros. repeat (eapply Mem.perm_store_1; eauto).
         * rewrite (Mem.nextblock_store _ _ _ _ _ _ HSprv); eauto.
      Qed.

  End LowHighSpecSim.

  (** ** Linking. *)
  Section Linking.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce :
      build_composite_env (node_t_comp :: queue_t_comp :: nil) = OK ce.

    Definition node_L : clayer intro_layerdata :=
      init_node ↦ init_node_high_sem
      ⊕ get_next ↦ get_next_high_sem
      ⊕ get_prev ↦ get_prev_high_sem
      ⊕ set_next ↦ set_next_high_sem
      ⊕ set_prev ↦ set_prev_high_sem.

    Definition node_Σ : clayer boot_layerdata :=
      init_node ↦ init_node_cprim
      ⊕ get_next ↦ get_next_cprim
      ⊕ get_prev ↦ get_prev_cprim
      ⊕ set_next ↦ set_next_cprim
      ⊕ set_prev ↦ set_prev_cprim.

    Definition node_M : cmodule :=
      init_node ↦ f_init_node
      ⊕ get_next ↦ f_get_next
      ⊕ get_prev ↦ f_get_prev
      ⊕ set_next ↦ f_set_next
      ⊕ set_prev ↦ f_set_prev.

    Hint Resolve init_node_code init_node_refine
                 get_next_code get_next_refine
                 get_prev_code get_prev_refine
                 set_next_code set_next_refine
                 set_prev_code set_prev_refine : linking.

    Theorem node_link :
      boot_L ⊢ (intro_R, node_M) : node_L.
    Proof. link_tac node_Σ. Qed.

    Lemma node_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) node_L.
    Proof. unfold node_L. typeclasses eauto. Qed.

  End Linking.

End Node.
