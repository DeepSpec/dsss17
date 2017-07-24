(**
 * Container.v
 *
 * Primitives to initialize and manage containers.
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
Require Import SimrelInvariant.
Require Import LayerLogicImpl.
Require Import ClightModules.
Require Import ClightXSemantics.
Require Import AbstractData.
Require Import AbstractionRelation.

Require Import TutoLib.
Require Import ContainerType.
Require Import ContainerIntro.

(** In this file we will implement primitives to [init] the root container,
  check if a container [can_consume] more memory, [alloc] more memory, and
  [split] a container to create a child. *)

Open Scope Z_scope.

Definition container_init : ident := 25%positive.
Definition container_can_consume : ident := 26%positive.
Definition container_alloc : ident := 27%positive.
Definition container_split : ident := 28%positive.

Section Container.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.

  (** ** Abstract Data *)
  Section AbsData.

    (** At this layer we now require that all of the containers are valid. *)

    Record container_data_inv (d: container_data) : Prop := {
      valid_inv: container_valid (cpool d);
      preinit_inv: init_flag d = false -> cpool d = ZMap.init container_unused
    }.

    Instance container_data_ops : AbstractDataOps container_data :=
      {|
        init_data := container_data_init;
        data_inv := container_data_inv;
        data_inject := fun _ _ _ => True
      |}.

    Instance container_data_data : AbstractData container_data.
    Proof.
      constructor; constructor.
      - apply container_unused_valid.
      - reflexivity.
    Qed.

    Definition container_layerdata : layerdata :=
      {|
        ldata_type := container_data;
        ldata_ops  := container_data_ops;
        ldata_prf  := container_data_data
      |}.

  End AbsData.

  (** ** High Level Specifications *)
  Section HighSpec.

    (** [init] sets the [init_flag] to true, and sets the container pool to its
      initial value. *)
    Definition container_init_high_spec (abs: container_layerdata)
        : option container_layerdata :=
      if decide (init_flag abs = false)
        then Some {| init_flag := true; cpool := container_pool_init |}
        else None.

    Definition container_init_high_sem : cprimitive container_layerdata :=
      cgensem container_layerdata container_init_high_spec.

    Definition container_init_layer : clayer container_layerdata :=
      container_init ↦ container_init_high_sem.

    Global Instance container_init_pres_inv :
      GenSemPreservesInvariant container_layerdata container_init_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      unfold container_init_high_spec in H3.
      destr_in H3; inv H3.
      constructor; cbn.
      - apply container_init_valid.
      - discriminate.
    Qed.

    (** [can_consume] checks whether the difference between [quota] and [usage]
      is at least [n]. *)
    Definition container_can_consume_high_spec (id: Z) (n: Z)
                                               (abs: container_layerdata)
                                               : option bool :=
      if init_flag abs
        then if decide (0 <= id < NUM_ID)
          then let c := ZMap.get id (cpool abs) in
            if decide (0 <= cusage c <= cquota c /\ cquota c <= Int.max_unsigned)
              then if cused c
                then Some (if decide (cusage c + n <= cquota c) then true else false)
                else None
              else None
          else None
        else None.

    Definition container_can_consume_high_sem : cprimitive container_layerdata :=
      cgensem container_layerdata container_can_consume_high_spec.

    Definition container_can_consume_layer : clayer container_layerdata :=
      container_can_consume ↦ container_can_consume_high_sem.

    Global Instance container_can_consume_pres_inv :
      GenSemPreservesInvariant container_layerdata container_can_consume_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem. inv_monad H2. inv H2.
      assumption.
    Qed.

    (** [alloc] increments the usage by 1. *)
    Definition container_alloc_high_spec (id: Z) (abs: container_layerdata)
        : option (container_layerdata * bool) :=
      if init_flag abs
        then if decide (0 <= id < NUM_ID)
          then let c := ZMap.get id (cpool abs) in
            if decide (0 <= cusage c <= cquota c /\ cquota c <= Int.max_unsigned)
              then if cused c
                then let c' := mkContainer (cquota c) (cusage c + 1) (cparent c)
                                           (cchildren c) (cused c) in
                  Some (if decide (cusage c < cquota c)
                             then ({| init_flag := init_flag abs;
                                      cpool := ZMap.set id c' (cpool abs) |},
                                   true)
                             else (abs, false))
                else None
              else None
          else None
        else None.

    Definition container_alloc_high_sem : cprimitive container_layerdata :=
      cgensem container_layerdata container_alloc_high_spec.

    Definition container_alloc_layer : clayer container_layerdata :=
      container_alloc ↦ container_alloc_high_sem.

    Global Instance container_alloc_pres_inv :
      GenSemPreservesInvariant container_layerdata container_alloc_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold container_alloc_high_spec in H1.
      repeat destr_in H1; try discriminate; inv H1.
      - inv Hinv. constructor; cbn; [| discriminate].
        rewrite <- Heqb1. apply container_alloc_valid; auto.
      - assumption.
    Qed.

    (** [split] creates a new child container with a given [quota]. *)
    Definition container_split_high_spec (id: Z) (quota: Z)
                                         (abs: container_layerdata)
                                         : option (container_layerdata * Z) :=
      if init_flag abs
        then let c := ZMap.get id (cpool abs) in
             let chid := id * MAX_CHILDREN + 1 + Z.of_nat (length (cchildren c)) in
          if decide (Z.of_nat (length (cchildren c)) < MAX_CHILDREN /\
                     0 < chid < NUM_ID /\
                     0 <= quota <= cquota c - cusage c /\
                     0 <= cusage c /\
                     0 <= cquota c <= Int.max_unsigned)
            then match cused c, cused (ZMap.get chid (cpool abs)) with
              | true, false =>
                let child := mkContainer quota 0 id nil true in
                let c' := mkContainer (cquota c) (cusage c + quota) (cparent c)
                                      (chid :: cchildren c) (cused c) in
                Some ({| init_flag := init_flag abs;
                         cpool := ZMap.set id c' (ZMap.set chid child (cpool abs)) |},
                      chid)
              | _, _ => None
              end
            else None
        else None.

    Definition container_split_high_sem : cprimitive container_layerdata :=
      cgensem container_layerdata container_split_high_spec.

    Definition container_split_layer : clayer container_layerdata :=
      container_split ↦ container_split_high_sem.

    Global Instance container_split_pres_inv :
      GenSemPreservesInvariant container_layerdata container_split_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold container_split_high_spec in H2.
      repeat destr_in H2; try discriminate. inv H2.
      constructor; cbn; [| discriminate].
      inv Hinv.
      rewrite <- Heqb0 at 1.
      apply container_split_valid; (auto || omega).
    Qed.

  End HighSpec.

  (** ** Module Implementation *)
  Section Code.

    (** TUTORIAL: Replace the following four [Axiom]s with [Definition]s of
        Clight functions from container.c and uncomment the Program Definitions.*)

    Axiom f_container_init : Clight.function.

(*
    Program Definition inlinable_f_container_init : function :=
      inline f_container_init _.
*)

    Definition ccc_id : ident := 29%positive.
    Definition ccc_n : ident := 30%positive.
    Definition ccc_quota : ident := 31%positive.
    Definition ccc_usage : ident := 32%positive.
    Definition ccc_ret : ident := 33%positive.

    Axiom f_container_can_consume : Clight.function.

(*
    Program Definition inlinable_f_container_can_consume : function :=
      inline f_container_can_consume _.
*)

    Definition ca_id : ident := 34%positive.
    Definition ca_quota : ident := 35%positive.
    Definition ca_usage : ident := 36%positive.

    Axiom f_container_alloc : Clight.function.

(*
    Program Definition inlinable_f_container_alloc : function :=
      inline f_container_alloc _.
*)

    Definition cs_id : ident := 37%positive.
    Definition cs_quota : ident := 38%positive.
    Definition cs_nchildren : ident := 39%positive.
    Definition cs_usage : ident := 40%positive.
    Definition cs_child_id : ident := 41%positive.

    Axiom f_container_split : Clight.function.

(*
    Program Definition inlinable_f_container_split : function :=
      inline f_container_split _.
*)

    (** TUTORIAL: Define mappings for init, can_consume, alloc, and split *)
    Axiom Minit : cmodule.
    Axiom Mconsume : cmodule.
    Axiom Malloc : cmodule.
    Axiom Msplit : cmodule.

  End Code.

  (** ** Low Level Specifications *)
  Section LowSpec.

    Definition container_init_csig := mkcsig Ctypes.Tnil tvoid.

    Inductive container_init_step :
      csignature -> list val * mwd container_intro_layerdata -> val * mwd container_intro_layerdata -> Prop :=
    | container_init_step_into m d d1 d':
        boot_init_high_spec d = d1 ->
        container_node_init_high_spec 0 ROOT_QUOTA 0 d1 = Some d' ->
        container_init_step container_init_csig (nil, (m, d)) (Vundef, (m, d')).

    Program Definition container_init_cprimitive : cprimitive container_intro_layerdata :=
      mkcprimitive _ container_init_step container_init_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Global Instance container_init_cprim_pres_inv :
      CPrimitivePreservesInvariant container_intro_layerdata container_init_cprimitive.
    Proof.
      constructor; intros.
      - inv H0.
        unfold container_node_init_high_spec in H10.
        repeat destr_in H10; try discriminate. inv H10.
        inv H1. inv cprimitive_inv_init_state_data_inv.
        repeat constructor; auto; cbn.
        discriminate.
      - inv H0; reflexivity.
    Qed.

    Definition container_can_consume_csig :=
      mkcsig (type_of_list_type (tuint :: tuint :: nil)) tuint.

    Inductive container_can_consume_step :
      csignature -> list val * mwd container_intro_layerdata -> val * mwd container_intro_layerdata -> Prop :=
    | container_can_consume_step_into m d id n ret:
        container_can_consume_high_spec (Int.unsigned id) (Int.unsigned n) d = Some ret ->
        container_can_consume_step container_can_consume_csig
                                   (Vint id :: Vint n :: nil, (m, d))
                                   (Vint (Int.repr (Z.b2z ret)), (m, d)).

    Program Definition container_can_consume_cprimitive : cprimitive container_intro_layerdata :=
      mkcprimitive _ container_can_consume_step container_can_consume_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Global Instance container_can_consume_cprim_pres_inv :
      CPrimitivePreservesInvariant container_intro_layerdata container_can_consume_cprimitive.
    Proof.
      constructor; intros.
      - inv H0.
        inv H1. inv cprimitive_inv_init_state_data_inv.
        repeat constructor; auto; cbn.
      - inv H0; reflexivity.
    Qed.

    Definition container_alloc_csig :=
      mkcsig (type_of_list_type (tuint :: nil)) tuint.

    Inductive container_alloc_step :
      csignature -> list val * mwd container_intro_layerdata -> val * mwd container_intro_layerdata -> Prop :=
    | container_alloc_step_into m d d' id ret:
        container_alloc_high_spec (Int.unsigned id) d = Some (d', ret) ->
        container_alloc_step container_alloc_csig
                             (Vint id :: nil, (m, d))
                             (Vint (Int.repr (Z.b2z ret)), (m, d')).

    Program Definition container_alloc_cprimitive : cprimitive container_intro_layerdata :=
      mkcprimitive _ container_alloc_step container_alloc_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Global Instance container_alloc_cprim_pres_inv :
      CPrimitivePreservesInvariant container_intro_layerdata container_alloc_cprimitive.
    Proof.
      constructor; intros.
      - inv H0.
        inv H1. inv cprimitive_inv_init_state_data_inv.
        unfold container_alloc_high_spec in H4.
        repeat destr_in H4; try discriminate; inv H4; cbn;
        repeat constructor; auto; cbn; congruence.
      - inv H0; reflexivity.
    Qed.

    Definition container_split_csig :=
      mkcsig (type_of_list_type (tuint :: tuint :: nil)) tuint.

    Inductive container_split_step :
      csignature -> list val * mwd container_intro_layerdata -> val * mwd container_intro_layerdata -> Prop :=
    | container_split_step_into m d d' id q chid:
        container_split_high_spec (Int.unsigned id) (Int.unsigned q) d = Some (d', chid) ->
        container_split_step container_split_csig
                             (Vint id :: Vint q :: nil, (m, d))
                             (Vint (Int.repr chid), (m, d')).

    Program Definition container_split_cprimitive : cprimitive container_intro_layerdata :=
      mkcprimitive _ container_split_step container_split_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Global Instance container_split_cprim_pres_inv :
      CPrimitivePreservesInvariant container_intro_layerdata container_split_cprimitive.
    Proof.
      constructor; intros.
      - inv H0.
        inv H1. inv cprimitive_inv_init_state_data_inv.
        unfold container_split_high_spec in H4.
        repeat destr_in H4; try discriminate. inv H4.
        repeat constructor; cbn; auto; discriminate.
      - inv H0; reflexivity.
    Qed.

  End LowSpec.

  (** ** Code Proofs *)
  Section CodeLowSpecSim.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce : build_composite_env (t_container_comp :: nil) = OK ce.

(** TUTORIAL: Uncomment these proofs and remove the Admitteds. *)
    Lemma container_init_code :
      container_intro_L ⊢ (id, Minit) : (container_init ↦ container_init_cprimitive).
    Proof.
      (*
      code_proof_tac.
      find_prim container_node_init.
      find_prim boot_init.
      inv CStep.
      cbn in H8. repeat destr_in H8; inv H8.
      cprim_step. repeat step_tac.
    Qed.
    *)
    Admitted.

    Lemma container_can_consume_code :
      container_intro_L ⊢ (id, Mconsume) : (container_can_consume ↦ container_can_consume_cprimitive).
    Proof.
      (*
      code_proof_tac.
      find_prim container_get_usage.
      find_prim container_get_quota.
      inv CStep.
      unfold container_can_consume_high_spec in H2.
      do 4 (destr_in H2; try discriminate). inv H2.
      clear Heqs0; destruct a0 as [Husg Hquo].
      rename Heqb0 into Hused.
      rename Heqs into Hid.
      destr.
      { (** usage + n <= quota *)
        assert (Hquo_n: Int.ltu (Int.repr (cquota (ZMap.get (Int.unsigned id) (cpool d')))) n = false).
        { unfold Int.ltu. rewrite Int.unsigned_repr; [| cbn; omega].
          rewrite zlt_false; [reflexivity | omega].
        }
        cprim_step. repeat step_tac.
        - unfold container_get_quota_high_spec.
          rewrite Hid. rewrite Hused.
          repeat f_equal.
          rewrite <- (Int.unsigned_repr (cquota _)); [reflexivity | cbn; omega].
        - unfold container_get_usage_high_spec.
          rewrite Hid. rewrite Hused.
          repeat f_equal.
          rewrite <- (Int.unsigned_repr (cusage _)); [reflexivity | cbn; omega].
        - rewrite Hquo_n; reflexivity.
        - change (Int.eq Int.one Int.zero) with false; cbn.
          repeat step_tac.
          + pose (Int.unsigned_range n) as Hn.
            replace (Int.ltu _ _) with false; [reflexivity |].
            unfold Int.sub, Int.ltu.
            repeat rewrite Int.unsigned_repr; try (cbn; omega).
            symmetry; apply zlt_false. omega.
          + reflexivity.
          + repeat step_tac.
      }
      { (** usage + n > quota *)
        cprim_step. repeat step_tac.
        - unfold container_get_quota_high_spec.
          rewrite Hid. rewrite Hused.
          repeat f_equal.
          rewrite <- (Int.unsigned_repr (cquota _)); [reflexivity | cbn; omega].
        - unfold container_get_usage_high_spec.
          rewrite Hid. rewrite Hused.
          repeat f_equal.
          rewrite <- (Int.unsigned_repr (cusage _)); [reflexivity | cbn; omega].
        - instantiate (1 := negb
            (Int.ltu (Int.repr (cquota (ZMap.get (Int.unsigned id) (cpool d'))))
                     n)).
          destruct (Int.ltu _ _); reflexivity.
        - destr; repeat step_tac.
          + pose (Int.unsigned_range n) as Hn.
            replace (Int.ltu _ _) with true; [reflexivity |].
            unfold Int.ltu in Heqb0.
            rewrite Int.unsigned_repr in Heqb0; [| cbn; omega].
            destr_in Heqb0; [discriminate |].
            unfold Int.sub, Int.ltu.
            repeat rewrite Int.unsigned_repr; try (cbn; omega).
            symmetry; apply zlt_true. omega.
          + reflexivity.
          + repeat step_tac.
      }
    Qed.
    *)
    Admitted.

    Lemma container_alloc_code :
      container_intro_L ⊢ (id, Malloc) : (container_alloc ↦ container_alloc_cprimitive).
    Proof.
    (*
      code_proof_tac.
      find_prim container_get_usage.
      find_prim container_get_quota.
      find_prim container_set_usage.
      inv CStep.
      unfold container_alloc_high_spec in H2.
      repeat (destr_in H2; try discriminate); inv H2;
      clear Heqs0; destruct a0 as [Husg Hquo];
      rename Heqb0 into Hused;
      rename Heqs into Hid;
      rename Heqb into Hinit.
      { (** usage < quota *)
        assert (Husg_quo: Int.ltu (Int.repr (cusage (ZMap.get (Int.unsigned id) (cpool d))))
                                  (Int.repr (cquota (ZMap.get (Int.unsigned id) (cpool d))))
                          = true).
        { unfold Int.ltu. repeat rewrite Int.unsigned_repr; try (cbn; omega).
          rewrite zlt_true; [reflexivity | omega].
        }
        cprim_step. repeat step_tac.
        - unfold container_get_quota_high_spec.
          rewrite Hid; rewrite Hused.
          repeat f_equal.
          rewrite <- (Int.unsigned_repr (cquota _)); [reflexivity | cbn; omega].
        - unfold container_get_usage_high_spec.
          rewrite Hid; rewrite Hused.
          repeat f_equal.
          rewrite <- (Int.unsigned_repr (cusage _)); [reflexivity | cbn; omega].
        - rewrite Husg_quo; reflexivity.
        - repeat step_tac.
          unfold container_set_usage_high_spec.
          rewrite Hid; rewrite Hinit; rewrite Hused.
          unfold Int.add.
          fold Int.one; rewrite Int.unsigned_one.
          repeat rewrite Int.unsigned_repr; try (cbn; omega).
          destr; [reflexivity | omega].
      }
      { (** usage >= quota *)
        assert (Husg_quo: Int.ltu (Int.repr (cusage (ZMap.get (Int.unsigned id) (cpool d'))))
                                  (Int.repr (cquota (ZMap.get (Int.unsigned id) (cpool d'))))
                          = false).
        { unfold Int.ltu. repeat rewrite Int.unsigned_repr; try (cbn; omega).
          rewrite zlt_false; [reflexivity | omega].
        }
        cprim_step. repeat step_tac.
        - unfold container_get_quota_high_spec.
          rewrite Hid; rewrite Hused.
          repeat f_equal.
          rewrite <- (Int.unsigned_repr (cquota _)); [reflexivity | cbn; omega].
        - unfold container_get_usage_high_spec.
          rewrite Hid; rewrite Hused.
          repeat f_equal.
          rewrite <- (Int.unsigned_repr (cusage _)); [reflexivity | cbn; omega].
        - rewrite Husg_quo; reflexivity.
        - repeat step_tac.
      }
    Qed.
    *)
    Admitted.

    Lemma container_split_code :
      container_intro_L ⊢ (id, Msplit) : (container_split ↦ container_split_cprimitive).
    Proof.
    (*
      code_proof_tac.
      find_prim container_get_nchildren.
      find_prim container_get_usage.
      find_prim container_node_init.
      find_prim container_set_usage.
      find_prim container_set_nchildren.
      inv CStep.
      unfold container_split_high_spec in H2.
      repeat destr_in H2; inv H2.
      destruct a as (Hnch & Hchid & Hq & Husg & Hquo).
      rename Heqb into Hinit;
      rename Heqb0 into Hused;
      rename Heqb1 into Hchused.
      assert (Hid: 0 <= Int.unsigned id < Int.unsigned id * MAX_CHILDREN + 1 +
                                          Z.of_nat (length (cchildren
                                            (ZMap.get (Int.unsigned id) (cpool d))))).
      { (** [omega] needs help to solve goals with multiplication *)
        assert (Hmul_add: forall x y z, 0 <= x -> 0 < y -> 0 < z -> x < x * y + z).
        { intros.
          cut (x <= x * y); [omega |].
          cut (x * 1 <= x * y); [omega |].
          apply Zmult_le_compat_l; omega.
        }
        pose MAX_CHILDREN_range as Hmc_range.
        pose (Int.unsigned_range id) as Hid_pos.
        rewrite <- Z.add_assoc.
        split; [omega | apply Hmul_add; omega].
      }
      assert (Hchid_repr:
        Int.unsigned id * MAX_CHILDREN + 1 +
          Z.of_nat (length (cchildren (ZMap.get (Int.unsigned id) (cpool d)))) =
        Int.unsigned
          (Int.add (Int.add (Int.mul id (Int.repr MAX_CHILDREN)) (Int.repr 1))
                   (Int.repr (Z.of_nat (length (cchildren (ZMap.get (Int.unsigned id) (cpool d)))))))).
      { unfold Int.add, Int.mul.
        fold Int.one; rewrite Int.unsigned_one.
        pose MAX_CHILDREN_range as Hmc_range.
        pose NUM_ID_range as Hnid_range.
        specialize (Int.unsigned_range id) as Hid_pos.
        assert (0 <= Int.unsigned id * MAX_CHILDREN) by (apply Z.mul_nonneg_nonneg; omega).
        repeat rewrite Int.unsigned_repr; try omega.
      }
      cprim_step. repeat step_tac.
      - unfold container_get_nchildren_high_spec.
        rewrite Hused. destruct (decide (_ <= _ < _)); [| omega].
        repeat f_equal.
        pose MAX_CHILDREN_range as Hmc_range.
        rewrite <- (Int.unsigned_repr (Z.of_nat _)); [reflexivity | omega].
      - unfold container_get_usage_high_spec.
        rewrite Hused. destruct (decide (_ <= _ < _)); [| omega].
        repeat f_equal.
        rewrite <- (Int.unsigned_repr (cusage _)); [reflexivity | cbn; omega].
      - unfold container_node_init_high_spec.
        rewrite Hinit.
        destr; [reflexivity |].
        exfalso; generalize n.
        rewrite <- Hchid_repr. intros; omega.
      - unfold container_set_usage_high_spec; cbn.
        rewrite ZMap.gso.
        rewrite Hused. destruct (decide (_ <= _ < NUM_ID)); [| omega].
        destr; [reflexivity |].
        exfalso; generalize n.
        unfold Int.add.
        repeat rewrite Int.unsigned_repr; intros; try (cbn; omega).
        rewrite <- Hchid_repr.
        assert (Hlt_neq: forall x y, x = y -> x < y -> False) by (intros; omega).
        destruct Hid as (_ & Hid). unfold not; intros.
        apply Hlt_neq in Hid; auto.
      - unfold container_set_nchildren_high_spec; cbn.
        rewrite ZMap.gss; cbn.
        destruct (decide (_ <= _ < _)); [| omega].
        destruct (decide (_ <= _)); [| omega].
        reflexivity.
      - cbn.
        pose proof Hchid_repr as Hchid_repr'.
        apply (f_equal Int.repr) in Hchid_repr. rewrite Int.repr_unsigned in Hchid_repr.
        rewrite <- Hchid_repr. rewrite ZMap.set2. unfold Int.add.
        repeat rewrite Int.unsigned_repr; try (cbn; omega).
        step_tac.
        rewrite Hchid_repr'. apply Int.unsigned_range_2.
    Qed.
    *)
    Admitted.

  End CodeLowSpecSim.

  (** ** Layer Relation *)
  Section LowHighSpecRel.

    Inductive match_data : container_layerdata -> mem -> Prop :=
    | match_data_intro: forall m (abs: container_layerdata),
        match_data abs m.

    Record relate_data (hadt: container_layerdata) (ladt: container_intro_layerdata) :=
      mkrelate_data {
        init_rel: init_flag hadt = init_flag ladt;
        cpool_rel: cpool hadt = cpool ladt
      }.

    Definition abrel_components_container_container_intro :
      abrel_components container_layerdata container_intro_layerdata :=
      {|
        abrel_relate := relate_data;
        abrel_match  := match_data;
        abrel_new_glbl := nil
      |}.

    Global Instance rel_ops :
      AbstractionRelation _ _ abrel_components_container_container_intro.
    Proof.
      constructor.
      - constructor; auto.
      - intros; constructor.
      - repeat red; cbn. intros d m1 m2 Hunchange Hmatch1.
        inv Hmatch1; econstructor.
      - decision.
    Qed.

    Definition abrel_container_container_intro :
      abrel container_layerdata container_intro_layerdata :=
      {|
        abrel_ops := abrel_components_container_container_intro;
        abrel_prf := rel_ops
      |}.

    Definition container_R : simrel _ _ :=
      abrel_simrel _ _ abrel_container_container_intro.

  End LowHighSpecRel.

  (** ** Refinement Proofs *)
  Section LowHighSpecSim.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce : build_composite_env (t_container_comp :: nil) = OK ce.

    Lemma container_init_refine :
      (container_init ↦ container_init_cprimitive) ⊢ (inv ∘ container_R ∘ inv, ∅) : container_init_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inv InvHi.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_init_high_spec in H1.
      repeat destr_in H1; inv H1.
      do 3 eexists; split.
      - econstructor; eauto.
        unfold container_node_init_high_spec.
        pose NUM_ID_range as Hnid_range.
        repeat destr; (auto || intuition).
      - split.
        + cbn. constructor.
        + split; auto; cbn.
          constructor; auto.
          * constructor; cbn; auto.
            rewrite <- cpool_rel0.
            inv cprimitive_inv_init_state_data_inv.
            rewrite preinit_inv0; auto.
          * constructor.
    Qed.

    Lemma container_can_consume_refine :
      (container_can_consume ↦ container_can_consume_cprimitive) ⊢ (container_R, ∅) : container_can_consume_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8. inv_monad H0. inv H0.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_can_consume_high_spec in H3.
      do 4 (destr_in H3; try discriminate). inv H3.
      rename Heqs into Hi.
      rename Heqs0 into Hquo_usg.
      rename Heqb0 into Hinit.
      rename Heqb1 into Hused.
      cbn in *; subst.
      destr.
      { (** usage + n <= quota *)
        rename Heqs into Hquo_n.
        do 3 eexists; split.
        - econstructor; eauto.
          unfold container_can_consume_high_spec.
          cbn; rewrite <- cpool_rel0; rewrite <- init_rel0.
          rewrite Hi; rewrite Hquo_usg; rewrite Hused.
          eauto.
        - rewrite Hquo_n.
          split; constructor; auto.
      }
      { (** usage + n > quota *)
        rename Heqs into Hquo_n.
        do 3 eexists; split.
        - econstructor; eauto.
          unfold container_can_consume_high_spec.
          cbn; rewrite <- cpool_rel0; rewrite <- init_rel0.
          rewrite Hi; rewrite Hquo_usg; rewrite Hused.
          eauto.
        - rewrite Hquo_n.
          split; constructor; auto.
      }
    Qed.

    Lemma container_alloc_refine :
      (container_alloc ↦ container_alloc_cprimitive) ⊢ (container_R, ∅) : container_alloc_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8. inv_monad H0.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_alloc_high_spec in H2.
      repeat destr_in H2; try discriminate; inv H2;
      rename Heqs into Hi;
      rename Heqs0 into Hquo_usg;
      rename Heqb0 into Hinit;
      rename Heqb1 into Hused;
      cbn in *; subst.
      { (** usage < quota *)
        rename Heqs1 into Husg_quo.
        do 3 eexists; split.
        - econstructor; eauto.
          unfold container_alloc_high_spec.
          cbn; rewrite <- cpool_rel0; rewrite <- init_rel0.
          rewrite Hi; rewrite Hquo_usg; rewrite Hused.
          rewrite Husg_quo. eauto.
        - split; constructor; auto.
          repeat constructor; auto; cbn in *.
          + eapply abrel_match_mem_perms; eauto.
          + eapply abrel_match_mem_nextblock; eauto.
          + eapply abrel_match_mem_nextblock; eauto.
      }
      { (** usage >= quota *)
        rename Heqs1 into Husg_quo.
        do 3 eexists; split.
        - econstructor; eauto.
          unfold container_alloc_high_spec.
          cbn; rewrite <- cpool_rel0; rewrite <- init_rel0.
          rewrite Hi; rewrite Hquo_usg; rewrite Hused.
          rewrite Husg_quo. eauto.
        - split; constructor; auto.
      }
    Qed.

    Lemma container_split_refine :
      (container_split ↦ container_split_cprimitive) ⊢ (container_R, ∅) : container_split_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_split_high_spec in H1.
      repeat destr_in H1; try discriminate. inv H1.
      destruct a as (Hnch & Hchid & Hq & Husg & Hquo).
      rename Heqs into Hranges;
      rename Heqb into Hinit;
      rename Heqb0 into Hused;
      rename Heqb1 into Hchused.
      do 3 eexists; split.
      - econstructor; eauto.
        unfold container_split_high_spec; cbn.
        rewrite <- init_rel0; rewrite <- cpool_rel0.
        rewrite Hranges; rewrite Hused; rewrite Hchused.
        reflexivity.
      - split; cbn.
        + rewrite H3; rewrite Int.repr_unsigned. constructor.
        + split; auto.
          repeat (constructor; auto).
    Qed.

  End LowHighSpecSim.

  (** ** Linking *)
  Section Linking.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce : build_composite_env (t_container_comp :: nil) = OK ce.

    Definition container_L : clayer container_layerdata :=
      container_init_layer
      ⊕ container_can_consume_layer
      ⊕ container_alloc_layer
      ⊕ container_split_layer.

    Definition container_Σ : clayer container_intro_layerdata :=
      container_init ↦ container_init_cprimitive
      ⊕ container_can_consume ↦ container_can_consume_cprimitive
      ⊕ container_alloc ↦ container_alloc_cprimitive
      ⊕ container_split ↦ container_split_cprimitive.

    Definition container_M : cmodule :=
      Minit
      ⊕ Mconsume
      ⊕ Malloc
      ⊕ Msplit.

    Hint Resolve container_init_code container_init_refine
                 container_can_consume_code container_can_consume_refine
                 container_alloc_code container_alloc_refine
                 container_split_code container_split_refine : linking.

    Hint Resolve container_intro_pres_inv : linking.

    Theorem container_link :
      container_intro_L ⊢ (inv ∘ container_R ∘ inv, container_M) : container_L.
    Proof. link_tac container_Σ. Qed.

    Lemma container_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) container_L.
    Proof. unfold container_L. typeclasses eauto. Qed.

    Hint Resolve container_intro_link container_link : linking.

    Theorem container_container_intro_link :
      boot_L ⊢ (container_intro_R ∘ inv ∘ container_R ∘ inv, container_intro_M ⊕ container_M) : container_L.
    Proof.
      apply (vdash_rel_equiv _ _ (container_intro_R ∘ (inv ∘ container_R ∘ inv))).
      rewrite cat_compose_assoc; rewrite cat_compose_assoc; reflexivity.
      eapply vcomp_rule; auto with linking.
    Qed.

  End Linking.

End Container.
