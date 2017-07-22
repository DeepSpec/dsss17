(**
 * ContainerType.v
 *
 * Definitions and properties of container data.
 *)

(** Compcert helper lib *)
Require Import Coqlib.
Require Import Maps.
(** Compcert types and semantics *)
Require Import AST.
Require Import Integers.
Require Import Values.
(** CertiKOS layer library *)
Require Import MemWithData.
Require Import Decision.

Require Import TutoLib.

(** This file contains the definitions of the abstract data for the container
  layers as well as some auxiliary lemmas. A container is an object that tracks
  a process' resource usage. In CertiKOS a pool of containers is maintained,
  one per process. Initially, only the root process' container is initialized,
  but new ones can be created using the [split] primitive. This example is a
  slightly simplified from the CertiKOS version, but follows it very closely.
  The fields and their meanings are:
  - [quota]: The maximum amount of memory a process is allowed to use
  - [usage]: The current amount of memory being used by the process
  - [parent]: The id of the process that spawned this one
  - [nchildren]: The number of processes this one has spawned
  - [used]: Whether a container is initialized *)

Open Scope Z_scope.

(** Some constants used throughout. *)
Definition NUM_ID : Z := 1024.
Fact NUM_ID_range : 0 < 20 * NUM_ID <= Int.max_unsigned.
Proof. cbn; omega. Qed.

Definition MAX_CHILDREN : Z := 8.
Fact MAX_CHILDREN_range : 0 < MAX_CHILDREN <= Int.max_unsigned.
Proof. cbv. intuition. Qed.

Definition PAGE_SIZE : Z := 4096.
Fact PAGE_SIZE_range : 0 < PAGE_SIZE <= Int.max_unsigned.
Proof. cbv. intuition. Qed.

Definition VM_USERLO : Z := 1073741824. (** 0x40000000 *)
Definition VM_USERHI : Z := 4026531840. (** 0xF0000000 *)
Fact VM_USERLO_range : 0 <= VM_USERLO < VM_USERHI.
Proof. cbv. intuition. Qed.
Fact VM_USERHI_range : VM_USERLO < VM_USERHI <= Int.max_unsigned.
Proof. cbv. intuition. Qed.

Definition ROOT_QUOTA : Z := 720896.
Fact ROOT_QUOTA_range : 0 <= ROOT_QUOTA <= Int.max_unsigned.
Proof. cbv. intuition. Qed.
Fact ROOT_QUOTA_eq : ROOT_QUOTA = (VM_USERHI - VM_USERLO) / PAGE_SIZE.
Proof. reflexivity. Qed.

(** We make these quantities opaque, because their actual values don't matter
  so long as the facts we proved about their ranges hold. *)
Global Opaque NUM_ID.
Global Opaque MAX_CHILDREN.
Global Opaque PAGE_SIZE.
Global Opaque VM_USERLO.
Global Opaque VM_USERHI.
Global Opaque ROOT_QUOTA.

(** ** Abstract Data *)
Section CONTAINER_DATA.

  (** The abstract data is almost just a Coq version of the C struct, but
    instead of storing just the number of children, we store a list containing
    their process ids. This is purely logical; only the length of the list is
    actually represented in the implementation. *)
  Record container_abs : Type := mkContainer {
    cquota: Z;
    cusage: Z;
    cparent: Z;
    cchildren: list Z;
    cused: bool
  }.

  Definition container_pool := ZMap.t container_abs.

  Definition container_unused := mkContainer 0 0 0 nil false.

  Definition container_pool_init :=
    ZMap.set 0 (mkContainer ROOT_QUOTA 0 0 nil true) (ZMap.init container_unused).

  Record container_data : Type := {
    init_flag: bool;
    cpool: container_pool
  }.

  Definition container_data_init : container_data :=
    {|
      init_flag := false;
      cpool := ZMap.init container_unused
    |}.

  (** The offsets of the fields in the struct. *)
  Definition quo_off := 0.
  Definition usg_off := 4.
  Definition par_off := 8.
  Definition nch_off := 12.
  Definition use_off := 16.
  Definition con_sz := 20.

End CONTAINER_DATA.

Ltac unfold_fields :=
  unfold con_sz, quo_off, usg_off, par_off, nch_off, use_off in *.

(** ** Properties of a Valid Container *)
Section CONTAINER_VALID.

  (** A 'valid' container must satisfy several properties:
    - Only containers for a valid process id can be initialized
    - Only the root process has itself as its parent
    - The quota must be bounded by the maximum unsigned integer
    - The usage must be bounded by the quota
    - A process' parent container must also be initialized
    - All of a process' children's containers must be intialized
    - A process must be in its parent's children (unless it is root)
    - A process must be the parent of all of its children
    - The sum of a process' children's quotas must be bounded by its usage
    - The list of children must not contain duplicates *)
  Inductive child_quotas_bounded : container_pool -> list Z -> Z -> Prop :=
  | cqb_nil: forall cp n,
      0 <= n -> child_quotas_bounded cp nil n
  | cqb_cons: forall cp c cs n m,
      0 <= cquota (ZMap.get c cp) <= m ->
      child_quotas_bounded cp cs n ->
      child_quotas_bounded cp (c :: cs) (n + m).

  Record container_valid (cp: container_pool) : Prop := mkContainerValid {
    cvalid_id: forall i,
      cused (ZMap.get i cp) = true ->
      0 <= i < NUM_ID;
    cvalid_root: forall i,
      cused (ZMap.get i cp) = true ->
      (i = cparent (ZMap.get i cp) <-> (i = 0));
    cvalid_quota: forall i,
      cused (ZMap.get i cp) = true ->
      cquota (ZMap.get i cp) <= Int.max_unsigned;
    cvalid_usage: forall i,
      cused (ZMap.get i cp) = true ->
      0 <= cusage (ZMap.get i cp) <= cquota (ZMap.get i cp);
    cvalid_parent_used: forall i,
      cused (ZMap.get i cp) = true ->
      cused (ZMap.get (cparent (ZMap.get i cp)) cp) = true;
    cvalid_children_used: forall i,
      cused (ZMap.get i cp) = true ->
      Forall (fun j => cused (ZMap.get j cp) = true) (cchildren (ZMap.get i cp));
    cvalid_parents_child: forall i,
      cused (ZMap.get i cp) = true ->
      i <> 0 ->
      In i (cchildren (ZMap.get (cparent (ZMap.get i cp)) cp));
    cvalid_childrens_parent: forall i,
      cused (ZMap.get i cp) = true ->
      Forall (fun j => cparent (ZMap.get j cp) = i) (cchildren (ZMap.get i cp));
    cvalid_cqb: forall i,
      cused (ZMap.get i cp) = true ->
      child_quotas_bounded cp (cchildren (ZMap.get i cp)) (cusage (ZMap.get i cp));
    cvalid_nodup: forall i,
      cused (ZMap.get i cp) = true ->
      NoDup (cchildren (ZMap.get i cp))
  }.

End CONTAINER_VALID.

(** ** Container Properties *)
Section CONTAINER_PROP.

  Context `{Hmem: BaseMemoryModel}.

  Local Ltac zmap_simpl := ((try subst; rewrite ZMap.gss) ||
                            (rewrite ZMap.gso; [| congruence]) ||
                            (try subst; rewrite ZMap.set2) ||
                            (rewrite ZMap.gi)).
  Local Ltac zmap_simpl_in H :=
    ((try subst; rewrite ZMap.gss in H) ||
     (rewrite ZMap.gso in H; [| congruence]) ||
     (try subst; rewrite ZMap.set2) ||
     (rewrite ZMap.gi)).

  (** *** Child Quotas Bounded *)

  (** These lemmas will be needed to prove that the primitives preserve the
    validity of a container. *)
  Lemma cqb_weaken : forall cs cp c n con,
    0 <= cquota con <= cquota (ZMap.get c cp) ->
    child_quotas_bounded cp cs n ->
    child_quotas_bounded (ZMap.set c con cp) cs n.
  Proof.
    induction cs; cbn; intros ? ? ? ? Hquo Hbound; inv Hbound.
    - constructor; assumption.
    - constructor; auto.
      destr_eq a c; zmap_simpl; [omega | auto].
  Qed.

  Lemma cqb_bound : forall cs cp n m,
    n <= m ->
    child_quotas_bounded cp cs n ->
    child_quotas_bounded cp cs m.
  Proof.
    induction cs; cbn; intros ? ? ? Hnm Hbound; inv Hbound.
    - constructor; omega.
    - eapply (IHcs _ _ (m - m0)) in H4; try omega.
      replace m with (m - m0 + m0) by omega.
      constructor; auto.
  Qed.

  Lemma cqb_notin : forall cs cp c n con,
    ~(In c cs) ->
    child_quotas_bounded cp cs n ->
    child_quotas_bounded (ZMap.set c con cp) cs n.
  Proof.
    induction cs; cbn; intros ? ? ? ? Hnin Hbound; inv Hbound.
    - constructor; assumption.
    - constructor; auto.
      destr_eq a c; zmap_simpl; [tauto | auto].
  Qed.

  Lemma cqb_reorder : forall cs cp c1 c2 con1 con2 n,
    c1 <> c2 ->
    child_quotas_bounded (ZMap.set c1 con1 (ZMap.set c2 con2 cp)) cs n ->
    child_quotas_bounded (ZMap.set c2 con2 (ZMap.set c1 con1 cp)) cs n.
  Proof.
    induction cs; cbn; intros ? ? ? ? ? ? Hneq Hbound; inv Hbound.
    - constructor; assumption.
    - constructor; auto.
      repeat rewrite ZMap.gsspec; repeat rewrite ZMap.gsspec in H2.
      destruct (ZIndexed.eq a c2); destruct (ZIndexed.eq a c1); (auto || congruence).
  Qed.

  (** *** Invariant Preservation *)

  (** Lemmas about primitives preserving validity. *)

  Lemma container_unused_valid : container_valid (ZMap.init container_unused).
  Proof.
    constructor; intros; rewrite ZMap.gi in *; discriminate.
  Qed.

  Lemma container_init_valid : container_valid container_pool_init.
  Proof.
    unfold container_pool_init.
    pose proof NUM_ID_range as Hnid_range.
    constructor; intros i; destr_eq i 0; repeat zmap_simpl;
    (easy || auto || discriminate || omega || now constructor || idtac).
  Qed.

  Lemma container_alloc_valid : forall cp i,
    let c := ZMap.get i cp in
    container_valid cp ->
    cused c = true ->
    cusage c < cquota c ->
    container_valid (ZMap.set i {| cquota := cquota c;
                                   cusage := cusage c + 1;
                                   cparent := cparent c;
                                   cchildren := cchildren c;
                                   cused := cused c |} cp).
  Proof.
    intros ? ? ? Hvalid Hused Husg. destruct Hvalid.
    constructor; cbn; intro i'.
    - (** cvalid_id *)
      destr_eq i i'; zmap_simpl; eauto.
    - (** cvalid_root *)
      destr_eq i i'; zmap_simpl; eauto.
    - (** cvalid_quota *)
      destr_eq i i'; zmap_simpl; eauto.
    - (** cvalid_usage *)
      destr_eq i i'; zmap_simpl; eauto.
      cbn; intros _. specialize (cvalid_usage0 _ Hused). subst c; omega.
    - (** cvalid_parent_used *)
      destr_eq i i'; zmap_simpl; cbn; intros.
      + destr_eq (cparent c) i'; [rewrite Heq |]; zmap_simpl; eauto.
      + destr_eq (cparent (ZMap.get i' cp)) i; zmap_simpl; eauto.
    - (** cvalid_children_used *)
      rewrite Forall_forall. intros Hused' i'' Hin.
      destr_eq i i''; zmap_simpl; auto.
      destr_eq i i';
      zmap_simpl_in Hin; zmap_simpl_in Hused';
      specialize (cvalid_children_used0 _ Hused');
      rewrite Forall_forall in cvalid_children_used0; auto.
    - (** cvalid_parents_child *)
      destr_eq i i'; zmap_simpl; cbn; intros Hused' Hneq0.
      + destr_eq (cparent c) i'; [rewrite Heq |]; zmap_simpl; eauto.
        specialize (cvalid_parents_child0 _ Hused Hneq0); subst c.
        rewrite Heq in cvalid_parents_child0; auto.
      + destr_eq (cparent (ZMap.get i' cp)) i; zmap_simpl; eauto.
    - (** cvalid_childrens_parent *)
      rewrite Forall_forall. intros Hused' i'' Hin.
      destr_eq i i''; zmap_simpl.
      + destr_eq i' i''; cbn;
        zmap_simpl_in Hin; zmap_simpl_in Hused';
        specialize (cvalid_childrens_parent0 _ Hused');
        rewrite Forall_forall in cvalid_childrens_parent0; subst c; auto.
      + destr_eq i i'; cbn;
        zmap_simpl_in Hin; zmap_simpl_in Hused';
        specialize (cvalid_childrens_parent0 _ Hused');
        rewrite Forall_forall in cvalid_childrens_parent0; subst c; auto.
    - (** cvalid_cqb *)
      intros Hused'. apply cqb_weaken.
      + specialize (cvalid_usage0 _ Hused); subst c; cbn; omega.
      + destr_eq i i'; zmap_simpl; cbn; [| zmap_simpl_in Hused']; auto.
        apply cqb_bound with (n := cusage c); try omega.
        subst c; auto.
    - (** cvalid_nodup *)
      destr_eq i i'; zmap_simpl; auto.
      cbn; subst c; auto.
  Qed.

  Lemma container_split_valid : forall cp id q,
    let c := ZMap.get id cp in
    let chid := id * MAX_CHILDREN + 1 + Z.of_nat (length (cchildren c)) in
    let child := {| cquota := q;
                    cusage := 0;
                    cparent := id;
                    cchildren := nil;
                    cused := true |} in
    let c' := {| cquota := cquota c;
                 cusage := cusage c + q;
                 cparent := cparent c;
                 cchildren := chid :: cchildren c;
                 cused := cused c |} in
    0 < chid < NUM_ID ->
    cused (ZMap.get chid cp) = false ->
    cused c = true ->
    0 <= q <= (cquota c - cusage c) ->
    container_valid cp ->
    container_valid (ZMap.set id c' (ZMap.set chid child cp)).
  Proof.
    intros ? ? ? ? ? ? ? Hchid Hchused Hused Hq Hvalid.
    pose proof Hvalid as Hvalid'; destruct Hvalid'.
    assert (Hquo: cquota (ZMap.get id cp) <= Int.max_unsigned) by auto.
    assert (Husg: 0 <= cusage (ZMap.get id cp)) by (apply cvalid_usage0; auto).
    constructor; cbn; intros id'.
    - (** cvalid_id *)
      destr_eq id id'; zmap_simpl; auto.
      destr_eq chid id'; zmap_simpl; (auto || omega).
    - (** cvalid_root *)
      subst c; destr_eq chid id'; repeat zmap_simpl; cbn.
      + intros Hused'; split; intros Heq.
        * rewrite <- Heq in Hused. rewrite Hused in Hchused; discriminate.
        * rewrite Heq in Hchid. omega.
      + destr_eq id id'; repeat zmap_simpl; intros Hused'; subst c'; eauto.
    - (** cvalid_quota *)
      destr_eq id id'; zmap_simpl; cbn; auto.
      destr_eq chid id'; zmap_simpl; cbn; auto.
      intros _. cbn in Hquo; subst c; omega.
    - (** cvalid_usage *)
      destr_eq id id'; zmap_simpl; cbn.
      + intros Hused'. subst c; omega.
      + destr_eq chid id'; zmap_simpl; cbn; (auto || omega).
    - (** cvalid_parent_used *)
      destr_eq id id'; zmap_simpl; cbn.
      + destr_eq id' (cparent (ZMap.get id' cp)); [rewrite Heq | subst c];
          repeat zmap_simpl; auto.
        intros Hused'.
        destr_eq chid (cparent (ZMap.get id' cp)); [rewrite Heq |]; zmap_simpl; auto.
      + destr_eq id' chid; repeat zmap_simpl; auto.
        destr_eq id (cparent (ZMap.get id' cp)); repeat zmap_simpl; auto.
        destr_eq chid (cparent (ZMap.get id' cp)); [rewrite Heq |];
          repeat zmap_simpl; auto.
    - (** cvalid_children_used *)
      rewrite Forall_forall. intros Hused' id'' Hin.
      destr_eq id id''; zmap_simpl; auto.
      destr_eq chid id''; zmap_simpl; auto.
      destr_eq id id'; zmap_simpl_in Hin; zmap_simpl_in Hused'.
      + specialize (cvalid_children_used0 _ Hused').
        rewrite Forall_forall in cvalid_children_used0.
        apply cvalid_children_used0.
        inv Hin; [contradiction | auto].
      + destr_eq chid id'; zmap_simpl_in Hin; repeat zmap_simpl_in Hused'.
        * contradiction.
        * specialize (cvalid_children_used0 _ Hused').
          rewrite Forall_forall in cvalid_children_used0; auto.
    - (** cvalid_parents_child *)
      destr_eq id id'; zmap_simpl.
      + intros Hused' Hid'.
        destr_eq id' (cparent c'); [rewrite Heq |]; zmap_simpl.
        * subst c c'; right; cbn; cbn in Heq.
          rewrite <- Heq.
          replace (ZMap.get id' cp) with
                  (ZMap.get (cparent (ZMap.get id' cp)) cp) by congruence.
          apply cvalid_parents_child0; auto.
        * destr_eq chid (cparent c'); [rewrite Heq |]; zmap_simpl; cbn; eauto.
          subst c; cbn in Heq. rewrite Heq in Hchused.
          apply cvalid_parent_used0 in Hused'. congruence.
      + destr_eq chid id'; repeat zmap_simpl; intros Hused' Hid'; cbn; auto.
        destr_eq id (cparent (ZMap.get id' cp)); zmap_simpl; cbn.
        * subst c; auto.
        * destr_eq chid (cparent (ZMap.get id' cp)); [rewrite Heq |];
            zmap_simpl; auto.
          rewrite Heq in Hchused. apply cvalid_parent_used0 in Hused'.
          congruence.
    - (** cvalid_childrens_parent *)
      rewrite Forall_forall.
      destr_eq id id'; zmap_simpl.
      + intros Hused' id'' Hin.
        specialize (cvalid_childrens_parent0 _ Hused).
        rewrite Forall_forall in cvalid_childrens_parent0.
        destr_eq id' id''; zmap_simpl; subst c c'; cbn in *.
        * destruct Hin as [Heq | Hin]; [congruence | auto].
        * destr_eq chid id''; zmap_simpl; auto.
          destruct Hin as [Heq | Hin]; [congruence | auto].
      + destr_eq chid id'; zmap_simpl; intros Hused' id'' Hin; [contradiction |].
        specialize (cvalid_childrens_parent0 _ Hused').
        rewrite Forall_forall in cvalid_childrens_parent0.
        destr_eq id id''; zmap_simpl; try solve [subst c c'; cbn in *; auto].
        destr_eq chid id''; zmap_simpl; auto.
        specialize (cvalid_children_used0 _ Hused').
        rewrite Forall_forall in cvalid_children_used0.
        specialize (cvalid_children_used0 _ Hin).
        congruence.
    - (** cvalid_cqb *)
      destr_eq id id'; zmap_simpl.
      + intros Hused'.
        destr_eq chid id'.
        * rewrite Heq in Hchused. subst c; cbn in Hused'. congruence.
        * constructor; repeat zmap_simpl; cbn; [omega |].
          apply cqb_reorder; auto.
          subst c c'; cbn in *.
          apply cqb_notin.
          -- specialize (cvalid_children_used0 _ Hused').
             rewrite Forall_forall in cvalid_children_used0.
             intros Hin; specialize (cvalid_children_used0 _ Hin).
             congruence.
          -- apply cqb_weaken; [cbn; omega | eauto].
      + destr_eq chid id'; zmap_simpl; cbn; intros Hused'.
        constructor; reflexivity.
        destr_eq id chid; [rewrite Heq; zmap_simpl |].
        * apply cqb_notin; auto.
          specialize (cvalid_children_used0 _ Hused').
          rewrite Forall_forall in cvalid_children_used0.
          intros Hin. specialize (cvalid_children_used0 _ Hin).
          congruence.
        * apply cqb_reorder; auto.
          subst c c'; cbn in *.
          apply cqb_notin.
          -- specialize (cvalid_children_used0 _ Hused').
             rewrite Forall_forall in cvalid_children_used0.
             intros Hin. specialize (cvalid_children_used0 _ Hin).
             congruence.
          -- apply cqb_weaken; [cbn; omega | auto].
    - (** cvalid_nodup *)
      destr_eq id id'; zmap_simpl.
      + intros Hused'. constructor; eauto.
        specialize (cvalid_children_used0 _ Hused).
        rewrite Forall_forall in cvalid_children_used0.
        intros Hin. specialize (cvalid_children_used0 _ Hin).
        congruence.
      + destr_eq chid id'; zmap_simpl; [constructor | auto].
  Qed.

  (** *** Container Struct Field Offsets *)

  (** In the code proofs of the getters and setters, the offset of a particular
    field of a container is represented as the following arithmetic expression
    using Compcert's [Ptrofs] type. This can be simplified to the expression on
    the right, but it is tedious to show this for each field individually, so
    we prove it for all fields here. *)

  Lemma container_fields_off_rewrite : forall foff i,
    0 <= Int.unsigned i < NUM_ID ->
    0 <= foff < con_sz ->
    (Ptrofs.unsigned
      (Ptrofs.add
        (Ptrofs.add Ptrofs.zero
          (Ptrofs.mul (Ptrofs.repr con_sz) (Ptrofs.of_intu i)))
        (Ptrofs.repr foff))) = con_sz * Int.unsigned i + foff.
  Proof.
    intros ? ? Hi_range Hoff_range.
    pose proof NUM_ID_range as Hnid_range.
    pose proof int_ptrofs_max as Hint_ptr.
    rewrite Ptrofs.add_zero_l.
    unfold Ptrofs.add, Ptrofs.mul, Ptrofs.zero, Ptrofs.of_intu, Ptrofs.of_int.
    assert (con_sz <= Int.max_unsigned) by auto.
    unfold_fields.
    repeat rewrite Ptrofs.unsigned_repr; omega.
  Qed.

  Corollary container_fields_store_ok : forall foff m m' b i v,
    0 <= Int.unsigned i < NUM_ID ->
    0 <= foff < con_sz ->
    Mem.store Mint32 m b (con_sz * Int.unsigned i + foff) v = Some m' ->
    Mem.store Mint32 m b
      (Ptrofs.unsigned
        (Ptrofs.add
          (Ptrofs.add Ptrofs.zero
            (Ptrofs.mul (Ptrofs.repr con_sz) (Ptrofs.of_intu i)))
          (Ptrofs.repr foff))) v = Some m'.
  Proof. intros; rewrite container_fields_off_rewrite; auto. Qed.

  Corollary container_fields_load_ok : forall foff m b i v,
    0 <= Int.unsigned i < NUM_ID ->
    0 <= foff < con_sz ->
    Mem.load Mint32 m b (con_sz * Int.unsigned i + foff) = Some v ->
    Mem.load Mint32 m b
      (Ptrofs.unsigned
        (Ptrofs.add
          (Ptrofs.add Ptrofs.zero
            (Ptrofs.mul (Ptrofs.repr con_sz) (Ptrofs.of_intu i)))
          (Ptrofs.repr foff))) = Some v.
  Proof. intros; rewrite container_fields_off_rewrite; auto. Qed.

  (** We will also need to know that the field offsets are aligned on the size
    of an integer (4 bytes). *)
  Lemma container_fields_align : forall i off,
    (off = quo_off \/ off = usg_off \/ off = par_off \/ off = nch_off \/ off = use_off) ->
    (4 | 20 * i + off).
  Proof.
    intros.
    replace (20 * i) with (4 * (5 * i)) by omega.
    apply Z.divide_add_r; [apply Z.divide_factor_l |].
    destruct H as [? | [? | [? | [? | ?]]]]; subst.
    - now exists 0.
    - now exists 1.
    - now exists 2.
    - now exists 3.
    - now exists 4.
  Qed.

End CONTAINER_PROP.
