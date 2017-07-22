(**
 * QueueData.v
 *
 * Definitions and properties of queue and node data.
 *)

(** Compcert helper lib *)
Require Import Coqlib.
Require Import Maps.
(** Compcert types and semantics *)
Require Import AST.
Require Import Integers.
Require Import Values.
(** CertiKOS layer library *)
Require Import Structures.
Require Import AbstractData.
Require Import AbstractionRelation.
Require Import SimulationRelation.
Require Import CPrimitives.
Require Import MemWithData.
Require Import Decision.

Require Import TutoLib.

(** This file contains the definitions of the abstract data for the queue
  layers as well as some auxiliary lemmas. The queue is represented at the low
  level by a doubly-linked list where indices into a fixed-size array are used
  instead of pointers. This is then abstracted in the top layer to a
  Coq [list]. This example differs from the other two by having two layers at
  the same level ([Node] and [QueueIntro]), and then building on top of their
  composition. One consequence of this is that the both the abstract data as
  well as the [match_data] and [relate_data] relations must be the same for
  both layers. For this reason, these definitions are in this file instead of
  their usual places. *)

Open Scope Z_scope.

Definition MAX_NODES : Z := 1024.
Fact MAX_NODES_range : 0 < 12 * MAX_NODES <= Int.max_unsigned.
Proof. cbv. intuition. Qed.

Global Opaque MAX_NODES.

(** ** Node Representations *)
Section NODE_DATA.

  (** *** Low Level Definition *)

  (** The low level node represents a node in a typical C doubly-linked list *)
  Inductive node_low : Type :=
  | NodeUndef
  | Node (data: Z) (next: Z) (prev: Z).

  Definition node_pool := ZMap.t node_low.

  (** Struct offsets *)
  Definition data_off := 0.
  Definition next_off := 4.
  Definition prev_off := 8.
  Definition node_sz := 12.

  (** A node is valid if it only points to nodes in the appropriate range. *)
  Inductive node_valid : node_low -> Prop :=
  | NodeOk: forall d nxt prv,
      0 <= nxt <= MAX_NODES ->
      0 <= prv <= MAX_NODES ->
      node_valid (Node d nxt prv).

  (** Sanity check. *)
  Remark node_undef_not_valid : ~node_valid NodeUndef.
  Proof. red; intros; inv H. Qed.

  (** *** Abstract Definition *)

  (** The high level node just stores data and keeps track of whether it is
    currently in the queue. *)
  Inductive abs_node : Type :=
  | AbsNodeUndef
  | AbsNode (data: Z) (inQ: bool).

  Definition abs_node_pool := ZMap.t abs_node.

  (** All non-undef nodes are valid here. *)
  Inductive abs_node_valid : abs_node -> Prop :=
  | AbsNodeOk: forall d inq,
      abs_node_valid (AbsNode d inq).

  Remark abs_node_undef_not_valid : ~abs_node_valid AbsNodeUndef.
  Proof. red; intros; inv H. Qed.

End NODE_DATA.

Ltac unfold_node_fields :=
  unfold node_sz, data_off, next_off, prev_off in *.

(** ** Queue Representations *)
Section QUEUE_DATA.

  (** *** Low Level Definition *)

  (** The low level queue is also essentially a C-style doubly-linked list. *)
  Inductive queue_low : Type :=
  | QueueUndef
  | Queue (head: Z) (tail: Z).

  (** Struct offsets. *)
  Definition head_off := 0.
  Definition tail_off := 4.
  Definition queue_sz := 8.

  (** A queue is valid if its head and tail are in the appropriate range. *)
  Inductive queue_valid : queue_low -> Prop :=
  | QVOk: forall hd tl,
      0 <= hd <= MAX_NODES ->
      0 <= tl <= MAX_NODES ->
      queue_valid (Queue hd tl).

  Remark queue_undef_not_valid : ~queue_valid QueueUndef.
  Proof. red; intros; inv H. Qed.

  (** ** Abstract Definition *)

  (** The high level queue is just a Coq [list]. *)
  Inductive abs_queue : Type :=
  | AbsQueueUndef
  | AbsQueue (q: list Z).

  (** Here a queue is valid if all of its nodes are in the right range. *)
  Inductive abs_queue_valid : abs_queue -> Prop :=
  | AQVQOk: forall q,
      Forall (fun nd => 0 <= nd < MAX_NODES) q ->
      abs_queue_valid (AbsQueue q).

  Remark abs_queue_undef_not_valid : ~abs_queue_valid AbsQueueUndef.
  Proof. red; intros; inv H. Qed.

  (** The elements of a queue are unique if each appears exactly once. *)
  Inductive abs_queue_unique : abs_queue -> Prop :=
  | AQUOk: forall q,
      Forall (fun nd => count_occ zeq q nd = 1%nat) q ->
      abs_queue_unique (AbsQueue q).

  (** The [inQ] flag of [abs_node] should actually mean the node is in the
    queue. *)
  Inductive In_Q_inQ : abs_queue -> Z -> abs_node_pool -> Prop :=
  | IQOk: forall q nd anpool dat inQ,
      ZMap.get nd anpool = AbsNode dat inQ ->
      (inQ = true <-> In nd q) ->
      In_Q_inQ (AbsQueue q) nd anpool.

End QUEUE_DATA.

Ltac unfold_queue_fields :=
  unfold queue_sz, head_off, tail_off in *.

(** ** Abstract Data *)
Section ABS_DATA.

  Context `{Hmem: BaseMemoryModel}.

  (** The abstract data tracks both the low level and high level queue
    representations, but each layer will only place invariants on one
    of them. *)
  Record abs_data : Type := {
    init_flag: bool;
    npool: node_pool;
    queue: queue_low;
    anpool: abs_node_pool;
    aqueue: abs_queue
  }.

  Definition abs_data_init : abs_data :=
    {|
      init_flag := false;
      npool := ZMap.init NodeUndef;
      queue := QueueUndef;
      anpool := ZMap.init AbsNodeUndef;
      aqueue := AbsQueueUndef
    |}.

  Instance boot_data_ops : AbstractDataOps unit :=
    {|
      init_data := tt;
      data_inv := fun _ => True;
      data_inject := fun _ _ _ => True
    |}.

  Instance boot_data_data : AbstractData unit.
  Proof. repeat constructor. Qed.

  Definition boot_layerdata : layerdata :=
    {|
      ldata_type := unit;
      ldata_ops  := boot_data_ops;
      ldata_prf  := boot_data_data
    |}.

  Definition boot_L : clayer boot_layerdata := ∅.

  (** The [Intro] layer represents the composition of the [Node] and
    [QueueIntro] layers. *)
  Record intro_inv (d: abs_data) : Prop := {
    npool_valid: forall node,
      let n := ZMap.get node (npool d) in
      0 <= node < MAX_NODES ->
      (n = NodeUndef \/ node_valid n);
    preinit_q: init_flag d = false -> queue d = QueueUndef;
    q_valid: init_flag d = true -> queue_valid (queue d)
  }.

  Instance intro_data_ops : AbstractDataOps abs_data :=
    {|
      init_data := abs_data_init;
      data_inv := intro_inv;
      data_inject := fun _ _ _ => True
    |}.

  Instance intro_data_data : AbstractData abs_data.
  Proof.
    constructor; constructor; cbn; intros; try congruence.
    rewrite ZMap.gi. auto.
  Qed.

  Definition intro_layerdata : layerdata :=
    {|
      ldata_type := abs_data;
      ldata_ops  := intro_data_ops;
      ldata_prf  := intro_data_data
    |}.

  (** Some functions to allow us to fake a record update syntax. *)
  Definition update_init_flag new abs :=
    {|
      init_flag := new;
      npool := npool abs;
      queue := queue abs;
      anpool := anpool abs;
      aqueue := aqueue abs
    |}.

  Definition update_npool new abs :=
    {|
      init_flag := init_flag abs;
      npool := new;
      queue := queue abs;
      anpool := anpool abs;
      aqueue := aqueue abs
    |}.

  Definition update_queue new abs :=
    {|
      init_flag := init_flag abs;
      npool := npool abs;
      queue := new;
      anpool := anpool abs;
      aqueue := aqueue abs
    |}.

  Definition update_anpool new abs :=
    {|
      init_flag := init_flag abs;
      npool := npool abs;
      queue := queue abs;
      anpool := new;
      aqueue := aqueue abs
    |}.

  Definition update_aqueue new abs :=
    {|
      init_flag := init_flag abs;
      npool := npool abs;
      queue := queue abs;
      anpool := anpool abs;
      aqueue := new
    |}.

End ABS_DATA.

(** Shorthand for updating one field of a record. *)
Notation "abs {init_flag : new }" := (update_init_flag new abs) (at level 1).
Notation "abs {npool : new }" := (update_npool new abs) (at level 1).
Notation "abs {queue : new }" := (update_queue new abs) (at level 1).
Notation "abs {anpool : new }" := (update_anpool new abs) (at level 1).
Notation "abs {aqueue : new }" := (update_aqueue new abs) (at level 1).

(** ** Node Properties *)
Section NODE_DATA_PROPS.

  Context `{Hmem: BaseMemoryModel}.

  (** Just like in the container example, we write some general lemmas to
    allow us to rewrite the [Ptrofs] expressions into something simpler. *)
  Lemma node_fields_off_rewrite : forall foff i,
    0 <= Int.unsigned i < MAX_NODES ->
    0 <= foff < node_sz ->
    (Ptrofs.unsigned
      (Ptrofs.add
        (Ptrofs.add Ptrofs.zero
          (Ptrofs.mul (Ptrofs.repr node_sz) (Ptrofs.of_intu i)))
        (Ptrofs.repr foff))) = node_sz * Int.unsigned i + foff.
  Proof.
    intros ? ? Hi_range Hoff_range.
    pose proof MAX_NODES_range as Hmn_range.
    pose proof int_ptrofs_max as Hint_ptr.
    rewrite Ptrofs.add_zero_l.
    unfold Ptrofs.add, Ptrofs.mul, Ptrofs.zero, Ptrofs.of_intu, Ptrofs.of_int.
    unfold_node_fields.
    repeat rewrite Ptrofs.unsigned_repr; omega.
  Qed.

  Corollary node_fields_store_ok : forall foff m m' b i v,
    0 <= Int.unsigned i < MAX_NODES ->
    0 <= foff < node_sz ->
    Mem.store Mint32 m b (node_sz * Int.unsigned i + foff) v = Some m' ->
    Mem.store Mint32 m b
      (Ptrofs.unsigned
        (Ptrofs.add
          (Ptrofs.add Ptrofs.zero
            (Ptrofs.mul (Ptrofs.repr node_sz) (Ptrofs.of_intu i)))
          (Ptrofs.repr foff))) v = Some m'.
  Proof. intros; rewrite node_fields_off_rewrite; auto. Qed.

  Corollary node_fields_load_ok : forall foff m b i v,
    0 <= Int.unsigned i < MAX_NODES ->
    0 <= foff < node_sz ->
    Mem.load Mint32 m b (node_sz * Int.unsigned i + foff) = Some v ->
    Mem.load Mint32 m b
      (Ptrofs.unsigned
        (Ptrofs.add
          (Ptrofs.add Ptrofs.zero
            (Ptrofs.mul (Ptrofs.repr node_sz) (Ptrofs.of_intu i)))
          (Ptrofs.repr foff))) = Some v.
  Proof. intros; rewrite node_fields_off_rewrite; auto. Qed.

  Lemma node_fields_align : forall i off,
    (off = data_off \/ off = next_off \/ off = prev_off) ->
    (4 | node_sz * i + off).
  Proof.
    intros; unfold_node_fields.
    replace (12 * i) with (4 * (3 * i)) by omega.
    apply Z.divide_add_r; [apply Z.divide_factor_l |].
    destruct H as [? | [? | ? ]]; subst.
    - now exists 0.
    - now exists 1.
    - now exists 2.
  Qed.

End NODE_DATA_PROPS.

(** Queue Properties *)
Section QUEUE_DATA_PROPS.

  Context `{Hmem: BaseMemoryModel}.

  Lemma queue_fields_off_rewrite : forall foff,
    0 <= foff < queue_sz ->
    (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr foff))) = foff.
  Proof.
    intros ? Hoff_range.
    pose proof int_ptrofs_max as Hint_ptr.
    rewrite Ptrofs.add_zero_l.
    unfold_queue_fields.
    rewrite Ptrofs.unsigned_repr; cbn in *; omega.
  Qed.

  Corollary queue_fields_store_ok : forall foff m m' b v,
    0 <= foff < queue_sz ->
    Mem.store Mint32 m b foff v = Some m' ->
    Mem.store Mint32 m b
      (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr foff))) v = Some m'.
  Proof. intros; rewrite queue_fields_off_rewrite; auto. Qed.

  Corollary queue_fields_load_ok : forall foff m b v,
    0 <= foff < queue_sz ->
    Mem.load Mint32 m b foff = Some v ->
    Mem.load Mint32 m b
      (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr foff))) = Some v.
  Proof. intros; rewrite queue_fields_off_rewrite; auto. Qed.

  Lemma queue_fields_align : forall off,
    (off = head_off \/ off = tail_off) ->
    (4 | off).
  Proof.
    intros; unfold_queue_fields; destruct H.
    - now exists 0.
    - now exists 1.
  Qed.

  (** Some additional lemmas about the uniqueness property. *)
  Lemma unique_unique : forall nd q,
    abs_queue_unique (AbsQueue (nd :: q)) ->
    abs_queue_unique (AbsQueue q).
  Proof.
    intros ? ? Hunique.
    inv Hunique; constructor.
    rewrite Forall_forall in *.
    intros ? Hin.
    assert (Hin': In x (nd :: q)) by (cbn; auto).
    apply H0 in Hin'. cbn in Hin'.
    destruct (zeq nd x); subst; auto.
    inv Hin'.
    rewrite <- count_occ_not_In in H1.
    contradiction.
  Qed.

  Lemma unique_not_in : forall nd q,
    abs_queue_unique (AbsQueue (nd :: q)) ->
    ~In nd q.
  Proof.
    red; intros ? ? Hunique Hin.
    pose proof Hunique as Hunique'. apply unique_unique in Hunique'.
    inv Hunique; inv Hunique'. rewrite Forall_forall in *.
    assert (Hin': In nd (nd :: q)) by (cbn; auto).
    apply H1 in Hin; apply H0 in Hin'.
    cbn in Hin'. rewrite zeq_true in Hin'.
    congruence.
  Qed.

  Lemma unique_not_in_unique : forall nd q,
    abs_queue_unique (AbsQueue q) ->
    ~In nd q ->
    abs_queue_unique (AbsQueue (nd :: q)).
  Proof.
    intros ? ? Hunique Hnin.
    inv Hunique; constructor.
    rewrite Forall_forall in *.
    intros ? Hin; cbn.
    destruct (zeq nd x); subst.
    - rewrite count_occ_not_In in Hnin; eauto.
    - destruct Hin; [contradiction | auto].
  Qed.

  (** A property about nodes not in the queue. *)
  Lemma NIn_Q_inQ : forall q nd anpool dat,
    In_Q_inQ (AbsQueue q) nd anpool ->
    ZMap.get nd anpool = AbsNode dat false ->
    ~In nd q.
  Proof.
    red; intros ? ? ? ? Hinq Hnode Hin.
    inv Hinq. rewrite Hnode in H0; inv H0.
    destruct H1. apply H0 in Hin. discriminate.
  Qed.

End QUEUE_DATA_PROPS.

(** ** Composite Environments *)

(** The [Node] and [QueueIntro] layers also have to have the same
  [composite_env] so these definitions have to be somewhere that both files can
  import from. *)

Definition node_t : ident := 7%positive.
Definition node_t_data : ident := 8%positive.
Definition node_t_next : ident := 9%positive.
Definition node_t_prev : ident := 10%positive.
Notation node_t_struct := (Tstruct node_t noattr).

Definition node_t_comp : composite_definition :=
  Composite node_t Struct
    ((node_t_data, tuint) ::
     (node_t_next, tuint) ::
     (node_t_prev, tuint) ::
     nil)
    noattr.

Definition queue_t : ident := 25%positive.
Definition queue_t_head : ident := 26%positive.
Definition queue_t_tail : ident := 27%positive.
Notation queue_t_struct := (Tstruct queue_t noattr).

Definition queue_t_comp : composite_definition :=
  Composite queue_t Struct
    ((queue_t_head, tuint) ::
     (queue_t_tail, tuint) ::
     nil)
    noattr.

(** ** Intro Layer Relations *)
Section ABS_REL.

  Context `{Hmem: BaseMemoryModel}.

  (** We must combine the [Node] and [QueueIntro] layers together so we can
    build the [Queue] layer on top. In particular, this means defining a
    new abstraction relation where the components are combinations of the
    corresponding components in the [Node] and [QueueIntro] relations. *)

  (** *** Node *)

  Definition NODE_POOL : ident := 6%positive.

  Inductive match_node : node_low -> val -> val -> val -> Prop :=
  | match_node_undef: forall dv nv pv,
      match_node NodeUndef dv nv pv
  | match_node_intro: forall d n p,
      match_node (Node d n p) (Vint (Int.repr d)) (Vint (Int.repr n)) (Vint (Int.repr p)).

  Inductive node_match_data : intro_layerdata -> mem -> Prop :=
  | node_match_data_intro:
      forall m (abs: intro_layerdata) npb
             (Hnpb: find_symbol NODE_POOL = Some npb),
        (forall node, 0 <= node < MAX_NODES ->
          (exists dat nxt prv,
            Mem.load Mint32 m npb (node_sz * node + data_off) = Some (Vint dat) /\
            Mem.load Mint32 m npb (node_sz * node + next_off) = Some (Vint nxt) /\
            Mem.load Mint32 m npb (node_sz * node + prev_off) = Some (Vint prv) /\
            Mem.valid_access m Mint32 npb (node_sz * node + data_off) Writable /\
            Mem.valid_access m Mint32 npb (node_sz * node + next_off) Writable /\
            Mem.valid_access m Mint32 npb (node_sz * node + prev_off) Writable /\
            match_node (ZMap.get node (npool abs))
                       (Vint dat) (Vint nxt) (Vint prv))) ->
        node_match_data abs m.

  Definition node_relate_data (hadt: intro_layerdata) (ladt: boot_layerdata) := True.

  (** *** QueueIntro *)

  Definition QUEUE : ident := 24%positive.

  Inductive match_queue : queue_low -> val -> val -> Prop :=
  | match_queue_undef: forall hv tv,
      match_queue QueueUndef hv tv
  | match_queue_intro: forall h t,
      match_queue (Queue h t) (Vint (Int.repr h)) (Vint (Int.repr t)).

  Inductive queue_intro_match_data : intro_layerdata -> mem -> Prop :=
  | queue_intro_match_data_intro:
      forall m (abs: intro_layerdata) qb
             (Hqb: find_symbol QUEUE = Some qb),
        (exists hd tl,
          Mem.load Mint32 m qb head_off = Some (Vint hd) /\
          Mem.load Mint32 m qb tail_off = Some (Vint tl) /\
          Mem.valid_access m Mint32 qb head_off Writable /\
          Mem.valid_access m Mint32 qb tail_off Writable /\
          match_queue (queue abs)
                      (Vint hd) (Vint tl)) ->
        queue_intro_match_data abs m.

  Definition queue_intro_relate_data (hadt: intro_layerdata) (ladt: boot_layerdata) := True.

  (** Define [match] and [relate] relations by and-ing together the
    corresponding [Node] and [QueueIntro] definitions. *)
  Definition abrel_components_intro_boot :
    abrel_components intro_layerdata boot_layerdata :=
    {|
      abrel_relate :=
        fun D1 D2 =>
          node_relate_data D1 D2 /\ queue_intro_relate_data D1 D2;
      abrel_match  :=
        fun D1 D2 =>
          node_match_data D1 D2 /\ queue_intro_match_data D1 D2;
      abrel_new_glbl :=
        (NODE_POOL, Init_space (MAX_NODES * node_sz) :: nil) ::
        (QUEUE, Init_space queue_sz :: nil) ::
        nil
    |}.

  Global Instance intro_rel_ops :
    AbstractionRelation _ _ abrel_components_intro_boot.
  Proof.
    constructor.
    - split; constructor.
    - intros. split.
      + (** Node match_data *)
        inv_abrel_init_props.
        econstructor; eauto; intros.
        pose MAX_NODES_range as Hmn_range.
        cbn -[Z.mul] in *; unfold_node_fields.
        rewrite Zmax_left in aip_perm by omega.
        destruct aip_load as [aip_load _].
        pose node_fields_align as Halign.
        do 3 eexists.
        repeat match goal with
        | |- _ /\ _ => split
        | |- Mem.load _ _ _ _ = Some _ =>
          apply aip_load; [omega | try omega | auto]
        | |- (4 | 12 * ?x + 0) => exists (3*x); omega
        | |- (4 | ?x * 12) => exists (3*x); omega
        | |- (4 | 12 * ?x + 4) => exists (3*x + 1); omega
        | |- (4 | 12 * ?x + 8) => exists (3*x + 2); omega
        | |- Mem.valid_access _ _ _ (12 * node + ?off) _ =>
            split; cbn -[Z.mul];
            [red; intros; apply aip_perm; omega | auto]
        end.
        rewrite ZMap.gi.
        constructor.
      + (** QueueIntro match_data *)
        inv_abrel_init_props.
        econstructor; eauto; intros.
        (** pose MAX_NODES_range as Hmn_range. *)
        cbn in *; unfold_queue_fields.
        destruct aip_load as [aip_load _].
        pose queue_fields_align as Halign.
        do 2 eexists.
        repeat match goal with
        | |- _ /\ _ => split
        | |- Mem.load _ _ _ _ = Some _ =>
          apply aip_load0; [omega | try omega | auto]
        | |- (4 | 0) => exists 0; omega
        | |- (4 | 4) => exists 1; omega
        | |- (4 | 8) => exists 2; omega
        | |- Mem.valid_access _ _ _ ?off _ =>
            split; cbn;
            [red; intros; apply aip_perm0; omega | auto]
        end.
        constructor.
    - repeat red; cbn. intros d m1 m2 Hunchange [Hnode_match Hqueue_match].
      split.
      + (** Node relate_data *)
        inv Hnode_match; econstructor; eauto.
        intros ? Hnode; specialize (H _ Hnode).
        destruct H as (dat & nxt & prv & ?).
        repeat match goal with
        | H: _ /\ _ |- _ => destruct H
        | H: Mem.valid_access _ _ _ _ _ |- _ => destruct H; red in H
        end.
        do 3 eexists.
        repeat match goal with
        | |- _ /\ _ => split
        | |- Mem.load _ _ _ _ = Some _ =>
            eapply Mem.load_unchanged_on; eauto; red; cbn; eauto
        | |- Mem.valid_access _ _ _ _ _ =>
            split;
            [red; intros; eapply Mem.perm_unchanged_on; eauto; red; cbn |];
            eauto
        end.
        assumption.
      + (** QueueIntro relate_data *)
        inv Hqueue_match; econstructor; eauto.
        destruct H as (hd & tl & ?).
        repeat match goal with
        | H: _ /\ _ |- _ => destruct H
        | H: Mem.valid_access _ _ _ _ _ |- _ => destruct H; red in H
        end.
        do 2 eexists.
        repeat match goal with
        | |- _ /\ _ => split
        | |- Mem.load _ _ _ _ = Some _ =>
            eapply Mem.load_unchanged_on; eauto; red; cbn; eauto
        | |- Mem.valid_access _ _ _ _ _ =>
            split;
            [red; intros; eapply Mem.perm_unchanged_on; eauto; red; cbn |];
            eauto
        end; intros; repeat eexists; eauto.
    - repeat constructor.
  Qed.

  Definition abrel_intro_boot : abrel intro_layerdata boot_layerdata :=
    {|
      abrel_ops := abrel_components_intro_boot;
      abrel_prf := intro_rel_ops
    |}.

  Definition intro_R : simrel _ _ :=
    abrel_simrel _ _ abrel_intro_boot.

End ABS_REL.

(** ** Helper Lemmas *)
Section AUX_LEMMAS.

  (** Some additional properties of Coq [list] functions and how they
    interact with the queue properties. *)

  Lemma remove_nin : forall x xs,
    ~In x xs -> remove zeq x xs = xs.
  Proof.
    induction xs; auto; cbn; intros.
    destruct (zeq x a); [subst |]; try tauto.
    f_equal. auto.
  Qed.

  Lemma remove_neq : forall x y xs,
    x <> y -> In x (remove zeq y xs) <-> In x xs.
  Proof.
    induction xs; cbn; intros; try tauto.
    destruct (zeq y a); [subst |]; cbn; try tauto.
    split; intros; try tauto.
    destruct H0; [congruence | tauto].
  Qed.

  Lemma count_occ_remove_neq : forall x y xs,
    x <> y -> count_occ zeq (remove zeq y xs) x = count_occ zeq xs x.
  Proof.
    induction xs; cbn; intros; try tauto.
    destruct (zeq y a); [subst |]; cbn.
    - rewrite zeq_false; auto.
    - destruct (zeq a x); [subst |]; cbn; try tauto.
      f_equal. tauto.
  Qed.

  Lemma count_occ_app : forall xs ys z,
    count_occ zeq (xs ++ ys) z = (count_occ zeq xs z + count_occ zeq ys z)%nat.
  Proof.
    induction xs.
    - simpl; intros; auto.
    - simpl; intros.
      destruct (zeq a z); simpl; f_equal; apply IHxs.
  Qed.

  Lemma last_In : forall x (q: list Z),
    (q = nil \/ In (last q x) q).
  Proof.
    induction q; auto.
    simpl.
    destruct q; auto.
    destruct IHq; [congruence | auto].
  Qed.

  Lemma remove_last : forall z q,
    ~ In z q ->
    List.remove zeq z (q ++ z :: nil) = q.
  Proof.
    induction q.
    - simpl. rewrite zeq_true. auto.
    - simpl in *.
      intros HNin.
      rewrite zeq_false by (contradict HNin; left; congruence).
      rewrite IHq by tauto.
      reflexivity.
  Qed.

  Lemma last_nonempty_dummy : forall {A} y z xs (x: A),
    last (x :: xs) y = last (x :: xs) z.
  Proof.
    induction xs; simpl in *; try rewrite IHxs; reflexivity.
  Qed.

  Lemma app_last : forall {A} (xs ys : list A) z,
    ys <> nil -> last (xs ++ ys) z = last ys z.
  Proof.
    induction xs.
    - simpl; auto.
    - intros.
      specialize (IHxs ys z H).
      simpl.
      destruct (xs ++ ys) eqn:?; auto; destruct xs; simpl in *; congruence.
  Qed.

  Lemma tail_last : forall dummy (q: list Z),
    q = nil \/  exists q', q = q' ++ (last q dummy :: nil).
  Proof.
    induction q.
    - left; congruence.
    - destruct q.
      + right. exists nil. reflexivity.
      + destruct IHq as [? |[ q' IH]]; [congruence|].
        right. exists (a :: q').
        simpl in *.
        congruence.
  Qed.

   Lemma last_nin_default : forall {A} xs (x y: A),
     ~In x xs -> last xs y = x -> xs = nil.
   Proof.
     intros.
     induction xs.
     - reflexivity.
     - cbn in H0.
       destruct xs.
       + rewrite <- H0 in H.
         contradict H.
         constructor.
         reflexivity.
       + discriminate IHxs.
         * rewrite not_in_cons in H.
           destruct H.
           exact H1.
         * exact H0.
  Qed.

  Lemma Forall_app_inv2 : forall (A: Type) (P: A -> Prop) (xs ys: list A),
    Forall P (xs ++ ys) -> Forall P ys.
  Proof.
    induction xs.
    - simpl; auto.
    - inversion 1. eauto.
  Qed.

  Lemma unique_not_In : forall xs y ys,
    abs_queue_unique (AbsQueue (xs ++ y :: ys)) ->
    ~ In y xs /\ ~In y ys.
  Proof.
    inversion 1 as [q Hcount Hq]. subst.
    repeat rewrite (count_occ_not_In zeq).
    apply Forall_app_inv2 in Hcount.
    inversion Hcount as [| ? ? Hcount' _]. subst.
    rewrite count_occ_app in Hcount'.
    destruct (count_occ zeq xs y); simpl in *;
      rewrite zeq_true in Hcount'; auto; omega.
  Qed.

End AUX_LEMMAS.
