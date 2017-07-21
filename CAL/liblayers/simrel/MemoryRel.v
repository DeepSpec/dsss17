Require Export compcert.lib.Coqlib.
Require Export compcert.common.Values.
Require Export compcert.common.Memory.
Require Export compcertx.common.MemoryX.
Require Export LogicalRelations.
Require Export OptionOrders.

(** * Relational version of memory model properties *)

(** ** Properties of the relations involved *)

(** In order to integrate [Cur]/[Max] to our relational properties, we
  define the following order. *)

Inductive perm_kind_order: rel perm_kind perm_kind :=
  | perm_kind_order_refl: Reflexive perm_kind_order
  | perm_kind_order_cur_max: perm_kind_order Cur Max.

Global Instance perm_order_preo:
  PreOrder perm_order.
Proof.
  split.
  - exact perm_refl.
  - exact perm_order_trans.
Qed.

Global Instance perm_kind_order_preo:
  PreOrder perm_kind_order.
Proof.
  split.
  - constructor.
  - intros p1 p2 p3 Hp12 Hp23.
    destruct Hp12; inversion Hp23; constructor.
Qed.


Global Instance val_lessdef_preorder:
  PreOrder Val.lessdef.
Proof.
  split.
  - exact Val.lessdef_refl.
  - exact Val.lessdef_trans.
Qed.

Global Instance memrel_extends_preorder `{Mem.MemoryModelX}:
  PreOrder Mem.extends.
Proof.
  split.
  - exact Mem.extends_refl.
  - exact Memtype.Mem.extends_extends_compose.
Qed.

(** ** [Mem.extends] properties *)

(** Note that we have to make these instances low-priority so that
  they don't override the [SimulationRelation] ones and break the
  [transport] tactic. To achieve this we have to use [Properish]
  (ie. [Related]) to avoid the priority flattening phenomenon
  associated with [proper_related]. *)

Section MEM_EXTENDS_REL.
  Context `{Hmem: Mem.MemoryModelX}.

  Global Instance memrel_mext_next:
    Related Mem.extends (eq @@ Mem.nextblock)%rel subrel.
  Proof.
    intros m1 m2 Hm.
    red.
    pose proof (Mem.valid_block_extends m1 m2 (Mem.nextblock m1) Hm) as H1.
    pose proof (Mem.valid_block_extends m1 m2 (Mem.nextblock m2) Hm) as H2.
    unfold Mem.valid_block in *.
    apply Pos.le_antisym.
    - apply Pos.le_nlt.
      rewrite H2.
      apply Pos.lt_irrefl.
    - apply Pos.le_nlt.
      rewrite <- H1.
      apply Pos.lt_irrefl.
  Qed.

  Global Instance memrel_load_extends:
    Monotonic
      Mem.load
      (- ==> Mem.extends ++> - ==> - ==> option_le Val.lessdef) | 10.
  Proof.
    intros chunk m1 m2 Hm b ofs.
    destruct (Mem.load chunk m1 b ofs) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.load_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    constructor; eauto.
  Qed.

  Global Instance memrel_loadv_extends:
    Monotonic
      Mem.loadv
      (- ==> Mem.extends ++> Val.lessdef ++> option_le Val.lessdef) | 10.
  Proof.
    intros chunk m1 m2 Hm v1 v2 Hv.
    destruct (Mem.loadv chunk m1 v1) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.loadv_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    constructor; eauto.
  Qed.

  Global Instance memrel_loadbytes_extends:
    Monotonic
      Mem.loadbytes
      (Mem.extends ++> - ==> - ==> - ==>
       option_le (list_forall2 Memdata.memval_lessdef)) | 10.
  Proof.
    intros m1 m2 Hm b ofs len.
    destruct (Mem.loadbytes m1 b ofs len) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.loadbytes_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    constructor; eauto.
  Qed.

  Global Instance memrel_store_extends:
    Monotonic
      Mem.store
      (- ==> Mem.extends ++> - ==> - ==> Val.lessdef ++>
        option_le Mem.extends) | 10.
  Proof.
    intros chunk m1 m2 Hm b ofs v1 v2 Hv.
    destruct (Mem.store chunk m1 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.store_within_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    constructor; eauto.
  Qed.

  Global Instance memrel_storev_extends:
    Monotonic
      Mem.storev
      (- ==> Mem.extends ++> Val.lessdef ++> Val.lessdef ++>
       option_le Mem.extends) | 10.
  Proof.
    intros chunk m1 m2 Hm a1 a2 Ha v1 v2 Hv.
    destruct (Mem.storev chunk m1 a1 v1) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.storev_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    constructor; eauto.
  Qed.

  Global Instance memrel_storebytes_extends:
    Monotonic
      Mem.storebytes
      (Mem.extends ++> - ==> - ==> list_forall2 Memdata.memval_lessdef ++>
       option_le Mem.extends) | 10.
  Proof.
    intros m1 m2 Hm b ofs bytes1 bytes2 Hbytes.
    destruct (Mem.storebytes m1 b ofs bytes1) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    constructor; eauto.
  Qed.

  Global Instance memrel_alloc_extends:
    Monotonic
      Mem.alloc
      (Mem.extends ++> Z.le --> Z.le ++> Mem.extends * eq) | 10.
  Proof.
    intros m1 m2 Hm lo1 lo2 Hlo hi1 hi2 Hhi.
    destruct (Mem.alloc m1 _ _) as [m1' b] eqn:Hm1'.
    edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    split; eauto.
  Qed.

  Global Instance memrel_free_extends:
    Monotonic
      Mem.free
      (Mem.extends ++> - ==> - ==> - ==> option_le Mem.extends) | 10.
  Proof.
    intros m1 m2 Hm b lo hi.
    destruct (Mem.free m1 b lo hi) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    constructor; eauto.
  Qed.

  Global Instance memrel_valid_block_extends:
    Monotonic Mem.valid_block (Mem.extends ++> - ==> iff) | 10.
  Proof.
    intros m1 m2 Hm b.
    eapply Mem.valid_block_extends; eauto.
  Qed.

  Global Instance memrel_perm_extends:
    Monotonic
      Mem.perm
      (Mem.extends ++> - ==> - ==> perm_kind_order ==> perm_order ++> impl) | 10.
  Proof.
    intros m1 m2 Hm b ofs k1 k2 Hk p1 p2 Hp H.
    eapply Mem.perm_extends; eauto.
    eapply Mem.perm_implies; eauto.
    destruct Hk; eauto.
    eapply Mem.perm_cur_max; eauto.
  Qed.

  Global Instance memrel_valid_access_implies:
    Monotonic
      Mem.valid_access
      (Mem.extends ==> - ==> - ==> - ==> perm_order ==> impl) | 10.
  Proof.
    intros m1 m2 Hm chunk b ofs p1 p2 Hp H.
    eapply Mem.valid_access_implies; eauto.
    eapply Mem.valid_access_extends; eauto.
  Qed.

  Global Instance memrel_valid_pointer_extends:
    Monotonic
      Mem.valid_pointer
      (Mem.extends ++> - ==> - ==> leb) | 10.
  Proof.
    intros m1 m2 Hm b ofs.
    destruct (Mem.valid_pointer m1 b ofs) eqn:Hm1; [|constructor].
    erewrite Mem.valid_pointer_extends; eauto.
    constructor.
  Qed.

  Global Instance memrel_weak_valid_pointer_extends:
    Monotonic
      Mem.weak_valid_pointer
      (Mem.extends ++> - ==> - ==> leb) | 10.
  Proof.
    intros m1 m2 Hm b ofs.
    destruct (Mem.weak_valid_pointer m1 b ofs) eqn:Hm1; [|constructor].
    erewrite Mem.weak_valid_pointer_extends; eauto.
    constructor.
  Qed.

  Global Instance memrel_drop_perm_extends:
    Monotonic
      Mem.drop_perm
      (Mem.extends ++> - ==> - ==> - ==> - ==> option_le Mem.extends) | 10.
  Proof.
    intros m1 m2 Hm b lo hi p.
    destruct (Mem.drop_perm m1 b lo hi p) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.drop_perm_parallel_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'.
    constructor; eauto.
  Qed.
End MEM_EXTENDS_REL.
