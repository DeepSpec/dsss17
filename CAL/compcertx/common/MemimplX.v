Require compcert.common.Memimpl.
Require MemoryX.

Import Coqlib.
Import Values.
Import Memimpl.
Import MemoryX.


(** Because we need the additional [storebytes_empty] property, we
have to modify the implementation of [storebytes]... *)

Definition is_empty {A: Type} (l: list A):
  {l = nil} + {l <> nil}.
Proof.
  destruct l; (left; congruence) || (right; congruence).
Defined.

Definition storebytes m b o l :=
  if is_empty l then Some m else Memimpl.Mem.storebytes m b o l.

(** ... and we have to again prove every property of [storebytes]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Ltac storebytes_tac thm :=
  simpl; intros;
  match goal with
    | H: storebytes ?m1 _ _ ?l = Some ?m2 |- _ =>
      unfold storebytes in H;
        destruct (is_empty l);
        [ | eapply thm; eassumption ];
        subst l;
        replace m2 with m1 in * by congruence;
        clear H;
        try congruence;
        unfold Memtype.Mem.range_perm, Memimpl.Mem.range_perm,
        Memtype.Mem.valid_access, Memimpl.Mem.valid_access;
        intuition (simpl in *; omega)
  end.

Lemma range_perm_storebytes:
   forall (m1 : Mem.mem) (b : block) (ofs : Z) (bytes : list memval),
   Mem.range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
   exists m2 : Mem.mem, storebytes m1 b ofs bytes = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using Mem.range_perm_storebytes'.
Qed.

Lemma encode_val_not_empty chunk v:
  encode_val chunk v <> nil.
Proof.
  generalize (encode_val_length chunk v). generalize (encode_val chunk v).
  destruct chunk; destruct l; compute; congruence.
Qed.

Lemma storebytes_store:
   forall (m1 : Mem.mem) (b : block) (ofs : Z) (chunk : AST.memory_chunk)
     (v : val) (m2 : Mem.mem),
   storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
   (align_chunk chunk | ofs) -> Mem.store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty (encode_val chunk v)); eauto using Mem.storebytes_store.
  edestruct encode_val_not_empty; eauto.
Qed.

Lemma store_storebytes:
   forall (m1 : Mem.mem) (b : block) (ofs : Z) (chunk : AST.memory_chunk)
     (v : val) (m2 : Mem.mem),
   Mem.store chunk m1 b ofs v = Some m2 ->
   storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty (encode_val chunk v)); eauto using Mem.store_storebytes.
  edestruct encode_val_not_empty; eauto.
Qed.

Lemma loadbytes_storebytes_same:
   forall (m1 : Mem.mem) (b : block) (ofs : Z) (bytes : list memval) (m2 : Mem.mem),
   storebytes m1 b ofs bytes = Some m2 ->
   Mem.loadbytes m2 b ofs (Z.of_nat (length bytes)) = Some bytes.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using Mem.loadbytes_storebytes_same.
  inv H. simpl.
  apply Mem.loadbytes_empty. omega.
Qed.

Lemma storebytes_concat: forall (m : Mem.mem) (b : block) (ofs : Z) (bytes1 : list memval)
         (m1 : Mem.mem) (bytes2 : list memval) (m2 : Mem.mem),
       storebytes m b ofs bytes1 = Some m1 ->
       storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 =
       Some m2 -> storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  unfold storebytes at 1.
  intros until m2.
  case_eq (is_empty bytes1).
  {
    intros.
    subst. inv H0.
    simpl in *.
    replace (ofs + 0) with ofs in * by omega.
    assumption.
  }
  intros.
  unfold storebytes in *.
  destruct (is_empty bytes2).
  {
    inv H1.
    rewrite <- app_nil_end.
    rewrite H.
    assumption.
  }
  exploit (Mem.storebytes_concat m b ofs bytes1 m1 bytes2 m2); eauto.
  intros.
  destruct bytes1; try congruence. (** HERE transparently use is_empty *)
  assumption.
Qed.

Lemma storebytes_split:
   forall (m : Mem.mem) (b : block) (ofs : Z) (bytes1 bytes2 : list memval)
     (m2 : Mem.mem),
   storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
   exists m1 : Mem.mem,
     storebytes m b ofs bytes1 = Some m1 /\
     storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 = Some m2.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty (bytes1 ++ bytes2)).
  {
    subst.
    inv H.
    destruct (app_eq_nil _ _ e). subst. simpl. eauto.
  }
  destruct (is_empty bytes1).
  {
    subst; simpl. replace (ofs + 0) with ofs in * by omega.
    simpl in *.
    destruct (is_empty bytes2); eauto.
    contradiction.
  }
  destruct (is_empty bytes2).
  {
    subst.
    rewrite <- app_nil_end in H. eauto.
  }
  eauto using Mem.storebytes_split.
Qed.

Lemma is_empty_list_forall2:
  forall (A B: Type) (P: A -> B -> Prop) l1 l2,
    list_forall2 P l1 l2 ->
    (l1 = nil <-> l2 = nil).
Proof.
  intros.
  inversion H; subst.
   tauto.
   split; discriminate.
Qed.

Lemma storebytes_within_extends:
   forall (m1 m2 : Mem.mem) (b : block) (ofs : Z) (bytes1 : list memval)
     (m1' : Mem.mem) (bytes2 : list memval),
   Mem.extends m1 m2 ->
   storebytes m1 b ofs bytes1 = Some m1' ->
   list_forall2 memval_lessdef bytes1 bytes2 ->
   exists m2' : Mem.mem,
     storebytes m2 b ofs bytes2 = Some m2' /\ Mem.extends m1' m2'.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty bytes1); destruct (is_empty bytes2); eauto using Mem.storebytes_within_extends.
  * inv H0. eauto.
  * apply is_empty_list_forall2 in H1. exfalso; tauto.
  * apply is_empty_list_forall2 in H1. exfalso; tauto.
Qed.

Lemma storebytes_mapped_inject:
   forall (f : meminj) (m1 : Mem.mem) (b1 : block) (ofs : Z)
     (bytes1 : list memval) (n1 m2 : Mem.mem) (b2 : block)
     (delta : Z) (bytes2 : list memval),
   Mem.inject f m1 m2 ->
   storebytes m1 b1 ofs bytes1 = Some n1 ->
   f b1 = Some (b2, delta) ->
   list_forall2 (memval_inject f) bytes1 bytes2 ->
   exists n2 : Mem.mem,
     storebytes m2 b2 (ofs + delta) bytes2 = Some n2 /\
     Mem.inject f n1 n2.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty bytes1); destruct (is_empty bytes2); eauto using Mem.storebytes_mapped_inject.
  * inv H0. eauto.
  * apply is_empty_list_forall2 in H2. exfalso; tauto.
  * apply is_empty_list_forall2 in H2. exfalso; tauto.
Qed.

Lemma storebytes_empty_inject:
   forall (f : meminj) (m1 : Mem.mem) (b1 : block) (ofs1 : Z)
     (m1' m2 : Mem.mem) (b2 : block) (ofs2 : Z) (m2' : Mem.mem),
   Mem.inject f m1 m2 ->
   storebytes m1 b1 ofs1 nil = Some m1' ->
   storebytes m2 b2 ofs2 nil = Some m2' -> Mem.inject f m1' m2'.
Proof.
  unfold storebytes; simpl; congruence.
Qed.

Lemma storebytes_unchanged_on:
   forall (P : block -> Z -> Prop) (m : Mem.mem) (b : block)
     (ofs : Z) (bytes : list memval) (m' : Mem.mem),
   storebytes m b ofs bytes = Some m' ->
   (forall i : Z, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P b i) ->
   Mem.unchanged_on P m m'.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using Mem.storebytes_unchanged_on.
  inv H. eapply Mem.unchanged_on_refl.
Qed.

(** Additional proof not present in CompCert *)

Lemma storebytes_empty:
  forall m b ofs m',
    storebytes m b ofs nil = Some m'
    -> m' = m.
Proof.
  unfold storebytes. intros.
  destruct (is_empty nil); congruence.
Qed.

(** Because we need the additional [free_range] property, we
have to modify the implementation of [free]... *)

Definition free (m: Mem.mem) (b: block) (lo hi: Z): option Mem.mem :=
  if zle hi lo then Some m else Mem.free m b lo hi.

(** ... and we have to again prove every property of [free]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Ltac free_tac thm :=
  simpl;
  intros;
  match goal with
    | H: free ?m1 _ ?lo ?hi = Some ?m2 |- _ =>
      unfold free in H;
        destruct (zle hi lo);
        try (eapply thm; eassumption);
        try replace m2 with m1 in * by congruence;
        try congruence;
        unfold Mem.range_perm, Memtype.Mem.range_perm, Mem.valid_access, Memtype.Mem.valid_access;
        try intuition omega
  end.

Lemma range_perm_free:
  forall m1 b lo hi,
  Mem.range_perm m1 b lo hi Cur Freeable ->
  exists m2: Mem.mem, free m1 b lo hi = Some m2.
Proof.
  unfold free. intros.
  destruct (zle hi lo); eauto using Mem.range_perm_free'.
Qed.

Lemma free_parallel_extends:
   forall (m1 m2 : Mem.mem) (b : block) (lo hi : Z) (m1' : Mem.mem),
   Mem.extends m1 m2 ->
   free m1 b lo hi = Some m1' ->
   exists m2' : Mem.mem, free m2 b lo hi = Some m2' /\ Mem.extends m1' m2'.
Proof.
  unfold free. intros until 1.
  destruct (zle hi lo); eauto using Mem.free_parallel_extends.
  inversion 1; subst; eauto.
Qed.

(** Additional proof not present in CompCert *)

Lemma free_range:
  forall m1 m1' b lo hi,
    free m1 b lo hi = Some m1' ->
    (lo < hi)%Z \/ m1' = m1.
Proof.
  unfold free. intros.
  destruct (zle hi lo).
   right; congruence.
  left; omega.
Qed.

(** Because we need the additional [inject_neutral_incr] property, we
have to modify the implementation of [inject_neutral]... *)

Definition inject_neutral (thr: block) (m: Mem.mem) :=
  Mem.inject_neutral thr m /\  (forall b, Ple thr b -> forall o k p, ~ Mem.perm m b o k p).

(** ... and we have to again prove every property of [inject_neutral]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Theorem neutral_inject:
  forall m, inject_neutral (Mem.nextblock m) m -> Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m.
Proof.
  destruct 1; eauto using Mem.neutral_inject.
Qed.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr Mem.empty.
Proof.
  split; eauto using Mem.empty_inject_neutral, Mem.perm_empty.
Qed.

Theorem alloc_inject_neutral:
  forall thr m lo hi b m',
  Mem.alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (Mem.nextblock m) thr ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Mem.alloc_inject_neutral.
  intros.
  intro. eapply Mem.perm_valid_block in H5. unfold Mem.valid_block in *.
  apply Mem.nextblock_alloc in H. rewrite H in H5. xomega.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  Mem.store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (Mem.flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Mem.store_inject_neutral.
  intros. intro. eapply H2. eassumption. eauto using Mem.perm_store_2.
Qed.

Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  Mem.drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Mem.drop_inject_neutral.
  intros. intro. eapply H2. eassumption. eauto using Mem.perm_drop_4.
Qed.

(** Additional proof not present in CompCert *)

Theorem inject_neutral_incr:
  forall m thr, inject_neutral thr m -> forall thr', Ple thr thr' -> inject_neutral thr' m.
Proof.
  intros ? ? [[] PERM].
  split.
  split.
   unfold Mem.flat_inj. intros until p. destruct (plt b1 thr'); try discriminate. injection 1; intros until 2; subst. intro. eapply mi_perm. 2: eassumption. unfold Mem.flat_inj. destruct (plt b2 thr). reflexivity. edestruct PERM. 2: eassumption. xomega.
   unfold Mem.flat_inj. intros until p. destruct (plt b1 thr'); try discriminate. injection 1; intros until 2; subst. intro. exists 0; omega.
   unfold Mem.flat_inj. intros until delta. destruct (plt b1 thr'); try discriminate. injection 1; intros until 2; subst. intro.
   intros. eapply memval_inject_incr. eapply mi_memval. 2: assumption. unfold Mem.flat_inj. destruct (plt b2 thr). reflexivity. edestruct PERM. 2: eassumption. xomega.
   unfold inject_incr. unfold Mem.flat_inj. intros until delta. destruct (plt b thr); try discriminate. injection 1; intros until 2; subst. destruct (plt b' thr'); try reflexivity. xomega.
   intros. eapply PERM. xomega.
Qed.

Theorem free_inject_neutral':
  forall m b lo hi m' thr,
  Mem.free m b lo hi = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  intros until 1. intros [? PERM]. intros.
  exploit Mem.free_left_inj; eauto. intro.
  exploit Mem.free_right_inj; eauto.
  intros until p. unfold Mem.flat_inj. destruct (plt b' thr); try discriminate. injection 1; intros until 2; subst. replace (ofs + 0) with ofs by omega. intros. eapply Mem.perm_free_2; eauto.
  split.
   assumption.
  intros. intro. eapply PERM. eassumption. eauto using Mem.perm_free_3.
Qed.

Theorem storebytes_inject_neutral':
  forall m b o l m' thr,
  Mem.storebytes m b o l = Some m' ->
  list_forall2 (memval_inject (Mem.flat_inj thr)) l l ->
  Plt b thr ->
  inject_neutral thr m ->
  inject_neutral thr m'.
Proof.
  inversion 4; subst.
  unfold Mem.inject_neutral in H3.
  generalize H. intro STORE.
  eapply Mem.storebytes_mapped_inj in STORE; eauto.
  Focus 3.
   unfold Mem.flat_inj. destruct (plt b thr); try reflexivity. contradiction.
  destruct STORE as (m2 & STORE & INJ).
  replace (o + 0) with o in * by omega.
  replace m2 with m' in * by congruence.
  split; auto.
  intros; intro. eapply Mem.perm_storebytes_2 in H6; eauto. eapply H4; eauto.
  unfold Mem.meminj_no_overlap.
  unfold Mem.flat_inj. intros.
  destruct (plt b1 thr); try discriminate.
  destruct (plt b2 thr); try discriminate.
  left; congruence.
Qed.

(** Extra properties about drop_perm and extends *)

Theorem drop_perm_right_extends:
  forall m1 m2 b lo hi p m2',
  Mem.extends m1 m2 ->
  Mem.drop_perm m2 b lo hi p = Some m2' ->
  (forall ofs k p, Mem.perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  Mem.extends m1 m2'.
Proof.
  intros. inv H. constructor.
  - rewrite (Mem.nextblock_drop _ _ _ _ _ _ H0). auto.
  - eapply Mem.drop_outside_inj; eauto.
    unfold inject_id; intros. inv H. eapply H1; eauto. omega.
  - intros b0 ofs k p0 H.
    eapply mext_perm_inv; eauto. eapply Mem.perm_drop_4; eauto.
Qed.

Theorem drop_perm_parallel_extends:
  forall m1 m2 b lo hi p m1',
  Mem.extends m1 m2 ->
  Mem.drop_perm m1 b lo hi p = Some m1' ->
  exists m2',
     Mem.drop_perm m2 b lo hi p = Some m2'
  /\ Mem.extends m1' m2'.
Proof.
  intros.
  inv H.
  exploit Mem.drop_mapped_inj; eauto.
  unfold Mem.meminj_no_overlap. unfold inject_id. intros; left; congruence.
  reflexivity.
  replace (lo + 0) with lo by omega.
  replace (hi + 0) with hi by omega.
  destruct 1 as [m2' [FREE INJ]]. exists m2'; split; auto.
  constructor; auto.
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ H0).
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ FREE). auto.
  intros b0 ofs k p0 H.
  exploit Mem.perm_drop_4; eauto.
  intro K. apply mext_perm_inv in K.
  destruct K.
  + destruct (andb (Pos.eqb b0 b) (andb (Z.leb lo ofs) (Z.ltb ofs hi))) eqn:BOOL.
    * repeat rewrite Bool.andb_true_iff in BOOL.
      rewrite Pos.eqb_eq in BOOL.
      rewrite Z.leb_le in BOOL.
      rewrite Z.ltb_lt in BOOL.
      destruct BOOL; subst.
      exploit Mem.perm_drop_2; eauto.
      intro.
      left. eapply Mem.perm_implies; eauto. eapply Mem.perm_drop_1; eauto.
    * rewrite <- not_true_iff_false in BOOL.
      repeat rewrite Bool.andb_true_iff in BOOL.
      rewrite Pos.eqb_eq in BOOL.
      rewrite Z.leb_le in BOOL.
      rewrite Z.ltb_lt in BOOL.
      left. eapply Mem.perm_drop_3; eauto.
      revert BOOL. clear.
      intros.
      assert (( ~ (lo <= ofs) ) <-> ofs < lo) by omega.
      assert (( ~ (ofs < hi) ) <-> hi <= ofs) by omega.
      tauto.
  + right.
    intro U.
    apply H1.
    eapply Mem.perm_drop_4; eauto.
Qed.

(** Additional property about unchanged_on, to prove transitivity
    of ec_mem_extends *)

Lemma unchanged_on_trans_strong (P Q: _ -> _ -> Prop) m1 m2 m3:
  (forall b, Mem.valid_block m1 b -> forall o, P b o -> Q b o) ->
  Mem.unchanged_on P m1 m2 ->
  Mem.unchanged_on Q m2 m3 ->
  Mem.unchanged_on P m1 m3.
Proof.
  inversion 2; subst.
  inversion 1; subst.
  constructor.
  + xomega.
  + intros b ofs k p H3 H4.
    rewrite unchanged_on_perm by auto.
    apply unchanged_on_perm0. eauto.
    unfold Mem.valid_block in *; xomega.
  + intros b ofs H3 H4.
    generalize (Mem.perm_valid_block _ _ _ _ _ H4). intro H5.
    generalize H4. intro H4_.
    rewrite unchanged_on_perm in H4_ by eauto.
    etransitivity.
     eapply unchanged_on_contents0; eauto.
    eauto.
Qed.

(** ... and we need to repackage instances for the CompCert memory model. *)

Lemma perm_free_2:
   forall (m1 : Mem.mem) (bf : block) (lo hi : Z) (m2 : Mem.mem),
   free m1 bf lo hi = Some m2 ->
   forall (ofs : Z) (k : perm_kind) (p : permission),
   lo <= ofs < hi -> ~ Mem.perm m2 bf ofs k p.
Proof.
  free_tac Mem.perm_free_2.
Qed.

Lemma perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  Mem.perm m2 b ofs k p -> Mem.perm m1 b ofs k p.
Proof.
  free_tac Mem.perm_free_3.
Qed.

Global Instance memory_model_ops: Mem.MemoryModelOps Mem.mem.
Proof.
  constructor.
  exact Mem.empty.
  exact Mem.alloc.
  exact free.
  exact Mem.load.
  exact Mem.store.
  exact Mem.loadbytes.
  exact storebytes.
  exact Mem.drop_perm.
  exact Mem.nextblock.
  exact Mem.perm.
  exact Mem.valid_pointer.
  exact Mem.extends.
  exact Mem.magree.
  exact Mem.inject.
  exact inject_neutral.
  exact Mem.unchanged_on.
  exact Mem.unchanged_on.
Defined. (** Qed does not work here, need transparent definitions for MemoryModel* *)

Lemma perm_free_list:
  forall l m m' b ofs k p,
    Memtype.Mem.free_list m l = Some m' ->
    Mem.perm m' b ofs k p ->
    Mem.perm m b ofs k p /\
    (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  Opaque free.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split.  eapply perm_free_3; eauto.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
  Transparent free.
Qed.

Lemma free_left_inject:
  forall f m1 m2 b lo hi m1',
  Mem.inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  Mem.inject f m1' m2.
Proof.
  free_tac Mem.free_left_inject.
Qed.

Lemma free_list_left_inject:
  forall f m2 l m1 m1',
    Mem.inject f m1 m2 ->
    Memtype.Mem.free_list m1 l = Some m1' ->
    Mem.inject f m1' m2.
Proof.
  Opaque free.
  induction l; simpl; intros.
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with m11; auto. eapply free_left_inject; eauto.
  Transparent free.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi m2',
  Mem.inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> Mem.perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  Mem.inject f m1 m2'.
Proof.
  free_tac Mem.free_right_inject.
Qed.

Lemma free_inject:
   forall (f : meminj) (m1 : Mem.mem) (l : list (block * Z * Z))
     (m1' m2 : Mem.mem) (b : block) (lo hi : Z) (m2' : Mem.mem),
   Mem.inject f m1 m2 ->
   Memtype.Mem.free_list m1 l = Some m1' ->
   Memtype.Mem.free m2 b lo hi = Some m2' ->
   (forall (b1 : block) (delta ofs : Z) (k : perm_kind) (p : permission),
    f b1 = Some (b, delta) ->
    Mem.perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi ->
    exists lo1 hi1 : Z, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
   Mem.inject f m1' m2'.
Proof.
  intros.
  eapply free_right_inject; eauto.
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

Lemma free_unchanged_on:
   forall (P : block -> Z -> Prop) (m : Mem.mem) (b : block)
     (lo hi : Z) (m' : Mem.mem),
     free m b lo hi = Some m' ->
   (forall i : Z, lo <= i < hi -> ~ P b i) -> Mem.unchanged_on P m m'.
Proof.
  unfold free. intros.
  destruct (zle hi lo); eauto using Mem.free_unchanged_on.
  inv H. apply Memimpl.Mem.unchanged_on_refl.
Qed.

Lemma magree_free:
  forall (m1 m2 : Mem.mem) (P Q : Memtype.Mem.locset) (b : block) (lo hi : Z) (m1' : Mem.mem),
    Memtype.Mem.magree m1 m2 P ->
    Memtype.Mem.free m1 b lo hi = Some m1' ->
    (forall (b' : block) (i : Z), Q b' i -> b' <> b \/ ~ lo <= i < hi -> P b' i) ->
    exists m2' : Mem.mem, Memtype.Mem.free m2 b lo hi = Some m2' /\ Memtype.Mem.magree m1' m2' Q.
Proof.
  simpl; intros.
  unfold free.
  free_tac Mem.magree_free.
  eexists; split; eauto.
  eapply Mem.magree_monotone; eauto. intros; eapply H1; eauto. right; omega.
Qed.

Lemma free_parallel_inject:
  forall (f : meminj) (m1 m2 : Mem.mem) (b : block) (lo hi : Z) (m1' : Mem.mem)
    (b' : block) (delta : Z),
    Memtype.Mem.inject f m1 m2 ->
    Memtype.Mem.free m1 b lo hi = Some m1' ->
    f b = Some (b', delta) ->
    exists m2' : Mem.mem,
      Memtype.Mem.free m2 b' (lo + delta) (hi + delta) = Some m2' /\ Memtype.Mem.inject f m1' m2'.
Proof.
  simpl; intros.
  unfold free.
  free_tac Mem.free_parallel_inject.
  rewrite zle_true. eexists; split; eauto. omega.
  rewrite zle_false. eapply Mem.free_parallel_inject; eauto. omega.
Qed.

Lemma magree_storebytes_parallel:
  forall (m1 m2 : Mem.mem) (P Q : Memtype.Mem.locset) (b : block) (ofs : Z)
    (bytes1 : list memval) (m1' : Mem.mem) (bytes2 : list memval),
    Mem.magree m1 m2 P ->
    storebytes m1 b ofs bytes1 = Some m1' ->
    (forall (b' : block) (i : Z),
        Q b' i -> b' <> b \/ i < ofs \/ ofs + Z.of_nat (length bytes1) <= i -> P b' i) ->
    list_forall2 memval_lessdef bytes1 bytes2 ->
    exists m2' : Mem.mem, storebytes m2 b ofs bytes2 = Some m2' /\ Mem.magree m1' m2' Q.
Proof.
  simpl; intros.
  unfold storebytes in *.
  destruct (is_empty bytes1). inv H0. inv H2.
  simpl. eexists; split; eauto.
  eapply Mem.magree_monotone; eauto. intros; eapply H1; eauto. simpl. right; omega.
  exploit Mem.magree_storebytes_parallel. eauto. eauto. eauto. eauto. inv H2. simpl. congruence.
  simpl. eauto.
Qed.

Global Instance memory_model: Mem.MemoryModel Mem.mem.
Proof.
  constructor.
  exact  Mem.valid_not_valid_diff.
  exact  Mem.perm_implies.
  exact  Mem.perm_cur_max.
  exact  Mem.perm_cur.
  exact  Mem.perm_max.
  exact  Mem.perm_valid_block.
  exact  Mem.range_perm_implies.
  exact  Mem.range_perm_cur.
  exact  Mem.range_perm_max.
  exact  Mem.valid_access_implies.
  exact  Mem.valid_access_valid_block.
  exact  Mem.valid_access_perm.
  exact  Mem.valid_pointer_nonempty_perm.
  exact  Mem.valid_pointer_valid_access.
  exact  Mem.weak_valid_pointer_spec.
  exact  Mem.valid_pointer_implies.
  exact  Mem.nextblock_empty.
  exact  Mem.perm_empty.
  exact  Mem.valid_access_empty.
  exact  Mem.valid_access_load.
  exact  Mem.load_valid_access.
  exact  Mem.load_type.
  exact  Mem.load_cast.
  exact  Mem.load_int8_signed_unsigned.
  exact  Mem.load_int16_signed_unsigned.
  exact  Mem.loadv_int64_split.
  exact  Mem.range_perm_loadbytes.
  exact  Mem.loadbytes_range_perm.
  exact  Mem.loadbytes_load.
  exact  Mem.load_loadbytes.
  exact  Mem.loadbytes_length.
  exact  Mem.loadbytes_empty.
  exact  Mem.loadbytes_concat.
  exact  Mem.loadbytes_split.
  exact  Mem.nextblock_store.
  exact  Mem.store_valid_block_1.
  exact  Mem.store_valid_block_2.
  exact  Mem.perm_store_1.
  exact  Mem.perm_store_2.
  exact  Mem.valid_access_store'.
  exact  Mem.store_valid_access_1.
  exact  Mem.store_valid_access_2.
  exact  Mem.store_valid_access_3.
  exact  Mem.load_store_similar.
  exact  Mem.load_store_similar_2.
  exact  Mem.load_store_same.
  exact  Mem.load_store_other.
  exact  Mem.load_store_pointer_overlap.
  exact  Mem.load_store_pointer_mismatch.
  exact  Mem.load_pointer_store.
  exact  Mem.loadbytes_store_same.
  exact  Mem.loadbytes_store_other.
  exact  Mem.store_signed_unsigned_8.
  exact  Mem.store_signed_unsigned_16.
  exact  Mem.store_int8_zero_ext.
  exact  Mem.store_int8_sign_ext.
  exact  Mem.store_int16_zero_ext.
  exact  Mem.store_int16_sign_ext.
  exact  Mem.storev_int64_split.
  exact range_perm_storebytes.
  now storebytes_tac Mem.storebytes_range_perm.
  now storebytes_tac Mem.perm_storebytes_1.
  now storebytes_tac Mem.perm_storebytes_2.
  now storebytes_tac Mem.storebytes_valid_access_1.
  now storebytes_tac Mem.storebytes_valid_access_2.
  now storebytes_tac Mem.nextblock_storebytes.
  now storebytes_tac Mem.storebytes_valid_block_1.
  now storebytes_tac Mem.storebytes_valid_block_2.
  exact  storebytes_store.
  exact  store_storebytes.
  exact  loadbytes_storebytes_same.
  now storebytes_tac Mem.loadbytes_storebytes_disjoint.
  now storebytes_tac Mem.loadbytes_storebytes_other.
  now storebytes_tac Mem.load_storebytes_other.
  exact  storebytes_concat.
  exact  storebytes_split.
  exact  Mem.alloc_result.
  exact  Mem.nextblock_alloc.
  exact  Mem.valid_block_alloc.
  exact  Mem.fresh_block_alloc.
  exact  Mem.valid_new_block.
  exact  Mem.valid_block_alloc_inv.
  exact  Mem.perm_alloc_1.
  exact  Mem.perm_alloc_2.
  exact  Mem.perm_alloc_3.
  exact  Mem.perm_alloc_4.
  exact  Mem.perm_alloc_inv.
  exact  Mem.valid_access_alloc_other.
  exact  Mem.valid_access_alloc_same.
  exact  Mem.valid_access_alloc_inv.
  exact  Mem.load_alloc_unchanged.
  exact  Mem.load_alloc_other.
  exact  Mem.load_alloc_same.
  exact  Mem.load_alloc_same'.
  exact  Mem.loadbytes_alloc_unchanged.
  exact  Mem.loadbytes_alloc_same.
  exact range_perm_free.
  now free_tac Mem.free_range_perm.
  now free_tac Mem.nextblock_free.
  now free_tac Mem.valid_block_free_1.
  now free_tac Mem.valid_block_free_2.
  now free_tac Mem.perm_free_1.
  exact  perm_free_2.
  exact  perm_free_3.
  now free_tac Mem.valid_access_free_1.
  now free_tac Mem.valid_access_free_2.
  now free_tac Mem.valid_access_free_inv_1.
  now free_tac Mem.valid_access_free_inv_2.
  now free_tac Mem.load_free.
  now free_tac Mem.loadbytes_free_2.
  exact  Mem.nextblock_drop.
  exact  Mem.drop_perm_valid_block_1.
  exact  Mem.drop_perm_valid_block_2.
  exact  Mem.range_perm_drop_1.
  exact  Mem.range_perm_drop_2'.
  exact  Mem.perm_drop_1.
  exact  Mem.perm_drop_2.
  exact  Mem.perm_drop_3.
  exact  Mem.perm_drop_4.
  exact  Mem.loadbytes_drop.
  exact  Mem.load_drop.
  exact  Mem.extends_refl.
  exact  Mem.load_extends.
  exact  Mem.loadv_extends.
  exact  Mem.loadbytes_extends.
  exact  Mem.store_within_extends.
  exact  Mem.store_outside_extends.
  exact  Mem.storev_extends.
  exact  storebytes_within_extends.
  now storebytes_tac Mem.storebytes_outside_extends.
  exact  Mem.alloc_extends.
  now free_tac Mem.free_left_extends.
  now free_tac Mem.free_right_extends.
  exact  free_parallel_extends.
  exact  Mem.valid_block_extends.
  exact  Mem.perm_extends.
  exact  Mem.valid_access_extends.
  exact  Mem.valid_pointer_extends.
  exact  Mem.weak_valid_pointer_extends.
  exact  Mem.ma_perm.
  exact  Mem.magree_monotone.
  exact  Mem.mextends_agree.
  exact  Mem.magree_extends.
  exact  Mem.magree_loadbytes.
  exact  Mem.magree_load.
  simpl.
  exact magree_storebytes_parallel.
  now storebytes_tac Mem.magree_storebytes_left.
  exact  Mem.magree_store_left.
  exact  magree_free.
  exact  Mem.magree_valid_access.
  exact  Mem.mi_no_overlap.
  exact  Mem.valid_block_inject_1.
  exact  Mem.valid_block_inject_2.
  exact  Mem.perm_inject.
  exact  Mem.range_perm_inject.
  exact  Mem.valid_access_inject.
  exact  Mem.valid_pointer_inject.
  exact  Mem.weak_valid_pointer_inject.
  exact  Mem.address_inject.
  exact  Mem.address_inject'.
  exact  Mem.valid_pointer_inject_no_overflow.
  exact  Mem.weak_valid_pointer_inject_no_overflow.
  exact  Mem.valid_pointer_inject_val.
  exact  Mem.weak_valid_pointer_inject_val.
  exact  Mem.inject_no_overlap.
  exact  Mem.different_pointers_inject.
  exact  Mem.disjoint_or_equal_inject.
  exact  Mem.aligned_area_inject.
  exact  Mem.load_inject.
  exact  Mem.loadv_inject.
  exact  Mem.loadbytes_inject.
  exact  Mem.store_mapped_inject.
  exact  Mem.store_unmapped_inject.
  exact  Mem.store_outside_inject.
  exact  Mem.storev_mapped_inject.
  exact  storebytes_mapped_inject.
  now storebytes_tac Mem.storebytes_unmapped_inject.
  now storebytes_tac Mem.storebytes_outside_inject.
  exact  storebytes_empty_inject.
  exact  Mem.alloc_right_inject.
  exact  Mem.alloc_left_unmapped_inject.
  exact  Mem.alloc_left_mapped_inject.
  exact  Mem.alloc_parallel_inject.
  exact  free_inject.
  exact  free_left_inject.
  exact  free_list_left_inject.
  exact  free_right_inject.
  exact free_parallel_inject.
  exact  Mem.drop_outside_inject.
  exact Mem.self_inject.
  exact  Memimpl.Mem.extends_inject_compose.
  exact Memimpl.Mem.extends_extends_compose.
  exact  neutral_inject.
  exact  empty_inject_neutral.
  exact  alloc_inject_neutral.
  exact  store_inject_neutral.
  exact  drop_inject_neutral.
  simpl; tauto.
  exact Mem.unchanged_on_nextblock.
  exact  Mem.unchanged_on_refl .
  exact Mem.unchanged_on_trans.
  exact Mem.unchanged_on_trans.
  exact  Mem.perm_unchanged_on .
  exact  Mem.perm_unchanged_on_2 .
  exact  Mem.loadbytes_unchanged_on_1 .
  exact  Mem.loadbytes_unchanged_on .
  exact  Mem.load_unchanged_on_1 .
  exact  Mem.load_unchanged_on .
  exact  Mem.store_unchanged_on .
  exact  storebytes_unchanged_on .
  exact  Mem.alloc_unchanged_on .
  exact  free_unchanged_on .
  exact Mem.drop_perm_unchanged_on.
  exact  Mem.unchanged_on_implies.
  exact  Mem.unchanged_on_implies.
  exact  Mem.inject_unchanged_on.
Qed.

(** Here we expose the additional properties that we need, and most of
which are actually already proved in the original CompCert
implementation. *)

Global Instance memory_model_x: Mem.MemoryModelX Mem.mem.
Proof.
  constructor.
  typeclasses eauto.
  exact Memimpl.Mem.extends_extends_compose.
  exact Memimpl.Mem.inject_extends_compose.
  exact Memimpl.Mem.inject_compose.
  exact Memimpl.Mem.extends_inject_compose.
  apply inject_neutral_incr.
  now free_tac free_inject_neutral'.
  apply drop_perm_right_extends.
  apply drop_perm_parallel_extends.
  now storebytes_tac storebytes_inject_neutral'.
  exact free_range.
  exact storebytes_empty.
  exact unchanged_on_trans_strong.
Qed.
