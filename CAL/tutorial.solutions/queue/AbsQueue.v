(**
 * AbsQueue.v
 *
 * Abstract queue representation.
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
Require Import MakeProgramSpec.
Require Import AbstractData.
Require Import AbstractionRelation.
(* Coq helper tactic *)
Require Import Coq.Program.Tactics. (* For the destruct_conjs tactic. *)

Require Import TutoLib.
Require Import QueueData.
Require Import Queue.

Open Scope Z_scope.

(** In the previous layer (Queue.v), the specification we gave for the
    queue primitives were abstracted to Coq datatypes, but it still
    followed the C implementation closely. We had a set of the nodes
    with next- and prev-indices, but the specification did not
    directly express that the nodes represent an ordered queue, and
    the specification for the primitives were in terms of operations
    like [if decide (tl = MAX_NODES) ...]  which have no intuitive
    meaning.

    In this file we abstract the linked list queue representation to a
    Coq [list].

    Unlike the other layers up to this point, this layer is purely a
    refinement; we add no additional code. We only have to define the
    relation between the representations, give the specifications for
    [enqueue] and [dequeue] on the high level queue, and then prove
    the refinement relation.  *)


Section AbsQueue.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.

  (** ** Abstract Data *)
  Section AbsData.

    (* The data types and invariants are defined in QueueData.v. Here
       we put them together into the abstract datatype for the
       abstract queue layer.

       The data consists of a node pool (anpool) and a list of
       integers (aqueue). The type anpool is similar to the low-level
       npool, but the nodes no longer have next- and prev-fields,
       instead each node carries data, and a boolean flag saying
       whether it is in the list or not.

       The invariants for these say that a node is in the list iff its
       boolean flag is true (inQ_valid), and that and that no node
       appears in the queue twice (abs_q_unique). This also rules out
       cycles. *)

    Record abs_queue_inv (d: abs_data) : Prop := {
      npool_valid: forall node,
        init_flag d = true ->
        0 <= node < MAX_NODES ->
        node_valid (ZMap.get node (npool d));
      npool_range: forall node,
        ~(0 <= node < MAX_NODES) ->
        ZMap.get node (npool d) = NodeUndef;
      preinit_q: init_flag d = false -> queue d = QueueUndef;
      q_valid: init_flag d = true -> queue_valid (queue d);
      inQ_valid: forall node,
        init_flag d = true ->
        0 <= node < MAX_NODES ->
        In_Q_inQ (aqueue d) node (anpool d);
      abs_q_unique: init_flag d = true -> abs_queue_unique (aqueue d)
    }.

    Instance abs_queue_data_ops : AbstractDataOps abs_data :=
      {|
        init_data := abs_data_init;
        data_inv := abs_queue_inv;
        data_inject := fun _ _ _ => True
      |}.

    Instance abs_queue_data_data : AbstractData abs_data.
    Proof.
      constructor; constructor; cbn; intros; try congruence.
      rewrite ZMap.gi; reflexivity.
    Qed.

    Definition abs_queue_layerdata : layerdata :=
      {|
        ldata_type := abs_data;
        ldata_ops  := abs_queue_data_ops;
        ldata_prf  := abs_queue_data_data
      |}.

  End AbsData.

  (** ** High Level Specifications *)
  Section HighSpec.

    (** Now we can define the specifications for the [enqueue] and
        [dequeue] primitives.  These are simpler and more intuitive than
        the low-level specification.

        For enqueue, the preconditions now are that the queue is
        initialized, the node index is in range, and the node we are
        trying to insert is not already in the list (the ``inQ'' flag
        is ``false''.

        When these conditions are true we update the state simply by
        prepending the node index to the list (node :: q), and setting
        ``inQ'' to ``true''.

        The abstract representation of the queue is backwards, with the tail of
        the queue being stored at the head of the list. *)
    Definition abs_enqueue_high_spec (node: Z) (abs: abs_queue_layerdata)
        : option abs_queue_layerdata :=
      if init_flag abs
        then if decide (0 <= node < MAX_NODES)
          then match aqueue abs, ZMap.get node (anpool abs) with
            | AbsQueue q, AbsNode dat false =>
                let n := AbsNode dat true in
                Some abs {aqueue: AbsQueue (node :: q)}
                         {anpool: ZMap.set node n (anpool abs)}
            | _, _ => None
          end
          else None
        else None.

    Definition abs_enqueue_high_sem : cprimitive abs_queue_layerdata :=
      cgensem _ abs_enqueue_high_spec.

    Global Instance abs_enqueue_pres_inv :
      GenSemPreservesInvariant abs_queue_layerdata abs_enqueue_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold abs_enqueue_high_spec in H2.
      destruct Hinv.
      repeat destr_in H2; inv H2.
      specialize (abs_q_unique0 eq_refl).
      constructor; cbn; intros; auto; try congruence.
      - (** In_Q_inQ *)
        destr_eq node (Int.unsigned i); [subst |].
        + econstructor.
          rewrite ZMap.gss; reflexivity.
          split; intros; cbn; auto.
        + apply inQ_valid0 in H2; auto; inv H2.
          econstructor.
          rewrite ZMap.gso; eauto.
          split; intros; cbn.
          * rewrite <- H5. auto.
          * rewrite H5. destruct H2; [congruence | auto].
      - (** abs_queue_unique *)
        inv abs_q_unique0; constructor.
        rewrite Forall_forall in H3; rewrite Forall_forall.
        intros; cbn.
        destruct (zeq (Int.unsigned i) x); [subst |].
        + eapply NIn_Q_inQ in Heqa1; auto.
          rewrite count_occ_not_In in Heqa1.
          eauto.
        + apply H3. destruct H2; [congruence | auto].
    Qed.

    (** For [dequeue], the precondition is that the layer is initialized
       and the list is nonempty, and the effect of the call is to
       delete the last item in it (List.remove zeq hd (tl :: q)).
       It is slightly more complicated due to the more limited
       set of tools for working with the end of a [list].
     *)

    Definition abs_dequeue_high_spec (abs: abs_queue_layerdata)
        : option (abs_queue_layerdata * Z) :=
      if init_flag abs
        then match aqueue abs with
          | AbsQueue (tl :: q) =>
              let hd := last q tl in
              match ZMap.get hd (anpool abs) with
              | AbsNode dat true =>
                  let n := AbsNode dat false in
                  Some (abs {aqueue: AbsQueue (List.remove zeq hd (tl :: q))}
                            {anpool: ZMap.set hd n (anpool abs)}, hd)
              | _ => None
              end
            | _ => None
        end
        else None.

    Definition abs_dequeue_high_sem : cprimitive abs_queue_layerdata :=
      cgensem _ abs_dequeue_high_spec.

    Global Instance abs_dequeue_pres_inv :
      GenSemPreservesInvariant abs_queue_layerdata abs_dequeue_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold abs_dequeue_high_spec in H2.
      destruct Hinv.
      do 5 (destr_in H2; try discriminate).
      inv H2.
      specialize (abs_q_unique0 eq_refl).
      assert (Hnin: ~In z0 l).
      { inv abs_q_unique0. rewrite Forall_forall in H2.
        red; intros.
        assert (In z0 (z0 :: l)) by (cbn; auto).
        apply H2 in H3.
        cbn in H3. rewrite zeq_true in H3. inv H3.
        rewrite <- count_occ_not_In in H6; auto.
      }
      constructor; cbn; intros; auto; try congruence.
      - (** In_Q_inQ *)
        destr_eq node (last l z0); [subst |].
        + econstructor; [rewrite ZMap.gss; auto |].
          split; [discriminate |]; intros.
          destruct (zeq (last l z0) z0).
          * apply remove_In in H3; auto.
          * destruct H3; auto. apply remove_In in H3; auto.
        + apply inQ_valid0 in H2; auto; inv H2.
          econstructor; [rewrite ZMap.gso; eauto |].
          rewrite H6.
          destruct (zeq (last l z0) z0) as [?Heq | ?Hneq].
          * rewrite Heq. rewrite remove_nin; auto.
            split; cbn; intros; auto.
            destruct H2; [congruence | auto].
          * destr_eq z0 node; [subst |].
            -- split; intros; cbn; auto.
            -- split; intros.
               ++ right. destruct H2; [congruence |]. rewrite remove_neq; auto.
               ++ right. destruct H2; [congruence |]. rewrite remove_neq in H2; auto.
      - (** abs_queue_unique *)
        inv abs_q_unique0; constructor.
        rewrite Forall_forall in H3; rewrite Forall_forall.
        intros; cbn.
        destruct (zeq (last l z0) z0) as [?Heq | ?Hneq].
        + rewrite Heq in *.
          assert (x <> z0).
          { red; intros; subst x.
            apply remove_In in H2; auto.
          }
          rewrite count_occ_remove_neq; auto.
          rewrite remove_neq in H2; auto.
          assert (Hin: In x (z0 :: l)) by (cbn; auto).
          erewrite <- count_occ_cons_neq; eauto.
        + destr_eq x z0; [subst |].
          * cbn. rewrite zeq_true. f_equal.
            rewrite <- count_occ_not_In.
            rewrite remove_neq; auto.
          * cbn. rewrite zeq_false; auto.
            destruct H2; [congruence |].
            assert (x <> last l z0).
            { red; intros; subst x.
              apply remove_In in H2; auto.
            }
            rewrite remove_neq in H2; auto.
            assert (Hin: In x (z0 :: l)) by (cbn; auto).
            rewrite count_occ_remove_neq; auto.
            erewrite <- count_occ_cons_neq; eauto.
    Qed.

  End HighSpec.

  (** ** Layer Relation *)
  Section LowHighSpecRel.

    (** Having defined the high-level specification, we now turn to
        the refinement proofs, beginning by defining the refinement
        relations.

        This layer is a pure refinement between abstract states, so
        the C memory plays no role, and we can use a trivial
        always-true relation [match_data].  *)


    Inductive match_data : abs_queue_layerdata -> mem -> Prop :=
    | match_data_intro: forall m abs,
        match_data abs m.

    (** [relate_npool] relates the high and low level node pools. It ensures
      that the [data] field matches between the two node representations. *)
    Inductive relate_npool : abs_node_pool -> node_pool -> Prop :=
    | relate_node_undef:
        relate_npool (ZMap.init AbsNodeUndef) (ZMap.init NodeUndef)
    | relate_npool_intro: forall anp np,
        (forall nd inQ dat,
          0 <= nd < MAX_NODES ->
          ZMap.get nd anp = AbsNode dat inQ ->
          exists nxt prv, ZMap.get nd np = Node dat nxt prv) ->
        relate_npool anp np.

    (** The next component of the refinement relation is perhaps the
        most interesting part of the refinement proof---we need to
        specify what a valid doubly-linked list looks like when it
        represents a given abstract list. For example, consider an
        abstract list with three items:

          [4 :: 9 :: 3 :: nil].

        The corresponding doubly-linked list can be drawn graphically as:

<<<
   tl=4 ----> 4                     9                 3              <---- hd=3
             +---------------+     +-----------+     +-----------------+
         X<--|nxt=MAX_NODES  | <---|nxt=4      | <---|nxt=9            |
             |         prv=9 |---> |     prv=3 |---> |    prv=MAX_NODES|-->X
             +---------------+     +-----------+     +-----------------+
>>>
        Note that we consider the tail to be the front of the list,
        and use MAX_NODES as the null value in the first and last
        items. The hd and tl fields of the low-level queue should
        therefore correspond to the first last item in the list.

        At this point you may want to pause, and try yourself to write
        down a Coq predicate capturing when a node pool and hd/tl
        value correctly represent a list of integers. When you are
        done, you look at the definition we came up with,
        [match_nxt_prv].

        Clearly, there are many equivalent ways to phrase this in Coq
        (e.g., as a fixpoint or an inductive definition), and finding
        one that's convenient to reason about will make a lot of
        difference on the proof. *)

    Fixpoint match_nxt_prv (q: list Z) (hd tl: Z) (next: Z) (np: node_pool) : Prop :=
      match q with
      | nil => hd = MAX_NODES /\ tl = MAX_NODES
      | n :: nil =>
          hd = n /\ tl = n /\
          exists dat, ZMap.get n np = Node dat next MAX_NODES
      | n :: q' =>
          tl = n /\
          exists dat prv,
            ZMap.get n np = Node dat next prv /\
            match_nxt_prv q' hd prv n np
      end.

    Inductive relate_queue : abs_queue -> queue_low -> node_pool -> Prop :=
    | relate_queue_undef:
        relate_queue AbsQueueUndef QueueUndef (ZMap.init NodeUndef)
    | relate_queue_intro: forall q hd tl np,
        match_nxt_prv q hd tl MAX_NODES np ->
        relate_queue (AbsQueue q) (Queue hd tl) np.

    Record relate_data (hadt: abs_queue_layerdata) (ladt: queue_layerdata) := {
      init_rel: init_flag hadt = init_flag ladt;
      npool_rel: relate_npool (anpool hadt) (npool ladt);
      queue_rel: relate_queue (aqueue hadt) (queue ladt) (npool ladt)
    }.

    Definition abrel_components_abs_queue_queue :
      abrel_components abs_queue_layerdata queue_layerdata :=
      {|
        abrel_relate := relate_data;
        abrel_match  := match_data;
        abrel_new_glbl := nil
      |}.

    Global Instance rel_ops :
      AbstractionRelation _ _ abrel_components_abs_queue_queue.
    Proof. repeat constructor. Qed.

    Definition abrel_abs_queue_queue
        : abrel abs_queue_layerdata queue_layerdata :=
      {|
        abrel_ops := abrel_components_abs_queue_queue;
        abrel_prf := rel_ops
      |}.

    Definition abs_queue_R : simrel _ _ :=
      abrel_simrel _ _ abrel_abs_queue_queue.

    (** Some additional properties about [match_nxt_prv]. *)
    Lemma match_nxt_prv_not_in : forall q hd tl next np,
      match_nxt_prv q hd tl next np ->
      (forall nd, ~In nd q ->
         forall node, match_nxt_prv q hd tl next (ZMap.set nd node np)).
    Proof.
      induction q; cbn; intros; auto.
      destruct q.
      - destruct H0 as (? & ? & ? & ?); subst.
        destr_eq a nd; [tauto |].
        rewrite ZMap.gso; eauto.
      - destruct H0 as (? & ? & ? & ? & ?); subst.
        destr_eq a nd; [tauto |].
        rewrite ZMap.gso; auto.
        rewrite H2.
        repeat esplit; auto.
    Qed.

    Lemma match_nxt_prv__last : forall q hd tl next np,
      match_nxt_prv q hd tl next np -> hd = last q hd.
    Proof.
      induction q; simpl.
      - intros; congruence.
      - intros.
        destruct q.
        + destruct H0; auto.
        + destruct H0 as [? [dat [prv [? ?]]]]; eapply IHq; eauto; congruence.
    Qed.

    Lemma match_nxt_prv_Def : forall x q hd tl next np,
      In x q -> match_nxt_prv q hd tl next np -> ZMap.get x np <> NodeUndef.
    Proof.
      induction q.
      - simpl. tauto.
      - simpl.
        destruct q.
        + intuition. destruct H5. congruence.
        + intuition; destruct H4 as [? [? [? ?]]]; eauto; congruence.
    Qed.

    Lemma match_nxt_prv_inv : forall np q x y hd tl tail,
      match_nxt_prv (x :: y :: q) hd tl tail np ->
      match_nxt_prv (y :: q) hd y x np.
    Proof.
      destruct q.
      - intros.
        simpl in *.
        firstorder.
      - intros.
        simpl in H0.
        destruct H0 as [? [dat [prv [? [? ?]]]]].
        subst.
        simpl in *.
        split; [reflexivity |].
        assumption.
    Qed.

    Lemma match_nxt_prv_remove : forall np x xd xn xp y,
      ZMap.get x np = Node xd xn xp ->
      forall q tl next,
        ~ In x q ->
        match_nxt_prv (q ++ x :: y :: nil) y tl next np ->
        match_nxt_prv (q ++ x :: nil) x tl next (ZMap.set x (Node xd xn MAX_NODES) np).
    Proof.
      induction q.
      - simpl. intros ? ? ? [? [? [? [? [? [? [? ?]]]]]]].
        split. auto.
        split. auto.
        exists xd. rewrite ZMap.gss. congruence.
      - destruct q.
        + intros ? ? HNIn Hmatch.
          assert (HNIn': ~ In x nil) by (simpl; tauto).
          specialize (IHq _ _ HNIn' (match_nxt_prv_inv _ _ _ _ _ _ _  Hmatch)).
          simpl in *.
          destruct_conjs.
          split; auto.
          exists H2. exists H6.
          split.
          * rewrite ZMap.gso by (contradict HNIn; auto).
            congruence.
          * split; auto.
            split; auto.
            exists H9.
            rewrite ZMap.gss.
            congruence.
        + intros ? ? HNIn Hmatch.
          assert (HNIn': ~ In x (t :: q)) by (simpl in *; tauto).
          specialize (IHq _ _ HNIn' (match_nxt_prv_inv _ _ _ _ _ _ _  Hmatch)).
          simpl in *.
          destruct Hmatch as [? [adat [aprv [? ?]]]].
          assert (t = aprv) by
            (destruct (q ++ x :: y :: nil); destruct_conjs; auto).
          split. assumption.
          exists adat. exists t.
          split.
          * rewrite ZMap.gso by (contradict HNIn; auto).
            congruence.
          * exact IHq.
    Qed.

    Lemma nxt_of_last : forall y ys hd  np dat nxt prv xs tl tail,
      match_nxt_prv (xs ++ y :: ys) hd tl tail np ->
      ZMap.get y np =  Node dat nxt prv ->
      nxt = last xs tail.
    Proof.
      induction xs.
      - simpl.
        destruct ys; intros; destruct_conjs; congruence.
      - destruct xs as [| x xs].
        + simpl in *.
          intros; destruct ys; destruct_conjs; congruence.
        + intros tl tail Hmatch Hget.
          specialize (IHxs _ _ (match_nxt_prv_inv _ _ _ _ _ _ _ Hmatch) Hget).
          change (last (a :: x :: xs) tail) with (last (x::xs) tail).
          rewrite <- (last_nonempty_dummy a).
          assumption.
    Qed.

  End LowHighSpecRel.

  (** ** Refinement Proofs *)
  Section LowHighSpecSim.

    Context `{ce: ClightCompositeEnv}.

    Lemma abs_enqueue_refine :
      (enqueue ↦ enqueue_high_sem) ⊢ (inv ∘ abs_queue_R ∘ inv, ∅) : (enqueue ↦ abs_enqueue_high_sem).
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inv InvLo.
      inv cprimitive_inv_init_state_data_inv.
      inv InvHi.
      inv cprimitive_inv_init_state_data_inv.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold abs_enqueue_high_spec in H1.
      repeat destr_in H1; inv H1.
      rename Heqs into Hi_range;
      rename a into Hi_rangeP;
      rename Heqa0 into Haqueue;
      rename Heqa1 into Hanode.
      inv queue_rel0.
      inv npool_rel0.
      { rewrite <- H3 in Hanode. rewrite ZMap.gi in Hanode. discriminate. }
      destr_eq tl MAX_NODES; [subst |].
      { (** tail = MAX_NODES *)
        do 3 eexists; split.
        - repeat constructor.
          unfold enqueue_high_spec.
          rewrite <- init_rel0, Hi_range, <- H1.
          eapply H0 in Hanode; auto.
          destruct Hanode as (nxt & prv & Hanode). rewrite Hanode.
          destruct (decide (_ = _)); [auto | congruence].
        - repeat (constructor; auto); cbn; try congruence.
          + intros. destr_eq nd (Int.unsigned i); [subst |].
            * rewrite ZMap.gss.
              rewrite ZMap.gss in H4; inv H4.
              eauto.
            * rewrite ZMap.gso; auto.
              rewrite ZMap.gso in H4; eauto.
          + assert (q = nil).
            { destruct q as [| ? [|]]; cbn in H2; auto.
              - destruct H2 as (? & ? & ? & ?).
                subst.
                rewrite npool_range0 in H4; try omega.
                inv H4.
              - destruct H2 as (? & ? & ? & ? & ?).
                subst.
                rewrite npool_range0 in H3; try omega.
                inv H3.
            }
            subst. rewrite ZMap.gss; eauto.
      }
      { (** tail <> MAX_NODES *)
        assert (Hq: exists nd q', q = nd :: q').
        { destruct q as [| ? [|]]; cbn in H2; eauto.
          destruct H2; congruence.
        }
        destruct Hq as (nd & q' & Hq); subst.
        assert (Htl: exists tldat tlnxt tlprv,
          ZMap.get tl (npool yd) = Node tldat tlnxt tlprv).
        { rewrite <- H1 in q_valid0.
          symmetry in init_rel0.
          specialize (q_valid0 init_rel0).
          inv q_valid0.
          assert (Htl_range: 0 <= tl < MAX_NODES) by omega.
          apply npool_valid0 in Htl_range; auto.
          destruct Htl_range.
          eauto.
        }
        destruct Htl as (tldat & tlnxt & tlprv & Htl).
        do 3 eexists; split.
        - repeat constructor.
          unfold enqueue_high_spec.
          rewrite <- init_rel0, Hi_range, <- H1.
          eapply H0 in Hanode; auto.
          destruct Hanode as (nxt & prv & Hanode). rewrite Hanode.
          destruct (decide (_ = _)); [congruence |].
          rewrite Htl.
          reflexivity.
        - repeat (constructor; auto); cbn; try congruence.
          + intros. destr_eq nd0 (Int.unsigned i); [subst |].
            * rewrite ZMap.gss.
              rewrite ZMap.gss in H4; inv H4.
              eauto.
            * rewrite ZMap.gso; auto.
              rewrite ZMap.gso in H4; auto.
              eapply H0 in H4; auto.
              destruct H4 as (? & ? & ?).
              destr_eq nd0 tl; [subst |].
              -- rewrite ZMap.gss.
                 rewrite H4 in Htl; inv Htl; eauto.
              -- rewrite ZMap.gso; eauto.
          + rewrite ZMap.gss.
            repeat esplit.
            destruct q'; cbn in H2.
            * destruct H2 as (? & ? & ? & ?); subst.
              repeat split; auto.
              rewrite H4 in Htl; inv Htl.
              destr_eq nd (Int.unsigned i); [subst |].
              -- specialize (inQ_valid0 _ eq_refl Hi_rangeP).
                 inv inQ_valid0.
                 cbn in H5; destruct H5.
                 destruct inQ; [congruence |].
                 cut (false = true); [discriminate | auto].
              -- rewrite ZMap.gso; auto.
                 rewrite ZMap.gss; eauto.
            * destruct H2 as (? & ? & ? & ? & ?); subst.
              repeat split; auto.
              destr_eq nd (Int.unsigned i); [subst |].
              -- specialize (inQ_valid0 _ eq_refl Hi_rangeP).
                 inv inQ_valid0.
                 cbn in H6; destruct H6.
                 destruct inQ; [congruence |].
                 cut (false = true); [discriminate | auto].
              -- rewrite H3 in Htl; inv Htl.
                 rewrite ZMap.gso; auto.
                 rewrite ZMap.gss.
                 repeat esplit.
                 apply match_nxt_prv_not_in.
                 apply match_nxt_prv_not_in.
                 auto.
                 apply unique_not_in; auto.
                 cut (~In (Int.unsigned i) (nd :: z :: q')); [cbn; tauto |].
                 eapply NIn_Q_inQ; eauto.
            }
    Qed.

    Lemma abs_dequeue_refine :
      (dequeue ↦ dequeue_high_sem) ⊢ (inv ∘ abs_queue_R ∘ inv, ∅) : (dequeue ↦ abs_dequeue_high_sem).
    Proof.
      Opaque Z.mul.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inv InvLo.
      inv cprimitive_inv_init_state_data_inv.
      inv InvHi.
      inv cprimitive_inv_init_state_data_inv.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      pose proof MAX_NODES_range as Hmn_range.
      unfold abs_dequeue_high_spec in H1.
      do 5 (destr_in H1; try discriminate).
      rename Heqb into Hinit;
      rename Heqa into Haqueue;
      rename Heqa0 into Hahead.
      inv H1.
      inv queue_rel0.
      inv npool_rel0.
      { rewrite <- H4 in Hahead. rewrite ZMap.gi in Hahead. discriminate. }
      rename z into head;
      rename z0 into tail;
      rename l into q;
      rename H3 into Hlast;
      rename H2 into Hq_match;
      rename H1 into Hq;
      rename H0 into Hnode_match;
      destruct (zeq (last q tail) tail) as [Heq | Hneq].
      { (** last q tail = tail (queue = tail :: nil) *)
        assert (Hnin: ~In tail q)
          by (destruct (unique_not_In nil tail q (abs_q_unique0 eq_refl));
              assumption).
        apply last_nin_default in Heq; auto; subst.
        cbn in Hlast; subst.
        cbn in Hq_match. destruct Hq_match as (? & ? & hddat & Hhead); subst.
        assert (Hhead_range: 0 <= Int.unsigned head < MAX_NODES).
        { cut (~~(0 <= Int.unsigned head < MAX_NODES)); try omega.
          red; intros Hrange. apply npool_range0 in Hrange. congruence.
        }
        cbn in Hahead. pose proof Hahead as Hhead'.
        apply Hnode_match in Hhead'; auto.
        destruct Hhead' as (? & ? & Hhead').
        rewrite Hhead in Hhead'; inv Hhead'.
        do 3 eexists; split.
        - repeat constructor.
          unfold dequeue_high_spec.
          rewrite <- init_rel0, <- Hq, Hhead.
          destr; try omega. destr; try omega.
          rewrite Int.unsigned_repr; [reflexivity | cbn; omega].
        - repeat (constructor; auto); cbn; try congruence.
          + rewrite Int.repr_unsigned. constructor.
          + intros ? ? ? ? Hnd. destr_eq nd (Int.unsigned head); [subst |].
            * rewrite ZMap.gss.
              rewrite ZMap.gss in Hnd; inv Hnd.
              eauto.
            * rewrite ZMap.gso; auto.
              rewrite ZMap.gso in Hnd; eauto.
      }
      { (** last q tail <> tail (queue = tail :: tailprev :: queue') *)
        destruct q as [| nd ?]; cbn in Hq_match; [contradiction |].
        destruct Hq_match as (? & tldat & tlprv & Htail & Hq_match); subst.
        assert (Htail_range: 0 <= tail < MAX_NODES).
        { cut (~~(0 <= tail < MAX_NODES)); try omega.
          red; intros Hrange. apply npool_range0 in Hrange. congruence.
        }
        assert (nd = tlprv).
        { (** by Hq_match *)
          destruct q; destruct Hq_match as [? [? ?]]; congruence.
        }
        assert (hd = Int.unsigned head).
        { (** if q = nil, tlprv = head, otherwise hd = last q = head *)
          assert (hd = last (nd :: q) tail).
          {
            rewrite <- (last_nonempty_dummy hd).
            eapply  (match_nxt_prv__last _ _ tlprv tail (npool yd)).
            exact Hq_match.
          }
          congruence.
        }
        subst.
        rewrite Hlast in *.
        assert (Int.unsigned head <> MAX_NODES).
        { rewrite <- Hlast.
          destruct (last_In tail (tlprv :: q)) as [HIn | HIn].
          - congruence.
          - rewrite Hlast in *.
            assert (Hhead_Def := match_nxt_prv_Def _ _ _ _ _ _ HIn Hq_match).
            specialize (npool_range0 (Int.unsigned head)).
            cut (~~(0 <= (Int.unsigned head) < MAX_NODES)); try omega.
            intros Hrange. apply npool_range0 in Hrange. congruence.
        }
        symmetry in init_rel0; specialize (q_valid0 init_rel0).
        inv q_valid0.
        rewrite <- Hq in H1; inv H1.
        assert (Hhead_range: 0 <= Int.unsigned head < MAX_NODES) by omega.
        pose proof Hhead_range as Hhead_range'.
        apply npool_valid0 in Hhead_range'; auto; inv Hhead_range'.
        rename H1 into Hhead.
        assert (nxt <> MAX_NODES).
        { (* if q = nil, hdnxt = tail, else hdnxt = non MAX_NODES *)
          destruct (tail_last tail (tlprv :: q)) as [? | [q' Hq']];
          [congruence |].
          assert (Hnxt_tail:
            match_nxt_prv (tlprv :: q) (Int.unsigned head) tlprv tail (npool yd))
            by (exact Hq_match).
          rewrite Hq' in Hnxt_tail.
          apply nxt_of_last with (dat := d) (nxt := nxt) (prv := prv) in Hnxt_tail.
          assert (Hin: In nxt (tail :: q')).
          {
            destruct (last_In tail q');
              subst; simpl in *; auto.
          }
          destruct Hin.
          - omega.
          - assert (Hin': In nxt (q' ++ last (tlprv :: q) tail :: nil))
              by (rewrite in_app; auto).
            assert (Hq_match':
              match_nxt_prv (tlprv :: q) (Int.unsigned head) tlprv tail (npool yd))
              by (exact Hq_match).
            rewrite Hq' in Hq_match'.
            assert (Hhead_Def := match_nxt_prv_Def _ _ _ _ _ _ Hin' Hq_match').
            specialize (npool_range0 nxt).
            cut (~~(0 <= nxt < MAX_NODES)); try omega.
            intros Hrange. apply npool_range0 in Hrange. congruence.
          - congruence.
        }
        assert (Hnxt_range: 0 <= nxt < MAX_NODES) by omega.
        apply npool_valid0 in Hnxt_range; auto; inv Hnxt_range.
        rename H6 into Hnxt.
        do 3 eexists; split.
        - repeat constructor.
          unfold dequeue_high_spec.
          rewrite init_rel0, <- Hq, <- Hhead, <- Hnxt.
          destr; try omega.
          destr; try omega.
          reflexivity.
        - repeat (constructor; auto); cbn; try congruence.
          + intros nd ? ? Hnd_range Hand.
            destr_eq nd (Int.unsigned head); [subst |].
            * rewrite ZMap.gss.
              rewrite ZMap.gss in Hand; inv Hand.
              apply Hnode_match in Hahead; auto.
              destruct Hahead as (? & ? & Hahead').
              rewrite Hahead' in Hhead; inv Hhead. eauto.
            * rewrite ZMap.gso; auto.
              rewrite ZMap.gso in Hand; auto.
              apply Hnode_match in Hand; auto. destruct Hand as (? & ? & Hand).
              destr_eq nd nxt; [subst |].
              -- rewrite ZMap.gss.
                 rewrite Hand in Hnxt; inv Hnxt; eauto.
              -- rewrite ZMap.gso; eauto.
          + destruct (zeq (Int.unsigned head) tlprv); [subst |].
            * (** queue = tail :: head :: nil *)
              assert (q = nil).
              { (** using that
                     last (Int.unsigned head :: q) tail = Int.unsigned head *)
                change (tail :: Int.unsigned head :: q)
                  with ((tail::nil) ++ Int.unsigned head :: q)
                  in abs_q_unique0.
                destruct (unique_not_In _ _ _ (abs_q_unique0 eq_refl)).
                destruct q.
                - reflexivity.
                - change (last (Int.unsigned head :: z :: q) tail)
                    with (last (z :: q) tail) in Hlast.
                  apply last_nin_default with (x := Int.unsigned head) (y := tail);
                  auto.
              }
              subst; cbn.
              destruct Hq_match as (? & ? & ? & ?); subst.
              assert (nxt = tail) by congruence.
              subst.
              rewrite ZMap.gso; auto. rewrite ZMap.gss.
              rewrite Htail in Hnxt; inv Hnxt.
              eauto.
            * (** queue = tail :: tailprv :: queue' ++ (head :: nil) *)
              assert (Hq_match_reshuffle :
                        match_nxt_prv (tlprv :: q)
                                      (Int.unsigned head)
                                      tlprv
                                      tail
                                      (npool yd))
                by exact Hq_match.
              clear Hq_match.
              rename Hq_match_reshuffle into Hq_match.
              assert (Hqtail: exists q', q = q' ++ (Int.unsigned head :: nil)).
              { (* head = last q *)
                destruct (tail_last tail (tlprv :: q)) as [? | [q' Hq']];
                [congruence |].
                rewrite Hlast in Hq'.
                destruct q'.
                - simpl in *; congruence.
                - exists q'.
                  simpl in *; congruence.
              }
              destruct Hqtail as (q' & Hqtail); subst.
              assert (Hlast_q': nxt = last (tlprv :: q') (Int.unsigned head)).
              {
                change (tlprv :: q'  ++ Int.unsigned head :: nil)
                  with ((tlprv :: q') ++ Int.unsigned head :: nil)
                  in Hq_match.
                symmetry in Hhead.
                assert (Hlast_q' := nxt_of_last _ _ _ _ _ _ _ _ _ _ Hq_match Hhead).
                rewrite <- (last_nonempty_dummy (Int.unsigned head)) in Hlast_q'.
                exact Hlast_q'.
              }
              assert (In nxt (tlprv :: q' ++ Int.unsigned head :: nil)).
              {
                rewrite Hlast_q'.
                destruct (last_In (Int.unsigned head) (tlprv :: q'));
                [congruence |].
                change (tlprv :: q' ++ Int.unsigned head :: nil)
                  with ((tlprv :: q') ++ Int.unsigned head :: nil).
                apply in_or_app.
                left.
                auto.
              }
              assert (tail <> nxt).
              { (** by abs_q_unique *)
                destruct (unique_not_In nil tail _ (abs_q_unique0 eq_refl)).
                intros Hcontra; rewrite Hcontra in *; tauto.
              }
              assert (HNIn_head : ~ In (Int.unsigned head) (tlprv :: q')).
              {
                change (tail :: tlprv :: q' ++ Int.unsigned head :: nil)
                  with ((tail :: tlprv :: q') ++ Int.unsigned head :: nil)
                  in abs_q_unique0.
                destruct (unique_not_In _ _ _ (abs_q_unique0 eq_refl)).
                simpl in *.
                tauto.
              }
              repeat rewrite ZMap.gso; auto.
              split; auto.
              esplit; esplit; split; eauto; cbn.
              assert (Hq':
                List.remove zeq (Int.unsigned head) (q' ++ Int.unsigned head :: nil) = q')
                by (rewrite remove_last; simpl in *; tauto).
              assert (Hq_match_reshuffle:
                        match_nxt_prv (tlprv :: q' ++ Int.unsigned head :: nil)
                                      (Int.unsigned head)
                                      tlprv
                                      tail
                                      (npool yd))
                by exact Hq_match.
              clear Hq_match.
              rename Hq_match_reshuffle into Hq_match.
              rewrite Hq'.
              destruct (tail_last (Int.unsigned head) q') as [Hq'' | [q'' Hq'']].
              -- subst.
                 assert (tlprv <> Int.unsigned head) by (simpl in *; tauto).
                 cbn in Hq_match.
                 destruct Hq_match as (_ & tlprvdat & tlprvprv & Htlprv & _ & ? & ? & Hhead');
                   subst.
                 rewrite <- Hhead in Hhead'; inv Hhead'.
                 simpl in Hnxt; rewrite Htlprv in Hnxt; inv Hnxt.
                 rewrite ZMap.gso; auto. rewrite ZMap.gss.
                 eauto.
              -- rewrite Hq'' in Hq_match.
                 replace ((q'' ++ last q' (Int.unsigned head) :: nil) ++ Int.unsigned head :: nil)
                    with (q'' ++ last q' (Int.unsigned head) :: Int.unsigned head :: nil)
                    in Hq_match by  (rewrite <- app_assoc; reflexivity).
                 (* un-reduce the goal. *)
                 cut (match_nxt_prv (tlprv :: q' )
                                      nxt
                                      tlprv
                                      tail
                                      (ZMap.set (Int.unsigned head) (Node d MAX_NODES MAX_NODES)
                                                (ZMap.set nxt (Node d0 nxt0 MAX_NODES) (npool yd)))) ; [(intros blah; exact blah) | ].
                 (* Need to change the type to say
                      nxt = (last :: q') (Int.unsigned head) *)
                 replace (last (tlprv :: q') (Int.unsigned head))
                   with (last q' (Int.unsigned head))
                   in Hlast_q'
                   by (rewrite Hq'';
                       change (tlprv :: q'' ++ last q' (Int.unsigned head) :: nil)
                         with ((tlprv :: q'') ++ last q' (Int.unsigned head) :: nil);
                       repeat rewrite app_last by congruence;
                       reflexivity).
                 rewrite <- Hlast_q' in *.
                 clear Hlast_q'.
                 assert (HNIn_nxt:  ~ In nxt (tlprv :: q'')).
                 {
                   rewrite Hq'' in abs_q_unique0.
                   rewrite <- app_assoc in abs_q_unique0.
                   change (tail :: tlprv :: q'' ++ (nxt :: nil) ++ Int.unsigned head :: nil)
                     with ((tail :: tlprv :: q'') ++ nxt ::  Int.unsigned head :: nil)
                     in abs_q_unique0.
                   destruct (unique_not_In _ _ _ (abs_q_unique0 eq_refl)).
                   simpl in *.
                   tauto.
                 }
                 apply match_nxt_prv_not_in; auto.
                 rewrite Hq'' in *.
                 change (tlprv :: q'' ++ nxt :: nil) with ((tlprv :: q'') ++ nxt :: nil).
                 apply match_nxt_prv_remove with (xp := prv0) (y := Int.unsigned head).
                 congruence.
                 exact HNIn_nxt.
                 assumption.
      }
    Qed.

  End LowHighSpecSim.

  (** ** Linking *)
  Section Linking.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce :
      build_composite_env (node_t_comp :: queue_t_comp :: nil) = OK ce.

    Definition abs_queue_L : clayer abs_queue_layerdata :=
      enqueue ↦ abs_enqueue_high_sem
      ⊕ dequeue ↦ abs_dequeue_high_sem.

    Hint Resolve abs_enqueue_refine
                 abs_dequeue_refine : linking.

    (** We only need to use the [link_solve_refine] tactic since there is no
      intermediate spec. *)
    Theorem abs_queue_link :
      queue_L ⊢ (inv ∘ abs_queue_R ∘ inv, ∅) : abs_queue_L.
    Proof. unfold queue_L. link_solve_refine. Qed.

    Lemma abs_queue_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) abs_queue_L.
    Proof. unfold abs_queue_L. typeclasses eauto. Qed.

    Hint Resolve queue_boot_link abs_queue_link : linking.

    Theorem queue_boot_link :
      boot_L ⊢ (intro_R ∘ inv ∘ queue_R ∘ inv ∘ abs_queue_R ∘ inv, intro_M ⊕ queue_M) : abs_queue_L.
    Proof.
      apply (vdash_module_le _ _ _ _ _ ((intro_M ⊕ queue_M) ⊕ ∅));
      [constructor | reflexivity |].
      apply (vdash_rel_equiv _ _ ((intro_R ∘ inv ∘ queue_R ∘ inv) ∘
                                  (inv ∘ abs_queue_R ∘ inv))).
      rewrite cat_compose_assoc. monotonicity. reflexivity.
      rewrite cat_compose_assoc. monotonicity. reflexivity.
      rewrite <- cat_compose_assoc. monotonicity. apply simrel_compose_inv_inv.
      reflexivity.
      eapply vcomp_rule; eauto with linking.
    Qed.

  End Linking.

End AbsQueue.
