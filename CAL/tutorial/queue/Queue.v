(**
 * Queue.v
 *
 * Low level queue representation.
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

Require Import TutoLib.
Require Import QueueData.
Require Import Node.
Require Import QueueIntro.

(** In this file we implement the [enqueue] and [dequeue] primitives on the
  low-level linked-list representation of the queue. *)

Open Scope Z_scope.

Definition enqueue : ident := 31%positive.
Definition dequeue : ident := 32%positive.

Section Queue.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.

  (** ** Abstract Data *)
  Section AbsData.

    Definition intro_L := node_L ⊕ queue_intro_L.

    Definition intro_M := node_M ⊕ queue_intro_M.

    Lemma intro_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) intro_L.
    Proof. unfold intro_L, node_L, queue_intro_L. typeclasses eauto. Qed.

    (** We now require that once initialized, all nodes in range are valid,
      and everything else is undefined. *)
    Record queue_inv (d: abs_data) : Prop := {
      npool_valid: forall node,
        init_flag d = true ->
        0 <= node < MAX_NODES ->
        node_valid (ZMap.get node (npool d));
      npool_range: forall node,
        ~(0 <= node < MAX_NODES) ->
        ZMap.get node (npool d) = NodeUndef;
      preinit_q: init_flag d = false -> queue d = QueueUndef;
      q_valid: init_flag d = true -> queue_valid (queue d);
    }.

    Instance queue_data_ops : AbstractDataOps abs_data :=
      {|
        init_data := abs_data_init;
        data_inv := queue_inv;
        data_inject := fun _ _ _ => True
      |}.

    Instance queue_data_data : AbstractData abs_data.
    Proof.
      constructor; constructor; cbn; intros; try congruence.
      rewrite ZMap.gi; reflexivity.
    Qed.

    Definition queue_layerdata : layerdata :=
      {|
        ldata_type := abs_data;
        ldata_ops  := queue_data_ops;
        ldata_prf  := queue_data_data
      |}.

  End AbsData.

  (** ** High Level Specifications *)
  Section HighSpec.

    (** The two possibilities for [enqueue] are:
        - Queue is empty: set head and tail equal to the new node
        - Queue is not empty: set tail to the new node and make the new node
          and the old tail point to each other *)
    Definition enqueue_high_spec (node: Z) (abs: queue_layerdata)
        : option queue_layerdata :=
      if init_flag abs
        then if decide (0 <= node < MAX_NODES)
          then match queue abs, ZMap.get node (npool abs) with
            | Queue hd tl, Node dat _ _ =>
                if decide (tl = MAX_NODES)
                  then let n := Node dat MAX_NODES MAX_NODES in
                    Some abs {queue: Queue node node}
                             {npool: ZMap.set node n (npool abs)}
                  else match ZMap.get tl (npool abs) with
                    | Node tldat _ tlprv =>
                        let n := Node dat MAX_NODES tl in
                        let tl' := Node tldat node tlprv in
                        Some abs {queue: Queue hd node}
                                 {npool: ZMap.set node n (ZMap.set tl tl' (npool abs))}
                    | _ => None
                  end
            | _, _ => None
          end
          else None
        else None.

    Definition enqueue_high_sem : cprimitive queue_layerdata :=
      cgensem _ enqueue_high_spec.

    Global Instance enqueue_pres_inv :
      GenSemPreservesInvariant queue_layerdata enqueue_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold enqueue_high_spec in H2.
      destruct Hinv.
      repeat destr_in H2; inv H2.
      - (** tl = MAX_NODES *)
        constructor; cbn; intros; auto; try congruence.
        + (** npool_valid *)
          destr_eq node (Int.unsigned i); [subst |].
          * rewrite ZMap.gss; constructor; omega.
          * rewrite ZMap.gso; auto.
        + (** npool_range *)
          destr_eq node (Int.unsigned i); [subst |].
          * omega.
          * rewrite ZMap.gso; auto.
        + (** q_valid *)
          constructor; omega.
      - (** tl <> MAX_NODES *)
        constructor; cbn; intros; auto; try congruence.
        + (** npool_valid *)
          destr_eq node (Int.unsigned i); [subst |].
          * rewrite ZMap.gss; constructor; try omega.
            specialize (q_valid0 eq_refl).
            inv q_valid0; auto.
          * rewrite ZMap.gso; auto.
            destr_eq node tail; [subst |].
            -- rewrite ZMap.gss.
               apply npool_valid0 in H2; auto; inv H2.
               constructor; (omega || congruence).
            -- rewrite ZMap.gso; auto.
        + (** npool_range *)
          destr_eq node (Int.unsigned i); [subst |].
          * omega.
          * rewrite ZMap.gso; auto.
            destr_eq node tail; [subst |].
            -- apply npool_range0 in H1. congruence.
            -- rewrite ZMap.gso; auto.
        + (** q_valid *)
          constructor; try omega.
          specialize (q_valid0 eq_refl).
          inv q_valid0; auto.
    Qed.

    (** [dequeue] also has two cases:
        - Queue has 1 element: set head and tail to [MAX_NODES]
        - Queue has more elements: set head to the old head's next node node
          and set the new head's prev to [MAX_NODES]

        One subtlety is that the order we update hd and hdnxt in the second
        case is important. We want to ensure that the node that is returned has
        its next and prev fields set to [MAX_NODES] so only nodes actually in
        the queue point to other nodes. Since we do not yet require that there
        are no cycles at this layer, it is possible for hd.next = hd in which
        case updating hd, then hd.next would undo the first step. Of course it
        is possible to design the specification to allow this behaviour, but it
        would require a change in the C code.

        TUTORIAL (optional):
        If you feel adventurous, uncomment the alternative version below and
        see how far through the proofs you get before you are stuck. You will
        find that at some point in the code proof you have to prove something
        like:
        [ZMap.set hd (Node data MAX_NODES MAX_NODES) =
         ZMap.set hd (Node data hd MAX_NODES)] *)
    Definition dequeue_high_spec (abs: queue_layerdata)
        : option (queue_layerdata * Z) :=
      if init_flag abs
        then match queue abs with
          | Queue hd tl =>
              if decide (hd <> MAX_NODES)
                then match ZMap.get hd (npool abs) with
                  | Node hddat hdnxt _ =>
                      let n := Node hddat MAX_NODES MAX_NODES in
                      let pool' := ZMap.set hd n (npool abs) in
                      if decide (hdnxt = MAX_NODES)
                        then Some (abs {queue: Queue MAX_NODES MAX_NODES}
                                       {npool: pool'},
                                   hd)
                        else match ZMap.get hdnxt (npool abs) with
                          | Node nxtdat nxtnxt _ =>
                              Some (abs {queue: Queue hdnxt tl}
                                        (** Swap these npools to see why the
                                           order matters *)
                                        (** {npool: ZMap.set hdnxt (Node nxtdat nxtnxt MAX_NODES ) pool'}, *)
                                        {npool: ZMap.set hd n
                                                  (ZMap.set hdnxt
                                                            (Node nxtdat nxtnxt MAX_NODES)
                                                            (npool abs))},
                                    hd)
                          | _ => None
                        end
                  | _ => None
                end
                else None
          | _ => None
        end
        else None.

    Definition dequeue_high_sem : cprimitive queue_layerdata :=
      cgensem _ dequeue_high_spec.

    Global Instance dequeue_pres_inv :
      GenSemPreservesInvariant queue_layerdata dequeue_high_spec.
    Proof.
      Opaque Z.mul.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold dequeue_high_spec in H2.
      destruct Hinv.
      pose proof MAX_NODES_range as Hmn_range.
      repeat destr_in H2; inv H2.
      - constructor; cbn; intros; auto; try congruence.
        + (** npool_valid *)
          destr_eq node (Int.unsigned z); [subst |].
          * rewrite ZMap.gss; constructor; omega.
          * rewrite ZMap.gso; auto.
        + (** npool_range *)
          destr_eq node (Int.unsigned z); [subst |].
          * apply npool_range0 in H1. congruence.
          * rewrite ZMap.gso; auto.
        + (** q_valid *)
          constructor; omega.
      - constructor; cbn; intros; auto; try congruence.
        + (** npool_valid *)
          destr_eq node (Int.unsigned z); [subst |].
          * rewrite ZMap.gss.
            constructor; omega.
          * rewrite ZMap.gso; auto.
            destr_eq node next; [subst |].
            -- rewrite ZMap.gss.
               apply npool_valid0 in H2; auto; inv H2.
               constructor; (omega || congruence).
            -- rewrite ZMap.gso; auto.
        + (** npool_range *)
          destr_eq node (Int.unsigned z); [subst |].
          * apply npool_range0 in H1. congruence.
          * rewrite ZMap.gso; auto.
            destr_eq node next; [subst |].
            -- apply npool_range0 in H1. congruence.
            -- rewrite ZMap.gso; auto.
        + (** q_valid *)
          specialize (q_valid0 eq_refl).
          inv q_valid0.
          assert (Hz: 0 <= Int.unsigned z < MAX_NODES).
          { cut (0 <= Int.unsigned z <= MAX_NODES /\ Int.unsigned z <> MAX_NODES);
            [omega | split]; eauto. }
          apply npool_valid0 in Hz; auto; inv Hz.
          constructor; congruence.
      Qed.

  End HighSpec.

  (** ** Module Implementation *)
  Section Code.

    Definition e_node : ident := 35%positive.
    Definition e_tail : ident := 36%positive.

    Definition f_enqueue' :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := (e_node, tuint) :: nil;
        fn_vars := nil;
        fn_temps := (e_tail, tuint) :: nil;
        fn_body :=
          Ssequence
           (Scall (Some e_tail)
             (Evar get_tail (Tfunction Ctypes.Tnil tuint cc_default)) nil)
           (Sifthenelse (Ebinop Oeq (Etempvar e_tail tuint)
                          (Econst_int (Int.repr MAX_NODES) tint) tint)
             (Ssequence
               (Scall None
                 (Evar set_next (Tfunction (Ctypes.Tcons tuint (Ctypes.Tcons tuint Ctypes.Tnil)) tvoid
                                   cc_default))
                 ((Etempvar e_node tuint) :: (Econst_int (Int.repr MAX_NODES) tint) :: nil))
               (Ssequence
                 (Scall None
                   (Evar set_prev (Tfunction (Ctypes.Tcons tuint (Ctypes.Tcons tuint Ctypes.Tnil)) tvoid
                                     cc_default))
                   ((Etempvar e_node tuint) :: (Econst_int (Int.repr MAX_NODES) tint) ::
                    nil))
                 (Ssequence
                   (Scall None
                     (Evar set_head (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) tvoid cc_default))
                     ((Etempvar e_node tuint) :: nil))
                   (Scall None
                     (Evar set_tail (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) tvoid cc_default))
                     ((Etempvar e_node tuint) :: nil)))))
             (Ssequence
               (Scall None
                 (Evar set_next (Tfunction (Ctypes.Tcons tuint (Ctypes.Tcons tuint Ctypes.Tnil)) tvoid
                                   cc_default))
                 ((Etempvar e_tail tuint) :: (Etempvar e_node tuint) :: nil))
               (Ssequence
                 (Scall None
                   (Evar set_prev (Tfunction (Ctypes.Tcons tuint (Ctypes.Tcons tuint Ctypes.Tnil)) tvoid
                                     cc_default))
                   ((Etempvar e_node tuint) :: (Etempvar e_tail tuint) :: nil))
                 (Ssequence
                   (Scall None
                     (Evar set_next (Tfunction (Ctypes.Tcons tuint (Ctypes.Tcons tuint Ctypes.Tnil)) tvoid
                                       cc_default))
                     ((Etempvar e_node tuint) :: (Econst_int (Int.repr MAX_NODES) tint) ::
                      nil))
                   (Scall None
                     (Evar set_tail (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) tvoid cc_default))
                     ((Etempvar e_node tuint) :: nil))))))
      |}.

    Program Definition f_enqueue : function :=
      inline f_enqueue' _.

    Definition d_head : ident := 37%positive.
    Definition d_next : ident := 38%positive.
    Definition d_node : ident := 39%positive.

    Definition f_dequeue' :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := (d_head, tuint) :: (d_next, tuint) :: (d_node, tuint) :: nil;
        fn_body :=
          Ssequence
           (Sset d_node (Econst_int (Int.repr MAX_NODES) tint))
           (Ssequence
             (Scall (Some d_head)
               (Evar get_head (Tfunction Ctypes.Tnil tuint cc_default)) nil)
             (Ssequence
               (Sifthenelse (Ebinop One (Etempvar d_head tuint)
                              (Econst_int (Int.repr MAX_NODES) tint) tint)
                 (Ssequence
                   (Sset d_node (Etempvar d_head tuint))
                   (Ssequence
                     (Scall (Some d_next)
                       (Evar get_next (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) tuint
                                         cc_default))
                       ((Etempvar d_head tuint) :: nil))
                     (Ssequence
                       (Sifthenelse (Ebinop Oeq (Etempvar d_next tuint)
                                      (Econst_int (Int.repr MAX_NODES) tint) tint)
                         (Ssequence
                           (Scall None
                             (Evar set_head (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) tvoid
                                               cc_default))
                             ((Econst_int (Int.repr MAX_NODES) tint) :: nil))
                           (Scall None
                             (Evar set_tail (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) tvoid
                                               cc_default))
                             ((Econst_int (Int.repr MAX_NODES) tint) :: nil)))
                         (Ssequence
                           (Scall None
                             (Evar set_prev (Tfunction
                                               (Ctypes.Tcons tuint (Ctypes.Tcons tuint Ctypes.Tnil)) tvoid
                                               cc_default))
                             ((Etempvar d_next tuint) ::
                              (Econst_int (Int.repr MAX_NODES) tint) :: nil))
                           (Scall None
                             (Evar set_head (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) tvoid
                                               cc_default))
                             ((Etempvar d_next tuint) :: nil))))
                       (Ssequence
                         (Scall None
                           (Evar set_next (Tfunction (Ctypes.Tcons tuint (Ctypes.Tcons tuint Ctypes.Tnil))
                                             tvoid cc_default))
                           ((Etempvar d_node tuint) ::
                            (Econst_int (Int.repr MAX_NODES) tint) :: nil))
                         (Scall None
                           (Evar set_prev (Tfunction (Ctypes.Tcons tuint (Ctypes.Tcons tuint Ctypes.Tnil))
                                             tvoid cc_default))
                           ((Etempvar d_node tuint) ::
                            (Econst_int (Int.repr MAX_NODES) tint) :: nil))))))
                 Sskip)
               (Sreturn (Some (Etempvar d_node tuint)))))
      |}.

    Program Definition f_dequeue : function :=
      inline f_dequeue' _.

  End Code.

  (** ** Low Level Specifications *)
  Section LowSpec.

    Definition enqueue_csig :=
      mkcsig (type_of_list_type (tuint :: nil)) tvoid.

    Inductive enqueue_step :
      csignature -> list val * mwd intro_layerdata -> val * mwd intro_layerdata -> Prop :=
    | enqueue_step_intro m d nd d':
        enqueue_high_spec (Int.unsigned nd) d = Some d' ->
        enqueue_step enqueue_csig
                     (Vint nd :: nil, (m, d))
                     (Vundef, (m, d')).

    Definition dequeue_csig :=
      mkcsig (type_of_list_type nil) tuint.

    Inductive dequeue_step :
      csignature -> list val * mwd intro_layerdata -> val * mwd intro_layerdata -> Prop :=
    | dequeue_step_intro m d nd d':
        dequeue_high_spec d = Some (d', Int.unsigned nd) ->
        dequeue_step dequeue_csig
                     (nil, (m, d))
                     (Vint nd, (m, d')).

    Program Definition enqueue_cprim : cprimitive intro_layerdata :=
      mkcprimitive _ enqueue_step enqueue_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition dequeue_cprim : cprimitive intro_layerdata :=
      mkcprimitive _ dequeue_step dequeue_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Global Instance enqueue_cprim_pres_inv : CPrimitivePreservesInvariant _ enqueue_cprim.
    Proof.
      constructor; intros.
      - inv H0. unfold enqueue_high_spec in H4.
        inv H1. inv cprimitive_inv_init_state_data_inv.
        repeat destr_in H4; inv H4.
        { (** tail = MAX_NODES *)
          constructor; auto.
          constructor; cbn; try congruence; intros.
          - destr_eq node (Int.unsigned nd); subst.
            + rewrite ZMap.gss. right. constructor; omega.
            + rewrite ZMap.gso; auto.
          - constructor; omega.
        }
        { (** tail <> MAX_NODES *)
          constructor; auto.
          specialize (q_valid0 eq_refl); inv q_valid0.
          constructor; cbn; try congruence; intros.
          - destr_eq node (Int.unsigned nd); subst.
            + rewrite ZMap.gss.
              right. constructor; omega.
            + rewrite ZMap.gso; auto.
              destr_eq node tail; subst.
              * rewrite ZMap.gss.
                apply npool_valid0 in H0.
                destruct H0; try congruence.
                inv H0. rewrite Heqn0 in H1; inv H1.
                right. constructor; try omega.
              * rewrite ZMap.gso; auto.
          - constructor; omega.
        }
      - inv H0; reflexivity.
    Qed.

    Global Instance dequeue_cprim_pres_inv : CPrimitivePreservesInvariant _ dequeue_cprim.
    Proof.
      Opaque Z.mul.
      pose proof MAX_NODES_range as Hmn_range.
      constructor; intros.
      - inv H0. unfold dequeue_high_spec in H4.
        inv H1. inv cprimitive_inv_init_state_data_inv.
        repeat destr_in H4; inv H4.
        { (** next = MAX_NODES *)
          constructor; auto.
          constructor; cbn; try congruence; intros.
          - destr_eq node (Int.unsigned nd); subst.
            + rewrite ZMap.gss. right. constructor; omega.
            + rewrite ZMap.gso; auto.
          - constructor; omega.
        }
        { (** next <> MAX_NODES *)
          constructor; auto.
          specialize (q_valid0 eq_refl); inv q_valid0.
          constructor; cbn; try congruence; intros.
          - destr_eq node (Int.unsigned nd); subst.
            + rewrite ZMap.gss.
              right. constructor; omega.
            + rewrite ZMap.gso; auto.
              destr_eq node next; subst.
              * rewrite ZMap.gss.
                apply npool_valid0 in H0.
                destruct H0; try congruence.
                inv H0. rewrite Heqn1 in H1; inv H1.
                right. constructor; try omega.
              * rewrite ZMap.gso; auto.
          - assert (0 <= Int.unsigned nd < MAX_NODES) by omega.
            apply npool_valid0 in H1.
            destruct H1; try congruence.
            inv H1. rewrite Heqn0 in H4; inv H4.
            constructor; omega.
        }
      - inv H0; reflexivity.
      Qed.

  End LowSpec.

  (** ** Code Proofs *)
  Section CodeLowSpecSim.

    Context `{ce: ClightCompositeEnv}.

    (** We can automatically solve the additional goal introduced by
      [code_proof_tac] by using a hint. *)
    Hint Resolve intro_pres_inv : linking.

    Lemma enqueue_code :
      intro_L ⊢ (inv, enqueue ↦ f_enqueue) : (enqueue ↦ enqueue_cprim).
    Proof.
      Opaque Z.mul.
      code_proof_tac.
      find_prim get_tail.
      find_prim set_next.
      find_prim set_prev.
      find_prim set_head.
      find_prim set_tail.
      inv Hmatch; inv CStep.
      destruct cprimitive_inv_init_state_data_inv.
      unfold enqueue_high_spec in H2.
      do 4 (destr_in H2; try discriminate).
      rename Heqb into Hinit;
      rename Heqq into Hqueue;
      rename Heqn into Hnode;
      rename Heqs into Hnode_range.
      cprim_step.
      pose proof MAX_NODES_range as Hmn_range.
      repeat (destr_in H2; inv H2).
      { (** tail = MAX_NODES *)
        repeat step_tac.
        - unfold get_tail_high_spec.
          rewrite Hinit, Hqueue.
          rewrite Int.unsigned_repr; [reflexivity | cbn; omega].
        - reflexivity.
        - repeat step_tac.
          + unfold set_next_high_spec.
            rewrite Hnode_range, Hnode.
            rewrite Int.unsigned_repr; try (cbn; omega). destr; try omega.
            reflexivity.
          + unfold set_prev_high_spec; cbn.
            rewrite Hnode_range.
            rewrite Int.unsigned_repr; try (cbn; omega). destr; try omega.
            rewrite ZMap.gss.
            reflexivity.
          + unfold set_head_high_spec; cbn.
            rewrite Hinit, Hqueue.
            destr; try omega.
            reflexivity.
          + unfold set_tail_high_spec; cbn.
            rewrite Hinit.
            destr; try omega.
            unfold update_queue, update_npool; cbn.
            rewrite ZMap.set2.
            reflexivity.
      }
      { (** tail <> MAX_NODES *)
        (** Need invariant to prove *)
        assert (Htail_range: 0 <= tail <= MAX_NODES).
        { specialize (q_valid0 eq_refl); inv q_valid0; auto. }
        destr_in H1; inv H1.
        rename Heqn0 into Htail.
        repeat step_tac.
        - unfold get_tail_high_spec.
          rewrite Hinit, Hqueue.
          rewrite Int.unsigned_repr; [reflexivity | cbn; omega].
        - rewrite Int.eq_false; [reflexivity |].
          red; intros.
          apply (f_equal Int.unsigned) in H0.
          repeat (rewrite Int.unsigned_repr in H0; try (cbn; omega)).
        - destr_eq tail (Int.unsigned nd); [subst |].
          + repeat step_tac.
            * unfold set_next_high_spec.
              rewrite Int.unsigned_repr; try (cbn; omega).
              rewrite Htail.
              repeat destr; try omega.
              reflexivity.
            * unfold set_prev_high_spec; cbn.
              rewrite Hnode_range.
              rewrite Int.unsigned_repr; try (cbn; omega). destr; try omega.
              subst; rewrite ZMap.gss. reflexivity.
            * unfold set_next_high_spec.
              rewrite Int.unsigned_repr; try (cbn; omega).
              rewrite Hnode_range.
              destr; try omega.
              rewrite ZMap.gss. reflexivity.
            * unfold set_tail_high_spec; cbn.
              rewrite Hinit, Hqueue.
              destr; try omega.
              unfold update_npool, update_queue; cbn.
              repeat rewrite ZMap.set2.
              congruence.
          + repeat step_tac.
            * unfold set_next_high_spec.
              rewrite Int.unsigned_repr; try (cbn; omega).
              rewrite Htail.
              repeat destr; try omega.
              reflexivity.
            * unfold set_prev_high_spec; cbn.
              rewrite Hnode_range.
              rewrite Int.unsigned_repr; try (cbn; omega). destr; try omega.
              subst; rewrite ZMap.gso; auto. rewrite Hnode.
              reflexivity.
            * unfold set_next_high_spec.
              rewrite Int.unsigned_repr; try (cbn; omega).
              rewrite Hnode_range.
              destr; try omega.
              rewrite ZMap.gss. reflexivity.
            * unfold set_tail_high_spec; cbn.
              rewrite Hinit, Hqueue.
              destr; try omega.
              unfold update_npool, update_queue; cbn.
              repeat rewrite ZMap.set2.
              congruence.
      }
    Qed.

    Lemma dequeue_code :
      intro_L ⊢ (inv, dequeue ↦ f_dequeue) : (dequeue ↦ dequeue_cprim).
    Proof.
      Opaque Z.mul.
      code_proof_tac.
      find_prim get_head.
      find_prim get_next.
      find_prim set_next.
      find_prim set_prev.
      find_prim set_head.
      find_prim set_tail.
      inv Hmatch; inv CStep.
      destruct cprimitive_inv_init_state_data_inv.
      unfold dequeue_high_spec in H2.
      do 4 (destr_in H2; try discriminate).
      rename Heqb into Hinit;
      rename Heqq into Hqueue;
      rename Heqn0 into Hnode.
      cprim_step.
      pose proof MAX_NODES_range as Hmn_range.
      (** Need invariant to prove *)
      assert (Hhead_range: 0 <= head < MAX_NODES).
      { cut (0 <= head <= MAX_NODES /\ head <> MAX_NODES);
        [omega | split]; auto.
        specialize (q_valid0 eq_refl); inv q_valid0; auto.
      }
      repeat (destr_in H2; inv H2).
      { (** next = MAX_NODES *)
        repeat step_tac.
        - unfold get_head_high_spec.
          rewrite Hinit, Hqueue.
          reflexivity.
        - rewrite Int.eq_false; [reflexivity |].
          red; intros Heq.
          pose proof n as Hneq; rewrite Heq in Hneq.
          rewrite Int.unsigned_repr in Hneq; [contradiction | cbn; omega].
        - repeat step_tac.
          + unfold get_next_high_spec.
            rewrite Hnode.
            destruct (decide (_ <= _ < _)); try omega.
            rewrite Int.unsigned_repr; [reflexivity | cbn; omega].
          + reflexivity.
          + repeat step_tac.
            * unfold set_head_high_spec.
              rewrite Hinit, Hqueue.
              rewrite Int.unsigned_repr; try (cbn; omega).
              destr; try omega.
              reflexivity.
            * unfold set_tail_high_spec; cbn.
              rewrite Hinit.
              rewrite Int.unsigned_repr; try (cbn; omega).
              destr; try omega.
              reflexivity.
            * unfold set_next_high_spec; cbn.
              rewrite Hnode.
              rewrite Int.unsigned_repr; try (cbn; omega).
              destr; try omega. destr; try omega.
              reflexivity.
            * unfold set_prev_high_spec; cbn.
              rewrite ZMap.gss.
              rewrite Int.unsigned_repr; try (cbn; omega).
              destr; try omega. destr; try omega.
              unfold update_queue, update_npool; cbn.
              rewrite ZMap.set2.
              reflexivity.
      }
      { (** next <> MAX_NODES *)
        (** Need invariant to prove *)
        assert (Hnext_range: 0 <= next <= MAX_NODES).
        { apply npool_valid0 in Hhead_range. rewrite Hnode in Hhead_range.
          destruct Hhead_range as [Hvalid | Hvalid]; inv Hvalid; auto.
        }
        destr_in H1; inv H1.
        rename Heqn1 into Hnext.
        repeat step_tac.
        - unfold get_head_high_spec.
          rewrite Hinit, Hqueue.
          rewrite Int.unsigned_repr; [reflexivity | cbn; omega].
        - rewrite Int.eq_false; [reflexivity |].
          red; intros Heq.
          apply (f_equal Int.unsigned) in Heq.
          repeat (rewrite Int.unsigned_repr in Heq; try (cbn; omega)).
        - repeat step_tac.
          + unfold get_next_high_spec.
            rewrite Int.unsigned_repr; try (cbn; omega).
            rewrite Hnode.
            destruct (decide (_ <= _ < _)); try omega.
            rewrite Int.unsigned_repr; [reflexivity | cbn; omega].
          + rewrite Int.eq_false; [reflexivity |].
            red; intros Heq.
            apply (f_equal Int.unsigned) in Heq.
            repeat (rewrite Int.unsigned_repr in Heq; try (cbn; omega)).
          + destr_eq next (Int.unsigned nd); [subst |].
            * repeat step_tac.
              -- unfold set_prev_high_spec.
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 rewrite Hnext.
                 destr; try omega. destr; try omega.
                 reflexivity.
              -- unfold set_head_high_spec; cbn.
                 rewrite Hinit, Hqueue.
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 destr; try omega.
                 reflexivity.
              -- unfold set_next_high_spec; cbn.
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 destr; try omega. destr; try omega.
                 rewrite ZMap.gss. reflexivity.
              -- unfold set_prev_high_spec; cbn.
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 destr; try omega. destr; try omega.
                 rewrite ZMap.gss. reflexivity.
              -- unfold update_queue, update_npool; cbn.
                 repeat rewrite ZMap.set2.
                 rewrite Hnext in Hnode. inv Hnode.
                 rewrite Int.repr_unsigned.
                 step_tac.
            * repeat step_tac.
              -- unfold set_prev_high_spec.
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 rewrite Hnext.
                 destr; try omega. destr; try omega.
                 reflexivity.
              -- unfold set_head_high_spec; cbn.
                 rewrite Hinit, Hqueue.
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 destr; try omega.
                 reflexivity.
              -- unfold set_next_high_spec; cbn.
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 destr; try omega. destr; try omega.
                 rewrite ZMap.gso; auto. rewrite Hnode.
                 reflexivity.
              -- unfold set_prev_high_spec; cbn.
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 rewrite Int.unsigned_repr; try (cbn; omega).
                 destr; try omega. destr; try omega.
                 rewrite ZMap.gss. reflexivity.
              -- unfold update_queue, update_npool; cbn.
                 repeat rewrite ZMap.set2.
                 rewrite Int.repr_unsigned.
                 step_tac.
      }
    Qed.

  End CodeLowSpecSim.

  (** ** Layer Relation *)
  Section LowHighSpecRel.

    Inductive match_data : queue_layerdata -> mem -> Prop :=
    | match_data_intro: forall m abs,
        match_data abs m.

    Record relate_data (hadt: queue_layerdata) (ladt: intro_layerdata) := {
      init_rel: init_flag hadt = init_flag ladt;
      npool_rel: npool hadt = npool ladt;
      queue_rel: queue hadt = queue ladt
    }.

    Definition abrel_components_queue_intro :
      abrel_components queue_layerdata intro_layerdata :=
      {|
        abrel_relate := relate_data;
        abrel_match  := match_data;
        abrel_new_glbl := nil
      |}.

    Global Instance rel_ops :
      AbstractionRelation _ _ abrel_components_queue_intro.
    Proof. repeat constructor. Qed.

    Definition abrel_queue_intro : abrel queue_layerdata intro_layerdata :=
      {|
        abrel_ops := abrel_components_queue_intro;
        abrel_prf := rel_ops
      |}.

    Definition queue_R : simrel _ _ := abrel_simrel _ _ abrel_queue_intro.

  End LowHighSpecRel.

  (** ** Refinement Proofs *)
  Section LowHighSpecSim.

    Context `{ce: ClightCompositeEnv}.

    Lemma enqueue_refine :
      (enqueue ↦ enqueue_cprim) ⊢ (queue_R, ∅) : (enqueue ↦ enqueue_high_sem).
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold enqueue_high_spec in H1.
      repeat destr_in H1; inv H1;
      rename Heqn into Hnode.
      { (** tail = MAX_NODES *)
        do 3 eexists; split.
        - econstructor. unfold enqueue_high_spec.
          rewrite <- init_rel0, <- queue_rel0, <- npool_rel0, Hnode.
          destr; try omega. destr; try omega.
          reflexivity.
        - repeat (constructor; auto).
          cbn; congruence.
      }
      { (** tail <> MAX_NODES *)
        rename Heqn0 into Htail.
        do 3 eexists; split.
        - econstructor. unfold enqueue_high_spec.
          rewrite <- init_rel0, <- queue_rel0, <- npool_rel0, Hnode, Htail.
          destr; try omega. destr; try omega.
          reflexivity.
        - repeat (constructor; auto).
          cbn; congruence.
      }
    Qed.

    Lemma dequeue_refine :
      (dequeue ↦ dequeue_cprim) ⊢ (queue_R, ∅) : (dequeue ↦ dequeue_high_sem).
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold dequeue_high_spec in H1.
      repeat destr_in H1; inv H1;
      rename Heqs into Hz_neq;
      rename Heqn0 into Hnode.
      { (** tail = MAX_NODES *)
        do 3 eexists; split.
        - econstructor. unfold dequeue_high_spec.
          rewrite <- init_rel0, <- queue_rel0, <- npool_rel0, Hz_neq, Hnode.
          destr; try omega.
          reflexivity.
        - repeat (constructor; auto).
          cbn; congruence.
      }
      { (** tail <> MAX_NODES *)
        rename Heqn1 into Hnext.
        rename  Heqs0 into Hnext_neq.
        do 3 eexists; split.
        - econstructor. unfold dequeue_high_spec.
          rewrite <- init_rel0, <- queue_rel0, <- npool_rel0, Hz_neq, Hnode,
                  Hnext, Hnext_neq.
          reflexivity.
        - repeat (constructor; auto).
          cbn; congruence.
      }
    Qed.

  End LowHighSpecSim.

  (** ** Linking *)
  Section Linking.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce :
      build_composite_env (node_t_comp :: queue_t_comp :: nil) = OK ce.

    Definition queue_L : clayer queue_layerdata :=
      enqueue ↦ enqueue_high_sem
      ⊕ dequeue ↦ dequeue_high_sem.

    Definition queue_Σ : clayer intro_layerdata :=
      enqueue ↦ enqueue_cprim
      ⊕ dequeue ↦ dequeue_cprim.

    Definition queue_M : cmodule :=
      enqueue ↦ f_enqueue
      ⊕ dequeue ↦ f_dequeue.

    Hint Resolve enqueue_code enqueue_refine
                 dequeue_code dequeue_refine : linking.

    (** [link_tac] still works even though [queue_L] is built on top of a
      composition of layers. *)
    Theorem queue_link :
      intro_L ⊢ (inv ∘ queue_R ∘ inv, queue_M) : queue_L.
    Proof. link_tac queue_Σ. Qed.

    Lemma queue_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) queue_L.
    Proof. unfold queue_L. typeclasses eauto. Qed.

    Hint Resolve node_link queue_intro_link queue_link : linking.

    Theorem queue_boot_link :
      boot_L ⊢ (intro_R ∘ inv ∘ queue_R ∘ inv, intro_M ⊕ queue_M) : queue_L.
    Proof.
      apply (vdash_rel_equiv _ _ (intro_R ∘ (inv ∘ queue_R ∘ inv))).
      rewrite cat_compose_assoc; rewrite cat_compose_assoc; reflexivity.
      eapply vcomp_rule; eauto with linking.
      unfold intro_M, intro_L.
      apply hcomp_rule; auto with linking.
    Qed.

  End Linking.

End Queue.
