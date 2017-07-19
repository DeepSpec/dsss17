(** * VminusStatics: SSA, Preservation and Progress *)

Require Import Arith.
Require Import List.
Import ListNotations.

Require Import Vminus.Classes.
Require Import Vminus.Util.
Require Import Vminus.Env.
Require Import Vminus.Vminus.
Require Import Vminus.CFG.

Require Import Vminus.Dom.
Require Import Vminus.VminusOpSem.

Module MakeStatics (Cfg: CFG).
Import Cfg.

(** * SSA Invariants: Typing CFGs*)

(** The only ways in which a Vminus program can "go wrong" are by
    accessing a local variable that hasn't been defined or jumping to a label
    that isn't in the CFG.  Therefore, its "typing" constraints ensure that each
    instruction only mentions local identifiers that are in scope according to
    the domination structure of the control-flow graph and that all mentioned
    labels are associated with blocks defined in the CFG.

    These properties are partly enforced by the "syntactic" well-formedness
    constraints imposed by the CFG interface (see CFG.v), which ensure that
    labels and instruction identifiers are unique.

    To enforce the scoping property, we formalize the notion of "dominance" in
    the control flow graph.  The module interface [Dom.Spec] defines dominance
    for arbitrary graphs.  Here, we instantiate the general theory with a
    suitable graph instance for our CFGs.

*)

Module Typing.  
(**  ------------------------------------------------------------------------- *)  
(* ################################################################# *)
(** * GRAPH instance for dominance calculation *)

(** We need to define an graph instance that captures all the edges of our CFGs.
    
    - vertices in the graph are just program points

    - program points _within_ a single block have "fallthrough" edges determined
      by incrementing the program counter
    
    - a block [b1] terminated by a branch to [b2] induces an edge from [b1] to
  [b2] in the CFG.  *)

  
  (** Graph edge relation *)

  Inductive succ_pc (g:Cfg.t) : pc -> pc -> Prop :=
  | succ_pc_S : forall p,
      succ_pc g p (incr_pc p)
  | succ_pc_J : forall p l i,
      insn_at_pc g p i ->
      In l (insn_lbls i) ->
      succ_pc g p (block_entry l).

(**  ------------------------------------------------------------------------- *)  
(* ################################################################# *)
(** * GRAPH instance for dominance calculation *)

(** Graph of program points *)

  Module PcGraph <: GRAPH.
    Definition t := Cfg.t.
    Definition V := pc.
    Definition entry g := block_entry (entry_block g).
    Definition Succ := succ_pc.
    Definition Mem := wf_pc.
  End PcGraph.

(** Instantiate the dominance spec for this graph *)
  
  Module Export Dom := Dom.Spec PcGraph.

  
(**  ------------------------------------------------------------------------- *)  
(* ################################################################# *)
(** * Defining SSA scoping *)
  
(** We can now use the dominance properties of the CFG to define scoping
    for well-formed SSA programs. We first need some auxliary predicates: *)

(** The command at the given [pc] defines uid. *)

  Definition def_at_pc (g:Cfg.t) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c) /\ defs_uid (uid, c). 

  (** The [uid] has a definition that strictly dominates the pc [p]. *)
 
  Definition uid_sdom_pc (g:Cfg.t) (uid:uid) (p:pc) : Prop :=
    exists p', def_at_pc g p' uid /\ SDom g p' p.

(**  ------------------------------------------------------------------------- *)  
(* ----------------------------------------------------------------- *)
(** *** Uses are dominated by their definitions *)
  
  (** All uses of a [uid] must be strictly dominated by
      their definitions. However, we have to treat [phi] instructions
      specially, since the "uses" of identifiers on the right-hand side of 
      are conditioned on control flow.  

      The right-hand-side of a phi node can safely refer to the identifier defined
      by the phi node itself.  For example, consider this snippet of code:
 [[
      entry:
        br blk      

      blk: 
        %x = phi [%entry: 0] [%blk: %x]    
        br blk
 ]]

      For non-phi instructions, we simply require:
  *)

  Definition wf_use (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    ~is_phi i -> forall uid, In (val_uid uid) (insn_uses i) -> uid_sdom_pc g uid p.


(**  ------------------------------------------------------------------------- *)  
  (** *** Well-formed phi nodes *)

  (**  Consider [ %x = phi [lbl1:v1, ...,lbln:vn] ].  This is well formed
       when every predecessor block with terminator program point p' 
       has a label associated with value v.  Moreover, if v is a uid then
       the definition of the uid strictly dominates p' (i.e. the terminator
       of the predecessor).
  *)

  Definition wf_phi_args (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall pred, succ_pc g pred (entry_of_pc p) ->
      (exists v, In (lbl_of pred, v) (insn_phis i)) /\
      (forall uid, In (lbl_of pred, val_uid uid) (insn_phis i) -> 
          uid_sdom_pc g uid pred).

  (** Moreover, we require that fore every labeled value appearing in the
      right-hand side, there is a predecessor block with that label. *)
  
  Definition wf_phi_pred (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall l v, In (l, v) (insn_phis i) ->
      (exists pred, succ_pc g pred (entry_of_pc p) /\ lbl_of pred = l).

  Definition wf_phi (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    is_phi i -> wf_phi_args g i p
             /\ wf_phi_pred g i p
             /\ insn_phis i <> [].

  (**  ------------------------------------------------------------------------- *)  
  (** *** Well-formed terminators *)

  (** All jump targets must be legal block labels. *)  

  Definition wf_lbl (g:Cfg.t) (i:insn) : Prop :=
    forall l, In l (insn_lbls i) -> wf_pc g (block_entry l).


  (**  ------------------------------------------------------------------------- *)  
  (** *** Reachability *)

  (** We further require that all program points in a well-formed control-flow
   graph be reachable from the entry point. Without this proviso, an program point  
   that is not reachable is trivially dominated by _every_ program point.  This 
   requirement isn't strictly necessary, and might require us to remove dead blocks
   that become unreachable due to program transformations, but it also simplifies
   some pathological cases when reasoning about optimizations.
  *)
    
  Definition reachable (g:Cfg.t) (p:pc) : Prop :=
    exists path, Path g (block_entry (entry_block g)) p path.
  
  (**  ------------------------------------------------------------------------- *)  
  (** *** Well-formed instructions *)

  (** We package all of the requirements into a single predicate that says when
  an instruction is well formed at a particular program point -- it is simply
  the conjunction of all the above properties. *)
  
  Inductive wf_insn (g:Cfg.t) : insn -> pc -> Prop :=
  | wf_insn_intro : forall i p
      (Huse: wf_use g i p)
      (Hlbl: wf_lbl g i)
      (Hphi: wf_phi g i p)
      (Hreach: reachable g p),
      wf_insn g i p.

  (**  ------------------------------------------------------------------------- *)  
  (** *** Well-formed programs *)

  (** Finally, we spell out the requirements for a full control-flow graph to 
   meet the SSA invariants:

     - the CFG is syntactically well formed (no duplicated labels or ids);
     - every instruction is well-formed;
     - every program point that claims to be a terminator does indeed have
       a terminator instruction; and,
     - there are no predecessors of the entry block
   *)
  
  Inductive wf_prog (g:Cfg.t) : Prop :=
  | wf_prog_intro : forall
      (Hwfcfg : wf_cfg g)
      (Hwfis : forall p i, insn_at_pc g p i -> wf_insn g i p)
      (Hwftmn : forall p' i, tmn_pc g p' -> insn_at_pc g p' i -> is_tmn i)
      (Hwfentry : forall p, ~ succ_pc g p (block_entry (entry_block g))),
      wf_prog g.

End Typing.

(**  ------------------------------------------------------------------------- *)  
(* ################################################################# *)
(** * Type Safety *)

(** We prove type safety for Vminus by setting up the usual _preservation_
    and _progress_ theorems.  *)

Module OpsemCorrect.
  Module Import V := Make (Cfg).  
  Import Typing Opsem.

  

  (**  ------------------------------------------------------------------------- *)  
  (** *** Dominance relation *)

  (** First, we formulate a lemma that packages the dominance information into a
   more convenient form: if [pc1] steps to [pc2], then any [uid'] that strictly
   dominates [pc2] also dominates [pc1].  (So long as [uid'] doesn't reside
   at [pc1].) *)

  Lemma uid_sdom_step : forall g uid' uid pc1 pc2 c,
    wf_prog g ->
    uid' <> uid ->
    wf_pc g pc2 ->
    succ_pc g pc1 pc2 ->
    insn_at_pc g pc1 (uid, c) ->
    uid_sdom_pc g uid' pc2 ->
    uid_sdom_pc g uid' pc1.
  Proof.
    unfold uid_sdom_pc. 
    intros g uid' uid pc1 pc2 c Hwff Hneq Hpc Hsucc Hi [pc' [Hdef Hdom]]. 
    exists pc'. split. assumption. 
    split. contradict Hneq. subst pc'.
    inversion Hwff.
    destruct Hdef as [? [? ?]]; eapply eq_pc_uid; eauto. 
    inversion Hwff; eapply dom_step; eauto. 
  Qed.

  (**  ------------------------------------------------------------------------- *)  
  (** *** Well-formed states *)

  (** We have to extend well-formedness definitions to include all components of
  the Vminus state. *)

  (** The local environment is well-formed at a given program point [p] when it
  contains a binding for every [uid] whose definition strictly dominates [p].
  This is the property that ensures "scope safety" for the SSA program.
  *)
  
  Definition wf_loc (g:Cfg.t) (p:pc) (loc:loc) : Prop :=
  forall uid, uid_sdom_pc g uid p -> exists n, loc uid = Some n.

  (** We also need a predicate that indicates when the program counter is at 
  the entry. *)
  
  Definition at_entry (g:Cfg.t) (p:pc) : Prop :=
    entry_of_pc p = block_entry (entry_block g).

  (** A Vminus state is well formed when all of its components are.  We need to 
  maintain the invariant that the [ppc] component does indeed correspond to
  a predecessor block (unless the program is at the entry, which has no predecessors).
  Similarly, the [ploc] previous local environment must be well-formed with the 
  program counter as it exited the predecessor block. 
  *)
  
  Inductive wf_state (g:Cfg.t) : state -> Prop :=
  | wf_state_intro : forall st
      (Hwfpc: wf_pc g st.(st_pc))
      (Hwfloc: wf_loc g st.(st_pc) st.(st_loc))
      (Hwfppc: at_entry g st.(st_pc) \/ 
                 succ_pc g st.(st_ppc) (entry_of_pc st.(st_pc)))
      (Hwfploc: at_entry g st.(st_pc) \/ 
                  wf_loc g st.(st_ppc) st.(st_ploc)),
      wf_state g st.


  (**  ------------------------------------------------------------------------- *)  
  (** *** Initial state is well formed *)

  Lemma wf_init_state : 
    forall g m, wf_prog g ->
    wf_state g (init_state g m).
  Proof.
    intros g m Hprog. inversion Hprog. 
    apply wf_entry in Hwfcfg.
    econstructor. auto.
    red. simpl. intros. red in H. destruct H as [? [? [? ?]]].
    red in H1. contradict H0.
    cut (In x [block_entry (entry_block g)]). simpl. intuition.
    eapply H1. econstructor. auto.
    left. unfold init_state, at_entry, entry_of_pc. auto.
    left. unfold init_state, at_entry, entry_of_pc. auto.
  Qed.


  (**  ------------------------------------------------------------------------- *)  
  (** *** Progress helper lemmas. *)

  (** There are no phi nodes in the entry block. *)

  Lemma at_entry_not_phi : forall g st i,
    wf_prog g ->
    at_entry g st.(st_pc) ->
    insn_at_pc g st.(st_pc) i ->
    ~ is_phi i.
   Proof.
     intros g st i Hprog Hentry Hinsn. 
     destruct Hprog as [_ ? _ ?].

     specialize (Hwfis _ _ Hinsn). inversion Hwfis; subst.
     intro Hphi2. specialize (Hphi Hphi2). destruct Hphi as [H0 [H1 H2]].
     destruct (insn_phis i) eqn:His. contradiction H2; auto.
     assert (In p (insn_phis i)) as Hin. rewrite His. left; auto.
     destruct p. apply H1 in Hin. destruct Hin as [pred [Hpred Ht0]].
     specialize (Hwfentry pred). contradict Hwfentry. 
     rewrite <- Hentry; auto.
   Qed.

   (**  ------------------------------------------------------------------------- *)  
   (** *** Progress helper lemmas. *)

   (** In a well-formed program with well-formed locals, evaluating the values
       used by a non-phi instruction is never undefined. (This is basically 
       the consequence of identifiers being "in scope".
   *)

  Lemma eval_val__wf_loc : forall g pc loc i v,
    wf_prog g ->
    wf_loc g pc loc ->
    ~is_phi i ->
    insn_at_pc g pc i ->
    In v (insn_uses i) ->
    exists n, eval_val loc v = Some n.
  Proof.
    intros ? ? ? ? v Hwff Hwfloc Hnotphi Hi ?. 
    destruct v as [uid | n].
    simpl. inversion Hwff as [_ ? _]. apply Hwfis in Hi. 
    destruct Hi as [? ? Huse].
    destruct (is_phi_decidable i).
    - contradiction.
    specialize (Huse Hnotphi uid). 
    lapply Huse; auto.
    simpl; eauto.
  Qed.

  (**  ------------------------------------------------------------------------- *)  
  (** ** Final State *)

  (** A Vminus program halts when the program reaches the [tmn_ret] instruction. *)
  
  Definition FinalState (g:Cfg.t) (s:state) : Prop :=
    exists uid, insn_at_pc g s.(st_pc) (uid, cmd_tmn tmn_ret).

  (**  ------------------------------------------------------------------------- *)  
  (** ** Progress *)

  (** The statement of progress is exactly as expected.  For any well-formed 
  program in a well-formed state, either the program has finished, or the 
  program can take a step. *)
  
  Lemma progress : forall g s,
    wf_prog g -> wf_state g s ->
    FinalState g s \/ exists s', step g s s'.
  Proof.
    intros g s Hwff Hwfs.
    inversion Hwfs as [? Hwfpc]; subst. inversion Hwff.
    pose proof (wf_pc_insn g Hwfcfg _ Hwfpc) as [[i c] Hi].
    rename s into j. set (s:=j) in *. destruct j. 
    destruct c.
  
    - (* Case "cmd_bop". *)
    eelim (eval_val__wf_loc) with (v:=v) (loc:=st_loc0); eauto; simpl; auto.
    eelim (eval_val__wf_loc) with (v:=v0) (loc:=st_loc0); eauto; simpl; auto.
    intros n1 Heqn1 n2 Heqn2.
    right. eexists. eapply step_bop; eauto. unfold eval_bop.
    rewrite Heqn1, Heqn2. reflexivity. 

    - (* Case "cmd_phi". *)
    right. specialize (Hwfis _ _ Hi). inversion Hwfis; subst.
    
    destruct Hwfppc as [|Hwfppc]. 
    exfalso; eapply at_entry_not_phi; eauto. simpl; trivial.
    destruct Hwfploc as [|Hwfploc]. 
    exfalso; eapply at_entry_not_phi; eauto. simpl; trivial.

    destruct (Hphi I) as [Hphi2 _]. clear Hphi.
    specialize (Hphi2 st_ppc0 Hwfppc). destruct Hphi2 as [[v Hin] Hdom].

    cut (exists v, assoc Lbl.eq_dec (lbl_of st_ppc0) l = Some v). intros [v' Hv].
    cut (exists n, eval_val st_ploc0 v' = Some n). intros [n Hn].
    eexists. eapply step_phi. eauto. unfold eval_phi.
    rewrite Hv. rewrite Hn. reflexivity.
  
    destruct v' as [i' | n']. simpl in *. apply Hwfploc. apply Hdom. 
    eapply assoc_in. apply Hv. simpl; eauto.
    eapply in_assoc_some. apply Hin.
  
    - (* Case "cmd_tmn". *)
    destruct t0.
    * (*  SCase "tmn_jmp". *)
      right. eexists. eapply step_tmn. eauto. reflexivity.

    * (* SCase "tmn_cbr". *)
      cut (exists n, eval_val st_loc0 v = Some n). intros [n Heqn].
      right. eexists. eapply step_tmn. eauto. simpl. rewrite Heqn. reflexivity.
      eapply eval_val__wf_loc; eauto; simpl; auto. 

    * (* SCase "tmn_ret". *)
      left. unfold FinalState. eexists. eauto.

    - (* Case "cmd_load". *)
    right. eexists. apply step_load. eauto.

    - (* Case "cmd_store". *)
    right. cut (exists n1, eval_val st_loc0 v = Some n1). 
    intros [n1 Heqn1]. eexists. eapply step_store. eauto. eauto.
    eapply eval_val__wf_loc; eauto; simpl; auto.
  Qed.

  (** *** Some first steps towards preservation. *)

  Lemma wf_pc_incr : forall g p i,
    wf_prog g ->
    wf_pc g p ->
    insn_at_pc g p i ->
    ~ is_tmn i ->
    wf_pc g (incr_pc p).
  Proof.
    intros. inversion H. 
    apply (wf_pc_tmn g Hwfcfg) in H0 as [pt [Ht Hle]].
    eapply wf_pc_le_tmn; eauto.
    inversion Hle; subst. destruct H0.
    contradict H2. eapply Hwftmn; eauto. 
    constructor; auto with arith.
  Qed.

  Lemma eval_tmn_in_lbls : forall l loc t uid,
    Some l = eval_tmn loc t -> In l (insn_lbls (uid, cmd_tmn t)).
  Proof.
    intros.
    destruct t0; simpl in *.
    inversion H; auto.
    destruct (eval_val loc v). injection H. 
      destruct n; eauto.
      discriminate H. discriminate H.
  Qed.

  (** *** More preservation helpers*)

  Lemma not_def_sdom_step : forall g p1 p2 i uid,
    wf_prog g ->
    wf_pc g p2 ->
    insn_at_pc g p1 i ->
    ~ defs_uid i ->
    succ_pc g p1 p2 ->
    uid_sdom_pc g uid p2 ->
    uid_sdom_pc g uid p1.
  Proof. 
    destruct i; intros. inversion H4 as [? [[? [? Ht]] ?]].
    eapply uid_sdom_step; [ apply H | idtac | apply H0
                            | apply H3 | apply H1 | apply H4].
    contradict Ht. subst t0. assert (x = p1). 
    inversion H; eapply uid_at_pc_inj; try red; eauto. subst x.
    replace (uid, x0) with (uid, c); trivial. 
    inversion H; eapply insn_at_pc_func; eauto.
  Qed.

  Lemma wf_loc_succ : forall g p1 p2 loc uid n c,
   wf_prog g ->
   wf_pc g p2 ->
   insn_at_pc g p1 (uid, c) ->
   succ_pc g p1 p2 ->
   wf_loc g p1 loc ->
   wf_loc g p2 (update loc uid (Some n)).
  Proof.
    intros. red; intros. destruct (Uid.eq_dec uid0 uid). subst.
    rewrite Locals.update_eq; eauto. reflexivity.
    rewrite Locals.update_neq; eauto. apply H3.
    eapply uid_sdom_step; eauto. 
  Qed.

  (** ** Preservation *)

  Lemma preservation : forall g s s',
    wf_prog g ->
    wf_state g s -> step g s s' -> wf_state g s'.
  Proof.
    intros g _ s' Hwff [s Hwfpc Hwfloc] Hstep.
    inversion Hstep; subst; simpl in *;
      rename pc into pc0.
    
    - (* Case "step_bop". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.

    - (* Case "step_phi". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.
  
    - (* Case "step_tmn". *)
    assert (wf_pc g (l', 0)) as Hwfpc'.
      inversion Hwff as [_ Hwfi _]. specialize (Hwfi _ _ H).
      inversion Hwfi. red in Hlbl. apply Hlbl. 
      eauto. eapply eval_tmn_in_lbls. eauto.

    assert (succ_pc g pc0 (l', 0)) as Hsucc.
      econstructor. eauto. eapply eval_tmn_in_lbls. eauto.
    constructor; simpl; eauto. red; intros. apply Hwfloc.
    eapply not_def_sdom_step; eauto.

    - (* Case "step_load". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.

    - (* Case "step_store". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    red; intros. apply Hwfloc. eapply not_def_sdom_step; eauto. constructor.
  Qed.


End OpsemCorrect.

End MakeStatics.