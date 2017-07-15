Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Vminus.Classes.
Require Import Vminus.Util.
Require Import Vminus.Vminus.

Require Import Vminus.CFG.
Set Bullet Behavior "Strict Subproofs".

(* ################################################################# *)
(** * List-based CFG Implementation *)

(**  One possible implementation of cfgs *)

Module ListCFG <: CFG.

  (** Blocks are labels paired with lists of instructions. *)
  
  Definition block := (lbl * list insn)%type.

  (** A control-flow graph is an entry label with a list of blocks. *)
  
  Definition t := (lbl * list block)%type.
  Local Notation cfg := t.

  Definition entry_block : cfg -> lbl := @fst _ _.

  (**  ------------------------------------------------------------------------- *)  
  (** * Syntactically Well-formed ListCFGs *)

  (** 
      - no duplicate block names
      - no duplicate instruction ids  (i.e. _single assignment_ )
      - there is an entry label to the CFG
      - there are no empty blocks

   *)
  
  Inductive wf_cfg' : cfg -> Prop :=
    wf_cfg_intro :
      forall l bs
        (Hlbls: NoDup (map (@fst _ _) bs))
        (Huids: NoDup (flat_map (fun b => map (@fst _ _) (snd b)) bs))
        (Hentry: In l (map (@fst _ _) bs))
        (Hnonnil: ~ In [] (map (@snd _ _) bs)),
        wf_cfg' (l, bs).

  (* hack around some Coq limitation re inductive types & parameters *)
  Definition wf_cfg := wf_cfg'.

    
  (**  ------------------------------------------------------------------------- *)  
  (** ** Implementing the interface requirements: *)
  
  Definition wf_pc (g:cfg) (p:pc) : Prop :=
    let (l, n) := p in
    exists is i, In (l, is) (snd g) /\ Nth i is n.

  Definition tmn_pc (g:cfg) (p:pc) : Prop :=
    let (l, n) := p in
    exists is, In (l, is) (snd g) /\ n = pred (length is).

  Definition insn_at_pc (g:cfg) (p:pc) (i:insn) : Prop :=
    let (l, n) := p in
    exists is, In (l, is) (snd g) /\ Nth i is n.
    
  Definition uid_at_pc (g:cfg) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c).

  Lemma wf_pc_insn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists i, insn_at_pc g p i.
  Proof.
    unfold wf_pc, insn_at_pc. destruct p; intros. 
    decompose [ex and] H0. eauto.
  Qed.

  Lemma wf_pc_tmn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists p', tmn_pc g p' /\ le_pc p p'.
  Proof.

    unfold wf_pc, tmn_pc. destruct p. intros.
    decompose [ex and] H0. 
    exists (t0, pred (length x)). split. eauto.
    constructor. 
    apply PeanoNat.Nat.lt_le_pred.
    eapply Nth_length; eauto.
  Qed.


  (* Helper lemma: blocks have non-zero length. *)
  
  Lemma wf_cfg_block_len : forall g, wf_cfg g ->
    forall l is, In (l, is) (snd g) -> length is <> 0.
  Proof.
    inversion 1. intros l0 is H1.  destruct is; simpl; auto. 
    contradict Hnonnil. 
    eapply in_map with (f:=@snd _ _) in H1. auto.
  Qed.

  Lemma wf_pc_le_tmn : forall g, wf_cfg g ->
    forall p', tmn_pc g p' -> forall p, le_pc p p' -> wf_pc g p.
  Proof.
    unfold wf_pc, tmn_pc. intros g H p' H0 p H1.  destruct p, p'.
    decompose [ex and] H0. exists x.

    destruct x. apply wf_cfg_block_len in H3; auto. contradict H3; auto.
    inversion H1; subst. apply le_lt_n_Sm in H5. 
    erewrite <- S_pred in H5. 
    apply length_Nth in H5 as [? ?]. 
    eexists. split; eauto. eauto.
  Qed.
  
  Lemma wf_entry : forall g, wf_cfg g ->
    wf_pc g (block_entry (entry_block g)).
  Proof.
    unfold wf_pc. inversion 1. simpl.
    apply in_map_iff in Hentry as [[? ?] [? ?]].
    destruct l0.
    exfalso. pose proof (wf_cfg_block_len g H t0 []) as contra. 
    subst g; simpl in *. apply contra; auto.
    eexists. eexists. 
    simpl in *. subst l. split; eauto.
    simpl; eauto.
  Qed.
  
  Lemma insn_at_pc_func : forall g, wf_cfg g ->
    functional (insn_at_pc g).
  Proof.
    unfold functional, insn_at_pc. inversion 1. destruct a.
    intros b1 b2 [is1 [Hin1 Hnth1]] [is2 [Hin2 Hnth2]].
    cut (is1 = is2). intro; subst is2. eapply Nth_eq; eauto.
    eapply NoDup_assoc_func; eauto.
  Qed.
  
  Lemma uid_at_pc_inj : forall g, wf_cfg g ->
    injective (uid_at_pc g).
  Proof.
    unfold injective, uid_at_pc, insn_at_pc. inversion 1.
    intros [l1 n1] [l2 n2] uid [c1 [is1 [Hin1 Hnth1]]] [c2 [is2 [Hin2 Hnth2]]].
    cut ((l1, is1) = (l2, is2)).
    intro Heq. inversion Heq; clear Heq. f_equal.
    eapply NoDup_flat_map__NoDup in Huids; eauto.
    change is1 with (snd (l1, is1)) in Hnth1.
    change is2 with (snd (l2, is2)) in Hnth2.
    subst; eapply NoDup_nth_inj; eauto. 

    set (f1 b := map (@fst _ _) (snd b)) in *.
    apply (NoDup_flat_map (l1, is1) (l2, is2) uid f1 bs); auto.
    unfold f1; simpl. 
    apply in_map_iff. exists (uid, c1); eauto using Nth_In.
    apply in_map_iff. exists (uid, c2); eauto using Nth_In.
  Qed.

  Lemma uid_at_pc_func : forall g, wf_cfg g ->
    functional (uid_at_pc g).
  Proof.
    intros g Hwfc. specialize (insn_at_pc_func g Hwfc).
    unfold functional, uid_at_pc. intros.
    destruct H0 as [c1 ?]. destruct H1 as [c2 ?].
    cut ((b1,c1) = (b2,c2)). inversion 1; auto.
    eauto.
  Qed.

  Lemma eq_pc_uid : forall g pc id1 id2 c1 c2,
    wf_cfg g ->
    insn_at_pc g pc (id1, c1) ->
    insn_at_pc g pc (id2, c2) ->
    id1 = id2.
  Proof.
    intros. pose proof (uid_at_pc_func g H).
    unfold functional in H2. eapply H2; red; eauto.
  Qed.

  
  Lemma blocks_inj : forall g, wf_cfg g -> forall l is1 is2, In (l, is1) (snd g) -> In (l, is2) (snd g) -> is1 = is2.
  Proof.
    intros g H l is1 is2 H0 H1.
    inversion H.
    subst; simpl in *.
    eapply NoDup_assoc_func; eauto.
  Qed.
  
  Lemma pc_at_uid_inj : forall g, wf_cfg g ->
                             injective (fun x p => uid_at_pc g p x).
  Proof.
    unfold injective, uid_at_pc, insn_at_pc.
    intros g Hwf a1 a2 [l n] [c1 [is1 [Hin1 Hn1]]] [c2 [is2 [Hin2 Hn2]]].
    inversion Hwf. subst. simpl in *.
    assert (is1 = is2).
    eapply NoDup_assoc_func; eauto. subst.
    assert ((a1, c1) = (a2, c2)) as H. eapply Nth_eq; eauto.
    inversion H. reflexivity.
  Qed.

  (**  ------------------------------------------------------------------------- *)  
  (** ** Working with ListCFG *)

  Fixpoint remove (bs:list block) (l:lbl) : list block :=
    match bs with
    | [] => []
    | (l',is)::bs =>
      if l == l' then
        remove bs l
      else (l',is)::remove bs l
    end.                                                      
  
  (** [update] Adds the given instruction list as a block labeled [l]. 

      Note: this function does not enforce the unique-block label property.
  *)

  Definition update (bs:list block) (l:lbl) (is:list insn) : list block :=
    (l, is)::bs.

  (** Lookup the block in the list. *)

  Definition lookup (bs:list block) (l:lbl) : option (list insn) :=
    assoc Lbl.eq_dec l bs.

  (** ** Simple lemmas about CFG modifications. *)

  Lemma update_eq :
    forall (is : list insn) (l1 l2 : lbl) (bs : list block),
      l1 = l2 -> lookup (update bs l1 is) l2 = Some is.
  Proof.
    intros; unfold update, lookup.
    subst. simpl. destruct (Lbl.eq_dec l2 l2); tauto.
  Qed.

  Lemma update_neq :
    forall (l1 l2 : lbl) (is : list insn) (bs: list block),
      l1 <> l2 -> lookup (update bs l1 is) l2 = lookup bs l2.
  Proof.
    intros; subst; simpl.
    destruct (Lbl.eq_dec l2 l1); subst; tauto.
  Qed.

  (**  ------------------------------------------------------------------------- *)  
  (** ** Implementing fetch *)
  
  Definition fetch (g : cfg) (p: pc): option insn :=
    let '(entry_label, blocks) := g in
    let '(trgt_block, offset) := p in
    match (lookup blocks trgt_block) with
    | Some found_block => nth_error found_block offset
    | None => None
    end.

  (** Helper lemma for proving that fetch corresponds to insn_at_pc *)
  
  Lemma fetch_iff_in_cfg: forall entry_label blks trgt_label trgt_offset i,
      NoDup (map fst blks) -> 
      fetch (entry_label, blks) (trgt_label, trgt_offset) = Some i <->
      exists instrs, In (trgt_label, instrs) blks /\ Nth i instrs trgt_offset.
  Proof.
    intros entry_label blks trgt_label trgt_offset i nodup.
    unfold fetch.
    destruct (lookup blks trgt_label) eqn:found.
    - unfold lookup in found. apply assoc_in in found.
      split.
      + intros. exists l. split; auto. apply nth_error_iff_Nth; auto.
      + intros [is [Hi Hnth]].
        assert (l = is).
        eapply NoDup_assoc_func; eauto. subst.
        eapply nth_error_iff_Nth; auto.
    - split.
      + intros H. inversion H.
      + intros [l [Hin Hn]].
        apply nth_error_iff_Nth in Hn. unfold lookup in found.
        apply in_assoc_none with (b:=l) in found.
        contradiction.
  Qed.
  
  (** [fetch] is the executable version of [insn_at_pc] *)
  
  Lemma insn_at_pc_fetch :
    forall g pc i, wf_cfg g ->
              insn_at_pc g pc i <-> fetch g pc = Some i.

  Proof.
    intros [l blks] pc i wf_g.
    inversion wf_g as
        [l' blks' nodup nodup_uid l_in_blks blks_not_empty [l_l' blks_blk]].
    destruct pc as [curr_label curr_offset].
    rewrite fetch_iff_in_cfg; auto.
    simpl.
    split; auto.
  Qed.      
  
End ListCFG.