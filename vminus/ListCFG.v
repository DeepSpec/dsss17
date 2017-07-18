(** ListCFG: A list-based CFG Implementation *)
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

  (**  This definition of control-flow-graph syntactic well-formedness could
  be reformulated to use the Metatheory Library rather than the explicit use of
  NoDup here.  In particular, the ListCFG representation is an association list
  mapping labels to blocks) and the blocks themselves are also association lists.
  The NoDup requirements here could be replaced by the Metatheory Library's notion 
  of [uniq].  Porting the Vminus development to better make use of the Metatheory
  library is left as an exercise for the reader :-) 
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

  
  (** EX5? (naming challenge) *)
  (** Port the above definition of wf_cfg' to use the [uniq] predicate from the Metatheory library. 
      Fix up all of the proofs!
   *)
    
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

  (** For all of the following exercises, reference
      CFG.v as well as the other recommended files. *) 
  
  (** **** Exercise: 2 stars, optional (wf_pc_insn)  *)
  (** Prove that well formed program counters always 
      point to an instruction (you shouldn't need any
      other definitions): *)  
  Lemma wf_pc_insn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists i, insn_at_pc g p i.
  Proof.
    (* FILL IN HERE *) Admitted.


  (** **** Exercise: 2 stars, optional (wf_pc_tmn)  *)
  (** Prove that every block has a terminator. See 
      PeanoNat.Nat and util for some helpful theorems. *)
  Lemma wf_pc_tmn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists p', tmn_pc g p' /\ le_pc p p'.
  Proof.
  (* FILL IN HERE *) Admitted.


  (* Helper lemma: blocks have non-zero length. *)
  (** **** Exercise: 2 stars, optional (wf_cfg_block_len)  *)
  (** Prove that well formed control flow graphs 
      have non-zero length. See list 
      theorems about In and map. *)
  Lemma wf_cfg_block_len : forall g, wf_cfg g ->
    forall l is, In (l, is) (snd g) -> length is <> 0.
  Proof.
    (* FILL IN HERE *) Admitted.

  (** **** Exercise: 3 stars, optional (wf_pc_le_tmn)  *)
  (** Prove there are no "gaps" in the pc labels. 
      In other words, that all pcs that come before
      some arbitrary but particular pc are well formed. *)
  Lemma wf_pc_le_tmn : forall g, wf_cfg g ->
    forall p', tmn_pc g p' -> forall p, le_pc p p' -> wf_pc g p.
  Proof.
    (* FILL IN HERE *) Admitted.    

  (** **** Exercise: 3 stars, optional (wf_entry)  *)
  (** Prove there is an instruction in the entry block. 
      Take a look at theorems about in and map in List. *)
  Lemma wf_entry : forall g, wf_cfg g ->
    wf_pc g (block_entry (entry_block g)).
  Proof.
    (* FILL IN HERE *) Admitted.    

  (** **** Exercise: 3 stars, optional (insn_at_pc_func)  *)
  (** Prove that insn_at_pc with respect to a CFG g is a 
      function from program counter to instruction. *)
  Lemma insn_at_pc_func : forall g, wf_cfg g ->
    functional (insn_at_pc g).
  Proof.
  (* FILL IN HERE *) Admitted.    

  (** **** Exercise: 4 stars, optional (uid_at_pc_inj)  *)
  (** Prove that uid_at_pc with respect to a CFG g is injective. 
      Take a look at List for In and map, and Util. *)
  Lemma uid_at_pc_inj : forall g, wf_cfg g ->
    injective (uid_at_pc g).
  Proof.
  (* FILL IN HERE *) Admitted.

  (** **** Exercise: 3 stars, optional (uid_at_pc_func)  *)
  (** Prove that uid_at_pc with respect to a CFG g 
      is a function. *)
  Lemma uid_at_pc_func : forall g, wf_cfg g ->
    functional (uid_at_pc g).
(* FILL IN HERE *) Admitted.

  (** **** Exercise: 2 stars, optional (eq_pc_uid)  *)
  (** Prove that if two instructions are at the same
      pc in a well formed CFG, then their ids are the same. *)
  Lemma eq_pc_uid : forall g pc id1 id2 c1 c2,
    wf_cfg g ->
    insn_at_pc g pc (id1, c1) ->
    insn_at_pc g pc (id2, c2) ->
    id1 = id2.
(* FILL IN HERE *) Admitted.

  (** **** Exercise: 2 stars, optional (blocks_inj)  *)
  (** Prove that in a cfg, for each label there 
      exists a single block. See Util. *)
  Lemma blocks_inj : forall g, wf_cfg g -> forall l is1 is2,
        In (l, is1) (snd g) -> In (l, is2) (snd g) -> is1 = is2.
  Proof.
  (* FILL IN HERE *) Admitted.

  (** **** Exercise: 3 stars, optional (pc_at_uid_inj)  *)
  (** Prove the other end of uid_at_pc_inj, 
      showing that uid_at_pc is a bijection. *)
  Lemma pc_at_uid_inj : forall g, wf_cfg g ->
                             injective (fun x p => uid_at_pc g p x).
  Proof.
  (* FILL IN HERE *) Admitted.

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
(* ================================================================= *)
(** ** Correspondence between [lookup] and [insn_at_pc]. *)

(** The following proposition asserts that the instruction sequence found at
    program point [p] in the control-flow graph [g] is exactly the list [is].
    Note that this connects the dynamic notion of what it means to "increment"
    the program counter to the static notion of the list of instructions.
*)

Fixpoint insns_at_pc (g:cfg) (p:pc) (is:list insn) : Prop := 
  match is with
    | nil => True
    | i :: is' => ListCFG.insn_at_pc g p i /\ insns_at_pc g (incr_pc p) is'
  end.

(** We prove that looking up the block labeled [l] in the concrete
    representation agrees with [insns_at_pc].
*)

Lemma cfg_insns_at : forall (bs:list block) (l:lbl) (is:list insn) (e:lbl),
  lookup bs l = Some is ->
  insns_at_pc (e, bs) (block_entry l) is.
Proof.
  intros.
  pose (k:=@nil insn). change is with (k ++ is) in H.
  unfold block_entry. change 0 with (length k).
  clearbody k. generalize dependent k.
  induction is; intros.
  - simpl; auto.
  - simpl. split. eexists. split.
    unfold lookup in H.
    apply assoc_in in H. simpl; eauto.
    clear H. induction k; simpl; auto.
    replace (S (length k)) with (length (k ++ [a])). apply IHis.
      rewrite <- app_assoc. auto. rewrite app_length.
      simpl. apply PeanoNat.Nat.add_1_r.
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