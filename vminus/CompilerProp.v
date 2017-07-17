Require Import FunctionalExtensionality. (* TODO: don't really need this *)
Require Import List.
Import ListNotations.
Require Import RelationClasses.


Require Import Vminus.Util Vminus.Classes.
Require Import Vminus.Vminus.
Require Import Vminus.CFG.
Require Import Vminus.ListCFG.
Require Import Vminus.Sequences.
Require Import Vminus.VminusOpSem.
Require Import Vminus.Imp.
Require Import Vminus.Compiler.

Import V.Opsem.


Set Bullet Behavior "Strict Subproofs".
Unset Printing Records.


(* ################################################################# *)
(** * To possibly refactor into CFGProp *)
(* ================================================================= *)
(** ** Correspondence between concrete and abstract CFGs. *)

(** Asserts that the instruction sequence found at program point p in
    the control-flow graph g is exactly the list [is]. *)

Fixpoint insns_at_pc (g:ListCFG.t) (p:pc) (is:list insn) : Prop :=
  match is with
    | nil => True
    | i :: is' => ListCFG.insn_at_pc g p i /\ insns_at_pc g (incr_pc p) is'
  end.

(** Looking up the block labeled [l] in the concrete represenation
    agrees with the declarative specification. *)

Lemma cfg_insns_at : forall g l is e,
  ListCFG.lookup g l = Some is ->
  insns_at_pc (e, g) (block_entry l) is.
Proof.
  intros.
  pose (k:=@nil insn). change is with (k ++ is) in H.
  unfold block_entry. change 0 with (length k).
  clearbody k. generalize dependent k.
  induction is; intros. simpl; auto.
    simpl. split. eexists. split.
    unfold ListCFG.lookup in H.
    apply assoc_in in H. simpl; eauto.
    clear H. induction k; simpl; auto.
    replace (S (length k)) with (length (k ++ [a])). apply IHis.
      rewrite <- app_assoc. auto. rewrite app_length.
      simpl. apply PeanoNat.Nat.add_1_r.
Qed.

(* ################################################################# *)
(** * End refactoring *)


(* ================================================================= *)
(** ** Auxiliary definitions. *)

Definition ids_preserved (cs:list uid) (st st':state) : Prop :=
  forall uid n, In uid cs ->
    st_loc st uid = Some n -> st_loc st' uid = Some n.

Definition good_return (cs:list uid) (v:val) : Prop :=
  forall uid, v = val_uid uid -> In uid cs.

Definition ctx_incr (cs cs':list uid) : Prop :=
  forall uid, In uid cs -> In uid cs'.

Instance ctx_incr_trans : Transitive ctx_incr.
Proof. red; unfold ctx_incr; intuition. Qed.



(* ################################################################# *)
(** * Proofs start here; commented out because of QuickChick for now  *)
Definition comp_correct (comp : ectmon (val * list insn))
                        (eval : mem -> nat) : Prop :=
  forall cs cs' g st is k v,
  (cs', (v, is)) = comp cs ->
  insns_at_pc g (st_pc st) (is ++ k) ->
  exists st',
    st_mem st' = st_mem st /\
    insns_at_pc g (st_pc st') k /\
    star (step g) st st' /\
    ids_preserved cs st st' /\
    good_return cs' v /\
    ctx_incr cs cs' /\
    eval_val (st_loc st') v = Some (eval (st_mem st)).

Lemma comp_bop_correct : forall b comp1 comp2 eval1 eval2
    (IHa1: comp_correct comp1 eval1)
    (IHa2: comp_correct comp2 eval2),
    comp_correct (comp_bop b comp1 comp2)
                 (fun m => bop_denote b (eval1 m) (eval2 m)).
Proof.
  unfold comp_correct.
  intros b comp1 comp2 eval1 eval2.
  intros until v. intros Hcomp Hinsns.

  unfold comp_bop in Hcomp.
  simpl in Hcomp.
  destruct (comp1 cs) as [cs1 [rl1 rr1]] eqn:Hc1.
  destruct (comp2 cs1) as [cs2 [rl2 rr2]] eqn:Hc2.
  inversion Hcomp; clear Hcomp.

  subst.
  repeat rewrite <- app_assoc in Hinsns.
  eelim IHa1; [| eauto ..].
  intros st1 (Hinv1 & His1 & Hstep1 & Hpres1 & Hret1 & Hincr1 & Heval1).
  eelim IHa2; [| eauto ..].
  intros st2 (Hinv2 & His2 & Hstep2 & Hpres2 & Hret2 & Hincr2 & Heval2).
  clear IHa1 IHa2.

  rename st2 into st2'; set (st2:=st2') in *; destruct st2'.
  eexists {| st_pc  := incr_pc (st_pc st2);
             st_loc := Locals.update (st_loc st2) (Uid.fresh cs2) _ |}. simpl.

  (* exp_invar *)
  split. transitivity (st_mem st1). transitivity (st_mem st2). reflexivity. auto.  apply Hinv1.

  (* insns_at_pc *)
  split. inversion His2; auto.

  (* star (Opsem.step g) *)
  split. eapply star_trans; eauto. eapply star_trans; eauto.
    eapply star_one. eapply step_bop. inversion His2; eauto.
    unfold eval_bop. simpl in Heval2. rewrite Heval2.
    replace (eval_val st_loc0 _) with (Some (eval1 (st_mem st))).
    reflexivity. symmetry.

    destruct rl1; auto. simpl.
    unfold good_return in *.
    rename t into t0.
    assert (In t0 cs1). apply Hret1; auto.
    unfold ids_preserved in Hpres2.
    apply Hpres2. auto. auto.

  (* ids_preserved *)
  split. red; simpl; intros. rewrite Locals.update_neq.
  change st_loc0 with (st_loc st2).
  apply Hpres2; auto. apply Hincr1, Hincr2 in H.
  inversion Hc2. contradict H. rewrite <- H. apply Uid.fresh_not_in.

  (* good_return *)
  split. red. intros uid' Hid. injection Hid; inversion Hc2. left; auto.

  (* ctx_incr *)
  split. transitivity cs1; auto. transitivity cs2; auto.
  unfold ctx_incr. inversion Hc2; intros. right; auto.

  (* eval_val *)
  simpl. rewrite Locals.update_eq.
  replace (st_mem st1) with (st_mem st). subst. reflexivity.
  inversion Hinv1; auto. reflexivity.
Qed.


Lemma comp_aexp_correct : forall (a:aexp),
  comp_correct (comp_aexp a) (aeval a).
Proof.
  (* comp_bop_correct takes care of all the inductive cases *)
  induction a; [ | | eapply comp_bop_correct; auto ..].

  - (* Case "ANum". *)
  unfold comp_correct; intros. inversion H; subst; clear H.
  exists st. repeat split; try red; auto using star_refl. discriminate.

  - (* Case "AId". *)
  unfold comp_correct. intros cs cs' g st is k v Hcomp Hinsns.
  simpl in Hcomp.
  destruct (fresh cs) as [cs1 idr] eqn:Hc.
  inversion Hcomp. clear Hcomp. subst.

  rename st into st'. set (st := st'). destruct st'.
  eexists {| st_pc := (incr_pc (st_pc st));
             st_loc := Locals.update (st_loc st) idr _ |}. simpl.
  split. reflexivity.
  split. inversion Hinsns; auto.
  split. apply star_one. apply step_load.
  inversion Hinsns; eauto.
  simpl in *.
  unfold fresh in Hc. inversion Hc. apply H.
  split. red; simpl; intros. rewrite Locals.update_neq; auto.
    inversion Hc. contradict H. rewrite <- H. apply Uid.fresh_not_in.
  split. red. intros. inversion Hc. injection H; intro. subst idr uid. left; auto.
  split. inversion Hc; red; intuition.
  rewrite Locals.update_eq. reflexivity. inversion Hc. reflexivity.
Qed.

Local Hint Resolve comp_aexp_correct.

Lemma comp_bexp_correct : forall (b:bexp),
  comp_correct (comp_bexp b) (fun m => b2n (beval b m)).
Proof.
  induction b.

  - (* Case "BTrue". *)
  unfold comp_correct; intros. inversion H; subst; clear H.
  exists st; repeat split; try red; auto using star_refl. discriminate.

  - (* Case "BFalse". *)
  unfold comp_correct; intros. inversion H; subst; clear H.
  exists st; repeat split; try red; auto using star_refl. discriminate.

  - (* Case "BEq". *)
  eapply (comp_bop_correct bop_eq); auto.

  - (* Case "BLe". *)
  eapply (comp_bop_correct bop_le); auto.

  - (* Case "BNot". *)
  simpl. evar (SPEC : mem -> nat). replace (fun (m:mem) => b2n _) with SPEC.
  subst SPEC. apply (comp_bop_correct bop_eq); eauto.
  unfold comp_correct; intros. inversion H; subst; clear H.
  instantiate (1:=fun m => 0).
  exists st; repeat split; try red; auto using star_refl. discriminate.
  unfold SPEC. apply functional_extensionality. intro.
  destruct (beval b x); auto.

  - (* Case "BAnd". *)
  simpl. evar (SPEC : mem -> nat). replace (fun (m:mem) => b2n _) with SPEC.
  subst SPEC. apply (comp_bop_correct bop_and); eauto.
  subst SPEC. apply functional_extensionality. intro.
  simpl. destruct (beval b1 x), (beval b2 x); auto.
Qed.


(**
  - First we define some helper definitions for compiling assignments and
    conditionals.
    - To simplify the simulation: each store is compiled to its own basic block.
  - Then we define the command compilation context as a state monad.
    - Generate fresh uids (like the [ectmon])
    - Generate fresh block labels
    - Add instructions to the (partial) CFG
  - Then we define the translation of commands (recursively).
*)


Lemma comp_store_correct :
  forall g a v le lr cs st,
  insns_at_pc g (block_entry le) (strun (comp_store a v lr) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = (block_entry lr) /\
    st_mem st' = (Memory.update (st_mem st) v (aeval a (st_mem st))).
Proof.
  intros.
  unfold strun, comp_store in H. simpl in H.
  match type of H with context[let (_,_) := ?x in _] => destruct x eqn:Hc end.
  destruct p as [x is].
  simpl in H. symmetry in Hc.

  rewrite <- H0 in H.
  eelim (comp_aexp_correct a); eauto.
  intros st' H'. decompose [and] H'; clear H'.
  rename st' into st''. set (st' := st'') in *. destruct st''.

  eexists.
  split. eapply plus_star_trans'. eauto.
  eapply plus_left. eapply step_store. apply H3. eauto.
  eapply star_step. eapply step_tmn. inversion H3. apply H9.
  reflexivity.
  eapply star_refl.
  simpl. split; auto.
  rewrite <- H1. reflexivity.
Qed.


Lemma comp_cond_correct :
  forall g cs b le l1 l2 st,
  insns_at_pc g (block_entry le) (strun (comp_cond b l1 l2) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = block_entry (if beval b (st_mem st) then l1 else l2) /\
    st_mem st = st_mem st'.
Proof.
  intros.
  unfold strun, comp_cond in H. simpl in H.
  match type of H with context[let (_,_) := ?x in _] => destruct x eqn:Hc end.
  destruct p as [x is].
  simpl in H. symmetry in Hc.

  rewrite <- H0 in H.
  eelim (comp_bexp_correct b); eauto.
  intros st' H'. decompose [and] H'; clear H'.
  rename st' into st''. set (st' := st'') in *. destruct st''.

  eexists.
  split. eapply plus_star_trans'. eauto.
  eapply plus_one. eapply step_tmn.
  apply H3. simpl in *. rewrite H8. reflexivity.
  simpl. split; auto.
  destruct (beval b (st_mem st)); simpl; auto.
Qed.


(* ================================================================= *)
(* ** Compiling Commands *)

(** State:
    - list of used block labels
    - list of used uids
    - current cfg *)

Definition cstate := (list lbl * list uid * list ListCFG.block)%type.
Notation ctmon := (ST cstate).

Definition fresh_lbl : ctmon lbl :=
  fun cs =>
  let '(ls, is, bs) := cs in
  let l := Lbl.fresh ls in
  (l::ls, is, ListCFG.update bs l [], l).

Definition raise_ectmon {T} (ec:ectmon T) : ctmon T :=
  fun cs =>
  let '(ls, is, cfg) := cs in
  let (is', r) := ec is in
  (ls, is', cfg, r).

Definition add_insns (l:lbl) (b:list insn) : ctmon unit :=
  fun cs =>
  let '(ls, is, cfg) := cs in
  (ls, is, ListCFG.update cfg l b, tt).

Open Scope imp_scope.

(* ################################################################# *)
(** * Correctness? *)

(** - Vminus is deterministic
    - Suffices to show a forward simulation. *)

(* ================================================================= *)
(** ** Simulation relation. *)

(** Relate Imp commands to sequences of basic blocks in the cfg. *)

Inductive match_config : Imp.com -> (ListCFG.t * lbl * lbl) -> Prop :=
  | MC_Skip : forall bs l,
      match_config SKIP (bs, l, l)
  | MC_Ass : forall g l l' uid a cs,
      insns_at_pc g (block_entry l) (strun (comp_store a uid l') cs) ->
      match_config (CAss uid a) (g, l, l')
  | MC_Seq : forall g l1 l2 l3 c1 c2,
      match_config c1 (g, l1, l2) ->
      match_config c2 (g, l2, l3) ->
      match_config (CSeq c1 c2) (g, l1, l3)
  | MC_If : forall g le lr l1 l2 b c1 c2 cs,
      match_config c1 (g, l1, lr) ->
      match_config c2 (g, l2, lr) ->
      insns_at_pc g (block_entry le) (strun (comp_cond b l1 l2) cs) ->
      match_config (CIf b c1 c2) (g, le, lr)
  | MC_While : forall g le lb lr b c cs,
      match_config c (g, lb, le) ->
      insns_at_pc g (block_entry le) (strun (comp_cond b lb lr) cs) ->
      match_config (CWhile b c) (g, le, lr).

Inductive match_states (g:ListCFG.t) (r:lbl)
  : (com * Imp.state) -> state -> Prop :=
  match_states_intro : forall c mem st l,
    match_config c (g, l, r) ->
    st_pc st = block_entry l ->
    st_mem st = mem ->
    match_states g r (c, mem) st.


Require Import Program.Equality.

(* ================================================================= *)
(** ** Translation simulation: First try. *)

Lemma simulation_step' :
  forall g c c' mem mem' st r,
  Imp.step (c, mem) (c', mem') ->
  match_states g r (c, mem) st ->
  exists st',
    star (step g) st st' /\
    match_states g r (c', mem') st'.
Proof.
  intros. generalize dependent st. revert r.

  dependent induction H; intros;
  inversion H0 as [? ? ? ? H']; inversion H'; subst.

  - (* Case "S_Ass". *)
  eapply comp_store_correct in H6 as [st' [? [? ?]]]; eauto.
  eexists. split. apply plus_star. apply H1. econstructor; eauto. apply MC_Skip.

  - (* Case "S_Seq". *)
    specialize (IHstep c1 c1' (st_mem st) mem').
    pose (K:=IHstep ltac:(auto) ltac:(auto)); clearbody K; clear IHstep.
    specialize (K l2 st).
    lapply K.
    intros [st' [? ?]].
    exists st'. split; auto.
    inversion H3.
    econstructor; eauto. econstructor; eauto.
    econstructor; eauto.

  - (* Case "S_SeqSkip". *)
  exists st. split. apply star_refl.
  inversion H'; subst. inversion H4; subst.
  econstructor; eauto.

  - (* Case "S_IfTrue". *)
  eapply comp_cond_correct in H14 as [st' [? [? ?]]].
  exists st'. split. apply plus_star; eauto. econstructor.
  eauto. rewrite H in H3. auto. symmetry; auto. auto.

  - (* Case "S_IfFalse". *)
  eapply comp_cond_correct in H14 as [st' [? [? ?]]].
  exists st'. split. apply plus_star; eauto. econstructor.
  eauto. rewrite H in H3. auto. symmetry; auto. auto.

  - (* Case "S_While". *)
  exists st. split. apply star_refl.
  econstructor; eauto. eapply MC_If; eauto.
  econstructor; eauto. apply MC_Skip; eauto.
Qed.

(* ################################################################# *)
(** * Stuttering *)

(** The proof above goes through, but does not ensure that if the
    source program diverges the compiled program does not go wrong!

    To fix it, we need to ensure that there is no "infinite stuttering"
    in which the source program takes an infinite number of steps while
    the target terminates (or gets stuck).
*)

(* ================================================================= *)
(** ** Eliminating Stuttering *)

(** First, define an appropriate measure. *)

Fixpoint num_skips (c:com) : nat :=
  match c with
    | (c1 ;; c2) => num_skips c1 + num_skips c2
    | SKIP => 2
    | _ => 0
  end.

Fixpoint while_head (c:com) : nat :=
  match c with
    | (c1 ;; _) => while_head c1
    | WHILE _ DO _ END => 1
    | _ => 0
  end.

Definition com_size (c:com) : nat := num_skips c + while_head c.

(* ================================================================= *)
(** ** Lemmas about the measure. *)

Require Import Omega.

Lemma while_head_bound : forall c, while_head c < 2.
Proof. induction c; simpl; omega. Qed.

Lemma com_size_seq : forall c1 c1' c2,
  com_size c1' < com_size c1 ->
  com_size (c1';; c2) < com_size (c1;; c2).
Proof.
  unfold com_size; destruct c1, c1';
  try solve [simpl; intros; omega].
Qed.

Lemma com_size_seqskip : forall c,
  com_size c < com_size (SKIP;; c).
Proof.
  unfold com_size; destruct c;
  try solve [simpl; try match goal with
                        | |- context[while_head ?X] =>
                             pose proof (while_head_bound X)
                        end; intros; omega].
Qed.


(* lift to states *)
Definition imp_size (st:com * mem) : nat :=
  let (c, _) := st in com_size c.



Local Hint Constructors match_config.
Hint Resolve com_size_seqskip com_size_seq.

(* ================================================================= *)
(** ** Final simulation relation. *)

Lemma transl_sim_step_final :
  forall g r imp_st imp_st' vmn_st,
  Imp.step imp_st imp_st' ->
  match_states g r imp_st vmn_st ->
  exists vmn_st',
    (plus (step g) vmn_st vmn_st' \/
     star (step g) vmn_st vmn_st' /\ imp_size imp_st' < imp_size imp_st) /\
    match_states g r imp_st' vmn_st'.
Proof.
  intros. generalize dependent vmn_st. revert r.

  dependent induction H; intros r vmn_st Hst;
  inversion Hst as [? ? ? ? Hcfg]; inversion Hcfg; subst.

  - (* Case "S_Ass". *)
  eapply comp_store_correct in H6 as [st' [? [? ?]]]; eauto.
  eexists. split; eauto. econstructor; eauto.

  - (* Case "S_Seq". *)
  specialize (IHstep l2 vmn_st).
  lapply IHstep. intros [vmn_st' [? ?]]. exists vmn_st'. split.
  simpl in *; intuition. inversion H2; subst.
  econstructor; eauto. econstructor; eauto.

  - (* Case "S_SeqSkip". *)
  exists vmn_st. split. right.
  split. apply star_refl. unfold imp_size.
  simpl; intuition. inversion H7; subst. econstructor; eauto.

  - (* Case "S_IfTrue". *)
  eapply comp_cond_correct in H13 as [st' [? [? ?]]]; eauto.
  exists st'. split; eauto. econstructor; eauto.
  rewrite H in H2; auto.

  - (* Case "S_IfFalse". *)
  eapply comp_cond_correct in H13 as [st' [? [? ?]]]; eauto.
  exists st'. split; eauto. econstructor; eauto.
  rewrite H in H2; auto.

  - (* Case "S_While". *)
  exists vmn_st. split. right; intuition. apply star_refl.
  econstructor; eauto.
Qed.

(** Is this enough? *)

(* ================================================================= *)
(** ** Relating initial states *)

(** We still must relate the initial states! *)

(** First, some helpers: *)

Require Import Vminus.LtacDebug.

Lemma comp_store_not_nil : forall a v l cs,
  strun (comp_store a v l) cs <> [].
Proof.
  intros. unfold strun.
  remember (comp_store _ _ _ _) as ma.
  unfold comp_store in Heqma. simpl in Heqma.
  match type of Heqma with context[let (_,_) := ?x in _] => destruct x eqn:Hc end.
  destruct p as [v' is].
  subst ma; simpl. intro.
  eapply app_cons_not_nil; eauto.
Qed.

Lemma comp_cond_not_nil : forall b v l cs,
  strun (comp_cond b v l) cs <> [].
Proof.
  intros. unfold strun.
  remember (comp_cond _ _ _ _) as ma.
  unfold comp_cond in Heqma. simpl in Heqma.
  match type of Heqma with context[let (_,_) := ?x in _] => destruct x eqn:Hc end.
  destruct p as [v' is].
  subst ma; simpl. intro.
  eapply app_cons_not_nil; eauto.
Qed.

(* ================================================================= *)
(** ** Compilation invariant *)

(** Compilation only "extends" the compilation state:
    - Uids and labels change only monotonically.
    - Compilation never removes code.
  *)

Inductive cstate_incr : cstate -> cstate -> Prop :=
  cstate_incr_intro : forall ls ls' ids ids' g g',
    (forall l, In l ls -> In l ls') ->
    (forall l is, In l ls -> is <> nil ->
      ListCFG.lookup g  l = Some is -> ListCFG.lookup g' l = Some is) ->
    cstate_incr (ls, ids, g) (ls', ids', g').

Instance cstate_incr_trans : Transitive cstate_incr.
Proof.
  red. inversion 1. inversion 1. constructor; intuition.
Qed.

Inductive cstate_incr_strong : cstate -> cstate -> Prop :=
  cstate_incr_strong_intro : forall ls ls' ids ids' g g',
    (forall l, In l ls -> In l ls') ->
    (forall l, In l ls -> ListCFG.lookup g l = ListCFG.lookup g' l) ->
    cstate_incr_strong (ls, ids, g) (ls', ids', g').

Instance cstate_incr_strong_trans : Transitive cstate_incr_strong.
Proof.
  red. inversion 1. inversion 1. subst. constructor.
  auto. intros. transitivity (ListCFG.lookup g' l); eauto.
Qed.


Instance cstate_incr_strong_refl : Reflexive cstate_incr_strong.
Proof.
  red. intro cs. destruct cs as [[? ?] ?]. constructor; auto.
Qed.


Lemma add_insns_incr : forall l is g ls ids cs',
  ListCFG.lookup g l = Some [] ->
  add_insns l is (ls, ids, g) = (cs', tt) ->
  cstate_incr (ls, ids, g) cs'.
Proof.
  destruct cs' as [[? ?] ?]. intros.
  constructor. inversion H0; intuition.
  intros. inversion H0; subst. rewrite ListCFG.update_neq. auto.
  contradict H2. subst l. rewrite H3 in H. injection H; auto.
Qed.


Lemma ectmon_incr_strong :
  forall (A:Type) (m:ectmon A) (r:A) cs cs' ,
  raise_ectmon m cs = (cs', r) ->
  cstate_incr_strong cs cs'.
Proof.
  destruct cs as [[? ?] ?], cs' as [[? ?] ?].
  inversion 1.
  destruct (m l0). inversion H1; subst; clear H1.
  constructor; auto; intros.
Qed.


Lemma fresh_add_incr_strong :
  forall l is cs1 cs2 cs3 cs4,
  fresh_lbl cs1 = (cs2, l) ->
  cstate_incr_strong cs2 cs3 ->
  add_insns l is cs3 = (cs4, tt) ->
  cstate_incr_strong cs1 cs4.
Proof.
  intros until cs4. intros Hfresh Hincr Hadd.
  destruct cs1 as [[? ?] ?], cs2 as [[? ?] ?],
           cs3 as [[? ?] ?], cs4 as [[? ?] ?].
  inversion Hadd; inversion Hfresh; inversion Hincr; subst.

  constructor; intros. apply H8. right; auto.
  assert (Lbl.fresh l0 <> l).
    contradict H. rewrite <- H. apply Lbl.fresh_not_in.
  rewrite ListCFG.update_neq; auto. rewrite <- H13.
  rewrite ListCFG.update_neq; auto. right; auto.
Qed.

Ltac bind_step H :=
  match type of H with
  | context[let (_,_) := ?b in _] => destruct b as [?x ?y] eqn:?Hb
  end.


Ltac compile :=
  repeat
    match goal with
    | [ x : Compiler.cstate |- _] => destruct x as [[?lbls ?ids] ?bs]
(*    | [ H : context[Compiler.add_insns _ _ _] |- _ ] => simpl in H *)
    | [ H : context[let (_,_) := ?x in _] |- _] => destruct x as [?l ?r] eqn:?Heq
    | [ H : (_, _) = (_, _) |- _] => inversion H; subst; clear H
    | [ H : () |- _ ] => destruct H
    end.

Lemma comp_com_incr_strong: forall c cst cst' e r,
  comp_com c r cst = (cst', e) -> cstate_incr_strong cst cst'.
Proof.
  induction c; intros cst cst' e r Htr; simpl in Htr; compile.

  - (* Case "CSkip".*)
    reflexivity.

  - (* Case "CAss". *)
  eapply fresh_add_incr_strong; eauto.
  eapply ectmon_incr_strong; eauto.

  - (* Case "CSeq". *)
  eapply transitivity.
  eapply IHc2; eauto.  eapply IHc1; eauto.

  -  (* Case "CIf". *)
  eapply transitivity. eapply IHc1; eauto.
  eapply transitivity. eapply IHc2; eauto.
  eapply fresh_add_incr_strong; eauto.
  eapply ectmon_incr_strong; eauto.

  - (* Case "CWhile". *)
  eapply fresh_add_incr_strong.
  eauto. eapply transitivity. eapply IHc; eauto.
  eapply ectmon_incr_strong; eauto. eauto.
Qed.


Lemma cstate_incr_weaken : forall cst cst',
  cstate_incr_strong cst cst' ->
  cstate_incr cst cst'.
Proof.
  inversion 1. constructor. auto. intros. rewrite <- H1; auto.
Qed.

Lemma comp_com_incr: forall c cst cst' e r,
  comp_com c r cst = (cst', e) -> cstate_incr cst cst'.
Proof.
  intros. apply cstate_incr_weaken.
  eapply comp_com_incr_strong; eauto.
Qed.

(* ================================================================= *)
(** ** Relating Initial Compilation *)

(** The key lemma is: *)

Lemma match_init : forall c le lr csti cst x g' e,
  comp_com c lr csti = (cst, le) ->
  cstate_incr cst (x, g') ->
  match_config c (e, g', le, lr).
Proof.
  induction c; intros le lr csti cst x g' e Hcomp Hincr; simpl in Hcomp; compile.

  - (* Case "CSkip". *)
  apply MC_Skip.

  - (* Case "CAss". *)
    simpl in Heq. inversion Heq; subst; clear Heq.
    simpl in Heq0.
    destruct (comp_store a i lr ids1) eqn:Hc'.
    inversion Heq0; subst; clear Heq0.
    simpl in Heq1.
    inversion Heq1; subst; clear Heq1.

    eapply MC_Ass, cfg_insns_at.
    inversion Hincr. subst.
    apply H5. left; auto.
    apply comp_store_not_nil. rewrite ListCFG.update_eq; auto.
    f_equal. rewrite surjective_pairing in Hc' at 1.
    inversion Hc'. reflexivity.

  - (* Case "CSeq". *)
    eapply MC_Seq. eapply IHc1; eauto. eapply IHc2; eauto.
    eapply transitivity; eauto. eapply comp_com_incr; eauto.

  - (* Case "CIf". *)
    eapply MC_If.

    + eapply IHc1; eauto.
      eapply transitivity. eapply comp_com_incr; eauto.
      eapply transitivity; eauto. eapply cstate_incr_weaken.
      eapply fresh_add_incr_strong; eauto.
      eapply ectmon_incr_strong; eauto.

    + eapply IHc2; eauto.
      eapply transitivity; eauto. eapply cstate_incr_weaken.
      eapply fresh_add_incr_strong; eauto.
      eapply ectmon_incr_strong; eauto.

    + inversion Heq1. subst. clear Heq1.
      simpl in Heq2.
      compile.
      inversion Heq3. subst. clear Heq3.
      eapply cfg_insns_at.
      inversion Hincr. subst.
      apply H5. left; auto.
      apply comp_cond_not_nil.
      rewrite ListCFG.update_eq; auto.
      f_equal.
      rewrite surjective_pairing in Heq1 at 1.
      inversion Heq1. reflexivity.

  - (* Case "CWhile". *)
    eapply MC_While with (cs:=ids2).

    + simpl in Heq. inversion Heq; subst. clear Heq.

      eapply IHc. eauto.
      apply comp_com_incr_strong in Heq0.
      apply ectmon_incr_strong in Heq1.
      eapply transitivity; eauto.
      eapply transitivity; eauto.
      eapply cstate_incr_weaken; eauto.
      apply add_insns_incr in Heq2; eauto.

      inversion Heq1. subst. rewrite <- H6.
      inversion Heq0. subst. rewrite <- H8.
      rewrite ListCFG.update_eq; auto.
      left. auto.
      inversion Heq0. subst. apply H2. left. auto.

    + inversion Heq.  subst.

      apply cfg_insns_at.
      inversion Hincr. subst.
      apply H5.

      apply comp_com_incr_strong in Heq0.
      apply ectmon_incr_strong in Heq1.
      inversion Heq0. subst.
      inversion Heq2. subst.
      inversion Heq1. subst.
      apply H3. apply H2. left. reflexivity.

      apply comp_cond_not_nil.

      inversion Heq2. subst. rewrite ListCFG.update_eq; auto.
      f_equal. rewrite surjective_pairing in Heq1 at 1.
      inversion Heq1. subst. unfold strun.
      destruct (comp_cond b r0 lr ids2). reflexivity.
Qed.


(* adapted from Leroy, OPLSS '12 Compil.v *)
(* Generic simulation proof. *)

Section SIMULATION_DIAGRAM.

Variable state1: Type.	                          (* source states *)
Variable step1: state1 -> state1 -> Prop.         (* source step relation *)

Variable state2: Type.	                          (* target states *)
Variable step2: state2 -> state2 -> Prop.         (* target step relation *)

Variable match_states: state1 -> state2 -> Prop.  (* the invariant *)

Variable measure: state1 -> nat.                  (* for stuttering *)

Hypothesis simulation:
  forall S1 S1' S2,
  step1 S1 S1' -> match_states S1 S2 ->
  exists S2',
    (plus step2 S2 S2' \/
     star step2 S2 S2' /\ measure S1' < measure S1) /\
    match_states S1' S2'.

Lemma simulation_star:
  forall S1 S1', star step1 S1 S1' ->
  forall S2, match_states S1 S2 ->
  exists S2', star step2 S2 S2' /\ match_states S1' S2'.
Proof.
  induction 1; intros.

  - (* Case "zero transition". *)
  exists S2; split. apply star_refl. auto.

  - (* Case "one or more transitions". *)
  destruct (simulation _ _ _ H H1) as [S2' [P Q]].
  destruct (IHstar _ Q) as [S2'' [U V]].
  exists S2''; split.
  eapply star_trans; eauto. destruct P.
  apply plus_star; auto. destruct H2; auto.
  auto.
Qed.

Lemma simulation_infseq_productive:
  forall N S1 S2,
  measure S1 < N ->
  infseq step1 S1 ->
  match_states S1 S2 ->
  exists S1', exists S2',
      plus step2 S2 S2'
   /\ infseq step1 S1'
   /\ match_states S1' S2'.
Proof.
  induction N; intros.
  - (* Case "N = 0". *)
  omega.
  - (* Case "N > 0". *)
  inversion H0; clear H0; subst.
  destruct (simulation _ _ _ H2 H1) as [S2' [P Q]].
  destruct P.
  + (* SCase "one or several transitions". *)
  exists b; exists S2'; auto.
  + (* SCase "zero, one or several transitions". *)
  destruct H0. inversion H0; clear H0; subst.
    * (* SSCase "zero transitions". *)
    eapply IHN; eauto. omega.
    * (* SSCase "one or several transitions". *)
    exists b; exists S2'; split. eapply plus_left; eauto. auto.
Qed.

Lemma simulation_infseq:
  forall S1 S2,
  infseq step1 S1 ->
  match_states S1 S2 ->
  infseq step2 S2.
Proof.
  intros.
  apply infseq_coinduction_principle_2 with
    (X := fun S2 => exists S1, infseq step1 S1 /\ match_states S1 S2).
  intros. destruct H1 as [S [A B]].
  destruct (simulation_infseq_productive (measure S + 1) S a)
  as [S1' [S2' [P [Q R]]]].
  omega. auto. auto.
  exists S2'; split. auto. exists S1'; auto.
  exists S1; auto.
Qed.

End SIMULATION_DIAGRAM.


Definition vminus_terminates (g:ListCFG.t) (m m':mem) : Prop :=
  exists x st',
    insns_at_pc g st'.(st_pc) [(x, cmd_tmn tmn_ret)] /\
    st'.(st_mem) = m' /\
    star (step g) (init_state g m) st'.

Definition vminus_diverges (g:ListCFG.t) (m:mem) : Prop :=
  infseq (step g) (init_state g m).

Definition imp_terminates (c: com) (m m':mem) : Prop :=
  star Imp.step (c, m) (SKIP, m').

Definition imp_diverges (c: com) (mem: mem) : Prop :=
  infseq Imp.step (c, mem).

Lemma match_config_ret : forall g le lr c,
  (g, le, lr) = compile c ->
  exists x, insns_at_pc g (block_entry lr) [(x, cmd_tmn tmn_ret)].
Proof.
  intros. unfold compile, comp_prog in H. simpl in H. compile.

  eexists. eapply cfg_insns_at. apply comp_com_incr_strong in Heq1.
  inversion Heq1; subst. rewrite <- H6. rewrite ListCFG.update_eq; auto.
  left. reflexivity.
Qed.

Lemma match_config_initial : forall g le lr c m,
  (g, le, lr) = compile c ->
  match_states g lr (c, m) (init_state g m).
Proof.
  intros. unfold compile, comp_prog in H. simpl in H. compile.
  econstructor; simpl; eauto.

  eapply match_init. eauto. eapply cstate_incr_weaken.
  eapply cstate_incr_strong_refl.
Qed.

Theorem compile_program_correct_terminating:
  forall c m m' g le lr,
  (g, le, lr) = compile c ->
  imp_terminates c m m' ->
  vminus_terminates g m m'.
Proof.
  intros. unfold imp_terminates in H.
  assert (exists machconf2,
           star (step g) (init_state g m) machconf2
           /\ match_states g lr (SKIP, m') machconf2).
  eapply simulation_star; eauto. eapply transl_sim_step_final.
  eapply match_config_initial; eauto.
  destruct H1 as [machconf2 [STAR MS]].
  inversion MS; subst.
  eelim match_config_ret. intros.
  red. exists x, machconf2. split. rewrite H4. eauto. eauto.
  inversion H3; subst. eauto.
Qed.

Theorem compile_program_correct_diverging:
  forall c m g le lr,
  (g, le, lr) = compile c ->
  imp_diverges c m ->
  vminus_diverges g m.
Proof.
  intros; red; intros.
  eapply simulation_infseq with (match_states := match_states g lr); eauto.
  eapply transl_sim_step_final. eapply match_config_initial; eauto.
Qed.
