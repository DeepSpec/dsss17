(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass. *)

Require Import Coqlib Errors.
Require Import Integers AST Linking.
Require Import Setoid.
Require Import Values Memory Separation Events Globalenvs Smallstep.
Require Import LTL Op Locations Linear Mach.
Require Import Bounds Conventions Stacklayout Lineartyping.
Require Import Stacking.
Require Import EraseArgs.

Local Open Scope sep_scope.

Definition match_prog (p: Linear.program) (tp: Mach.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

(** * Basic properties of the translation *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Remark align_type_chunk:
  forall ty, align_chunk (chunk_of_type ty) = 4 * Locations.typealign ty.
Proof.
  destruct ty; reflexivity.
Qed.

Lemma slot_outgoing_argument_valid:
  forall f ofs ty sg,
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> slot_valid f Outgoing ofs ty = true.
Proof.
  intros. exploit loc_arguments_acceptable_2; eauto. intros [A B].
  unfold slot_valid. unfold proj_sumbool.
  rewrite zle_true by omega.
  rewrite pred_dec_true by auto.
  auto.
Qed.

Lemma load_result_inject:
  forall j ty v v',
  Val.inject j v v' -> Val.has_type v ty -> Val.inject j v (Val.load_result (chunk_of_type ty) v').
Proof.
  intros until v'; unfold Val.has_type, Val.load_result; destruct Archi.ptr64;
  destruct 1; intros; auto; destruct ty; simpl;
  try contradiction; try discriminate; econstructor; eauto.
Qed.


Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls}.

Variable return_address_offset: Mach.function -> Mach.code -> ptrofs -> Prop.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Section WITHINITSP.

Variables init_sp init_ra: val.
Let step := Mach.step init_sp init_ra return_address_offset.

Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
  intros; discriminate.
Qed.

Lemma transf_function_well_typed:
  wt_function f = true.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb. auto. intros; discriminate.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= Ptrofs.max_unsigned.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. omega.
  intros; discriminate.
Qed.

Remark bound_stack_data_stacksize:
  f.(Linear.fn_stacksize) <= b.(bound_stack_data).
Proof.
  unfold b, function_bounds, bound_stack_data. apply Zmax1.
Qed.

(** * Memory assertions used to describe the contents of stack frames *)

Local Opaque Z.add Z.mul Z.divide.

(** Accessing the stack frame using [load_stack] and [store_stack]. *)

Lemma contains_get_stack:
  forall spec m ty sp ofs,
  m |= contains (chunk_of_type ty) sp ofs spec ->
  exists v, load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = Some v /\ spec v.
Proof.
  intros. unfold load_stack. 
  replace (Val.offset_ptr (Vptr sp Ptrofs.zero) (Ptrofs.repr ofs)) with (Vptr sp (Ptrofs.repr ofs)).
  eapply loadv_rule; eauto.
  simpl. rewrite Ptrofs.add_zero_l; auto.
Qed.

Lemma hasvalue_get_stack:
  forall ty m sp ofs v,
  m |= hasvalue (chunk_of_type ty) sp ofs v ->
  load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = Some v.
Proof.
  intros. exploit contains_get_stack; eauto. intros (v' & A & B). congruence.
Qed.

Lemma contains_set_stack:
  forall (spec: val -> Prop) v spec1 m ty sp ofs P,
  m |= contains (chunk_of_type ty) sp ofs spec1 ** P ->
  spec (Val.load_result (chunk_of_type ty) v) ->
  exists m',
      store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) v = Some m'
  /\ m' |= contains (chunk_of_type ty) sp ofs spec ** P.
Proof.
  intros. unfold store_stack. 
  replace (Val.offset_ptr (Vptr sp Ptrofs.zero) (Ptrofs.repr ofs)) with (Vptr sp (Ptrofs.repr ofs)).
  eapply storev_rule; eauto.
  simpl. rewrite Ptrofs.add_zero_l; auto.
Qed.

(** [contains_locations j sp pos bound sl ls] is a separation logic assertion
  that holds if the memory area at block [sp], offset [pos], size [4 * bound],
  reflects the values of the stack locations of kind [sl] given by the
  location map [ls], up to the memory injection [j].

  Two such [contains_locations] assertions will be used later, one to
  reason about the values of [Local] slots, the other about the values of
  [Outgoing] slots. *)

Program Definition contains_locations (j: meminj) (sp: block) (pos bound: Z) (sl: slot) (ls: locset) : massert := {|
  m_pred := fun m =>
    (8 | pos) /\ 0 <= pos /\ pos + 4 * bound <= Ptrofs.modulus /\
    Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable /\
    forall ofs ty, 0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
    exists v, Mem.load (chunk_of_type ty) m sp (pos + 4 * ofs) = Some v
           /\ Val.inject j (ls (S sl ofs ty)) v;
  m_footprint := fun b ofs =>
    b = sp /\ pos <= ofs < pos + 4 * bound
  ;
  m_invar_weak := false
|}.
Next Obligation.
  intuition auto. 
- red; intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- exploit H4; eauto. intros (v & A & B). exists v; split; auto.
  eapply Mem.load_unchanged_on; eauto.
  simpl; intros. rewrite size_type_chunk, typesize_typesize in H8. 
  split; auto. omega.
Qed.
Next Obligation.
  eauto with mem.
Qed.

Remark valid_access_location:
  forall m sp pos bound ofs ty p,
  (8 | pos) ->
  Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Mem.valid_access m (chunk_of_type ty) sp (pos + 4 * ofs) p.
Proof.
  intros; split.
- red; intros. apply Mem.perm_implies with Freeable; auto with mem. 
  apply H0. rewrite size_type_chunk, typesize_typesize in H4. omega.
- rewrite align_type_chunk. apply Z.divide_add_r. 
  apply Zdivide_trans with 8; auto.
  exists (8 / (4 * typealign ty)); destruct ty; reflexivity.
  apply Z.mul_divide_mono_l. auto.
Qed.

Lemma get_location:
  forall m j sp pos bound sl ls ofs ty,
  m |= contains_locations j sp pos bound sl ls ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (pos + 4 * ofs)) = Some v
  /\ Val.inject j (ls (S sl ofs ty)) v.
Proof.
  intros. destruct H as (D & E & F & G & H).
  exploit H; eauto. intros (v & U & V). exists v; split; auto.
  unfold load_stack; simpl. rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; auto.
  unfold Ptrofs.max_unsigned. generalize (typesize_pos ty). omega.
Qed.

Lemma set_location:
  forall m j sp pos bound sl ls P ofs ty v v',
  m |= contains_locations j sp pos bound sl ls ** P ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (pos + 4 * ofs)) v' = Some m'
  /\ m' |= contains_locations j sp pos bound sl (Locmap.set (S sl ofs ty) v ls) ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F & G & H).
  edestruct Mem.valid_access_store as [m' STORE]. 
  eapply valid_access_location; eauto. 
  assert (PERM: Mem.range_perm m' sp pos (pos + 4 * bound) Cur Freeable).
  { red; intros; eauto with mem. }
  exists m'; split.
- unfold store_stack; simpl. rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; eauto.
  unfold Ptrofs.max_unsigned. generalize (typesize_pos ty). omega.
- simpl. intuition auto.
+ unfold Locmap.set. 
  destruct (Loc.eq (S sl ofs ty) (S sl ofs0 ty0)); [|destruct (Loc.diff_dec (S sl ofs ty) (S sl ofs0 ty0))].
* (* same location *)
  inv e. rename ofs0 into ofs. rename ty0 into ty.
  exists (Val.load_result (chunk_of_type ty) v'); split.
  eapply Mem.load_store_similar_2; eauto. omega. 
  apply Val.load_result_inject; auto.
* (* different locations *)
  exploit H; eauto. intros (v0 & X & Y). exists v0; split; auto.
  rewrite <- X; eapply Mem.load_store_other; eauto.
  destruct d. congruence. right. rewrite ! size_type_chunk, ! typesize_typesize. omega.
* (* overlapping locations *)
  destruct (Mem.valid_access_load m' (chunk_of_type ty0) sp (pos + 4 * ofs0)) as [v'' LOAD].
  apply Mem.valid_access_implies with Writable; auto with mem. 
  eapply valid_access_location; eauto.
  exists v''; auto.
+ apply (m_invar P) with m; auto. 
  cut (Mem.strong_unchanged_on (m_footprint P) m m').
  {
    destruct (m_invar_weak P); auto using Mem.strong_unchanged_on_weak.
  }
  eapply Mem.store_strong_unchanged_on; eauto.
  intros i; rewrite size_type_chunk, typesize_typesize. intros; red; intros.
  eelim C; eauto. simpl. split; auto. omega.
Qed.

Lemma initial_locations:
  forall j sp pos bound P sl ls m,
  m |= range sp pos (pos + 4 * bound) ** P ->
  (8 | pos) ->
  (forall ofs ty, ls (S sl ofs ty) = Vundef) ->
  m |= contains_locations j sp pos bound sl ls ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F). split.
- simpl; intuition auto. red; intros; eauto with mem. 
  destruct (Mem.valid_access_load m (chunk_of_type ty) sp (pos + 4 * ofs)) as [v LOAD].
  eapply valid_access_location; eauto.
  red; intros; eauto with mem.
  exists v; split; auto. rewrite H1; auto.
- split; assumption.
Qed.

Lemma contains_locations_exten:
  forall ls ls' j sp pos bound sl,
  (forall ofs ty, ls' (S sl ofs ty) = ls (S sl ofs ty)) ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j sp pos bound sl ls').
Proof.
  intros; split; simpl; intros; auto.
  intuition auto. rewrite H. eauto.
Qed.

Lemma contains_locations_incr:
  forall j j' sp pos bound sl ls,
  inject_incr j j' ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j' sp pos bound sl ls).
Proof.
  intros; split; simpl; intros; auto.
  intuition auto. exploit H5; eauto. intros (v & A & B). exists v; eauto.
Qed.

(** [contains_callee_saves j sp pos rl ls] is a memory assertion that holds
  if block [sp], starting at offset [pos], contains the values of the
  callee-save registers [rl] as given by the location map [ls],
  up to the memory injection [j].  The memory layout of the registers in [rl]
  is the same as that implemented by [save_callee_save_rec]. *)

Fixpoint contains_callee_saves (j: meminj) (sp: block) (pos: Z) (rl: list mreg) (ls: locset) : massert :=
  match rl with
  | nil => pure True
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let pos1 := align pos sz in
      contains (chunk_of_type ty) sp pos1 (fun v => Val.inject j (ls (R r)) v)
      ** contains_callee_saves j sp (pos1 + sz) rl ls
  end.

Lemma contains_callee_saves_invar_weak rl :
  forall j sp pos ls,
    m_invar_weak (contains_callee_saves j sp pos rl ls) = false.
Proof.
  induction rl; simpl; auto.
Qed.

(** Record [massert_eqv] and [massert_imp] as relations so that they can be used by rewriting tactics. *)
Local Add Relation massert massert_imp
  reflexivity proved by massert_imp_refl
  transitivity proved by massert_imp_trans
as massert_imp_prel.

Local Add Relation massert massert_eqv
  reflexivity proved by massert_eqv_refl
  symmetry proved by massert_eqv_sym
  transitivity proved by massert_eqv_trans
as massert_eqv_prel.

Lemma contains_callee_saves_incr:
  forall j j' sp ls,
  inject_incr j j' ->
  forall rl pos,
  massert_imp (contains_callee_saves j sp pos rl ls)
              (contains_callee_saves j' sp pos rl ls).
Proof.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_1; auto. apply contains_imp. eauto.
Qed.

Lemma contains_callee_saves_exten:
  forall j sp ls ls' rl pos,
  (forall r, In r rl -> ls' (R r) = ls (R r)) ->
  massert_eqv (contains_callee_saves j sp pos rl ls)
              (contains_callee_saves j sp pos rl ls').
Proof.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_2; auto. rewrite H by auto. reflexivity.
Qed.

(** Separation logic assertions describing the stack frame at [sp].
  It must contain:
  - the values of the [Local] stack slots of [ls], as per [contains_locations]
  - the values of the [Outgoing] stack slots of [ls], as per [contains_locations]
  - the [parent] pointer representing the back link to the caller's frame
  - the [retaddr] pointer representing the saved return address
  - the initial values of the used callee-save registers as given by [ls0],
    as per [contains_callee_saves].

In addition, we use a nonseparating conjunction to record the fact that
we have full access rights on the stack frame, except the part that
represents the Linear stack data. *)

Definition frame_contents_1 (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) :=
    contains_locations j sp fe.(fe_ofs_local) b.(bound_local) Local ls
 ** contains_locations j sp fe_ofs_arg b.(bound_outgoing) Outgoing ls
 ** hasvalue Mptr sp fe.(fe_ofs_link) parent
 ** hasvalue Mptr sp fe.(fe_ofs_retaddr) retaddr
 ** contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0.

Definition frame_contents (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) :=
  mconj (frame_contents_1 j sp ls ls0 parent retaddr)
        (range sp 0 fe.(fe_stack_data) **
         range sp (fe.(fe_stack_data) + b.(bound_stack_data)) fe.(fe_size)).

Lemma frame_contents_invar_weak j sp ls ls0 parent retaddr:
  m_invar_weak (frame_contents j sp ls ls0 parent retaddr) = false.
Proof.
  simpl.
  rewrite contains_callee_saves_invar_weak.
  reflexivity.
Qed.

(** Accessing components of the frame. *)

Lemma frame_get_local:
  forall ofs ty j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_local fe ofs)) = Some v
  /\ Val.inject j (ls (S Local ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_proj1 in H.
  eapply get_location; eauto. 
Qed.

Lemma frame_get_outgoing:
  forall ofs ty j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_arg ofs)) = Some v
  /\ Val.inject j (ls (S Outgoing ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick2 in H.
  eapply get_location; eauto. 
Qed.

Lemma frame_get_parent:
  forall j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  load_stack m (Vptr sp Ptrofs.zero) Tptr (Ptrofs.repr fe.(fe_ofs_link)) = Some parent.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick3 in H. rewrite <- chunk_of_Tptr in H.
  eapply hasvalue_get_stack; eauto.
Qed.

Lemma frame_get_retaddr:
  forall j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  load_stack m (Vptr sp Ptrofs.zero) Tptr (Ptrofs.repr fe.(fe_ofs_retaddr)) = Some retaddr.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick4 in H. rewrite <- chunk_of_Tptr in H.
  eapply hasvalue_get_stack; eauto.
Qed.

(** Assigning a [Local] or [Outgoing] stack slot. *)

Lemma frame_set_local:
  forall ofs ty v v' j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_local fe ofs)) v' = Some m'
  /\ m' |= frame_contents j sp (Locmap.set (S Local ofs ty) v ls) ls0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1. 
  rewrite ! sep_assoc; intros SEP.
  unfold slot_valid in H1; InvBooleans. simpl in H0. 
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  {  intros. unfold store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc; exact B.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

Lemma frame_set_outgoing:
  forall ofs ty v v' j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_arg ofs)) v' = Some m'
  /\ m' |= frame_contents j sp (Locmap.set (S Outgoing ofs ty) v ls) ls0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1.
  rewrite ! sep_assoc, sep_swap. intros SEP. 
  unfold slot_valid in H1; InvBooleans. simpl in H0. 
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  {  intros. unfold store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc, sep_swap; eauto.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

(** Invariance by change of location maps. *)

Lemma frame_contents_exten:
  forall ls ls0 ls' ls0' j sp parent retaddr P m,
  (forall sl ofs ty, ls' (S sl ofs ty) = ls (S sl ofs ty)) ->
  (forall r, In r b.(used_callee_save) -> ls0' (R r) = ls0 (R r)) ->
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp ls' ls0' parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- ! (contains_locations_exten ls ls') by auto.
  erewrite  <- contains_callee_saves_exten by eauto.
  assumption.
Qed.

(** Invariance by assignment to registers. *)

Corollary frame_set_reg:
  forall r v j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.set (R r) v ls) ls0 parent retaddr ** P.
Proof.
  intros. apply frame_contents_exten with ls ls0; auto.
Qed.

Corollary frame_undef_regs:
  forall j sp ls ls0 parent retaddr m P rl,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (LTL.undef_regs rl ls) ls0 parent retaddr ** P.
Proof.
Local Opaque sepconj.
  induction rl; simpl; intros.
- auto.
- apply frame_set_reg; auto. 
Qed.

Corollary frame_set_regpair:
  forall j sp ls0 parent retaddr m P p v ls,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.setpair p v ls) ls0 parent retaddr ** P.
Proof.
  intros. destruct p; simpl.
  apply frame_set_reg; auto.
  apply frame_set_reg; apply frame_set_reg; auto.
Qed.

Corollary frame_set_res:
  forall j sp ls0 parent retaddr m P res v ls,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.setres res v ls) ls0 parent retaddr ** P.
Proof.
  induction res; simpl; intros.
- apply frame_set_reg; auto.
- auto.
- eauto.
Qed.

(** Invariance by change of memory injection. *)

Lemma frame_contents_incr:
  forall j sp ls ls0 parent retaddr m P j',
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  inject_incr j j' ->
  m |= frame_contents j' sp ls ls0 parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- (contains_locations_incr j j') by auto.
  rewrite <- (contains_locations_incr j j') by auto.
  erewrite  <- contains_callee_saves_incr by eauto.
  assumption.
Qed.

(** * Agreement between location sets and Mach states *)

(** Agreement with Mach register states *)

Definition agree_regs (j: meminj) (ls: locset) (rs: regset) : Prop :=
  forall r, Val.inject j (ls (R r)) (rs r).

(** Agreement over locations *)

Record agree_locs (ls ls0: locset) : Prop :=
  mk_agree_locs {

    (** Unused registers have the same value as in the caller *)
    agree_unused_reg:
       forall r, ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);

    (** Incoming stack slots have the same value as the
        corresponding Outgoing stack slots in the caller *)
    agree_incoming:
       forall ofs ty,
       In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters f.(Linear.fn_sig))) ->
       ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty)
}.

(** Auxiliary predicate used at call points *)

Definition agree_callee_save (ls ls0: locset) : Prop :=
  forall l,
  match l with
  | R r => is_callee_save r = true
  | S _ _ _ => True
  end ->
  ls l = ls0 l.

(** ** Properties of [agree_regs]. *)

(** Values of registers *)

Lemma agree_reg:
  forall j ls rs r,
  agree_regs j ls rs -> Val.inject j (ls (R r)) (rs r).
Proof.
  intros. auto.
Qed.

Lemma agree_reglist:
  forall j ls rs rl,
  agree_regs j ls rs -> Val.inject_list j (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  auto. constructor; auto using agree_reg.
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignments of machine registers. *)

Lemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros.
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0.
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_set_pair:
  forall j p v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setpair p v ls) (set_pair p v' rs).
Proof.
  intros. destruct p; simpl.
- apply agree_regs_set_reg; auto.
- apply agree_regs_set_reg. apply agree_regs_set_reg; auto. 
  apply Val.hiword_inject; auto. apply Val.loword_inject; auto.
Qed.

Lemma agree_regs_set_res:
  forall j res v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setres res v ls) (set_res res v' rs).
Proof.
  induction res; simpl; intros.
- apply agree_regs_set_reg; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_inject; auto.
  apply Val.loword_inject; auto.
Qed.

Lemma agree_regs_exten:
  forall j ls rs ls' rs',
  agree_regs j ls rs ->
  (forall r, ls' (R r) = Vundef \/ ls' (R r) = ls (R r) /\ rs' r = rs r) ->
  agree_regs j ls' rs'.
Proof.
  intros; red; intros.
  destruct (H0 r) as [A | [A B]].
  rewrite A. constructor.
  rewrite A; rewrite B; auto.
Qed.

Lemma agree_regs_undef_regs:
  forall j rl ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_regs rl ls) (Mach.undef_regs rl rs).
Proof.
  induction rl; simpl; intros.
  auto.
  apply agree_regs_set_reg; auto.
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall j ls rs sl ofs ty v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (S sl ofs ty) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. auto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
Proof.
  intros; red; intros; eauto with stacking.
Qed.

(** Preservation at function entry. *)

Lemma agree_regs_call_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (call_regs ls) rs.
Proof.
  intros.
  unfold call_regs; intros; red; intros; auto.
Qed.

(** ** Properties of [agree_locs] *)

(** Preservation under assignment of machine register. *)

Lemma agree_locs_set_reg:
  forall ls ls0 r v,
  agree_locs ls ls0 ->
  mreg_within_bounds b r ->
  agree_locs (Locmap.set (R r) v ls) ls0.
Proof.
  intros. inv H; constructor; auto; intros.
  rewrite Locmap.gso. auto. red. intuition congruence.
Qed.

Lemma caller_save_reg_within_bounds:
  forall r,
  is_callee_save r = false -> mreg_within_bounds b r.
Proof.
  intros; red; intros. congruence.
Qed.

Lemma agree_locs_set_pair:
  forall ls0 p v ls,
  agree_locs ls ls0 ->
  forall_rpair (fun r => is_callee_save r = false) p ->
  agree_locs (Locmap.setpair p v ls) ls0.
Proof.
  intros.
  destruct p; simpl in *.
  apply agree_locs_set_reg; auto. apply caller_save_reg_within_bounds; auto.
  destruct H0.
  apply agree_locs_set_reg; auto. apply agree_locs_set_reg; auto.
  apply caller_save_reg_within_bounds; auto. apply caller_save_reg_within_bounds; auto. 
Qed.

Lemma agree_locs_set_res:
  forall ls0 res v ls,
  agree_locs ls ls0 ->
  (forall r, In r (params_of_builtin_res res) -> mreg_within_bounds b r) ->
  agree_locs (Locmap.setres res v ls) ls0.
Proof.
  induction res; simpl; intros.
- eapply agree_locs_set_reg; eauto.
- auto.
- apply IHres2; auto using in_or_app.
Qed.

Lemma agree_locs_undef_regs:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  (forall r, In r regs -> mreg_within_bounds b r) ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  induction regs; simpl; intros.
  auto.
  apply agree_locs_set_reg; auto.
Qed.

Lemma agree_locs_undef_locs_1:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  (forall r, In r regs -> is_callee_save r = false) ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  intros. eapply agree_locs_undef_regs; eauto.
  intros. apply caller_save_reg_within_bounds. auto.
Qed.

Lemma agree_locs_undef_locs:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  existsb is_callee_save regs = false ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  intros. eapply agree_locs_undef_locs_1; eauto. 
  intros. destruct (is_callee_save r) eqn:CS; auto. 
  assert (existsb is_callee_save regs = true).
  { apply existsb_exists. exists r; auto. }
  congruence.
Qed.

(** Preservation by assignment to local slot *)

Lemma agree_locs_set_slot:
  forall ls ls0 sl ofs ty v,
  agree_locs ls ls0 ->
  slot_writable sl = true ->
  agree_locs (Locmap.set (S sl ofs ty) v ls) ls0.
Proof.
  intros. destruct H; constructor; intros.
- rewrite Locmap.gso; auto. red; auto.
- rewrite Locmap.gso; auto. red. left. destruct sl; discriminate.
Qed.

(** Preservation at return points (when [ls] is changed but not [ls0]). *)

Lemma agree_locs_return:
  forall ls ls0 ls',
  agree_locs ls ls0 ->
  agree_callee_save ls' ls ->
  agree_locs ls' ls0.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
- rewrite H0; auto. unfold mreg_within_bounds in H. tauto.
- rewrite H0; auto.
Qed.

(** Preservation at tailcalls (when [ls0] is changed but not [ls]). *)

Lemma agree_locs_tailcall:
  forall ls ls0 ls0',
  agree_locs ls ls0 ->
  agree_callee_save ls0 ls0' ->
  agree_locs ls ls0'.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
- rewrite <- H0; auto. unfold mreg_within_bounds in H. tauto.
- rewrite <- H0; auto.
Qed.

(** ** Properties of [agree_callee_save]. *)

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto. rewrite H; auto.
Qed.

Lemma agree_callee_save_set_result:
  forall sg v ls1 ls2,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.setpair (loc_result sg) v ls1) ls2.
Proof.
  intros; red; intros. rewrite Locmap.gpo. apply H; auto. 
  assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
  { intros. destruct l; auto. simpl; congruence. }
  generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto.
Qed.

(** ** Properties of destroyed registers. *)

Definition no_callee_saves (l: list mreg) : Prop :=
  existsb is_callee_save l = false.

Remark destroyed_by_op_caller_save:
  forall op, no_callee_saves (destroyed_by_op op).
Proof.
  unfold no_callee_saves; destruct op; reflexivity.
Qed.

Remark destroyed_by_load_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_load chunk addr).
Proof.
  unfold no_callee_saves; destruct chunk; reflexivity.
Qed.

Remark destroyed_by_store_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_store chunk addr).
Proof.
Local Transparent destroyed_by_store.
  unfold no_callee_saves, destroyed_by_store; intros; destruct chunk; try reflexivity; destruct Archi.ptr64; reflexivity.
Qed.

Remark destroyed_by_cond_caller_save:
  forall cond, no_callee_saves (destroyed_by_cond cond).
Proof.
  unfold no_callee_saves; destruct cond; reflexivity.
Qed.

Remark destroyed_by_jumptable_caller_save:
  no_callee_saves destroyed_by_jumptable.
Proof.
  red; reflexivity.
Qed.

Remark destroyed_by_setstack_caller_save:
  forall ty, no_callee_saves (destroyed_by_setstack ty).
Proof.
  unfold no_callee_saves; destruct ty; reflexivity.
Qed.

Remark destroyed_at_function_entry_caller_save:
  no_callee_saves destroyed_at_function_entry.
Proof.
  red; reflexivity.
Qed.

Hint Resolve destroyed_by_op_caller_save destroyed_by_load_caller_save
    destroyed_by_store_caller_save
    destroyed_by_cond_caller_save destroyed_by_jumptable_caller_save
    destroyed_at_function_entry_caller_save: stacking.

Remark destroyed_by_setstack_function_entry:
  forall ty, incl (destroyed_by_setstack ty) destroyed_at_function_entry.
Proof.
Local Transparent destroyed_by_setstack destroyed_at_function_entry.
  unfold incl; destruct ty; simpl; tauto.
Qed.

Remark transl_destroyed_by_op:
  forall op e, destroyed_by_op (transl_op e op) = destroyed_by_op op.
Proof.
  intros; destruct op; reflexivity.
Qed.

Remark transl_destroyed_by_load:
  forall chunk addr e, destroyed_by_load chunk (transl_addr e addr) = destroyed_by_load chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

Remark transl_destroyed_by_store:
  forall chunk addr e, destroyed_by_store chunk (transl_addr e addr) = destroyed_by_store chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Section SAVE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls: locset.

Hypothesis ls_temp_undef:
  forall ty r, In r (destroyed_by_setstack ty) -> ls (R r) = Vundef.

Hypothesis wt_ls: forall r, Val.has_type (ls (R r)) (mreg_type r).

Lemma save_callee_save_rec_correct:
  forall k l pos rs m P,
  (forall r, In r l -> is_callee_save r = true) ->
  m |= range sp pos (size_callee_save_area_rec l pos) ** P ->
  agree_regs j ls rs ->
  exists rs', exists m',
     star step tge
        (State cs fb (Vptr sp Ptrofs.zero) (save_callee_save_rec l pos k) rs m)
     E0 (State cs fb (Vptr sp Ptrofs.zero) k rs' m')
  /\ m' |= contains_callee_saves j sp pos l ls ** P
  /\ (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p)
  /\ agree_regs j ls rs'
  /\ (forall b, Mem.valid_block m b -> Mem.valid_block m' b)
  /\ Mem.unchanged_on (fun b o => b <> sp) m m'.
Proof.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl; intros until P; intros CS SEP AG.
- exists rs, m. 
  split. apply star_refl.
  split. rewrite sep_pure; split; auto. eapply sep_drop; eauto.
  split. auto. 
  split. auto.
  split. auto. apply Mem.unchanged_on_refl. 
- set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (pos1 := align pos sz) in *.
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (SZREC: pos1 + sz <= size_callee_save_area_rec l (pos1 + sz)) by (apply size_callee_save_area_rec_incr).
  assert (POS1: pos <= pos1) by (apply align_le; auto).
  assert (AL1: (align_chunk (chunk_of_type ty) | pos1)).
  { unfold pos1. apply Zdivide_trans with sz.
    unfold sz; rewrite <- size_type_chunk. apply align_size_chunk_divides.
    apply align_divides; auto. }
  apply range_drop_left with (mid := pos1) in SEP; [ | omega ].
  apply range_split with (mid := pos1 + sz) in SEP; [ | omega ].
  unfold sz at 1 in SEP. rewrite <- size_type_chunk in SEP.
  apply range_contains in SEP; auto.
  exploit (contains_set_stack (fun v' => Val.inject j (ls (R r)) v') (rs r)).
  eexact SEP.
  apply load_result_inject; auto. apply wt_ls. 
  clear SEP; intros (m1 & STORE & SEP).
  set (rs1 := undef_regs (destroyed_by_setstack ty) rs).
  assert (AG1: agree_regs j ls rs1).
  { red; intros. unfold rs1. destruct (In_dec mreg_eq r0 (destroyed_by_setstack ty)).
    erewrite ls_temp_undef by eauto. auto.
    rewrite undef_regs_other by auto. apply AG. }
  rewrite sep_swap in SEP. 
  exploit (IHl (pos1 + sz) rs1 m1); eauto.
  intros (rs2 & m2 & A & B & C & D & VALID & UNCH).
  exists rs2, m2. 
  split. eapply star_left; eauto. constructor. exact STORE. auto. traceEq.
  split. rewrite sep_assoc, sep_swap. exact B.
  split. intros. apply C. unfold store_stack in STORE; simpl in STORE. eapply Mem.perm_store_1; eauto.
  split. auto.
  split. unfold store_stack, Val.offset_ptr, Mem.storev in STORE.
  eauto with mem.
  unfold store_stack, Val.offset_ptr, Mem.storev in STORE.
  eapply Mem.unchanged_on_trans. 2: apply UNCH.
  eapply Mem.store_unchanged_on; eauto.
Qed.

End SAVE_CALLEE_SAVE.

Remark LTL_undef_regs_same:
  forall r rl ls, In r rl -> LTL.undef_regs rl ls (R r) = Vundef.
Proof.
  induction rl; simpl; intros. contradiction.
  unfold Locmap.set. destruct (Loc.eq (R a) (R r)). auto.
  destruct (Loc.diff_dec (R a) (R r)); auto.
  apply IHrl. intuition congruence.
Qed.

Remark LTL_undef_regs_others:
  forall r rl ls, ~In r rl -> LTL.undef_regs rl ls (R r) = ls (R r).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. intuition. red. intuition.
Qed.

Remark LTL_undef_regs_slot:
  forall sl ofs ty rl ls, LTL.undef_regs rl ls (S sl ofs ty) = ls (S sl ofs ty).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. red; auto.
Qed.

Remark undef_regs_type:
  forall ty l rl ls,
  Val.has_type (ls l) ty -> Val.has_type (LTL.undef_regs rl ls l) ty.
Proof.
  induction rl; simpl; intros.
- auto.
- unfold Locmap.set. destruct (Loc.eq (R a) l). red; auto.
  destruct (Loc.diff_dec (R a) l); auto. red; auto.
Qed.

Lemma save_callee_save_correct:
  forall j ls ls0 rs sp cs fb k m P,
  m |= range sp fe.(fe_ofs_callee_save) (size_callee_save_area b fe.(fe_ofs_callee_save)) ** P ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  agree_callee_save ls ls0 ->
  agree_regs j ls rs ->
  let ls1 := LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) in
  let rs1 := undef_regs destroyed_at_function_entry rs in
  exists rs', exists m',
     star step tge
        (State cs fb (Vptr sp Ptrofs.zero) (save_callee_save fe k) rs1 m)
     E0 (State cs fb (Vptr sp Ptrofs.zero) k rs' m')
  /\ m' |= contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0 ** P
  /\ (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p)
  /\ agree_regs j ls1 rs'
  /\ (forall b, Mem.valid_block m b -> Mem.valid_block m' b )
  /\ Mem.unchanged_on (fun b o => b <> sp) m m'.
Proof.
  intros until P; intros SEP TY AGCS AG; intros ls1 rs1.
  exploit (save_callee_save_rec_correct j cs fb sp ls1).
- intros. unfold ls1. apply LTL_undef_regs_same. eapply destroyed_by_setstack_function_entry; eauto.
- intros. unfold ls1. apply undef_regs_type. apply TY. 
- exact b.(used_callee_save_prop).
- eexact SEP.
- instantiate (1 := rs1). apply agree_regs_undef_regs. apply agree_regs_call_regs. auto.
- clear SEP. intros (rs' & m' & EXEC & SEP & PERMS & AG' & VALID & UNCH).
  exists rs', m'. 
  split. eexact EXEC.
  split. rewrite (contains_callee_saves_exten j sp ls0 ls1). exact SEP.
  intros. apply b.(used_callee_save_prop) in H.
    unfold ls1. rewrite LTL_undef_regs_others. unfold call_regs. 
    apply AGCS; auto.
    red; intros.
    assert (existsb is_callee_save destroyed_at_function_entry = false)
       by  (apply destroyed_at_function_entry_caller_save).
    assert (existsb is_callee_save destroyed_at_function_entry = true).
    { apply existsb_exists. exists r; auto. }
    congruence.
  split. exact PERMS.
  split. exact AG'.
  split. exact VALID.
  exact UNCH.
Qed.

(** As a corollary of the previous lemmas, we obtain the following
  correctness theorem for the execution of a function prologue
  (allocation of the frame + saving of the link and return address +
  saving of the used callee-save registers). *)

Lemma function_prologue_correct:
  forall j ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k P,
  agree_regs j ls rs ->
  agree_callee_save ls ls0 ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) ->
  rs1 = undef_regs destroyed_at_function_entry rs ->
  Mem.alloc m1 0 f.(Linear.fn_stacksize) = (m2, sp) ->
  Val.has_type parent Tptr -> Val.has_type ra Tptr ->
  m1' |= minjection j m1 ** globalenv_inject ge j ** P ->
  exists j', exists rs', exists m2', exists sp', exists m3', exists m4', exists m5',
     Mem.alloc m1' 0 tf.(fn_stacksize) = (m2', sp')
  /\ store_stack m2' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_retaddr_ofs) ra = Some m4'
  /\ star step tge
         (State cs fb (Vptr sp' Ptrofs.zero) (save_callee_save fe k) rs1 m4')
      E0 (State cs fb (Vptr sp' Ptrofs.zero) k rs' m5')
  /\ agree_regs j' ls1 rs'
  /\ agree_locs ls1 ls0
  /\ m5' |= frame_contents j' sp' ls1 ls0 parent ra ** minjection j' m2 ** globalenv_inject ge j' ** P
  /\ j' sp = Some(sp', fe.(fe_stack_data))
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m1'
  /\ (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b)
  /\ (forall b, Mem.valid_block m1' b -> Mem.valid_block m5' b)
  /\ (forall b o k p, Mem.perm m1' b o k p -> Mem.perm m5' b o k p)
  /\ Mem.unchanged_on (fun b o => b <> sp') m1' m5'.
Proof.
  intros until P; intros AGREGS AGCS WTREGS LS1 RS1 ALLOC TYPAR TYRA SEP.
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
  (* Stack layout info *)
Local Opaque b fe.
  generalize (frame_env_range b) (frame_env_aligned b). replace (make_env b) with fe by auto. simpl. 
  intros LAYOUT1 LAYOUT2.
  (* Allocation step *)
  destruct (Mem.alloc m1' 0 (fe_size fe)) as [m2' sp'] eqn:ALLOC'.
  exploit alloc_parallel_rule_2.
  eexact SEP. eexact ALLOC. eexact ALLOC'. 
  instantiate (1 := fe_stack_data fe). tauto.
  reflexivity. 
  instantiate (1 := fe_stack_data fe + bound_stack_data b). rewrite Z.max_comm. reflexivity.
  generalize (bound_stack_data_pos b) size_no_overflow; omega.
  tauto.
  tauto.
  clear SEP. intros (j' & SEP & INCR & SAME & INJSEP).
  (* Remember the freeable permissions using a mconj *)
  assert (SEPCONJ:
    m2' |= mconj (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
                 (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
           ** minjection j' m2 ** globalenv_inject ge j' ** P).
  { apply mconj_intro; rewrite sep_assoc; assumption. }
  (* Dividing up the frame *)
  apply (frame_env_separated b) in SEP. replace (make_env b) with fe in SEP by auto.
  (* Store of parent *)
  rewrite sep_swap3 in SEP.
  apply (range_contains Mptr) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = parent) parent (fun _ => True) m2' Tptr).
  rewrite chunk_of_Tptr; eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m3' & STORE_PARENT & SEP).
  rewrite sep_swap3 in SEP.
  (* Store of return address *)
  rewrite sep_swap4 in SEP.
  apply (range_contains Mptr) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = ra) ra (fun _ => True) m3' Tptr).
  rewrite chunk_of_Tptr; eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m4' & STORE_RETADDR & SEP).
  rewrite sep_swap4 in SEP.
  (* Saving callee-save registers *)
  rewrite sep_swap5 in SEP.
  exploit (save_callee_save_correct j' ls ls0 rs); eauto.
  apply agree_regs_inject_incr with j; auto.
  replace (LTL.undef_regs destroyed_at_function_entry (call_regs ls)) with ls1 by auto.
  replace (undef_regs destroyed_at_function_entry rs) with rs1 by auto.
  clear SEP; intros (rs2 & m5' & SAVE_CS & SEP & PERMS & AGREGS' & VALID & UNCH).
  rewrite sep_swap5 in SEP.
  (* Materializing the Local and Outgoing locations *)
  exploit (initial_locations j'). eexact SEP. tauto. 
  instantiate (1 := Local). instantiate (1 := ls1). 
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  exploit (initial_locations j'). eexact SEP. tauto. 
  instantiate (1 := Outgoing). instantiate (1 := ls1). 
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  (* Now we frame this *)
  assert (SEPFINAL: m5' |= frame_contents j' sp' ls1 ls0 parent ra ** minjection j' m2 ** globalenv_inject ge j' ** P).
  { eapply frame_mconj. eexact SEPCONJ.
    rewrite chunk_of_Tptr in SEP.  
    unfold frame_contents_1; rewrite ! sep_assoc. exact SEP.
    assert (forall ofs k p, Mem.perm m2' sp' ofs k p -> Mem.perm m5' sp' ofs k p).
    { intros. apply PERMS. 
      unfold store_stack in STORE_PARENT, STORE_RETADDR.
      simpl in STORE_PARENT, STORE_RETADDR.
      eauto using Mem.perm_store_1. }
    eapply sep_preserved. eapply sep_proj1. eapply mconj_proj2. eexact SEPCONJ.
    intros; apply range_preserved with m2'; auto.
    intros; apply range_preserved with m2'; auto.
  }
  clear SEP SEPCONJ.
(* Conclusions *)
  exists j', rs2, m2', sp', m3', m4', m5'.
  split. auto.
  split. exact STORE_PARENT.
  split. exact STORE_RETADDR.
  split. eexact SAVE_CS.
  split. exact AGREGS'.
  split. rewrite LS1. apply agree_locs_undef_locs; [|reflexivity].
    constructor; intros. unfold call_regs. apply AGCS. 
    unfold mreg_within_bounds in H; tauto.
    unfold call_regs. apply AGCS. auto.
  split. exact SEPFINAL.
  split. exact SAME.
  split. exact INCR.
  split. exact INJSEP.
  split. eauto with mem.
  split. unfold store_stack, Val.offset_ptr, Mem.storev in * ; eauto with mem.
  split.
  - intros.
    eapply PERMS.
    unfold store_stack, Val.offset_ptr, Mem.storev in * ; eauto with mem.
  - eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on. eauto.
    eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on.
    unfold store_stack in STORE_PARENT. simpl in STORE_PARENT. eauto.
    intuition.
    eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on.
    unfold store_stack in STORE_RETADDR. simpl in STORE_RETADDR. eauto.
    intuition.
    exact UNCH.
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls0: locset.
Variable m: mem.

Definition agree_unused (ls0: locset) (rs: regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> Val.inject j (ls0 (R r)) (rs r).

Lemma restore_callee_save_rec_correct:
  forall l ofs rs k,
  m |= contains_callee_saves j sp ofs l ls0 ->
  agree_unused ls0 rs ->
  (forall r, In r l -> mreg_within_bounds b r) ->
  exists rs',
    star step tge
      (State cs fb (Vptr sp Ptrofs.zero) (restore_callee_save_rec l ofs k) rs m)
   E0 (State cs fb (Vptr sp Ptrofs.zero) k rs' m)
  /\ (forall r, In r l -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused ls0 rs'.
Proof.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl; intros.
- (* base case *)
  exists rs. intuition auto. apply star_refl.
- (* inductive case *)
  set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (ofs1 := align ofs sz).
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (OFSLE: ofs <= ofs1) by (apply align_le; auto).
  assert (BOUND: mreg_within_bounds b r) by eauto.
  exploit contains_get_stack.
    eapply sep_proj1; eassumption.
  intros (v & LOAD & SPEC).
  exploit (IHl (ofs1 + sz) (rs#r <- v)).
    eapply sep_proj2; eassumption.
    red; intros. rewrite Regmap.gso. auto. intuition congruence.
    eauto.
  intros (rs' & A & B & C & D).
  exists rs'.
  split. eapply star_step; eauto. 
    econstructor. exact LOAD. traceEq.
  split. intros.
    destruct (In_dec mreg_eq r0 l). auto. 
    assert (r = r0) by tauto. subst r0.
    rewrite C by auto. rewrite Regmap.gss. exact SPEC.
  split. intros. 
    rewrite C by tauto. apply Regmap.gso. intuition auto.
  exact D.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_callee_save_correct:
  forall m j sp ls ls0 pa ra P rs k cs fb,
  m |= frame_contents j sp ls ls0 pa ra ** P ->
  agree_unused j ls0 rs ->
  exists rs',
    star step tge
       (State cs fb (Vptr sp Ptrofs.zero) (restore_callee_save fe k) rs m)
    E0 (State cs fb (Vptr sp Ptrofs.zero) k rs' m)
  /\ (forall r,
        is_callee_save r = true -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r,
        is_callee_save r = false -> rs' r = rs r).
Proof.
  intros.
  unfold frame_contents, frame_contents_1 in H. 
  apply mconj_proj1 in H. rewrite ! sep_assoc in H. apply sep_pick5 in H. 
  exploit restore_callee_save_rec_correct; eauto.
  intros; unfold mreg_within_bounds; auto.
  intros (rs' & A & B & C & D).
  exists rs'.
  split. eexact A.
  split; intros.
  destruct (In_dec mreg_eq r (used_callee_save b)).
  apply B; auto.
  rewrite C by auto. apply H0. unfold mreg_within_bounds; tauto.
  apply C. red; intros. apply (used_callee_save_prop b) in H2. congruence.
Qed.

(** As a corollary, we obtain the following correctness result for
  the execution of a function epilogue (reloading of used callee-save
  registers + reloading of the link and return address + freeing
  of the frame). *)

Lemma function_epilogue_correct:
  forall m' j sp' ls ls0 pa ra P m rs sp m1 k cs fb,
  m' |= frame_contents j sp' ls ls0 pa ra ** minjection j m ** P ->
  agree_regs j ls rs ->
  agree_locs ls ls0 ->
  j sp = Some(sp', fe.(fe_stack_data)) ->
  Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m1 ->
  exists rs1, exists m1',
     load_stack m' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_link_ofs) = Some pa
  /\ load_stack m' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_retaddr_ofs) = Some ra
  /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
  /\ star step tge
       (State cs fb (Vptr sp' Ptrofs.zero) (restore_callee_save fe k) rs m')
    E0 (State cs fb (Vptr sp' Ptrofs.zero) k rs1 m')
  /\ agree_regs j (return_regs ls0 ls) rs1
  /\ agree_callee_save (return_regs ls0 ls) ls0
  /\ m1' |= minjection j m1 ** P.
Proof.
  intros until fb; intros SEP AGR AGL INJ FREE.
  (* Can free *)
  exploit free_parallel_rule.
    rewrite <- sep_assoc. eapply mconj_proj2. eexact SEP.
    eexact FREE.
    eexact INJ.
    auto. rewrite Z.max_comm; reflexivity.
  intros (m1' & FREE' & SEP').
  (* Reloading the callee-save registers *)
  exploit restore_callee_save_correct.
    eexact SEP.
    instantiate (1 := rs). 
    red; intros. destruct AGL. rewrite <- agree_unused_reg0 by auto. apply AGR.
  intros (rs' & LOAD_CS & CS & NCS).
  (* Reloading the back link and return address *)
  unfold frame_contents in SEP; apply mconj_proj1 in SEP.
  unfold frame_contents_1 in SEP; rewrite ! sep_assoc in SEP.
  exploit (hasvalue_get_stack Tptr). rewrite chunk_of_Tptr. eapply sep_pick3; eexact SEP. intros LOAD_LINK.
  exploit (hasvalue_get_stack Tptr). rewrite chunk_of_Tptr. eapply sep_pick4; eexact SEP. intros LOAD_RETADDR.
  clear SEP.
  (* Conclusions *)
  rewrite unfold_transf_function; simpl.
  exists rs', m1'.
  split. assumption.
  split. assumption.
  split. assumption.
  split. eassumption.
  split. red; unfold return_regs; intros. 
    destruct (is_callee_save r) eqn:C.
    apply CS; auto.
    rewrite NCS by auto. apply AGR.
  split. red; unfold return_regs; intros.
    destruct l; auto. rewrite H; auto.
  assumption.
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariants *)

(** This is the memory assertion that captures the contents of the stack frames
  mentioned in the call stacks. *)

Variable init_ls: locset.

Fixpoint stack_contents (j: meminj) (cs: list Linear.stackframe) (cs': list Mach.stackframe) : massert :=
  match cs, cs' with
  | nil, nil => pure True
  | Linear.Stackframe f _ ls c :: cs, Mach.Stackframe fb (Vptr sp' _) ra c' :: cs' =>
      frame_contents f j sp' ls (parent_locset init_ls cs) (parent_sp init_sp cs') (parent_ra init_ra cs')
      ** stack_contents j cs cs'
  | _, _ => pure False
  end.

Lemma stack_contents_invar_weak cs :
  forall j cs' , m_invar_weak (stack_contents j cs cs') = false.
Proof.
  induction cs; destruct cs' ; simpl; auto.
  + destruct a; auto.
  + destruct a; auto.
    destruct s; auto.
    destruct sp0; auto.
    match goal with
        [ |- context [m_invar_weak (?U ** ?V)] ] =>
        replace (m_invar_weak (U ** V))
                with (m_invar_weak U || m_invar_weak V)
          by reflexivity
    end.
    rewrite frame_contents_invar_weak.
    simpl.
    auto.
Qed.

(* [init_sg] is the signature of the outermost calling function. In the
whole-program, this is the signature of the [main] function (see the
match_states' definition at the very end of this file) *)

Variable init_sg: signature.

(** [match_stacks] captures additional properties (not related to memory)
  of the Linear and Mach call stacks. *)


Inductive match_stacks (j: meminj) :
  list Linear.stackframe -> list stackframe -> signature -> signature -> Prop :=
| match_stacks_empty:
    forall sg
      (TP: tailcall_possible sg \/ sg = init_sg)
      (BND: 4 * size_arguments sg <= Ptrofs.max_unsigned),
      match_stacks j nil nil sg sg
| match_stacks_cons:
    forall f sp ls c cs fb sp' ra c' cs' sg trf
      isg
      (TAIL: is_tail c (Linear.fn_code f))
      (FINDF: Genv.find_funct_ptr tge fb = Some (Internal trf))
      (TRF: transf_function f = OK trf)
      (TRC: transl_code (make_env (function_bounds f)) c = c')
      (INJ: j sp = Some(sp', (fe_stack_data (make_env (function_bounds f)))))
      (INJ_UNIQUE: forall b delta, j b = Some (sp', delta) -> b = sp)
      (TY_RA: Val.has_type ra Tptr)
      (AGL: agree_locs f ls (parent_locset init_ls cs))
      (ARGS: forall ofs ty,
          In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
          slot_within_bounds (function_bounds f) Outgoing ofs ty)
      (BND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (NOT_INIT: forall (b : block) (o : ptrofs), init_sp = Vptr b o -> b <> sp')
      (STK: match_stacks j cs cs' (Linear.fn_sig f) isg),
      match_stacks j
                   (Linear.Stackframe f (Vptr sp Ptrofs.zero) ls c :: cs)
                   (Stackframe fb (Vptr sp' Ptrofs.zero) ra c' :: cs')
                   sg isg.

(* [args_out_of_bounds] states that the locations in [l] have no permission and
can therefore not be overwritten by the callee. This is exclusively applied to
the locations of the arguments of the outermost caller ([main] in the
whole-program setting). *)

Definition init_args_out_of_bounds sg m :=
  forall b o,
    init_sp = Vptr b o ->
    forall of ty,
      List.In (Locations.S Outgoing of ty) (regs_of_rpairs (loc_arguments sg)) ->
      let ofs := Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (fe_ofs_arg + 4 * of))) in
      forall o,
        ofs <= o < (ofs + size_chunk (chunk_of_type ty)) ->
        loc_out_of_bounds m b o.

Lemma init_args_out_of_bounds_store sg chunk m b o v m':
  Mem.store chunk m b o v = Some m' ->
  init_args_out_of_bounds sg m ->
  init_args_out_of_bounds sg m'.
Proof.
  unfold init_args_out_of_bounds.
  intros H H0 b0 o0 H1 of ty H2 o1 H3.
  intro ABSURD.
  eapply Mem.perm_store_2 in ABSURD; eauto.
  eapply H0; eauto.
Qed.

Lemma init_args_out_of_bounds_storev sg chunk m addr v m':
  Mem.storev chunk m addr v = Some m' ->
  init_args_out_of_bounds sg m ->
  init_args_out_of_bounds sg m'.
Proof.
  destruct addr; try discriminate.
  apply init_args_out_of_bounds_store.
Qed.

Lemma init_args_out_of_bounds_free sg m b lo hi m' :
  Mem.free m b lo hi = Some m' ->
  init_args_out_of_bounds sg m ->
  init_args_out_of_bounds sg m' .
Proof.
  unfold init_args_out_of_bounds.
  intros H H0 b0 o H1 of ty H2 o0 H3.
  intro ABSURD.
  eapply Mem.perm_free_3 in ABSURD; eauto.
  eapply H0; eauto.
Qed.

Lemma init_args_out_of_bounds_external_call sg_ ef args m_ t vl m'_ :
  (forall b o, init_sp = Vptr b o -> Mem.valid_block m_ b) ->
  external_call ef ge args m_ t vl m'_ ->
  forall j m m' sg ll lm ,
    match_stacks j ll lm sg sg_ ->
    Mem.extends m_ m ->
    Mem.inject j m m' ->
    init_args_out_of_bounds sg_ m_ ->
    init_args_out_of_bounds sg_ m'_ .
Proof.
  unfold init_args_out_of_bounds.
  intros VB H j m m' sg ll lm H0 H1 H2 H3 b o H4 of ty H5 o0 H6.
  intro ABSURD.
  eapply H3; eauto.
  eapply external_call_max_perm; eauto.
Qed.

Definition block_prop P v :=
  match v with
    Vptr b o => P b
  | _ => True
  end.

Lemma init_args_out_of_bounds_alloc m_ lo hi m'_ b :
  Mem.alloc m_ lo hi = (m'_, b) ->
  block_prop (Mem.valid_block m_) init_sp ->
  forall sg_ j m m' sg ll lm,
    match_stacks j ll lm sg sg_ ->
    Mem.extends m_ m ->
    Mem.inject j m m' ->
    init_args_out_of_bounds sg_ m_ ->
    init_args_out_of_bounds sg_ m'_ .
Proof.
  unfold init_args_out_of_bounds, loc_out_of_bounds.
  intros H SPV sg_ j m m' sg ll lm H0 H1 H2 H3 b0 o H4 of ty H5 o0 H6.
  intro ABSURD.
  eapply Mem.perm_alloc_4 in ABSURD; eauto.
  { eapply H3; eauto. }
  apply Mem.fresh_block_alloc in H. red in SPV. rewrite H4 in SPV. congruence.
Qed.

Lemma match_stacks_size_args:
  forall j ll lm sg sg_
    (MS: match_stacks j ll lm sg sg_),
    4 * size_arguments sg <= Ptrofs.max_unsigned.
Proof.
  inversion 1; auto.
Qed.

(** Invariance with respect to change of memory injection. *)

Lemma stack_contents_change_meminj:
  forall m j j', inject_incr j j' ->
  forall cs cs' P,
  m |= stack_contents j cs cs' ** P ->
  m |= stack_contents j' cs cs' ** P.
Proof.
Local Opaque sepconj.
  induction cs as [ | [] cs]; destruct cs' as [ | [] cs']; simpl; intros; auto.
  destruct sp0; auto.
  rewrite sep_assoc in H0 |- * .
  apply frame_contents_incr with (j := j); auto.
  rewrite sep_swap. apply IHcs. rewrite sep_swap. assumption.
Qed.

Lemma match_stacks_change_meminj:
  forall j j', inject_incr j j' ->
          (exists m m',
              inject_separated j j' m m' /\
              (forall b b' delta, j b = Some (b', delta) -> Mem.valid_block m' b')) ->
  forall cs cs' sg isg,
  match_stacks j cs cs' sg isg ->
  match_stacks j' cs cs' sg isg.
Proof.
  induction 3; intros.
- constructor; auto.
- econstructor; eauto.
  destruct H0 as (m & m' & (H0 & VB)).
  intros.
  destruct (j b) eqn:?.
  + destruct p. exploit H. eauto. intros.
    assert (b0 = sp') by congruence. subst. eapply INJ_UNIQUE in Heqo. auto.
  + generalize (H0 _ _ _ Heqo H2).
    intros (A & B).
    apply VB in INJ. congruence.
Qed.

(* [args_in_bounds] states that the locations of arguments in [l] are freeable
in [m]. This is instantiated with the locations of the arguments of the
outermost caller ([main] in the whole-program setting). In practice, the memory
[m] is that of the Mach memory state. *)

Definition args_in_bounds sp l m :=
  exists m_, free_extcall_args sp m l = Some m_.

Definition init_args_in_bounds sg :=
  args_in_bounds init_sp (regs_of_rpairs (loc_arguments sg)).

Lemma init_args_in_bounds_perm sg m m':
  (forall b o_, init_sp = Vptr b o_ -> forall o k p, Mem.perm m b o k p -> Mem.perm m' b o k p) ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  unfold init_args_in_bounds, args_in_bounds.
  generalize init_sp.
  intros sp H H0.
  destruct H0 as (m_ & H0).
  revert m m' H m_ H0.
  induction (regs_of_rpairs (loc_arguments sg)); simpl; eauto.
  intros m m' H m_.
  unfold free_extcall_arg.
  destruct a; eauto.
  destruct sl; eauto.
  destruct sp; try discriminate.
  set (o := Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (fe_ofs_arg + 4 * pos)))).
  destruct (
      Mem.free m b o (o + size_chunk (chunk_of_type ty))
    ) eqn:FREE; try discriminate.
  intros H0.
  generalize FREE. intro FREE1.
  apply Mem.free_range_perm in FREE1.
  unfold Mem.range_perm in FREE1.
  generalize (fun ofs J => H _ _ (eq_refl _) _ _ _ (FREE1 ofs J)).
  clear FREE1. intro FREE2.
  apply Mem.range_perm_free in FREE2.
  destruct FREE2 as (m2 & FREE2).
  rewrite FREE2.
  eapply IHl; try eassumption.
  inversion 1; subst b0 o_.
  intros o0 k p.
  erewrite Mem.perm_free by eassumption.
  intros H2.
  erewrite Mem.perm_free by eassumption.
  specialize (H _ _ (eq_refl _) o0 k p).
  tauto.
Qed.

Lemma init_args_in_bounds_store sg chunk m b o v m':
  Mem.store chunk m b o v = Some m' ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  intro K.
  apply init_args_in_bounds_perm.
  intros b0 o_ H o0 k p.
  eauto using Mem.perm_store_1.
Qed.

Lemma init_args_in_bounds_storev sg chunk m bo v m':
  Mem.storev chunk m bo v = Some m' ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  destruct bo; try discriminate.
  apply init_args_in_bounds_store.
Qed.


Lemma init_args_in_bounds_free m b lo hi m' sg:
  Mem.free m b lo hi = Some m' ->
  (forall b' o', init_sp = Vptr b' o' -> b' <> b) ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  intros H H0.
  apply init_args_in_bounds_perm.
  intros b0 o_ H1 o k p.
  specialize (H0 _ _ H1).
  clear H1.
  intros H1.
  erewrite Mem.perm_free by eassumption.
  tauto.
Qed.

Lemma init_args_in_bounds_alloc m lo hi b m' sg:
  Mem.alloc m lo hi = (m', b) ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  intros H.
  apply init_args_in_bounds_perm.
  intros b0 o_ H0 o k p.
  eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma free_extcall_args_change_mem sp:
  forall (l : list loc) (m' m'_ : mem)
    (PERM:
       forall b o (EQsp: sp = Vptr b o)
         of ty (IN: In (S Outgoing of ty) l)
         o'
         (RNG: Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (fe_ofs_arg + 4 * of))) <= o' <
               Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (fe_ofs_arg + 4 * of))) +
               size_chunk (chunk_of_type ty))
         k p (PERM: Mem.perm m' b o' k p), Mem.perm m'_ b o' k p)
    m_ (FEA: free_extcall_args sp m' l = Some m_),
  exists m_0, free_extcall_args sp m'_ l = Some m_0.
Proof.
  induction l. simpl; eauto.
  intros until m_.
  simpl.
  unfold free_extcall_arg.
  simpl In in PERM.
  destruct a; eauto.
  destruct sl; eauto.
  destruct sp; try discriminate.
  set (ofs := Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (fe_ofs_arg + 4 * pos)))).
  destruct (Mem.free m' b ofs (ofs + size_chunk (chunk_of_type ty))) eqn:FREE; try discriminate.
  generalize (Mem.free_range_perm _ _ _ _ _ FREE).
  unfold Mem.range_perm.
  intro RANGE.
  generalize (fun o K => PERM _ _ (eq_refl _) _ _ (or_introl _ (eq_refl _)) o K _ _ (RANGE _ K)).
  clear RANGE. intro RANGE.
  apply Mem.range_perm_free in RANGE.
  fold ofs in RANGE.
  destruct RANGE as (m2 & Hm2).
  rewrite Hm2.
  eapply IHl; eauto.
  intros b0 o EQ of ty0 IN o' RNG k p PERM'.
  inv EQ.
  erewrite Mem.perm_free by eassumption.
  erewrite Mem.perm_free in PERM' by eassumption.
  destruct PERM'; split; eauto.
Qed.


Lemma init_args_in_bounds_external_call sg_ ef args m_ t vl m'1 :
  forall (EC: external_call ef ge args m_ t vl m'1)
    j m m'
    (MPG: meminj_preserves_globals ge j)
    (K: forall b o, init_sp = Vptr b o -> j b = Some (b, 0))
    (IMAGE: forall b o, init_sp = Vptr b o -> forall b' delta, j b' = Some (b, delta) -> b' = b /\ delta = 0)
    (MEXT: Mem.extends m_ m)
    (MINJ: Mem.inject j m m')
    (IAOOB: init_args_out_of_bounds sg_ m_)
    ll lm sg
    (MS: match_stacks j ll lm sg sg_)
    args'
    (INJARGS: Val.inject_list j args args')
    vl' m'2
    (EC2: external_call ef ge args' m' t vl' m'2)
    (IAIB: init_args_in_bounds sg_ m'),
    init_args_in_bounds sg_ m'2.
Proof.
  intros EC j m m' MPG K IMAGE MEXT MINJ IAOOB ll lm sg MS args' INJARGS vl' m'2 EC2 IAIB.
  generalize (Mem.extends_inject_compose _ _ _ _ MEXT MINJ).
  intros MINJ'.
  revert EC2.
  exploit external_call_mem_inject ; eauto.
  destruct 1 as (_ & res'_ & m'2_ & EC2 & _ & _ & _ & UNCHANGED & _ & _).
  intros EC2'.
  exploit external_call_determ .
  eexact EC2.
  eexact EC2'.
  destruct 1 as (_ & INJ).
  specialize (INJ (eq_refl _)).
  destruct INJ; subst.
  destruct IAIB.
  eapply free_extcall_args_change_mem. 2: eauto.
  intros b o EQsp of ty IN o' RNG k p PERM.
  specialize (K _ _ EQsp).
  eapply Mem.perm_unchanged_on; eauto.
  unfold init_args_out_of_bounds in IAOOB.
  unfold loc_out_of_reach.
  intros b0 delta JB.
  generalize JB. intro JB'.
  eapply IMAGE in JB'.
  destruct JB'; subst.
  rewrite Zminus_0_r.
  eapply IAOOB; eauto. eauto.
Qed.

Opaque Z.mul.


Lemma args_always_in_bounds j m' sg_ ll lm sg  :
  forall (MS: match_stacks j ll lm sg sg_)
    (IAIB: init_args_in_bounds sg_ m')
    (SEP: m' |= stack_contents j ll lm),
    args_in_bounds (parent_sp init_sp lm) (regs_of_rpairs (loc_arguments sg)) m'.
Proof.
  inversion 1; subst; auto.
  simpl. intros _ SEP.
  clear - external_calls_prf ARGS SEP TRF BND.
  cut (forall l2 l1,
          regs_of_rpairs (loc_arguments sg) = l1 ++ l2 ->
          forall m',
            (forall o ty,
                In (S Outgoing o ty) l2 ->
                let of := Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (fe_ofs_arg + 4 * o)))
                in
                forall ofs,
                  of <= ofs < of + size_chunk (chunk_of_type ty) ->
                  0 <= ofs < fe_size (make_env (function_bounds f)) ->
                  ofs < fe_stack_data (make_env (function_bounds f)) \/
                  fe_stack_data (make_env (function_bounds f)) +
                  bound_stack_data (function_bounds f) <= ofs ->
                  Mem.perm m' sp' ofs Cur Freeable) ->
            args_in_bounds (Vptr sp' Ptrofs.zero) l2 m').
  {
    intros H.
    apply (H _ nil (eq_refl _)).
    intros.
    apply sep_proj1 in SEP.
    destruct SEP.
    destruct H3.
    apply sep_proj1 in H5.
    destruct H5. destruct H6.
    apply H7. omega.
    apply sep_proj2 in H5. destruct H5. destruct H6. apply H7. omega.
  }
  intro l2.
  unfold args_in_bounds.
  Opaque fe_stack_data fe_size.
  induction l2; simpl; eauto.
  intros l1 H m'0 H0.

  simpl In in H0.
  assert (regs_of_rpairs (loc_arguments sg) = (l1 ++ a :: nil) ++ l2) as EQ.
  {
    rewrite H.
    rewrite app_ass.
    reflexivity.
  }
  specialize (IHl2 _ EQ).
  clear EQ.
  unfold free_extcall_arg.
  destruct a; eauto.
  destruct sl; eauto.
  assert (In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) as IN.
  {
    rewrite H.
    apply in_or_app.
    simpl.
    auto.
  }
  generalize (ARGS _ _ IN). intro ARGS_.
  generalize (H0 _ _ (or_introl _ (eq_refl _))).
  set (of := Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (fe_ofs_arg + 4 * pos)))).
  intros H1.
  generalize (eq_refl of).
  unfold of at 2.
  revert H1.
  generalize of. clear of. intro of.
  intros H1 H2.
  rewrite Ptrofs.add_commut in H2.
  rewrite Ptrofs.add_zero in H2.
  assert (EQ: Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + 4 * pos)) = fe_ofs_arg + 4 * pos).
  {
    apply Ptrofs.unsigned_repr.
    generalize (loc_arguments_bounded _ _ _ IN); eauto.
    simpl. intro.
    exploit loc_arguments_acceptable_2; eauto. intros [A B].
    split. omega.
    transitivity (4 * size_arguments sg). apply Z.mul_le_mono_nonneg_l. omega.
    generalize (typesize_pos ty); omega. auto.
  }

  rewrite EQ in H2.
  exploit (Mem.range_perm_free' m'0 sp' of (of + size_chunk (chunk_of_type ty))).
  {
    red.
    intros ofs H3.
    eapply H1; eauto; try omega.
    - subst. rewrite Ptrofs.add_zero_l in *.
      simpl in EQ. rewrite EQ in *. simpl in H3. omega.
    - red in ARGS_.
      generalize (frame_env_separated' (function_bounds f)).
      intros.
      exploit loc_arguments_acceptable_2; eauto. intros [A B].
      split. simpl in H2. omega. simpl in H2.
      eapply Zlt_le_trans. apply H3.
      etransitivity.
      2: apply frame_env_range. rewrite size_type_chunk, typesize_typesize.
      etransitivity.
      subst. rewrite <- Z.mul_add_distr_l. apply Z.mul_le_mono_nonneg_l. omega.
      apply ARGS_.
      etransitivity.
      eapply align_le.
      2: etransitivity. 2: apply H4. destruct (Archi.ptr64); omega.
      generalize (bound_stack_data_pos (function_bounds f)); omega.
    - left.
      eapply Zlt_le_trans. apply H3.
      rewrite size_type_chunk, typesize_typesize.
      etransitivity.
      subst. simpl. rewrite <- Z.mul_add_distr_l. apply Z.mul_le_mono_nonneg_l. omega.
      apply ARGS_.
      generalize (frame_env_separated' (function_bounds f)).
      intros.
      etransitivity. eapply align_le.
      2: etransitivity. 2: apply H4. destruct (Archi.ptr64); omega.
      omega.
  }
  destruct 1 as (m2 & Hm2).
  rewrite Hm2.
  eapply IHl2; clear IHl2.
  intros o ty0 H3 ofs H4 H5 H6.
  eapply Mem.perm_free_1; eauto.
  clear H0.
  right.
  generalize (loc_arguments_norepet sg).
  rewrite H.
  intros H0.
  apply Loc.norepet_app_inv in H0.
  destruct H0 as (_ & H0 & _).
  inversion H0; subst.
  rewrite Loc.notin_iff in H9.
  specialize (H9 _ H3).
  simpl in H9.
  destruct H9; try congruence.
  rewrite size_type_chunk in *.
  rewrite typesize_typesize in *.
  rewrite Ptrofs.add_commut in H4.
  rewrite Ptrofs.add_zero in H4.
  clear IN.
  assert (In (S Outgoing o ty0) (regs_of_rpairs (loc_arguments sg))) as IN.
  {
    rewrite H.
    apply in_or_app.
    simpl; auto.
  }
  generalize (ARGS _ _ IN). intro ARGS_IN.

  simpl.
  assert (EQ4: Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + 4 * o)) = fe_ofs_arg + 4 * o).
  {
    apply Ptrofs.unsigned_repr.
    generalize (loc_arguments_bounded _ _ _ IN); eauto.
    simpl. intro.
    exploit loc_arguments_acceptable_2; eauto. intros [A B].
    split. omega.
    transitivity (4 * size_arguments sg). apply Z.mul_le_mono_nonneg_l. omega.
    generalize (typesize_pos ty); omega. auto.
  }
  rewrite EQ4 in H4. simpl in H4. omega.
Qed.

Lemma tailcall_possible_in_bounds:
  forall sg,
    tailcall_possible sg ->
    forall m,
      init_args_in_bounds sg m.
Proof.
  intros sg H m.
  unfold init_args_in_bounds, args_in_bounds.
  red in H.
  revert H.
  induction (regs_of_rpairs (loc_arguments sg)); simpl; eauto.
  intros H.
  unfold free_extcall_arg.
  destruct a.
  {
    eapply IHl; eauto.
    intros l0 H1.
    eapply H; eauto.
  }
  destruct sl; try (eapply IHl; eauto; intros; eapply H; eauto).
  exfalso. specialize (H _ (or_introl _ (eq_refl _))).
  contradiction.
Qed.

Lemma match_stacks_change_sig:
  forall sg1 j cs cs' sg isg,
  match_stacks j cs cs' sg isg ->
  tailcall_possible sg1 ->
  4 * size_arguments sg1 <= Ptrofs.max_unsigned ->
  match_stacks j cs cs' sg1
               match cs with
                   nil => sg1
                 | _ => isg
               end.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto. intros. elim (H0 _ H2).
Qed.

(** Typing properties of [match_stacks]. *)

(** [CompCertX:test-compcert-protect-stack-arg] In whole-program settings, [init_sp = Vzero], so the following hypotheses are trivially true. 
    In non-whole-program settings, the following two hypotheses are provided by the caller's assembly semantics, which maintains the well-typedness of the assembly register set as an invariant. *)
Hypothesis init_sp_int: Val.has_type init_sp Tptr.
Hypothesis init_ra_int: Val.has_type init_ra Tptr.


Lemma match_stacks_type_sp:
  forall j cs cs' sg isg,
  match_stacks j cs cs' sg isg ->
  Val.has_type (parent_sp init_sp cs') Tptr.
Proof.
  induction 1; unfold parent_sp. auto. apply Val.Vptr_has_type.
Qed. 

Lemma match_stacks_type_retaddr:
  forall j cs cs' sg isg,
  match_stacks j cs cs' sg isg ->
  Val.has_type (parent_ra init_ra cs') Tptr.
Proof.
  induction 1; unfold parent_ra. auto. auto. 
Qed.

(** * Syntactic properties of the translation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_save_callee_save:
  forall lbl l ofs k,
  Mach.find_label lbl (save_callee_save_rec l ofs k) = Mach.find_label lbl k.
Proof.
  induction l; simpl; auto.
Qed.

Remark find_label_restore_callee_save:
  forall lbl l ofs k,
  Mach.find_label lbl (restore_callee_save_rec l ofs k) = Mach.find_label lbl k.
Proof.
  induction l; simpl; auto.
Qed.

Lemma transl_code_eq:
  forall fe i c, transl_code fe (i :: c) = transl_instr fe i (transl_code fe c).
Proof.
  unfold transl_code; intros. rewrite list_fold_right_eq. auto.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
- auto.
- rewrite transl_code_eq.
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  unfold restore_callee_save. rewrite find_label_restore_callee_save. auto.
  simpl. destruct (peq lbl l). reflexivity. auto.
  unfold restore_callee_save. rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) =
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl.
  unfold transl_body. unfold save_callee_save. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code tail property for Linear executions. *)

Lemma find_label_tail:
  forall lbl c c',
  Linear.find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. auto with coqlib.
  auto with coqlib.
Qed.

(** Code tail property for translations *)

Lemma is_tail_save_callee_save:
  forall l ofs k,
  is_tail k (save_callee_save_rec l ofs k).
Proof.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto. 
Qed.

Lemma is_tail_restore_callee_save:
  forall l ofs k,
  is_tail k (restore_callee_save_rec l ofs k).
Proof.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto. 
Qed.

Lemma is_tail_transl_instr:
  forall fe i k,
  is_tail k (transl_instr fe i k).
Proof.
  intros. destruct i; unfold transl_instr; auto with coqlib.
  destruct s; auto with coqlib.
  destruct s; auto with coqlib.
  unfold restore_callee_save.  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
  unfold restore_callee_save.  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
Qed.

Lemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
Proof.
  induction 1; simpl. auto with coqlib.
  rewrite transl_code_eq.
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed.

Lemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (Linear.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (fn_code tf).
Proof.
  intros. rewrite (unfold_transf_function _ _ H). simpl.
  unfold transl_body, save_callee_save. 
  eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed.

(** * Semantic preservation *)

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof. apply senv_preserved. Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial TRANSF).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros; monadInv H.
  rewrite (unfold_transf_function _ _ EQ). auto.
  auto.
Qed.

Lemma find_function_translated:
  forall j ls rs m ros f,
  agree_regs j ls rs ->
  m |= globalenv_inject ge j ->
  Linear.find_function ge ros ls = Some f ->
  exists bf, exists tf,
     find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros AG [bound [_ [?????]]] FF.
  destruct ros; simpl in FF.
- exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF.
  rewrite Genv.find_funct_find_funct_ptr in FF.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). rewrite EQ. intro INJ. inv INJ.
  rewrite DOMAIN in H2. inv H2. simpl. auto. eapply FUNCTIONS; eauto.
- destruct (Genv.find_symbol ge i) as [b|] eqn:?; try discriminate.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  rewrite symbols_preserved. auto.
Qed.

(** Preservation of the arguments to an external call. *)


(* [init_args_mach] states that the locations of the arguments of function with
signature [sg] can be retrieved in [m'] (a Mach memory state) and agree with the
locset [init_ls].*)

Definition init_args_mach j sg m' :=
  forall sl of ty,
    List.In (Locations.S sl of ty) (regs_of_rpairs (loc_arguments sg)) ->
    forall rs,
    exists v,
      extcall_arg rs m' init_sp (S sl of ty) v /\
      Val.inject j (init_ls (S sl of ty)) v.

(** General case *)

Section EXTERNAL_ARGUMENTS.

Variable j: meminj.
Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable sg: signature.
Variables bound bound': block.
Variable isg: signature.
Hypothesis MS: match_stacks j cs cs' sg isg.
Variable ls: locset.
Variable rs: regset.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset init_ls cs).
Variable m': mem.
Hypothesis SEP: m' |= stack_contents j cs cs'.

Hypothesis init_args: init_args_mach j isg m'.

Lemma transl_external_argument:
  forall l,
  In l (regs_of_rpairs (loc_arguments sg)) ->
  exists v, extcall_arg rs m' (parent_sp init_sp cs') l v /\ Val.inject j (ls l) v.
Proof.
  intros.
  assert (loc_argument_acceptable l) by (apply loc_arguments_acceptable_2 with sg; auto).
  destruct l; red in H0.
- exists (rs r); split. constructor. auto.
- destruct sl; try contradiction.
  inv MS.
  + destruct TP as [TP|TP].
    * elim (TP _ H).
    * subst isg. simpl in *.
      red in AGCS. rewrite AGCS; auto.
  + simpl in SEP. simpl.
    assert (slot_valid f Outgoing pos ty = true).
    { destruct H0. unfold slot_valid, proj_sumbool.
      rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. }
    assert (slot_within_bounds (function_bounds f) Outgoing pos ty) by eauto.
    exploit frame_get_outgoing; eauto. intros (v & A & B).
    exists v; split.
    constructor. exact A. red in AGCS. rewrite AGCS; auto.
Qed.

Lemma transl_external_argument_2:
  forall p,
  In p (loc_arguments sg) ->
  exists v, extcall_arg_pair rs m' (parent_sp init_sp cs') p v /\ Val.inject j (Locmap.getpair p ls) v.
Proof.
  intros. destruct p as [l | l1 l2].
- destruct (transl_external_argument l) as (v & A & B). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists v; split; auto. constructor; auto. 
- destruct (transl_external_argument l1) as (v1 & A1 & B1). eapply in_regs_of_rpairs; eauto; simpl; auto.
  destruct (transl_external_argument l2) as (v2 & A2 & B2). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists (Val.longofwords v1 v2); split. 
  constructor; auto.
  apply Val.longofwords_inject; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
      list_forall2 (extcall_arg_pair rs m' (parent_sp init_sp cs')) locs vl
   /\ Val.inject_list j (map (fun p => Locmap.getpair p ls) locs) vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil val); split. constructor. constructor.
  exploit transl_external_argument_2; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
      extcall_arguments rs m' (parent_sp init_sp cs') sg vl
   /\ Val.inject_list j (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) vl.
Proof.
  unfold extcall_arguments.
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** Preservation of the arguments to a builtin. *)

Section BUILTIN_ARGUMENTS.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.
Variable j: meminj.
Variables m m': mem.
Variables ls ls0: locset.
Variable rs: regset.
Variables sp sp': block.
Variables parent retaddr: val.
Hypothesis INJ: j sp = Some(sp', fe.(fe_stack_data)).
Hypothesis AGR: agree_regs j ls rs.
Hypothesis SEP: m' |= frame_contents f j sp' ls ls0 parent retaddr ** minjection j m ** globalenv_inject ge j.

Lemma transl_builtin_arg_correct:
  forall a v,
  eval_builtin_arg ge ls (Vptr sp Ptrofs.zero) m a v ->
  (forall l, In l (params_of_builtin_arg a) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_arg a) -> slot_within_bounds b sl ofs ty) ->
  exists v',
     eval_builtin_arg ge rs (Vptr sp' Ptrofs.zero) m' (transl_builtin_arg fe a) v'
  /\ Val.inject j v v'.
Proof.
  assert (SYMB: forall id ofs, Val.inject j (Senv.symbol_address ge id ofs) (Senv.symbol_address ge id ofs)).
  { assert (G: meminj_preserves_globals ge j).
    { eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eexact SEP. }
    intros; unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id) eqn:FS; auto.
    destruct G. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
Local Opaque fe.
  induction 1; simpl; intros VALID BOUNDS.
- assert (loc_valid f x = true) by auto.
  destruct x as [r | [] ofs ty]; try discriminate.
  + exists (rs r); auto with barg.
  + exploit frame_get_local; eauto. intros (v & A & B). 
    exists v; split; auto. constructor; auto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- set (ofs' := Ptrofs.add ofs (Ptrofs.repr (fe_stack_data fe))).
  apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  instantiate (1 := Val.offset_ptr (Vptr sp' Ptrofs.zero) ofs').
  simpl. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
  intros (v' & A & B). exists v'; split; auto. constructor; auto. 
- econstructor; split; eauto with barg.
  unfold Val.offset_ptr. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
- apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. 
- destruct IHeval_builtin_arg1 as (v1 & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2); auto using in_or_app.
  exists (Val.longofwords v1 v2); split; auto with barg.
  apply Val.longofwords_inject; auto.
Qed.

Lemma transl_builtin_args_correct:
  forall al vl,
  eval_builtin_args ge ls (Vptr sp Ptrofs.zero) m al vl ->
  (forall l, In l (params_of_builtin_args al) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_args al) -> slot_within_bounds b sl ofs ty) ->
  exists vl',
     eval_builtin_args ge rs (Vptr sp' Ptrofs.zero) m' (List.map (transl_builtin_arg fe) al) vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; simpl; intros VALID BOUNDS.
- exists (@nil val); split; constructor.
- exploit transl_builtin_arg_correct; eauto using in_or_app. intros (v1' & A & B).
  exploit IHlist_forall2; eauto using in_or_app. intros (vl' & C & D).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End BUILTIN_ARGUMENTS.

(** [CompCertX:test-compcert-protect-stack-arg] We have to prove that
the memory injection introduced by the compilation pass is independent
of the initial memory i.e. it does not inject new blocks into blocks
already existing in the initial memory. This is stronger than
[meminj_preserves_globals], which only preserves blocks associated to
the global environment. *)

Section WITHMEMINIT.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Satisfaction of the separation logic assertions that describe the contents 
  of memory.  This is a separating conjunction of facts about:
-- the current stack frame
-- the frames in the call stack
-- the injection from the Linear memory state into the Mach memory state
-- the preservation of the global environment.
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs].
- The Linear code [c] is a suffix of the code of the
  function [f] being executed.
- Well-typedness of [f].
*)

Require Linear2.

Definition state_mem (s: Linear.state) :=
  match s with
  | Linear.State stack f sp c rs m => m
  | Linear.Callstate stack f rs m => m
  | Linear.Returnstate stack rs m => m
  end.

Definition has_at_most_one_antecedent (j: meminj) P :=
  forall b' o' (EQ: P = Vptr b' o')
    b1 b2 delta1 delta2
    (J1: j b1 = Some (b', delta1))
    (J2: j b2 = Some (b', delta2)),
    b1 = b2.

Lemma has_at_most_one_antecedent_incr:
  forall j j' (INCR: inject_incr j j')
    m m' (SEP: inject_separated j j' m m')
    v (HAMOA: has_at_most_one_antecedent j v)
    (BP: block_prop (Mem.valid_block m') v),
    has_at_most_one_antecedent j' v.
Proof.
  red; intros. subst. red in HAMOA.
  specialize (HAMOA _ _ eq_refl).
  destruct (j b1) eqn:?. destruct p.
  destruct (j b2) eqn:?. destruct p.
  erewrite INCR in J1; eauto.
  erewrite INCR in J2; eauto.
  inv J1; inv J2.
  eapply HAMOA; eauto.
  generalize (SEP _ _ _ Heqo0 J2). intros (A & B); elim B. apply BP.
  generalize (SEP _ _ _ Heqo J1). intros (A & B); elim B. apply BP.
Qed.

Opaque Z.mul.

Program Definition minit_args_mach j sg_ : massert :=
  {|
    m_pred := init_args_mach j sg_;
    m_footprint := fun b o =>
                     exists sl ofs ty,
                       In (S sl ofs ty) (regs_of_rpairs (loc_arguments sg_)) /\
                       exists o', init_sp = Vptr b o' /\
                             let lo := Ptrofs.unsigned (Ptrofs.add o' (Ptrofs.repr (fe_ofs_arg + 4 * ofs))) in
                             lo <= o < lo + size_chunk (chunk_of_type ty);
    m_invar_weak := false
  |}.
Next Obligation.
  red; intros.
  exploit H. eauto. intros (v & EA & INJ).
  inv EA.
  eexists; split; eauto. econstructor; eauto.
  unfold load_stack, Val.offset_ptr, Mem.loadv in *.
  destruct init_sp; try discriminate.
  eapply Mem.load_unchanged_on; eauto.
  simpl; intros.
  exists Outgoing, of, ty; split; auto.
  eexists; split; eauto.
  Unshelve. eauto.
Defined.
Next Obligation.
  exploit H. eauto.
  intros (v & EA & INJ). inv EA.
  unfold load_stack, Val.offset_ptr, Mem.loadv in *.
  eapply Mem.load_valid_access in H12.
  destruct H12.
  exploit H0. split.
  apply Zle_refl. destruct H2; simpl; omega.
  eapply Mem.perm_valid_block; eauto.
  Unshelve. constructor.
Defined.

Fixpoint bounds_stack m ll (* hi *) :=
  match ll with
  | Linear.Stackframe f (Vptr sp o) ls c :: ll =>
    (forall ofs p,
        Mem.perm m sp ofs Max p ->
        0 <= ofs < Linear.fn_stacksize f) /\ (* Plt sp hi /\  *) bounds_stack m ll (* sp *)
  | _ => True
  end.

Lemma bounds_stack_store:
  forall s m (BS: bounds_stack m s)
    chunk b o v m'
    (STORE: Mem.store chunk m b o v = Some m'),
    bounds_stack m' s.
Proof.
  induction s; simpl; intros; auto. destruct a; auto.
  destruct sp; auto. split; auto.
  intros. destruct BS. eapply H0. eauto with mem.
  eapply IHs; eauto. apply BS.
Qed.

Lemma bounds_stack_free:
  forall s m (* b *) (BS: bounds_stack m s)
    b lo hi m'
    (FREE: Mem.free m b lo hi = Some m'),
    bounds_stack m' s.
Proof.
  induction s; simpl; intros; auto. destruct a; auto.
  destruct sp; auto. destruct BS.
  repeat (refine (conj _ _)).
  - intros. eapply H. rewrite Mem.perm_free in H1. 2: eauto. destruct H1; eauto.
  - eapply IHs; eauto.
Qed.

Fixpoint valid_stack m s :=
  match s with
  | Linear.Stackframe f (Vptr sp o) ls c :: cs =>
    Mem.valid_block m sp /\ valid_stack m cs
  | _ => True
  end.

Lemma match_stacks_valid_stack:
  forall j ll lm sg sg_
    (MS: match_stacks j ll lm sg sg_)
    m m'
    (MINJ: Mem.inject j m m'),
    valid_stack m ll.
Proof.
  induction 1; simpl; intros. auto.
  split; auto.
  - eapply Mem.valid_block_inject_1; eauto.
  - eapply IHMS; eauto.
Qed.

Lemma bounds_stack_perm:
  forall s m (BS: bounds_stack m s)
    (VS: valid_stack m s)
    m'
    (PERM: forall b ofs p, Mem.valid_block m b -> Mem.perm m' b ofs Max p -> Mem.perm m b ofs Max p),
    bounds_stack m' s.
Proof.
  induction s; simpl; intros; eauto.
  destruct a; auto. destruct sp; auto. destruct BS.
  split. intros; eauto. eapply H. eapply PERM; eauto. destruct VS; auto.
  eapply IHs; auto. apply H0. destruct VS; auto.
Qed.

Variables init_m : mem.

Inductive match_states: Linear2.state -> Mach.state -> Prop :=
| match_states_intro:
    forall sg_ cs f sp c ls m cs' fb sp' rs m' j tf
        (STACKS: match_stacks j cs cs' f.(Linear.fn_sig) sg_)
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_locs f ls (parent_locset init_ls cs))
        (INJSP: j sp = Some(sp', fe_stack_data (make_env (function_bounds f))))
        (INJUNIQUE: forall b delta, j b = Some (sp', delta) -> b = sp)
        (INJ_INIT_SP: block_prop (fun b => j b = Some (b,0)) init_sp)
        (HAMOA: has_at_most_one_antecedent j init_sp)
        (ISP'VALID: block_prop (Mem.valid_block m') init_sp)
        (INCR_init: inject_incr (Mem.flat_inj (Mem.nextblock init_m)) j)
        (INCR_sep: inject_separated (Mem.flat_inj (Mem.nextblock init_m)) j init_m init_m)
        (INIT_VB: Ple (Mem.nextblock init_m) (Mem.nextblock m))
        (INIT_VB': Ple (Mem.nextblock init_m) (Mem.nextblock m'))
        (TAIL: is_tail c (Linear.fn_code f))
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.State cs f (Vptr sp Ptrofs.zero) c ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (Hsome_init_args: init_args_in_bounds sg_ m')
        (SP_NOT_INIT: forall b o, init_sp = Vptr b o -> b <> sp')
        (SEP: m' |= frame_contents f j sp' ls (parent_locset init_ls cs) (parent_sp init_sp cs') (parent_ra init_ra cs')
                 ** stack_contents j cs cs'
                 ** (mconj (minjection j m) (minit_args_mach j sg_))
                 ** globalenv_inject ge j
        )
        (PERM_stack: forall (ofs : Z) (p : permission), Mem.perm m sp ofs Max p -> 0 <= ofs < Linear.fn_stacksize f)
        (BS: bounds_stack m cs),
      match_states s2_
                   (Mach.State cs' fb (Vptr sp' Ptrofs.zero) (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:

      forall sg_ cs f ls m cs' fb rs m' j tf
        (STACKS: match_stacks j cs cs' (Linear.funsig f) sg_)
        (TRANSL: transf_fundef f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some tf)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset init_ls cs))
        (INCR_init: inject_incr (Mem.flat_inj (Mem.nextblock init_m)) j)
        (INCR_sep: inject_separated (Mem.flat_inj (Mem.nextblock init_m)) j init_m init_m)
        (INIT_VB: Ple (Mem.nextblock init_m) (Mem.nextblock m))
        (INIT_VB': Ple (Mem.nextblock init_m) (Mem.nextblock m'))
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.Callstate cs f ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (Hsome_init_args: init_args_in_bounds sg_ m')
        (INJ_INIT_SP: block_prop (fun b => j b = Some (b,0)) init_sp)
        (HAMOA: has_at_most_one_antecedent j init_sp)
        (ISP'VALID: block_prop (Mem.valid_block m') init_sp)
        (SEP: m' |= stack_contents j cs cs'
                 ** (mconj (minjection j m) (minit_args_mach j sg_))
                 ** globalenv_inject ge j)
        (BS: bounds_stack m cs),
      match_states s2_ (Mach.Callstate cs' fb rs m')
  | match_states_return:
      forall sg_ cs ls m cs' rs m' j sg
        (STACKS: match_stacks j cs cs' sg sg_)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset init_ls cs))
        (INCR_init: inject_incr (Mem.flat_inj (Mem.nextblock init_m)) j)
        (INCR_sep: inject_separated (Mem.flat_inj (Mem.nextblock init_m)) j init_m init_m)
        (INIT_VB: Ple (Mem.nextblock init_m) (Mem.nextblock m))
        (INIT_VB': Ple (Mem.nextblock init_m) (Mem.nextblock m'))
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.Returnstate cs ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (Hsome_init_args: init_args_in_bounds sg_ m')
        (INJ_INIT_SP: block_prop (fun b => j b = Some (b,0)) init_sp)
        (HAMOA: has_at_most_one_antecedent j init_sp)
        (ISP'VALID: block_prop (Mem.valid_block m') init_sp)
        (SEP: m' |= stack_contents j cs cs'
                 ** (mconj (minjection j m) (minit_args_mach j sg_))
                 ** globalenv_inject ge j)
        (BS: bounds_stack m cs),
      match_states s2_ (Mach.Returnstate cs' rs m').

(** Record [massert_eqv] and [massert_imp] as relations so that they can be used by rewriting tactics. *)
Local Add Relation massert massert_imp
  reflexivity proved by massert_imp_refl
  transitivity proved by massert_imp_trans
as massert_imp_prel2.

Local Add Relation massert massert_eqv
  reflexivity proved by massert_eqv_refl
  symmetry proved by massert_eqv_sym
  transitivity proved by massert_eqv_trans
as massert_eqv_prel2.

Lemma sep_rot:
  forall P Q R S,
    massert_eqv (P ** Q ** R ** S) (S ** P ** Q ** R).
Proof.
  intros.
  rewrite <- (sep_assoc  Q R), <- (sep_assoc P).
  rewrite (sep_comm _ S). auto.
Qed.

Lemma Ple_Plt:
  forall a b,
    (forall c, Plt c a -> Plt c b) ->
    Ple a b.
Proof.
  intros a b H.
  destruct (peq a xH).
  + subst a. xomega.
  + exploit Ppred_Plt; eauto.
    intros H0.
    specialize (H _ H0).
    exploit Pos.succ_pred; eauto.
    intro K.
    xomega.
Qed.

Lemma eval_addressing_lessdef_strong:
  forall sp1 sp2 addr vl1 vl2 v1,
    Val.lessdef_list vl1 vl2 ->
    Val.lessdef sp1 sp2 ->
    eval_addressing ge sp1 addr vl1 = Some v1 ->
    exists v2, eval_addressing ge sp2 addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. rewrite val_inject_list_lessdef in H.
  assert (exists v2 : val,
             eval_addressing ge sp2 addr vl2 = Some v2
             /\ Val.inject (fun b => Some(b, 0)) v1 v2).
  eapply eval_addressing_inj with (sp1 := sp1).
  intros. rewrite <- val_inject_lessdef; auto.
  rewrite <- val_inject_lessdef; auto.
  eauto. auto.
  destruct H2 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto.
Qed.

Lemma reglist_lessdef rs1 rs2
      (LESSDEF: forall r, Val.lessdef (rs1 r) (rs2 r))
      l:
  Val.lessdef_list (reglist rs1 l) (reglist rs2 l).
Proof.
  induction l; simpl; auto.
Qed.

Lemma block_prop_impl (P Q: block -> Prop) v:
  (forall b, P b -> Q b) ->
  block_prop P v -> block_prop Q v.
Proof.
  destruct v; auto. simpl. intuition.
Qed.

Lemma free_extcall_args_inject_right j m m' sg_ ll lm sg m_ m'_ :
  forall (MS: match_stacks j ll lm sg sg_)
    (IAOOB: init_args_out_of_bounds sg_ m_)
    (MEXT: Mem.extends m_ m)
    (MINJ: Mem.inject j m m')
    (FEA: free_extcall_args (parent_sp init_sp lm) m' (regs_of_rpairs (loc_arguments sg)) = Some m'_)
    (INJ_FLAT: block_prop (fun b => j b = Some (b, 0)) init_sp)
    (INJ_UNIQUE: has_at_most_one_antecedent j init_sp)
    (BS: bounds_stack m ll),
    Mem.inject j m_ m'_.
Proof.
  intros MS IAOOB MEXT MINJ FEA INJ_FLAT INJ_UNIQUE BS.
  generalize (Mem.extends_inject_compose _ _ _ _ MEXT MINJ).
  revert FEA.
  cut (forall l2 l1,
          regs_of_rpairs(loc_arguments sg) = l1 ++ l2 ->
          free_extcall_args (parent_sp init_sp lm) m' l2 = Some m'_ ->
          Mem.inject j m_ m' ->
          Mem.inject j m_ m'_).
  {
    clear MEXT MINJ.
    intros HYP FEA MINJ.
    eapply HYP with (l1 := nil); eauto.
    reflexivity.
  }
  clear MINJ.
  intro l2. revert m' m'_; induction l2; simpl; intros m' m'_ l1 EQ FEA MINJ. congruence.
  generalize (IHl2 m' m'_ (l1 ++ a :: nil)). intro IHl2'.
  rewrite app_ass in IHl2'; simpl in IHl2'.
  specialize (IHl2' EQ).
  destruct a; simpl in *; auto.
  destruct sl; eauto.
  destruct (parent_sp init_sp lm) eqn:?; try discriminate.
  clear IHl2'.
  set (o := Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (4 * pos)))).
  fold o in FEA.
  destruct (Mem.free m' b o (o + size_chunk (chunk_of_type ty))) eqn:FREE; try discriminate.
  exploit Mem.free_right_inject; eauto.
  - intros b1 delta ofs k p JB PERM RNG.
    inv MS.
    + simpl in *.  subst. simpl in INJ_FLAT; red in INJ_UNIQUE.
      specialize (INJ_UNIQUE _ _ eq_refl _ _ _ _ INJ_FLAT JB). subst b1.
      assert (delta = 0) by congruence. subst delta.
      replace (ofs + 0) with ofs in * by omega.
      eapply IAOOB. eauto.
      rewrite EQ, in_app; simpl; eauto.
      unfold o in *; eauto.
      eapply Mem.perm_max.
      eapply Mem.perm_implies; eauto.
      constructor.
    + Opaque fe_stack_data.
      simpl in *. inv Heqv.
      specialize (INJ_UNIQUE0 _ _ JB).
      destruct INJ_UNIQUE0.
      subst.
      apply Mem.perm_max in PERM.
      assert (forall ofs p,
                 Mem.perm m_ b1 ofs Max p ->
                 0 <= ofs < Linear.fn_stacksize f) as BOUND.
      {
        intros ofss pp H3.
        eapply BS.
        eapply Mem.perm_extends; eauto.
      }
      specialize (BOUND _ _ PERM).
      rewrite INJ in JB; inv JB.
      revert RNG BOUND.
      rewrite size_type_chunk.
      generalize (bound_stack_data_stacksize f).
      unfold o in *.
      clear o.
      simpl. intros.
      generalize (frame_env_separated' (function_bounds f)).
      assert (In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) as IN.
      {
        rewrite EQ, ! in_app; simpl; auto.
      }
      generalize (loc_arguments_bounded _ _ _ IN); eauto.
      intros.
      assert (EQ4: Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + 4 * pos)) = fe_ofs_arg + 4 * pos).
      {
        apply Ptrofs.unsigned_repr.
        generalize (loc_arguments_bounded _ _ _ IN); eauto.
        simpl. intro.
        exploit loc_arguments_acceptable_2; eauto. intros [A B].
        split. omega.
        transitivity (4 * size_arguments sg). apply Z.mul_le_mono_nonneg_l. omega.
        generalize (typesize_pos ty); omega. auto.
      }
      simpl in EQ4. rewrite Ptrofs.add_zero_l, EQ4 in *.
      cut (4 * pos + AST.typesize ty <= fe_stack_data (make_env (function_bounds f))). omega.
      rewrite typesize_typesize.
      etransitivity.
      subst. simpl. rewrite <- Z.mul_add_distr_l. apply Z.mul_le_mono_nonneg_l. omega.
      apply ARGS. eauto.
      etransitivity.
      2: apply H1. apply align_le. destruct Archi.ptr64; omega.
  - intros.
    eapply (IHl2 m0 m'_ (l1 ++ S Outgoing pos ty :: nil)).
    rewrite EQ , app_ass; simpl; auto.
    eauto. auto.
Qed.

Lemma free_extcall_args_external_call sg_ ef args m_ t vl m'_ :
  forall (EC: external_call ef ge args m_ t vl m'_)
    j m m'
    (MEXT: Mem.extends m_ m)
    (MINJ: Mem.inject j m m')
    (IAOOB: init_args_out_of_bounds sg_ m_)
    ll lm
    (MS: match_stacks j ll lm (ef_sig ef) sg_)
    (SEP: m' |= stack_contents j ll lm ** globalenv_inject ge j)
    args'
    (ARGSINJ: Val.inject_list j args args')
    (IAIB: init_args_in_bounds sg_ m')
    (FLATINJ: block_prop (fun b : block => j b = Some (b, 0)) init_sp)
    (INJUNIQUE: has_at_most_one_antecedent j init_sp)
    (BS: bounds_stack m ll),
    exists m'_, free_extcall_args
             (parent_sp init_sp lm)
             m'
             (regs_of_rpairs (loc_arguments (ef_sig ef))) = Some m'_ /\
           exists t2 res2 m2,
             external_call ef ge args' m'_ t2 res2 m2.
Proof.
  intros EC j m m' MEXT MINJ IAOOB ll lm MS SEP args' ARGSINJ IAIB FLATINJ INJUNIQUE BS.
  exploit args_always_in_bounds; eauto.
  apply sep_proj1 in SEP; eauto.
  destruct 1.
  esplit.
  split; eauto.
  exploit free_extcall_args_inject_right; eauto.
  intros MINJ'.
  exploit external_call_mem_inject ; eauto.
  eapply globalenv_inject_preserves_globals.
  eapply sep_proj2 in SEP; eauto.
  destruct 1 as (? & ? & ? & ? & _).
  eauto.
Qed.

Lemma map_reg_lessdef rs1 rs2
      (LESSDEF: forall r: loc, Val.lessdef (rs1 r) (rs2 r))
      args:
  Val.lessdef_list (fun p => Locmap.getpair p rs1) ## args (fun p => Locmap.getpair p rs2) ## args.
Proof.
  induction args; simpl; auto.
  constructor; auto.
  destruct a; simpl; auto.
  apply Val.longofwords_lessdef; auto.
Qed.

Ltac constr_match_states :=
  econstructor;
  match goal with
    |- Linear2.state_lower _ = _ =>
    symmetry; eassumption
  | |- _ => idtac
  end.

Lemma intv_dec:
  forall a b c,
    { a <= b < c } + { b < a \/ b >= c }.
Proof.
  clear.
  intros.
  destruct (zle a b); destruct (zlt b c); try (right; omega); try (left; omega).
Qed.

Section EVAL_BUILTIN_ARG_LESSDEF.

  Variable A : Type.
  Variable ge' : Senv.t.
  Variables rs1 rs2 : A -> val.
  Hypothesis rs_lessdef: forall a, Val.lessdef (rs1 a) (rs2 a).
  Variables sp sp' : val.
  Hypothesis sp_lessdef: Val.lessdef sp sp'.
  Variable m m' : mem.
  Hypothesis m_ext: Mem.extends m m'.


  Lemma eval_builtin_arg_lessdef':
  forall arg v v'
    (EBA: eval_builtin_arg ge' rs1 sp m arg v)
    (EBA': eval_builtin_arg ge' rs2 sp' m' arg v'),
    Val.lessdef v v'.
  Proof.
    induction arg; intros; inv EBA; inv EBA'; subst; auto.
    - intros. exploit Mem.loadv_extends. eauto. apply H2.
      2: rewrite H3. simpl. apply Val.offset_ptr_lessdef; auto. intros (v2 & B & C). inv B. auto.
    - intros; apply Val.offset_ptr_lessdef; auto.
    - intros. exploit Mem.loadv_extends. eauto.  apply H3.
      2: rewrite H4. auto. intros (v2 & B & C). inv B. auto.
    - apply Val.longofwords_lessdef. eauto. eauto.
  Qed.

  Lemma eval_builtin_args_lessdef':
    forall args vl vl'
      (EBA: eval_builtin_args ge' rs1 sp m args vl)
      (EBA': eval_builtin_args ge' rs2 sp' m' args vl'),
      Val.lessdef_list vl vl'.
  Proof.
    induction args; simpl; intros. inv EBA; inv EBA'. constructor.
    inv EBA; inv EBA'. constructor; auto.
    eapply eval_builtin_arg_lessdef'; eauto.
  Qed.

End EVAL_BUILTIN_ARG_LESSDEF.

Lemma init_args_incr:
  forall j j' sg m,
    inject_incr j j' ->
    init_args_mach j sg m ->
    init_args_mach j' sg m.
Proof.
  red. intros j j' sg m INCR IAM sl of ty IN rs.
  exploit IAM; eauto. instantiate (1 := rs).
  intros (v & ea & inj); eexists; split; eauto.
Qed.

Lemma footprint_impl:
  forall P Q Q' b o,
    (forall b o, m_footprint Q b o -> m_footprint Q' b o) ->
    m_footprint (P ** Q) b o ->
    m_footprint (P ** Q') b o.
Proof.
  intros.
  destruct H0.
  left; auto.
  right; eauto.
Qed.

Lemma init_args_mach_unch:
  forall j sg m m' P,
    Mem.unchanged_on P m m' ->
    (forall b o, init_sp = Vptr b o -> forall i, P b i) ->
    init_args_mach j sg m ->
    init_args_mach j sg m'.
Proof.
  red. intros j sg m m' P UNCH NSP IAM sl of ty IN rs.
  exploit IAM; eauto. instantiate (1 := rs).
  intros (v & ea & inj); eexists; split; eauto.
  inv ea; constructor; auto.
  destruct init_sp; try discriminate.
  unfold load_stack in *. simpl in *.
  erewrite Mem.load_unchanged_on; eauto.
Qed.

Lemma inject_incr_sep_trans:
  forall f j j' im im' m m',
    inject_incr f j ->
    inject_incr j j' ->
    inject_separated f j im im' ->
    inject_separated j j' m m' ->
    Ple (Mem.nextblock im) (Mem.nextblock m) ->
    Ple (Mem.nextblock im') (Mem.nextblock m') ->
    inject_separated f j' im im'.
Proof.
  clear.
  red. intros f j j' im im' m m' INCR INCR' SEP SEP' PLE PLE' b1 b2 delta FB J'B.
  destruct (j b1) as [ (b & delta') | ] eqn: JB.
  exploit INCR'. apply JB. rewrite J'B. injection 1. intros; subst.
  exploit SEP; eauto.
  exploit SEP'; eauto.
  unfold Mem.valid_block; intuition xomega.
Qed.

Theorem transf_step_correct:
  forall s1 t s2, Linear2.step ge s1 t s2 ->
  forall (WTS: wt_state init_ls (Linear2.state_lower s1)) s1' (MS: match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1;
    clear step_ge_eq_before step_ge_eq_after.
 inversion step_low; subst; intros;
  inv MS; (try congruence);
  (repeat
  match goal with
      K1: _ = Linear2.state_lower ?s1,
      K2: Linear2.state_lower ?s1 = _
      |- _ =>
      rewrite K2 in K1;
        symmetry in K1;
        inv K1
  end);
  try rewrite transl_code_eq;
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.

  - (* Lgetstack *)
    destruct BOUND as [BOUND1 BOUND2].
    exploit wt_state_getstack; eauto. intros SV.
    unfold destroyed_by_getstack; destruct sl.
    + (* Lgetstack, local *)
      exploit frame_get_local; eauto. intros (v & A & B).
      econstructor; split.
      apply plus_one. apply exec_Mgetstack. exact A.
      constr_match_states.
      4: apply agree_regs_set_reg; eauto.
      4: apply agree_locs_set_reg; eauto.
      all: eauto with mem.
      eapply is_tail_cons_left; eauto.
      revert Hno_init_args.
      generalize (Linear2.state_invariant s1). rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in *; now intuition congruence.
      congruence.

    + (* Lgetstack, incoming *)
      unfold slot_valid in SV. InvBooleans.
      exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
      inversion STACKS; clear STACKS.
      subst. destruct TP as [TP | TP] .
      * elim (TP _ IN_ARGS).
      * assert (init_args_mach j init_sg m') as INIT_ARGS_MACH.
        {

          apply sep_proj2 in SEP. apply sep_proj2 in SEP.
          apply sep_proj1 in SEP. destruct SEP. simpl in H3; subst; auto.
        }
        exploit frame_get_parent; eauto.
        intro PARST. Opaque Z.mul bound_outgoing.
        subst.
        exploit INIT_ARGS_MACH. eauto. intros (v & EA & EAinj).
        esplit.
        -- split.
           ++ eapply plus_one.
              econstructor; eauto.
              exploit unfold_transf_function; eauto.
              intro; subst tf; eauto.
              simpl. inv EA. eauto.
           ++ constr_match_states.
              constructor; auto. all: eauto with mem.
              ** apply agree_regs_set_reg; auto.
                 change (rs0 # temp_for_parent_frame <- Vundef)
                 with (undef_regs (destroyed_by_getstack Incoming) rs0).
                 eapply agree_regs_undef_regs; eauto.
                 erewrite agree_incoming. eauto. eauto. eauto.
              ** apply agree_locs_set_reg; eauto.
                 apply agree_locs_set_reg; eauto.
                 apply caller_save_reg_within_bounds.
                 reflexivity.
              ** eapply is_tail_cons_left; eauto.
              ** revert Hno_init_args.
                 generalize (Linear2.state_invariant s1). rewrite Hs2.
                 inversion step_high; inversion 1; subst; simpl in *; now intuition congruence.
              ** congruence.

      * subst sg isg.
        subst s cs'.
        exploit frame_get_outgoing.
        apply sep_proj2 in SEP. simpl in SEP. rewrite sep_assoc in SEP. eexact SEP.
        eapply ARGS; eauto.
        eapply slot_outgoing_argument_valid; eauto.
        intros (v & A & B).
        econstructor; split.
        -- apply plus_one. eapply exec_Mgetparam; eauto.
           rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs.
           eapply frame_get_parent. eexact SEP.
        -- constr_match_states.
           now (econstructor; eauto).
           all: eauto.
           ++ apply agree_regs_set_reg; auto.
              change (rs0 # temp_for_parent_frame <- Vundef)
              with (undef_regs (destroyed_by_getstack Incoming) rs0).
              eapply agree_regs_undef_regs; eauto.
              erewrite agree_incoming. eauto. eauto. eauto.
           ++ apply agree_locs_set_reg; eauto.
              apply agree_locs_set_reg; eauto.
              apply caller_save_reg_within_bounds.
              reflexivity.
           ++ eapply is_tail_cons_left; eauto.
           ++ revert Hno_init_args.
              generalize (Linear2.state_invariant s1). rewrite Hs2.
              inversion step_high; inversion 1; subst; simpl in *; now intuition congruence.
           ++ congruence.

    + (* Lgetstack, outgoing *)
      exploit frame_get_outgoing; eauto. intros (v & A & B).
      econstructor; split.
      apply plus_one. apply exec_Mgetstack. exact A.
      constr_match_states. all: eauto with coqlib.
      apply agree_regs_set_reg; auto.
      apply agree_locs_set_reg; auto.
      revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
      congruence.

  - (* Lsetstack *)
    exploit wt_state_setstack; eauto. intros (SV & SW).
    set (ofs' := match sl with
                 | Local => offset_local (make_env (function_bounds f)) ofs
                 | Incoming => 0 (* dummy *)
                 | Outgoing => offset_arg ofs
                 end).
    eapply frame_undef_regs with (rl := destroyed_by_setstack ty) in SEP.
    assert (A: exists m'',
               store_stack m' (Vptr sp' Ptrofs.zero) ty (Ptrofs.repr ofs') (rs0 src) = Some m''
               /\ m'' |= frame_contents f j sp' (Locmap.set (S sl ofs ty) (rs (R src))
                                                           (LTL.undef_regs (destroyed_by_setstack ty) rs))
                     (parent_locset init_ls s) (parent_sp init_sp cs') (parent_ra init_ra cs')
                     ** stack_contents j s cs' ** (mconj (minjection j m) (minit_args_mach j sg_)) ** globalenv_inject ge j
           ).
    {
      unfold ofs'; destruct sl; try discriminate.
      eapply frame_set_local; eauto.
      eapply frame_set_outgoing; eauto.
    }
    clear SEP; destruct A as (m'' & STORE & SEP).
    econstructor; split.
    + apply plus_one. destruct sl; try discriminate.
      econstructor. eexact STORE. eauto.
      econstructor. eexact STORE. eauto.
    + constr_match_states. all: eauto with coqlib. 
      * apply agree_regs_set_slot. apply agree_regs_undef_regs. auto.
      * apply agree_locs_set_slot. apply agree_locs_undef_locs. auto. apply destroyed_by_setstack_caller_save. auto.
      * eapply block_prop_impl; try eassumption.
        unfold store_stack, Val.offset_ptr, Mem.storev in STORE. eauto with mem.
      * unfold store_stack in STORE. etransitivity. apply INIT_VB'.
        simpl in STORE. rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE). apply Ple_refl. 
      * revert Hno_init_args.
        generalize (Linear2.state_invariant s1).
        rewrite Hs2.
        inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
      * congruence.
      * unfold store_stack in STORE. eapply init_args_in_bounds_storev; eauto.

- (* Lop *)
  assert (OP_INJ:
            exists v',
              eval_operation ge (Vptr sp' Ptrofs.zero)
                             (transl_op (make_env (function_bounds f)) op) rs0##args m' = Some v' /\
              Val.inject j v v').
  {
    eapply eval_operation_inject; eauto.
    eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2.
    eapply sep_proj2. eexact SEP.
    eapply agree_reglist; eauto.
    apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. apply SEP.
  }
  destruct OP_INJ as [v' [A B]].
  econstructor; split.
  + apply plus_one. econstructor.
    instantiate (1 := v'). rewrite <- A. apply eval_operation_preserved.
    exact symbols_preserved. eauto.
  + constr_match_states. all: eauto with coqlib.
    * apply agree_regs_set_reg; auto.
      rewrite transl_destroyed_by_op.  apply agree_regs_undef_regs; auto.
    * apply agree_locs_set_reg; auto. apply agree_locs_undef_locs. auto. apply destroyed_by_op_caller_save.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
    * congruence.
    * apply frame_set_reg. apply frame_undef_regs. exact SEP.

- (* Lload *)
  assert (ADDR_INJ:
            exists a',
              eval_addressing ge (Vptr sp' Ptrofs.zero)
                              (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a' /\
              Val.inject j a a').
  {
    eapply eval_addressing_inject; eauto.
    eapply globalenv_inject_preserves_globals.
    eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
    eapply agree_reglist; eauto.
  }
  destruct ADDR_INJ as [a' [A B]].
  exploit loadv_parallel_rule.
  apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. apply SEP.
  eauto. eauto. 
  intros [v' [C D]].
  econstructor; split.
  + apply plus_one. econstructor.
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
    eexact C. eauto.
  + constr_match_states. all: eauto with coqlib.
    * apply agree_regs_set_reg. rewrite transl_destroyed_by_load. apply agree_regs_undef_regs; auto. auto.
    * apply agree_locs_set_reg. apply agree_locs_undef_locs. auto. apply destroyed_by_load_caller_save. auto.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
    * congruence.

- (* Lstore *)
  assert (STORE_INJ:
            exists a',
              eval_addressing ge (Vptr sp' Ptrofs.zero)
                              (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a' /\
              Val.inject j a a').
  {
    eapply eval_addressing_inject; eauto.
    eapply globalenv_inject_preserves_globals.
    eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
    eapply agree_reglist; eauto.
  }
  destruct STORE_INJ as [a' [A B]].
  rewrite sep_swap3 in SEP.
  exploit storev_parallel_rule.
  eapply mconj_proj1. eexact SEP.
  eauto.
  eauto.
  apply AGREGS.
  rename SEP into SEP_init.
  intros (m1' & C & SEP).
  rewrite sep_swap3 in SEP.
  econstructor; split.
  + apply plus_one. econstructor.
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
    eexact C. eauto.
  + revert Hno_init_args.
    generalize (Linear2.state_invariant s1).
    rewrite Hs2.
    inversion step_high; inversion 1; subst; simpl in * |- * ; try now intuition congruence.
    exploit eval_addressing_lessdef_strong. 2: apply sp_lessdef. apply reglist_lessdef.
    eauto. eauto. intros (v2 & EA & LD).
    rewrite EA in H1; inv H1.
    destruct a0; try discriminate. inv LD. inv B. simpl in *.
    intro OOB.
    constr_match_states. all: eauto with coqlib.
    * rewrite transl_destroyed_by_store. apply agree_regs_undef_regs; auto.
    * apply agree_locs_undef_locs. auto. apply destroyed_by_store_caller_save.
    * eapply block_prop_impl; try eassumption.
      eauto with mem.
    * etransitivity. apply INIT_VB.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H2). apply Ple_refl.
    * etransitivity. apply INIT_VB'.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ C). apply Ple_refl.
    * rewrite <- H3. simpl.
      eapply init_args_out_of_bounds_store; eauto.
    * congruence.
    * eapply init_args_in_bounds_store; eauto.
    * eapply frame_undef_regs; eauto.
      rewrite sep_swap23, sep_swap12.
      rewrite sep_swap23, sep_swap12 in SEP.
      apply mconj_intro. auto.
      split; [|split].
      2: eapply sep_proj2; eauto.
      -- simpl. red; simpl. intros sl of ty IN rs2.
         exploit mconj_proj2. eexact SEP_init. intro D; apply sep_proj1 in D.
         simpl in D. red in D. generalize IN; intro IN'. eapply D with (rs := rs2) in IN.
         clear D. destruct IN as (v & EA' & INJ).
         inv EA'.
         eexists; split; eauto. constructor.
         unfold load_stack in H11 |- *. clear SEP_init. clear init_sp_int.
         clearbody step.
         destruct init_sp eqn:?; simpl in *; try discriminate.
         erewrite Mem.load_store_other. eauto. eauto.
         destruct (eq_block b1 b2); auto.
         assert (b0 = b1).
         clear - H8 e INJ_INIT_SP HAMOA SP_NOT_INIT external_calls_prf. subst.
         eapply HAMOA; eauto.
         subst b1. subst b0. assert (delta = 0) by congruence. subst delta.
         rewrite Ptrofs.add_zero in *.
         destruct (zle (Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr (4*of))) + size_chunk (chunk_of_type ty))
                       (Ptrofs.unsigned i)); auto.
         destruct (zle (Ptrofs.unsigned i + size_chunk chunk)
                       (Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr (4 * of))))); auto.

         cut (exists o,
                 Ptrofs.unsigned i <= o < Ptrofs.unsigned i + size_chunk chunk /\
                 Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr (fe_ofs_arg + 4 * of))) <= o <
                 Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr (fe_ofs_arg + 4 * of))) + size_chunk (chunk_of_type ty)).
         intros (o & RNG1 & RNG2).

         exfalso.
         exploit OOB. eauto.
         eauto. eauto.
         eapply Mem.store_valid_access_3 in H5. destruct H5.
         eapply Mem.perm_cur_max. eapply Mem.perm_implies. eapply H1.
         eauto. constructor. auto.

         simpl.
         exists (Z.max (Ptrofs.unsigned i) (Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr (4*of))))).
         repeat split.
         apply Zmax_bound_l. omega.
         rewrite Zmax_spec. destruct (zlt _ _). destruct chunk; simpl; omega. omega.
         apply Zmax_bound_r. omega.
         rewrite Zmax_spec. destruct (zlt _ _). omega. destruct (chunk_of_type ty); simpl; omega.
      -- apply mconj_proj2 in SEP_init.
         apply sep_swap23 in SEP_init. destruct SEP_init as (A1 & A2 & A3).
         revert A3. auto.
    * intros; eapply PERM_stack; eauto.
      eauto with mem.
    * eapply bounds_stack_store; eauto.

- (* Lcall *)
  exploit find_function_translated; eauto.
  eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [bf [tf' [A [B C]]]].
  exploit is_tail_transf_function; eauto. intros IST.
  rewrite transl_code_eq in IST. simpl in IST.
  exploit return_address_offset_exists. eexact IST. intros [ra D].
  econstructor; split.
  + apply plus_one. econstructor; eauto.
  + constr_match_states; eauto.
    * econstructor; eauto with coqlib.
      apply Val.Vptr_has_type.
      intros; red.
      apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
      apply loc_arguments_bounded; auto.
      etransitivity. apply Z.mul_le_mono_nonneg_l. omega. apply BOUND.
      etransitivity. 2: eapply size_no_overflow; eauto.
      transitivity (fe_stack_data (make_env (function_bounds f))).
      generalize (frame_env_separated' (function_bounds f)). simpl. clear. intros. decompose [and] H.
      change (Z.max (max_over_instrs f outgoing_space) (max_over_slots_of_funct f outgoing_slot) ) with
      (bound_outgoing (function_bounds f)).
      etransitivity.
      2: apply H7. apply align_le. destruct Archi.ptr64; omega.
      generalize (frame_env_range (function_bounds f)).
      generalize (bound_stack_data_pos (function_bounds f)). simpl.
      omega. 
    * simpl; red; auto.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
    * congruence.
    * simpl. rewrite sep_assoc. exact SEP.
    * simpl. split; auto.

- (* Ltailcall *)
  rewrite (sep_swap (stack_contents j s cs')) in SEP.
  exploit function_epilogue_correct; eauto.
  rewrite sep_swap12. eapply mconj_proj1. rewrite sep_swap12. eauto.
  rename SEP into SEP_init. intros (rs1 & m1' & P & Q & R & S & T & U & SEP).
  inv Hinit_ls.
  rewrite sep_swap in SEP.
  exploit find_function_translated; eauto.
  eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [bf [tf' [A [B C]]]].
  econstructor; split.
  + eapply plus_right. eexact S. econstructor; eauto. traceEq.
  + assert (TAILCALL: tailcall_possible (Linear.funsig f')).
    {
      apply zero_size_arguments_tailcall_possible. eapply wt_state_tailcall; eauto.
    }
    exploit match_stacks_change_sig. eauto. eauto.
    erewrite wt_state_tailcall. vm_compute. congruence. eauto.
    intros MS'.
    constr_match_states.  all: eauto. subst; eauto.
    * etransitivity. apply INIT_VB.
      rewrite (Mem.nextblock_free _ _ _ _ _ H5). apply Ple_refl.
    * etransitivity. apply INIT_VB'.
      rewrite (Mem.nextblock_free _ _ _ _ _ R). apply Ple_refl.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      destruct s eqn:?.
      -- clear H1. subst.
         intros _.
         clear - TAILCALL. red; red; intros.
         apply TAILCALL in H0. easy.
      -- eapply init_args_out_of_bounds_free; eauto.
    * congruence.
    * destruct s eqn:?.
      -- eapply tailcall_possible_in_bounds; eauto.
      -- eapply init_args_in_bounds_free; eauto.
    * eapply block_prop_impl; try eassumption.
      eauto with mem.
    * rewrite sep_swap12.
      eapply mconj_intro. rewrite sep_swap12; eauto.
      split. 2:split.
      -- simpl. clear H1. inv MS'. inv STACKS. simpl in *.
         ++ red.
            intros sl of ty H rs2.
            elim (TAILCALL _ H).
         ++ rewrite sep_swap12 in SEP_init. apply mconj_proj2 in SEP_init. apply sep_proj1 in SEP_init.
            red; intros.
            exploit SEP_init. eauto. instantiate (1 := rs2). intros (v & ea & VINJ).
            econstructor; split; eauto.
            inv ea; constructor.
            clear SEP_init. clear init_sp_int.
            clearbody step.
            destruct init_sp eqn:?; try discriminate.
            unfold load_stack in H7 |- *; simpl in *.
            erewrite Mem.load_free. eauto. eauto. eauto.
      -- eapply sep_proj2. apply sep_swap12. eauto.
      -- apply sep_proj2 in SEP_init. apply mconj_proj2 in SEP_init.
         destruct SEP_init as (A1 & A2 & A3). revert A3. destruct s; auto.
         red; intros.
         eapply A3; eauto.
         destruct H. decompose [ex and] H.
         exploit TAILCALL. apply H4. simpl. easy.
    * eapply bounds_stack_free; eauto.

- (* Lbuiltin *)
  destruct BOUND as [BND1 BND2].
  exploit transl_builtin_args_correct.
  eauto. eauto.
  rewrite sep_swap12.
  rewrite sep_swap12 in SEP. apply sep_proj2 in SEP.
  rewrite sep_swap12 in SEP. apply mconj_proj1 in SEP. eauto.
  eauto. rewrite <- forallb_forall. eapply wt_state_builtin; eauto.
  exact BND2.
  intros [vargs' [P Q]].
  assert (m'0
            |= minjection j m **
            globalenv_inject ge j **
            frame_contents f j sp' rs (parent_locset init_ls s) (parent_sp init_sp cs')
            (parent_ra init_ra cs') **
            stack_contents j s cs').
  {
    eapply mconj_proj1.
    rewrite sep_rot, sep_rot. eexact SEP.
  }
  exploit (external_call_parallel_rule).
  3: eassumption.
  {
    repeat
    match goal with
        [ |- context [m_invar_weak (?U ** ?V)] ] =>
        replace (m_invar_weak (U ** V))
                with (m_invar_weak U || m_invar_weak V)
          by reflexivity
    end.
    rewrite frame_contents_invar_weak.
    rewrite stack_contents_invar_weak.
    reflexivity.
  }
  all: eauto.
  rename SEP into SEP_init; intros (j' & res' & m1' & EC & RES & SEP & INCR & ISEP).
  econstructor; split.
  + apply plus_one. econstructor; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  + constr_match_states.
    4: apply agree_regs_set_res; auto. 4: apply agree_regs_undef_regs; auto. 4: eapply agree_regs_inject_incr; eauto.
    4: eauto.
    4: apply agree_locs_set_res; auto. 4: apply agree_locs_undef_regs; auto.
    eapply match_stacks_change_meminj; eauto. all: eauto.
    * exists m, m'0; split; auto.
      intros. eapply Mem.valid_block_inject_2; eauto.
      apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init.
      apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init.
      simpl in SEP_init. eauto.
    * intros.
      destruct (j b0) eqn:?. destruct p.
      generalize (INCR _ _ _ Heqo). intros. rewrite H4 in H3; inv H3.
      eapply INJUNIQUE; eauto.
      generalize (ISEP _ _ _ Heqo H3).
      intros (A & B).
      apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init.
      apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init.
      simpl in SEP_init. simpl in SEP_init.
      exploit Mem.valid_block_inject_2. apply INJSP. eauto. congruence.
    * revert INJ_INIT_SP. revert INCR. clear. destruct init_sp; simpl; auto.
    * eapply has_at_most_one_antecedent_incr; eauto.
    * eapply block_prop_impl; try eassumption.
      intro; eapply external_call_valid_block; eauto.
    * eapply inject_incr_trans; eauto.
    * eapply inject_incr_sep_trans; eauto.
    * etransitivity. apply INIT_VB.
      eapply external_call_nextblock; eauto.
    * etransitivity. apply INIT_VB'.
      eapply external_call_nextblock; eauto.
    * eauto with coqlib.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      eapply init_args_out_of_bounds_external_call; eauto.
      intros.
      rewrite H7 in INJ_INIT_SP; inversion INJ_INIT_SP.
      rewrite Mem.valid_block_extends.
      eapply Mem.valid_block_inject_1; eauto.
      apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init.
      apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init.
      simpl in SEP_init. eauto.
      eauto.
      apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init.
      apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init.
      simpl in SEP_init. eauto.
    * congruence.
    * revert Hsome_init_args Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      intros IAIB IAOOB.
      eapply init_args_in_bounds_external_call. eexact H6.
      eapply globalenv_inject_preserves_globals.
      apply sep_pick2 in H. eauto.
      all: eauto.
      -- intros.
         revert INJ_INIT_SP INCR H7. clear. intros. subst. simpl in *; auto.
      -- revert HAMOA INJ_INIT_SP INCR ISEP ISP'VALID. clear.
         intros; subst; simpl in *; auto.
         specialize (HAMOA _ _ eq_refl _ _ _ _ INJ_INIT_SP H0). subst.
         rewrite H0 in INJ_INIT_SP. inv INJ_INIT_SP. auto.
      -- apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init.
         apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init.
         simpl in SEP_init. eauto.
      -- eapply val_list_lessdef_inject_compose. 2: apply Q.
         exploit Events.eval_builtin_args_lessdef. apply rs_lessdef. apply m_ext. eauto.
         intros (vl2 & EBA & LDL).
         eapply Val.lessdef_list_trans. eauto.
         eapply Events.eval_builtin_args_lessdef'. 3: eauto. 3: eauto. all: eauto.
    * apply frame_set_res. apply frame_undef_regs. apply frame_contents_incr with j; auto.
      rewrite sep_swap2. apply stack_contents_change_meminj with j; auto. rewrite sep_swap2.
      rewrite sep_swap23, sep_swap12.
      apply mconj_intro. rewrite <- ! sep_assoc.
      rewrite sep_comm. rewrite ! sep_assoc. rewrite sep_swap12. eauto.
      split.
      rewrite sep_swap23, sep_swap12 in SEP_init. apply mconj_proj2 in SEP_init.
      apply sep_proj1 in SEP_init. revert SEP_init.
      -- simpl.
         revert Hsome_init_args Hno_init_args.
         generalize (Linear2.state_invariant s1).
         rewrite Hs2.
         inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
         intros IAIB IAOOB.
         exploit eval_builtin_args_lessdef'. eauto. eauto. eauto. eauto. eauto. intro LDlist.
         exploit external_call_mem_extends. apply H6. eauto. eauto.
         intros (vres' & m2' & EC2 & LDres & EXTres & UNCH).
         exploit external_call_determ. eexact H2. eexact EC2.
         intros (A & B). intuition subst. clear H2.
         exploit external_call_mem_inject.
         3: eapply Mem.extends_inject_compose. 3: apply m_ext.
         3: apply sep_proj1 in H; simpl in H; eauto.
         eapply globalenv_inject_preserves_globals.
         apply sep_pick2 in H; eauto.
         eauto.
         eapply val_list_lessdef_inject_compose. 2: apply Q.
         auto.
         intros (f' & vres'0 & m2'0 & EC3 & INJres & MINJres & UNCH' & UNCH3 & INCR2 & SEP2).
         exploit external_call_determ.
         eexact EC. eexact EC3. intuition subst.
         revert HAMOA INJ_INIT_SP UNCH3 SEP_init IAOOB INCR. clear - external_calls_prf.
         red; intros.
         exploit SEP_init. eauto. instantiate (1 := rs).
         intros (v & ea & inj); eexists; split; eauto.
         inv ea; constructor; eauto.
         destruct init_sp eqn:?; simpl in *; try discriminate.
         unfold load_stack in *; simpl in *.
         eapply Mem.load_unchanged_on. eexact UNCH3. 2: eauto.
         red; red; intros.
         exploit IAOOB; eauto.
         exploit HAMOA. eauto. apply INJ_INIT_SP. apply H1.
         intro. subst b0.
         assert (delta = 0) by congruence. subst delta.
         rewrite Zminus_0_r in H2; eauto.
      -- split. apply sep_proj2 in SEP. rewrite sep_comm in SEP. rewrite <- sep_assoc.  eauto.
         rewrite sep_swap23, sep_swap12 in SEP_init.
         apply mconj_proj2 in SEP_init.
         destruct SEP_init as (A1 & A2 & A3).
         revert A3.
         clear - INCR. red; simpl.
         intros. decompose [ex and] H. clear H.
         exploit A3. simpl. repeat eexists; eauto.
         revert H0.
         eapply footprint_impl.
         intros b0 o; apply footprint_impl.
         simpl. auto. auto.
    * intros.
      exploit external_call_max_perm. eexact H2. 2: apply H3.
      eapply Mem.valid_block_inject_1; eauto.
      apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init.
      apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init.
      simpl in SEP_init. eauto.
      apply PERM_stack.
    * eapply bounds_stack_perm. eauto. eapply match_stacks_valid_stack; eauto.
      apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init.
      apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init.
      simpl in SEP_init. eauto.
      intros. eapply external_call_max_perm. 3: eauto. eauto. eauto.

- (* Llabel *)
  econstructor; split.
  apply plus_one; apply exec_Mlabel.
  constr_match_states.
  all: eauto with coqlib.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lgoto *)
  econstructor; split.
  apply plus_one; eapply exec_Mgoto; eauto.
  apply transl_find_label; eauto.
  constr_match_states; eauto.
  eapply find_label_tail; eauto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lcond, true *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_true; eauto.
  eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto.
  apply sep_pick3 in SEP. destruct SEP. exact H. auto.
  eapply transl_find_label; eauto.
  constr_match_states. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto. 
  apply agree_locs_undef_locs. auto. apply destroyed_by_cond_caller_save.
  all: eauto.
  eapply find_label_tail; eauto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lcond, false *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_false; eauto.
  eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto.
  apply sep_pick3 in SEP. destruct SEP. exact H. auto.
  constr_match_states. eauto. eauto. eauto.
  apply agree_regs_undef_regs; eauto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_cond_caller_save.
  all: eauto.
  eauto with coqlib.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Ljumptable *)
  assert (rs0 arg = Vint n).
  { generalize (AGREGS arg). rewrite H1. intro IJ; inv IJ; auto. }
  econstructor; split.
  apply plus_one; eapply exec_Mjumptable; eauto.
  apply transl_find_label; eauto.
  constr_match_states. eauto. eauto. eauto.
  apply agree_regs_undef_regs; eauto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_jumptable_caller_save.
  all: eauto.
  eapply find_label_tail; eauto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lreturn *)
  rewrite (sep_swap (stack_contents j s cs')) in SEP.
  exploit function_epilogue_correct; eauto.
  rewrite sep_swap12 in SEP |- *.
  apply mconj_proj1 in SEP; eauto.
  intros (rs' & m1' & A & B & C & D & E & F & G).
  econstructor; split.
  eapply plus_right. eexact D. econstructor; eauto. traceEq.
  inv Hinit_ls.
  constr_match_states. all: try subst; eauto.
  + etransitivity. apply INIT_VB.
    rewrite (Mem.nextblock_free _ _ _ _ _ H2). apply Ple_refl.
  + etransitivity. apply INIT_VB'.
    rewrite (Mem.nextblock_free _ _ _ _ _ C). apply Ple_refl.
  + revert Hno_init_args.
    generalize (Linear2.state_invariant s1).
    rewrite Hs2.
    inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
    intros; eapply init_args_out_of_bounds_free; eauto.
  + congruence.
  + eapply init_args_in_bounds_free; eauto.
  + eapply block_prop_impl; try eassumption.
    eauto with mem.
  + rewrite sep_swap.
    eapply frame_mconj. apply sep_drop in SEP. apply SEP. exact G.
    simpl.
    red; intros.
    apply sep_proj2 in SEP.
    apply mconj_proj2 in SEP.
    apply sep_pick1 in SEP.
    exploit SEP. eauto. instantiate (1 := rs1). intros (v & ea & VINJ).
    econstructor; split; eauto.
    inv ea; constructor.
    clear SEP. clear init_sp_int.
    clearbody step.
    destruct init_sp eqn:?; try discriminate.
    unfold load_stack in H7 |- *; simpl in *.
    erewrite Mem.load_free. eauto. eauto. eauto.
  + eapply bounds_stack_free; eauto.

- (* internal function *)
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  destruct (transf_function f) as [tfn|] eqn:TRANSL; simpl; try congruence.
  intros EQ; inversion EQ; clear EQ; subst tf.
  rewrite <- sep_assoc, sep_comm in SEP.
  rewrite <- sep_assoc, sep_comm in SEP.
  exploit function_prologue_correct.
  eassumption.
  eassumption.
  eassumption.
  red; intros; eapply wt_callstate_wt_regs; eauto.
  reflexivity.
  reflexivity.
  eassumption.
  eapply match_stacks_type_sp; eauto.
  eapply match_stacks_type_retaddr; eauto.
  eapply mconj_proj1; eassumption.
  rename SEP into SEP_init;
  intros (j' & rs' & m2' & sp' & m3' & m4' & m5' & A & B & C & D & E & F & SEP & J & K & KSEP & KV & KV' & PERMS & UNCH).
  econstructor; split.
  + eapply plus_left. econstructor; eauto.
    rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body.
    eexact D. traceEq.
  + constr_match_states.
    eapply match_stacks_change_meminj; eauto. all: eauto with coqlib.
    * exists m, m'0; split; eauto.
      intros.
      eapply Mem.valid_block_inject_2; eauto.
      apply mconj_proj1 in SEP_init; apply sep_proj1 in SEP_init; simpl in SEP_init ; eauto.
    * intros.
      destruct (j b) eqn:?. destruct p.
      exploit K. apply Heqo. rewrite H. intro Z; inv Z.
      eapply Mem.valid_block_inject_2 in Heqo.
      2:       apply mconj_proj1 in SEP_init; apply sep_proj1 in SEP_init; simpl in SEP_init ; eauto.
      eapply Mem.fresh_block_alloc in A. congruence.
      generalize (KSEP _ _ _ Heqo H).
      intros (VB1 & VB2).
      eapply Mem.valid_block_inject_1 in H.
      2:   apply sep_proj2 in SEP; apply sep_proj1 in SEP; simpl in SEP ; eauto.
      clear - VB1 H H1 external_calls_prf.
      unfold Mem.valid_block in *.
      exploit Mem.nextblock_alloc; eauto.
      exploit Mem.alloc_result; eauto. intros; subst.
      rewrite H2 in H.
      apply Plt_succ_inv in H; destruct H; congruence.
    * revert INJ_INIT_SP K; clear. destruct init_sp; simpl; auto.
    * eapply has_at_most_one_antecedent_incr; eauto.
    * eapply block_prop_impl; eauto.
    * eapply inject_incr_trans; eauto.
    * eapply inject_incr_sep_trans; eauto.
    * etransitivity. apply INIT_VB.
      apply Ple_Plt. apply KV.
    * etransitivity. apply INIT_VB'.
      apply Ple_Plt. apply KV'.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      eapply init_args_out_of_bounds_alloc. eauto.
      {
        revert ISP'VALID.
        apply mconj_proj1 in SEP_init; apply sep_proj1 in SEP_init; simpl in SEP_init ; eauto.
        clear - m_ext SEP_init memory_model_prf INJ_INIT_SP.
        destruct init_sp; simpl; auto. intros.
        rewrite Mem.valid_block_extends. 2: eauto.
        eapply Mem.valid_block_inject_1; eauto.
      }
      eauto. eauto.
      apply mconj_proj1 in SEP_init; apply sep_proj1 in SEP_init; simpl in SEP_init ; eauto.
    * congruence.
    * unfold store_stack in *.
      eapply init_args_in_bounds_perm.
      intros b o_ H o k p. apply PERMS. eauto.
    * apply mconj_proj1 in SEP_init; apply sep_proj1 in SEP_init; simpl in SEP_init ; eauto.
      revert SEP_init INJ_INIT_SP A . clear - memory_model_prf.
      intros; subst. inversion INJ_INIT_SP.
      eapply Mem.fresh_block_alloc in A. simpl in *.
      eapply Mem.valid_block_inject_2 in INJ_INIT_SP; eauto. congruence.
    *
      rewrite sep_rot in SEP. rewrite sep_swap12.
      eapply stack_contents_change_meminj; eauto.
      rewrite sep_swap23, sep_swap12.
      eapply mconj_intro.
      rewrite sep_swap12, sep_swap23. eexact SEP.
      split;[|split].
      -- simpl.
         apply mconj_proj2 in SEP_init. apply sep_proj1 in SEP_init.
         eapply init_args_mach_unch; eauto. simpl.
         revert ISP'VALID A. clear - external_calls_prf. destruct init_sp; simpl; try congruence.
         intros.
         eapply Mem.fresh_block_alloc in A. inv H. congruence.
         eapply init_args_incr; eauto.
      -- rewrite sep_swap23, sep_swap12 in SEP. apply sep_proj2 in SEP. assumption.
      --
        apply mconj_proj2 in SEP_init.
        destruct SEP_init as (A1 & A2 & A3). revert A3.
        red. simpl.
        intros.
        exploit A3. simpl. eauto.
        destruct H2. right; auto.
        destruct H2. 2: left; auto.
        simpl in H2.
        assert ( b = sp' ).
        clear - H2.
        repeat match goal with
                 H : m_footprint _ _ _ \/ m_footprint _ _ _ |- _ => destruct H; auto
               | H : m_footprint _ _ _ |- _ => destruct H; auto
               end.
        revert H.
        generalize (used_callee_save (function_bounds f))
                   (fe_ofs_callee_save (make_env (function_bounds f)))
                   (parent_locset init_ls s).
        induction l; simpl; intros. easy.
        destruct H; auto. destruct H. auto. eauto.
        clear - A ISP'VALID H H3.
        decompose [ex and] H.
        exfalso. subst. eapply Mem.fresh_block_alloc; eauto. tauto.
    * intros. eapply Mem.perm_alloc_3; eauto.
    * eapply bounds_stack_perm. eauto.
      eapply match_stacks_valid_stack.
      eauto.
      apply mconj_proj1 in SEP_init; apply sep_proj1 in SEP_init; eauto.
      intros.
      eapply Mem.perm_alloc_4; eauto.
      eapply Mem.fresh_block_alloc in H1. congruence.

- (* external function *)
  simpl in TRANSL. inversion TRANSL; subst tf.
  exploit transl_external_arguments; eauto. apply sep_proj1 in SEP; eauto.
  { (* init_args_mach *)
    eapply sep_drop in SEP.
    eapply mconj_proj2 in SEP.
    eapply sep_proj1 in SEP.
    simpl in SEP; eauto.
  }
  intros [vl [ARGS VINJ]].
  assert (SEP_init := SEP).
  rewrite <- sep_swap12 in SEP. apply mconj_proj1 in SEP.
  rewrite (sep_comm _ (globalenv_inject _ _)) in SEP.
  exploit external_call_parallel_rule; eauto.
  {
    rewrite stack_contents_invar_weak. reflexivity.
  }
  intros (j' & res' & m1' & A & B & C & D & E).
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
	rewrite Hs2.
	inversion step_high; inversion 1; subst; try (simpl in * |- * ; now intuition congruence).
  intro Hno_init_args.
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  {
	  inversion f_eq; subst.
    exploit free_extcall_args_external_call. all: eauto.
    rewrite sep_swap12 in SEP_init. apply mconj_proj1 in SEP_init.
    apply sep_proj1 in SEP_init. simpl in SEP_init. eauto.
    rewrite sep_swap12 in SEP_init.
    apply sep_drop in SEP_init. eauto.
	  eapply val_list_lessdef_inject_compose; eauto.
    apply map_reg_lessdef; auto.
    intros (m'_ & FEA & t2 & res2 & m2 & EC2).
    exists m'_; split; eauto.
    eapply external_call_symbols_preserved in EC2; eauto. apply senv_preserved.
  }
  inv f_eq.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constr_match_states.
  eapply match_stacks_change_meminj. 3: eexact STACKS.
  all:eauto.
  exists m, m'0; split; eauto.
  intros; eapply Mem.valid_block_inject_2; eauto. apply sep_proj1 in SEP; simpl in SEP; eauto.
  apply agree_regs_set_pair. apply agree_regs_inject_incr with j; auto. auto.
  apply agree_callee_save_set_result; auto.
  * eapply inject_incr_trans; eauto.
  * eapply inject_incr_sep_trans; eauto.
  * etransitivity. apply INIT_VB.
    eapply external_call_nextblock; eauto.
  * etransitivity. apply INIT_VB'.
    eapply external_call_nextblock; eauto.
  * rewrite <- H1. simpl in *.
    eapply init_args_out_of_bounds_external_call; eauto.
    intros.
    rewrite H3 in INJ_INIT_SP; inversion INJ_INIT_SP.
    rewrite Mem.valid_block_extends.
    eapply Mem.valid_block_inject_1; eauto. apply sep_proj1 in SEP; simpl in SEP; eauto.
    eauto.
    apply sep_proj1 in SEP; simpl in SEP; eauto.
  * congruence.
  * revert Hsome_init_args Hno_init_args.
    simpl.
    intros IAIB IAOOB.
    eapply init_args_in_bounds_external_call. eexact H4.
    eapply globalenv_inject_preserves_globals.
    apply sep_pick2 in SEP. eauto. all: eauto.
    -- intros.
       revert INJ_INIT_SP D H3. clear. intros. subst. simpl in *; auto.
    -- revert HAMOA INJ_INIT_SP D E ISP'VALID. clear.
       intros; subst; simpl in *; auto.
       specialize (HAMOA _ _ eq_refl _ _ _ _ INJ_INIT_SP H0). subst.
       rewrite H0 in INJ_INIT_SP. inv INJ_INIT_SP. auto.
    -- apply sep_pick1 in SEP; simpl in SEP; eauto.
    -- eapply val_list_lessdef_inject_compose. 2: apply VINJ.
       inv f_eq. apply map_reg_lessdef. auto.
    -- inv f_eq. eauto.
  * revert INJ_INIT_SP D. clear.
    destruct init_sp; simpl; auto.
  * revert HAMOA D E ISP'VALID. clear.
    red; intros.
    destruct (j b1) eqn:?. destruct p.
    destruct (j b2) eqn:?. destruct p.
    exploit D. eexact Heqo.
    exploit D. eexact Heqo0.
    intros. assert (b0 = b' /\ b = b') by (split; congruence). destruct H1; subst.
    eapply HAMOA; eauto.
    exploit E; eauto. rewrite EQ in ISP'VALID; simpl in ISP'VALID. intuition congruence.
    exploit E; eauto. rewrite EQ in ISP'VALID; simpl in ISP'VALID. intuition congruence.
  * eapply block_prop_impl. 2: eauto. intros; eapply external_call_valid_block; eauto.
  * apply stack_contents_change_meminj with j; auto.
    rewrite sep_swap12.
    apply mconj_intro.
    rewrite (sep_comm (stack_contents _ _ _)). eauto.
    split.
    rewrite sep_swap12 in SEP_init. apply mconj_proj2 in SEP_init.
    apply sep_proj1 in SEP_init. revert SEP_init.
    -- simpl.
       intro IAM.
       inv f_eq.
       exploit external_call_mem_extends. apply H4. eauto.
       apply map_reg_lessdef. apply rs_lessdef.
       intros (vres' & m2' & EC2 & LDres & EXTres & UNCH).
       exploit external_call_determ. eexact EC2. eexact H2.
       intros (AA & BB). intuition subst. clear H2.
       exploit external_call_mem_inject.
       3: eapply Mem.extends_inject_compose. 3: apply m_ext.
       3: apply sep_proj1 in SEP; simpl in SEP; eauto.
       eapply globalenv_inject_preserves_globals.
       apply sep_pick2 in SEP; eauto.
       eauto.
       eapply val_list_lessdef_inject_compose.
       apply map_reg_lessdef. apply rs_lessdef.
       simpl in VINJ. apply VINJ.
       intros (f' & vres'0 & m2'0 & EC3 & INJres & MINJres & UNCH' & UNCH3 & INCR2 & SEP2).
       exploit external_call_determ.
       eexact A. eexact EC3. intuition subst.
       revert HAMOA INJ_INIT_SP UNCH3 IAM Hno_init_args D. clear - external_calls_prf.
       red; intros.
       exploit IAM. eauto. instantiate (1 := rs).
       intros (v & ea & inj); eexists; split; eauto.
       inv ea; constructor; eauto.
       destruct init_sp eqn:?; simpl in *; try discriminate.
       unfold load_stack in *; simpl in *.
       eapply Mem.load_unchanged_on. eexact UNCH3. 2: eauto.
       red; red; intros.
       exploit Hno_init_args; eauto.
       exploit HAMOA. eauto. apply INJ_INIT_SP. apply H1.
       intro. subst b0.
       assert (delta = 0) by congruence. subst delta.
       rewrite Zminus_0_r in H2; eauto.
    -- split. apply sep_proj2 in C. rewrite sep_comm in C. eauto.
       rewrite sep_swap12 in SEP_init.
       apply mconj_proj2 in SEP_init.
       destruct SEP_init as (A1 & A2 & A3).
       revert A3.
       clear - D. red; simpl.
       intros. decompose [ex and] H. clear H.
       exploit A3. simpl. repeat eexists; eauto.
       revert H0.
       eapply footprint_impl.
       simpl. auto. auto.
  * eapply bounds_stack_perm. eauto. eapply match_stacks_valid_stack; eauto.
    apply sep_proj1 in SEP; eauto.
    intros. eapply external_call_max_perm; eauto.

- (* return *)
  inv STACKS. simpl in AGLOCS. simpl in SEP. rewrite sep_assoc in SEP. 
  econstructor; split.
  apply plus_one. apply exec_return.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; subst; simpl in * |- * ; try now intuition congruence.
  intro IAOOB.
  constr_match_states; eauto.
  apply agree_locs_return with rs0; auto.
  rewrite <- H0; simpl; eassumption.
  congruence.
  apply frame_contents_exten with rs0 (parent_locset init_ls s); auto.
  intros. eapply BS. eauto. eapply BS.
  Unshelve. eauto.
Qed.

End WITHMEMINIT.

End WITHINITSP.

Inductive match_states' (s : Linear2.state) (s': Mach.state): Prop :=
| match_states'_intro:
    match_states Vnullptr Vnullptr (Locmap.init Vundef) (signature_main) Val.Vnullptr_has_type Mem.empty s s' ->
    match_states' s s'.

Lemma transf_initial_states:
  forall st1, Linear2.initial_state prog st1 ->
  exists st2, Mach.initial_state tprog st2 /\ match_states' st1 st2.
Proof.
  intros. inv H.
  inv init_lower.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved. eauto.
  set (j := Mem.flat_inj (Mem.nextblock m0)).
  constructor.
  econstructor. instantiate (4 := j). all: eauto.
  - rewrite H3. constructor.
    left; red; simpl. easy.
    vm_compute. congruence.
  - unfold Locmap.init. red; intros; auto.
  - unfold Locmap.init. red; intros; auto.
  - unfold j, Mem.flat_inj.
    red. intros.
    destruct (plt b0 (Mem.nextblock Mem.empty)); try congruence.
    rewrite Mem.nextblock_empty in p; xomega.
  - red. unfold Mem.flat_inj. intros b1.
    unfold Mem.valid_block. simpl.
    rewrite Mem.nextblock_empty in *. intros. split; xomega.
  - rewrite Mem.nextblock_empty; xomega.
  - rewrite Mem.nextblock_empty; xomega.
  - red. red. discriminate.
  - congruence.
  - red.  red.
    rewrite loc_arguments_main. simpl; eauto.
  - unfold Vnullptr. destruct Archi.ptr64; simpl; auto.
  - red. discriminate.
  - unfold Vnullptr. destruct Archi.ptr64; simpl; auto.
  - simpl stack_contents. rewrite sep_pure. split; auto. split;[|split].
    + split.
      * simpl. eapply Genv.initmem_inject; eauto.
      * simpl. red. simpl. easy.
    +  simpl. exists (Mem.nextblock m0); split. apply Ple_refl.
       unfold j, Mem.flat_inj; constructor; intros.
       apply pred_dec_true; auto.
       destruct (plt b1 (Mem.nextblock m0)); congruence.
       change (Mem.valid_block m0 b0). eapply Genv.find_symbol_not_fresh; eauto.
       change (Mem.valid_block m0 b0). eapply Genv.find_funct_ptr_not_fresh; eauto.
       change (Mem.valid_block m0 b0). eapply Genv.find_var_info_not_fresh; eauto.
    + red; simpl; tauto.
  - red; simpl. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states' st1 st2 -> Linear2.final_state st1 r -> Mach.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv fin_higher. inv fin_lower. inv H0; try congruence.
  inv STACKS; try congruence.
  assert (R: exists r, loc_result signature_main = One r).
  { destruct (loc_result signature_main) as [r1 | r1 r2] eqn:LR.
  - exists r1; auto.
  - generalize (loc_result_type signature_main). rewrite LR. discriminate.
  }
  destruct R as [rres EQ]. rewrite EQ in H1. simpl in H1.
  rewrite <- H2 in Hs2; inv Hs2.
  generalize (Linear2.state_invariant st1).
  rewrite <- H, <- H2. intro A; inv A.
  generalize (AGREGS rres).
  specialize (rs_lessdef (R rres)); rewrite H1 in rs_lessdef. inv rs_lessdef. intro A; inv A.
  econstructor; eauto.
  unfold Locmap.getpair in H3. simpl in H3.
  rewrite EQ in H3. simpl in H3.
  unfold signature_main in EQ. vm_compute in EQ. inv EQ.
  congruence.
Qed.

Lemma wt_prog:
  forall i fd, In (i, Some (Gfun fd)) prog.(prog_defs) -> wt_fundef fd.
Proof.
  intros.
  exploit list_forall2_in_left. eexact (proj1 TRANSF). eauto.
  intros ([i' g] & P & Q & R). simpl in *. inv R.
  inv H1.
  destruct fd; simpl in *.
- monadInv H3. unfold transf_function in EQ.
  destruct (wt_function f). auto. discriminate.
- auto.
Qed.

Theorem transf_program_correct':
  forward_simulation (Linear2.semantics prog) (Mach.semantics return_address_offset tprog).
Proof.
  set (ms := fun s s' => wt_state (Locmap.init Vundef) (Linear2.state_lower s) /\ match_states' s s').
  eapply forward_simulation_plus with (match_states := ms).
- apply senv_preserved.
- intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
  exists st2; split; auto. split; auto.
  apply wt_initial_state with (prog0 := prog); auto. exact wt_prog.
  inv H. congruence.
- intros. destruct H. eapply transf_final_states; eauto.
- intros.
  destruct H0. destruct H1.
  exploit transf_step_correct; eauto.
  apply Val.Vnullptr_has_type. 
  intros [s2' [A B]].
  exists s2'; split. exact A. split.
  inv H.
  eapply step_type_preservation; eauto. eexact wt_prog.
  assert (Linear2.state_init_ls s1 = Locmap.init Vundef) as INIT.
  {
    inversion H1; congruence.
  }
  rewrite <- INIT.
  eexact step_low.
  repeat eexists; eauto. 
Qed.

Theorem transf_program_correct:
  forward_simulation (Linear.semantics prog) (Mach.semantics return_address_offset tprog).
Proof.
  eapply compose_forward_simulations.
  eapply Linear2.whole_program_linear_to_linear2.
  apply transf_program_correct' .
Qed.

End PRESERVATION.
