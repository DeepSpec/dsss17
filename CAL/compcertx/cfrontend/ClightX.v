Require compcert.cfrontend.Clight.
Require SmallstepX.
Require EventsX.

Import Coqlib.
Import AST.
Import Values.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Ctypes.
Export Clight.

(** Execution of Clight functions with C-style arguments (long long 64-bit integers allowed)
    BUT with Asm signature (not C signature).
 *)

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.


Inductive initial_state
          (p: Clight.program) (i: ident) (m: mem)
          (sg: signature) (args: list val): state -> Prop :=
| initial_state_intro
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (** We need to keep the signature because it is required for lower-level languages *)
    targs tres tcc
    (Hty: type_of_fundef f = Tfunction targs tres tcc)
    (Hsig: sg = signature_of_type targs tres tcc)
  :
    initial_state p i m sg args (Callstate f args Kstop m)
.

Inductive final_state (sg: signature): state -> (val * mem) -> Prop :=
| final_state_intro
    v
    m :
    final_state sg (Returnstate v Kstop m) (v, m)
.

(** We define the per-module semantics of RTL as adaptable to both C-style and Asm-style;
    by default it is C-style (except for signature, which must be Asm-style). *)

Definition semantics
           (p: Clight.program) (i: ident) (m: mem)
           (sg: signature) (args: list val) : semantics _ :=
  Semantics_gen
    Clight.step2
    (initial_state p i m sg args) (final_state sg) (Clight.globalenv p) (Clight.globalenv p).

(* Single events *)

Lemma semantics_single_events p i m sg args:
  single_events (semantics p i m sg args).
Proof.
  red.
  intros s t s' H.
  inversion H; subst; simpl; auto;
    eapply external_call_trace_length; eauto.
Qed.

(* Semantics is receptive *)

Lemma semantics_receptive p i m sg args:
  receptive (semantics p i m sg args).
Proof.
  constructor; auto using semantics_single_events.
  inversion 1; subst;
    try now (inversion 1; subst; eauto).
  * intros.
    exploit external_call_receptive; eauto.
    destruct 1 as (? & ? & ?).
    esplit.
    econstructor; eauto.
  * intros.
    exploit external_call_receptive; eauto.
    destruct 1 as (? & ? & ?).
    esplit.
    econstructor; eauto.
Qed.

(* Semantics is determinate *)

Lemma deref_loc_determ ty m b ofs v1 v2:
  deref_loc ty m b ofs v1 ->
  deref_loc ty m b ofs v2 ->
  v1 = v2.
Proof.
  inversion 1; subst; inversion 1; congruence.
Qed.

Lemma assign_loc_determ ge ty m b ofs v m1 m2:
  assign_loc ge ty m b ofs v m1 ->
  assign_loc ge ty m b ofs v m2 ->
  m1 = m2.
Proof.
  inversion 1; subst; inversion 1; congruence.
Qed.

Lemma alloc_variables_determ ge e m l e1 m1 e2 m2:
  alloc_variables ge e m l e1 m1 ->
  alloc_variables ge e m l e2 m2 ->
  e1 = e2 /\ m1 = m2.
Proof.
  induction 1; inversion 1; subst; auto.
  apply IHalloc_variables.
  congruence.
Qed.

Lemma bind_parameters_determ e:
  forall ge m l lv m1 m2,
    bind_parameters ge e m l lv m1 ->
    bind_parameters ge e m l lv m2 ->
    m1 = m2.
Proof.
  induction 1; inversion 1; subst; auto.
  apply IHbind_parameters; eauto.
  replace b0 with b in * by congruence.
  replace m4 with m1 in * by (eapply assign_loc_determ; eauto).
  eauto.
Qed.

Lemma eval_expr_lvalue_determ ge le te m:
  (
    forall e v1,
      eval_expr ge le te m e v1 ->
      forall v2,
        eval_expr ge le te m e v2 ->
        v1 = v2
  ) /\
  (
    forall e b1 o1,
      eval_lvalue ge le te m e b1 o1 ->
      forall b2 o2,
        eval_lvalue ge le te m e b2 o2 ->
        b1 = b2 /\ o1 = o2
  ).
Proof.
  apply eval_expr_lvalue_ind;
    intros;
    try now
        (repeat
           match goal with
           | H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Econst_float _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Econst_float _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Econst_long _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Econst_long _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Evar _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Evar _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Efield _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Efield _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Eaddrof _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Esizeof _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Esizeof _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Ealignof _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Ealignof _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Ecast _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Eunop _ _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ |- _ => inv H; auto
           | H : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inv H; auto
           | H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ |- _ => inv H; auto
           | H0: forall _, eval_expr _ _ _ _ _ _  -> _ |- _ =>
             exploit H0; eauto; intuition subst; try congruence; revert H0
           | H0: forall _ _, eval_lvalue _ _ _ _ _ _ _ -> _ |- _ =>
             exploit H0; eauto; intuition subst; try congruence; revert H0
           end; congruence).

  - inv H ; simpl in *; inv H2; exploit H0; eauto; intuition subst; eapply deref_loc_determ; eauto.
  - inv H0; intuition congruence.
  - inv H1; intuition congruence.
  - inv H1. exploit H0; eauto. injection 1. intuition congruence.
  - inv H4; exploit H0; eauto; injection 1; intuition congruence.
  - inv H3; exploit H0; eauto; injection 1; intuition congruence.
Qed.

Lemma eval_expr_determ ge le te m:
  (
    forall e v1,
      eval_expr ge le te m e v1 ->
      forall v2,
        eval_expr ge le te m e v2 ->
        v1 = v2
  ) .
Proof.
  apply eval_expr_lvalue_determ.
Qed.

Lemma eval_lvalue_determ ge le te m:
  (
    forall e b1 o1,
      eval_lvalue ge le te m e b1 o1 ->
      forall b2 o2,
        eval_lvalue ge le te m e b2 o2 ->
        b1 = b2 /\ o1 = o2
  ).
Proof.
  apply eval_expr_lvalue_determ.
Qed.

Lemma eval_exprlist_determ ge le te m:
  forall l t lv1,
    eval_exprlist ge le te m l t lv1 ->
    forall lv2,
      eval_exprlist ge le te m l t lv2 ->
      lv1 = lv2.
Proof.
  induction 1; inversion 1; subst; auto.
  f_equal; eauto.
  replace v1 with v0 in * by (eapply eval_expr_determ; eauto).
  congruence.
Qed.

Lemma function_entry2_determ ge f vargs m e1 le1 m1 e2 le2 m2:
  function_entry2 ge f vargs m e1 le1 m1 ->
  function_entry2 ge f vargs m e2 le2 m2 ->
  (e1 = e2 /\ m1 = m2) /\ le1 = le2.
Proof.
  inversion 1; inversion 1; subst.
  split.
  * eapply alloc_variables_determ; eauto.
  * congruence.
Qed.

Theorem step2_determ:
  forall ge s s1 t1 t2 s2,
    Clight.step2 ge s t1 s1 ->
    Clight.step2 ge s t2 s2 ->
    (match_traces ge t1 t2 /\ (t1 = t2 -> s1 = s2)).
Proof.
  intro ge.
  assert (MTZ: match_traces ge E0 E0) by constructor.
  inversion 1; subst;
    inversion 1; subst; try contradiction; try intuition (congruence || now constructor).
  * split; auto. 
    intros _.
    f_equal.
    replace v2 with v0 in * by (eapply eval_expr_determ; eauto).
    assert (loc0 = loc /\ ofs0 = ofs) as K by (eapply eval_lvalue_determ; eauto).
    destruct K; subst.
    replace v1 with v in * by congruence.
    eapply assign_loc_determ; eauto.
  * split; auto.
    intros _.
    f_equal.
    f_equal.
    eapply eval_expr_determ; eauto.
  * split; auto.
    intros _.
    replace vf0 with vf in * by (eapply eval_expr_determ; eauto).
    replace fd0 with fd in * |- * by congruence.
    f_equal.
    replace tyargs0 with tyargs in * by congruence.
    eapply eval_exprlist_determ; eauto.
  * replace vargs0 with vargs in * by (eapply eval_exprlist_determ; eauto).
    exploit external_call_determ.
    { eexact H1. }
    { eexact H15. }
    intuition congruence.
  * split; auto.
    intros _.
    replace v1 with v0 in * by (eapply eval_expr_determ; eauto).
    replace b0 with b in * by congruence.
    reflexivity.
  * split; auto.
    intros _.
    replace v0 with v in * by (eapply eval_expr_determ; eauto).
    congruence.
  * split; auto.
    intros _.
    exploit eval_expr_determ. eexact H0. eexact H12. intros; subst. congruence.
  * split; auto.
    intros _.
    assert (
        (e0 = e /\ m2 = m1) /\ le0 = le
      ) by (eapply function_entry2_determ; eauto).
    intuition congruence.
  * exploit external_call_determ. eexact H0. eexact H11.
    intuition congruence.
Qed.

Lemma semantics_determinate p i m sg args:
  determinate (semantics p i m sg args).
Proof.
  constructor; auto using semantics_single_events.
  * intros; eapply step2_determ; simpl in * |- * ; eauto.
  * inversion 1; inversion 1; congruence.
  * inversion 1; subst.
    red.
    intros.
    intro ABS.
    inv ABS.
  * inversion 1; inversion 1; congruence.
Qed.

End WITHCONFIG.
