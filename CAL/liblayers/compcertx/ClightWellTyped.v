Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcertx.common.MemoryX.
Require Import compcertx.common.EventsX.
Require Export liblayers.compcertx.ClightModules.
Require Import liblayers.compcertx.SimClight.

(** ** Function execution is well-typed at return. *)

(** There is a tricky case: if the function returns void, then we
  must ensure that its body's return statements have no returned
  expression. *)

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statement_ind2 := Induction for labeled_statements Sort Prop.

Combined Scheme statement_labeled_statement_ind2
  from statement_ind2, labeled_statement_ind2.

Section WITHCOMPILERCONFIGOPS.

  Context `{ec_ops: ExternalCallsOps}.
  Context {cc_ops: (@EnableBuiltins _ _ ec_ops)}.

  Fixpoint topmost_fundef_of_cont (f: option Clight.function) (k: cont): option Clight.function :=
    match k with
      | Kstop => f
      | Kcall _ phi _ _ k' =>
        topmost_fundef_of_cont (Some phi) k'
      | Kseq _ k' => topmost_fundef_of_cont f k'
      | Kloop1 _ _ k' => topmost_fundef_of_cont f k'
      | Kloop2 _ _ k' => topmost_fundef_of_cont f k'
      | Kswitch k' => topmost_fundef_of_cont f k'
    end.

  Lemma topmost_fundef_of_cont_call_cont k:
    forall f,
      topmost_fundef_of_cont f (call_cont k) =
      topmost_fundef_of_cont f k.
  Proof.
    induction k; simpl; auto.
  Qed.

  Lemma topmost_fundef_of_cont_stop f k:
    call_cont k = Kstop ->
    topmost_fundef_of_cont f k = f.
  Proof.
    induction k; simpl; eauto; discriminate.
  Qed.

  Lemma topmost_fundef_find_label f:
    (forall s,
       forall lbl k s' k',
         find_label lbl s k = Some (s', k') ->
         topmost_fundef_of_cont f k' = topmost_fundef_of_cont f k) /\
    (forall s,
       forall lbl k s' k',
         find_label_ls lbl s k = Some (s', k') ->
         topmost_fundef_of_cont f k' = topmost_fundef_of_cont f k).
  Proof.
    apply statement_labeled_statement_ind2; simpl; eauto; try discriminate.
    + intros s H s0 H0 lbl k s' k' H1.
      destruct (find_label _ _ (Kseq _ _)) eqn:FIND; eauto.
      inversion H1; clear H1; subst.
      apply H in FIND.
      assumption.
    + intros e s H s0 H0 lbl k s' k' H1.
      destruct (find_label lbl s k) eqn:FIND; eauto.
      inversion H1; subst; eauto.
    + intros s H s0 H0 lbl k s' k' H1.
      destruct (find_label _ _ (Kloop1 _ _ _)) eqn:FIND.
      - inversion H1; clear H1; subst.
        apply H in FIND.
        assumption.
      - apply H0 in H1.
        assumption.
    + intros e l H lbl k s' k' H0.
      apply H in H0.
      assumption.
    + intros l s H lbl k s' k' H0.
      destruct (ident_eq _ _); eauto.
      congruence.
    + intros o s H l H0 lbl k s' k' H1.
      destruct (find_label _ _ (Kseq _ _)) eqn:FIND; eauto.
      inversion H1; clear H1; subst.
      apply H in FIND.
      assumption.
  Qed.

  Definition topmost_fundef_of_state (s: state): option Clight.function :=
    match s with
      | State phi _ k _ _ _ =>
        topmost_fundef_of_cont (Some phi) k
      | Callstate f _ k _ =>
        topmost_fundef_of_cont match f with
                                    Internal phi => Some phi
                                 | _ => None
                               end
                               k
      | Returnstate _ k _ =>
        topmost_fundef_of_cont None k
    end.

  Lemma sem_cast_correct m v a ty (Hty: ty <> Tvoid) v':
    Cop.sem_cast v a ty m = Some v' ->
    Val.has_type v' (typ_of_type ty).
  Proof.
    unfold Cop.sem_cast.
    destruct (Cop.classify_cast a ty) eqn:CLASSIFY;
      try now (destruct a; simpl in *; try discriminate;
               destruct ty; simpl in *; try discriminate;
               try destruct i; try discriminate;
               try destruct i0; try discriminate;
               try destruct f; try discriminate;
               try destruct f0; try discriminate;
               destruct v; try discriminate;
               unfold Tptr;
               destruct Archi.ptr64 eqn:?; try discriminate;
               inversion 1; subst; simpl; auto).
    + destruct v; try discriminate.
      destruct (Cop.cast_float_int _ _) eqn:CAST_FLOAT_INT; try discriminate.
      inversion 1; subst.
      destruct a, ty; try discriminate; try constructor;
        try destruct f0; try discriminate;
          try destruct f1; try discriminate.
    + destruct v; try discriminate.
      destruct (Cop.cast_single_int _ _) eqn:CAST_FLOAT_INT; try discriminate.
      inversion 1; subst.
      destruct a, ty; try discriminate; try constructor;
        try destruct f0; try discriminate;
          try destruct f1; try discriminate.
    + destruct v; try discriminate.
      destruct (Cop.cast_float_long _ _) eqn:CAST_FLOAT_INT; try discriminate.
      inversion 1; subst.
      destruct a, ty; try discriminate; try constructor;
        try destruct i0; try discriminate;
          try destruct i1; try discriminate;
            try destruct f0; try discriminate;
              try destruct f1; try discriminate.
    + destruct v; try discriminate.
      destruct (Cop.cast_single_long _ _) eqn:CAST_FLOAT_INT; try discriminate.
      inversion 1; subst.
      destruct a, ty; try discriminate; try constructor;
        try destruct i0; try discriminate;
          try destruct i1; try discriminate;
            try destruct f0; try discriminate;
              try destruct f1; try discriminate.
    + destruct v; try discriminate.
      inversion 1; subst.
      destruct a, ty; try discriminate; try constructor;
            try destruct f; try discriminate;
              try destruct f0; try discriminate.
      destruct Archi.ptr64 eqn:?; simpl; try discriminate.
      destruct Cop.weak_valid_pointer; try discriminate.
      inversion 1; subst.
      destruct a, ty; try discriminate; try constructor;
            try destruct f; try discriminate;
              try destruct f0; try discriminate.
    + destruct v; try discriminate.
      destruct (ident_eq _ _); try discriminate.
      inversion 1; subst.
      destruct a, ty; try discriminate; try constructor;
            try destruct f; try discriminate;
              try destruct f0; try discriminate;
                try destruct i0; try discriminate;
                  try destruct i1; try discriminate.
    + destruct v; try discriminate.
      destruct (ident_eq _ _); try discriminate.
      inversion 1; subst.
      destruct a, ty; try discriminate; try constructor;
            try destruct f; try discriminate;
              try destruct f0; try discriminate;
                try destruct i0; try discriminate;
                  try destruct i1; try discriminate.      
  Qed.

  Fixpoint topmost_no_return_cont (f: list statement) (k: cont) {struct k}: Prop :=
    match k with
      | Kstop => forall s, In s f -> ClightModules.no_return_value_statement s = true
      | Kcall _ _ _ _ k' => topmost_no_return_cont nil k'
      | Kseq s k' => topmost_no_return_cont (s :: f) k'
      | Kloop1 s1 s2 k' => topmost_no_return_cont (s1 :: s2 :: f) k'
      | Kloop2 s1 s2 k' => topmost_no_return_cont (s1 :: s2 :: f) k'
      | Kswitch k' => topmost_no_return_cont f k'
    end.

  Lemma topmost_no_return_cont_ext k:
    forall f1 f2,
      (forall i,
        In i f2 ->
        (In i f1 \/
         ClightModules.no_return_value_statement i = true)) ->
      topmost_no_return_cont f1 k ->
      topmost_no_return_cont f2 k.
  Proof.
    clear.
    induction k; simpl; eauto.
    + firstorder.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      simpl; firstorder.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      simpl; firstorder.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      simpl; firstorder.
  Qed.

  Lemma topmost_no_return_cont_seq k:
    forall f1 f2,
      (forall i,
        In i f2 ->
        (In i f1 \/
         exists s1 s2, In (Ssequence s1 s2) f1 /\ (i = s1 \/ i = s2))) ->
      topmost_no_return_cont f1 k ->
      topmost_no_return_cont f2 k.
  Proof.
    clear.
    induction k; simpl; eauto.
    + intros f1 f2 H H0 s H1.
      apply H in H1; clear H.
      destruct H1 as [ | H1 ] ; auto.
      destruct H1 as (? & ? & H1 & EQ).
      apply H0 in H1; clear H0.
      simpl in H1.
      apply andb_true_iff in H1.
      intuition congruence.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | H0 ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ?).
      eauto 7.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ?).
      eauto 7.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ?).
      eauto 7.
  Qed.

  Lemma topmost_no_return_cont_if k:
    forall f1 f2,
      (forall i,
        In i f2 ->
        (In i f1 \/
         exists e s1 s2, In (Sifthenelse e s1 s2) f1 /\ (i = s1 \/ i = s2))) ->
      topmost_no_return_cont f1 k ->
      topmost_no_return_cont f2 k.
  Proof.
    clear.
    induction k; simpl; eauto.
    + intros f1 f2 H H0 s H1.
      apply H in H1; clear H.
      destruct H1 as [ | H1 ] ; auto.
      destruct H1 as (? & ? & ? & H1 & EQ).
      apply H0 in H1; clear H0.
      simpl in H1.
      apply andb_true_iff in H1.
      intuition congruence.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | H0 ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?).
      eauto 7.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?).
      eauto 8.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?).
      eauto 8.
  Qed.

  Lemma topmost_no_return_cont_loop k:
    forall f1 f2,
      (forall i,
        In i f2 ->
        (In i f1 \/
         exists s1 s2, In (Sloop s1 s2) f1 /\ (i = s1 \/ i = s2))) ->
      topmost_no_return_cont f1 k ->
      topmost_no_return_cont f2 k.
  Proof.
    clear.
    induction k; simpl; eauto.
    + intros f1 f2 H H0 s H1.
      apply H in H1; clear H.
      destruct H1 as [ | H1 ] ; auto.
      destruct H1 as (? & ? & H1 & EQ).
      apply H0 in H1; clear H0.
      simpl in H1.
      apply andb_true_iff in H1.
      intuition congruence.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | H0 ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ?).
      eauto 7.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ?).
      eauto 7.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ?).
      eauto 7.
  Qed.

  Lemma topmost_no_return_cont_loop_inv k:
    forall f1 f2,
      (forall i,
         In i f2 ->
         (In i f1 \/
          exists s1 s2, i = Sloop s1 s2 /\ In s1 f1 /\ In s2 f1)) ->
      topmost_no_return_cont f1 k ->
      topmost_no_return_cont f2 k.
  Proof.
    clear.
    induction k; simpl; eauto.
    + intros f1 f2 H H0 s H1.
      apply H in H1; clear H.
      destruct H1 as [ | H1 ] ; auto.
      destruct H1 as (? & ? & ? & H1 & H2) ; subst.
      apply H0 in H1.
      apply H0 in H2; clear H0.
      simpl.
      apply andb_true_iff; auto.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | H0 ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?); subst.
      eauto 8.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?).
      subst.
      eauto 10.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?).
      eauto 10.
  Qed.

  Lemma seq_of_labeled_statement_no_return ls:
    ClightModules.no_return_value_labeled_statements ls = true ->
    ClightModules.no_return_value_statement (seq_of_labeled_statement ls) = true.
  Proof.
    induction ls; simpl; auto.
    intros H.
    apply andb_true_iff in H.
    destruct H.
    apply andb_true_iff.
    split; auto.
  Qed.

  Lemma select_switch_case_no_return sl:
    ClightModules.no_return_value_labeled_statements sl = true ->
    forall n ls,
      select_switch_case n sl = Some ls ->
      ClightModules.no_return_value_labeled_statements ls  = true.
  Proof.
    induction sl; simpl; try discriminate.
    intros H n ls H0.
    apply andb_true_iff in H.
    destruct H.
    destruct o; eauto.
    destruct (zeq _ _); eauto.
    inversion H0; subst. simpl.
    apply andb_true_iff; auto.
  Qed.

  Lemma select_switch_default_no_return sl:
    ClightModules.no_return_value_labeled_statements sl = true ->
    ClightModules.no_return_value_labeled_statements (select_switch_default sl)  = true.
  Proof.
    induction sl; simpl; auto.
    intros H.
    apply andb_true_iff in H.
    destruct H.
    destruct o; auto.
    simpl.
    apply andb_true_iff; auto.
  Qed.

  Lemma select_switch_no_return n sl:
    ClightModules.no_return_value_labeled_statements sl = true ->
    ClightModules.no_return_value_labeled_statements (select_switch n sl)   = true.
  Proof.
    unfold select_switch.
    destruct (select_switch_case n sl) eqn:SWITCH.
    + intros; eapply select_switch_case_no_return; eauto.
    + apply select_switch_default_no_return.
  Qed.

  Lemma topmost_no_return_cont_switch k:
    forall f1 f2,
      (forall i,
         In i f2 ->
         (In i f1 \/
          exists a n sl,
            i = seq_of_labeled_statement (select_switch n sl) /\
            In (Sswitch a sl) f1)) ->
      topmost_no_return_cont f1 k ->
      topmost_no_return_cont f2 k.
  Proof.
    clear.
    induction k; simpl; eauto.
    + intros f1 f2 H H0 s H1.
      apply H in H1; clear H.
      destruct H1 as [ | H1 ] ; auto.
      destruct H1 as (? & ? & ? & ? & H1).
      subst.
      apply H0 in H1; clear H0.
      simpl in H1.
      apply seq_of_labeled_statement_no_return.
      apply select_switch_no_return.
      assumption.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | H0 ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?).
      eauto 7.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?).
      eauto 8.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ? & ? & ? & ?).
      eauto 8.
  Qed.

  Lemma topmost_no_return_cont_label k:
    forall f1 f2,
      (forall i,
         In i f2 ->
         (In i f1 \/
          exists l,
            In (Slabel l i) f1)) ->
      topmost_no_return_cont f1 k ->
      topmost_no_return_cont f2 k.
  Proof.
    clear.
    induction k; simpl; eauto.
    + intros f1 f2 H H0 s H1.
      apply H in H1; clear H.
      destruct H1 as [ | H1 ] ; auto.
      destruct H1 as (? & H1).
      apply H0 in H1; clear H0.
      simpl in H1.
      assumption.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | H0 ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ?).
      eauto 7.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ?).
      eauto 8.
    + intros f1 f2 H H0.
      eapply IHk; clear IHk; [ | eexact H0 ] ; clear H0.
      intros i H0.
      simpl in H0.
      destruct H0 as [ | [ | H0 ] ] ; simpl; eauto.
      apply H in H0; clear H.
      destruct H0 as [ | H0 ] ; eauto.
      destruct H0 as (? & ?).
      eauto 8.
  Qed.

  Lemma topmost_no_return_call_cont k:
    call_cont k <> Kstop ->
    forall l1 l2,
      topmost_no_return_cont l1 k ->
      topmost_no_return_cont l2 (call_cont k).
  Proof.
    induction k; simpl; eauto.
  Qed.

  Lemma topmost_no_return_call_cont_inv k:
    call_cont k <> Kstop ->
    forall l1 l2,
      topmost_no_return_cont l1 k ->
      topmost_no_return_cont l2 k.
  Proof.
    induction k; simpl; eauto.
  Qed.

  Lemma topmost_no_return_call_cont_Kstop k:
    call_cont k = Kstop ->
    forall l,
      topmost_no_return_cont l k ->
      forall i,
        In i l ->
        ClightModules.no_return_value_statement i = true.
  Proof.
    induction k; simpl; eauto; try discriminate.
    + intros H l H0 i H1.
      eapply IHk; try eexact H0; eauto.
      simpl; auto.
    + intros H l H0 i H1.
      eapply IHk; try eexact H0; eauto.
      simpl; auto.
    + intros H l H0 i H1.
      eapply IHk; try eexact H0; eauto.
      simpl; auto.
  Qed.

  Lemma find_label_no_return_stop:
    (forall s,
       no_return_value_statement s = true ->
       forall lbl k s' k' l1,
         find_label lbl s k = Some (s', k') ->
         call_cont k = Kstop ->
         topmost_no_return_cont l1 k ->
         topmost_no_return_cont (s' :: nil) k') /\
    (forall s,
       no_return_value_labeled_statements s = true ->
       forall lbl k s' k' l1,
         find_label_ls lbl s k = Some (s', k') ->
         call_cont k = Kstop ->
         topmost_no_return_cont l1 k ->
         topmost_no_return_cont (s' :: nil) k').
  Proof.
    apply statement_labeled_statement_ind2; simpl; eauto; try discriminate.
    + intros s H s0 H0 H1 lbl k s' k' l1 H2 H3 H4.
      apply andb_true_iff in H1.
      destruct H1 as (H1a & H1b).
      destruct (find_label _ _ (Kseq _ _)) eqn:FIND; eauto.
      inversion H2; clear H2; subst.
      eapply H; clear H H0; eauto.
      simpl.
      eapply topmost_no_return_cont_ext.
      2: eassumption.
      instantiate (1 := l1).
      destruct 1; subst; auto.
    + intros e s H s0 H0 H1 lbl k s' k' l1 H2 H3 H4.
      apply andb_true_iff in H1.
      destruct H1 as (H1a & H1b).
      destruct (find_label lbl s k) eqn:FIND; eauto.
      inversion H2; clear H2; subst.
      eapply H; clear H H0; eauto.
    + intros s H s0 H0 H1 lbl k s' k' l1 H2 H3 H4.
      apply andb_true_iff in H1.
      destruct H1 as (H1a & H1b).
      destruct (find_label lbl s (Kloop1 s s0 k)) eqn:FIND.
      - inversion H2; clear H2; subst.
        eapply H; clear H H0; eauto.
        simpl.
        eapply topmost_no_return_cont_ext.
        2: eassumption.
        instantiate (1 := l1).
        simpl.
        revert H1a H1b.
        clear. intros. intuition congruence.
      - eapply H0; clear H H0; eauto.
        simpl.
        eapply topmost_no_return_cont_ext.
        2: eassumption.
        instantiate (1 := l1).
        simpl.
        revert H1a H1b.
        clear. intros. intuition congruence.
    + intros l s H H0 lbl k s' k' l1 H1 H2 H3.
      destruct (ident_eq _ _); eauto.
      inversion H1; clear H1; subst.
      eapply topmost_no_return_cont_ext.
      2: eassumption.
      destruct 1; subst; auto; contradiction.
    + intros o s H l H0 H1 lbl k s' k' l1 H2 H3 H4.
      apply andb_true_iff in H1.
      destruct H1 as (H1a & H1b).
      destruct (find_label lbl s (Kseq _ _)) eqn:FIND; eauto.
      inversion H2; clear H2; subst.
      eapply H; clear H H0; eauto.
      simpl.
      eapply topmost_no_return_cont_ext.
      2: eassumption.
      instantiate (1 := l1).
      destruct 1; auto.
      subst.
      auto using seq_of_labeled_statement_no_return.
  Qed.

  Lemma find_label_no_return_call:
    (forall s,
       forall lbl k s' k' l1 l2,
         find_label lbl s k = Some (s', k') ->
         call_cont k <> Kstop ->
         topmost_no_return_cont l1 k ->
         topmost_no_return_cont l2 k') /\
    (forall s,
       forall lbl k s' k' l1 l2,
         find_label_ls lbl s k = Some (s', k') ->
         call_cont k <> Kstop ->
         topmost_no_return_cont l1 k ->
         topmost_no_return_cont l2 k').
  Proof.
    apply statement_labeled_statement_ind2; simpl; eauto; try discriminate.
    + intros s H s0 H0 lbl k s' k' l1 l2 H1 H2 H3.
      destruct (find_label _ _ (Kseq _ _)) eqn:FIND; eauto.
      inversion H1; clear H1; subst.
      eapply H; clear H H0; eauto.
      simpl.
      instantiate (1 := l1).
      eapply topmost_no_return_call_cont_inv; eauto.
    + intros e s H s0 H0 lbl k s' k' l1 l2 H1 H2 H3.
      destruct (find_label lbl s k) eqn:FIND; eauto.
      inversion H1; clear H1; subst.
      eauto.
    + intros s H s0 H0 lbl k s' k' l1 l2 H1 H2 H3.
      destruct (find_label _ _ (Kloop1 _ _ _)) eqn:FIND.
      - inversion H1; clear H1; subst.
        eapply H; clear H H0; eauto.
        simpl.
        instantiate (1 := l1).
        eapply topmost_no_return_call_cont_inv; eauto.
      - eapply H0; clear H H0; eauto.
        simpl.
        instantiate (1 := l1).
        eapply topmost_no_return_call_cont_inv; eauto.
    + intros l s H lbl k s' k' l1 l2 H0 H1 H2.
      destruct (ident_eq _ _); eauto.
      inversion H0; clear H0; subst.
      eapply topmost_no_return_call_cont_inv; eauto.
    + intros o s H l H0 lbl k s' k' l1 l2 H1 H2 H3.
      destruct (find_label _ _ (Kseq _ _)) eqn:FIND; eauto.
      inversion H1; clear H1; subst.
      eapply H; clear H H0; eauto.
      simpl.
      instantiate (1 := l1).
      eapply topmost_no_return_call_cont_inv; eauto.
  Qed.

  Definition topmost_no_return_state (s: state): Prop :=
    match s with
      | State phi s k _ _ _ => topmost_no_return_cont (s :: nil) k
      | Callstate _ _ k _ => topmost_no_return_cont nil k
      | Returnstate _ k _ => topmost_no_return_cont nil k
    end.

  Definition wf_call_cont_state (s: state): Prop :=
    match s with
      | State _ _ _ _ _ _ => True
      | Callstate _ _ k _ => is_call_cont k
      | Returnstate _ k _ => is_call_cont k
    end.

  Lemma topmost_fundef_of_returnstate_has_type ge s1 t s2:
    Smallstep.star Clight.step2 ge s1 t s2 ->
    forall f,
      topmost_fundef_of_state s1 = Some f ->
      (fn_return f = Tvoid -> topmost_no_return_state s1) ->
      (fn_return f = Tvoid -> no_return_value_statement (fn_body f) = true) ->
      wf_call_cont_state s1 ->
      forall v' m',
        s2 = Returnstate v' Kstop m' ->
        Val.has_type v' (typ_of_type (fn_return f)).
  Proof.
    induction 1.
    {
      intros f H H0 H1 H2 v' m' H3.
      subst.
      discriminate.
    }
    intros f H2 H3 NO_RET WTC v' m' H4.
    subst.
    inversion H; subst; (try now
                            (eapply IHstar; eauto)).
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in * ; eauto.
      simpl.
      destruct 1; auto.
      subst; simpl; auto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in * ; eauto.
      simpl.
      destruct 1; auto.
      subst; simpl; auto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in * ; eauto.
      simpl.
      clear; tauto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in * ; eauto.
      simpl.
      destruct 1; auto.
      subst; simpl; auto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_seq.
      2: simpl in * ; eauto.
      clear.
      simpl. destruct 1 as [ | [ | ] ] ; subst; (try contradiction); eauto 8.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in * ; eauto.
      simpl.
      clear; tauto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in * ; eauto.
      simpl; clear; tauto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in * ; eauto.
      simpl; clear; tauto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_if.
      2: simpl in * ; eauto.
      simpl; clear.
      destruct b; simpl; destruct 1; (try contradiction); eauto 8.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_loop.
      2: simpl in *; eauto.
      simpl.
      clear.
      destruct 1 as [ | [ | [ | ] ] ] ; subst; (try contradiction); eauto 8.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in *; eauto.
      simpl; clear; tauto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in *; eauto.
      destruct 1; subst; (try contradiction); eauto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_loop_inv.
      2: simpl in *; eauto.
      destruct 1; try contradiction.
      subst.
      simpl; eauto 10.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in *; eauto.
      destruct 1; subst; (try contradiction); eauto.
    + simpl in *.
      rewrite <- topmost_fundef_of_cont_call_cont in H2.
      generalize (call_cont_is_call_cont k).
      destruct (call_cont k) eqn:CALL_CONT; try contradiction.
      - intros _ .
        simpl in H2. inversion H2; clear H2; subst.
        inversion H0; subst.
        * constructor.
        * inversion H2.
      - intros _.
        eapply IHstar.
        * assumption.
        * rewrite <- CALL_CONT. intros.
          eapply topmost_no_return_call_cont; eauto.
          rewrite CALL_CONT; clear; congruence.
        * assumption.
        * simpl; auto.
        * reflexivity.
    + simpl in *.
      rewrite <- topmost_fundef_of_cont_call_cont in H2.
      generalize (call_cont_is_call_cont k).
      destruct (call_cont k) eqn:CALL_CONT; try contradiction.
      - intros _ .
        simpl in H2. inversion H2; clear H2; subst.
        inversion H0; subst.
        * eapply sem_cast_correct; eauto.
          intro ABSURD.
          exploit topmost_no_return_call_cont_Kstop; eauto.
          { left; reflexivity. }
          discriminate.
        * inversion H2.
      - intros _.
        eapply IHstar.
        * assumption.
        * rewrite <- CALL_CONT. intros.
          eapply topmost_no_return_call_cont; eauto.
          rewrite CALL_CONT; clear; congruence.
        * assumption.
        * simpl; auto.
        * reflexivity.
    + simpl in *.
      rewrite <- topmost_fundef_of_cont_call_cont in H2.
      rewrite call_cont_is_call_cont_id in * by assumption.
      destruct k; try contradiction.
      - simpl in H2. inversion H2; clear H2; subst.
        inversion H0; subst.
        * constructor.
        * inversion H2.
      - eapply IHstar.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * reflexivity.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_switch.
      2: simpl in * ; eauto.
      simpl.
      destruct 1; try contradiction.
      subst.
      eauto 10.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_ext.
      2: simpl in *; eauto.
      destruct 1; subst; (try contradiction); eauto.
    + eapply IHstar; eauto.
      intros. simpl.
      eapply topmost_no_return_cont_label.
      2: simpl in *; eauto.
      destruct 1; subst; (try contradiction); simpl; eauto 10.
    + simpl in *.
      generalize (call_cont_is_call_cont k).
      destruct (call_cont k) eqn:CALL_CONT; try contradiction.
      - intros _.
        rewrite topmost_fundef_of_cont_stop in H2 by assumption.
        inversion H2; clear H2; subst.
        eapply IHstar; eauto.
        * destruct (topmost_fundef_find_label (Some f)) as (K & _).
          erewrite K; eauto.
          reflexivity.
        * intros H2.
          generalize find_label_no_return_stop.
          destruct 1 as (K & _).
          eapply K with (l1 := nil); eauto.
          simpl. contradiction.
      - intros _.
        eapply IHstar; eauto.
        * destruct (topmost_fundef_find_label (Some f0)) as (K & _).
          erewrite K by eassumption.
          rewrite <- CALL_CONT.
          rewrite topmost_fundef_of_cont_call_cont.
          assumption.
        * intros H4.
          generalize find_label_no_return_call.
          destruct 1 as (K & _).
          eapply K; eauto.
          { simpl. congruence. }
          instantiate (1 := nil).
          rewrite <- CALL_CONT.
          eapply topmost_no_return_call_cont; eauto.
          congruence.
    + eapply IHstar; clear IHstar; simpl; eauto.
      simpl in WTC.
      simpl in H3.
      destruct k; try contradiction.
      - simpl in H2.
        inversion H2; clear H2; subst.
        intros H2.
        simpl.
        destruct 1; subst; auto.
      - intros H4.
        eapply topmost_no_return_call_cont_inv; eauto.
        simpl; congruence.
    + eapply IHstar; clear IHstar; simpl; eauto.
      simpl in H3.
      intros H1.
      eapply topmost_no_return_cont_ext.
      2: eauto.
      destruct 1; subst; simpl; auto.
  Qed.

  Lemma clight_funcall_wt ge κ l m v' m':
    Smallstep.plus Clight.step2 ge
      (Callstate (Internal (InlinableFunction.function κ)) l Kstop m)
      E0
      (Returnstate v' Kstop m') ->
    Val.has_type v' (typ_of_type (fn_return κ)).
  Proof.
    intros PLUS.
    apply Smallstep.plus_star in PLUS.
    eapply topmost_fundef_of_returnstate_has_type in PLUS.
    2: simpl; reflexivity.
    5: reflexivity.
    2: simpl; contradiction.
    2: apply ClightModules.InlinableFunction.no_return_void.
    2: simpl; auto.
    assumption.
  Qed.

End WITHCOMPILERCONFIGOPS.

