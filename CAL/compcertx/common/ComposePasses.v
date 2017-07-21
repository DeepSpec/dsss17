Require compcert.common.Globalenvs.

Import Coqlib.
Import Errors.
Import AST.
Import Globalenvs.

Set Implicit Arguments.

(* How to compose two transformations *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Lemma apply_partial_bind: apply_partial = Errors.bind.
Proof. reflexivity. Qed.

Notation "a @@@ b" :=
   (apply_partial a b) (at level 50, left associativity).

Definition compose_partial (A B C: Type) (f: A -> res B) (g: B -> res C) : A -> res C := fun a => (((OK a) @@@ f) @@@ g).

Notation "a ';;;' b" :=
  (compose_partial a b) (at level 50, left associativity).

Definition compose_partial' (A B C D: Type) (f: A -> B -> res C) (g: A -> C -> res D) : A -> B -> res D :=
  fun a b => f a b @@@ g a .

Notation "f '>>' g" := (compose_partial' f g) (at level 50, left associativity).

Ltac destr :=
  match goal with
    |- context [match ?a with _ => _ end] => destruct a eqn:?; simpl in *; try now intuition congruence
  | |- _ => simpl in *; try now intuition congruence
  end.

Ltac destr_in H :=
  match type of H with
    context [match ?a with _ => _ end] => destruct a eqn:?; simpl in *; try now intuition congruence
  end.

Ltac destr_hyps :=
  repeat
    match goal with
      H : _ |- _ => destr_in H
    end.

Ltac des t := destruct t eqn:?; simpl in *; try subst; try now intuition congruence.

Section Transf_partial2_compose.

Variables (A B C: Type) (ab: ident -> A -> res B) (bc: ident -> B -> res C)
         (U V W: Type) (uv: ident -> U -> res V) (vw: ident -> V -> res W).

Lemma transf_globdefs_compose: forall lau lbv,
    transf_globdefs ab uv lau = OK lbv ->
    transf_globdefs ( ab >> bc ) ( uv >> vw ) lau = transf_globdefs bc vw lbv.
Proof.
  induction lau; simpl.
  - intros lbv H; inv H. reflexivity.
  - des a. des o.
    + (* some *)
      des g.
      * (* fun *)
        unfold bind at 1.
        unfold compose_partial' at 1. unfold apply_partial.
        intros.
        des (ab i f). destr_in H. inv H. simpl.
        erewrite IHlau; eauto.
      * (* var *)
        unfold transf_globvar at 1. simpl.
        unfold transf_globvar at 1. unfold compose_partial' at 1. unfold apply_partial.
        intros.
        des (uv i (gvar_info v)).
        des (transf_globdefs ab uv lau). inv H.
        erewrite IHlau; eauto. reflexivity.
    + (* none *)
      case_eq (transf_globdefs ( ab) ( uv) lau); try discriminate; simpl.
      injection 2; intros; subst; simpl.
      erewrite IHlau; eauto.
Qed.

Lemma transf_globdefs_compose_error: forall lau msg,
  transf_globdefs ab uv lau = Error msg ->
  exists msg',
  transf_globdefs ( ab >> bc) ( uv >> vw ) lau = Error msg'.
Proof.
  induction lau; simpl.
  - discriminate.
  - des a; des o.
    + (* some *)
      destruct g.
      * (* fun *)
        unfold bind at 1.
        unfold compose_partial' at 1. unfold apply_partial.
        des (ab i f); eauto. destr.
        intros msg I; inv I.
        destruct (IHlau _ eq_refl) as (msg' & TG). rewrite TG.
        destr; eauto.
      * (* var *)
        unfold transf_globvar at 1. simpl.
        unfold transf_globvar at 1. unfold compose_partial' at 1. unfold apply_partial.
        destruct (uv i (gvar_info v)); simpl; eauto.
        des (transf_globdefs ab uv lau).
        intros ? I; inv I.
        destruct (IHlau _ eq_refl) as (msg' & TG). rewrite TG.
        destr; eauto.
    + (* none *)
      des (transf_globdefs ab uv lau).
      intros ? I; inv I.
      destruct (IHlau _ eq_refl) as (msg' & TG). rewrite TG.
      destr; eauto.
Qed.

Theorem transform_partial_program2_compose:
  forall pau pbv,
    transform_partial_program2 ab uv pau = OK pbv ->
    transform_partial_program2 bc vw pbv = transform_partial_program2 (ab >> bc) (uv >> vw) pau.
Proof.
  intros until pbv.
  destruct pau; simpl.
  unfold transform_partial_program2.
  intro H. monadInv H.
  erewrite transf_globdefs_compose; eauto.
Qed.

Theorem transform_partial_program2_compose_error:
  forall pau msg,
    transform_partial_program2 ab uv pau = Error msg ->
    exists msg',
      transform_partial_program2 (ab >> bc) (uv >> vw) pau = Error msg'.
Proof.
  intros until msg.
  destruct pau; simpl.
  unfold transform_partial_program2.
  simpl.
  case_eq (transf_globdefs (ab) ( uv) prog_defs); try discriminate.
  intros until 1.
  exploit transf_globdefs_compose_error; eauto.
  destruct 1 as [? ERR].
  rewrite ERR. simpl. eauto.
Qed.


Lemma transform_partial_program2_compose_out_in:
  forall pau pbv,
    ((transform_partial_program2 ab uv) ;;; (transform_partial_program2 bc vw)) pau = OK pbv ->
    transform_partial_program2 (ab >> bc) (uv >> vw) pau = OK pbv.
Proof.
  unfold compose_partial at 1.
  simpl.
  intros until pbv.
  des (transform_partial_program2 ab uv pau).
  intros.
  erewrite <- transform_partial_program2_compose; eauto.
Qed.

Lemma transform_partial_program2_compose_in_out:
  forall pau pbv,
    transform_partial_program2 (ab >> bc) (uv >> vw) pau = OK pbv ->
    ((transform_partial_program2 ab uv) ;;; (transform_partial_program2 bc vw)) pau = OK pbv.
Proof.
  unfold compose_partial.
  simpl.
  intros.
  des (transform_partial_program2 ab uv pau).
  erewrite transform_partial_program2_compose; eauto.
  edestruct (transform_partial_program2_compose_error); eauto. congruence.
Qed.

End Transf_partial2_compose.

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Notation "a @@ b" :=
   (apply_total a b) (at level 50, left associativity).

Definition compose_total_left (A B C: Type) (f: A -> B) (g: B -> res C) : A -> res C := fun a => ((OK a @@ f) @@@ g).

Notation "a '<;' b" :=
  (compose_total_left a b) (at level 50, left associativity).

Definition compose_total_left' (A B C D: Type) (f: B -> C) (g: A -> C -> res D) : A -> B -> res D :=
  fun a b => (OK (f b)) @@@ g a.

Notation "a '>>>' b" :=
  (compose_total_left' a b) (at level 50, left associativity).


Section Transf_partial2_compose_total_left.

Variables (A B C: Type) (ab: A -> B) (bc: ident -> B -> res C)
         (U W: Type) (uw: ident -> U -> res W).

Lemma ctl_rew: (ab >>> bc) = ((fun a b => OK (ab b)) >> bc).
Proof.
  reflexivity.
Qed.

Lemma id_compose_partial: uw = ((fun a b => OK b)  >> uw ).
Proof.
  reflexivity.
Qed.

Theorem transform_partial_program_compose_total_left:
  (transform_program ab) <; (transform_partial_program2 bc uw) = transform_partial_program2 (ab >>> bc) uw.
Proof.
  apply FunctionalExtensionality.functional_extensionality.
  intro.
  unfold compose_total_left. simpl.
  rewrite ctl_rew.
  rewrite id_compose_partial.
  apply transform_partial_program2_compose.
  apply transform_program_partial_program.
Qed.



End Transf_partial2_compose_total_left.

Definition compose_total_right (A B C: Type) (f: A -> res B) (g: B -> C) : A -> res C := fun a => (((OK a) @@@ f) @@ g).

Notation "a ';>' b" :=
  (compose_total_right a b) (at level 50, left associativity).

Definition compose_total_right' (A B C D: Type) (f: A -> B -> res C) (g: C -> D) : A -> B -> res D :=
  fun a b => (f a b) @@ g.

Notation "a '<<<' b" :=
  (compose_total_right' a b) (at level 50, left associativity).

Section Transf_partial2_compose_total_right.

  Variables (A B C: Type) (ab: ident -> A -> res B) (bc: B -> C)
            (U V: Type) (uv: ident -> U -> res V).

  Lemma ctr_rew: (ab <<< bc) = (ab >> (fun b c => OK (bc c))).
  Proof eq_refl.

  Lemma id_compose_partial': uv = (uv >> (fun a b => OK b)).
  Proof.
    apply FunctionalExtensionality.functional_extensionality.
    intro; apply FunctionalExtensionality.functional_extensionality.
    intros.
    unfold compose_partial', apply_partial. destr.
  Qed.

  Theorem transform_partial_program2_compose_right:
    forall pau pbv,
      transform_partial_program2 ab uv pau = OK pbv ->
      transform_partial_program2 (ab <<< bc) uv pau = OK (transform_program bc pbv).
  Proof.
    intros.
    rewrite ctr_rew.
    rewrite id_compose_partial'.
    erewrite <- transform_partial_program2_compose; eauto.
    apply transform_program_partial_program.
  Qed.

  Theorem transform_partial_program2_compose_right_error:
    forall pau msg,
      transform_partial_program2 ab uv pau = Error msg ->
      exists msg',
        transform_partial_program2 (ab <<< bc) uv pau = Error msg'.
  Proof.
    intros.
    rewrite ctr_rew, id_compose_partial'.
    eapply transform_partial_program2_compose_error; eauto.
  Qed.

End Transf_partial2_compose_total_right.

Lemma compose_partial_intro:
  forall
    (A B C: Type)
    (ab: A -> res B)
    (bc:  B -> res C)
    a b, ab a = OK b ->
         forall c, bc b = OK c ->
              (ab ;;; bc) a = OK c.
Proof.
  unfold compose_partial. intros.
  simpl. rewrite H. simpl.
  assumption.
Qed.

Lemma compose_partial_elim:
  forall (A B C: Type)
         (ab: A -> res B)
         (bc: B -> res C)
         a c, (ab ;;; bc) a = OK c ->
              {b | ab a = OK b /\ bc b = OK c}.
Proof.
  unfold compose_partial; simpl.
  intros until c.
  destruct (ab a); simpl; try discriminate.
  eauto.
Qed.

Lemma compose_total_left_elim:
  forall (A B C: Type)
         (ab: A -> B)
         (bc: B -> res C)
         a c, (ab <; bc) a = OK c ->
              bc (ab a) = OK c.
Proof.
  tauto.
Qed.

Lemma compose_total_left_intro:
  forall (A B C: Type)
         a (ab: A -> B) b c (bc: B -> res C),
    ab a = b ->
    bc b = OK c ->
    (ab <; bc) a = OK c.
Proof.
  unfold compose_total_left. simpl. intros; subst. assumption.
Qed.

Lemma compose_total_right_elim:
  forall (A B C: Type)
         (ab: A -> res B)
         (bc: B -> C)
         a c, (ab ;> bc) a = OK c ->
                {b | ab a = OK b /\ bc b = c}.
Proof.
  unfold compose_total_right; simpl.
  intros until c.
  destruct (ab a); simpl; try discriminate.
  inversion 1; subst; eauto.
Qed.

Lemma compose_total_right_intro:
  forall (A B C: Type)
         a (ab: A -> res B) b c (bc: B -> C),
    ab a = OK b ->
    bc b = c ->
    (ab ;> bc) a = OK c.
Proof.
  unfold compose_total_right; simpl.
  intros until bc.
  intros.
  rewrite H.
  simpl.
  congruence.
Qed.

Lemma compose_partial_intro':
  forall
    (A B C: Type)
    (ab: ident -> A -> res B)
    (bc: ident -> B -> res C)
    i a b, ab i a = OK b ->
         forall c, bc i b = OK c ->
                   (ab >> bc) i a = OK c.
Proof.
  unfold compose_partial'. intros.
  rewrite H. simpl.
  assumption.
Qed.

Lemma compose_partial_elim':
  forall (A B C: Type)
         (ab: ident -> A -> res B)
         (bc: ident -> B -> res C)
         i a c, (ab >> bc) i a = OK c ->
              {b | ab i a = OK b /\ bc i b = OK c}.
Proof.
  unfold compose_partial'; simpl.
  intros until c.
  destruct (ab i a); simpl; try discriminate.
  eauto.
Qed.

Lemma compose_total_left_elim':
  forall (A B C: Type)
         (ab: A -> B)
         (bc: ident -> B -> res C)
         i a c, (ab >>> bc) i a = OK c ->
                bc i (ab a) = OK c.
Proof.
  tauto.
Qed.

Lemma compose_total_left_intro':
  forall (A B C: Type)
         a (ab: A -> B) b c (bc: ident -> B -> res C) i,
    ab a = b ->
    bc i b = OK c ->
    (ab >>> bc) i a = OK c.
Proof.
  unfold compose_total_left'. simpl. intros; subst. assumption.
Qed.

Lemma compose_total_right_elim':
  forall (A B C: Type)
         (ab: ident -> A -> res B)
         (bc: B -> C)
         i a c, (ab <<< bc) i a = OK c ->
                {b | ab i a = OK b /\ bc b = c}.
Proof.
  unfold compose_total_right'; simpl.
  intros until c.
  destruct (ab i a); simpl; try discriminate.
  inversion 1; subst; eauto.
Qed.

Lemma compose_total_right_intro':
  forall (A B C: Type)
         a (ab: ident -> A -> res B) b c (bc: B -> C) i,
    ab i a = OK b ->
    bc b = c ->
    (ab <<< bc) i a = OK c.
Proof.
  unfold compose_total_right'; simpl.
  intros until bc.
  intros.
  rewrite H.
  simpl.
  congruence.
Qed.

Ltac compose_elim t :=
  match goal with
    | [ H : (?ab ;;; ?bc) ?a = OK ?c |- _] =>
            apply compose_partial_elim in H;
            let b := fresh "b" in
            let Hab := fresh "Hab" in
            let Hbc := fresh "Hbc" in
            destruct H as [b [Hab Hbc]]; t
    | [ H : (?ab <; ?bc) ?a = OK ?c |- _] =>
            apply compose_total_left_elim in H
    | [ H : (?ab ;> ?bc) ?a = OK ?c |- _] =>
            apply compose_total_right_elim in H;
            let b := fresh "b" in
            let Hab := fresh "Hab" in
            let Hbc := fresh "Hbc" in
            destruct H as [b [Hab Hbc]]; subst; t
    | [ H : (?ab >> ?bc) ?i ?a = OK ?c |- _] =>
            apply compose_partial_elim' in H;
            let b := fresh "b" in
            let Hab := fresh "Hab" in
            let Hbc := fresh "Hbc" in
            destruct H as [b [Hab Hbc]]; t
    | [ H : (?ab >>> ?bc) ?i ?a = OK ?c |- _] =>
            apply compose_total_left_elim' in H
    | [ H : (?ab <<< ?bc) ?i ?a = OK ?c |- _] =>
            apply compose_total_right_elim' in H;
            let b := fresh "b" in
            let Hab := fresh "Hab" in
            let Hbc := fresh "Hbc" in
            destruct H as [b [Hab Hbc]]; subst; t
    | [ H : OK ?a = OK ?b |- _] => inv H
  end.

Lemma apply_partial_elim:
  forall (A B: Type)
         (oa: res A)
         (ab: A -> res B)
         (b: B),
    oa @@@ ab = OK b ->
    {a | oa = OK a /\ ab a = OK b}.
Proof.
  unfold apply_partial; simpl.
  destruct oa; try discriminate.
  eauto.
Qed.

Lemma apply_total_elim:
  forall (A B: Type)
         (oa: res A)
         (ab: A -> B)
         (b: B),
    oa @@ ab = OK b ->
    {a | oa = OK a /\ ab a = b}.
Proof.
  unfold apply_total; simpl.
  destruct oa; try discriminate.
  inversion 1; subst; eauto.
Qed.

Ltac apply_elim t :=
  match goal with
    | [ H : ?oa @@@ ?ab = OK ?b |- _] =>
            apply apply_partial_elim in H;
            let a := fresh "a" in
            let Hal := fresh "Hal" in
            let Har := fresh "Har" in
            destruct H as [a [Hal Har]]; t
    | [ H : ?oa @@ ?ab = OK ?b |- _] =>
      apply apply_total_elim in H;
        let a := fresh "a" in
        let Hal := fresh "Hal" in
        let Har := fresh "Har" in
        destruct H as [a [Hal Har]]; subst; t
    | [ H : OK ?a = OK ?b |- _] => inv H
  end.

Lemma apply_partial_intro:
  forall (A: Type)
         (oa: res A) (a: A),
    oa = OK a ->
    forall (B: Type) (ab: A -> res B) (b: B),
      ab a = OK b ->
    oa @@@ ab = OK b.
Proof.
  unfold apply_partial; simpl.
  destruct oa; simpl; try discriminate.
  inversion 1; subst; eauto.
Qed.

Lemma apply_total_intro:
  forall (A: Type)
         (oa: res A) (a: A),
    oa = OK a ->
    forall (B: Type) (ab: A -> B) (b: B),
      ab a = b ->
    oa @@ ab = OK b.
Proof.
  unfold apply_partial; simpl.
  destruct oa; simpl; try discriminate.
  inversion 1; subst; congruence.
Qed.

Definition compose {A B C: Type} (ab: A -> B) (bc: B -> C): A -> C.
Proof. tauto. Defined.

Notation " ab '|>' bc" := (compose ab bc) (at level 50, left associativity).

Lemma transf_program_compose:
  forall (A B C V: Type) (ab: A -> B) (bc: B -> C),
    transform_program (ab |> bc) = (transform_program ab) |> (transform_program (V := V) bc).
Proof.
  unfold transform_program, compose. intros. apply FunctionalExtensionality.functional_extensionality. destruct x; simpl. f_equal.
  induction prog_defs; simpl; eauto.
  f_equal; auto.
  unfold transform_program_globdef. destruct a; simpl. destruct o; simpl; auto. destruct g; simpl; auto.
Qed.

Lemma transform_partial_program15_compose_out_in:
  forall {A B C U V: Type} (ab: ident -> A -> res B) (bc: B -> res C) (uv: ident -> U -> res V),
  forall pau pbv,
    ((transform_partial_program2 ab uv) ;;; (transform_partial_program bc)) pau = OK pbv ->
    transform_partial_program2 (ab >> (fun _ => bc)) uv pau = OK pbv.
Proof.
  intros until pbv. unfold transform_partial_program.
  replace (fun p : AST.program B V =>
             transform_partial_program2 (fun _ f => bc f) (fun _ v => OK v) p)
  with (transform_partial_program2 (fun _ => bc) (fun _ => @OK V)) by reflexivity.
  intro.
  erewrite (id_compose_partial uv).
  erewrite <- transform_partial_program2_compose_out_in. 2: eauto.
  unfold compose_partial'. simpl.
  f_equal.
  apply FunctionalExtensionality.functional_extensionality.
  intros.   apply FunctionalExtensionality.functional_extensionality.
  intros; des (uv x x0).
Qed.

Lemma transform_partial_program15_compose_in_out:
  forall {A B C U V: Type} (ab: ident -> A -> res B) (bc: B -> res C) (uv: ident -> U -> res V),
  forall pau pbv,
    transform_partial_program2 (ab >> (fun _ => bc)) uv pau = OK pbv ->
    ((transform_partial_program2 ab uv) ;;; (transform_partial_program bc)) pau = OK pbv.
Proof.
  intros until pbv. unfold transform_partial_program.
  replace (fun p : AST.program B V =>
             transform_partial_program2 (fun _ f => bc f) (fun _ v => OK v) p)
  with (transform_partial_program2 (fun _ => bc) (fun _ => @OK V)) by reflexivity.
  intro.
  erewrite (id_compose_partial uv) in H.
  eapply transform_partial_program2_compose_in_out; eauto.
  rewrite <- H; f_equal.
  unfold compose_partial'. simpl. apply FunctionalExtensionality.functional_extensionality.
  intros; apply FunctionalExtensionality.functional_extensionality.
  intro x0; destruct (uv x x0); reflexivity.
Qed.

Lemma transform_partial_program_compose_out_in:
  forall {A B C U: Type} (ab: A -> res B) (bc: B -> res C),
  forall pau pbv,
    ((transform_partial_program ab) ;;; (transform_partial_program bc (V := U))) pau = OK pbv ->
    transform_partial_program (ab ;;; bc) pau = OK pbv.
Proof.
  intros until pbv. unfold transform_partial_program at 1 3.
  eapply transform_partial_program15_compose_out_in; eauto.
Qed.

Lemma transform_partial_program_compose_in_out:
  forall {A B C U: Type} (ab: A -> res B) (bc: B -> res C),
  forall pau pbv,
    transform_partial_program (V := U) (ab ;;; bc) pau = OK pbv ->
    ((transform_partial_program ab) ;;; (transform_partial_program bc)) pau = OK pbv.
Proof.
  intros until pbv. unfold transform_partial_program at 1 2.
  eapply transform_partial_program15_compose_in_out; eauto.
Qed.

Lemma transform_partial_program_compose_right_out_in:
  forall (A B C U: Type)
    (ab: A -> res B)
    (bc: B -> C)
    a c,
    ((transform_partial_program ab) ;> (transform_program (V := U) bc)) a = OK c ->
    transform_partial_program (ab ;> bc) a = OK c.
Proof.
  unfold transform_partial_program.
  intros until c.
  intro.
  compose_elim idtac.
  eapply transform_partial_program2_compose_right.
  assumption.
Qed.

Lemma comp_total_right_eq {A B C : Type} (ab: A -> res B) (bc: B -> C):
    (fun (_: ident) f => (ab ;> bc) f) = ((fun (_:ident) => ab) <<< bc).
Proof eq_refl.

Lemma transform_partial_program_compose_right_in_out:
  forall (A B C U: Type)
    (ab: A -> res B)
    (bc: B -> C)
    a c,
    transform_partial_program (ab ;> bc) a = OK c ->
    ((transform_partial_program ab) ;> (transform_program (V := U) bc)) a = OK c.
Proof.
  unfold transform_partial_program.
  intros until c.
  intro.
  case_eq (transform_partial_program2 (fun _ => ab) (fun _ v => OK v) a).
  intros.
  eapply compose_total_right_intro.
  eassumption.
  rewrite comp_total_right_eq in H.
  erewrite transform_partial_program2_compose_right in H; eauto.
  congruence.
  intros.
  exfalso.
  rewrite comp_total_right_eq in H.
  edestruct (transform_partial_program2_compose_right_error) with (bc:=bc). apply H0.
  congruence.
Qed.

Lemma genv_next_apply_total:
  forall {A U B V: Type} (tr: AST.program A U -> AST.program B V),
    (forall p, Genv.genv_next (Genv.globalenv (tr p)) = Genv.genv_next (Genv.globalenv p)) ->
    forall n (r: res (AST.program A U)),
      (forall p, r = OK p -> Genv.genv_next (Genv.globalenv p) = n) ->
      forall p, r @@ tr = OK p ->
                Genv.genv_next (Genv.globalenv p) = n.
Proof.
  intros. unfold apply_total in H1. destruct r; try discriminate. inv H1. erewrite H. eauto.
Qed.

Lemma genv_next_apply_partial:
  forall {A U B V: Type} (tr: AST.program A U -> res (AST.program B V)),
    (forall p p', tr p = OK p' -> Genv.genv_next (Genv.globalenv p') = Genv.genv_next (Genv.globalenv p)) ->
    forall n (r: res (AST.program A U)),
      (forall p, r = OK p -> Genv.genv_next (Genv.globalenv p) = n) ->
      forall p, r @@@ tr = OK p ->
                Genv.genv_next (Genv.globalenv p) = n.
Proof.
  intros. unfold apply_partial in H1. destruct r; try discriminate. erewrite H; eauto.
Qed.
