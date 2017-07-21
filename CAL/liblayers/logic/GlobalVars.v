Require Import Decision.
Require Import PseudoJoin.
Require Import OptionOrders.
Require Import ErrorMonad.

Class GlobalVarsOps (V: Type): Type :=
  {
    globalvar_eq_dec :> EqDec V
  }.

(* For future use.
<<
Class GlobalVars V {gv_ops: GlobalVarsOps V}: Prop :=
  {
  }.
>>
*)

Section WITHGLOBALVARSOPS.
Context `{gvar_ops: GlobalVarsOps}.

Global Instance res_globalvar_oplus:
  Oplus (res V) :=
  {
    oplus rv1 rv2 :=
      _ <- eassert nil (rv1 = rv2);
    rv1
  }.

Lemma res_globalvar_oplus_def rv1 rv2:
  rv1 ⊕ rv2 =
      _ <- eassert nil (rv1 = rv2);
    rv1.
Proof.
  reflexivity.
Qed.

Global Opaque res_globalvar_oplus.

Lemma res_globalvar_oplus_idem (rv: res V):
  rv ⊕ rv = rv.
Proof.
  rewrite res_globalvar_oplus_def.
  eassert_true; auto.
Qed.

Hint Rewrite res_globalvar_oplus_idem: res_globalvar.

Lemma res_globalvar_oplus_diff (rv1 rv2: res V):
  rv1 <> rv2 ->
  rv1 ⊕ rv2 = Error nil.
Proof.
  intros.
  rewrite res_globalvar_oplus_def.
  eassert_false; auto.
Qed.

Lemma res_globalvar_oplus_comm (rv1 rv2: res V):
  rv1 ⊕ rv2 = rv2 ⊕ rv1.
Proof.
  rewrite res_globalvar_oplus_def.
  destruct (decide (rv1 = rv2));
    rewrite res_globalvar_oplus_def.
  + repeat (eassert_true; auto).
  + repeat (eassert_false; auto).
Qed.  

Lemma res_globalvar_oplus_error_nil_left rv:
  rv ⊕ Error nil = Error nil.
Proof.
  destruct (decide (rv = Error nil));
  subst;
  autorewrite with res_globalvar;
  auto.
  apply res_globalvar_oplus_diff; auto.
Qed.

Hint Rewrite res_globalvar_oplus_error_nil_left: res_globalvar.

Lemma res_globalvar_oplus_error_nil_right rv:
  Error nil ⊕ rv  = Error nil.
Proof.
  rewrite res_globalvar_oplus_comm.
  autorewrite with res_globalvar.
  reflexivity.
Qed.

Hint Rewrite res_globalvar_oplus_error_nil_right: res_globalvar.

Lemma res_globalvar_oplus_ok_error v e:
  OK v ⊕ Error e = Error nil.
Proof.
  reflexivity.
Qed.

Hint Rewrite res_globalvar_oplus_ok_error: res_globalvar.

Lemma res_globalvar_oplus_error_ok e v:
  Error e ⊕ OK v = Error nil.
Proof.
  reflexivity.
Qed.

Hint Rewrite res_globalvar_oplus_error_ok: res_globalvar.

Lemma res_globalvar_oplus_error_left e1 v:
  isError (Error e1 ⊕ v).
Proof.
  rewrite res_globalvar_oplus_def.
  destruct (decide (Error e1 = v)).
  + eassert_true; eauto.
  + eassert_false; eauto.
Qed.

Lemma res_globalvar_oplus_error_right v e1:
  isError (v ⊕ Error e1).
Proof.
  rewrite res_globalvar_oplus_comm.
  apply res_globalvar_oplus_error_left.
Qed.

Lemma res_globalvar_oplus_assoc (rv1 rv2 rv3: res V):
  (rv1 ⊕ rv2) ⊕ rv3 = rv1 ⊕ (rv2 ⊕ rv3).
Proof.
  destruct (decide (rv1 = rv2)).
  + subst. autorewrite with res_globalvar.
    destruct (decide (rv2 = rv3)).
    - subst. autorewrite with res_globalvar. reflexivity.
    - rewrite (res_globalvar_oplus_diff rv2 rv3); auto.
      autorewrite with res_globalvar.
      reflexivity.
  + rewrite (res_globalvar_oplus_diff rv1 rv2); auto.
    autorewrite with res_globalvar.
    destruct (decide (rv2 = rv3)).
    - subst. autorewrite with res_globalvar.
      symmetry. apply res_globalvar_oplus_diff. assumption.
    - rewrite (res_globalvar_oplus_diff rv2 rv3); auto.
      autorewrite with res_globalvar.
      reflexivity.
Qed.      

Local Instance res_globalvar_le {gvar_ops: GlobalVarsOps V}:
  Le (res V) :=
  {
    le := res_le eq
  }.

Local Instance res_globalvar_oplus_left_upper_bound:
  LeftUpperBound (A := res V) (≤) (⊕).
Proof.
  repeat red.
  intros x y.
  destruct (decide (x = y)); subst; autorewrite with res_globalvar.
  + subst. reflexivity.
  + rewrite res_globalvar_oplus_diff; auto. constructor.
Qed.

Local Instance res_globalvar_oplus_mono:
  @Proper (res V -> res V -> res V) ((≤) ++> (≤) ++> (≤)) (⊕).
Proof.
  repeat red.
  intros x y H x0 y0 H0.
  rewrite (res_globalvar_oplus_def y y0).
  destruct (decide (y = y0)); [ eassert_true | eassert_false ]; auto;
  try constructor.
  subst.
  inversion H0; subst; inversion H; subst; try constructor.
  rewrite res_globalvar_oplus_def.
  eassert_true; auto.
Qed.

Ltac res_globalvar_red :=
  autorewrite with res_globalvar;
  repeat (
      match goal with
          [ |- context [ Error ?v1 ⊕ ?v2 ] ] =>
          let e := fresh "e" in
          let He := fresh "H" e in
          destruct (res_globalvar_oplus_error_left v1 v2) as [e He];
          rewrite He;
          autorewrite with res_globalvar
      end
    ).

Lemma res_globalvar_lub (v1 v2 v: res V):
  v1 ≤ v ->
  v2 ≤ v ->
  v1 ⊕ v2 ≤ v.
Proof.
  inversion 1; subst; inversion 1; subst;
  res_globalvar_red;
  auto;
  constructor.
Qed.

Global Instance option_res_globalvar_oplus:
  Oplus (option (res V)) :=
  {
    oplus orv1 orv2 :=
      match orv1, orv2 with
        | None, _ => orv2
        | _, None => orv1
        | Some rv1, Some rv2 => Some (rv1 ⊕ rv2)
      end
  }.

Lemma option_res_globalvar_oplus_def orv1 orv2:
  orv1 ⊕ orv2 =
  match orv1, orv2 with
    | None, _ => orv2
    | _, None => orv1
    | Some rv1, Some rv2 => Some (rv1 ⊕ rv2)
  end.
Proof.
  reflexivity.
Qed.

Global Opaque option_res_globalvar_oplus.

Lemma option_res_globalvar_oplus_none_left rv:
  None ⊕ rv = rv.
Proof.
  destruct rv; auto.
Qed.

Hint Rewrite option_res_globalvar_oplus_none_left: option_res_globalvar.

Lemma option_res_globalvar_oplus_none_right rv:
  rv ⊕ None = rv.
Proof.
  destruct rv; auto.
Qed.

Hint Rewrite option_res_globalvar_oplus_none_right: option_res_globalvar.

Lemma option_res_globalvar_oplus_some rv1 rv2:
  Some rv1 ⊕ Some rv2 = Some (rv1 ⊕ rv2).
Proof.
  reflexivity.
Qed.

Hint Rewrite option_res_globalvar_oplus_some: option_res_globalvar.

Lemma option_res_globalvar_oplus_idem rv:
  rv ⊕ rv = rv.
Proof.
  destruct rv; auto.
  rewrite option_res_globalvar_oplus_def.
  autorewrite with res_globalvar.
  reflexivity.
Qed.

Hint Rewrite option_res_globalvar_oplus_idem: option_res_globalvar.

Lemma option_res_globalvar_oplus_comm (rv1 rv2: option (res V)):
  rv1 ⊕ rv2 = rv2 ⊕ rv1.
Proof.
  destruct rv1; destruct rv2; autorewrite with option_res_globalvar; auto.
  rewrite res_globalvar_oplus_comm.
  reflexivity.
Qed.

Lemma option_res_globalvar_oplus_assoc (rv1 rv2 rv3: option (res V)):
  (rv1 ⊕ rv2) ⊕ rv3 = rv1 ⊕ (rv2 ⊕ rv3).
Proof.
  destruct rv1; destruct rv2; destruct rv3;
  autorewrite with option_res_globalvar;
  auto.
  rewrite res_globalvar_oplus_assoc.
  reflexivity.
Qed.

Lemma option_res_globalvar_oplus_error_nil_left rv:
  Some (Error nil) ⊕ rv = Some (Error nil).
Proof.
  destruct rv; autorewrite with option_res_globalvar; auto.
  autorewrite with res_globalvar; auto.
Qed.

Hint Rewrite option_res_globalvar_oplus_error_nil_left: option_res_globalvar.

Lemma option_res_globalvar_oplus_error_nil_right rv:
  rv ⊕ Some (Error nil)  = Some (Error nil).
Proof.
  rewrite option_res_globalvar_oplus_comm.
  autorewrite with option_res_globalvar.
  reflexivity.
Qed.

Hint Rewrite option_res_globalvar_oplus_error_nil_right: option_res_globalvar.

Global Instance option_res_globalvar_le {gvar_ops: GlobalVarsOps V}:
  Le (option (res V)) :=
  {
    le := option_le (≤)
  }.

Local Instance option_res_globalvar_oplus_mono:
  @Proper (option (res V) -> _ -> _) ((≤) ++> (≤) ++> (≤)) (⊕).
Proof.
  repeat red.
  intros x y H x0 y0 H0.
  inversion H; clear H; subst; inversion H0; clear H0; subst;
  autorewrite with option_res_globalvar.
  + constructor.
  + destruct y; autorewrite with option_res_globalvar; constructor; auto.
    rewrite res_globalvar_oplus_comm.
    simpl (≤).
    etransitivity; eauto.
    apply res_globalvar_oplus_left_upper_bound.
  + destruct y0; autorewrite with option_res_globalvar; constructor; auto.
    simpl (≤).
    etransitivity; eauto.
    apply res_globalvar_oplus_left_upper_bound.
  + constructor.
    solve_monotonic.
Qed.

Global Instance option_res_globalvar_pseudojoin:
  PseudoJoin (option (res V)) None.
Proof.
  constructor; simpl (≤); try typeclasses eauto.
  + split; typeclasses eauto.
  + repeat red. intros; autorewrite with option_res_globalvar; reflexivity.
  + repeat red. intros. rewrite option_res_globalvar_oplus_assoc. reflexivity.
  + repeat red. intros. rewrite option_res_globalvar_oplus_comm. reflexivity.
  + repeat red. intros x y.
    destruct x; try constructor.
    destruct y; autorewrite with option_res_globalvar; repeat constructor.
    - apply res_globalvar_oplus_left_upper_bound.
    - reflexivity.
Qed.
  
Lemma option_res_globalvar_lub (v1 v2 v: option (res V)):
  v1 ≤ v ->
  v2 ≤ v ->
  v1 ⊕ v2 ≤ v.
Proof.
  inversion 1; subst; inversion 1; subst;
  autorewrite with option_res_globalvar;
  constructor; auto using res_globalvar_lub.
Qed.


Global Instance res_option_globalvar_oplus:
  Oplus (res (option V)) :=
  {
    oplus rov1 rov2 :=
      option_res_flip (res_option_flip rov1 ⊕ res_option_flip rov2)
  }.

Lemma res_option_globalvar_oplus_def rov1 rov2:
  rov1 ⊕ rov2 =
  option_res_flip (res_option_flip rov1 ⊕ res_option_flip rov2).
Proof.
  reflexivity.
Qed.

Global Opaque res_option_globalvar_oplus.

Lemma res_option_globalvar_oplus_none_left (rv: res (option V)):
  OK None ⊕ rv = rv.
Proof.
  rewrite res_option_globalvar_oplus_def.
  simpl.
  autorewrite with option_res_globalvar.
  apply res_option_flip_inv.
Qed.

Hint Rewrite res_option_globalvar_oplus_none_left: res_option_globalvar.

Lemma res_option_globalvar_oplus_comm (rv1 rv2: res (option V)):
  rv1 ⊕ rv2 = rv2 ⊕ rv1.
Proof.
  repeat rewrite res_option_globalvar_oplus_def.
  rewrite option_res_globalvar_oplus_comm.
  reflexivity.
Qed.

Lemma res_option_globalvar_oplus_none_right (rv: res (option V)):
  rv ⊕ OK None = rv.
Proof.
  rewrite res_option_globalvar_oplus_comm.
  autorewrite with res_option_globalvar.
  reflexivity.
Qed.

Hint Rewrite res_option_globalvar_oplus_none_right: res_option_globalvar.

Lemma res_option_globalvar_oplus_idem (rv: res (option V)):
  rv ⊕ rv = rv.
Proof.
  rewrite res_option_globalvar_oplus_def.
  autorewrite with option_res_globalvar.
  apply res_option_flip_inv.
Qed.

Hint Rewrite res_option_globalvar_oplus_idem: res_option_globalvar.

Lemma res_option_globalvar_oplus_error_nil_left (rv: res (option V)):
  Error nil ⊕ rv = Error nil.
Proof.
  rewrite res_option_globalvar_oplus_def.
  autorewrite with option_res_globalvar.
  reflexivity.
Qed.

Hint Rewrite res_option_globalvar_oplus_error_nil_left: res_option_globalvar.

Lemma res_option_globalvar_oplus_error_nil_right (rv: res (option V)):
  rv ⊕ Error nil = Error nil.
Proof.
  rewrite res_option_globalvar_oplus_comm.
  autorewrite with res_option_globalvar.
  reflexivity.
Qed.

Hint Rewrite res_option_globalvar_oplus_error_nil_right: res_option_globalvar.

Lemma res_option_globalvar_oplus_diff (v1 v2: V):
  v1 <> v2 ->
  OK (Some v1) ⊕ OK (Some v2) = Error nil.
Proof.
  intros H.
  rewrite res_option_globalvar_oplus_def.
  simpl.
  rewrite option_res_globalvar_oplus_def.
  rewrite res_globalvar_oplus_diff by congruence.
  reflexivity.
Qed.

Lemma res_option_globalvar_oplus_ok_error v e:
  OK (Some v) ⊕ Error e = Error nil.
Proof.
  reflexivity.
Qed.

Hint Rewrite res_option_globalvar_oplus_ok_error: res_option_globalvar.

Lemma res_option_globalvar_oplus_error_ok v e:
  Error e  ⊕ OK (Some v) = Error nil.
Proof.
  reflexivity.
Qed.

Hint Rewrite res_option_globalvar_oplus_error_ok: res_option_globalvar.

Lemma res_option_globalvar_oplus_error_left e (rv: res (option V)):
  isError (Error e ⊕ rv).
Proof.
  rewrite res_option_globalvar_oplus_def.
  simpl.
  destruct rv as [ [ | ] | e' ]; simpl;
  autorewrite with option_res_globalvar;
  simpl; eauto;
  res_globalvar_red;
  eauto.
Qed.

Lemma res_option_globalvar_oplus_error_right (rv: res (option V)) e:
  isError (rv ⊕ Error e).
Proof.
  rewrite res_option_globalvar_oplus_comm.
  apply res_option_globalvar_oplus_error_left.
Qed.

Lemma res_option_globalvar_oplus_assoc (rv1 rv2 rv3: res (option V)):
  (rv1 ⊕ rv2) ⊕ rv3 = rv1 ⊕ (rv2 ⊕ rv3).
Proof.
  repeat rewrite res_option_globalvar_oplus_def.
  repeat rewrite option_res_flip_inv.
  rewrite option_res_globalvar_oplus_assoc.
  reflexivity.
Qed.

Global Instance res_option_globalvar_le {gvar_ops: GlobalVarsOps V}:
  Le (res (option V)) :=
  {
    le := res_le (option_le eq)
  }.

Global Instance res_option_globalvar_pseudojoin:
  PseudoJoin (res (option V)) (OK None).
Proof.
  constructor; simpl (≤); try typeclasses eauto.
  + split; typeclasses eauto.
  + repeat red.
    intros.
    repeat rewrite res_option_globalvar_oplus_def.
    apply option_res_le_flip.
    solve_monotonic.
  + repeat red.
    intros.
    autorewrite with res_option_globalvar.
    reflexivity.
  + repeat red.
    intros.
    rewrite res_option_globalvar_oplus_assoc.
    reflexivity.
  + repeat red.
    intros.
    rewrite res_option_globalvar_oplus_comm.
    reflexivity.
  + repeat red.
    intros.
    rewrite res_option_globalvar_oplus_def.
    etransitivity;
      [ |
        eapply option_res_le_flip;
          exact (oplus_le_left (res_option_flip x) (res_option_flip y)) ].
    rewrite res_option_flip_inv.
    reflexivity.
Qed.

Lemma res_option_globalvar_lub (v1 v2 v: res (option V)):
  v1 ≤ v ->
  v2 ≤ v ->
  v1 ⊕ v2 ≤ v.
Proof.
  simpl.
  intros H H0.
  rewrite <- res_option_le_flip in H.
  rewrite <- res_option_le_flip in H0.
  rewrite <- res_option_le_flip.
  rewrite res_option_globalvar_oplus_def.
  rewrite option_res_flip_inv.
  apply option_res_globalvar_lub; auto.
Qed.

End WITHGLOBALVARSOPS.

Hint Rewrite @res_globalvar_oplus_idem: res_globalvar.
Hint Rewrite @res_globalvar_oplus_error_nil_left: res_globalvar.
Hint Rewrite @res_globalvar_oplus_error_nil_right: res_globalvar.
Hint Rewrite @res_globalvar_oplus_ok_error: res_globalvar.
Hint Rewrite @res_globalvar_oplus_error_ok: res_globalvar.
Hint Rewrite @option_res_globalvar_oplus_none_left: option_res_globalvar.
Hint Rewrite @option_res_globalvar_oplus_none_right: option_res_globalvar.
Hint Rewrite @option_res_globalvar_oplus_some: option_res_globalvar.
Hint Rewrite @option_res_globalvar_oplus_idem: option_res_globalvar.
Hint Rewrite @option_res_globalvar_oplus_error_nil_left: option_res_globalvar.
Hint Rewrite @option_res_globalvar_oplus_error_nil_right: option_res_globalvar.
Hint Rewrite @res_option_globalvar_oplus_none_left: res_option_globalvar.
Hint Rewrite @res_option_globalvar_oplus_none_right: res_option_globalvar.
Hint Rewrite @res_option_globalvar_oplus_idem: res_option_globalvar.
Hint Rewrite @res_option_globalvar_oplus_error_nil_left: res_option_globalvar.
Hint Rewrite @res_option_globalvar_oplus_error_nil_right: res_option_globalvar.
Hint Rewrite @res_option_globalvar_oplus_ok_error: res_option_globalvar.
Hint Rewrite @res_option_globalvar_oplus_error_ok: res_option_globalvar.

Ltac res_globalvar_red :=
  autorewrite with res_globalvar;
  repeat (
      match goal with
          [ |- context [ Error ?v1 ⊕ ?v2 ] ] =>
          let e := fresh "e" in
          let He := fresh "H" e in
          destruct (res_globalvar_oplus_error_left v1 v2) as [e He];
          rewrite He;
          autorewrite with res_globalvar
          | [ |- context [ ?v2 ⊕ Error ?v1 ] ] =>
          let e := fresh "e" in
          let He := fresh "H" e in
          destruct (res_globalvar_oplus_error_right v2 v1) as [e He];
          rewrite He;
          autorewrite with res_globalvar
      end
    ).

Ltac res_option_globalvar_red :=
  autorewrite with res_option_globalvar;
  repeat (
      match goal with
          [ |- context [ Error ?v1 ⊕ ?v2 ] ] =>
          let e := fresh "e" in
          let He := fresh "H" e in
          destruct (res_option_globalvar_oplus_error_left v1 v2) as [e He];
          rewrite He;
          autorewrite with res_option_globalvar
          | [ |- context [ ?v2 ⊕ Error ?v1 ] ] =>
          let e := fresh "e" in
          let He := fresh "H" e in
          destruct (res_option_globalvar_oplus_error_right v2 v1) as [e He];
          rewrite He;
          autorewrite with res_option_globalvar
      end
    ).
