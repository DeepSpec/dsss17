Require Export Monad.
Require Import Decision.

(** * The [option] monad *)

(** ** [option] is a fully invertible monad *)

Section INSTANCES.
  Global Instance option_monad_ops: MonadOps option := {
    bind A B f mx :=
      match mx with
        | Some a => f a
        | None => None
      end;
    ret := @Some
  }.

  Global Instance option_monad: Monad option.
  Proof.
    split; intros; try destruct m; try reflexivity.
    typeclasses eauto.
  Qed.

  Global Instance option_inv_ret: MonadInvRet option.
  Proof.
    intros A x y H.
    inversion H; reflexivity.
  Qed.

  Global Instance option_inv_bind: MonadInvBind option.
  Proof.
    intros A B f ma b.
    destruct ma.
    - exists a; reflexivity.
    - discriminate.
  Qed.
End INSTANCES.

(** ** Some [option]-specific rewrite rule *)

Lemma option_bind_none {A B} (f: A -> option B):
  bind f None = None.
Proof.
  reflexivity.
Qed.

Hint Rewrite @option_bind_none : monad.

(** ** Some [option]-specific definition *)

Definition assert P `{HP: Decision P}: option P :=
  match (decide P) with
    | left HP => Some HP
    | right _ => None
  end.

Definition guard {X} P `{Decision P} (x: option X): option X :=
  _ <- assert P; x.

Lemma assert_inv `{Decision} {A} (f: P -> option A) (r: A):
  bind f (assert P) = Some r ->
  exists H, f H = Some r.
Proof.
  unfold assert.
  destruct (decide P); try discriminate.
  unfold bind; simpl.
  eauto.
Qed.

Ltac assert_inv H :=
  match type of H with
    | bind _ (assert _) = _ =>
        apply assert_inv in H;
        let H' := fresh H in
          destruct H as [H' H];
        try assert_inv H
  end.


(** * [option]-related decision procedures *)

Definition isSome {A} (x: option A) :=
  exists a, x = Some a.

Definition isNone {A} (x: option A) :=
  x = None.

Global Instance isSome_dec {A} (x: option A): Decision (exists a, x = Some a) :=
  match x with
    | Some a => left _
    | None => right _
  end.
Proof.
  abstract eauto.
  abstract (intros [a Ha]; discriminate).
Defined.

Global Instance isNone_dec {A} (x: option A): Decision (x = None) :=
  match x with
    | Some _ => right _
    | None => left _
  end.
Proof.
  abstract discriminate.
  abstract reflexivity.
Defined.
