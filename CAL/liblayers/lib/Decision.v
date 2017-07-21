Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.PArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Open Scope Z_scope.


(** * MathClasses-style "Decision" class. *)

Class Decision (P: Prop) := decide: {P} + {~P}.
Arguments decide P {_}.

(** A common special case is that of decidable equality. *)
Class EqDec A := eq_dec (a b : A) :> Decision (a = b).

Definition isTrue P `{Decision P} :=
  if decide P then true else false.

Lemma isTrue_sound P `{Decision P}:
  isTrue P = true -> P.
Proof.
  unfold isTrue.
  destruct (decide P).
  tauto.
  discriminate.
Qed.

Lemma isTrue_complete P `{Decision P}:
  P -> isTrue P = true.
Proof.
  intro HP.
  unfold isTrue.
  destruct (decide P); eauto.
Qed.

Lemma isTrue_correct P `{Decision P}:
  isTrue P = true <-> P.
Proof.
  split.
  * apply isTrue_sound.
  * apply isTrue_complete.
Qed.

Ltac decision :=
  eapply isTrue_sound;
  reflexivity.

Ltac obviously H P :=
  assert (H: P) by decision.

Ltac ensure P :=
  let H := fresh "H" in
  obviously H P; clear H.


(** * Instances *)

Instance decide_Zeq: EqDec Z := Z_eq_dec.
Instance decide_Zle (m n: Z): Decision (m <= n) := {decide := Z_le_dec m n}.
Instance decide_Zlt (m n: Z): Decision (m < n) := {decide := Z_lt_dec m n}.
Instance decide_Zge (m n: Z): Decision (m >= n) := {decide := Z_ge_dec m n}.
Instance decide_Zgt (m n: Z): Decision (m > n) := {decide := Z_gt_dec m n}.
Instance decide_nateq: EqDec nat := eq_nat_dec.
Instance decide_natle m n: Decision (m <= n)%nat := { decide := le_dec m n }.
Instance decide_natlt m n: Decision (m < n)%nat := { decide := lt_dec m n }.
Instance decide_poseq: EqDec positive := Pos.eq_dec.
Instance decide_booleq: EqDec bool := Bool.bool_dec.
Instance decide_Neq: EqDec N := N.eq_dec.

Instance decide_posle (m n: positive): Decision (Pos.le m n).
Proof.
  destruct (Pos.leb m n) eqn:leb.
  - left; apply Pos.leb_le, leb.
  - right; rewrite <- Pos.leb_le, leb; discriminate.
Defined.

Instance and_dec A B: Decision A -> Decision B -> Decision (A /\ B) := {
  decide :=
    match (decide A) with
      | left HA =>
          match (decide B) with
            | left HB => left (conj HA HB)
            | right HnB => right (fun H => HnB (proj2 H))
          end
      | right HnA => right (fun H => HnA (proj1 H))
    end
}.

Instance or_dec A B: Decision A -> Decision B -> Decision (A \/ B) := {
  decide :=
    match (decide A) with
      | left HA => left (or_introl HA)
      | right HnA =>
        match (decide B) with
          | left HB => left (or_intror HB)
          | right HnB => right (fun HAB => match HAB with
                                             | or_introl HA => HnA HA
                                             | or_intror HB => HnB HB
                                           end)
        end
    end
}.

Instance impl_dec P Q `(Pdec: Decision P) `(Qdec: Decision Q): Decision (P->Q) :=
  {
    decide :=
      match Qdec with
        | left HQ => left (fun _ => HQ)
        | right HnQ =>
          match Pdec with
            | left HP => right _
            | right HnP => left _
          end
      end
  }.
Proof.
  * abstract tauto.
  * abstract tauto.
Defined.

Instance not_dec P `(Pdec: Decision P): Decision (~P) :=
  {
    decide :=
      match Pdec with
        | left _ => right _
        | right _ => left _
      end
  }.
Proof.
  * abstract tauto.
  * abstract tauto.
Defined.

Program Instance decide_none {A} (a: option A): Decision (a = None) := {
  decide :=
    match a with
      | Some _ => right _
      | None => left _
    end
}.

Instance decide_option_eq A `{EqDec A}:
  EqDec (option A) :=
  fun x y =>
    match x, y with
      | Some x, Some y =>
        match decide (x = y) with
          | left H => left (f_equal _ H)
          | right H => right _
        end
      | None, None =>
        left eq_refl
      | _, _ =>
        right _
    end.
Proof.
  * abstract (injection; eauto).
  * abstract discriminate.
  * abstract discriminate.
Defined.

Section DECIDE_PROD.
  Context A `{Adec: EqDec A}.
  Context B `{Bdec: EqDec B}.

  Global Instance decide_eq_pair: EqDec (A * B).
  Proof.
    intros [x1 x2] [y1 y2].
    destruct (decide (x1 = y1)).
    destruct (decide (x2 = y2)).
    left; congruence.
    right; intro H; inversion H; now auto.
    right; intro H; inversion H; now auto.
  Defined.
End DECIDE_PROD.

(** * Decision procedures for lists *)

Instance decide_In: forall `{EqDec} a l, Decision (@In A a l) :=
  @In_dec.

Instance decide_Forall {A} (P: A -> Prop):
  (forall a, Decision (P a)) ->
  (forall l, Decision (Forall P l)).
Proof.
  intros HP l.
  induction l.
  * left.
    constructor.
  * destruct (decide (Forall P l)) as [Hl | Hl].
    destruct (decide (P a)) as [Ha | Ha].
    + left.
      constructor;
      assumption.
    + right.
      inversion 1.
      tauto.
    + right.
      inversion 1.
      tauto.
Defined.

Instance decide_list_eq `{EqDec}: EqDec (list A) :=
  list_eq_dec H.

(** * Decision procedures from [compare] *)

(** This takes care of many orders, which are defined as, say,
  [le x y := compare x y <> Gt]. *)

Instance comparison_eq_dec: EqDec comparison.
Proof.
  intros x y.
  red.
  decide equality.
Defined.

(** Decision and equivalence *)

Local Instance decide_rewrite P Q (Heq: P <-> Q) `(Decision P): Decision Q :=
  match decide P with
    | left _ => left _
    | right _ => right _
  end.
Proof.
  abstract tauto.
  abstract tauto.
Defined.

(** Decision and discriminable cases *)

Theorem decide_discr {A}
        (Q1 Q2 P: A -> Prop)
        (discr: forall i, {Q1 i} + {Q2 i})
        (dec_1: Decision (forall i, Q1 i -> P i))
        (dec_2: Decision (forall i, Q2 i -> P i)):
  Decision (forall i, P i).
Proof.
  unfold Decision in *.
  firstorder.
Defined.
