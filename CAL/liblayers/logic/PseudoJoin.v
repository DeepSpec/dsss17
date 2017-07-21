Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import liblayers.lib.Decision.
Require Export liblayers.logic.Structures.
Require Export liblayers.logic.LayerData.


(** * Pseudo-joins and some properties *)

Class PseudoJoin A `{Ale: Le A} `{Aoplus: Oplus A} (lb: A): Prop :=
  {
    oplus_preorder :>
      PreOrder (≤);
    oplus_lower_bound :>
      LowerBound (≤) lb;
    oplus_monotonic :>
      Proper ((≤) ==> (≤) ==> (≤)) (⊕);
    oplus_id_left_le :>
      LeftIdentity (≤) (⊕) lb;
    oplus_assoc_le:
      Associative (≤) (⊕);
    oplus_comm_le:
      Commutative (≤) (⊕);
    oplus_le_left :>
      LeftUpperBound (≤) (⊕)
  }.

Global Instance oplus_params:
  Params (@oplus) 2.

(** By default, we want associativity to be used in terms of [≡],
  because it can be used for rewriting regardless of variance.
  This is why [oplus_assoc_le] above is not declared as an instance.
  Note that the [≤] version (as well as [flip (≤)]) can be recovered
  by following the [subrelation] instances. *)
Section EQUIV_INSTANCES.
  Local Existing Instance oplus_assoc_le.
  Local Existing Instance oplus_comm_le.
  Local Existing Instance le_equiv_assoc.
  Local Existing Instance le_equiv_comm.

  Global Instance oplus_assoc_equiv `{PseudoJoin}:
    Associative (≡) (⊕) := _.
  Global Instance oplus_assoc_comm `{PseudoJoin}:
    Commutative (≡) (⊕) := _.
End EQUIV_INSTANCES.


(** Sometimes we need those in terms of [eq]. *)

Global Instance oplus_id_left `{PseudoJoin} `{HA: !Antisymmetric A eq (≤)}:
  LeftIdentity eq (⊕) lb.
Proof.
  intros x.
  apply antisymmetry.
  apply id_left.
  apply right_upper_bound.
Qed.

Global Instance oplus_comm `{PseudoJoin} `{HA: !Antisymmetric A eq (≤)}:
  Commutative eq (⊕).
Proof.
  intros x y.
  apply antisymmetry; apply commutativity.
Qed.

(** Combined, specialized versions of associativity, used to
  accelerate tactics. *)

Lemma oplus_assoc_equiv2 `{PseudoJoin} x y y2 z:
  ((x ⊕ y) ⊕ y2) ⊕ z ≡ x ⊕ (y ⊕ (y2 ⊕ z)).
Proof.
  rewrite associativity.
  rewrite associativity.
  reflexivity.
Qed.

Lemma oplus_assoc_equiv3 `{PseudoJoin} x y y2 y3 z:
  (((x ⊕ y) ⊕ y2) ⊕ y3) ⊕ z ≡ x ⊕ (y ⊕ (y2 ⊕ (y3 ⊕ z))).
Proof.
  rewrite oplus_assoc_equiv2.
  rewrite associativity.
  reflexivity.
Qed.

(*
          Lemma oplus_assoc_equiv4 `{PseudoJoin} x y y2 y3 y4 z:
            ((((x ⊕ y) ⊕ y2) ⊕ y3) ⊕ y4) ⊕ z ≡ x ⊕ (y ⊕ (y2 ⊕ (y3 ⊕ (y4 ⊕ z)))).
          Proof.
            rewrite oplus_assoc_equiv3.
            rewrite associativity.
            reflexivity.
          Qed.
 *)

Ltac oplus_assoc_simpl_term T:=
  lazymatch T with
(*| ((((?x ⊕ ?y) ⊕ ?y2) ⊕ ?y3) ⊕ ?y4) ⊕ ?z => rewrite (oplus_assoc_equiv4 x y y2 y3 y4 z)*)
| (((?x ⊕ ?y) ⊕ ?y2) ⊕ ?y3) ⊕ ?z => rewrite (oplus_assoc_equiv3 x y y2 y3 z)
| ((?x ⊕ ?y) ⊕ ?y2) ⊕ ?z => rewrite (oplus_assoc_equiv2 x y y2 z)
| (?x ⊕ ?y) ⊕ ?z => rewrite (oplus_assoc_equiv x y z)
end.

Lemma oplus_assoc_comm_equiv `{PseudoJoin} x y z:
  (x ⊕ y) ⊕ z ≡ y ⊕ (x ⊕ z).
Proof.
  rewrite (commutativity x y).
  rewrite associativity.
  reflexivity.
Qed.


(** * Data-indexed version *)

Class SimPseudoJoin V E T
    `{VErg: CategoryOps V E}
    `{Tsim: Sim V E T}
    `{Toplus: forall v, Oplus (T v)}
    (lb: forall v, T v): Prop :=
  {
    oplus_sim_quiv_sim :>
      CategorySim V E T;
    oplus_sim_lower_bound v1 v2 e x :>
      Convertible x (lb v1) ->
      @LowerBound (T v1) (T v2) (simRR v1 v2 e) x;
    oplus_sim_monotonic :>
      Monotonic
        (fun v => (@oplus (T v) _))
        (forallr R, sim R ++> sim R ++> sim R);
    oplus_sim_id_left_le v x :>
      Convertible x (lb v) ->
      LeftIdentity (sim id) (⊕) x;
    oplus_sim_assoc_le v:
      @Associative (T v) (sim id) (⊕);
    oplus_sim_comm_le v:
      @Commutative (T v) (sim id) (⊕);
    oplus_sim_le_left v :>
      @LeftUpperBound (T v) (sim id) (⊕)
  }.

Local Existing Instance cat_sim_cat.

(** XXX: Because of its form, [oplus_sim_monotonic] cannot be resolved
  by the [monotonicity] tactic or setoid rewriting. For the [id] case,
  we can work around this with an explicitely specialized instance. *)
Global Instance oplus_le_monotonic `{SimPseudoJoin} v:
  @Proper (T v -> T v -> T v) (sim id ++> sim id ++> sim id) (⊕).
Proof.
  apply oplus_sim_monotonic.
Qed.

Section SIM_EQUIV_INSTANCES.
  Local Existing Instance oplus_sim_assoc_le.
  Local Existing Instance oplus_sim_comm_le.
  Local Existing Instance le_equiv_assoc.
  Local Existing Instance le_equiv_comm.

  Global Instance oplus_sim_assoc_equiv `{SimPseudoJoin} D:
    @Associative (T D) (≡) (⊕) := _.
  Global Instance oplus_sim_comm_equiv `{SimPseudoJoin} D:
    @Commutative (T D) (≡) (⊕) := _.
End SIM_EQUIV_INSTANCES.

Global Instance oplus_sim_id_left `{SimPseudoJoin} D:
  Antisymmetric (T D) eq (≤) ->
  @LeftIdentity (T D) eq (⊕) (lb D).
Proof.
  intros Hantisym y.
  apply antisymmetry.
  apply id_left.
  apply right_upper_bound.
Qed.

Global Instance oplus_sim_comm `{SimPseudoJoin} D:
  Antisymmetric (T D) eq (≤) ->
  @Commutative (T D) eq (⊕).
Proof.
  intros Hantisym x y.
  apply antisymmetry; apply commutativity.
Qed.

(** ** Deriving the [PseudoJoin]s on [(T D)] *)

Global Instance sim_pseudojoin `(SimPseudoJoin):
  forall D, PseudoJoin (T D) (lb D).
Proof.
  intros D; split; typeclasses eauto.
Qed.

(** ** A more complete join *)

Section SIMJOIN.
  Context {V E T} `{HVET: CategorySim V E T}.
  Context `{Top: forall v, Oplus (T v)}.

  Class SimLUB v (x y z: T v) :=
    {
      hlub_ub_l: sim id x z;
      hlub_ub_r: sim id y z;
      hlub_intro v' (e: E v v') t: sim e x t -> sim e y t -> sim e z t
    }.

  Class SimJoin :=
    is_join v x y :> SimLUB v x y (x ⊕ y).

  Context `{Hop: !SimJoin}.

  Local Instance simjoin_sim v1 v2 (e: E v1 v2):
    Monotonic (⊕) (sim e ++> sim e ++> sim e).
  Proof.
    repeat rstep.
    apply hlub_intro.
    + htransitivity y; eauto.
      apply hlub_ub_l.
    + htransitivity y0; eauto.
      eapply hlub_ub_r.
  Qed.

  Local Instance simjoin_pjoin (bot: forall v, T v):
    (forall v1 v2 e, LowerBound (simRR v1 v2 e) (bot v1)) ->
    SimPseudoJoin V E T bot.
  Proof.
    split.
    - assumption.
    - intros v1 v2 e x Hx.
      rewrite Hx.
      eauto.
    - rauto.
    - intros v x Hx.
      rewrite Hx; clear x Hx.
      intros x.
      eapply hlub_intro.
      + eapply lower_bound.
      + reflexivity.
    - intros v x y z.
      eapply hlub_intro.
      + apply hlub_intro.
        * apply hlub_ub_l.
        * transitivity (y ⊕ z).
          apply hlub_ub_l.
          apply hlub_ub_r.
      + transitivity (y ⊕ z).
        * apply hlub_ub_r.
        * apply hlub_ub_r.
    - intros v x y.
      apply hlub_intro.
      + eapply hlub_ub_r.
      + eapply hlub_ub_l.
    - intros v x y.
      eapply hlub_ub_l.
  Qed.
End SIMJOIN.

Arguments SimJoin V E T {_ _ _}.


(** * Normalization procedure *)

(*
(** Merge sort *)

Ltac lmerge tac l1 l2 :=
  lazymatch l1 with
    | nil => tac l2
    | ?i ↦ ?x :: ?xs =>
      lazymatch l2 with
        | nil => tac l1
        | ?j ↦ ?y :: ?ys =>
          (ensure (Pos.le i j);
           let cont t := tac (i ↦ x :: t) in
           lmerge cont xs (j ↦ y :: ys)) ||
          (let cont t := tac (j ↦ y :: t) in
           lmerge cont (i ↦ x :: xs) ys)
      end
  end.

Ltac lsort tac t :=
  lazymatch t with
    | ?t1 ⊕ ?t2 =>
      let cont1 t1' :=
        let cont2 t2' :=
          lmerge tac t1' t2' in
        lsort cont2 t2 in
      lsort cont1 t1
    | ?t0 =>
      tac (t0::nil)
  end.

Ltac lfold tac l :=
  lazymatch l with
    | ?x::nil => tac x
    | ?x::?xs => let cont t := tac (x ⊕ t) in lfold cont xs
    | nil => tac ∅
  end.

Ltac lnorm tac t :=
  let cont l := lfold tac l in
  lsort cont t.

Ltac oplus_normalize_in_goal M :=
  let cont M' := (
    let H := fresh "H" in
    cut (M ≡ M');
    [intro H; try rewrite H at 1; clear H|] ||
    fail 10) in
  lnorm cont M.

Ltac peelright i x tac oplus_monotonic oplus_sim_monotonic
                       left_upper_bound right_upper_bound :=
  match goal with
    | |- ?R _ (?j ↦ ?y ⊕ ?ys) =>
      ensure (i = j);
      (apply oplus_monotonic || apply oplus_sim_monotonic); [|
        tac oplus_monotonic oplus_sim_monotonic left_upper_bound right_upper_bound
      ]
    | |- ?R _ (?j ↦ ?y) =>
      idtac
    | |- ?R _ (?a ⊕ ?b) =>
      rewrite <- (right_upper_bound a b);
      tac oplus_monotonic oplus_sim_monotonic left_upper_bound right_upper_bound
  end.

Ltac peelone i x left_upper_bound right_upper_bound :=
  match goal with
    | |- ?R _ (?j ↦ ?y ⊕ ?ys) =>
      ensure (i = j); apply left_upper_bound
    | |- ?R _ (?j ↦ ?y) =>
      idtac
    | |- ?R _ (?a ⊕ ?b) =>
      rewrite <- (right_upper_bound a b);
      peelone i x left_upper_bound right_upper_bound
  end.

Ltac peelsim oplus_monotonic oplus_sim_monotonic
             left_upper_bound right_upper_bound :=
  lazymatch goal with
    | |- ?R (?i ↦ _) (?i ↦ _) =>
      idtac
    | |- ?R (?i ↦ ?x ⊕ ?xs) _ =>
      peelright i x peelsim oplus_monotonic oplus_sim_monotonic
                            left_upper_bound right_upper_bound
    | |- ?R (?i ↦ ?x) _ =>
      peelone i x left_upper_bound right_upper_bound
    | |- _ =>
      idtac
  end.

Ltac sim_split oplus_monotonic oplus_sim_monotonic
               left_upper_bound right_upper_bound :=
  lazymatch goal with
    | |- ?R ?X ?Y =>
      lazymatch type of R with
        | ?TX -> ?TY -> Prop =>
          oplus_normalize_in_goal (X : TX); [
          oplus_normalize_in_goal (Y : TY); [
          peelsim oplus_monotonic oplus_sim_monotonic
                  left_upper_bound right_upper_bound |] |]
        | rel ?TX ?TY =>
          oplus_normalize_in_goal (X : TX); [
          oplus_normalize_in_goal (Y : TY); [
          peelsim oplus_monotonic oplus_sim_monotonic
                  left_upper_bound right_upper_bound |] |]
        | relation ?T =>
          oplus_normalize_in_goal (Y : T); [
          oplus_normalize_in_goal (X : T); [
          peelsim oplus_monotonic oplus_sim_monotonic
                  left_upper_bound right_upper_bound |] |]
      end
  end.

Section TEST.
  Context `{SimPseudoJoin}.
  Context `{forall D, Mapsto positive positive (T D)}.
  Local Open Scope positive.

  Goal forall D1 D2 R, simRR D1 D2 R (1 ↦ 42 ⊕ 20 ↦ 3 ⊕ 2 ↦ 1) (30 ↦ 7 ⊕ 20 ↦ 4 ⊕ 2 ↦ 42 ⊕ 1 ↦ 18).
    intros.
    sim_split (oplus_monotonic (A := T D1)) oplus_sim_monotonic
              left_upper_bound right_upper_bound.
  Abort.
End TEST.
*)


(** * Booleans have a pseudo-join structure *)

Global Instance bool_oplus : Oplus bool := { oplus := orb }.

Global Instance bool_pjoin : PseudoJoin bool false.
Proof.
  split; typeclasses eauto.
Qed.


(** * Product of pseudo-join structures *)

Section PSEUDOJOIN_PROD.
  Context {A Ale Aoplus Alb} `{HA: @PseudoJoin A Ale Aoplus Alb}.
  Context {B Ble Boplus Blb} `{HB: @PseudoJoin B Ble Boplus Blb}.

  Local Instance prod_le_op : Le (A * B) :=
    { le := (≤) * (≤) }.

  Local Instance prod_oplus: Oplus (A * B)%type :=
    {
      oplus x y :=
        match x, y with
          | (xa, xb), (ya, yb) => (xa ⊕ ya, xb ⊕ yb)
        end
    }.

  Local Instance prod_pjoin : PseudoJoin (A * B)%type (Alb, Blb).
  Proof.
    split.
    * simpl.
      typeclasses eauto.
    * intros [a b].
      constructor;
      apply lower_bound.
    * intros [xa1 xb1] [xa2 xb2] [Hxa Hxb] [ya1 yb1] [ya2 yb2] [Hya Hyb].
      simpl in *.
      solve_monotonic.
    * intros [a b].
      constructor; simpl;
        apply id_left.
    * intros [xa xb] [ya yb] [za zb].
      constructor; simpl;
        apply associativity.
    * intros [xa xb] [ya yb].
      unfold oplus;
        simpl.
      split; simpl; apply commutativity.
    * intros [xa xb] [ya yb].
      constructor; simpl;
        apply left_upper_bound.
  Qed.
End PSEUDOJOIN_PROD.


(** * Adjoining an extra element *)

Definition extension A := (A * bool)%type.

Section PSEUDOJOIN_EXTENSION.
  Context `{PseudoJoin}.

  Definition ext_le: relation (extension A) :=
    (≤) * leb.

  Definition ext_inj (a: A): extension A :=
    (a, false).

  Definition ext_elem: extension A :=
    (lb, true).

  Definition ext_map {B} (f: A -> B) (x: extension A): extension B :=
    match x with (a, b) => (f a, b) end.

  Local Instance ext_le_op : Le (extension A) := prod_le_op.
  Local Instance ext_oplus : Oplus (extension A) := prod_oplus.
  Local Instance ext_pjoin : PseudoJoin (extension A) (ext_inj lb) := prod_pjoin.
End PSEUDOJOIN_EXTENSION.
