Require Import Coq.Program.Basics.
Require Import LogicalRelations.
Require Import SimulationRelation.
Require Import Structures.
Require Import OptionOrders.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Import BoolRel.

(** * Prerequisites *)

(** ** Typeclass version of [Archi.ptr64] *)

Class ArchiPtr64 b := archi_ptr_64 : Archi.ptr64 = b.

(** When we encounter a term of the form [if Archi.ptr64 then _ else _],
  we need to destruct [Archi.ptr64] to make progress. We also remember
  the value used in each branch as an instance of [ArchiPtr64]. *)

Lemma if_ptr64_destruct {A1 A2} (R: rel A1 A2) (a1 c1: A1) (a2 c2: A2):
  RStep
    ((ArchiPtr64 true  -> R c1 c2) /\
     (ArchiPtr64 false -> R a1 a2))
    (R (if Archi.ptr64 then c1 else a1)
       (if Archi.ptr64 then c2 else a2)).
Proof.
  firstorder.
Qed.

Hint Extern 1
  (RStep _ (_ (if Archi.ptr64 then _ else _) (if Archi.ptr64 then _ else _))) =>
  eapply if_ptr64_destruct : typeclass_instances.

Lemma if_ptr64_destruct_r {A1 A2} (R: rel A1 A2) x1 a2 c2:
  RStep
    ((ArchiPtr64 true  -> R x1 c2) /\
     (ArchiPtr64 false -> R x1 a2))
    (R x1 (if Archi.ptr64 then c2 else a2)).
Proof.
  firstorder.
Qed.

Hint Extern 2
  (RStep _ (_ _ (if Archi.ptr64 then _ else _))) =>
  eapply if_ptr64_destruct_r : typeclass_instances.

(** ** Typed [match_val] *)

Section VALUES_PREREQ.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  (** *** Definition *)

  (** Another issue is that we want to express some typing constraints
    and guarantees as part of our relational properties. To this end
    we introduce the following version of [match_val], which ensures
    that the related values have a given type. *)

  Inductive match_val_of_type_int (p: simrel_world R): rel val val :=
    | match_val_of_type_int_int:
        Monotonic (@Vint) (- ==> match_val_of_type_int p)
    | match_val_of_type_int_ptr b1 ofs1 b2 ofs2:
        ArchiPtr64 false ->
        (** XXX why not use rel_curry? *)
        match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
        match_val_of_type_int p (Vptr b1 ofs1) (Vptr b2 ofs2)
    | match_val_of_type_int_undef:
        Monotonic (@Vundef) (match_val_of_type_int p)
    | match_val_of_type_int_undef_int i:
        simrel_undef_matches_values R ->
        Related Vundef (Vint i) (match_val_of_type_int p)
    | match_val_of_type_int_undef_ptr b ofs:
        simrel_undef_matches_block R p b ->
        ArchiPtr64 false ->
        Related Vundef (Vptr b ofs) (match_val_of_type_int p).

  Inductive match_val_of_type_long (p: simrel_world R): rel val val :=
    | match_val_of_type_long_long:
        Monotonic Vlong (- ==> match_val_of_type_long p)
    | match_val_of_type_long_ptr b1 ofs1 b2 ofs2:
        ArchiPtr64 true ->
        match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
        match_val_of_type_long p (Vptr b1 ofs1) (Vptr b2 ofs2)
    | match_val_of_type_long_undef:
        Monotonic Vundef (match_val_of_type_long p)
    | match_val_of_type_long_undef_lb i:
        simrel_undef_matches_values R ->
        Related Vundef (Vlong i) (match_val_of_type_long p)
    | match_val_of_type_long_undef_ptr b ofs:
        simrel_undef_matches_block R p b ->
        ArchiPtr64 true ->
        Related Vundef (Vptr b ofs) (match_val_of_type_long p).

  Inductive match_val_of_type_float (p: simrel_world R): rel val val :=
    | match_val_of_type_float_float:
        Monotonic Vfloat (- ==> match_val_of_type_float p)
    | match_val_of_type_float_undef:
        Monotonic Vundef (match_val_of_type_float p)
    | match_val_of_type_float_undef_lb f:
        simrel_undef_matches_values R ->
        Related Vundef (Vfloat f) (match_val_of_type_float p).

  Inductive match_val_of_type_single (p: simrel_world R): rel val val :=
    | match_val_of_type_single_single:
        Monotonic Vsingle (- ==> match_val_of_type_single p)
    | match_val_of_type_single_undef:
        Monotonic Vundef (match_val_of_type_single p)
    | match_val_of_type_single_undef_lb f:
        simrel_undef_matches_values R ->
        Related Vundef (Vsingle f) (match_val_of_type_single p).

  Inductive match_val_of_type_any32 (p: simrel_world R): rel val val :=
    | match_val_of_type_any32_int:
        Monotonic (@Vint) (- ==> match_val_of_type_any32 p)
    | match_val_of_type_any32_single:
        Monotonic (@Vsingle) (- ==> match_val_of_type_any32 p)
    | match_val_of_type_any32_ptr b1 ofs1 b2 ofs2:
        ArchiPtr64 false ->
        match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
        match_val_of_type_any32 p (Vptr b1 ofs1) (Vptr b2 ofs2)
    | match_val_of_type_any32_undef:
        Monotonic (@Vundef) (match_val_of_type_any32 p)
    | match_val_of_type_any32_undef_int i:
        simrel_undef_matches_values R ->
        Related Vundef (Vint i) (match_val_of_type_any32 p)
    | match_val_of_type_any32_undef_single f:
        simrel_undef_matches_values R ->
        Related Vundef (Vsingle f) (match_val_of_type_any32 p)
    | match_val_of_type_any32_undef_ptr b ofs:
        simrel_undef_matches_block R p b ->
        ArchiPtr64 false ->
        Related Vundef (Vptr b ofs) (match_val_of_type_any32 p).

  Definition match_val_of_type p ty: rel val val :=
    match ty with
      | Tint => match_val_of_type_int p
      | Tlong => match_val_of_type_long p
      | Tfloat => match_val_of_type_float p
      | Tsingle => match_val_of_type_single p
      | Tany32 => match_val_of_type_any32 p
      | Tany64 => match_val R p
    end.

  (** *** Properties *)

  (** Note that we use [RIntro] directly here instead of [Monotonic].
    This is because we need the [NotEvar] guard to avoid generating
    uninstantiated evars in some circumstances, but [monotonicity]
    always uses an evar as the relation due to the way subrelations
    and [RElim] are handled. *)
  Global Instance Vundef_rel p ty:
    NotEvar ty -> (* would generate uninstantiated evars *)
    RIntro True (match_val_of_type p ty) Vundef Vundef.
  Proof.
    destruct ty; repeat constructor.
  Qed.

  Global Instance Vint_rel p:
    Monotonic (@Vint) (- ==> match_val_of_type p Tint).
  Proof.
    constructor.
  Qed.

  Global Instance Vlong_rel p:
    Monotonic (@Vlong) (- ==> match_val_of_type p Tlong).
  Proof.
    constructor.
  Qed.

  Global Instance Vfloat_rel p:
    Monotonic (@Vfloat) (- ==> match_val_of_type p Tfloat).
  Proof.
    constructor.
  Qed.

  Global Instance Vsingle_rel p:
    Monotonic (@Vsingle) (- ==> match_val_of_type p Tsingle).
  Proof.
    constructor.
  Qed.

  Global Instance Vptr32_rel p:
    ArchiPtr64 false ->
    Monotonic
      (@Vptr)
      (rel_curry (match_ptrbits R p ++> match_val_of_type p Tint)).
  Proof.
    intros Hptr64.
    repeat rstep.
    destruct x, y; simpl.
    constructor; eauto.
  Qed.

  Global Instance Vptr64_rel p:
    ArchiPtr64 true ->
    Monotonic
      (@Vptr)
      (rel_curry (match_ptrbits R p ++> match_val_of_type p Tlong)).
  Proof.
    intros Hptr64.
    repeat rstep.
    destruct x, y; simpl.
    constructor; eauto.
  Qed.

  Global Instance Vundef_Vint_rel p i:
    simrel_undef_matches_values R ->
    Related Vundef (Vint i) (match_val_of_type p Tint).
  Proof.
    constructor; eauto.
  Qed.

  Global Instance Vundef_Vlong_rel p i:
    simrel_undef_matches_values R ->
    Related Vundef (Vlong i) (match_val_of_type p Tlong).
  Proof.
    constructor; eauto.
  Qed.

  Global Instance Vundef_Vfloat_rel p f:
    simrel_undef_matches_values R ->
    Related Vundef (Vfloat f) (match_val_of_type p Tfloat).
  Proof.
    constructor; eauto.
  Qed.

  Global Instance Vundef_Vsingle_rel p f:
    simrel_undef_matches_values R ->
    Related Vundef (Vsingle f) (match_val_of_type p Tsingle).
  Proof.
    constructor; eauto.
  Qed.

  Global Instance Vundef_Vptr32_rel p b ofs:
    simrel_undef_matches_block R p b ->
    ArchiPtr64 false ->
    Related Vundef (Vptr b ofs) (match_val_of_type p Tint).
  Proof.
    constructor; eauto.
  Qed.

  Global Instance Vundef_Vptr64_rel p b ofs:
    simrel_undef_matches_block R p b ->
    ArchiPtr64 true ->
    Related Vundef (Vptr b ofs) (match_val_of_type p Tlong).
  Proof.
    constructor; eauto.
  Qed.

  Global Instance match_val_subtype p t1 t2:
    Convertible (subtype t1 t2) true ->
    Related
      (match_val_of_type p t1)
      (match_val_of_type p t2)
      subrel.
  Proof.
    intros Ht.
    destruct t1, t2; try discriminate; try rauto;
      (intros v1 v2 MVT1; inv MVT1; constructor; auto).
  Qed.

  Global Instance match_val_erase_type p ty:
    Related
      (match_val_of_type p ty)
      (match_val R p)
      subrel.
  Proof.
    intros v1 v2 Hv.
    destruct ty; destruct Hv; constructor; eauto.
  Qed.

  Lemma match_val_has_type p ty v1 v2:
    match_val_of_type p ty v1 v2 ->
    Val.has_type v2 ty.
  Proof.
    intros Hv.
    destruct ty; destruct Hv; simpl; eauto.
  Qed.

  Lemma match_val_of_type_intro p ty v1 v2:
    match_val R p v1 v2 ->
    Val.has_type v2 ty ->
    match_val_of_type p ty v1 v2.
  Proof.
    intros Hv Hv2.
    destruct Hv, ty; try contradiction; try constructor; eauto;
    destruct y; try contradiction; try constructor; eauto.
  Qed.

  Global Instance match_val_of_type_acc:
    Monotonic (match_val_of_type) ((≤) ++> - ==> subrel).
  Proof.
    intros p p' Hp ty x y.
    destruct ty; simpl;
    destruct 1; try constructor;
    solve [ eauto | rauto | revert H; rauto ].
  Qed.

  Global Instance match_val_any64_val p:
    Related (match_val R p) (match_val_of_type p Tany64) subrel.
  Proof.
    simpl. rauto.
  Qed.
  
  Global Opaque match_val_of_type.
End VALUES_PREREQ.

(** ** Miscellaneous *)

(** FIXME: this belongs somewhere else *)

Instance : UpperBound impl True.
  firstorder.
Qed.

(** * Properties of [match_val_of_type_*] wrt. equivalence *)

Section VALUES_PREREQ_EQUIV.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} {R1 R2: simrel D1 D2}.
  Context {f} {EQUIV: SimulationRelationEquivalence R1 R2 f}.

  Lemma match_val_of_type_int_simrel_equiv_fw p:
    subrel (match_val_of_type_int R1 p) (match_val_of_type_int R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1;
    constructor;
    revert H; try revert H0; simrel_equiv_rewrite; auto.
    intros; eapply match_ptrbits_simrel_equiv_fw; auto.
    intros; eapply simrel_equiv_undef_matches_block_fw; eauto.
  Qed.

  Lemma match_val_of_type_int_simrel_equiv_bw p:
    subrel (match_val_of_type_int R2 p) (match_val_of_type_int R1 (simrel_equiv_bw f p)).
  Proof.
    destruct 1; constructor; simrel_equiv_rewrite; auto.
    eapply match_ptrbits_simrel_equiv_bw; eauto.
    eapply simrel_equiv_undef_matches_block_bw; eauto.
  Qed.

  Lemma match_val_of_type_long_simrel_equiv_fw p:
    subrel (match_val_of_type_long R1 p) (match_val_of_type_long R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1;
    constructor; revert H;
    simrel_equiv_rewrite; intros; auto.
    eapply match_ptrbits_simrel_equiv_fw; auto.
    eapply simrel_equiv_undef_matches_block_fw; eauto.
  Qed.

  Lemma match_val_of_type_long_simrel_equiv_bw p:
    subrel (match_val_of_type_long R2 p) (match_val_of_type_long R1 (simrel_equiv_bw f p)).
  Proof.
    destruct 1; constructor; simrel_equiv_rewrite; auto.
    eapply match_ptrbits_simrel_equiv_bw; eauto.
    eapply simrel_equiv_undef_matches_block_bw; eauto.
  Qed.

  Lemma match_val_of_type_float_simrel_equiv_fw p:
    subrel (match_val_of_type_float R1 p) (match_val_of_type_float R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1;
    constructor; revert H;
    simrel_equiv_rewrite; intros; auto.
  Qed.

  Lemma match_val_of_type_float_simrel_equiv_bw p:
    subrel (match_val_of_type_float R2 p) (match_val_of_type_float R1 (simrel_equiv_bw f p)).
  Proof.
    destruct 1; constructor; simrel_equiv_rewrite; auto.
  Qed.

  Lemma match_val_of_type_single_simrel_equiv_fw p:
    subrel (match_val_of_type_single R1 p) (match_val_of_type_single R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1;
    constructor; revert H;
    simrel_equiv_rewrite; intros; auto.
  Qed.

  Lemma match_val_of_type_single_simrel_equiv_bw p:
    subrel (match_val_of_type_single R2 p) (match_val_of_type_single R1 (simrel_equiv_bw f p)).
  Proof.
    destruct 1; constructor; simrel_equiv_rewrite; auto.
  Qed.

  Lemma match_val_of_type_any32_simrel_equiv_fw p:
    subrel (match_val_of_type_any32 R1 p) (match_val_of_type_any32 R2 (simrel_equiv_fw f p)).
  Proof.
    destruct 1;
    constructor; revert H;
    simrel_equiv_rewrite; intros; auto.
    eapply match_ptrbits_simrel_equiv_fw; auto.
    eapply simrel_equiv_undef_matches_block_fw; eauto.
  Qed.

  Lemma match_val_of_type_any32_simrel_equiv_bw p:
    subrel (match_val_of_type_any32 R2 p) (match_val_of_type_any32 R1 (simrel_equiv_bw f p)).
  Proof.
    destruct 1; constructor; simrel_equiv_rewrite; auto.
    eapply match_ptrbits_simrel_equiv_bw; eauto.
    eapply simrel_equiv_undef_matches_block_bw; eauto.
  Qed.

  Lemma match_val_of_type_simrel_equiv_fw p t:
    subrel (match_val_of_type R1 p t) (match_val_of_type R2 (simrel_equiv_fw f p) t).
  Proof.
    Local Transparent match_val_of_type.
    unfold match_val_of_type.
    destruct t.
    apply match_val_of_type_int_simrel_equiv_fw.
    apply match_val_of_type_float_simrel_equiv_fw.
    apply match_val_of_type_long_simrel_equiv_fw.
    apply match_val_of_type_single_simrel_equiv_fw.
    apply match_val_of_type_any32_simrel_equiv_fw.
    apply match_val_simrel_equiv_fw.
  Qed.

  Lemma match_val_of_type_simrel_equiv_bw p t:
    subrel (match_val_of_type R2 p t) (match_val_of_type R1 (simrel_equiv_bw f p) t).
  Proof.
    Local Transparent match_val_of_type.
    unfold match_val_of_type.
    destruct t.
    apply match_val_of_type_int_simrel_equiv_bw.
    apply match_val_of_type_float_simrel_equiv_bw.
    apply match_val_of_type_long_simrel_equiv_bw.
    apply match_val_of_type_single_simrel_equiv_bw.
    apply match_val_of_type_any32_simrel_equiv_bw.
    apply match_val_simrel_equiv_bw.
  Qed.

End VALUES_PREREQ_EQUIV.

Global Opaque match_val_of_type.

Ltac simrel_equiv_rewrite_using f :=
  (SimrelEquivalence.simrel_equiv_rewrite_using f) ||
  erewrite
  ?(match_val_of_type_int_simrel_equiv_fw (f := f)),
  ?(match_val_of_type_long_simrel_equiv_fw (f := f)),
  ?(match_val_of_type_float_simrel_equiv_fw (f := f)),
  ?(match_val_of_type_single_simrel_equiv_fw (f := f)),
  ?(match_val_of_type_simrel_equiv_fw (f := f)),
  ?(match_val_of_type_int_simrel_equiv_bw (f := f)),
  ?(match_val_of_type_long_simrel_equiv_bw (f := f)),
  ?(match_val_of_type_float_simrel_equiv_bw (f := f)),
  ?(match_val_of_type_single_simrel_equiv_bw (f := f)),
  ?(match_val_of_type_simrel_equiv_bw (f := f))
  in * ; try reflexivity.

Ltac simrel_equiv_rewrite :=
  repeat
    match goal with
      | H: SimulationRelationEquivalence _ _ ?f |- _ =>
        progress simrel_equiv_rewrite_using f
    end.

(** * Operations over values *)

Section VALUES_REL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  (** ** Preparations *)

  (** A common pattern is for arithmetic operations to match against
    the value and return [Vundef] in all cases but one: if the value
    is of the correct kind, the operation is performed. Our tactic
    works beautifully to discharge the case where the related values
    of the argument are of the same kind, but when [Vundef] is
    involved as a bottom element, the left-hand side [match] is
    reduced whereas the one on the right-hand side [match] persists
    (because that value could be of any kind). This is not a problem
    when the codomain relation is [match_val], but [match_val_of_type]
    does not have [Vundef] as a bottom element (the right-hand side
    needs to have the prescribed type).

    To address this special case we register the following instance of
    [RIntro], which basically destructs the right-hand side value in
    order to reduce the right-hand side [match] as well. We keep it
    local; if useful elsewhere we may want to register an external
    hint but we want to avoid instantiating an existential variable
    with a [match] term. *)

  Local Instance vundef_vs_match_rintro (R: rel val val) v vu vi vl vf vs vp:
    RIntro
      ((R Vundef vu) /\
       (forall i, v = Vint i -> R Vundef (vi i)) /\
       (forall i, v = Vlong i -> R Vundef (vl i)) /\
       (forall f, v = Vfloat f -> R Vundef (vf f)) /\
       (forall f, v = Vsingle f -> R Vundef (vs f)) /\
       (forall b ofs, v = Vptr b ofs -> R Vundef (vp b ofs)))
      R
      Vundef
      (match v with
         | Vundef => vu
         | Vint i => vi i
         | Vlong i => vl i
         | Vfloat f => vf f
         | Vsingle f => vs f
         | Vptr b ofs => vp b ofs
       end).
  Proof.
    intros (Hu & Hi & Hl & Hf & Hs & Hp).
    destruct v; eauto.
  Qed.

  (** A similar case occurs with [match_option_val_of_type], and its
    own not-quite-bottom element [None]. *)

  Local Instance none_vs_match_rintro (R: relation (option val)) v vu vi vl vf vs vp:
    RIntro
      ((R None vu) /\
       (forall i, v = Vint i -> R None (vi i)) /\
       (forall i, v = Vlong i -> R None (vl i)) /\
       (forall f, v = Vfloat f -> R None (vf f)) /\
       (forall f, v = Vsingle f -> R None (vs f)) /\
       (forall b ofs, v = Vptr b ofs -> R None (vp b ofs)))
      R
      (@None val)
      (match v with
         | Vundef => vu
         | Vint i => vi i
         | Vlong i => vl i
         | Vfloat f => vf f
         | Vsingle f => vs f
         | Vptr b ofs => vp b ofs
       end).
  Proof.
    intros (Hu & Hi & Hl & Hf & Hs & Hp).
    destruct v; eauto.
  Qed.

  (** A similar situation occurs with [if]. *)

  Local Instance vundef_if_sumbool_rintro R P Q (cond: {P}+{Q}) (vc va: val):
    RIntro (R Vundef vc /\ R Vundef va) R Vundef (if cond then vc else va).
  Proof.
    intros [Hc Ha].
    destruct cond; eauto.
  Qed.

  Local Instance none_if_sumbool_rintro R P Q (cond: {P}+{Q}) (vc va: val):
    RIntro (R None vc /\ R None va) R (@None val) (if cond then vc else va).
  Proof.
    intros [Hc Ha].
    destruct cond; eauto.
  Qed.

  Local Instance vundef_if_bool_rintro R (cond: bool) (vc va: val):
    RIntro (R Vundef vc /\ R Vundef va) R Vundef (if cond then vc else va).
  Proof.
    intros [Hc Ha].
    destruct cond; eauto.
  Qed.

  Local Instance none_if_bool_rintro R (cond: bool) (vc va: option val):
    RIntro (R None vc /\ R None va) R (@None val) (if cond then vc else va).
  Proof.
    intros [Hc Ha].
    destruct cond; eauto.
  Qed.

  (** Another situation that can hinder progress is when the goal is
    something like:
<<
    match_option_val_of_type R p Tlong None (option_map Vlong (Float.fooofbar x))
>>
    Whether [Float.fooofbar x] is [None] or [Some], things will work
    out, but we need to destruct it for that to become apparent. The
    following hint does just that. *)

  Local Instance none_option_map_rintro {A} R (f: A -> val) (o: option A):
    RIntro
      (R None None /\ forall a, R None (Some (f a)))
      R (@None val) (option_map f o).
  Proof.
    intros [Hnone Hsome].
    destruct o; eauto.
  Qed.

  (** ** Constants *)

  Global Instance Vzero_match p:
    Monotonic (@Vzero) (match_val_of_type R p Tint).
  Proof.
    unfold Vzero; rauto.
  Qed.

  Global Instance Vone_match p:
    Monotonic (@Vone) (match_val_of_type R p Tint).
  Proof.
    unfold Vone; rauto.
  Qed.

  Global Instance Vmone_match p:
    Monotonic (@Vmone) (match_val_of_type R p Tint).
  Proof.
    unfold Vmone; rauto.
  Qed.

  Global Instance Vtrue_match p:
    Monotonic (@Vtrue) (match_val_of_type R p Tint).
  Proof.
    unfold Vtrue; rauto.
  Qed.

  Global Instance Vfalse_match p:
    Monotonic (@Vfalse) (match_val_of_type R p Tint).
  Proof.
    unfold Vfalse; rauto.
  Qed.

  Global Instance vptrofs_match p:
    Monotonic (@Vptrofs) (- ==> match_val R p).
  Proof.
    unfold Vptrofs.
    rauto.
  Qed.

  Global Instance val_has_type_match p:
    Monotonic (@Val.has_type) (match_val R p --> - ==> impl).
  Proof.
    unfold Val.has_type; rauto.
  Qed.

  Global Instance val_has_type_list_match p:
    Monotonic (@Val.has_type_list) (list_rel (match_val R p) --> - ==> impl).
  Proof.
    induction 1; simpl; solve_monotonic.
  Qed.

  Global Instance val_has_opttype p:
    Monotonic (@Val.has_opttype) (match_val R p --> option_le eq ++> impl).
  Proof.
    unfold Val.has_opttype.
    intros v1 v2 Hv ty1 ty2 Hty.
    repeat rstep.
    intro; subst.
    inversion Hv; destruct y; constructor.
  Qed.

  Global Instance val_bool_of_val p:
    Monotonic (@Val.bool_of_val) (match_val R p ++> set_rel leb).
  Proof.
    solve_set_rel.
  Qed.

  (** ** Arithmetic operations *)

  Global Instance val_neg_match p:
    Monotonic (@Val.neg) (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.neg.
    solve_monotonic.
  Qed.

  Global Instance val_negf_match p:
    Monotonic (@Val.negf) (match_val R p ++> match_val_of_type R p Tfloat).
  Proof.
    unfold Val.negf.
    solve_monotonic.
  Qed.

  Global Instance val_absf_match p:
    Monotonic (@Val.absf) (match_val R p ++> match_val_of_type R p Tfloat).
  Proof.
    unfold Val.absf.
    solve_monotonic.
  Qed.

  (** Unfortunately, the relational property
    [simrel_option_le R (match_val_of_type R p ty) ++> match_val_of_type R p ty]
    does not hold for [Val.maketotal] because [simrel_option_le] only
    takes into account [simrel_undef_matches_values], whereas the
    right-hand side could be a pointer that [R] does not match to
    undef, even though it does match non-pointer values.

    Since [Val.maketotal] is only used in a handful of cases, we
    circumvent the problem by proving the following, admittedly less
    compositional lemmas about these specific cases instead. *)

  Lemma val_maketotal_intoffloat_match p:
    Monotonic
      (fun v => Val.maketotal (Val.intoffloat v))
      (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    intros v1 v2 Hv.
    unfold Val.maketotal, Val.intoffloat.
    destruct Hv; try constructor.
    - destruct (Float.to_int _); simpl; rauto.
    - destruct (Float.to_int _); simpl; rauto.
  Qed.

  Lemma val_maketotal_floatofint_match p:
    Monotonic
      (fun v => Val.maketotal (Val.floatofint v))
      (match_val R p ++> match_val_of_type R p Tfloat).
  Proof.
    intros v1 v2 Hv.
    unfold Val.maketotal, Val.floatofint.
    destruct Hv; rauto.
  Qed.

  Global Instance val_intoffloat_match p:
    Monotonic
      (@Val.intoffloat)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.intoffloat.
    solve_monotonic.
  Qed.

  Global Instance val_intuoffloat_match p:
    Monotonic
      (@Val.intuoffloat)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.intuoffloat.
    solve_monotonic.
  Qed.

  Global Instance val_floatofint_match p:
    Monotonic
      (@Val.floatofint)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tfloat)).
  Proof.
    unfold Val.floatofint.
    solve_monotonic.
  Qed.

  Global Instance val_floatofintu_match p:
    Monotonic
      Val.floatofintu
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tfloat)).
  Proof.
    unfold Val.floatofintu.
    solve_monotonic.
  Qed.

  Global Instance val_negint_match p:
    Monotonic
      (@Val.negint)
      (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.negint.
    solve_monotonic.
  Qed.

  Global Instance val_notint_match p:
    Monotonic (@Val.notint) (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.notint.
    solve_monotonic.
  Qed.

  Global Instance val_of_bool_match p:
    Monotonic (@Val.of_bool) (- ==> match_val_of_type R p Tint).
  Proof.
    unfold Val.of_bool.
    solve_monotonic.
  Qed.

  Global Instance val_boolval_match p:
    Monotonic (@Val.boolval) (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.boolval.
    solve_monotonic.
  Qed.

  Global Instance val_notbool_match p:
    Monotonic (@Val.notbool) (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.notbool.
    solve_monotonic.
  Qed.

  Global Instance val_zero_ext_match p:
    Monotonic
      (@Val.zero_ext)
      (- ==> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.zero_ext.
    solve_monotonic.
  Qed.

  Global Instance val_sign_ext_match p:
    Monotonic
      (@Val.sign_ext)
      (- ==> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.sign_ext.
    solve_monotonic.
  Qed.

  Global Instance val_singleoffloat_match p:
    Monotonic
      (@Val.singleoffloat)
      (match_val R p ++> match_val_of_type R p Tsingle).
  Proof.
    unfold Val.singleoffloat.
    solve_monotonic.
  Qed.

  Global Instance val_add_match p:
    Monotonic
      (@Val.add)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.add.
    destruct 1; destruct 1; constructor; eauto.
  Qed.

  Global Instance val_sub_match p:
    Monotonic
      (@Val.sub)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.sub.
    destruct 1; destruct 1; try constructor; eauto.
  Qed.

  Global Instance val_mul_match p:
    Monotonic
      (@Val.mul)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.mul.
    solve_monotonic.
  Qed.

  Global Instance val_mulhs_match p:
    Monotonic
      (@Val.mulhs)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.mulhs.
    solve_monotonic.
  Qed.

  Global Instance val_mulhu_match p:
    Monotonic
      (@Val.mulhu)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.mulhu.
    solve_monotonic.
  Qed.

  Global Instance val_divs_match p:
    Monotonic
      (@Val.divs)
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.divs.
    solve_monotonic.
  Qed.

  Global Instance val_mods_match p:
    Monotonic
      (@Val.mods)
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.mods.
    solve_monotonic.
  Qed.

  Global Instance val_divu_match p:
    Monotonic
      (@Val.divu)
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.divu.
    solve_monotonic.
  Qed.

  Global Instance val_modu_match p:
    Monotonic
      (@Val.modu)
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.modu.
    solve_monotonic.
  Qed.

  Global Instance val_add_carry p:
    Monotonic
      (@Val.add_carry)
      (match_val R p ++> match_val R p ++> match_val R p ++>
       match_val_of_type R p Tint).
  Proof.
    unfold Val.add_carry.
    solve_monotonic.
  Qed.

  Global Instance val_sub_overflow_match p:
    Monotonic
      (@Val.sub_overflow)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.sub_overflow.
    solve_monotonic.
  Qed.

  Global Instance val_negative_match p:
    Monotonic
      (@Val.negative)
      (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.negative.
    solve_monotonic.
  Qed.

  Global Instance val_and_match p:
    Monotonic
      (@Val.and)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.and.
    solve_monotonic.
  Qed.

  Global Instance val_or_match p:
    Monotonic
      (@Val.or)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.or.
    solve_monotonic.
  Qed.

  Global Instance val_xor_match p:
    Monotonic
      (@Val.xor)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.xor.
    solve_monotonic.
  Qed.

  Global Instance val_shl_match p:
    Monotonic
      (@Val.shl)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.shl.
    solve_monotonic.
  Qed.

  Global Instance val_shr_match p:
    Monotonic
      (@Val.shr)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.shr.
    solve_monotonic.
  Qed.

  Global Instance val_shr_carry_match p:
    Monotonic
      (@Val.shr_carry)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.shr_carry.
    solve_monotonic.
  Qed.

  Global Instance val_shrx_match p:
    Monotonic
      (@Val.shrx)
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.shrx.
    solve_monotonic.
  Qed.

  Global Instance val_shru_match p:
    Monotonic
      (@Val.shru)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.shru.
    solve_monotonic.
  Qed.

  Global Instance val_rolm_match p:
    Monotonic
      (@Val.rolm)
      (match_val R p ++> - ==> - ==> match_val_of_type R p Tint).
  Proof.
    unfold Val.rolm.
    solve_monotonic.
  Qed.

  Global Instance val_ror_match p:
    Monotonic
      (@Val.ror)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.ror.
    solve_monotonic.
  Qed.

  Global Instance val_addf_match p:
    Monotonic
      (@Val.addf)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tfloat).
  Proof.
    unfold Val.addf.
    solve_monotonic.
  Qed.

  Global Instance val_subf_match p:
    Monotonic
      (@Val.subf)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tfloat).
  Proof.
    unfold Val.subf.
    solve_monotonic.
  Qed.

  Global Instance val_mulf_match p:
    Monotonic
      (@Val.mulf)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tfloat).
  Proof.
    unfold Val.mulf.
    solve_monotonic.
  Qed.

  Global Instance val_divf_match p:
    Monotonic
      (@Val.divf)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tfloat).
  Proof.
    unfold Val.divf.
    solve_monotonic.
  Qed.

  Global Instance val_floatofwords_match p:
    Monotonic
      (@Val.floatofwords)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tfloat).
  Proof.
    unfold Val.floatofwords.
    solve_monotonic.
  Qed.

  (** ** Operations on 64-bit integers *)

  Global Instance val_longofwords_match p:
    Monotonic
      (@Val.longofwords)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.longofwords.
    solve_monotonic.
  Qed.

  Global Instance val_loword_match p:
    Monotonic (@Val.loword) (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.loword.
    solve_monotonic.
  Qed.

  Global Instance val_hiword_match p:
    Monotonic (@Val.hiword) (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.hiword.
    solve_monotonic.
  Qed.

  Global Instance val_negl_match p:
    Monotonic (@Val.negl) (match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.negl.
    solve_monotonic.
  Qed.

  Global Instance val_notl_match p:
    Monotonic (@Val.notl) (match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.notl.
    solve_monotonic.
  Qed.

  Global Instance val_longofint_match p:
    Monotonic (@Val.longofint) (match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.longofint.
    solve_monotonic.
  Qed.

  Global Instance val_longofintu_match p:
    Monotonic (@Val.longofintu) (match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.longofintu.
    solve_monotonic.
  Qed.

  Global Instance val_longoffloat_match p:
    Monotonic
      (@Val.longoffloat)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tlong)).
  Proof.
    unfold Val.longoffloat.
    solve_monotonic.
  Qed.

  Global Instance val_longuoffloat_match p:
    Monotonic
      (@Val.longuoffloat)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tlong)).
  Proof.
    unfold Val.longuoffloat.
    solve_monotonic.
  Qed.

  Global Instance val_floatoflong_match p:
    Monotonic
      (@Val.floatoflong)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tfloat)).
  Proof.
    unfold Val.floatoflong.
    solve_monotonic.
  Qed.

  Global Instance val_floatoflongu_match p:
    Monotonic
      (@Val.floatoflongu)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tfloat)).
  Proof.
    unfold Val.floatoflongu.
    solve_monotonic.
  Qed.

  Global Instance val_singleoflong_match p:
    Monotonic
      (@Val.singleoflong)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tsingle)).
  Proof.
    unfold Val.singleoflong.
    solve_monotonic.
  Qed.

  Global Instance val_singleoflongu_match p:
    Monotonic
      (@Val.singleoflongu)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tsingle)).
  Proof.
    unfold Val.singleoflongu.
    solve_monotonic.
  Qed.

  Global Instance val_addl_match p:
    Monotonic
      (@Val.addl)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.addl.
    repeat rstep.
    - eapply match_ptrbits_shift; eauto.
    - eapply match_ptrbits_shift; eauto.
    - subst y0.
      inv H0.
      constructor; typeclasses eauto.
      constructor; typeclasses eauto.
  Qed.

  Global Instance val_subl_match p:
    Monotonic
      Val.subl
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.subl.
    solve_monotonic.
    - rewrite !Ptrofs.sub_add_opp.
      eapply match_ptrbits_shift; eauto.
    - assert (match_block R p b1 b2) by (eapply match_ptrbits_block; eauto).
      assert (match_block R p b0 b3) by (eapply match_ptrbits_block; eauto).
      destruct (eq_block b1 b0); destruct (eq_block b2 b3); subst; try constructor.
      + inversion H3; inversion H4; subst.
        replace delta0 with delta in * by congruence.
        rewrite Ptrofs.sub_shifted.
        constructor.
      + destruct n; eapply match_block_functional; eauto.
      + eapply simrel_undef_matches_block_also_values.
        eapply simrel_undef_matches_block_or_injective; eauto.
  Qed.

  Global Instance val_mull_match p:
    Monotonic
      Val.mull
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.mull.
    solve_monotonic.
  Qed.

  Global Instance val_mull'_match p:
    Monotonic
      Val.mull'
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.mull'.
    solve_monotonic.
  Qed.

  Global Instance val_mullhs_match:
    forall p,
      Monotonic Val.mullhs (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    intros p v1 v2 MV1 v3 v4 MV2.
    inv MV1; inv MV2; simpl; constructor; auto.
  Qed.

  Global Instance val_mullhu_match:
    forall p,
      Monotonic Val.mullhu (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    intros p v1 v2 MV1 v3 v4 MV2.
    inv MV1; inv MV2; simpl; constructor; auto.
  Qed.

  Global Instance val_divls_match p:
    Monotonic
      Val.divls
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tlong)).
  Proof.
    unfold Val.divls.
    solve_monotonic.
  Qed.

  Global Instance val_modls_match p:
    Monotonic
      Val.modls
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tlong)).
  Proof.
    unfold Val.modls.
    solve_monotonic.
  Qed.

  Global Instance val_divlu_match p:
    Monotonic
      Val.divlu
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tlong)).
  Proof.
    unfold Val.divlu.
    solve_monotonic.
  Qed.

  Global Instance val_modlu_match p:
    Monotonic
      Val.modlu
      (match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tlong)).
  Proof.
    unfold Val.modlu.
    solve_monotonic.
  Qed.

  Global Instance val_andl_match p:
    Monotonic
      Val.andl
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.andl.
    solve_monotonic.
  Qed.

  Global Instance val_orl_match p:
    Monotonic
      Val.orl
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.orl.
    solve_monotonic.
  Qed.

  Global Instance val_xorl_match p:
    Monotonic
      Val.xorl
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.xorl.
    solve_monotonic.
  Qed.

  Global Instance val_shll_match p:
    Monotonic
      Val.shll
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.shll.
    solve_monotonic.
  Qed.

  Global Instance val_shrl_match p:
    Monotonic
      Val.shrl
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.shrl.
    solve_monotonic.
  Qed.

  Global Instance val_shrlu_match p:
    Monotonic
      Val.shrlu
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tlong).
  Proof.
    unfold Val.shrlu.
    solve_monotonic.
  Qed.

  (** ** Comparisons *)

  (** *** Prerequisites *)

  (** Comparisons involving pointers are tricky. This is because the
    result may be true, false, or undefined depending on whether the
    pointers being compared are valid, and whether they're in the same
    block. In case we actually end up comparing offsets of related
    pointers, we have to handle the complications introduced by
    modular arithmetic. *)

  (** Block comparisons are mostly straightforward to handle. *)

  Global Instance match_ptrbits_block_rstep p b1 b2 ofs1 ofs2:
    RStep
      (match_ptrbits R p (b1, ofs1) (b2, ofs2))
      (match_block R p b1 b2) | 100.
  Proof.
    red.
    apply match_ptrbits_block.
  Qed.

  Global Instance eq_block_rel p:
    Monotonic
      (@eq_block)
      (forallr b1 b1' : match_block R p,
       forallr b2 b2' : match_block R p,
       sumbool_le).
  Proof.
    intros b1 b2 Hb b1' b2' Hb'.
    destruct (eq_block b1 b1'); repeat rstep.
    destruct (eq_block b2 b2'); repeat rstep.
    elim n.
    subst.
    eapply match_block_functional; eauto.
  Qed.

  (** Offset comparisons are more involved. *)

  Section PTROFS_CMP.
    Lemma ptrofs_eq_Z_eqb x y:
      Ptrofs.eq x y = Z.eqb (Ptrofs.unsigned x) (Ptrofs.unsigned y).
    Proof.
      apply eq_iff_eq_true.
      rewrite Z.eqb_eq.
      unfold Ptrofs.eq.
      clear; destruct (zeq _ _); intuition congruence.
    Qed.

    Lemma Z_eqb_shift x y d:
      Z.eqb (x + d) (y + d) = Z.eqb x y.
    Proof.
      apply eq_iff_eq_true.
      repeat rewrite Z.eqb_eq.
      omega.
    Qed.

    Lemma ptrofs_ltu_Z_ltb x y:
      Ptrofs.ltu x y = Z.ltb (Ptrofs.unsigned x) (Ptrofs.unsigned y).
    Proof.
      apply eq_iff_eq_true.
      rewrite Z.ltb_lt.
      unfold Ptrofs.ltu.
      clear; destruct (zlt _ _); intuition congruence.
    Qed.

    Lemma Z_ltb_shift x y d:
      Z.ltb (x + d) (y + d) = Z.ltb x y.
    Proof.
      apply eq_iff_eq_true.
      repeat rewrite Z.ltb_lt.
      omega.
    Qed.

    Definition Z_cmpb c :=
      match c with
        | Ceq => Z.eqb
        | Cle => fun x y => negb (Z.ltb y x)
        | Cgt => fun x y => Z.ltb y x
        | Cge => fun x y => negb (Z.ltb x y)
        | Cne => fun x y => negb (Z.eqb x y)
        | Clt => Z.ltb
      end.

    Lemma ptrofs_cmpu_Z_cmpb c u v:
      Ptrofs.cmpu c u v = Z_cmpb c (Ptrofs.unsigned u) (Ptrofs.unsigned v).
    Proof.
      destruct c; simpl;
      rewrite ?ptrofs_eq_Z_eqb, ?ptrofs_ltu_Z_ltb;
      reflexivity.
    Qed.

    Lemma Z_cmpb_shift c x y d:
      Z_cmpb c (x + d) (y + d) = Z_cmpb c x y.
    Proof.
      destruct c;
      simpl;
      rewrite ?Z_eqb_shift, ?Z_ltb_shift;
      reflexivity.
    Qed.
  End PTROFS_CMP.

  Global Instance ptrofs_eq_rintro p xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
    RIntro
      (match_ptrbits R p (xb1, xofs1) (xb2, xofs2) /\
       match_ptrbits R p (yb1, yofs1) (yb2, yofs2) /\
       xb1 = yb1)
      eq
      (Ptrofs.eq xofs1 yofs1)
      (Ptrofs.eq xofs2 yofs2).
  Proof.
    intros (Hx & Hy & Hb).
    inversion Hx.
    inversion Hy.
    subst.
    assert (delta0 = delta) by congruence; subst.
    rewrite Ptrofs.translate_eq.
    reflexivity.
  Qed.

  Global Instance ptrofs_ltu_rintro p m1 m2 xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
    RIntro
      (match_mem R p m1 m2 /\
       match_ptrbits R p (xb1, xofs1) (xb2, xofs2) /\
       match_ptrbits R p (yb1, yofs1) (yb2, yofs2) /\
       xb1 = yb1 /\
       Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned xofs1) = true /\
       Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned yofs1) = true)
      eq
      (Ptrofs.ltu xofs1 yofs1)
      (Ptrofs.ltu xofs2 yofs2).
  Proof.
    intros (Hm & Hx & Hy & Hb & Hxv & Hyv).
    inversion Hx.
    inversion Hy.
    subst.
    assert (delta0 = delta) by congruence; subst.
    rewrite !ptrofs_ltu_Z_ltb.
    eapply (simrel_weak_valid_pointer_address_inject_weak p) in H0; [ | eauto].
    destruct H0 as (delta' & Hdelta').
    rewrite !Hdelta' by eauto.
    rewrite Z_ltb_shift.
    reflexivity.
  Qed.

  Global Instance ptrofs_cmpu_rintro p m1 m2 c xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
    RIntro
      (match_mem R p m1 m2 /\
       match_ptrbits R p (xb1, xofs1) (xb2, xofs2) /\
       match_ptrbits R p (yb1, yofs1) (yb2, yofs2) /\
       xb1 = yb1 /\
       Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned xofs1) = true /\
       Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned yofs1) = true)
      eq
      (Ptrofs.cmpu c xofs1 yofs1)
      (Ptrofs.cmpu c xofs2 yofs2).
  Proof.
    intros (Hm & Hx & Hy & Hb & Hxv & Hyv).
    inversion Hx.
    inversion Hy.
    subst.
    assert (delta0 = delta) by congruence; subst.
    eapply (simrel_weak_valid_pointer_address_inject_weak p) in H0; [ | eauto].
    destruct H0 as (delta' & Hdelta').
    rewrite !ptrofs_cmpu_Z_cmpb.
    rewrite !Hdelta' by eauto.
    rewrite Z_cmpb_shift.
    reflexivity.
  Qed.

  (** One last complication is that [Val.cmpu] and [Val.cmplu] can
    formally accept an arbitrary [valid_pointer] predicate, but our
    proof relies on the fact that they are actually passed
    [Mem.valid_pointer] applied to related memories. Thankfully, we
    can express this constraint with the relation
    [(match_mem R p) !! Mem.valid_pointer]. We also use the following
    instance of [RStep] to automatically fold the derived
    [weak_valid_pointer] into the actual [Mem.weak_valid_pointer] that
    we know things about. *)

  Lemma fold_weak_valid_pointer_rstep Rb (m1:mwd D1) (m2:mwd D2) b1 b2 ofs1 ofs2:
    RStep
      (Rb (Mem.weak_valid_pointer m1 b1 ofs1)
          (Mem.weak_valid_pointer m2 b2 ofs2))
      (Rb (Mem.valid_pointer m1 b1 ofs1 || Mem.valid_pointer m1 b1 (ofs1 - 1))
          (Mem.valid_pointer m2 b2 ofs2 || Mem.valid_pointer m2 b2 (ofs2 - 1))).
  Proof.
    intros H.
    exact H.
  Qed.

  Hint Extern 1
    (RStep _ (_ (Mem.valid_pointer _ _ _ || Mem.valid_pointer _ _ _)
                (Mem.valid_pointer _ _ _ || Mem.valid_pointer _ _ _))) =>
    eapply fold_weak_valid_pointer_rstep : typeclass_instances.

  (** *** Comparison operations *)

  Global Instance val_cmp_bool_match p:
    Monotonic
      Val.cmp_bool
      (- ==> match_val R p ++> match_val R p ++> simrel_option_le R eq).
  Proof.
    unfold Val.cmp_bool.
    solve_monotonic.
  Qed.

  Global Instance val_cmpu_bool_match p:
    Monotonic
      Val.cmpu_bool
      ((match_mem R p) !! Mem.valid_pointer ++> - ==>
       match_val R p ++> match_val R p ++> simrel_option_le R eq).
  Proof.
    intros ? ? H.
    destruct H.
    unfold Val.cmpu_bool.

    repeat rstep.
    - destruct b4.
      + rdestruct_remember.
        repeat rstep;
        subst;
        repeat match goal with
          | H: _ && _ = true |- _ =>
            apply andb_true_iff in H;
            destruct H
        end;
        assumption.
      + subst.
        assert (simrel_undef_matches_values R).
        {
          eapply simrel_undef_matches_block_also_values.
          eapply simrel_undef_matches_block_or_injective; eauto; rauto.
        }
        destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                  Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
        * generalize Hvp.
          transport Hvp.
          intros Hvp'.
          setoid_rewrite Hvp.
          assert (ofs2 <> ofs3).
          {
            apply andb_prop in Hvp.
            apply andb_prop in Hvp'.
            destruct Hvp, Hvp'.
            inversion H4.
            inversion H5.
            eapply (simrel_different_pointers_inject p) in n; try eassumption.
            destruct n; try congruence.
          }
          destruct x0; simpl; repeat rstep;
          rewrite Ptrofs.eq_false; eauto.
        * rauto.

    - destruct b4.
      + subst.
        assert (simrel_undef_matches_values R).
        {
          eapply simrel_undef_matches_block_also_values.
          eapply simrel_undef_matches_block_or_injective; eauto; rauto.
        }
        destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                  Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
        * generalize Hvp.
          transport Hvp.
          intros Hvp'.
          setoid_rewrite Hvp.
          assert (ofs2 <> ofs3).
          {
            apply andb_prop in Hvp.
            apply andb_prop in Hvp'.
            destruct Hvp, Hvp'.
            inversion H4.
            inversion H5.
            eapply (simrel_different_pointers_inject p) in H7; try eassumption.
            destruct H7; try congruence.
          }
          destruct x0; simpl; repeat rstep;
          rewrite Ptrofs.eq_false; eauto.
        * rauto.
      + repeat rstep.
  Qed.

  Global Instance val_cmpf_bool_match p:
    Monotonic
      Val.cmpf_bool
      (- ==> match_val R p ++> match_val R p ++> simrel_option_le R eq).
  Proof.
    unfold Val.cmpf_bool.
    solve_monotonic.
  Qed.

  Global Instance val_cmpl_bool_match p:
    Monotonic
      Val.cmpl_bool
      (- ==> match_val R p ++> match_val R p ++> simrel_option_le R eq).
  Proof.
    unfold Val.cmpl_bool.
    solve_monotonic.
  Qed.

  Global Instance val_cmplu_bool_match p:
    Monotonic
      Val.cmplu_bool
      ((match_mem R p) !! Mem.valid_pointer ++> - ==>
       match_val R p ++> match_val R p ++> simrel_option_le R eq).
  Proof.
    intros ? ? H.
    destruct H.
    unfold Val.cmplu_bool.

    repeat rstep.
    - destruct b4.
      + rdestruct_remember.
        repeat rstep;
        subst;
        repeat match goal with
          | H: _ && _ = true |- _ =>
            apply andb_true_iff in H;
            destruct H
        end;
        assumption.
      + subst.
        assert (simrel_undef_matches_values R).
        {
          eapply simrel_undef_matches_block_also_values.
          eapply simrel_undef_matches_block_or_injective; eauto; rauto.
        }
        destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                  Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
        * generalize Hvp.
          transport Hvp.
          intros Hvp'.
          setoid_rewrite Hvp.
          assert (ofs2 <> ofs3).
          {
            apply andb_prop in Hvp.
            apply andb_prop in Hvp'.
            destruct Hvp, Hvp'.
            inversion H4.
            inversion H5.
            eapply (simrel_different_pointers_inject p) in n; try eassumption.
            destruct n; try congruence.
          }
          destruct x0; simpl; repeat rstep;
          rewrite Ptrofs.eq_false; eauto.
        * rauto.

    - destruct b4.
      + subst.
        assert (simrel_undef_matches_values R).
        {
          eapply simrel_undef_matches_block_also_values.
          eapply simrel_undef_matches_block_or_injective; eauto; rauto.
        }
        destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                  Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
        * generalize Hvp.
          transport Hvp.
          intros Hvp'.
          setoid_rewrite Hvp.
          assert (ofs2 <> ofs3).
          {
            apply andb_prop in Hvp.
            apply andb_prop in Hvp'.
            destruct Hvp, Hvp'.
            inversion H4.
            inversion H5.
            eapply (simrel_different_pointers_inject p) in H6; try eassumption.
            destruct H6; try congruence.
          }
          destruct x0; simpl; repeat rstep;
          rewrite Ptrofs.eq_false; eauto.
        * rauto.
      + repeat rstep.
  Qed.

  Global Instance val_of_optbool_match p:
    Monotonic
      Val.of_optbool
      (simrel_option_le R eq ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.of_optbool.
    solve_monotonic.
    destruct y0 as [[|]|]; solve_monotonic.
  Qed.

  Global Instance val_cmp_match p:
    Monotonic
      Val.cmp
      (- ==> match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.cmp.
    solve_monotonic.
  Qed.

  Global Instance val_cmpu_match p:
    Monotonic
      Val.cmpu
      ((match_mem R p) !! Mem.valid_pointer ++>
       - ==> match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.cmpu.
    solve_monotonic.
  Qed.

  Global Instance val_cmpf_match p:
    Monotonic
      Val.cmpf
      (- ==> match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    unfold Val.cmpf.
    solve_monotonic.
  Qed.

  Global Instance val_cmpl_match p:
    Monotonic
      Val.cmpl
      (- ==> match_val R p ++> match_val R p ++>
       simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.cmpl.
    solve_monotonic.
  Qed.

  Global Instance val_cmplu_match p:
    Monotonic
      Val.cmplu
      ((match_mem R p) !! Mem.valid_pointer ++> - ==> match_val R p ++>
       match_val R p ++> simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.cmplu.
    solve_monotonic.
  Qed.

  Global Instance val_maskzero_bool_match p:
    Monotonic
      Val.maskzero_bool
      (match_val R p ++> - ==> simrel_option_le R eq).
  Proof.
    unfold Val.maskzero_bool.
    solve_monotonic.
  Qed.

  Global Instance val_offset_ptr_match p:
    Monotonic
      Val.offset_ptr
      (match_val R p ++> - ==> match_val R p).
  Proof.
    unfold Val.offset_ptr.
    solve_monotonic.
    apply match_ptrbits_shift; eauto.
  Qed.

  Global Instance val_load_result_match p:
    Monotonic
      Val.load_result
      (forall_pointwise_rel
         (fun chunk =>
            match_val R p ++>
            match_val_of_type R p (type_of_chunk chunk))).
  Proof.
    unfold Val.load_result.
    solve_monotonic.
  Qed.
End VALUES_REL.
