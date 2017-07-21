Require Import liblayers.lib.Decision.
Require Export liblayers.logic.LayerData.
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Primitives.
Require Export liblayers.compcertx.ErrorMonad.
Require Import liblayers.logic.GlobalVars.

Section WITH_LAYER_DATA.
Context {layerdata simrel} `{HVE: Category layerdata simrel}.


(** * Layers *)

(** The semantic counterpart of modules are layers, which are indexed
  by abstract data and simulation relations. As for modules, there is
  a generic implementation using [positive] identifiers in the file
  [PTreeLayers]. *)

Class LayerOps ident primsem V (layer: layerdata -> Type)
    {gv_ops: GlobalVarsOps V}
    `{primsem_ops: PrimitiveOps layerdata primsem} :=
  {
    layer_empty :> forall D, Emptyset (layer D);
    layer_oplus :> forall D, Oplus (layer D);
    layer_mapsto_primitive :> forall D, Mapsto ident (primsem D) (layer D);
    layer_mapsto_globalvar :> forall D, Mapsto ident V (layer D);

    get_layer_primitive {D} (i: ident): layer D -> res (option (primsem D));
    get_layer_globalvar {D} (i: ident): layer D -> res (option V);
    layers_disjoint {D1} {D2} : layer D1 -> layer D2 -> Prop;
    layer_wf {D}: layer D -> Prop;

    layer_decide_primitive D (P: res (option (primsem D)) -> Prop) :>
      (forall σ, Decision (P σ)) ->
      (forall L, Decision (forall i, P (get_layer_primitive i L)));
    layer_decide_primitive_name D (P: ident -> Prop) :>
      (forall i, Decision (P i)) ->
      (forall L, Decision (forall i, get_layer_primitive (D:=D) i L <> OK None -> P i));
    layer_decide_globalvar D (P: res (option V) -> Prop) :>
      (forall τ, Decision (P τ)) ->
      (forall L, Decision (forall i, P (get_layer_globalvar (D:=D) i L)));
    layer_decide_globalvar_name D (P: ident -> Prop) :>
      (forall i, Decision (P i)) ->
      (forall L, Decision (forall i, get_layer_globalvar (D:=D) i L <> OK None -> P i));
    layers_disjoint_dec {D1 D2} (L1: layer D1) (L2: layer D2) :>
      Decision (layers_disjoint L1 L2)
  }.


(** Properties of layers *)

Class Layers ident primsem V layer
    `{lops: LayerOps ident primsem V layer}
    `{psim_op: Sim layerdata simrel primsem}
    `{lsim_op: Sim layerdata simrel layer} :=
  {
    layer_csim :>
      CategorySim layerdata simrel layer;
    layer_isjoin :>
      SimJoin layerdata simrel layer;
    layer_lower_bound D1 D2 R :>
      LowerBound (A := layer D1) (simRR D1 D2 R) ∅;

    layer_sim_intro D1 D2 (R: simrel D1 D2) i σ1 σ2 :
      sim R σ1 σ2 ->
      sim R (i ↦ σ1) (i ↦ σ2);

    get_layer_primitive_empty {D} i:
      get_layer_primitive (D:=D) i ∅ = OK None;
    get_layer_primitive_mapsto {D} i σ:
      get_layer_primitive (D:=D) i (i ↦ σ) = OK (Some σ);
    get_layer_primitive_mapsto_other_primitive {D} i j (σ: primsem D):
      i <> j -> get_layer_primitive (D:=D) i (j ↦ σ) = OK None;
    get_layer_primitive_mapsto_globalvar {D} i j (τ: V):
      get_layer_primitive (D:=D) i (j ↦ τ) = OK None;
    get_layer_primitive_oplus {D} i (L1 L2: layer D):
      get_layer_primitive i (L1 ⊕ L2) =
      get_layer_primitive i L1 ⊕ get_layer_primitive i L2;
    get_layer_primitive_sim_monotonic :>
      Monotonic
        (@get_layer_primitive _ _ _ _ _ _ _)
        (forallr R, - ==> sim R ++> res_le (option_le (sim R)));

    get_layer_globalvar_empty {D} i:
      get_layer_globalvar (D:=D) i ∅ = OK None;
    get_layer_globalvar_mapsto {D} i τ:
      get_layer_globalvar (D:=D) i (i ↦ τ) = OK (Some τ);
    get_layer_globalvar_mapsto_other_globalvar {D} i j (τ: V):
      i <> j -> get_layer_globalvar (D:=D) i (j ↦ τ) = OK None;
    get_layer_globalvar_mapsto_primitive {D} i j (σ: primsem D):
      get_layer_globalvar (D:=D) i (j ↦ σ) = OK None;
    get_layer_globalvar_oplus {D} i (L1 L2: layer D):
      get_layer_globalvar (D:=D) i (L1 ⊕ L2) =
      get_layer_globalvar i L1 ⊕ get_layer_globalvar i L2;
    get_layer_globalvar_sim_monotonic :>
      Monotonic
        (@get_layer_globalvar _ _ _ _ _ _ _)
        (forallr R, - ==> sim R ++> res_le (option_le eq));

    layers_disjoint_empty {D1 D2} L:
      layers_disjoint (D1:=D1) (D2:=D2) ∅ L;
    layers_disjoint_sym {D1 D2} L1 L2:
      layers_disjoint (D1:=D1) (D2:=D2) L1 L2 ->
      layers_disjoint L2 L1;
    layers_disjoint_oplus {D1 D2} L1 L21 L22:
      layers_disjoint (D1:=D1) (D2:=D2) L1 L21 ->
      layers_disjoint (D1:=D1) (D2:=D2) L1 L22 ->
      layers_disjoint L1 (L21 ⊕ L22);
    layers_disjoint_mapsto_primitive_primitive
      {D1 D2} i1 i2 (σ1: primsem D1) (σ2: primsem D2):
      i1 <> i2 ->
      layers_disjoint (i1 ↦ σ1) (i2 ↦ σ2);
    layers_disjoint_mapsto_primitive_globalvar
      {D1 D2} i1 i2 (σ1: primsem D1) (κ2: V):
      i1 <> i2 ->
      layers_disjoint (D2:=D2) (i1 ↦ σ1) (i2 ↦ κ2);
    layers_disjoint_mapsto_globalvar_globalvar
      {D1 D2} i1 i2 (κ1 κ2: V):
      i1 <> i2 ->
      layers_disjoint (D1:=D1) (D2:=D2) (i1 ↦ κ1) (i2 ↦ κ2);

    layer_sim_cancel_disjoint {D D'} (R: simrel D D') L L1 L2:
      layers_disjoint L L2 ->
      sim R L (L1 ⊕ L2) ->
      sim R L L1;
    layers_disjoint_primitive i D (L1 L2: layer D):
      layers_disjoint L1 L2 ->
      get_layer_primitive i (L1 ⊕ L2) = get_layer_primitive i L1 \/
      get_layer_primitive i (L1 ⊕ L2) = get_layer_primitive i L2;
    layers_disjoint_globalvar i D (L1 L2: layer D):
      layers_disjoint L1 L2 ->
      get_layer_globalvar i (L1 ⊕ L2) = get_layer_globalvar i L1 \/
      get_layer_globalvar i (L1 ⊕ L2) = get_layer_globalvar i L2;

    oplus_wf D (L1 L2: layer D):
      layer_wf L1 ->
      layer_wf L2 ->
      layer_wf (L1 ⊕ L2)
  }.

  Global Instance layer_pjoin `(Layers):
    SimPseudoJoin layerdata simrel layer (fun _ => ∅).
  Proof.
    eapply simjoin_pjoin; typeclasses eauto.
  Qed.

  (** Specialized version of [layer_sim_intro]. *)
  Lemma layer_le_intro `{Layers} {D} i (σ1 σ2: primsem D):
    σ1 ≤ σ2 ->
    i ↦ σ1 ≤ i ↦ σ2.
  Proof.
    apply layer_sim_intro.
  Qed.

(** NOW WRONG -- though can be enforced through layer_ok
  <<<
    get_layer_primitive_globalvar_disjoint {D} (L: layer D) (i: ident):
      isOK (get_layer_primitive i L) ->
      isOK (get_layer_globalvar i L) ->
      isOKNone (get_layer_primitive i L) \/ isOKNone (get_layer_globalvar i L)
  >>> *)
End WITH_LAYER_DATA.

Global Instance get_layer_primitive_sim_monotonic_params:
  Params (@get_layer_primitive) 3.

Global Instance get_layer_globalvar_sim_monotonic_params:
  Params (@get_layer_globalvar) 3.

(** Rewrite hints for [get_layer_primitive] and [get_layer_globalvar] *)

Ltac get_layer_normalize :=
  repeat rewrite
    ?get_layer_primitive_empty,
    ?get_layer_primitive_mapsto,
    ?get_layer_primitive_mapsto_other_primitive,
    ?get_layer_primitive_mapsto_globalvar,
    ?get_layer_primitive_oplus,
    ?get_layer_globalvar_empty,
    ?get_layer_globalvar_mapsto,
    ?get_layer_globalvar_mapsto_other_globalvar,
    ?get_layer_globalvar_mapsto_primitive,
    ?get_layer_globalvar_oplus by congruence.

Ltac get_layer_normalize_in H :=
  repeat rewrite
    ?get_layer_primitive_empty,
    ?get_layer_primitive_mapsto,
    ?get_layer_primitive_mapsto_other_primitive,
    ?get_layer_primitive_mapsto_globalvar,
    ?get_layer_primitive_oplus,
    ?get_layer_globalvar_empty,
    ?get_layer_globalvar_mapsto,
    ?get_layer_globalvar_mapsto_other_globalvar,
    ?get_layer_globalvar_mapsto_primitive,
    ?get_layer_globalvar_oplus in H by congruence.


(** * Asserting a property for all primitives *)

Section FORALL_PRIM.
  Context `{Hlayer: Layers}.
  Context `{Hident: EqDec ident}.

  Class ForallPrimitive D (P: primsem D -> Prop) (L: layer D) :=
    {
      forall_primitive_at i σ:
        get_layer_primitive i L = OK (Some σ) ->
        P σ
    }.

  Global Instance forallprim_empty D P:
    ForallPrimitive D P ∅.
  Proof.
    split.
    simpl.
    intros.
    rewrite get_layer_primitive_empty in H.
    discriminate.
  Qed.

  Global Instance forallprim_mapsto_primitive D (P: _ -> Prop) i σ:
    P σ ->
    ForallPrimitive D P (i ↦ σ).
  Proof.
    intros Hσ.
    split.
    - intros j σj Hσj.
      destruct (decide (j = i)); subst; get_layer_normalize_in Hσj; congruence.
  Qed.

  Global Instance forallprim_mapsto_globalvar D P i (τ: V):
    ForallPrimitive D P (i ↦ τ).
  Proof.
    split.
    - intros j σj Hσj.
      rewrite get_layer_primitive_mapsto_globalvar in Hσj.
      discriminate.
  Qed.

  Lemma forallprim_oplus_disjoint D (P: primsem D -> Prop) L1 L2:
    layers_disjoint L1 L2 ->
    ForallPrimitive D P L1 ->
    ForallPrimitive D P L2 ->
    ForallPrimitive D P (L1 ⊕ L2).
  Proof.
    intros HP H1 H2.
    constructor.
    intros i σ Hσ.
    destruct (layers_disjoint_primitive i D L1 L2); eauto.
    - eapply (forall_primitive_at (L:=L1) i).
      congruence.
    - eapply (forall_primitive_at (L:=L2) i).
      congruence.
  Qed.

  Lemma forallprim_oplus_union D (P: primsem D -> Prop) L1 L2:
    (forall σ1 σ2, P σ1 -> P σ2 -> P (σ1 ⊕ σ2)) ->
    ForallPrimitive D P L1 ->
    ForallPrimitive D P L2 ->
    ForallPrimitive D P (L1 ⊕ L2).
  Proof.
    intros HP H1 H2.
    split.
    - intros i σ Hσ.
      simpl in Hσ.
      rewrite get_layer_primitive_oplus in Hσ.
      destruct (get_layer_primitive i L1) as [[|]|] eqn:Hσ1;
      destruct (get_layer_primitive i L2) as [[|]|] eqn:Hσ2;
      try discriminate;
      simpl in Hσ;
      monad_norm;
      inversion Hσ; clear Hσ; subst.
      + eapply HP; eauto.
        * eapply (forall_primitive_at _ _ Hσ1).
        * eapply (forall_primitive_at _ _ Hσ2).
      + eapply (forall_primitive_at _ _ Hσ1).
      + eapply (forall_primitive_at _ _ Hσ2).
  Qed.

  Global Instance forallprim_mono:
    Monotonic ForallPrimitive (forallr -, (- ==> impl) ++> - ==> impl).
  Proof.
    repeat red.
    intros D P1 P2 HP L HL.
    constructor.
    intros i σ Hσ.
    apply HP.
    eapply HL.
    eassumption.
  Qed.

(** The following is wrong, because of [OK None] being refined by [OK (Some _)].
<<
  Global Instance forallprim_sim_mono:
    Proper
      (∀ R, (sim R ++> impl) ++> sim R ++> impl)
      ForallPrimitive.
>>
*)

End FORALL_PRIM.

(* unused ATM, needs [: typeclass_instances]
Hint Extern 2 (ForallPrimitive _ _ (_ ⊕ _)) =>
  eapply forallprim_oplus.
*)


(** * Well-formed layers *)

Section LAYER_OK.
  Context `{Hlayer: Layers}.
  Context `{Hprim: !Primitives primsem}.
  Context `{ident_dec: EqDec ident}.

  Record LayerOK_at {D} (L: layer D) (i: ident): Prop :=
    {
      layer_ok_primitive:
        isOK (get_layer_primitive i L);
      layer_ok_globalvar:
        isOK (get_layer_globalvar i L);
      layer_ok_disjoint:
        isOKNone (get_layer_primitive i L) \/
        isOKNone (get_layer_globalvar i L)
    }.

  Global Instance layer_ok_at_dec {D} (L: layer D) (i: ident):
    Decision (LayerOK_at L i) :=
    match (decide (isOK (get_layer_primitive i L) /\
                   isOK (get_layer_globalvar i L) /\
                   (isOKNone (get_layer_primitive i L) \/
                    isOKNone (get_layer_globalvar i L))))
    with
      | left Hyes => left _
      | right Hno => right _
    end.
  Proof.
    abstract (destruct Hyes as (H1 & H2 & H3); split; assumption).
    abstract (intros [H1 H2 H3]; eauto).
  Defined.

  Class LayerOK {D} (L: layer D): Prop :=
    layer_ok_at: forall i, LayerOK_at L i.

  (** This alternate definition is used for providing a decision procedure. *)
  Definition LayerOK_alt {D} (L: layer D) :=
    (forall i, get_layer_primitive i L <> OK None ->
               (fun i => isOK (get_layer_primitive i L) /\
                         isOKNone (get_layer_globalvar i L)) i) /\
    (forall i, get_layer_globalvar i L <> OK None ->
               (fun i => isOK (get_layer_globalvar i L) /\
                         isOKNone (get_layer_primitive i L)) i).

  (** Let's prove it is equivalent *)
  Lemma LayerOK_alt_equiv {D} (L: layer D):
    LayerOK_alt L <-> LayerOK L.
  Proof.
    unfold LayerOK_alt.
    split.
    * intros [H1 H2] i.
      specialize (H1 i).
      specialize (H2 i).
      split.
      + destruct (get_layer_primitive i L) as [[|]|]; eauto.
        destruct H1; try discriminate.
        assumption.
      + destruct (get_layer_globalvar i L) as [[|]|]; eauto.
        destruct H2; try discriminate.
        assumption.
      + destruct (get_layer_primitive i L) as [[|]|]; eauto.
        - destruct H1; try discriminate; eauto.
        - destruct H1; try discriminate; eauto.
    * intros H.
      split; intros i Hi; destruct (H i) as [Hp Hv Hd];
      split; destruct Hd; eauto; congruence.
  Qed.

  Global Instance LayerOK_dec {D} (L: layer D): Decision (LayerOK L) :=
    match decide (LayerOK_alt L) with
      | left Hyes => left _
      | right Hno => right _
    end.
  Proof.
    * abstract (apply LayerOK_alt_equiv; assumption).
    * abstract (rewrite <- LayerOK_alt_equiv; assumption).
  Defined.

  (** ** Monotonicity *)

  Global Instance layer_ok_at_le:
    Monotonic (@LayerOK_at) (forallr -, (≤) --> - ==> impl).
  Proof.
    intros D L2 L1 HL i [Hp Hg Hd].
    red in HL.
    split.
    - revert Hp; rauto.
    - revert Hg; rauto.
    - revert Hd; rauto.
  Qed.

  Lemma layer_ok_at_sim {D1 D2} (R: simrel D1 D2) L1 L2 i:
    sim R L1 L2 ->
    LayerOK_at L2 i ->
    LayerOK_at L1 i.
  Proof.
    intros HL [H2p H2v H2d].
    split.
    * eapply (isOK_le _ _ (option_le (sim R))); try eassumption.
      solve_monotonic.
    * eapply (isOK_le _ _ (option_le eq)); try eassumption.
      solve_monotonic.
    * destruct H2d; [left|right].
      + eapply (isOKNone_le _ _ (sim R)); try eassumption.
        solve_monotonic.
      + eapply (isOKNone_le _ _ eq); try eassumption.
        solve_monotonic.
  Qed.

  (** XXX: need as an instance of [LayerOK] also? *)
  Global Instance layer_ok_antitonic:
    Monotonic (@LayerOK) (forallr -, (≤) --> impl).
  Proof.
    intros D L2 L1 HL H i.
    specialize (H i).
    eapply layer_ok_at_le; eassumption.
  Qed.

  Global Instance layer_ok_sim_antitonic {D1 D2} (R: simrel D1 D2) L1 L2:
    sim R L1 L2 ->
    LayerOK L2 ->
    LayerOK L1.
  Proof.
    intros HL HL2 i.
    specialize (HL2 i).
    eapply layer_ok_at_sim; eassumption.
  Qed.

  (** ** Basic instances *)

  Global Instance empty_ok `{Layers} D:
    LayerOK (D := D) ∅.
  Proof.
    intros i.
    split; get_layer_normalize; eauto.
  Qed.

  Global Instance mapsto_function_ok {D} i (σ: primsem D):
    LayerOK (i ↦ σ).
  Proof.
    intros j.
    destruct (decide (j = i)); subst;
    split; get_layer_normalize; eauto.
  Qed.

  Global Instance mapsto_variable_ok {D} i (τ: V):
    LayerOK (D:=D) (i ↦ τ).
  Proof.
    intros j.
    destruct (decide (j = i)); subst;
    split; get_layer_normalize; eauto.
  Qed.

  Lemma layer_oplus_primitive_ok {D} (L: layer D) (i: ident) (σ: primsem D):
    isOKNone (get_layer_primitive i L) ->
    isOKNone (get_layer_globalvar i L) ->
    LayerOK L ->
    LayerOK (L ⊕ i ↦ σ).
  Proof.
    intros HLip HLiv HL j.
    specialize (HL j); destruct HL as [HLp HLv HLd].
    unfold isOKNone in *.
    destruct (decide (j = i)); subst.
    * split; get_layer_normalize;
      rewrite ?HLip, ?HLiv, ?id_left;
      eauto.
      right; reflexivity.
    * split; get_layer_normalize;
      rewrite ?id_right;
      eauto.
      destruct HLd as [H|H]; rewrite H; eauto.
      right; reflexivity.
  Qed.
End LAYER_OK.

(** * Other properties *)

(** Properties of [layers_disjoint]. *)

Lemma layers_disjoint_mapsto_globalvar_primitive `{Layers}
      {D1 D2} i1 i2 (κ1: V) (σ2: primsem D2):
      i1 <> i2 ->
      layers_disjoint (D1:=D1) (i1 ↦ κ1) (i2 ↦ σ2).
Proof.
  intros H0.
  apply layers_disjoint_sym.
  apply layers_disjoint_mapsto_primitive_globalvar.
  congruence.
Qed.

(** Express the monotonicity of [i ↦ σ] in terms of [≤]. *)

Global Instance layer_mapsto_mon `{Layers} D:
  @Monotonic (ident -> primsem D -> layer D) (↦) (- ==> (≤) ++> (≤)).
Proof.
  intros i σ1 σ2 Hσ.
  apply layer_le_intro.
  assumption.
Qed.

Lemma layer_oplus_primitive_same `{Layers} {D} L i (σ: primsem D):
  isOKNone (get_layer_primitive i L) ->
  get_layer_primitive i (L ⊕ i ↦ σ) = OK (Some σ).
Proof.
  intros HLi.
  get_layer_normalize.
  red in HLi.
  rewrite HLi.
  rewrite id_left.
  reflexivity.
Qed.

Lemma layer_oplus_primitive_other `{Layers} {D} L i (σ: primsem D) j:
  j <> i ->
  get_layer_primitive j (L ⊕ i ↦ σ) = get_layer_primitive j L.
Proof.
  intros Hij.
  get_layer_normalize.
  rewrite id_right.
  reflexivity.
Qed.

Lemma layer_oplus_globalvar `{Layers} {D} L i (σ: primsem D) j:
  get_layer_globalvar j (L ⊕ i ↦ σ) = get_layer_globalvar j L.
Proof.
  get_layer_normalize.
  autorewrite with res_option_globalvar.
  reflexivity.
Qed.

Section AuxLemma.

  Lemma get_layer_primitive_isOK `{LOps: Layers} {D}:
    forall i (a b: _ D),
      isOK (get_layer_primitive i (a ⊕ b)) ->
      isOK (get_layer_primitive i a)
      /\ isOK (get_layer_primitive i b).
  Proof.
    intros. destruct H as [? Hcom].
    specialize (get_layer_primitive_oplus i a b).
    rewrite Hcom.
    intros.
    destruct (get_layer_primitive i a);
      destruct (get_layer_primitive i b); inv_monad H.
    - eauto.
    - destruct o; inversion H1.
  Qed.

  Lemma get_layer_primitive_none `{LOps: Layers} {D}:
    forall i (a b: _ D),
      get_layer_primitive i b = OK None ->
      get_layer_primitive i a = OK None ->
      isOK (get_layer_primitive i (a ⊕ b)) ->
      get_layer_primitive i (a ⊕ b) = OK None.
  Proof.
    intros. destruct H1 as [? Hcom].
    specialize (get_layer_primitive_oplus i a b).
    rewrite Hcom. rewrite H. rewrite H0.
    intros. inv_monad H1. 
    reflexivity.
  Qed.
 
  Lemma get_layer_globalvar_isOK `{LOps: Layers} {D}:
    forall i (a b: _ D),
      isOK (get_layer_globalvar i (a ⊕ b)) ->
      isOK (get_layer_globalvar i a)
      /\ isOK (get_layer_globalvar i b).
  Proof.
    intros. destruct H as [? Hcom].
    specialize (get_layer_globalvar_oplus i a b).
    rewrite Hcom.
    destruct (get_layer_globalvar i a) as [ [ va | ] | ] ;
      destruct (get_layer_globalvar i b) as [ [ vb | ] | ] ;
      res_option_globalvar_red;
      eauto;
      congruence.
  Qed.

  Lemma get_layer_globalvar_OK_Some_left `{LOps: Layers} {D}:
    forall i (a b: _ D) v v',
      get_layer_globalvar i a = OK (Some v) ->
      get_layer_globalvar i (a ⊕ b) = OK (Some v') ->
      v' = v.
  Proof.
    intros. 
    specialize (get_layer_globalvar_oplus i a b).
    rewrite H. rewrite H0.
    destruct (get_layer_globalvar i b) as [ [ v0 | ] | ];
      res_option_globalvar_red;
      try congruence.
    destruct (globalvar_eq_dec v v0).
    - subst. autorewrite with res_option_globalvar. congruence.
    - rewrite res_option_globalvar_oplus_diff; congruence.
  Qed.

  Lemma get_layer_globalvar_OK_Some_right `{LOps: Layers} {D}:
    forall i (a b: _ D) v v',
      get_layer_globalvar i b = OK (Some v) ->
      get_layer_globalvar i (a ⊕ b) = OK (Some v') ->
      v' = v.
  Proof.
    intros. 
    specialize (get_layer_globalvar_oplus i a b).
    rewrite H. rewrite H0.
    destruct (get_layer_globalvar i a) as [ [ v0 | ] | ];
      res_option_globalvar_red;
      try congruence.
    destruct (globalvar_eq_dec v v0).
    - subst. autorewrite with res_option_globalvar. congruence.
    - rewrite res_option_globalvar_oplus_diff; congruence.
  Qed.

  Lemma get_layer_globalvar_left `{LOps: Layers} {D}:
    forall i (a b: _ D) v,
      get_layer_globalvar i a = OK (Some v) ->
      isOK (get_layer_globalvar i (a ⊕ b)) ->
      get_layer_globalvar i (a ⊕ b) = OK (Some v).
  Proof.
    intros. destruct H0 as [? Hcom].
    specialize (get_layer_globalvar_oplus i a b).
    rewrite Hcom. rewrite H.
    destruct (get_layer_globalvar i b) as [ [ v0 | ] | ];
      res_option_globalvar_red;
      try congruence.
    destruct (globalvar_eq_dec v v0).
    - subst. autorewrite with res_option_globalvar. congruence.
    - rewrite res_option_globalvar_oplus_diff; congruence.
  Qed.

  Lemma get_layer_globalvar_right `{LOps: Layers} {D}:
    forall i (a b: _ D) v,
      get_layer_globalvar i b = OK (Some v) ->
      isOK (get_layer_globalvar i (a ⊕ b)) ->
      get_layer_globalvar i (a ⊕ b) = OK (Some v).
  Proof.
    intros. destruct H0 as [? Hcom].
    specialize (get_layer_globalvar_oplus i a b).
    rewrite Hcom. rewrite H. 
    destruct (get_layer_globalvar i a) as [ [ v0 | ] | ];
      res_option_globalvar_red;
      try congruence.
    destruct (globalvar_eq_dec v v0).
    - subst. autorewrite with res_option_globalvar. congruence.
    - rewrite res_option_globalvar_oplus_diff; congruence.
  Qed.

  Lemma get_layer_globalvar_none `{LOps: Layers} {D}:
    forall i (a b:_ D),
      get_layer_globalvar i b = OK None ->
      get_layer_globalvar i a = OK None ->
      isOK (get_layer_globalvar i (a ⊕ b)) ->
      get_layer_globalvar i (a ⊕ b) = OK None.
  Proof.
    intros. destruct H1 as [? Hcom].
    specialize (get_layer_globalvar_oplus i a b).
    rewrite Hcom. rewrite H. rewrite H0.
    autorewrite with res_option_globalvar.
    congruence.
  Qed.

  Lemma get_layer_primitive_cancel `{LOps: Layers} {D}:
    forall i (a b: _ D),
      get_layer_primitive i (a ⊕ b) = OK None ->
      get_layer_primitive i b = OK None /\
      get_layer_primitive i a = OK None.
  Proof.
    intros. 
    specialize (get_layer_primitive_oplus i a b).
    rewrite H. 
    intros. 
    destruct (get_layer_primitive i a); try destruct o;
    destruct (get_layer_primitive i b); try destruct o;
    inv_monad H0; eauto.
  Qed.

  Lemma get_layer_globalvar_cancel `{LOps: Layers} {D}:
    forall i (a b: _ D),
      get_layer_globalvar i (a ⊕ b) = OK None ->
      get_layer_globalvar i b = OK None /\
      get_layer_globalvar i a = OK None.
  Proof.
    intros. 
    specialize (get_layer_globalvar_oplus i a b).
    rewrite H. 
    destruct (get_layer_globalvar i a) as [ [ va | ] | ] ;
    destruct (get_layer_globalvar i b) as [ [ vb | ] | ] ;
    res_option_globalvar_red;
    try congruence;
    auto.
    destruct (globalvar_eq_dec va vb).
    - subst. autorewrite with res_option_globalvar. congruence.
    - rewrite res_option_globalvar_oplus_diff; congruence.
  Qed.

  Lemma get_layer_primitive_OK_eq `{LOps: Layers} `{Heq: EqDec ident} {D}:
    forall i j σ1 σ2,
      get_layer_primitive (D:=D) j (i ↦ σ2) = OK (Some σ1) ->
      σ2 = σ1.      
  Proof.
    intros.  
    destruct (Heq j i); subst.
    - subst. rewrite get_layer_primitive_mapsto in H.
      inversion H. reflexivity.
    - rewrite get_layer_primitive_mapsto_other_primitive in H.
      discriminate. assumption.
  Qed.

End AuxLemma.
