Require Import liblayers.lib.Decision.
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Layers.
Require Import liblayers.logic.GlobalVars.

Section WITH_LAYER_DATA.
Context {layerdata simrel} `{Hld: Category layerdata simrel}.


(** * Semantics of modules *)

Class SemanticsOps ident F primsem V module layer
    {gvar_ops: GlobalVarsOps V}
    `{module_ops: !ModuleOps ident F V module}
    `{primsem_prim_ops: !PrimitiveOps (V:=layerdata) primsem}
    `{layer_ops: !LayerOps ident primsem V layer} :=
  {
    lang_semof :> Semof module layer layer
  }.


(** * Semantics of individual function definitions *)

(** This is used as a general interface between implementations of
  types of layers and the semantics of languages. *)

Class FunctionSemanticsOps ident F primsem V module layer
    {gvar_ops: GlobalVarsOps V}
    `{module_ops: !ModuleOps ident F V module}
    `{primsem_sim: !Sim simrel primsem}
    `{primsem_prim_ops: !PrimitiveOps primsem}
    `{layerqs_sim: !Sim simrel layer}
    `{layer_ops: !LayerOps ident primsem V layer} :=
  {
    semof_fundef D (ML: module * layer D) :> ident -> F -> res (primsem D)
  }.


(** * Specification *)

(** In order to express a monotonicity property that can capture the
  requirement of vertical composition, we introduce the relation
  [module_layer_sim], which allows the primitives in [L1] to be
  implemented in [M2] when they are not refined in [L2].

  For [make_program] to be monotonic under this relation, we also need
  the following condition to hold (so that a function in [M2] cannot
  both already be present in [M1] and implement a primitive in [L1],
  which would cause an [Error] on the left-hand side, but not on the
  right-hand side). *)

Record modules_layers_ok `{SemanticsOps} {D1 D2} M1 M2 L1 L2 :=
{
  modules_layers_function_primitive_ok:
  forall i κ1 κ2 σ1,
    get_module_function i M1 = OK (Some κ1) ->
    get_module_function i M2 = OK (Some κ2) ->
    get_layer_primitive (D:=D1) i L1 = OK (Some σ1) ->
    get_layer_primitive (D:=D2) i L2 <> OK None;
  modules_layers_variable_ok:
  forall i v1 v2 v1',
    get_module_variable i M1 = OK (Some v1) ->
    get_module_variable i M2 = OK (Some v2) ->
    get_layer_globalvar (D:=D1) i L1 = OK (Some v1') ->
    v1 <> v1' ->
    get_layer_globalvar (D:=D2) i L2 <> OK None
}.

Inductive module_layer_sim `{SemanticsOps} `{!Sim simrel layer} D1 D2 R:
  rel (module * layer D1)%type (module * layer D2)%type :=
    module_layer_sim_intro M1 M2 L1 L2:
      M1 ≤ M2 ->
      simRR D1 D2 R L1 (〚M2〛 L2) ->
      layer_wf L2 ->
      modules_layers_ok M1 M2 L1 L2 ->
      module_layer_sim D1 D2 R (M1, L1) (M2, L2).

(** Now we can specify both [semof_fundef] and [semof] in terms of
  this relation. *)

Class FunctionSemantics ident F primsem V module layer
    `{semof_fundef_ops: FunctionSemanticsOps ident F primsem V module layer}
    `{semof_ops: SemanticsOps ident F primsem V module layer}: Prop :=
  {
    semof_fundef_sim :>
      Monotonic
        semof_fundef
        (forallr R, module_layer_sim _ _ R ++> - ==> - ==> res_le (sim R))
  }.

Global Instance semof_fundef_sim_params_:
  Params (@semof_fundef) 4.

Definition semof_function `{fsem_ops: FunctionSemanticsOps} :=
  fun D (ML: module * layer D) (i: ident) (d: res (option F)) =>
    mκ <- d;
    match mκ with
      | None => OK None
      | Some κ =>
        σ <- semof_fundef (FunctionSemanticsOps := fsem_ops) D ML i κ;
        OK (Some σ)
    end.

Class Semantics ident F primsem V module layer
    `{fsem_ops: FunctionSemanticsOps ident F primsem V module layer}
    `{lsem_ops: !SemanticsOps ident F primsem V module layer} :=
  {
    semof_monotonic :>
      Monotonic semof (forallr R, module_layer_sim _ _ R ++> sim R);
    get_semof_globalvar {D} (i: ident) (M: module) (L: layer D):
      get_layer_globalvar i (〚M〛 L) =
      get_module_variable i M ⊕
      get_layer_globalvar i L;
    get_semof_primitive {D} (i: ident) (M: module) (L: layer D):
      get_layer_primitive i (〚M〛 L) = 
      semof_function D (M, L) i (get_module_function i M) ⊕
      get_layer_primitive i L;
    semof_variable {D} (i: ident) (τ: V) (L: layer D):
      i ↦ τ ≤ 〚i ↦ τ〛 L;
    semof_incr D (M: module) (L: layer D):
      sim id L (〚M〛 L);
    semof_empty D (L: layer D):
      sim id (〚∅〛 L) L;
    lang_semof_wf {D} (M: module) (L: layer D):
      layer_wf L ->
      layer_wf (〚M〛 L)
  }.

Global Instance semof_monotonic_params_:
  Params (@semof) 2.


  (** * Properties *)

  Context `{Hsem: Semantics} `{Hmod: !Modules _ _ _ _} `{Hlay: !Layers _ _ _ _}.

  Global Instance layer_sim_module_layer_sim D1 D2 R:
    Related
      ((≤) * (sim R /\ rsat layer_wf))%rel
      (module_layer_sim D1 D2 R)
      subrel.
  Proof.
    intros [M1 L1] [M2 L2] (HM & HL (* & HL2 *)); simpl in *.
    constructor; eauto.
    - htransitivity L2; try rauto.
      eapply semof_incr.
    - change (rsat layer_wf L1 L2); rauto.
    - split.
      +
      intros i κ1 κ2 σ1 HM1i HM2i HL1i.
      assert
        (H: res_le (option_le (sim R))
          (get_layer_primitive i L1)
          (get_layer_primitive i L2))
        by solve_monotonic.
      destruct H as [_ _ [|]|]; try discriminate; eauto.
      +
      intros i v1 v2 v1' HM1i HM2i HL1i.
      assert
        (H: res_le (option_le eq)
          (get_layer_globalvar i L1)
          (get_layer_globalvar i L2))
        by solve_monotonic.
      destruct H as [_ _ [|]|]; try discriminate; eauto.
  Qed.

  (** ** Propeties of [semof_fundef] *)

  (** Flip the order of the subgoals for [bind] *)
  Local Instance bind_res_le {A1 B1 A2 B2} (RA:rel A1 A2) (RB:rel B1 B2) f g x y:
    RStep
      (res_le RA x y /\ (RA ++> res_le RB)%rel f g)
      (res_le RB (bind f x) (bind g y)).
  Proof.
    intros [Hxy Hfg].
    rauto.
  Qed.

  Lemma semof_function_sim
      `{semof_fundef_ops: !FunctionSemanticsOps _ _ _ _ _ _}
      `{Hsemof_fundef: !FunctionSemantics _ _ _ _ _ _}:
    Monotonic
      semof_function
      (forallr R, module_layer_sim _ _ R ++> - ==> res_le (option_le eq) ++>
            res_le (option_le (sim R))).
  Proof.
    unfold semof_function.
    rauto.
  Qed.

  (** ** Properties of [semof] *)

  Lemma lang_semof_hcomp {D} (M N: module) (L: layer D):
    layer_wf L ->
    sim id (〚M〛 L ⊕ 〚N〛 L) (〚M ⊕ N〛 L).
  Proof.
    intros.
    apply hlub_intro.
    - repeat rstep.
      apply left_upper_bound.
      split; try rauto; assumption.
    - repeat rstep.
      apply right_upper_bound.
      split; try rauto; assumption.
  Qed.

  Lemma lang_semof_vcomp {D} (M N: module) (L: layer D):
    layer_wf L ->
    sim id (〚M〛 (〚N〛 L)) (〚M ⊕ N〛 L).
  Proof.
    intros HL.
    monotonicity.
    constructor; eauto.
    - apply left_upper_bound.
    - monotonicity.
      constructor; eauto.
      + apply right_upper_bound.
      + apply semof_incr.
      + split;
        repeat intro;
        congruence.
    - split.
      +
      intros i κ1 κ2 σ1.
      get_module_normalize.
      rewrite get_semof_primitive.
      intros Hκ1 Hκ2 Hσ1.
      destruct (get_layer_primitive i L) as [[|]|]; try discriminate.
      destruct (get_module_function i N) as [[|]|]; try discriminate.
      destruct (get_module_function i M) as [[|]|]; try discriminate.
      +
      intros i v1 v2 v1'.
      get_module_normalize.
      rewrite get_semof_globalvar.
      intros Hv1 Hv2 Hv1'.
      intro Hdiff.
      destruct (get_layer_globalvar i L) as [[|]|]; try discriminate.
      exfalso.
      revert Hv1'. autorewrite with res_option_globalvar.
      intro ABSURD.
      rewrite ABSURD in Hv2. rewrite Hv1 in Hv2.
      rewrite res_option_globalvar_oplus_diff in Hv2; congruence.
  Qed.

  (** ** Disjointness of modules and layers *)

  (** Due to ⊕ being idempotent on global variables, we have to replace
      this property with [noconflict], modified accordingly. *)

  Inductive noconflict {A B C}:
    res(option A) -> res(option B) -> res(option C) -> res(option B) -> Prop :=
  | noconflict_n: noconflict (OK None) (OK None) (OK None) (OK None)
  | noconflict_a a: noconflict (OK (Some a)) (OK None) (OK None) (OK None)
  | noconflict_b b: noconflict (OK None) (OK (Some b)) (OK None) (OK None)
  | noconflict_c c: noconflict (OK None) (OK None) (OK (Some c)) (OK None)
  | noconflict_d d: noconflict (OK None) (OK None) (OK None) (OK (Some d))
  (** The following case is due to idempotent ⊕ on global variables. *)
  | noconflict_eq b: noconflict (OK None) (OK (Some b)) (OK None) (OK (Some b)).

  Definition isError' {U} (a: res U) :=
    match a with
      | OK _ => False
      | Error _ => True
    end.

  Lemma isError_equiv {U}:
    isError' = isError (A := U).
  Proof.
    clear.
    apply FunctionalExtensionality.functional_extensionality.
    intro u.
    apply ExtensionalityAxioms.prop_ext.
    unfold isError, isError'.
    destruct u.
    + split; try tauto. destruct 1; congruence.
    + split; try tauto. eauto.
  Qed.

  Lemma noconflict_equiv {I A B C} {a : I -> res (option A)} {b1 b2: I -> res (option B)} {c: I -> res (option C)}:
    ((forall i, (~ isOKNone (a i)) -> (~ isError (a i)) /\ isOKNone (b1 i) /\ isOKNone (c i) /\ isOKNone (b2 i)) /\
    (forall i, (~ isOKNone (b1 i)) -> (~ isError (b1 i)) /\ isOKNone (a i) /\ isOKNone (c i) /\ (isOKNone (b2 i) \/ b2 i = b1 i)) /\
    (forall i, (~ isOKNone (c i)) -> (~ isError (c i)) /\ isOKNone (a i) /\ isOKNone (b1 i) /\ isOKNone (b2 i)) /\
    (forall i, (~ isOKNone (b2 i)) -> (~ isError (b2 i)) /\ isOKNone (a i) /\ isOKNone (c i) /\ (isOKNone (b1 i) \/ b1 i = b2 i))) <->
    (forall i, noconflict (a i) (b1 i) (c i) (b2 i)).
  Proof.
    clear.
    symmetry.
    repeat rewrite <- isError_equiv.
    split.
    + intro NOCONF.
      split; [ | split; [ | split ] ];
      intro i;
      specialize (NOCONF i);
      inversion NOCONF; subst; simpl; unfold isOKNone, isError';
      intuition congruence.
    + intros (HA & HB1 & HC & HB2) i.
      specialize (HA i). specialize (HB1 i). specialize (HC i). specialize (HB2 i).
      unfold isOKNone, isError' in HA, HB1, HC, HB2.
      destruct (a i) as [ [ | ] | ] ;
        [ | | (exfalso; intuition congruence) ].
      {
        destruct HA as (_ & Hb1 & Hc & Hb2);
        [ congruence | ] ;
        rewrite Hb1; rewrite Hc; rewrite Hb2;
        constructor.
      }
      clear HA.
      destruct (c i) as [ [ | ] | ] ;
        [ | | (exfalso; intuition congruence) ].
      {
        destruct HC as (_ & _ & Hb1 & Hb2);
        [ congruence | ] ;
        rewrite Hb1; rewrite Hb2;
        constructor.
      }
      clear HC.
      destruct (b1 i) as [ [ | ] | ] ;
        [ | | (exfalso; intuition congruence) ] .
      {
        destruct HB1 as (_ & _ & _ & Hb2);
        [ congruence  | ] ;
        destruct Hb2 as [Hb2 | Hb2];
        rewrite Hb2;
        constructor.
      }
      clear HB1.
      destruct (b2 i) as [ [ | ] | ] ;
        [ | | (exfalso; intuition congruence) ] ;
        constructor.
  Qed.

  Definition module_layer_disjoint {D} M (L: layer D) :=
    forall i,
      noconflict
        (get_module_function i M)
        (get_module_variable i M)
        (get_layer_primitive i L)
        (get_layer_globalvar i L).

  Global Instance module_layer_disjoint_dec {D} M (L: layer D):
    Decision (module_layer_disjoint M L).
  Proof.
    unfold module_layer_disjoint.
    apply (decide_rewrite _ _ noconflict_equiv).
    typeclasses eauto.
  Defined.
End WITH_LAYER_DATA.

Global Instance semof_fundef_sim_params:
  Params (@semof_fundef) 4.

Global Instance semof_monotonic_params:
  Params (@semof) 2.
