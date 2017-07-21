Require Import Coq.ZArith.ZArith.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import liblayers.lib.Decision.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.logic.PTrees.
Require Import liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeModules.
Require Export liblayers.logic.Semantics.
Require Import liblayers.logic.GlobalVars.

Local Existing Instance ptree_module_ops.
Local Existing Instance ptree_layer_ops.
Local Existing Instance ptree_module_prf.
Local Existing Instance ptree_layer_prf.
Local Transparent ptree_module ptree_module_ops.
Local Transparent ptree_layer ptree_layer_ops.
Local Opaque PTree.combine.

Local Hint Extern 1 (Sim _ (ptree_layer _ _)) =>
  eapply ptree_layer_sim_op : typeclass_instances.


(** * Preliminaries *)

(** We want to be able to use [PTree]-based layers to build up more
  complex kinds of layers, then use the code in this file to build a
  semantics operator with all the required properties for these more
  complex layers. To make this possible, we write our definitions in
  the context of an arbitrary kind of layers, and we make the
  connection with PTree layers explicit thanks to the following
  class. *)

Class PTreeSemanticsOps {layerdata simrel primsem V} layer
    `{layer_ops: LayerOps layerdata ident primsem V layer}
    `{primsem_sim_op: Sim layerdata simrel primsem}
    `{layer_sim_op: Sim layerdata simrel layer} :=
  {
    ptree_semof_inj D:
      ptree_layer primsem V D -> layer D
  }.

Class PTreeSemantics {layerdata simrel primsem V} layer
    `{ptree_semof_ops: PTreeSemanticsOps layerdata simrel primsem V layer}
    `{cat_ops: !CategoryOps layerdata simrel} :=
  {
    ptree_semof_primitives :>
      Primitives primsem;
    ptree_semof_layers :>
      Layers ident primsem V layer;
    ptree_semof_inj_sim :>
      Monotonic ptree_semof_inj (forallr R, sim R ++> sim R);
    get_ptree_semof_inj_primitive i D L:
      get_layer_primitive i (ptree_semof_inj D L) =
      get_layer_primitive i L;
    get_ptree_semof_inj_globalvar i D L:
      get_layer_globalvar i (ptree_semof_inj D L) =
      get_layer_globalvar i L;
    ptree_semof_inj_variable i D (τ: V):
      sim id (i ↦ τ) (ptree_semof_inj D (i ↦ τ));
    ptree_semof_inj_empty D:
      sim id (ptree_semof_inj D ∅) ∅;
    ptree_semof_wf D (L: layer D) (L': ptree_layer primsem V D):
      layer_wf L ->
      layer_wf (ptree_semof_inj D L' ⊕ L)
  }.

Global Instance ptree_semof_inj_sim_params:
  Params (@ptree_semof_inj) 2.

(** The trivial instance below can be used to obtain a semantics on
  [ptree_layer] itself. *)

Section PTREE_TRIVIAL_SEMANTICS.
  Local Instance ptree_semantics_trivial_ops {layerdata simrel primsem V}
      {gvar_ops: GlobalVarsOps V}
      `{PrimitiveOps layerdata primsem}
      `{primsem_sim_op: Sim layerdata simrel primsem}:
    PTreeSemanticsOps (ptree_layer primsem V) :=
    {
      ptree_semof_inj D L := L
    }.

  Local Instance ptree_semantics_trivial_prf {layerdata simrel primsem V}
      {gvar_ops: GlobalVarsOps V}
      `{Primitives layerdata simrel primsem}:
    PTreeSemantics (ptree_layer primsem V).
  Proof.
    split; try typeclasses eauto; simpl.
    - solve_monotonic.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - tauto.
  Qed.
End PTREE_TRIVIAL_SEMANTICS.

Hint Extern 1 (PTreeSemanticsOps (ptree_layer _ _)) =>
  eapply ptree_semantics_trivial_ops : typeclass_instances.

Hint Extern 1 (PTreeSemantics (ptree_layer _ _)) =>
  eapply ptree_semantics_trivial_prf : typeclass_instances.


(** * Semantics of [ptree_module]s *)

Section PTREE_SEMANTICS.
  Context `{Hps: PTreeSemantics}.
  Context {F} `{Fops: !FunctionSemanticsOps _ F _ _ (ptree_module _ _) layer}.

  Definition ptree_semantics_mapdef D (M: ptree_module F V) L:
    ptree_layer _ _ D :=
      (PTree.map (fun i => Monad.bind (semof_fundef D (M, L) i)) (fst M),
       snd M).

  Definition ptree_semof_module D (M: ptree_module F V) L :=
    ptree_semof_inj D (ptree_semantics_mapdef D M L).

  Lemma ptree_get_semof_module_primitive {D} i M L:
    get_layer_primitive i (ptree_semof_module D M L) = 
    semof_function D (M, L) i (get_module_function i M).
  Proof.
    simpl.
    unfold ptree_semof_module.
    rewrite get_ptree_semof_inj_primitive.
    simpl.
    unfold ptree_layer_primitive, ptree_semantics_mapdef; simpl.
    unfold semof_function, ptree_module_function; simpl.
    rewrite PTree.gmap.
    destruct ((fst M) ! i) as [[|]|]; reflexivity.
  Qed.

  Lemma ptree_get_semof_module_globalvar {D} i M L:
    get_layer_globalvar i (ptree_semof_module D M L) =
    get_module_variable i M.
  Proof.
    unfold ptree_semof_module.
    rewrite get_ptree_semof_inj_globalvar.
    reflexivity.
  Qed.

  Local Instance ptree_semof:
      SemanticsOps ident F primsem V (ptree_module F V) layer :=
    {
      lang_semof :=
        {|
          semof D ML :=
            let '(M, L) := ML in ptree_semof_module D M L ⊕ L
        |}
    }.

  (* We prove accessor lemmas separately, outside of the Semantics proof,
     so that they can be used to prove FunctionSemantics. *)

  Lemma ptree_get_semof_globalvar
        (D : layerdata) (i : ident) (M : ptree_module F V) (L : layer D):
    get_layer_globalvar i (〚 M 〛 L) =
    get_module_variable i M ⊕ get_layer_globalvar i L.
  Proof.
    simpl (semof _ _).
    get_layer_normalize.
    rewrite ptree_get_semof_module_globalvar.
    reflexivity.
  Qed.

  Lemma ptree_get_semof_primitive
        (D : layerdata) (i : ident) (M : ptree_module F V) (L : layer D):
    get_layer_primitive i (〚 M 〛 L) =
    semof_function D (M, L) i (get_module_function i M)
    ⊕ get_layer_primitive i L.
  Proof.
    simpl (semof _ _).
    get_layer_normalize.
    rewrite ptree_get_semof_module_primitive.
    reflexivity.
  Qed.

  Context `{HFops: !FunctionSemantics _ F _ _ (ptree_module _ _) layer}.

  Global Instance ptree_semantics_mapdef_rel:
    Monotonic
      ptree_semantics_mapdef
      (forallr R, rel_curry (module_layer_sim _ _ R ++> sim R)).
  Proof.
    unfold ptree_semantics_mapdef.
    intros D1 D2 R [M1 L1] [M2 L2] HML.
    inversion HML as [HM HL HL2 Hdisj]; subst.
    simpl.
    solve_monotonic.
  Qed.

  Global Instance ptree_semof_module_rel:
    Monotonic
      ptree_semof_module
      (forallr R, rel_curry (module_layer_sim _ _ R ++> sim R)).
  Proof.
    unfold ptree_semof_module.
    repeat rstep.
    destruct x, y.
    simpl.
    solve_monotonic.
  Qed.

  Global Instance ptree_semof_rel:
    Monotonic
      semof
      (forallr R, module_layer_sim _ _ R ++> sim R).
  Proof.
    simpl.
    repeat rstep.
    simpl (semof _ _) in *.
    apply hlub_intro; eauto.
    htransitivity (ptree_semof_inj v (ptree_semantics_mapdef v M2 L2)).
    - unfold ptree_semof_module.
      solve_monotonic.
      constructor; eauto.
    - apply left_upper_bound.
  Qed.

  Lemma ptree_semof_module_variable D i τ L:
    sim id (i ↦ τ) (ptree_semof_module D (i ↦ τ) L).
  Proof.
    unfold ptree_semof_module.
    htransitivity (ptree_semof_inj D (i ↦ τ)).
    - apply ptree_semof_inj_variable.
    - monotonicity.
      split.
      + intros j.
        simpl.
        rewrite PTree.gempty.
        constructor.
      + intros j.
        simpl.
        destruct (decide (j = i)) as [Hij | Hij].
        * subst.
          rewrite !PTree.gss; simpl.
          reflexivity.
        * rewrite !PTree.gso by assumption.
          reflexivity.
  Qed.

  Lemma ptree_semof_module_empty D L:
    sim id (ptree_semof_module D ∅ L) ∅.
  Proof.
    unfold ptree_semof_module.
    htransitivity (ptree_semof_inj D ∅).
    - reflexivity.
    - apply ptree_semof_inj_empty.
  Qed.

  Global Instance ptree_semof_prf:
    Semantics ident F primsem V (ptree_module F V) layer.
  Proof.
    split; try typeclasses eauto; simpl (semof _ _).
    - apply ptree_get_semof_globalvar.
    - apply ptree_get_semof_primitive.
    - intros D i M L.
      ehtransitivity.
      + eapply ptree_semof_module_variable.
      + apply left_upper_bound.
    - intros D M L.
      rewrite commutativity.
      apply left_upper_bound. (** XXX: should be able to use right_upper_bound *)
    - intros D L.
      apply hlub_intro.
      + etransitivity.
        * apply ptree_semof_module_empty.
        * apply lower_bound.
      + reflexivity.
    - intros D M L.
      apply ptree_semof_wf.
  Qed.
End PTREE_SEMANTICS.
