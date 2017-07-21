Require Export liblayers.logic.Language.

Section WITH_SEMANTICS.
  Context {layerdata simrel ident F primsem V module layer}
    `{Hld: Category layerdata simrel}
    `{Hmodule: Modules ident F V module}
    `{primsem_sim: !Sim simrel primsem}
    `{primsem_prim_ops: !PrimitiveOps primsem}
    `{Hprimsem: !CategorySim layerdata simrel primsem}
    `{layersim_op: !Sim simrel layer}
    `{Hlayercs: !CategorySim layerdata simrel layer}
    `{layer_ops: !LayerOps ident primsem V layer}
    `{Hlayer: !Layers ident primsem V layer}
    `{sem_ops: !SemanticsOps ident F primsem V module layer}
    `{fsem_ops: !FunctionSemanticsOps ident F primsem V module layer}
    `{Hsem: !Semantics ident F primsem V module layer}.

  Global Instance logic_impl_ops: LayerLogicOps ident F primsem V module layer :=
    {
      ll_vdash D1 D2 :=
        {| vdash2 L1 R M L2 := sim R L2 (〚M〛 L1) |}
    }.

  Global Instance logic_impl:
    LayerLogic ident F primsem V module layer.
  Proof.
    split.

Opaque module_oplus.

    (** [empty_rule] *)
    * intros D L.
      simpl.
      change (sim id) with (le (A:=layer D)).
      apply semof_incr.

    (** [var_rule] *)
    * intros D L i τ.
      simpl.
      apply (semof_variable i τ L).

    (** [vcomp_rule] *)
    * intros D1 D2 D3 R S L1 L2 L3 M N.
      unfold vdash2; simpl.
      intros HL1 H12 H23.
      htransitivity (〚N〛 L2); trivial.
      htransitivity (〚N〛 (〚M〛 L1)).
      + repeat rstep.
        split; eauto.
        eapply lang_semof_wf; eauto.
      + transitivity (〚N ⊕ M〛 L1).
        - eapply lang_semof_vcomp; eauto.
        - repeat first [apply commutativity | rstep].
          split; eauto; rauto.

    (** [hcomp_rule] *)
    * intros D D' R L M1 M2 L1 L2.
      unfold vdash2; simpl.
      intros HL H1 H2.
      htransitivity (〚M1〛 L ⊕ 〚M2〛 L).
      + apply oplus_sim_monotonic; eauto.
      + apply lang_semof_hcomp; eauto.

    (** [conseq_rule] *)
    * intros D1 D2 D3 D4 R21 R32 R43 L1 L2 L3 L4 M.
      unfold vdash2; simpl.
      intros HL1 H21 H43 H32.
      htransitivity L3; try assumption.
      htransitivity (〚M〛 L2); try assumption.
      solve_monotonic.
      split; eauto; rauto.

    (** [vdash_module_le] *)
    * intros D1 D2 R L1 L2 M N HL1 HMN.
      simpl.
      eapply cat_sim_monotonic; eauto;
      solve_monotonic.
      split; eauto; rauto.

    (** [vdash_rel_equiv] *)
    * intros D1 D2 R S L1 L2 M HRS H.
      simpl in *.
      rewrite <- HRS.
      assumption.
  Qed.

  Lemma logic_intro {DL DH} (LL: layer DL) R M (LH: layer DH):
    sim R LH (〚M〛 LL) ->
    LL ⊢ (R, M) : LH.
  Proof.
    tauto.
  Qed.

  Lemma logic_elim {DL DH} (LL: layer DL) R M (LH: layer DH):
    LL ⊢ (R, M) : LH ->
    sim R LH (〚M〛 LL).
  Proof.
    tauto.
  Qed.

  (** (now a special case of [vdash_module_le]) *)
  Lemma vdash_oplus_empty {D1 D2} L1 (R: simrel D1 D2) M L2:
    layer_wf L1 ->
    L1 ⊢ (R, M) : L2 ->
    L1 ⊢ (R, M ⊕ ∅) : L2.
  Proof.
    intros Hwf.
    eapply vdash_module_le; eauto.
    eapply left_upper_bound.
  Qed.
End WITH_SEMANTICS.
