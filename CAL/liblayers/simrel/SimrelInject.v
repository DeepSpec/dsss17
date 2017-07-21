Require Import Coq.Program.Basics.
Require Import LogicalRelations.
Require Import SimulationRelation.
Require Import Structures.
Require Import OptionOrders.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Import liblayers.compcertx.CompcertStructures.
Local Opaque mwd_ops.

(** * [inject] as a simulation relation *)

Lemma Ple_lub a b:
  (forall c, Plt c a -> Plt c b) ->
  Ple a b.
Proof.
  intros H.
  destruct (peq a 1) as [ | NE ]; try xomega.
  generalize (Ppred_Plt _ NE). intro LT.
  specialize (H _ LT).
  revert LT.
  replace a with (Pos.succ (Pos.pred a)) at 2 3; [ xomega | ] .
  apply Pos.succ_pred.
  assumption.
Qed.

Record simrel_inject_world: Type :=
  {
    simrel_inject_meminj :> block -> option (block * Z);
    nextblock_high: block;
    nextblock_low: block;
    simrel_inject_meminj_valid b1 b2 o:
      simrel_inject_meminj b1 = Some (b2, o) ->
      Plt b1 nextblock_high /\ Plt b2 nextblock_low;
    simrel_inject_globals b:
      block_is_global b -> simrel_inject_meminj b = Some (b, 0);
  }.

Lemma simrel_inject_world_eq j1 j2:
  simrel_inject_meminj j1 = simrel_inject_meminj j2 -> 
  nextblock_high j1 = nextblock_high j2 ->
  nextblock_low j1 = nextblock_low j2 ->
  j1 = j2.
Proof.
  intros H H0 H1.
  destruct j1; destruct j2; simpl in * |- * ; subst.
  f_equal;
  apply ProofIrrelevance.proof_irrelevance.
Qed.


Record simrel_inject_acc (j1 j2: simrel_inject_world): Prop :=
  simrel_inject_acc_intro
    {
      simrel_inject_acc_carrier :> Values.inject_incr j1 j2;
      nextblock_high_le: Ple (nextblock_high j1) (nextblock_high j2);
      nextblock_low_le: Ple (nextblock_low j1) (nextblock_low j2);
      simrel_inject_acc_separated:
        forall b1 b2 delta,
          j1 b1 = None ->
          j2 b1 = Some (b2, delta) ->
          ~ Plt b1 (nextblock_high j1) /\
          ~ Plt b2 (nextblock_low j1)        
    }.

Hint Resolve simrel_inject_acc_carrier.

Local Instance simrel_inject_acc_refl: Reflexive simrel_inject_acc.
Proof.
  red. intro j.
  constructor; auto using Ple_refl; congruence.
Qed.

Local Instance simrel_inject_acc_trans: Transitive simrel_inject_acc.
Proof.
  red. intros j1 j2 j3.
  inversion 1.
  inversion 1.
  constructor; eauto using Values.inject_incr_trans, Ple_trans.
  intros b1 b2 delta H1 H2.
  destruct (j2 b1) as [[ b12 ? ] | ]  eqn:J2.
  {
    exploit simrel_inject_acc_separated0; eauto.
    specialize (simrel_inject_acc_carrier1 _ _ _ J2).
    replace b12 with b2 in * by congruence.
    xomega.
  }
  exploit simrel_inject_acc_separated1; eauto.
  xomega.
Qed.

Global Instance simrel_inject_world_preserves_globals_incr:
  Monotonic
    Events.meminj_preserves_globals
    (forallr -, forallr -, - ==> simrel_inject_acc ++> impl).
Proof.
  repeat red.
  intros v v0 a x y H H0.
  unfold Events.meminj_preserves_globals in H0.
  destruct H0 as (DOMAIN1 & DOMAIN2 & IMAGE).
  split; [|split].
  {
    intros id b H1.
    apply H.
    eauto.
  }
  {
    intros id b H1.
    apply H.
    eauto.
  }
  {
    intros b1 b2 delta gv H0 H1.
    destruct (x b1) as [ [ ? ? ] | ] eqn:X.
    {
      erewrite ((H: Values.inject_incr _ _) _ _ _ X) in H1; eauto.
      inversion H1; clear H1; subst.
      eauto.
    }
    exploit simrel_inject_acc_separated; eauto.
    destruct 1.
    exploit DOMAIN2; eauto.
    intros H4.
    clear H1.
    exploit simrel_inject_meminj_valid; eauto.
    tauto.
  }
Qed.


Section INJECT_SIMREL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Record simrel_inject_match_mem j (m1 m2: mwd D) :=
    {
      simrel_inject_match_mem_base :> Mem.inject (simrel_inject_meminj j) m1 m2;
      nextblock_high_match: nextblock_high j = Mem.nextblock m1;
      nextblock_low_match: nextblock_low j = Mem.nextblock m2
    }.

  Hint Resolve simrel_inject_match_mem_base.

  Lemma simrel_inject_acc_inject_separated j1 m1 m2 j2:
    simrel_inject_match_mem j1 m1 m2 ->
    simrel_inject_acc j1 j2 ->
    Events.inject_separated j1 j2 m1 m2.
  Proof.
    inversion 1.
    inversion 1.
    red.
    unfold Mem.valid_block.
    rewrite <- nextblock_high_match0.
    rewrite <- nextblock_low_match0.
    assumption.
  Qed.

  Lemma inject_separated_inject_incr j1 m1 m2 j2 m1_ m2_:
    simrel_inject_match_mem j1 m1 m2 ->
    Values.inject_incr j1 j2 ->
    Events.inject_separated j1 j2 m1 m2 ->
    Mem.inject j2 m1_ m2_ ->
    (forall b, Mem.valid_block m1 b -> Mem.valid_block m1_ b) ->
    (forall b, Mem.valid_block m2 b -> Mem.valid_block m2_ b) ->
    { j3: simrel_inject_world | j2 = j3 /\
                   simrel_inject_match_mem j3 m1_ m2_ /\
                   simrel_inject_acc j1 j3
    }.
  Proof.
    intros H H0 H1 H2 H3 H4.
    inversion H.
    apply Ple_lub in H3.
    apply Ple_lub in H4.
    unfold Events.inject_separated in H1.
    unfold Mem.valid_block in H1.
    eexists {| simrel_inject_meminj := _ |}; simpl.
    split.
    { reflexivity. }
    split; econstructor; simpl; eauto; try congruence.
    rewrite nextblock_low_match0.
    rewrite nextblock_high_match0.
    assumption.
  Grab Existential Variables.
    {
      intros b H5.
      apply (simrel_inject_globals j1) in H5.
      eauto.
    }
    {
      intros b1 b2 o H5.
      split.
      {
        eapply Mem.valid_block_inject_1; eauto.
      }
      eapply Mem.valid_block_inject_2; eauto.
    }
  Qed.

  Lemma inject_same_nextblock j m1 m2 m1_ m2_:
    simrel_inject_match_mem j m1 m2 ->
    Mem.inject j m1_ m2_ ->
    Mem.nextblock m1_ = Mem.nextblock m1 ->
    Mem.nextblock m2_ = Mem.nextblock m2 ->
    simrel_inject_match_mem j m1_ m2_.
  Proof.
    inversion 1.
    intros H0 H1 H2.
    constructor; congruence.
  Qed.

  Lemma simrel_inject_exists ge (j: Values.meminj) m1 m2:
    stencil_matches ge ->
    (forall id b, Senv.find_symbol ge id = Some b -> j b = Some (b, 0)) ->
    Mem.inject j m1 m2 ->
    { j_ | simrel_inject_match_mem j_ m1 m2 /\
           j = j_ }.
  Proof.
    intros H H0 H1.
    eexists {| simrel_inject_meminj := _ |}.
    split; simpl; eauto.
    econstructor; simpl; eauto.
  Grab Existential Variables.
    {
      intros b H2.
      apply block_is_global_find_symbol in H2.
      destruct H2 as [i Hi].
      eapply H0.
      erewrite stencil_matches_find_symbol by eauto.
      eassumption.
    }
    {
      split.
      {
        eapply Mem.valid_block_inject_1; eauto.
      } 
      eapply Mem.valid_block_inject_2; eauto.
    }
  Qed.


  Definition simrel_inject_ops :=
    {|
      simrel_world := simrel_inject_world;
      simrel_acc := {| Structures.le := simrel_inject_acc |};
      simrel_undef_matches_values_bool := true;
      simrel_undef_matches_block p b := True;
      simrel_new_glbl := nil;
      simrel_meminj p := p;
      match_mem := simrel_inject_match_mem
    |}.
  
  Require Import ExtensionalityAxioms.

  Lemma match_val_simrel_inject:
    match_val simrel_inject_ops = Val.inject.
  Proof.
    eapply functional_extensionality; intro p.
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext.
    split.
    - destruct 1; simpl in *; subst; try constructor.
      inversion H; subst.
      econstructor; eauto.
    - destruct 1; try constructor.
      + subst.
        constructor.
        assumption.
      + destruct v; constructor; constructor.
  Qed.

  Lemma match_memval_simrel_inject:
    match_memval simrel_inject_ops = memval_inject.
  Proof.
    eapply functional_extensionality; intro p.
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext.
    split.
    - destruct 1; simpl in *; subst; try constructor.
      rewrite match_val_simrel_inject in H.
      assumption.
    - destruct 1.
      + constructor.
      + subst.
        constructor.
        rewrite match_val_simrel_inject.
        assumption.
      + destruct mv; constructor; try constructor.
        rewrite match_val_simrel_inject.
        constructor.
  Qed.

  Theorem free_parallel_inject:
    forall f (m1 m2: mwd D) b b' lo hi m1' delta,
      Mem.inject f m1 m2 ->
      f b = Some (b', delta) ->
      Mem.free m1 b lo hi = Some m1' ->
      exists m2',
        Mem.free m2 b' (lo + delta) (hi + delta)  = Some m2'
        /\ Mem.inject f m1' m2'.
  Proof.
    intros until delta.
    intros MEM_INJ BLOCK_INJ FREE_SRC.
    generalize (Mem.free_range_perm _ _ _ _ _ FREE_SRC). intro PERM_SRC.
    generalize (Mem.range_perm_inject _ _ _ _ _ _ _ _ _ _ BLOCK_INJ MEM_INJ PERM_SRC). intro PERM_TGT.
    destruct (Mem.range_perm_free _ _ _ _ PERM_TGT) as [? FREE_TGT].      
    rewrite FREE_TGT.
    esplit. split.
    reflexivity.
    eapply Mem.free_right_inject.
    eapply Mem.free_left_inject.
    eassumption.
    eassumption.
    eassumption.
    intros b1 delta1 ofs1 k1 p1 BLOCK_INJ1 PERM1 RANGE1.
    destruct (peq b1 b).
    subst.
    replace delta1 with delta in * by congruence.
    eapply (Mem.perm_free_2 (mem := mwd D)). eexact FREE_SRC. 2: eassumption. omega.
    eapply Mem.perm_free_3 in PERM1; eauto.
    exploit (Mem.inject_no_overlap (mem := mwd D)).
    eexact MEM_INJ.
    eassumption.
    eassumption.
    eassumption.
    eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
    eapply Mem.perm_max. eapply Mem.perm_implies. eapply PERM_SRC. instantiate (1 := ofs1 + delta1 - delta). 
    omega. constructor.
    intros; elim H; intros; apply H0; trivial.
    xomega.
  Qed.

  (** For the initial memory, we cannot use SimrelInitMem, because in
      between the construction of an initial memory, no memory
      injection can be proven. However, CompCert proves that an
      initial memory always injects into itself. On the other hand, we
      prove that simrel_program_rel introduces memory extensions
      between initial memory states, so we can compose this extension
      with the self-injection of initial memory states to obtain
      memory injection. Thus, we need: *)

  Require SimrelLessdef.
  Require InitMem.

  (** Relation with inject_neutral for the initial memory state. *)

  Lemma neutral_inject m:
    Mem.inject_neutral (Mem.nextblock m) m ->
    (forall b, block_is_global b -> Mem.valid_block m b) ->
    {j | simrel_inject_match_mem j m m /\
         Mem.flat_inj (Mem.nextblock m) = j
    }.
  Proof.
    intros H H0.
    apply Mem.neutral_inject in H.
    eexists {| simrel_inject_meminj := _ |}; simpl.
    split; [ | reflexivity ].
    econstructor; simpl; eauto.
  Grab Existential Variables.
    {
    intros b H1.
    unfold Mem.valid_block in H0.
    apply H0 in H1.
    unfold Mem.flat_inj.
    destruct (plt b (Mem.nextblock m)); tauto.
    }
    {
      intros b1 b2 o H1.
      unfold Mem.flat_inj in H1.
      destruct (plt b1 (Mem.nextblock m)); try discriminate.
      inversion H1; subst; auto.
    }      
  Qed.

  Global Instance simrel_inject_prf:
    SimulationRelation simrel_inject_ops.
  Proof.
    assert (Heqsub: forall A B, subrel (@eqrel A B) (@subrel A B)).
    {
      intros A B x y H.
      repeat red in H.
      tauto.
    }
    constructor.

    (** Compatibility with order *)
    - constructor; typeclasses eauto.
    - constructor.
    - repeat red.
      intros x y H a.
      simpl.
      destruct (x a) as [ [ ] | ] eqn:EQ; try now constructor.
      apply H in EQ.
      rewrite EQ.
      reflexivity.
 
    (** Properties of [simrel_meminj] *)
    - constructor.
    - constructor.
    - simpl; trivial.
    - simpl; trivial.
    - simpl; trivial.
    - exact simrel_inject_globals.

    (** [Genv.init_mem] *)
    - intros F V p1 p2 Hp.
      generalize Hp. intro Hp' .
      apply genv_globalenv_rel in Hp.
      generalize Hp. intro Hp2.
      apply genv_le_stencil_matches_l in Hp.
      apply genv_le_stencil_matches_r in Hp2.
      apply (simrel_init_mem (D1:=D) (D2:=D) (SimulationRelation := SimrelLessdef.simrel_lessdef_prf)) in Hp'.
      inversion Hp' ; clear Hp' ; subst; try now constructor.
      match goal with
        K: (rexists w: simrel_world SimrelLessdef.simrel_lessdef_ops, match_mem _ w)%rel ?x ?y |- _ =>
        destruct K as [w Hm];
          rename x into m1;
          rename y into m2
      end.
      simpl in Hm.
      assert (Mem.nextblock m1 = glob_threshold) as NEXT1.
      {
        apply stencil_matches_genv_next in Hp.
        rewrite <- Hp.
        symmetry.
        apply Genv.init_mem_genv_next.
        congruence.
      }
      assert (Mem.nextblock m2 = glob_threshold) as NEXT2.
      {
        apply stencil_matches_genv_next in Hp2.
        rewrite <- Hp2.
        symmetry.
        apply Genv.init_mem_genv_next.
        congruence.
      }
      assert (Mem.inject_neutral (Mem.nextblock m1) m1) as INJ.
      {
        eapply InitMem.Genv.initmem_inject_neutral.
        symmetry.
        eassumption.
      }
      apply neutral_inject in INJ.
      {
        destruct INJ as (j & INJ & Hj).
        constructor.
        exists j.
        inversion INJ.
        constructor; try congruence.
        eapply Mem.inject_extends_compose; eauto.
      }
      intros b Hb.
      apply block_is_global_find_symbol in Hb.
      destruct Hb as (i & Hi).
      erewrite <- stencil_matches_symbols in Hi by eexact Hp.
      apply Genv.genv_symb_range in Hi.
      erewrite (Genv.init_mem_genv_next (mem := mwd D)) in Hi by (symmetry; eassumption).
      assumption.

    (** [Mem.alloc] *)
    - repeat red.
      intros p x y H a a0.
      destruct (Mem.alloc x _ _) eqn:Halloc1.
      edestruct (Mem.alloc_parallel_inject (mem := mwd D)) as (j2 & ? & ? & Halloc2 & INJ & INCR & J & ?); try eassumption; try reflexivity; eauto.
      edestruct inject_separated_inject_incr as  (j3 & ? & INJ_ & INCR_); eauto using (Mem.valid_block_alloc (mem := mwd D)).
      {
        red.
        intros b1 b2 delta H1 H2.
        destruct (peq b1 b) as [ | NE ].
        {
          subst.
          rewrite J in H2. inversion H2; clear H2; subst.
          eauto using (Mem.fresh_block_alloc (mem := mwd D)).
        }
        apply H0 in NE.
        congruence.
      }
      subst j2.
      rewrite Halloc2.
      econstructor; eauto.
      split; simpl; eauto.
      split; eauto.

    (** [Mem.free] *)
    - repeat red.
      simpl.
      intros p x y H x0 y0 H0.
      inversion H0; subst.
      inversion H1; subst.
      simpl.
      destruct (Mem.free x _ _ _) eqn:Hfree1; try constructor.
      edestruct free_parallel_inject as (? & Hfree2 & INJ); eauto.
      replace (ofs1 + delta + sz) with (ofs1 + sz + delta) by omega.
      rewrite Hfree2.
      constructor.
      exists p.
      split; try reflexivity.
      eapply inject_same_nextblock; eauto using (Mem.nextblock_free (mem := mwd D)).

    (** [Mem.load] *)
    - rewrite match_val_simrel_inject.
      repeat red.
      simpl.
      intros p a x y H x0 y0 H0.
      inversion H0; subst.
      simpl.
      destruct (Mem.load _ x _ _) eqn:Hload; try constructor.
      edestruct (Mem.load_inject (mem := mwd D)) as (? & Hload2 & ?); eauto.
      simpl in * |- * .
      rewrite Hload2.
      constructor; assumption.

    (** [Mem.store] *)
    - rewrite match_val_simrel_inject.
      repeat red.
      simpl.
      intros p a x y H x0 y0 H0 x1 y1 H1.
      inversion H0; subst.
      simpl.
      destruct (Mem.store _ x _ _ _) eqn:Hstore1; try constructor.
      simpl in * |- * .
      edestruct (Mem.store_mapped_inject (mem := mwd D)) as (? & Hstore2 & ?); eauto.
      rewrite Hstore2.
      constructor.
      exists p.
      split; try reflexivity.
      eapply inject_same_nextblock; eauto using (Mem.nextblock_store (mem := mwd D)).

    (** [Mem.loadbytes] *)
    - rewrite match_memval_simrel_inject.
      repeat red.
      simpl.
      intros p x y H x0 y0 H0 a.
      inversion H0; subst.
      simpl.
      destruct (Mem.loadbytes x _ _ _) eqn:Hlb1; try constructor.
      edestruct (Mem.loadbytes_inject (mem := mwd D)) as (? & Hlb2 & ?); eauto.
      rewrite Hlb2.
      constructor.
      rewrite <- CompcertStructures.list_forall2_list_rel; assumption.

    (** [Mem.storebytes] *)
    - rewrite match_memval_simrel_inject.
      simpl.
      repeat red.
      intros p x y H x0 y0 H0 x1 y1 H1.
      inversion H0; subst.
      simpl.
      destruct (Mem.storebytes x _ _ _) eqn:Hsb1; try constructor.
      edestruct (Mem.storebytes_mapped_inject (mem := mwd D)) as (? & Hsb2 & ?); eauto.
      { rewrite CompcertStructures.list_forall2_list_rel; eassumption. }
      rewrite Hsb2.
      constructor.
      exists p.
      split; try reflexivity.
      eapply inject_same_nextblock; eauto using (Mem.nextblock_storebytes (mem := mwd D)).

    (** [Mem.perm] *)
    - repeat red.
      intros p x y H x0 y0 H0 a a0 H1.
      inversion H0; subst.
      simpl in * |- * .
      eapply Mem.perm_inject; eauto.

    (** [Mem.valid_block] *)
    - intros p m1 m2 Hm b1 b2 [delta Hb].
      simpl in *.
      split; intro H.
      + eapply Mem.valid_block_inject_2; eauto.
      + eapply Mem.valid_block_inject_1; eauto.

    (** [Mem.different_pointers_inject] *)
    - eauto using (Mem.different_pointers_inject (mem := mwd D)).

    (** [Mem.weak_valid_pointer_inject_val] *)
    - inversion 3; subst.
      eapply Mem.weak_valid_pointer_inject_val; eauto.

    (** [Mem.weak_valid_pointer_address_inject_weak] *)
    - intros p m1 m2 b1 b2 delta H H0.
      inversion H; clear H; subst.
      simpl in H0.
      exists (Ptrofs.unsigned (Ptrofs.repr delta)).
      intros ofs1 H.
      rewrite Ptrofs.add_unsigned.
      apply Ptrofs.unsigned_repr.
      eapply (Mem.weak_valid_pointer_inject_no_overflow (mem := mwd D)); eauto.

    (** [Mem.address_inject] *)
    - intro. 
      eauto using (Mem.address_inject (mem := mwd D)).

    (** [Mem.aligned_area_inject] *)
    - intro.
      eauto using (Mem.aligned_area_inject (mem := mwd D)).

    (** [Mem.disjoint_or_equal_inject] *)
    - intro.
      eauto using (Mem.disjoint_or_equal_inject (mem := mwd D)).
  Qed.

  Definition inj :=
    {|
      simrel_ops := simrel_inject_ops
    |}.

End INJECT_SIMREL.

  (* Internal composition. *)

  Lemma compose_meminj_exists (j1 j2: simrel_inject_world):
    { j: simrel_inject_world | Values.compose_meminj j1 j2 = j /\
                  nextblock_high j = nextblock_high j1 /\
                  nextblock_low j = nextblock_low j2
    }.
  Proof.
    eexists {| simrel_inject_meminj := _ |}; simpl.
    intuition reflexivity.
  Grab Existential Variables.
    {
    intros b H.
    unfold compose_meminj.
    erewrite simrel_inject_globals by eassumption.
    erewrite simrel_inject_globals by eassumption.
    reflexivity.
    }
    {
      unfold compose_meminj.
      intros b1 b2 o H.
      destruct (j1 b1) as [ [ b12 ?] | ] eqn:J1 ; try discriminate.
      destruct (j2 b12) as [ [ ? ? ] | ] eqn:J2 ; try discriminate.
      inversion H; subst.
      apply simrel_inject_meminj_valid in J1.
      apply simrel_inject_meminj_valid in J2.
      intuition congruence.
    }
  Qed.

  Definition compose_meminj j1 j2 :=
    let (j, _) := compose_meminj_exists j1 j2 in j.

  Lemma compose_meminj_correct_strong (j1 j2: simrel_inject_world):
    Values.compose_meminj j1 j2 = compose_meminj j1 j2 /\
    nextblock_high (compose_meminj j1 j2) = nextblock_high j1 /\
    nextblock_low (compose_meminj j1 j2) = nextblock_low j2.
  Proof.
    unfold compose_meminj.
    destruct compose_meminj_exists.
    assumption.
  Qed.

  Lemma compose_meminj_correct (j1 j2: simrel_inject_world):
    Values.compose_meminj j1 j2 = compose_meminj j1 j2.
  Proof.
    apply compose_meminj_correct_strong.
  Qed.

(* # The following is wrong due to inject_separated.
  Global Instance compose_meminj_incr:
    Proper
      (simrel_inject_acc ++>
       simrel_inject_acc ++>
       simrel_inject_acc)
      compose_meminj.
   # However, we have the following weaker form,
   # which is true because nextblock_low j12 = nextblock_high j23.
 *)

Section INJECT_COMPOSE.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Lemma compose_meminj_incr j12 j23 (m1 m2 m3: mwd D) j12_ j23_ (m1_ m2_ m3_: mwd D):
    simrel_inject_match_mem j12 m1 m2 ->
    simrel_inject_match_mem j23 m2 m3 ->
    simrel_inject_match_mem j12_ m1_ m2_ ->
    simrel_inject_match_mem j23_ m2_ m3_ ->
    simrel_inject_acc j12 j12_ ->
    simrel_inject_acc j23 j23_ ->
    simrel_inject_acc (compose_meminj j12 j23) (compose_meminj j12_ j23_).        
  Proof.
    intros H H0 H1 H2 H3 H4.
    inversion H.
    inversion H0.
    inversion H1.
    inversion H2.
    inversion H3.
    inversion H4.
    generalize (compose_meminj_correct_strong j12 j23). intros (EQ & ? & ?).
    generalize (compose_meminj_correct_strong j12_ j23_). intros (EQ_ & ? & ?).
    constructor; try congruence.
    {
      red.
      intros b1 b3 delta.
      rewrite <- EQ.
      rewrite <- EQ_.
      unfold Values.compose_meminj.
      destruct (j12 b1) as [ [ b2 ? ] | ] eqn:X; try discriminate.
      rewrite (simrel_inject_acc_carrier0 _ _ _ X).
      destruct (j23 b2) as [ [ ? ? ] | ] eqn:Y; try discriminate.
      rewrite (simrel_inject_acc_carrier1 _ _ _ Y).
      tauto.
    }
    intros b1 b3_ delta.
    rewrite <- EQ.
    rewrite <- EQ_.
    unfold Values.compose_meminj.
    destruct (j12 b1) as [ [ b2 ? ] | ] eqn:X.
    {
      rewrite (simrel_inject_acc_carrier0 _ _ _ X).
      destruct (j23 b2) as [ [ ? ? ] | ] eqn:Y; try discriminate.
      destruct (j23_ b2) as [ [ ? ? ] | ] eqn:Z; try discriminate.
      inversion 2; subst.
      exploit simrel_inject_acc_separated1; eauto.      
      eapply (Mem.valid_block_inject_2 (mem := mwd D)) in X; eauto.
      unfold Mem.valid_block in X.
      intuition congruence.
    }
    destruct (j12_ b1) as [ [ b2 ? ] | ] eqn:Y; try discriminate.
    destruct (j23_ b2) as [ [ ? ? ] | ] eqn:Z; try discriminate.
    inversion 2; subst.
    exploit simrel_inject_acc_separated0; eauto.
    clear X.
    destruct 1.
    destruct (j23 b2) as [ [ b3 ? ] | ] eqn:NONE.
    {
      eapply (Mem.valid_block_inject_1 (mem := mwd D)) in NONE; eauto.
      unfold Mem.valid_block in NONE.
      congruence.
    }
    exploit simrel_inject_acc_separated1; eauto.
    intuition congruence.
  Qed.

  Lemma inject_compose p12 p23 (m1 m2 m3: mwd D):
    simrel_inject_match_mem p12 m1 m2 ->
    simrel_inject_match_mem p23 m2 m3 ->
    simrel_inject_match_mem (compose_meminj p12 p23) m1 m3.
  Proof.
    intros H H0.
    inversion H.
    inversion H0.
    generalize (compose_meminj_correct_strong p12 p23).
    intros (EQ & ? & ?).
    constructor; try congruence.
    rewrite <- EQ.
    eapply Mem.inject_compose; eauto.
  Qed.


  (* Relation with inject_neutral, to connect the CompCert caller's
     memory state with the target memory state via simulation. *)

  Lemma flat_inj_compose (m1 m2: mwd D) j1 j2:
    simrel_inject_match_mem j1 m1 m1 ->
    Mem.flat_inj (Mem.nextblock m1) = j1 ->
    simrel_inject_match_mem j2 m1 m2 ->
    compose_meminj j1 j2 = j2.
  Proof.
    intros H H0 H1.
    inversion H.
    inversion H1.
    generalize (compose_meminj_correct_strong j1 j2).
    intros (EQ & ? & ?).
    apply simrel_inject_world_eq; try congruence.
    rewrite <- EQ.
    apply functional_extensionality.
    intro b.
    unfold Values.compose_meminj.
    rewrite <- H0.
    unfold Mem.flat_inj.
    destruct (plt b (Mem.nextblock m1)) as [ | INVAL ].
    {
      destruct (j2 b) as [ [ ? ? ] | ] ; simpl; auto.
    }
    symmetry.
    destruct (j2 b) as [ [ ? ? ] | ] eqn:J2; auto.
    destruct INVAL.
    eapply Mem.valid_block_inject_1; eauto.
  Qed.

  (** XXX: it's not clear that this is used, but in any case it's
    broken at them moment. *)
  (*
  Lemma flat_inj_preserves_globals m:
    (forall b, block_is_global b -> Mem.valid_block m b) ->
    forall {F V: Type} (ge: Globalenvs.Genv.t F V),
      stencil_matches ge ->
      Events.meminj_preserves_globals ge (Mem.flat_inj (Mem.nextblock m)).
  Proof.
    intros H0 F V ge H1.
    red.
    split.
    {
      intros b H2.
      unfold Mem.flat_inj.
      destruct (plt b (Mem.nextblock m)) as [ | NE ]; auto.
      destruct NE.
      apply H0.
      erewrite stencil_matches_genv_next in H2; eauto.
      assumption.
    }
    intros b1 b2 delta H2 H3.
    unfold Mem.flat_inj in H3.
    destruct (plt b1 (Mem.nextblock m)); congruence.    
  Qed.
   *)

End INJECT_COMPOSE.


(** * Wrap [simrel_inject] into a stronger version, for [ec_mem_inject] *)

Section STRONG_INJECT.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Record strong_inject_world: Type :=
    mk_strong_inject_world
      {
        strong_inject_meminj: simrel_inject_world;
        strong_inject_high: mwd D;
        strong_inject_low: mwd D;
        strong_inject_prop: simrel_inject_match_mem strong_inject_meminj strong_inject_high strong_inject_low
      }.

  Lemma strong_inject_world_eq mm1 mm2:
    strong_inject_meminj mm1 = strong_inject_meminj mm2 ->
    strong_inject_high mm1 = strong_inject_high mm2 ->
    strong_inject_low mm1 = strong_inject_low mm2 ->
    mm1 = mm2.
  Proof.
    intros H H0 H1.
    destruct mm1; destruct mm2; simpl in * |- * ; subst.
    f_equal;
      apply ProofIrrelevance.proof_irrelevance.
  Qed.

  Definition strong_inject (mm: strong_inject_world) (m m': mwd D): Prop :=
    m = strong_inject_high mm /\
    m' = strong_inject_low mm.

  Lemma strong_inject_intro' j m m' :
    simrel_inject_match_mem j m m' ->
    {
      mm | strong_inject mm m m' /\
           strong_inject_meminj mm = j
    }.
  Proof.
    intros H.
    exists (mk_strong_inject_world _ _ _ H).
    simpl.
    split; auto.
    split; auto.
  Qed.

  Lemma strong_inject_intro ge (j: Values.meminj) m1 m2:
    stencil_matches ge ->
    (forall id b, Senv.find_symbol ge id = Some b -> j b = Some (b, 0)) ->
    Mem.inject j m1 m2 ->
    { j_ | strong_inject j_ m1 m2 /\
           j = strong_inject_meminj j_ }.
  Proof.
    intros H H0 H1.
    generalize (simrel_inject_exists _ _ _ _  H H0 H1).
    destruct 1 as (j_ & INJ & EQ).
    subst.
    destruct (strong_inject_intro' _ _ _ INJ) as (? & ? & EQ).
    symmetry in EQ.
    esplit.
    split; eauto.
    (* coercion *) f_equal; eauto.
  Qed.

  Lemma strong_inject_elim' mm m m':
    strong_inject mm m m' ->
    simrel_inject_match_mem (strong_inject_meminj mm) m m'.
  Proof.
    destruct 1; subst.
    destruct mm; auto.
  Qed.

  Hint Resolve simrel_inject_match_mem_base strong_inject_elim' .

  Record strong_inject_acc (mm1 mm2: strong_inject_world): Prop :=
    strong_inject_acc_intro'
    {
      strong_inject_acc_elim' : simrel_inject_acc (strong_inject_meminj mm1) (strong_inject_meminj mm2);
      strong_inject_acc_unmapped: Mem.unchanged_on (Events.loc_unmapped (strong_inject_meminj mm1)) (strong_inject_high mm1) (strong_inject_high mm2);
      strong_inject_acc_out_of_reach: Mem.unchanged_on (Events.loc_out_of_reach (strong_inject_meminj mm1) (strong_inject_high mm1)) (strong_inject_low mm1) (strong_inject_low mm2);
      (* the following is necessary for the transitivity of Mem.unchanged_on *)
      strong_inject_acc_max_perm:
        forall b o p,
          Mem.valid_block (strong_inject_high mm1) b ->
          Mem.perm (strong_inject_high mm2) b o Max p ->
          Mem.perm (strong_inject_high mm1) b o Max p
    }.

  Local Instance strong_inject_acc_refl: Reflexive strong_inject_acc.
  Proof.
    constructor; try reflexivity; auto using (Mem.unchanged_on_refl (mem := mwd D)).
  Qed.

  Local Instance strong_inject_acc_trans: Transitive strong_inject_acc.
  Proof.
    red.
    intros x y z H H0.
    inversion H; subst.
    inversion H0; subst.
    constructor.
    + etransitivity; eauto.
    + eapply Mem.unchanged_on_trans_strong with (Q := Events.loc_unmapped (strong_inject_meminj y)); eauto.
      unfold Events.loc_unmapped.
      intros b H1 o H2.
      destruct ((strong_inject_meminj y) b) as [ [ ] | ] eqn:INJ ; auto.
      exfalso.
      exploit (simrel_inject_acc_separated (strong_inject_meminj x) (strong_inject_meminj y)); eauto.
      erewrite nextblock_high_match by apply strong_inject_prop.
      revert H1. clear. tauto.
    + eapply Mem.unchanged_on_trans_strong with (Q := Events.loc_out_of_reach (strong_inject_meminj y) (strong_inject_high y)); eauto.
      unfold Events.loc_out_of_reach.
      intros b H1 o H2 b0 delta H3.
      destruct ((strong_inject_meminj x) b0) as [ [ ] | ] eqn:INJ.
      - generalize INJ. intro INJ_.
        apply strong_inject_acc_elim'0 in INJ_.
        rewrite INJ_ in H3.
        inversion H3; clear H3; subst.
        intro ABSURD.
        eapply H2; eauto.
        eapply strong_inject_acc_max_perm0; eauto.
        clear INJ_.
        eapply Mem.valid_block_inject_1; eauto using strong_inject_prop.
      - intros _.
        exploit (simrel_inject_acc_separated (strong_inject_meminj x) (strong_inject_meminj y)); eauto.
        erewrite nextblock_low_match by apply strong_inject_prop.
        revert H1. clear. tauto.
    + intros b o p H1 H2.
      eapply strong_inject_acc_max_perm0; eauto.
      eapply strong_inject_acc_max_perm1; eauto.
      generalize (nextblock_high_le _ _ (strong_inject_acc_elim' _ _ H)).
      repeat erewrite nextblock_high_match by apply strong_inject_prop.
      unfold Mem.valid_block in *.
      xomega.
  Qed.

  Lemma strong_inject_acc_intro mm1 m1 m'1 (j2: Values.meminj) m2 m'2:
    strong_inject mm1 m1 m'1 ->
    Values.inject_incr (strong_inject_meminj mm1) j2 ->
    Events.inject_separated (strong_inject_meminj mm1) j2 m1 m'1 ->
    Mem.inject j2 m2 m'2 ->
    (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
    (forall b, Mem.valid_block m'1 b -> Mem.valid_block m'2 b) ->
    Mem.unchanged_on (Events.loc_unmapped (strong_inject_meminj mm1)) m1 m2 ->
    Mem.unchanged_on (Events.loc_out_of_reach (strong_inject_meminj mm1) m1) m'1 m'2 ->
    (forall b o p,
       Mem.valid_block m1 b ->
       Mem.perm m2 b o Max p ->
       Mem.perm m1 b o Max p) ->
    { mm2 |
      j2 = strong_inject_meminj mm2 /\
      strong_inject mm2 m2 m'2 /\
      strong_inject_acc mm1 mm2 }.
  Proof.
    intros H H0 H1 H2 H3 H4 H5 H6 H7.
    inversion H; subst.
    generalize (inject_separated_inject_incr _ _ _ _ _ _ (strong_inject_prop mm1) H0 H1 H2 H3 H4).
    destruct 1 as (j2_ & ? & INJ & INCR); subst.
    apply strong_inject_intro' in INJ.
    destruct INJ as (mm2 & INJ & ?); subst.
    esplit.
    split; eauto.
    split; auto.
    inversion INJ; subst.
    constructor; auto.
  Qed.

  Lemma strong_inject_acc_elim mm1 m1 m'1 mm2 m2 m'2:
    strong_inject mm1 m1 m'1 ->
    strong_inject mm2 m2 m'2 ->
    strong_inject_acc mm1 mm2 ->
    Values.inject_incr (strong_inject_meminj mm1) (strong_inject_meminj mm2) /\
    Events.inject_separated (strong_inject_meminj mm1) (strong_inject_meminj mm2) m1 m'1 /\
    (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b) /\
    (forall b, Mem.valid_block m'1 b -> Mem.valid_block m'2 b) /\
    Mem.unchanged_on (Events.loc_unmapped (strong_inject_meminj mm1)) m1 m2 /\
    Mem.unchanged_on (Events.loc_out_of_reach (strong_inject_meminj mm1) m1) m'1 m'2 /\
    (forall b o p,
       Mem.valid_block m1 b ->
       Mem.perm m2 b o Max p ->
       Mem.perm m1 b o Max p).
  Proof.
    intros H H0 H1.
    inversion H; subst.
    inversion H0; subst.
    inversion H1; subst.
    inversion strong_inject_acc_elim'0; subst.
    split; auto.
    split.
    { eapply simrel_inject_acc_inject_separated; eauto. }
    repeat erewrite nextblock_low_match in nextblock_low_le0 by apply strong_inject_prop.
    repeat erewrite nextblock_high_match in nextblock_high_le0 by apply strong_inject_prop.
    split.
    { unfold Mem.valid_block. intro. xomega. }
    split; auto.
    unfold Mem.valid_block. intro. xomega.
  Qed.

  Definition simrel_strong_inject_ops :=
    {|
      simrel_world := strong_inject_world;
      simrel_acc := {| Structures.le := strong_inject_acc |};
      simrel_undef_matches_values_bool := true;
      simrel_undef_matches_block p b := True;
      simrel_new_glbl := nil;
      simrel_meminj := strong_inject_meminj;
      match_mem := strong_inject
    |}.

  Lemma match_ptr_strong_inject'  p:
    match_ptr simrel_strong_inject_ops p =
    match_ptr (simrel_inject_ops (D:=D)) (strong_inject_meminj p).
  Proof.
    eapply functional_extensionality; intros [b1 o1].
    eapply functional_extensionality; intros [b2 o2].
    eapply prop_ext.
    split; inversion 1; subst; constructor; auto.
  Qed.

  Lemma match_ptrbits_strong_inject'  p:
    match_ptrbits simrel_strong_inject_ops p =
    match_ptrbits (simrel_inject_ops (D:=D)) (strong_inject_meminj p).
  Proof.
    eapply functional_extensionality; intros [b1 o1].
    eapply functional_extensionality; intros [b2 o2].
    eapply prop_ext.
    split; inversion 1; subst; constructor; auto.
  Qed.

  Lemma match_block_strong_inject'  p:
    match_block simrel_strong_inject_ops p =
    match_block (simrel_inject_ops (D:=D)) (strong_inject_meminj p).
  Proof.
    reflexivity.
  Qed.

  Lemma match_val_strong_inject' p:
    match_val simrel_strong_inject_ops p =
    match_val (simrel_inject_ops (D:=D)) (strong_inject_meminj p).
  Proof.
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext.
    split; inversion 1; subst; constructor; eauto.
    + rewrite <- match_ptrbits_strong_inject'. assumption.
    + rewrite -> match_ptrbits_strong_inject'. assumption.
  Qed.

  Lemma match_val_strong_inject p:
    match_val simrel_strong_inject_ops p =
    Val.inject (strong_inject_meminj p).
  Proof.
    rewrite match_val_strong_inject'.
    rewrite match_val_simrel_inject.
    reflexivity.
  Qed.

  Lemma match_memval_strong_inject' p:
    match_memval simrel_strong_inject_ops p =
    match_memval (simrel_inject_ops (D:=D)) (strong_inject_meminj p).
  Proof.
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext.
    split; inversion 1; subst; constructor;
    rewrite ?match_val_strong_inject' in *; eauto.
  Qed.

  Lemma match_memval_strong_inject p:
    match_memval simrel_strong_inject_ops p =
    memval_inject (strong_inject_meminj p).
  Proof.
    rewrite match_memval_strong_inject'.
    rewrite match_memval_simrel_inject.
    reflexivity.
  Qed.

  Global Instance simrel_strong_inject_prf:
    SimulationRelation simrel_strong_inject_ops.
  Proof.
    assert (Heqsub: forall A B, subrel (@eqrel A B) (@subrel A B)).
    {
      intros A B x y H.
      repeat red in H.
      tauto.
    }
    constructor.

    (** Compatibility with order *)
    - constructor; typeclasses eauto.
    - simpl.
      solve_monotonic.
    - repeat red.
      intros x y H a.
      simpl.
      destruct ((strong_inject_meminj x) a) as [ [ ] | ] eqn:EQ; try now constructor.
      apply H in EQ.
      rewrite EQ.
      reflexivity.

    (** Properties of [simrel_meminj] *)
    - constructor.
    - constructor.
    - simpl; trivial.
    - simpl; trivial.
    - simpl; trivial.
    - intro. apply simrel_inject_globals.

    (** [Genv.init_mem]: reuse the proof of simrel_inject *)
    - intros F V p1 p2 Hp.
      apply (simrel_init_mem (D1:=D) (D2:=D) (SimulationRelation := simrel_inject_prf)) in Hp.
      inversion Hp ; clear Hp ; subst; try now constructor.
      match goal with
        K: (rexists w: simrel_world simrel_inject_ops, match_mem _ w)%rel ?x ?y |- _ =>
        destruct K as [w Hm];
          rename x into m1;
          rename y into m2
      end.
      apply strong_inject_intro' in Hm.
      destruct Hm as (j & INJ & Hj).
      subst.
      constructor.
      exists j.
      assumption.

    (** [Mem.alloc]: redo the proof, because of stronger [le] *)
    - repeat red.
      intros p x y H a a0.
      destruct (Mem.alloc x _ _) eqn:Halloc1.
      edestruct (Mem.alloc_parallel_inject (mem := mwd D)) as (j2 & ? & ? & Halloc2 & INJ & INCR & J & ?); try eassumption; try reflexivity; eauto.
      edestruct strong_inject_acc_intro as  (mm2 & ? & INJ_ & INCR_);
      eauto using (Mem.valid_block_alloc (mem := mwd D)).
      + red.
        intros b1 b2 delta H1 H2.
        destruct (peq b1 b) as [ | NE ].
        {
          subst.
          rewrite J in H2. inversion H2; clear H2; subst.
          eauto using (Mem.fresh_block_alloc (mem := mwd D)).
        }
        apply H0 in NE.
        congruence.
      + eapply Mem.alloc_unchanged_on; eauto.
      + eapply Mem.alloc_unchanged_on; eauto.
      + intros.
        eapply Mem.perm_alloc_4; eauto.
        intro; subst.
        eapply (Mem.fresh_block_alloc x); eauto.
      + subst j2.
        rewrite Halloc2.
        econstructor; eauto.
        split; simpl; eauto.
        split; eauto.

    (** [Mem.free]: redo the proof, because of stronger [le] *)
    - simpl.
      intros p x y H x0 y0 H0.
      inversion H0; subst.
      inversion H1; subst.
      simpl.
      destruct (Mem.free x _ _ _) eqn:Hfree1; try now solve_monotonic.
      edestruct (free_parallel_inject (D:=D)) as (? & Hfree2 & INJ); eauto.
      replace (ofs1 + delta + sz) with (ofs1 + sz + delta) by omega.
      rewrite Hfree2.
      edestruct strong_inject_acc_intro as  (mm2 & ? & INJ_ & INCR_);
      eauto using (Mem.valid_block_free_1 (mem := mwd D)).
      + red. intros; congruence.
      + eapply Mem.free_unchanged_on; eauto.
        intros i H2.
        unfold Events.loc_unmapped.
        simpl in *.
        congruence.
      + eapply Mem.free_unchanged_on; eauto.
        intros i H2.
        unfold Events.loc_out_of_reach.
        intro ABSURD.
        eapply ABSURD; eauto.
        apply Mem.perm_cur_max.
        eapply Mem.perm_implies; [ eapply Mem.free_range_perm; eauto; omega | ].
        constructor.
      + eauto using (Mem.perm_free_3 (mem := mwd D)).
      + solve_monotonic.

    (** [Mem.load]: reuse the proof of simrel_inject *)
    - intros p a x y H.
      rewrite match_ptr_strong_inject'.
      rewrite match_val_strong_inject'.
      eapply (simrel_load (R := inj) (strong_inject_meminj p)); eauto.
      apply strong_inject_elim'; auto.

    (** [Mem.store]: redo the proof, because of stronger [le] *)
    - intro p.
      rewrite match_val_strong_inject.
      simpl.
      intros a x y H x0 y0 H0 x1 y1 H1.
      inversion H0; subst.
      simpl.
      destruct (Mem.store _ x _ _ _) eqn:Hstore1; try now solve_monotonic.
      simpl in * |- * .
      edestruct (Mem.store_mapped_inject (mem := mwd D)) as (? & Hstore2 & INJ); eauto.
      rewrite Hstore2.
      edestruct strong_inject_acc_intro as  (mm2 & ? & INJ_ & INCR_);
      eauto using (Mem.store_valid_block_1 (mem := mwd D)).
      + red. intros; congruence.
      + eapply Mem.store_unchanged_on; eauto.
        intros i H3.
        unfold Events.loc_unmapped.
        congruence.
      + eapply Mem.store_unchanged_on; eauto.
        intros i H3.
        unfold Events.loc_out_of_reach.
        intro ABSURD.
        eapply ABSURD; eauto.
        apply Mem.perm_cur_max.
        eapply Mem.perm_implies; [ eapply Mem.store_valid_access_3; eauto; omega | ].
        constructor.
      + eauto using (Mem.perm_store_2 (mem := mwd D)).
      + solve_monotonic.

    (** [Mem.loadbytes]: reuse the proof of simrel_inject *)
    - intros p a x y H.
      rewrite match_ptr_strong_inject'.
      rewrite match_memval_strong_inject'.
      eapply (simrel_loadbytes (R := inj) (strong_inject_meminj p)); eauto.
      apply strong_inject_elim'; auto.

    (** [Mem.storebytes]: redo the proof, because of stronger [le] *)
    - intro p.
      rewrite match_memval_strong_inject.
      simpl.
      intros x y H x0 y0 H0 x1 y1 H1.
      inversion H0; subst.
      simpl.
      destruct (Mem.storebytes x _ _ _) eqn:Hsb1; try now solve_monotonic.
      edestruct (Mem.storebytes_mapped_inject (mem := mwd D)) as (? & Hsb2 & INJ); eauto.
      { rewrite CompcertStructures.list_forall2_list_rel; eassumption. }
      rewrite Hsb2.
      assert (length x1 = length y1) as LEN by solve_monotonic.
      edestruct strong_inject_acc_intro as  (mm2 & ? & INJ_ & INCR_);
      eauto using (Mem.storebytes_valid_block_1 (mem := mwd D)).
      + red. intros; congruence.
      + eapply Mem.storebytes_unchanged_on; eauto.
        unfold Events.loc_unmapped.
        simpl in *.
        intros; congruence.
      + eapply Mem.storebytes_unchanged_on; eauto.
        rewrite <- LEN.
        intros i H3.
        unfold Events.loc_out_of_reach.
        intro ABSURD.
        eapply ABSURD; eauto.
        apply Mem.perm_cur_max.
        eapply Mem.perm_implies; [ eapply Mem.storebytes_range_perm; eauto; omega | ].
        constructor.
      + eauto using (Mem.perm_storebytes_2 (mem := mwd D)).
      + solve_monotonic.

    (** [Mem.perm]: reuse the proof of simrel_inject *)
    - intros p x y H.
      rewrite match_ptr_strong_inject'.
      eapply (simrel_perm (R := inj) (strong_inject_meminj p)); simpl in *; eauto.

    (** [Mem.valid_block]: reuse the proof of simrel_inject *)
    - intros p x y H.
      rewrite match_block_strong_inject'.
      eapply (simrel_valid_block (R := inj) (strong_inject_meminj p)); simpl in *; eauto.

    (** [Mem.different_pointers_inject] *)
    - eauto using (Mem.different_pointers_inject (mem := mwd D)).

    (** [Mem.weak_valid_pointer_inject_val] *)
    - inversion 3; subst.
      eapply Mem.weak_valid_pointer_inject_val; eauto.

    (** [Mem.weak_valid_pointer_address_inject_weak] *)
    - intros p m1 m2 b1 b2 delta H H0.
      exists (Ptrofs.unsigned (Ptrofs.repr delta)).
      intros ofs1 K.
      rewrite Ptrofs.add_unsigned.
      apply Ptrofs.unsigned_repr.
      eapply (Mem.weak_valid_pointer_inject_no_overflow (mem := mwd D)); eauto.

    (** [Mem.address_inject] *)
    - intro.
      eauto using (Mem.address_inject (mem := mwd D)).

    (** [Mem.aligned_area_inject] *)
    - intro.
      eauto using (Mem.aligned_area_inject (mem := mwd D)).

    (** [Mem.disjoint_or_equal_inject] *)
    - intro.
      eauto using (Mem.disjoint_or_equal_inject (mem := mwd D)).
  Qed.

  Definition simrel_strong_inject :=
    {|
      simrel_ops := simrel_strong_inject_ops
    |}.

End STRONG_INJECT.
