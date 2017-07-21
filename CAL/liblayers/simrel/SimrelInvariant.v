Require Import SimrelDefinition.
Require Import SimrelCategory.

(** ** Invariants *)

(** The simulation diagrams by themselves do not require an invariant
  to hold. However, in many places, we need an invariant to hold for
  the simulation to work. To express this requirement, we leverage our
  simulation relation infrastructure by encoding the invariant I(s) as
  a relation {(s, s) | I(s)}, and by showing that this invariant is in
  fact a [SimulationRelation]. This invariant combines [data_inv], and
  inject-neutral properties.

  Equipped with this new relation [inv], we can deploy our simulation
  infrastructure on [inv ∘ R ∘ inv]. Then the derived simulation
  relation keeps track of the invariant for both machines, and the
  simulation of primitive calls can be established as long as the two
  primitives are related by [R], and preserve invariants. *)

Section INVARIANT.
  Context `{Hmem: BaseMemoryModel}.

  (** *** Definition *)

  Definition inv_world :=
    sig (fun x => forall b, block_is_global b -> Pos.lt b x).

  Inductive inv_match_mem D: inv_world -> mwd D -> mwd D -> Prop :=
    inv_match_mem_intro (m: mem) (d: D):
      forall Hinv: data_inv d,
      forall Hnb: forall b, block_is_global b -> Mem.valid_block m b,
      forall Hmwf: Mem.inject_neutral (Mem.nextblock m) m,
      forall Hdwf: data_inject (Mem.flat_inj (Mem.nextblock m)) d d,
        inv_match_mem D (exist _ (Mem.nextblock m) Hnb) (m, d) (m, d).


  Inductive inv_match_mem' D: inv_world -> mwd D -> mwd D -> Prop :=
    inv_match_mem_intro' (m: mem) (d: D):
      forall Hinv: data_inv d,
      forall Hnb: forall b, block_is_global b -> Mem.valid_block m b,
      forall Hmwf: Mem.inject_neutral (Mem.nextblock m) m,
      forall Hdwf: data_inject (Mem.flat_inj (Mem.nextblock m)) d d,
      forall w,
      forall Hw: proj1_sig w = Mem.nextblock m,
        inv_match_mem' D w (m, d) (m, d).

  Lemma imm_eq:
    forall D w m1 m2,
      inv_match_mem' D w m1 m2 ->
      inv_match_mem D w m1 m2.
  Proof.
    inversion 1. subst.
    destruct w. simpl in *. subst. constructor; auto.
  Qed.

  Program Definition inv_ops D: simrel_components D D :=
    {|
      simrel_world := inv_world;
      simrel_acc := {| le := (Pos.le @@ (@proj1_sig _ _))%rel |};
      simrel_new_glbl := nil;
      simrel_undef_matches_values_bool := false;
      simrel_undef_matches_block p b := False;
      match_mem := inv_match_mem D;
      simrel_meminj x := let (b, _) := x in Mem.flat_inj b
    |}.

  Local Instance: forall A P, Measure (@proj1_sig A P).

  (** *** Properties *)

  Global Instance match_mem_inv_eq D p:
    Related (match_mem (inv_ops D) p) eq subrel.
  Proof.
    intros m m' H.
    destruct H.
    reflexivity.
  Qed.

  Global Instance match_val_inv_eq D p:
    Related (match_val (inv_ops D) p) eq subrel.
  Proof.
    intros v1 v2 Hv.
    destruct Hv; try constructor; try now (discriminate H || destruct H).
    inversion  H; subst.
    destruct p.
    simpl in H1.
    unfold Mem.flat_inj in H1.
    destruct plt; try discriminate.
    inversion H1; subst.
    rewrite Ptrofs.add_zero.
    reflexivity.
  Qed.

  Global Instance match_vals_inv_eq D p:
    Related (list_rel (match_val (inv_ops D) p)) eq subrel.
  Proof.
    intros vs1 vs2 Hvs.
    induction Hvs; try constructor.
    f_equal; eauto.
    eapply match_val_inv_eq; eauto.
  Qed.

  Global Instance match_memval_inv_eq D p:
    Related (match_memval (inv_ops D) p) eq subrel.
  Proof.
    intros v1 v2 Hv.
    destruct Hv; try constructor; try now (discriminate H || destruct H).
    f_equal; rauto.
  Qed.

  Global Instance match_memvals_inv_eq D p:
    Related (list_rel (match_memval (inv_ops D) p)) eq subrel.
  Proof.
    intros vs1 vs2 Hvs.
    induction Hvs; try constructor.
    f_equal; eauto.
    eapply match_memval_inv_eq; eauto.
  Qed.

  Lemma inv_inject_neutral_match_val D p v:
    Val.inject (Mem.flat_inj (proj1_sig p)) v v <->
    match_val (inv_ops D) p v v.
  Proof.
    destruct p.
    simpl.
    split; intros Hv;
    inversion Hv; clear Hv; try constructor.
    {
      pattern ofs1 at 2.
      rewrite H3.
      constructor.
      assumption.
    }
    subst.
    inversion H1.
    rewrite H4 at 1.
    econstructor; eauto.
  Qed.

  Lemma inv_inject_neutral_match_vals D p l:
    Val.inject_list (Mem.flat_inj (proj1_sig p)) l l <->
    list_rel (match_val (inv_ops D) p) l l .
  Proof.
    destruct p.
    simpl.
    split; intros Hl; induction l; inversion Hl; subst; constructor; auto.
    + rewrite <- inv_inject_neutral_match_val. simpl. assumption.
    + rewrite <- inv_inject_neutral_match_val in *. simpl in *. assumption.
  Qed.

  Lemma inv_inject_neutral_match_memval D p v:
    memval_inject (Mem.flat_inj (proj1_sig p)) v v <->
    match_memval (inv_ops D) p v v.
  Proof.
    destruct p.
    simpl.
    split; intros Hv;
    inversion Hv; clear Hv; try constructor.
    - apply inv_inject_neutral_match_val.
      assumption.
    - apply inv_inject_neutral_match_val in H1.
      assumption.
  Qed.

  Lemma inv_inject_neutral_match_memvals D p vs:
    list_forall2 (memval_inject (Mem.flat_inj (proj1_sig p))) vs vs <->
    list_rel (match_memval (inv_ops D) p) vs vs.
  Proof.
    generalize (eq_refl vs).
    generalize vs at 2 4 6.
    revert vs.
    intros vs1 vs2 Hvseq.
    split.
    {
      intro Hvs.
      revert Hvseq.
      induction Hvs.
      - constructor.
      - intros Heq.
        constructor.
        + inversion Heq.
          eapply inv_inject_neutral_match_memval.
          congruence.
        + eapply IHHvs.
          congruence.
    }
    intro Hvs.
    revert Hvseq.
    induction Hvs.
    - constructor.
    - intros Heq.
      constructor.
      + inversion Heq.
        apply inv_inject_neutral_match_memval with (D := D).
        congruence.
      + eapply IHHvs.
        congruence.
  Qed.

  Lemma inv_match_val_inject_neutral D p thr v1 v2:
    match_val (inv_ops D) p v1 v2 ->
    proj1_sig p = thr ->
    Val.inject (Mem.flat_inj thr) v1 v2.
  Proof.
    intros Hv Hthr; subst.
    destruct p; simpl in *.
    inversion Hv; subst; try now constructor.
    inversion H; subst.
    econstructor; eauto.
  Qed.

  Lemma inv_match_memval_inject_neutral D p thr v1 v2:
    match_memval (inv_ops D) p v1 v2 ->
    proj1_sig p = thr ->
    memval_inject (Mem.flat_inj thr) v1 v2.
  Proof.
    intros Hv Hthr; subst.
    destruct p; simpl in *.
    inversion Hv; subst; constructor.
    eapply inv_match_val_inject_neutral; eauto.
  Qed.

  Lemma inv_match_memvals_inject_neutral D p thr v1 v2:
    list_rel (match_memval (inv_ops D) p) v1 v2 ->
    proj1_sig p = thr ->
    list_forall2 (memval_inject (Mem.flat_inj thr)) v1 v2.
  Proof.
    intros Hv Hthr.
    induction Hv; constructor; eauto.
    eapply inv_match_memval_inject_neutral; eauto.
  Qed.

  (** *** Initial states *)

  (** To prove that initial memories satisfy the invariant, we first
    characterize the construction of initial memories with abstract
    data. *)

  Section WITHDATA.
    Context {D: layerdata}.

    Lemma store_zeros_with_data:
      forall m b o n (d: D),
        store_zeros (m, d) b o n =
        match store_zeros m b o n with
          | Some m' => Some (m', d)
          | None => None
        end.
    Proof.
      intros.
      functional induction (store_zeros m b o n); intros.
      * rewrite store_zeros_equation.
        rewrite e.
        reflexivity.
      * rewrite <- IHo0; clear IHo0.
        rewrite store_zeros_equation.
        rewrite e.
        lift_unfold.
        rewrite e0.
        reflexivity.
      * rewrite store_zeros_equation.
        rewrite e.
        lift_unfold.
        rewrite e0.
        reflexivity.
    Qed.

    Lemma store_init_data_with_data:
      forall {F V: Type} (ge: _ F V) m b p a (d: D),
        Genv.store_init_data ge (m, d) b p a =
        match Genv.store_init_data ge m b p a with
          | Some m' => Some (m', d)
          | None => None
        end.
    Proof.
      intros.
      destruct a; simpl; try reflexivity.
      destruct (Genv.find_symbol ge i); reflexivity.
    Qed.

    Lemma store_init_data_list_with_data:
      forall {F V: Type} (ge: _ F V) l m b p (d: D),
        Genv.store_init_data_list ge (m, d) b p l =
        match Genv.store_init_data_list ge m b p l with
          | Some m' => Some (m', d)
          | None => None
        end.
    Proof.
      induction l; simpl; try reflexivity.
      intros.
      rewrite store_init_data_with_data.
      destruct (Genv.store_init_data ge m b p a); try reflexivity.
      eauto.
    Qed.

    Lemma alloc_global_with_data:
      forall {F V} (ge: _ F V),
        forall m ig (d: D),
          Genv.alloc_global ge (m, d) ig =
          match Genv.alloc_global ge m ig with
            | Some m' => Some (m', d)
            | None => None
          end.
    Proof.
      unfold Genv.alloc_global. intros.
      destruct ig as [? [ [ | ] | ]].
      * (* function *)
        lift_unfold.
        destruct (Mem.alloc m 0 1).
        reflexivity.
      * (* variable *)
        lift_unfold.
        destruct (Mem.alloc m 0 (init_data_list_size (gvar_init v))).
        unfold set; simpl.
        rewrite store_zeros_with_data.
        destruct (store_zeros m0 b 0 (init_data_list_size (gvar_init v))); try reflexivity.
        rewrite store_init_data_list_with_data.
        destruct (Genv.store_init_data_list ge m1 b 0 (gvar_init v)); reflexivity.
      * (* none *)
        lift_unfold.
        destruct (Mem.alloc m 0 0); reflexivity.
    Qed.

    Lemma alloc_globals_with_data:
      forall {F V} (ge: _ F V),
        forall l m (d: D),
          Genv.alloc_globals ge (m, d) l =
          match Genv.alloc_globals ge m l with
            | Some m' => Some (m', d)
            | None => None
          end.
    Proof.
      induction l; simpl; try reflexivity.
      intros.
      rewrite alloc_global_with_data.
      destruct (Genv.alloc_global ge m a); try reflexivity.
      eauto.
    Qed.

    Theorem init_mem_with_data:
      forall {F V} (p: _ F V),
        Genv.init_mem (mem := mwd D) p =
        match Genv.init_mem (mem := mem) p with
          | Some m' => Some (m', init_data)
          | None => None
        end.
    Proof.
      intros.
      unfold Genv.init_mem.
      simpl.
      apply alloc_globals_with_data.
    Qed.
  End WITHDATA.

(** XXX: mettre au bon endroit. *)
Instance:
  Related Pos.lt Pos.le subrel.
Proof.
  intros x y Hxy.
  apply Pos.le_lteq.
  eauto.
Qed.

  Global Instance inv_prf D:
    SimulationRelation (inv_ops D).
  Proof.
    split.
    - (* carrier preorder *)
      split; simpl; typeclasses eauto.
    - (* simrel_undef_matches_block increases with carrier *)
      simpl. solve_monotonic.
    - (* match_block increases with carrier *)
      simpl; unfold RelCompFun.
      intros p1 p2 Hp.
      destruct p1 as [p1 Hp1].
      destruct p2 as [p2 Hp2].
      red in Hp.
      simpl in Hp.
      red.
      intro b.
      unfold Mem.flat_inj.
      destruct (plt b p1); destruct (plt b p2); try now repeat constructor.
      xomega.
    - (* undef_matches_values implies undef_matches_block *)
      discriminate.
    - (* undef_matches_block implies undef_matches_values *)
      simpl; tauto.
    - (* undef_match_block for non-injective match_block *)
      simpl.
      destruct p.
      inversion 2 as [? K0].
      inversion 1 as [? K1].
      simpl in K0, K1.
      unfold Mem.flat_inj in K0.
      destruct (plt _ _); try discriminate.
      inversion K0; clear K0; subst.
      unfold Mem.flat_inj in K1.
      destruct (plt _ _); try discriminate.
      inversion K1; clear K1; subst.
      congruence.
    - (* undef_match_block for non weakly valid pointers *)
      simpl.
      destruct p.
      inversion 1; subst.
      inversion 2 as [? ? ? ? K]; subst.
      simpl in K.
      unfold Mem.flat_inj in K.
      destruct (plt _ _); try discriminate.
      inversion K; clear K; subst.
      rewrite Ptrofs.add_zero.
      congruence.
    - (* undef_match_block for invalid pointers *)
      simpl.
      destruct p.
      inversion 1; subst.
      inversion 2 as [? ? ? ? K]; subst.
      simpl in K.
      unfold Mem.flat_inj in K.
      destruct (plt _ _); try discriminate.
      inversion K; clear K; subst.
      rewrite Ptrofs.add_zero.
      congruence.

    - (* global blocks related to themselves *)
      intros [thr Hthr] b Hb.
      red.
      unfold match_block_sameofs.
      simpl.
      apply Hthr in Hb.
      unfold Mem.flat_inj.
      destruct (plt b thr); congruence.

    - (* [Genv.init_mem] *)
      intros.
      intros p1 p2 Hp.
      assert
        ((option_le ((rexists w, match_mem (simrel_id (D:=D)) w) /\
                     (req glob_threshold @@ Mem.nextblock)))
           (Genv.init_mem p1)
           (Genv.init_mem p2)) as Hm.
      {
        eapply genv_init_mem_simrel_withnextblock; eauto.
        + apply SimrelCategory.simrel_id_init_mem.
        + intros x y [H _].
          exists tt.
          assumption.
      }
      pose proof (@init_mem_with_data D F V p1).
      destruct (Genv.init_mem (mem:=mwd D) p1) as [m1|] eqn:Hinit_mem; [|constructor].
      destruct (Genv.init_mem (mem:=mem) p1) as [m|] eqn:Hm1'; try discriminate.
      inversion Hm as [ | xm1 xm2 Hmeq]; clear Hm; subst.
      constructor.
      destruct Hmeq as [[[] Hmeq] Hmnb].
      simpl in Hmeq; subst.
      inversion H; clear H; subst.
      assert (Hw: forall b, block_is_global b -> (b < Mem.nextblock m)%positive).
      {
        intros b Hb.
        red in Hmnb.
        lift_unfold.
        destruct Hmnb.
        exact Hb.
      }
      exists (exist _ _ Hw).
      simpl.
      constructor.
      + apply init_data_inv.
      + eapply InitMem.Genv.initmem_inject_neutral; eauto.
      + red in Hmnb.
        lift_unfold.
        destruct Hmnb.
        eapply init_data_inject.

    - (* [Mem.alloc] *)
      intros _ _ _ [m d Hinv Hnb Hwf] ofs sz.
      lift_unfold.
      destruct (Mem.alloc m ofs sz) as [m' b] eqn:Hm'.
      assert (Mem.nextblock m < Mem.nextblock m')%positive as Hnb_lt.
      {
        erewrite (Mem.nextblock_alloc m _ _ m') by eassumption.
        xomega.
      }
      assert (Hnb': (forall b, block_is_global b -> Mem.valid_block m' b)%positive).
      {
        intros b0 H.
        apply Hnb in H.
        unfold Mem.valid_block in * |- * .
        xomega.
      }
      exists (exist _ _ Hnb').
      split.
      + simpl; unfold RelCompFun; simpl.
        red; simpl.
        xomega.
      + split; [ constructor | ] ; simpl.
        * assumption.
        * eapply Mem.alloc_inject_neutral; eauto.
          eapply Mem.inject_neutral_incr; eauto.
          xomega.
        * revert Hdwf.
          solve_monotonic.
        * erewrite (Mem.alloc_result _ _ _ _ b) by eassumption.
          unfold match_block_sameofs.
          simpl.
          unfold Mem.flat_inj.
          destruct (plt _ _); intuition xomega.

    - (* [Mem.free] *)
      intros p m1 m2 Hm [[b1 lo1] hi1] [[b2 lo2] hi2] Hb.
      inversion Hm; subst.
      inversion Hb; subst.
      inversion H0; subst.
      simpl in H1.
      generalize H1. intros H1_.
      unfold Mem.flat_inj in H1.
      destruct (plt _ _); try discriminate.
      inversion H1; clear H1; subst.
      rewrite Z.add_0_r in  * |- * .
      simpl in *.
      lift_unfold.
      pose proof (Mem.nextblock_free m b2 lo1 (lo1 + sz)) as Hbnf.
      destruct (Mem.free _ _ _ _) as [m'|] eqn:Hm'; constructor.
      exists (exist _ (Mem.nextblock m) Hnb).
      split.
      {
        red.
        simpl.
        reflexivity.
      }
      change (set fst m' (m, d)) with (m', d).
      clear H0 Hb.
      revert Hnb Hm.
      unfold Mem.valid_block.
      erewrite <- Mem.nextblock_free by eassumption.
      inversion 1; subst.
      constructor.
      + assumption.
      + eapply Mem.free_inject_neutral.
        * eassumption.
        * congruence.
        * congruence.
      + revert Hdwf; solve_monotonic.

    - (* [Mem.load] *)
      intros p chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb.
      inversion Hm; subst.
      inversion Hb; subst.
      simpl in *.
      lift_unfold.
      generalize H0. intro H0_.
      unfold Mem.flat_inj in H0.
      destruct (plt _ _); try discriminate.
      inversion H0; clear H0; subst.
      rewrite Z.add_0_r in * |- * .
      destruct (Mem.load chunk m b2 ofs1) as [v|] eqn:Hv; constructor.
      eapply inv_inject_neutral_match_val.
      eapply Mem.load_inject_neutral; eauto.

    - (* [Mem.store] *)
      intros p chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb v1 v2 Hv.
      inversion Hm; subst.
      inversion Hb; subst.
      pose proof (match_val_inv_eq D _ v1 v2 Hv).
      subst.
      eapply inv_match_val_inject_neutral in Hv; eauto.
      simpl in *.
      lift_unfold.
      generalize H0. intro H0_.
      unfold Mem.flat_inj in H0.
      destruct (plt _ _); try discriminate.
      inversion H0; clear H0; subst.
      rewrite Z.add_0_r in * |- * .
      destruct (Mem.store chunk m b2 ofs1 v2) as [m'|] eqn:Hm'; constructor.
      exists (exist _ (Mem.nextblock m) Hnb).
      split.
      {
        red.
        simpl.
        reflexivity.
      }
      clear Hm Hb.
      revert Hnb Hv.
      unfold Mem.valid_block.
      erewrite <- Mem.nextblock_store by eassumption.
      intros Hnb Hv.
      constructor.
      + assumption.
      + eapply Mem.store_inject_neutral.
        * eassumption.
        * erewrite Mem.nextblock_store; eauto.
        * erewrite Mem.nextblock_store; eauto.
        * assumption.
      + simpl.
        exploit Mem.nextblock_store; eauto.
        congruence.

    - (* [Mem.loadbytes] *)
      intros p m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb len.
      inversion Hm; subst.
      inversion Hb; subst.
      simpl in *.
      generalize H0. intro H0_.
      unfold Mem.flat_inj in H0.
      destruct (plt _ _) as [ H | ] ; try discriminate.
      inversion H0; clear H0; subst.
      rewrite Z.add_0_r in * |- * .
      lift_unfold.
      destruct (Mem.loadbytes m b2 ofs1 len) as [v|] eqn:Hv; constructor.
      pose proof (Mem.loadbytes_inject_neutral m Hmwf _ _ _ _ Hv H) as Hvwf.
      clear Hv.
      eapply inv_inject_neutral_match_memvals.
      assumption.

    - (* [Mem.storebytes] *)
      intros p m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb vs1 vs2 Hvs.
      inversion Hm; subst.
      inversion Hb; subst.
      pose proof (match_memvals_inv_eq D _ vs1 vs2 Hvs).
      subst; simpl in *.
      generalize H0. intro H0_.
      unfold Mem.flat_inj in H0.
      destruct (plt _ _) ; try discriminate.
      inversion H0; clear H0; subst.
      rewrite Z.add_0_r in * |- * .
      lift_unfold.
      destruct (Mem.storebytes m b2 ofs1 vs2) as [m'|] eqn:Hm'; constructor.
      exists (exist _ (Mem.nextblock m) Hnb).
      split.
      {
        red.
        simpl.
        reflexivity.
      }
      clear Hm Hb.
      revert Hnb Hvs.
      unfold Mem.valid_block.
      erewrite <- Mem.nextblock_storebytes by eassumption.
      intros Hnb Hvs.
      constructor.
      + assumption.
      + eapply Mem.storebytes_inject_neutral.
        * eassumption.
        * eapply inv_match_memvals_inject_neutral; eauto.
        * erewrite Mem.nextblock_storebytes; eauto.
        * erewrite Mem.nextblock_storebytes; eauto.
      + exploit Mem.nextblock_storebytes; eauto.
        simpl.
        congruence.

    - (* [Mem.perm] *)
      intros p m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb k perm.
      inversion Hm; subst.
      inversion Hb; subst.
      simpl in H0.
      unfold Mem.flat_inj in H0.
      destruct (plt _ _); try discriminate.
      inversion H0; clear H0; subst.
      rewrite Z.add_0_r.
      reflexivity.

    - (* [Mem.valid_block] *)
      intros p m1 m2 Hm b1 b2 Hb.
      inversion Hm; subst.
      inversion Hb; subst.
      simpl in H.
      simpl in *.
      unfold Mem.flat_inj in H.
      destruct (plt _ _); intuition congruence.

    - (* [Mem.different_pointers_inject] *)
      intros p m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2 H H0 H1 H2 H3 H4.
      destruct p.
      simpl in H3, H4.
      unfold Mem.flat_inj in H3, H4.
      destruct (plt b1 _); try discriminate.
      inversion H3; clear H3; subst.
      destruct (plt b2 _); try discriminate.
      inversion H4; clear H4; subst.
      tauto.

    - (* [Mem.weak_valid_pointer_inject_val] *)
      inversion 1; subst.
      inversion 2 as [? ? ? ? K]; subst.
      simpl in K.
      unfold Mem.flat_inj in K.
      destruct (plt _ _); try discriminate.
      inversion K; clear K; subst.
      rewrite Ptrofs.add_zero.
      assumption.

    - (* weak_valid_pointer_address_inject_weak *)
      intros p m1 m2 b1 b2 delta H H0.
      inversion H; clear H; subst.
      simpl in H0.
      unfold Mem.flat_inj in H0.
      destruct (plt _ _); try discriminate.
      inversion H0; clear H0; subst.
      exists 0.
      intros ofs1 H.
      rewrite Ptrofs.add_zero.
      omega.

    - (* [Mem.address_inject] *)
      intros p m1 m2 b1 ofs1 b2 delta pe H H0 H1.
      simpl in H1.
      destruct p.
      unfold Mem.flat_inj in H1.
      destruct (plt _ _); try discriminate.
      inversion H1; clear H1; subst.
      rewrite Ptrofs.add_zero.
      omega.

    - (* [Mem.aligned_area_inject] *)
      intros p m m' b ofs al sz b' delta H H0 H1 H2 H3 H4 H5.
      simpl in H5.
      destruct p.
      unfold Mem.flat_inj in H5.
      destruct (plt _ _); try discriminate.
      inversion H5; clear H5; subst.
      rewrite Z.add_0_r.
      assumption.

    - (* [Mem.disjoint_or_equal_inject] *)
      intros p m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz H H0 H1 H2 H3 H4 H5.
      simpl in H0.
      destruct p.
      unfold Mem.flat_inj in H0.
      destruct (plt _ _); try discriminate.
      inversion H0; clear H0; subst.
      simpl in H1.
      unfold Mem.flat_inj in H1.
      destruct (plt _ _); try discriminate.
      inversion H1; clear H1; subst.
      intuition omega.
  Qed.

  Definition inv {D}: simrel D D :=
    {|
      simrel_ops := inv_ops D
    |}.
End INVARIANT.

Section EQUIVALENCE.

  Context `{Hmem: BaseMemoryModel}.

  Definition max_worlds D (p: simrel_world (simrel_compose (inv (D:=D)) inv)) : simrel_world (D2:=D) inv.
  Proof.
    destruct p as (p1 & p2).
    destruct p1, p2.
    exists (Pmax x x0).
    destruct (Pos.max_spec x x0) as [[A B]|[A B]]; rewrite B; auto.
  Defined.

  Lemma simrel_compose_inv_inv (D: layerdata) :
    simrel_equiv (simrel_compose inv inv) (inv (D := D)).
  Proof.
    exists {| simrel_equiv_fw := max_worlds D;
         simrel_equiv_bw := fun x => (x,x) |}.
    econstructor; simpl; eauto.
    - repeat rstep. unfold max_worlds.
      destruct H. destruct x,y; simpl in *.
      destruct i, i1; simpl in *.
      destruct i0, i2; simpl in *.
      red in H. 
      red in H0. simpl in *.
      apply Pos.max_le_compat; auto.
    - repeat rstep.
    - intros.
      intros [(b' & ? & ?)|?]; auto.
    - intros p b [].
    - intros [p12 p23].
      simpl. destruct p12, p23.
      intros (m1,d1) (m3,d3) ((m2,d2) & A & B); inv A; inv B.
      apply imm_eq. constructor; auto.
      simpl. apply Pos.max_id.
    - intros p (m1,d1) (m2,d2) A. exists (m1,d1).
      inv A; split; econstructor; eauto.
    - destruct p as ((p1,l1),(p2,l2)). simpl.
      unfold compose_meminj.
      unfold Mem.flat_inj.
      intros.
      destruct (plt b p1); try constructor; auto.
      destruct (plt b p2); try constructor; auto.
      rewrite pred_dec_true; auto. constructor; auto.
      apply Pos.max_lt_iff; auto.
    - intros p b. destruct p; simpl.
      unfold compose_meminj.
      unfold Mem.flat_inj.
      destruct (plt b x) eqn:P; try constructor; auto.
      rewrite P. constructor; reflexivity.
    - destruct w.
      unfold max_worlds; split; red; simpl.
      destruct i, i0; simpl.
      apply Pos.le_max_l.
      destruct i, i0; simpl.
      apply Pos.le_max_r.
    - intro. red. destruct w; simpl.
      rewrite Pos.max_id. reflexivity.
  Qed.

End EQUIVALENCE.
