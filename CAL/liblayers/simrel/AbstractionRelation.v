Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Floats.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import liblayers.logic.LayerData.
Require Import liblayers.compcertx.CompcertStructures.
Require Import liblayers.simrel.SimulationRelation.

Section WITH_MEMORY_MODEL.
  Context `{Hmem: BaseMemoryModel}.


  (** * Definition *)

  Record abrel_components (D1 D2: layerdata) :=
    {
      abrel_relate: rel D1 D2;
      abrel_match: rel D1 mem;
      abrel_new_glbl: list (ident * list AST.init_data)
    }.

  (** The [abrel_match] component will usually be defined in terms of
    [Mem.load]s on the low-level memory. To make it easy to prove that
    initial states are related, we introduce the following extensional
    characterization of the initial memory state, similar to
    [Genv.load_store_init_data] and [Genv.init_mem_characterization].
    The [abrel_components] will provide concrete initial data, and
    the definitions below will reduce to hypotheses that can be
    destructed and used conveniently. *)

  Fixpoint abrel_init_prop m b p (l: list AST.init_data) :=
    match l with
      | nil => True
      | id::l' =>
        match id with
          | Init_int8 n =>
            Mem.load Mint8unsigned m b p = Some (Vint (Int.zero_ext 8 n)) /\
            Mem.load Mint8signed m b p = Some (Vint (Int.sign_ext 8 n))
          | Init_int16 n =>
            Mem.load Mint16unsigned m b p = Some (Vint (Int.zero_ext 16 n)) /\
            Mem.load Mint16signed m b p = Some (Vint (Int.sign_ext 16 n))
          | Init_int32 n =>
            Mem.load Mint32 m b p = Some (Vint n)
          | Init_int64 n =>
            Mem.load Mint64 m b p = Some (Vlong n)
          | Init_float32 f =>
            Mem.load Mfloat32 m b p = Some (Vsingle f)
          | Init_float64 f =>
            Mem.load Mfloat64 m b p = Some (Vfloat f)
          | Init_space sz =>
            forall ofs,
              p <= ofs < p + sz ->
              Mem.load Mint8unsigned m b ofs = Some Vzero /\
              Mem.load Mint8signed m b ofs = Some Vzero /\
              ((4 | ofs) -> (4 | p + sz) -> Mem.load Mint32 m b ofs = Some Vzero)
          | Init_addrof symb ofs =>
            forall b',
              find_symbol symb = Some b' ->
              Mem.load Mptr m b p = Some (Vptr b' ofs)
        end /\
        abrel_init_prop m b (p + init_data_size id) l'
    end.

  Fixpoint abrel_init_props m (l: list (ident * list AST.init_data)) :=
    match l with
        | nil => True
        | (i, init)::l' =>
          (exists b, find_symbol i = Some b /\
                abrel_init_prop m b 0 init /\
                Mem.range_perm m b 0 (init_data_list_size init) Cur Writable) /\
          abrel_init_props m l'
    end.

  (** Another property required for [abrel_match] is that it should
    only depend on the values of the global variables, not the rest of
    the concrete memory. We express this property using
    [Mem.unchanged_on] with the following mask. *)

  Definition abrel_new_glbl_mask D1 D2 (R: abrel_components D1 D2) :=
    fun (b: block) (ofs: Z) =>
      exists i idata,
        In (i, idata) (abrel_new_glbl D1 D2 R) /\
        find_symbol i = Some b.

  Class AbstractionRelation D1 D2 (R: abrel_components D1 D2) :=
    {
      abrel_relate_init_mem:
        abrel_relate D1 D2 R init_data init_data;
      abrel_match_init_mem m2:
        abrel_init_props m2 (abrel_new_glbl D1 D2 R) ->
        abrel_match D1 D2 R init_data m2;
      abrel_match_unchanged_on :>
        Monotonic
          (abrel_match D1 D2 R)
          (- ==> Mem.unchanged_on (abrel_new_glbl_mask D1 D2 R) ++> impl);
      abrel_new_glbl_thr:
        Forall (fun x => Plt x glob_threshold) (map fst (abrel_new_glbl D1 D2 R))
    }.

  Record abrel (D1 D2: layerdata) :=
    {
      abrel_ops :> abrel_components D1 D2;
      abrel_prf : AbstractionRelation D1 D2 abrel_ops
    }.

  Global Existing Instance abrel_prf.


  (** * Embedding as [simrel] *)

  Require Import SimrelLessdef.
  Require Import ExtensionalityAxioms.

  (** ** Definition *)

  (** Two memories with abstract data match if: their concrete
    components are related by [Mem.extends], their abstract components
    are related by [abrel_relate], and the abstract component of the
    left-hand side is related to the concrete component of the
    right-hand side by [abrel_match].

    In addition, we need to know that the left-hand side memory has no
    permissions for the new globals, so that we know that "parallel"
    accesses cannot touch them. We also need to know that
    [Mem.nextblock] is beyond [glob_threshold] to ensure that this
    invariant is preserved by [Mem.alloc]. *)

  Record abrel_match_mem D1 D2 (R: abrel D1 D2) m1 d1 m2 d2 :=
    {
      abrel_match_mem_relate:
        abrel_relate D1 D2 R d1 d2;
      abrel_match_mem_match:
        abrel_match D1 D2 R d1 m2;
      abrel_match_mem_perms i init b ofs k p:
        In (i, init) (abrel_new_glbl D1 D2 R) ->
        find_symbol i = Some b ->
        ~ Mem.perm m1 b ofs k p /\
        Mem.range_perm m2 b 0 (init_data_list_size init) Cur Writable;
      abrel_match_mem_nextblock b:
        block_is_global b ->
        (b < Mem.nextblock m1)%positive /\ (b < Mem.nextblock m2)%positive
    }.

  Lemma abrel_match_mem_preserved D1 D2 (R: abrel D1 D2) m1 m2 d1 d2 m1' m2':
    abrel_match_mem D1 D2 R m1 d1 m2 d2 ->
    Mem.unchanged_on (abrel_new_glbl_mask D1 D2 R) m1 m1' ->
    Mem.unchanged_on (abrel_new_glbl_mask D1 D2 R) m2 m2' ->
    (Mem.nextblock m1 <= Mem.nextblock m1')%positive ->
    (Mem.nextblock m2 <= Mem.nextblock m2')%positive ->
    abrel_match_mem D1 D2 R m1' d1 m2' d2.
  Proof.
    intros H Hm1 Hm2 Hnb1 Hnb2 (*Hm*).
    destruct H as [Hrelate Hmatch Hperms Hnb].
    split; simpl; eauto.
    - eapply abrel_match_unchanged_on; eauto.
    - intros i gv b ofs k perm Hi Hb.
      split.
      + intro Hp.
        lift_unfold.
        eapply Hperms; eauto.
        eapply Mem.perm_unchanged_on_2; eauto.
        * red.
          eauto.
        * red.
          eapply Hnb; eauto.
      + red; intros.
        eapply Mem.perm_unchanged_on; eauto.
        * red. eauto.
        * eapply Hperms; eauto. 
    - intros b Hb.
      apply Hnb in Hb.
      split; eapply Pos.lt_le_trans; eauto; xomega.
  Qed.

  (** With this we can define the [simrel] for a given [abrel] *)

  Definition abrel_simrel_ops D1 D2 (R: abrel D1 D2) :=
    {|
      simrel_world :=
        simrel_world (ext (D:=D1));
      simrel_undef_matches_values_bool :=
        simrel_undef_matches_values_bool (ext (D:=D1));
      simrel_undef_matches_block :=
        simrel_undef_matches_block (ext (D:=D1));
      simrel_new_glbl :=
        abrel_new_glbl D1 D2 R;
      simrel_meminj :=
        simrel_meminj (ext (D:=D1));
      match_mem p m1 m2 :=
        Mem.extends (fst m1) (fst m2) /\
        abrel_match_mem D1 D2 R (fst m1) (snd m1) (fst m2) (snd m2)
    |}.

  Coercion abrel_simrel_ops : abrel >-> simrel_components.

  (** ** Lemmas *)

  Lemma simrel_acc_abrel D1 D2 R:
    simrel_acc (abrel_simrel_ops D1 D2 R) =
    simrel_acc (ext (D:=D1)).
  Proof.
    reflexivity.
  Qed.

  Lemma simrel_undef_matches_values_abrel D1 D2 R:
    simrel_undef_matches_values (abrel_simrel_ops D1 D2 R) =
    simrel_undef_matches_values (ext (D:=D1)).
  Proof.
    reflexivity.
  Qed.

  Lemma simrel_undef_matches_block_abrel D1 D2 R:
    simrel_undef_matches_block (abrel_simrel_ops D1 D2 R) =
    simrel_undef_matches_block (ext (D:=D1)).
  Proof.
    reflexivity.
  Qed.

  Lemma simrel_meminj_abrel D1 D2 R:
    simrel_meminj (abrel_simrel_ops D1 D2 R) =
    simrel_meminj (ext (D:=D1)).
  Proof.
    reflexivity.
  Qed.

  Lemma match_ptr_abrel D1 D2 R p:
    match_ptr (abrel_simrel_ops D1 D2 R) p =
    match_ptr (ext (D:=D1)) p.
  Proof.
    eapply eqrel_eq; split;
    intros ptr1 ptr2 Hptr;
    destruct Hptr; constructor;
    assumption.
  Qed.

  Lemma match_ptrbits_abrel D1 D2 R p:
    match_ptrbits (abrel_simrel_ops D1 D2 R) p =
    match_ptrbits (ext (D:=D1)) p.
  Proof.
    eapply eqrel_eq; split;
    intros ptr1 ptr2 Hptr;
    destruct Hptr; constructor;
    assumption.
  Qed.

  Lemma match_ptrrange_abrel D1 D2 R p:
    match_ptrrange (abrel_simrel_ops D1 D2 R) p =
    match_ptrrange (ext (D:=D1)) p.
  Proof.
    eapply eqrel_eq; split;
    intros r1 r2 Hr;
    destruct Hr; constructor;
    rewrite match_ptr_abrel in *;
    assumption.
  Qed.

  Lemma match_block_abrel D1 D2 R p:
    match_block (abrel_simrel_ops D1 D2 R) p =
    match_block (ext (D:=D1)) p.
  Proof.
    reflexivity.
  Qed.

  Lemma match_block_sameofs_abrel D1 D2 R p:
    match_block_sameofs (abrel_simrel_ops D1 D2 R) p =
    match_block_sameofs (ext (D:=D1)) p.
  Proof.
    reflexivity.
  Qed.

  Lemma match_val_abrel D1 D2 R p:
    match_val (abrel_simrel_ops D1 D2 R) p =
    match_val (ext (D:=D1)) p.
  Proof.
    eapply eqrel_eq; split.
    - destruct 1; constructor; eauto.
      rewrite match_ptrbits_abrel in H.
      assumption.
    - destruct 1; constructor; eauto.
      rewrite match_ptrbits_abrel.
      assumption.
  Qed.

  Lemma match_memval_abrel D1 D2 R p:
    match_memval (abrel_simrel_ops D1 D2 R) p =
    match_memval (ext (D:=D1)) p.
  Proof.
    eapply eqrel_eq; split.
    - destruct 1; constructor; eauto; rewrite <- match_val_abrel; eauto.
    - destruct 1; constructor; eauto; rewrite match_val_abrel; eauto.
  Qed.

  Hint Rewrite
    simrel_acc_abrel
    simrel_undef_matches_values_abrel
    simrel_undef_matches_block_abrel
    simrel_meminj_abrel
    match_ptr_abrel
    match_ptrbits_abrel
    match_ptrrange_abrel
    match_block_abrel
    match_block_sameofs_abrel
    match_val_abrel
    match_memval_abrel : simrel.

  (** ** Initial states *)

  (** The following lemmas establish a correspondance between
    [simrel_program_rel] and [Genv.find_def], so that we can use
    [Genv.init_mem_characterization_gen] and
    [Genv.globals_initialized]. *)

  Lemma abrel_new_glbl_for_nonnil D1 D2 (R: abrel D1 D2) i init:
    In (i, init) (abrel_new_glbl D1 D2 R) ->
    simrel_new_glbl_for (abrel_new_glbl D1 D2 R) i <> nil /\
    (forall init',
        simrel_newvar_ok (abrel_new_glbl D1 D2 R) true i init' ->
        init = init').
  Proof.
    unfold simrel_new_glbl, simrel_newvar_ok, simrel_new_glbl_for.
    induction (abrel_new_glbl D1 D2 R) as [ | [j d] l IHl]; try contradiction.
    simpl.
    unfold test at 1 4 7.
    intros [Hgv | Hl].
    - inversion Hgv; clear Hgv; subst.
      destruct (decide _); try congruence.
      split; try congruence.
      intros init' [H | [H _]]; try congruence.
    - destruct (decide _).
      + split; try congruence.
        destruct IHl as [Hnnil Hinit]; eauto.
        intros init' Hinit'.
        destruct Hinit' as [? | [? ?]]; try congruence.
      + eauto.
  Qed.

  Local Transparent find_symbol.

  Lemma find_symbol_eq i b:
    find_symbol i = Some b ->
    i = b.
  Proof.
    unfold find_symbol, find_symbol_upto.
    destruct (decide _); congruence.
  Qed.

  Lemma abrel_init_mem_find_def {F1 F2 V} D1 D2 (R: abrel D1 D2) p1 p2:
    simrel_program_rel (F1:=F1) (F2:=F2) (V:=V) R p1 p2 ->
    forall i init,
      In (i, init) (abrel_new_glbl D1 D2 R) ->
      Genv.find_def (Genv.globalenv p1) i = None /\
      exists gv,
        Genv.find_def (Genv.globalenv p2) i = Some (Gvar gv) /\
        gvar_init gv = init /\
        perm_order (Genv.perm_globvar gv) Writable /\
        gvar_volatile gv = false.
  Proof.
    intros Hp i init Hinit.
    apply genv_globalenv_rel in Hp.
    simpl in *.
    revert Hp.
    generalize (Genv.globalenv p1), (Genv.globalenv p2).
    intros ge1 ge2 Hge.

    (* Function/variable definition at [i] *)
    pose proof Hge as Hf.
    eapply genv_rel_find_funct_ptr in Hf.
    instantiate (1 := i) in Hf.
    pose proof Hge as Hv.
    eapply genv_rel_find_var_info in Hv.
    instantiate (1 := i) in Hv.

    apply abrel_new_glbl_for_nonnil in Hinit.
    destruct Hinit as [Hngi Hgv].
    erewrite !stencil_matches_symbols in Hf, Hv by eauto.
    destruct (find_symbol i) as [b|] eqn:Hb.
    - simpl in *.
      pose proof (find_symbol_eq _ _ Hb); subst b.
      inversion Hv as [ | | ]; try contradiction.
      split.
      + destruct (Genv.find_def ge1 i) as [[f1|v1]|] eqn:Hd1; eauto.
        * exfalso.
          assert (exists f2, Genv.find_def ge2 i = Some (Gfun f2)) as [f2 Hf2].
          {
            rewrite <- Genv.find_funct_ptr_iff in Hd1.
            setoid_rewrite <- Genv.find_funct_ptr_iff.
            rewrite Hd1 in Hf.
            inversion Hf; eauto.
          }
          symmetry in H2.
          rewrite Genv.find_var_info_iff in H2.
          congruence.
        * rewrite <- Genv.find_var_info_iff in Hd1.
          congruence.
      + eexists {| gvar_init := init |}; repeat split; eauto.
        * apply Genv.find_var_info_iff.
          symmetry.
          erewrite Hgv; eauto.
        * constructor.
    - simpl in *.
      exfalso.
      unfold find_symbol, find_symbol_upto in Hb.
      destruct (decide _) as [Hi | Hi]; try discriminate.
      eapply Hngi.
      generalize (abrel_new_glbl_thr (R:=R)).
      revert Hi.
      clear.
      intros Hi.
      induction (abrel_new_glbl D1 D2 R); eauto.
      inversion 1; subst.
      unfold simrel_new_glbl_for.
      simpl.
      unfold test.
      destruct (decide _); try congruence.
      apply IHl; eauto.
  Qed.

  Local Opaque find_symbol.

  Local Existing Instance mwd_liftmem_prf.

  Lemma abrel_program_rel_globdefs_rel {F V} D1 D2 (R: abrel D1 D2) p1 p2:
    simrel_program_rel (F1:=F) (F2:=F) (V:=V) R p1 p2 ->
    globdefs_rel
      (fun _ : ident => option_le ⊤)
      (fun _ : ident => option_le eq)
      glob_threshold
      (prog_defs p1)
      (prog_defs p2).
  Proof.
    intros [Hp _ _ _].
    destruct Hp as [defs1 defs2 Hdefs pub main]; simpl.
    clear pub main.
    revert Hdefs.
    repeat rstep.
    intros v1 v2 Hv.
    destruct Hv; constructor.
    reflexivity.
  Qed.

  Lemma stencil_matches_symbols_funext {F V} (ge: Genv.t F V):
    stencil_matches ge ->
    Genv.find_symbol ge = find_symbol.
  Proof.
    intro.
    apply functional_extensionality.
    intro i.
    rewrite stencil_matches_symbols; eauto.
  Qed.

  Lemma simrel_init_mem_exists {F V} D1 D2 (R: abrel D1 D2) (p1 p2: _ F V) m1:
    simrel_program_rel R p1 p2 ->
    Genv.init_mem (F:=F) (V:=V) p1 = Some m1 ->
    exists m2, Genv.init_mem (F:=F) (V:=V) p2 = Some m2.
  Proof.
    intros Hp Hm1.
    pose proof (genv_globalenv_rel _ _ p1 p2 Hp) as Hge.
    (*
    pose proof (abrel_program_rel_globdefs_rel D1 D2 R p1 p2 Hp) as Hdefs.
     *)
    apply Genv.init_mem_exists.
    intros i v Hv.
    pose proof (Genv.init_mem_valid p1 m1 Hm1 i v) as Hvalid1.
    rewrite stencil_matches_symbols_funext in Hvalid1 |- * by eauto.
    clear Hm1 Hge.
    destruct Hp as [Hp _ _ _].
    destruct Hp as [defs1 defs2 Hdefs pub main].
    simpl in *.
    clear pub main.
    induction Hdefs as [ | j defs1 defs2 Hdefs IHdefs d1 d2 Hd]; eauto.
    rewrite in_app in Hv, Hvalid1.
    simpl in Hv, Hvalid1.
    destruct Hv as [Hv|[Hv|Hv]]; eauto.
    clear IHdefs.
    inversion Hv; clear Hv; subst.
    destruct Hd as [Hf Hd].
    unfold rel_pull in Hf, Hd.
    destruct d1 as [[f1|v1]|]; monad_norm; simpl in Hf, Hd.
    - inversion Hf.
    - inversion Hd; clear Hd; subst; eauto.
    - inversion Hd; eauto.
  Qed.

  Lemma abrel_init_props_alternate:
    forall m l,
      Forall
        (fun x =>
           let '(i, init) := x in
           exists b : block,
             find_symbol i = Some b /\
             abrel_init_prop m b 0 init /\
             Mem.range_perm m b 0 (init_data_list_size init) Cur Writable) l ->
      abrel_init_props m l.
  Proof.
    induction 1; simpl; intros; eauto.
    destruct x. eauto.
  Qed.

  Lemma load_store_init_data_abrel_init_prop:
    forall {F V} (ge: Genv.t F V) gi m i o 
      (SM: stencil_matches ge),
      Genv.load_store_init_data ge m i o gi ->
      abrel_init_prop m i o gi.
  Proof.
    induction gi; simpl; intros; auto.
    destruct a; destruct H as (LOAD & LSID); repeat split; auto.
    - rewrite Mem.load_int8_signed_unsigned. rewrite LOAD. simpl.
      rewrite Int.sign_ext_zero_ext; auto. omega.
    - rewrite Mem.load_int16_signed_unsigned. rewrite LOAD. simpl.
      rewrite Int.sign_ext_zero_ext. reflexivity.  omega.
    - rewrite LOAD. reflexivity. omega. simpl. omega.
      exists ofs; simpl; omega.
    - rewrite LOAD. reflexivity. omega. simpl. omega.
      exists ofs; simpl; omega.
    - intros; rewrite LOAD.
      reflexivity. omega. simpl.
      destruct H0, H1. rewrite H1; subst. omega.
      simpl. auto.
    - intros.
      destruct LOAD as (bb' & FS & LOAD).
      rewrite LOAD.
      repeat f_equal.
      apply find_symbol_eq in H. subst.
      rewrite stencil_matches_symbols in FS.
      apply find_symbol_eq in FS. congruence.
      auto.
  Qed.


  Lemma abrel_init_mem_match {F V} D1 D2 (R: abrel D1 D2):
    Related
      (Genv.init_mem (F:=F) (V:=V))
      (Genv.init_mem (F:=F) (V:=V))
      (simrel_program_rel (abrel_simrel_ops D1 D2 R) ++>
       option_le
         (rexists w, match_mem (abrel_simrel_ops D1 D2 R) w)).
  Proof.
    intros p1 p2 Hp.
    setoid_rewrite LiftMem.lift_genv_init_mem.
    destruct (Genv.init_mem p1) as [m1|] eqn:Hm1; [|constructor].
    edestruct (simrel_init_mem_exists D1 D2 R p1 p2) as [m2 Hm2]; eauto.
    rewrite Hm2.
    constructor.
    exists tt.
    simpl.
    split.
    {
      eapply Genv.init_mem_le_extends; eauto.
      eapply abrel_program_rel_globdefs_rel; eauto.
    }
    constructor.
    - eapply abrel_relate_init_mem.
    - eapply abrel_match_init_mem.
      eapply abrel_init_props_alternate.
      apply Forall_forall.
      intros.
      destruct x.
      exploit (@abrel_init_mem_find_def). apply Hp. apply H.
      intros (FDnone & gv & FD & INIT & PO & NV). subst.
      generalize (@abrel_new_glbl_thr _ _ _ (abrel_prf _ _ R)).
      rewrite Forall_forall. intros C.
      specialize (C i).
      destruct (block_is_global_find_symbol i) as (i' & FS).
      {
        apply C.
        rewrite in_map_iff.
        eexists; split; eauto. reflexivity.
      }
      exploit  find_symbol_eq. apply FS. intros; subst.
      eexists; split; eauto.
      exploit Genv.init_mem_characterization_gen_strong. apply Hm2.
      intros (A&B). exploit B; eauto.
      simpl. intros (RP & PERM & LSID & LB).
      split.
      + eapply load_store_init_data_abrel_init_prop; auto.
        eapply genv_globalenv_rel in Hp; eauto.
      + eapply Mem.range_perm_implies; eauto.
    - intros i init b ofs k p IN FS.
      exploit (@abrel_init_mem_find_def). apply Hp. apply IN.
      intros (FDnone & gv & FD & INIT & PO & NV). subst.
      exploit Genv.init_mem_characterization_gen_strong. apply Hm1. intros (A&B).
      exploit find_symbol_eq. apply FS. intros; subst.
      split.
      + apply A; auto.
      + exploit Genv.init_mem_characterization_gen_strong. apply Hm2.
        intros (C&D).
        exploit D; eauto. simpl. intros (RP & _).
        eapply Mem.range_perm_implies; eauto.
    - intros.
      erewrite <- !Genv.init_mem_genv_next by eauto.
      apply genv_globalenv_rel in Hp.
      rewrite !stencil_matches_genv_next by eauto.
      split; assumption.
  Qed.

  (** ** Main proof *)

  Lemma match_block_sameofs_simrel_lessdef D p:
    match_block_sameofs (simrel_lessdef_ops (D:=D)) p = eq.
  Proof.
    apply eqrel_eq; split.
    - intros b1 b2 Hb.
      inversion Hb.
      reflexivity.
    - intros b1 b2 H; subst.
      constructor.
  Qed.

  (** FIXME: we need to figure out how to best reuse [ext]. It used to be,
    we could use it on the base memory model [mem], but now we can
    only use it on [mwd D1] or [mwd D2]. *)

  Instance abrel_simrel_prf D1 D2 R:
    SimulationRelation (abrel_simrel_ops D1 D2 R).
  Proof.
    Local Opaque ext.
    split;
    simpl (simrel_world _); simpl (match_mem _ _ _ _);
    intros; autorewrite with simrel in *.
    Local Transparent ext.
    - apply simrel_acc_preorder.
    - apply simrel_acc_undef_matches_pointer.
    - apply simrel_acc_meminj.
    - constructor.
    - constructor.
    - constructor.
    - constructor.
    - constructor.
    - reflexivity.
    - apply abrel_init_mem_match.
    - intros [m1 d1] [m2 d2] Hm lo hi.
      destruct Hm as [Hme Hmm].
      exists p; split; [constructor|].
      lift_unfold.
      lens_unfold.
      destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Hm1'.
      autorewrite with simrel.
      rewrite match_block_sameofs_simrel_lessdef.
      generalize Hm1'; transport Hm1'; intros Hm1'.
      rewrite H. (* H: Mem.alloc m2 lo hi = _ *)
      repeat rstep.
      split; eauto.
      eapply abrel_match_mem_preserved; eauto.
      + eapply Mem.alloc_unchanged_on; eauto.
      + eapply Mem.alloc_unchanged_on; eauto.
      + simpl.
        erewrite (Mem.nextblock_alloc m1 lo hi m1') by eauto.
        xomega.
      + simpl.
        erewrite (Mem.nextblock_alloc m2 lo hi x) by eauto.
        xomega.
    - intros [m1 d1] [m2 d2] Hm [[b1 lo1] hi1] [[b2 lo2] hi2] Hptr.
      destruct Hm as [Hme Hmm].
      lift_unfold.
      lens_unfold.
      simpl in Hptr.
      destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|constructor].
      generalize Hm1'; transport Hm1'; intro Hm1'.
      rewrite match_ptrrange_simrel_lessdef in Hptr.
      inversion Hptr; clear Hptr; subst.
      rewrite H.
      constructor.
      exists p; split; eauto.
      simpl.
      split; eauto.
      eapply abrel_match_mem_preserved; eauto.
      + eapply Mem.free_unchanged_on; eauto.
        intros ofs1 Hofs1 (i & idata & Hglbl & Hfs).
        eapply Mem.free_range_perm in Hofs1; eauto.
        eapply abrel_match_mem_perms; eauto.
      + eapply Mem.free_unchanged_on; eauto.
        intros ofs1 Hofs1 (i & idata & Hglbl & Hfs).
        eapply Mem.free_range_perm in Hofs1; eauto.
        eapply abrel_match_mem_perms; eauto.
      + rewrite (Mem.nextblock_free m1 b2 lo2 hi2 m1'); eauto.
        reflexivity.
      + rewrite (Mem.nextblock_free m2 b2 lo2 hi2 x); eauto.
        reflexivity.
    - intros chunk [m1 d1] [m2 d2] [Hme Hmm] [b1 ofs1] [b2 ofs2] Hptr.
      lift_unfold.
      rewrite match_ptr_simrel_lessdef in Hptr.
      rewrite match_val_simrel_lessdef.
      inversion Hptr; clear Hptr; subst.
      rauto.
    - intros chunk [m1 d1] [m2 d2] [Hme Hmm] [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv.
      lift_unfold.
      lens_unfold.
      destruct (Mem.store chunk m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
      rewrite match_val_simrel_lessdef in Hv.
      rewrite match_ptr_simrel_lessdef in Hptr.
      inversion Hptr; clear Hptr; subst.
      generalize Hm1'; transport Hm1'; intro Hm1'.
      rewrite H.
      constructor.
      exists p; split; eauto.
      simpl.
      split; eauto.
      eapply abrel_match_mem_preserved; eauto.
      + eapply Mem.store_unchanged_on; eauto.
        intros ofs Hofs (i & idata & Hglbl & Hfs).
        edestruct (Mem.store_valid_access_3 chunk m1) as [Hrp _]; eauto.
        eapply abrel_match_mem_perms; eauto.
      + eapply Mem.store_unchanged_on; eauto.
        intros ofs Hofs (i & idata & Hglbl & Hfs).
        edestruct (Mem.store_valid_access_3 chunk m1) as [Hrp _]; eauto.
        eapply abrel_match_mem_perms; eauto.
      + rewrite (Mem.nextblock_store chunk m1 b2 ofs2 v1 m1'); eauto.
        reflexivity.
      + rewrite (Mem.nextblock_store chunk m2 b2 ofs2 v2 x); eauto.
        reflexivity.
    - intros [m1 d1] [m2 d2] [Hme Hmm] [b1 ofs1] [b2 ofs2] Hptr bytes.
      lift_unfold.
      rewrite match_ptr_simrel_lessdef in Hptr.
      rewrite match_memval_simrel_lessdef.
      rewrite <- list_forall2_list_rel.
      inversion Hptr; clear Hptr; subst.
      rauto.
    - intros [m1 d1] [m2 d2] [Hme Hmm] [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
      lift_unfold.
      lens_unfold.
      destruct (Mem.storebytes m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
      rewrite match_memval_simrel_lessdef in Hvs.
      rewrite <- list_forall2_list_rel in Hvs.
      rewrite match_ptr_simrel_lessdef in Hptr.
      inversion Hptr; clear Hptr; subst.
      generalize Hm1'; transport Hm1'; intro Hm1'.
      rewrite H.
      constructor.
      exists p; split; eauto.
      simpl.
      split; eauto.
      eapply abrel_match_mem_preserved; eauto.
      + eapply Mem.storebytes_unchanged_on; eauto.
        intros ofs Hofs (i & idata & Hglbl & Hfs).
        eapply abrel_match_mem_perms; eauto.
        eapply (Mem.storebytes_range_perm m1); eauto.
      + eapply Mem.storebytes_unchanged_on; eauto.
        intros ofs Hofs (i & idata & Hglbl & Hfs).
        eapply abrel_match_mem_perms; eauto.
        eapply (Mem.storebytes_range_perm m1); eauto.
        rewrite list_forall2_list_rel in Hvs.
        rewrite Hvs.
        eassumption.
      + rewrite (Mem.nextblock_storebytes m1 b2 ofs2 vs1 m1'); eauto.
        reflexivity.
      + rewrite (Mem.nextblock_storebytes m2 b2 ofs2 vs2 x); eauto.
        reflexivity.
    - intros [m1 d1] [m2 d2] [Hme Hmm] [b1 ofs1] [b2 ofs2] Hptr pk pe.
      lift_unfold.
      rewrite match_ptr_simrel_lessdef in Hptr.
      inversion Hptr; clear Hptr; subst.
      rauto.
    - intros [m1 d1] [m2 d2] [Hm _] b1 b2 Hb.
      setoid_rewrite LiftMem.lift_valid_block.
      lift_unfold.
      rewrite match_block_simrel_lessdef in Hb.
      rauto.
    - inversion H3; subst.
      inversion H4; subst.
      eauto.
    - destruct H.
      revert H0.
      setoid_rewrite LiftMem.lift_weak_valid_pointer.
      intro.
      lift_unfold.
      rewrite match_ptrbits_simrel_lessdef in H1.
      inversion H1; clear H1; subst.
      eapply Mem.weak_valid_pointer_extends; eauto.
    - destruct H.
      setoid_rewrite LiftMem.lift_weak_valid_pointer.
      lift_unfold.
      inversion H0; clear H0; subst.
      exists 0%Z.
      intros ofs1 H0.
      rewrite Ptrofs.add_zero.
      omega.
    - destruct H.
      lift_unfold.
      inversion H1; subst.
      rewrite Ptrofs.add_zero.
      omega.
    - destruct H.
      setoid_rewrite LiftMem.lift_range_perm in H3.
      lift_unfold.
      inversion H5; subst.
      rewrite Z.add_0_r.
      assumption.
    - destruct H.
      setoid_rewrite LiftMem.lift_range_perm in H2.
      setoid_rewrite LiftMem.lift_range_perm in H3.
      lift_unfold.
      inversion H0; subst.
      inversion H1; subst.
      repeat rewrite Z.add_0_r.
      tauto.
  Qed.

  Definition abrel_simrel D1 D2 (R: abrel D1 D2) : simrel D1 D2 :=
    {|
      simrel_ops := abrel_simrel_ops D1 D2 R
    |}.

  (* The following lemmas are not used at the moment *)

  Theorem abrel_extends_left_equiv D1 D2 (R: abrel D1 D2):
    simrel_equiv
      (simrel_compose ext (abrel_simrel D1 D2 R))
      (abrel_simrel D1 D2 R).
  Proof.
    esplit.
    apply extends_compose_left; try reflexivity.
    simpl.
    intros p m1 m2 m3 H H0.
    destruct H0.
    revert H.
    lift_simpl.
    intros (EXT & DATA).
    split.
    { eapply Mem.extends_extends_compose; eauto. }
    assert (snd m1 = snd m2) as EQ by assumption.
    rewrite EQ.
    inversion H1.
    split; auto.
    + intros i gv b ofs k p0 H H2.
      split.
      * intro ABSURD.
        eapply abrel_match_mem_perms0; eauto using Mem.perm_extends.
      * eapply abrel_match_mem_perms0; eauto using Mem.perm_extends.
    + apply MemoryRel.memrel_mext_next in EXT.
      rewrite EXT.
      assumption.
  Qed.

  Theorem abrel_extends_right_equiv D1 D2 (R: abrel D1 D2):
    Monotonic
      (abrel_match D1 D2 R)
      (- ==> Mem.extends ++> impl) ->
    simrel_equiv
      (simrel_compose (abrel_simrel D1 D2 R) ext)
      (abrel_simrel D1 D2 R).
  Proof.
    intro PROPER.
    esplit.
    apply extends_compose_right; try reflexivity.
    simpl.
    intros p m1 m2 m3 H H0.
    destruct H.
    assert (Mem.extends (fst m2) (fst m3) /\ snd m3 = snd m2) as EXT.
    {
      revert H0. lift_simpl. destruct 1; auto.
    }
    destruct EXT as (EXT & EQ).
    split.
    { eapply Mem.extends_extends_compose; eauto. }
    rewrite EQ.
    inversion H1.
    split; auto.
    - eapply PROPER; eauto.
    - intros. specialize (abrel_match_mem_perms0 _ _ _ ofs k p0 H2 H3).
      destruct abrel_match_mem_perms0. split; auto.
      red; intros. eauto using Mem.perm_extends.
    - apply MemoryRel.memrel_mext_next in EXT.
      rewrite <- EXT.
      assumption.
   Qed.
End WITH_MEMORY_MODEL.
