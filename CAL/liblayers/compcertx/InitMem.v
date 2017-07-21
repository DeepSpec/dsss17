Require Import Relations.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcertx.common.MemoryX.
Require Import compcert.common.Globalenvs.
Require Import coqrel.LogicalRelations.
Require Import liblayers.logic.OptionOrders.
Require Export liblayers.compcertx.CompcertStructures.

(** * Miscellaneous properties of [Genv.init_mem] *)

(** Next we show other properties of initial memories. Some of these
  proofs could be updated to use the relational property defined
  in the [InitMemRel] library, and some of these lemmas may become
  obsolete now that we have that more general property. *)

Module Genv.
Export Globalenvs.Genv.

Section WITHMEM.
Context `{Hmem: Mem.MemoryModelX}.

Theorem initmem_inject_neutral:
  forall {F V: Type},
  forall (p: _ F V) m,
    init_mem p = Some m ->
    Mem.inject_neutral (Mem.nextblock m) m.
Proof.
  intros.
  eapply alloc_globals_neutral; eauto. 
  intros. exploit find_symbol_not_fresh; eauto.
  eassumption.
  apply Mem.empty_inject_neutral.
  apply Ple_refl.
Qed.

(** Proving that the initial memory of a program extends to the
initial memory of a more defined program. *)

Lemma store_zeros_right_extends:
  forall m2 b lo hi m2',
    store_zeros m2 b lo hi = Some m2' ->
    forall m1, Mem.extends m1 m2 ->
               (forall o k p, Mem.perm m1 b o k p -> False) ->
               Mem.extends m1 m2'.
Proof.
  intros until hi.
  functional induction (store_zeros m2 b lo hi); try congruence.
  intros. eapply IHo; eauto using Mem.store_outside_extends.
Qed.

Lemma store_init_data_right_extends:
  forall {F V} (ge: _ F V)
         i m2 b o m2',
    store_init_data ge m2 b o i = Some m2' ->
    forall m1, Mem.extends m1 m2 ->
               (forall o, Mem.perm m1 b o Cur Readable -> False) ->
               Mem.extends m1 m2'.
Proof.
  destruct i; simpl; try congruence; eauto using Mem.store_outside_extends.
  destruct (find_symbol ge i); try discriminate.
  eauto using Mem.store_outside_extends.
Qed.

Lemma store_init_data_list_right_extends:
  forall {F V} (ge: _ F V)
         l m2 b o m2',
    store_init_data_list ge m2 b o l = Some m2' ->
    forall m1, Mem.extends m1 m2 ->
               (forall o k p, Mem.perm m1 b o k p -> False) ->
               Mem.extends m1 m2'.
Proof.
  induction l; simpl; try congruence.
  intros until o.
  destruct (store_init_data ge m2 b o a) eqn:?; try discriminate.
  eauto using store_init_data_right_extends.
Qed.

Lemma init_data_size_nonnegative a:
  0 <= init_data_size a.
Proof.
  destruct a; simpl; try omega.
  apply Z.le_max_r.
  destruct Archi.ptr64; omega.
Qed.

Lemma init_data_list_size_nonnegative l:
  0 <= init_data_list_size l.
Proof.
  induction l; simpl.
   omega.
  generalize (init_data_size_nonnegative a); omega.
Qed.

Lemma store_zeros_parallel_extends:
  forall m1 b lo hi m1',
    store_zeros m1 b lo hi = Some m1' ->
    forall m2, Mem.extends m1 m2 ->
               exists m2',
                 store_zeros m2 b lo hi = Some m2' /\
                 Mem.extends m1' m2'.
Proof.
  intros until hi.
  functional induction (store_zeros m1 b lo hi); try congruence.
  * intros. inv H. rewrite store_zeros_equation. rewrite e. eauto.
  * intros.
    exploit Mem.store_within_extends; eauto.
    destruct 1 as [? [STORE ?]].
    rewrite store_zeros_equation.
    rewrite e.
    rewrite STORE.
    eauto.
Qed.

Lemma store_init_data_parallel_extends:
  forall {F V} (ge: _ F V)
         i m1 b o m1',
    store_init_data ge m1 b o i = Some m1' ->
    forall m2, Mem.extends m1 m2 ->
               exists m2',
                 store_init_data ge m2 b o i = Some m2' /\
                 Mem.extends m1' m2'.
Proof.
  destruct i; simpl; try congruence; intros; eauto using Mem.store_within_extends.
  * inv H. eauto.
  * destruct (find_symbol ge i); try discriminate.
    eauto using Mem.store_within_extends.
Qed.

Lemma store_init_data_list_parallel_extends:
  forall {F V} (ge: _ F V)
         l m1 b o m1',
    store_init_data_list ge m1 b o l = Some m1' ->
    forall m2, Mem.extends m1 m2 ->
               exists m2',
                 store_init_data_list ge m2 b o l = Some m2' /\
                 Mem.extends m1' m2'.
Proof.
  induction l; simpl.
  * injection 3; intros; subst; eauto.
  * intros until m1'.
    destruct (store_init_data ge m1 b o a) eqn:?; try discriminate.
    intros.
    exploit (store_init_data_parallel_extends (F := F) (V := V)); eauto.
    destruct 1 as [? [STORE ?]].
    rewrite STORE.
    eauto.
Qed.

Lemma store_init_data_symbols_preserved:
  forall {F1 V1 F2 V2} (ge1: _ F1 V1) (ge2: _ F2 V2),
    (forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i) ->
    forall m b o i,
      store_init_data ge2 m b o i = store_init_data ge1 m b o i.
Proof.
  destruct i; try reflexivity.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma store_init_data_list_symbols_preserved:
  forall {F1 V1 F2 V2} (ge1: _ F1 V1) (ge2: _ F2 V2),
    (forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i) ->
    forall l m b o,
      store_init_data_list ge2 m b o l = store_init_data_list ge1 m b o l.
Proof.
  induction l; simpl; try reflexivity.
  intros.
  erewrite store_init_data_symbols_preserved; eauto.
  destruct (store_init_data ge1 m b o a); congruence.
Qed.

  Lemma alloc_global_extends:
  forall {F V: Type},
  forall (ge1 ge2: _ F V),
  forall SYMB: forall i', find_symbol ge2 i' = find_symbol ge1 i',
    forall m1 m2,
      Mem.extends m1 m2 ->
      forall i d1 d2,
      globdef_rel (fun _ => option_le ⊤%rel) (fun _ => option_le eq) i d1 d2 ->
      forall m'1, 
        alloc_global ge1 m1 (i, d1) = Some m'1 ->
        forall m'2, 
        alloc_global ge2 m2 (i, d2) = Some m'2 ->
        Mem.extends m'1 m'2.
  Proof.
    unfold alloc_global.
    assert (NO_PERM: forall m m' b o k p, Mem.alloc m 0 0 = (m', b) -> Mem.perm m' b o k p -> False).
    {
      intros m m' b o k p Hm' Hp.
      eapply Mem.perm_alloc_3 in Hp; eauto.
      omega.
    }
    destruct 3 as [Hf Hv].
    destruct d1 as [[f1|v1]|], d2 as [[f2|v2]|];
    monad_norm; simpl in Hf, Hv;
    inversion Hf as [xf2 | xf1 xf2 Hf']; clear Hf; subst;
    inversion Hv as [xv2 | xv1 xv2 Hv']; clear Hv; subst;
    destruct (Mem.alloc m1 _ _) eqn:Halloc1, (Mem.alloc m2 _ _) eqn:Halloc2;
    intros;
    repeat match goal with H: Some _ = Some _ |- _ => inversion H; clear H; subst end.
    - (* fun/fun *)
      edestruct Mem.alloc_extends as (?&?&?); eauto.
      + reflexivity.
      + reflexivity.
      + replace x with m0 in * by congruence.
        replace b0 with b in * by congruence.
        edestruct Mem.drop_perm_parallel_extends as (?&?&?); eauto.
        congruence.
    - (* var/var *)
      edestruct Mem.alloc_extends as (?&?&?); eauto.
      + reflexivity.
      + reflexivity.
      + replace x with m0 in * by congruence.
        replace b0 with b in * by congruence.
        subst.
        destruct (store_zeros m _ _ _) eqn:?; try discriminate.
        edestruct store_zeros_parallel_extends as (? & Hsz2 & ?); eauto.
        rewrite Hsz2 in *.
        destruct (store_init_data_list ge1 _ _ _ _) eqn:?; try discriminate.
        edestruct @store_init_data_list_parallel_extends as (? & Hid2 & ?); eauto.
        erewrite <- store_init_data_list_symbols_preserved in Hid2; eauto.
        rewrite Hid2 in *.
        edestruct Mem.drop_perm_parallel_extends as (?&?&?); eauto.
        congruence.
    - (* none/fun *)
      edestruct Mem.alloc_extends as (?&?&?); eauto.
      + reflexivity.
      + instantiate (1:=1); omega.
      + replace x with m0 in * by congruence.
        replace b0 with b in * by congruence.
        eapply Mem.drop_perm_right_extends; eauto.
    - (* none/var *)
      edestruct Mem.alloc_extends as (?&?&?); eauto.
      + reflexivity.
      + instantiate (1 := init_data_list_size (gvar_init v2)).
        eauto using init_data_list_size_nonnegative.
      + replace x with m0 in * by congruence.
        replace b0 with b in * by congruence.
        destruct (store_zeros _ _ _ _) as [ m'2_2 | ] eqn:Hstorezeros; try discriminate.
        destruct (store_init_data_list _ _ _ _ _) as [ m'2_3 | ] eqn:Hstoreinit; try discriminate.
        eapply Mem.drop_perm_right_extends; [ | eauto ..].
        eapply store_init_data_list_right_extends; eauto.
        eapply store_zeros_right_extends; eauto.
    - (* none/none *)
      edestruct Mem.alloc_extends as (?&?&?); eauto.
      + reflexivity.
      + reflexivity.
      + congruence.
  Qed.

  Lemma alloc_globals_app_inv {F V} (ge: Genv.t F V) defs1 defs2 m m2:
    alloc_globals ge m (defs1 ++ defs2) = Some m2 ->
    exists m1,
      alloc_globals ge m defs1 = Some m1 /\
      alloc_globals ge m1 defs2 = Some m2.
  Proof.
    revert m m2.
    induction defs1 as [ | def defs1 IHdefs1]; simpl.
    - eauto.
    - intros m m2.
      destruct (alloc_global ge m def); try discriminate.
      eauto.
  Qed.

  Lemma alloc_globals_extends:
  forall {F V: Type},
  forall (ge1 ge2: _ F V),
  forall SYMB: forall i', find_symbol ge2 i' = find_symbol ge1 i',
  forall l1 l2,
    globdefs_rel (fun _ => option_le ⊤%rel) (fun _ => option_le eq) glob_threshold l1 l2 ->
    forall m1 m2,
      Mem.extends m1 m2 ->
      forall m'1, 
        alloc_globals ge1 m1 l1 = Some m'1 ->
        forall m'2, 
        alloc_globals ge2 m2 l2 = Some m'2 ->
        Mem.extends m'1 m'2.
  Proof.
    Opaque alloc_global.
    intros F V ge1 ge2 Hsymb.
    eapply Pos.peano_ind with (p := glob_threshold).
    - intros l1 l2 Hl m1 m2 Hm m1' Hm1' m2' Hm2'.
      inversion Hl; clear Hl; subst; simpl in *.
      + congruence.
      + exfalso; eapply Pos.succ_not_1; eauto.
    - intros n IHn.
      intros l1 l2 Hl m1 m2 Hm m1' Hm1' m2' Hm2'.
      inversion Hl as [Hi | i defs1 defs2 Hdefs d1 d2 Hd Hi]; clear Hl; subst.
      + exfalso; eapply Pos.succ_not_1; eauto.
      + eapply Pos.succ_inj in Hi; subst.
        eapply alloc_globals_app_inv in Hm1'; destruct Hm1' as (m1'' & Hm1'' & Hd1).
        eapply alloc_globals_app_inv in Hm2'; destruct Hm2' as (m2'' & Hm2'' & Hd2).
        simpl in *.
        destruct (alloc_global ge1 _ _) eqn:Ha1; inversion Hd1; clear Hd1; subst. 
        destruct (alloc_global ge2 _ _) eqn:Ha2; inversion Hd2; clear Hd2; subst.
        eapply alloc_global_extends.
        * eassumption.
        * eapply IHn; eauto.
        * eassumption.
        * eassumption.
        * eassumption.
  Qed.

  Lemma add_globals_le_symbols_preserved:
    forall {F V: Type},
    forall l1 l2, globdefs_rel (fun _ => option_le ⊤%rel) (fun _ => option_le eq) glob_threshold l1 l2 ->
                  forall (ge1 ge2: _ F V),
                  forall SYMB: (forall i', find_symbol ge2 i' = find_symbol ge1 i') /\ genv_next ge2 = genv_next ge1,
                    (forall i, Genv.find_symbol (add_globals ge2 l2) i = Genv.find_symbol (add_globals ge1 l1) i) /\ genv_next (add_globals ge2 l2) = genv_next (add_globals ge1 l1).
  Proof.
    intros ? ? ? ? H ge1 ge2.
    induction H; simpl; auto.
    intros.
    destruct SYMB as [SYMB NEXT].
    rewrite !add_globals_app.
    simpl.
    edestruct IHglobdefs_rel as [Hsymb Hnext]; eauto.
    unfold find_symbol, add_global; simpl.
    split; try congruence.
    intro i'.
    rewrite !PTree.gsspec.
    destruct (peq i' i); try congruence.
    apply Hsymb.
  Qed.

  Lemma globalenv_le_symbols_preserved:
    forall {F V: Type},
      forall (p1 p2: _ F V),
        globdefs_rel (fun _ => option_le ⊤%rel) (fun _ => option_le eq) glob_threshold (prog_defs p1) (prog_defs p2) ->
        (forall i', find_symbol (globalenv p2) i' = find_symbol (globalenv p1) i') /\
        genv_next (globalenv p2) = genv_next (globalenv p1).
  Proof.
    intros.
    apply add_globals_le_symbols_preserved; auto.
  Qed.

  Lemma init_mem_le_extends:
  forall {F V: Type},
  forall (p1 p2: _ F V),
    globdefs_rel (fun _ => option_le ⊤%rel) (fun _ => option_le eq) glob_threshold (prog_defs p1) (prog_defs p2) ->
    forall m'1, 
      init_mem p1 = Some m'1 ->
      forall m'2,
        init_mem p2 = Some m'2 ->
        Mem.extends m'1 m'2.
  Proof.
    intros.
    eapply alloc_globals_extends.
    eapply globalenv_le_symbols_preserved; eauto.
    eassumption.
    eapply Mem.extends_refl.
    eassumption.
    eassumption.
  Qed.

  (*
  Corollary init_mem_le_genv_next:
    forall {F V: Type},
    forall (p1 p2: _ F V),
      globdefs_rel (fun _ => option_le ⊤%rel) (fun _ => option_le eq) glob_threshold (prog_defs p1) (prog_defs p2) ->
      forall m'1, 
        init_mem p1 = Some m'1 ->
        forall m'2,
          init_mem p2 = Some m'2 ->
          Mem.nextblock m'2 = Mem.nextblock m'1.
  Proof.
    intros.
    symmetry.
    apply Mem.mext_next.
    eauto using init_mem_le_extends.
  Qed.
   *)

  Corollary init_mem_le_inject:
    forall {F V: Type},
    forall (p1 p2: _ F V),
      globdefs_rel (fun _ => option_le ⊤%rel) (fun _ => option_le eq) glob_threshold (prog_defs p1) (prog_defs p2) ->
      forall m'1, 
        init_mem p1 = Some m'1 ->
        forall m'2,
          init_mem p2 = Some m'2 ->
          Mem.inject (Mem.flat_inj (Mem.nextblock m'1)) m'1 m'2.
  Proof.
    intros.
    eapply Mem.inject_extends_compose.
    eapply initmem_inject; eauto.
    eauto using init_mem_le_extends.
  Qed.

(** Proving that there are no permissions for blocks associated to no
function or variable. *)

Definition none_symbols_no_perm {F V} (g: _ F V) (m: mem) :=
  forall i b,
    find_symbol g i = Some b ->
    find_funct_ptr g b = None ->
    find_var_info g b = None ->
    forall o k p,
      Mem.perm m b o k p -> False.
  
Lemma alloc_global_genv_next':
  forall {F V},
  forall (ge0 ge: _ F V) m id g m',
  genv_next ge = Mem.nextblock m ->
  alloc_global ge0 m (id, g) = Some m' ->
  genv_next (add_global ge (id, g)) = Mem.nextblock m'.
Proof.
  intros.
  simpl.
  erewrite alloc_global_nextblock; eauto.
  congruence.
Qed.

Lemma alloc_global_no_perm:
  forall {F V},
  forall (ge0 ge: _ F V) m id g m',
  genv_next ge = Mem.nextblock m ->
  alloc_global ge0 m (id, g) = Some m' ->
  none_symbols_no_perm ge m ->
  none_symbols_no_perm (add_global ge (id, g)) m'.
Proof.
  intros. 
  exploit alloc_global_nextblock; eauto. intros NB.
  destruct g as [[f|v]|].
  * (* function *)
    red; intros.
    Transparent alloc_global.
    unfold alloc_global in H0.
    unfold find_var_info, find_def in H4. simpl in H4.
    unfold find_funct_ptr, find_def in H3. simpl in H3.
    unfold find_symbol in H2. simpl in H2.
    rewrite PTree.gsspec in H2.
    destruct (peq i id).
  + subst. inv H2.
    rewrite PTree.gss in H3.
    discriminate.
  + exploit genv_symb_range; eauto.
    intro.
    rewrite PTree.gso in H3; eauto using Plt_ne.
    rewrite H in H6.
    destruct (Mem.alloc m 0 1) eqn:?.
    generalize (Mem.alloc_result _ _ _ _ _ Heqp0).
    intro; subst.
    exploit H1; eauto.
    {
      unfold find_var_info, find_def.
      assert (b <> genv_next ge).
      {
        destruct (Decision.decide (b = genv_next ge)); eauto.
        apply genv_symb_range in H2.
        subst.
        eelim Pos.lt_irrefl; eauto.
      }
      rewrite PTree.gso in H4; eauto.
    }
    eapply Mem.perm_alloc_4; eauto using Plt_ne.
    eapply Mem.perm_drop_4; eauto using Plt_ne.
  * (* variable *)
    red; intros.
    Transparent alloc_global.
    unfold alloc_global in H0.
    unfold find_var_info in H4. simpl in H4. 
    unfold find_funct_ptr in H3. simpl in H3.
    unfold find_symbol in H2. simpl in H2.
    rewrite PTree.gsspec in H2.
    destruct (peq i id).
  + subst. inv H2.
    unfold find_def in H4.
    simpl in H4.
    rewrite PTree.gss in H4.
    discriminate.
  + exploit genv_symb_range; eauto.
    intro.
    unfold find_def in H4.
    simpl in H4.
    rewrite PTree.gso in H4; eauto using Plt_ne.
    rewrite H in H6.
    destruct (Mem.alloc m 0 (init_data_list_size (gvar_init v))) eqn:?.
    generalize (Mem.alloc_result _ _ _ _ _ Heqp0).
    intro; subst.
    destruct (store_zeros m0 (Mem.nextblock m) 0 (init_data_list_size (gvar_init v))) eqn:?; try discriminate.
    destruct (store_init_data_list ge0 m1 (Mem.nextblock m) 0 (gvar_init v)) eqn:?; try discriminate.
    unfold find_def in H3.
    simpl in H3.
    assert (b <> genv_next ge).
    {
      intro; subst.
      eapply genv_symb_range in H2.
      eapply Pos.lt_irrefl; eauto.
    }
    rewrite PTree.gso in H3; eauto.
    exploit H1; eauto.
    eapply Mem.perm_alloc_4; eauto using Plt_ne.
    eapply store_zeros_perm; eauto.
    eapply store_init_data_list_perm; eauto.
    eapply Mem.perm_drop_4; eauto using Plt_ne.
  * (* none *)
    red; intros.
    Transparent alloc_global.
    unfold alloc_global in H0.
    unfold find_var_info in H4. simpl in H4. 
    unfold find_funct_ptr in H3. simpl in H3.
    unfold find_symbol in H2. simpl in H2.
    rewrite PTree.gsspec in H2.
    destruct (Mem.alloc m 0 0) eqn:?.
    inv H0.
    generalize (Mem.alloc_result _ _ _ _ _ Heqp0).
    intro; subst.
    destruct (peq i id).
  + subst. inv H2.
    rewrite H in H5.
    exploit Mem.perm_alloc_3; eauto.
    omega.
  + exploit genv_symb_range; eauto.
    intro.
    rewrite H in H0.
    exploit H1; eauto.
    eapply Mem.perm_alloc_4; eauto using Plt_ne.
Qed.

Lemma alloc_globals_no_perm:
  forall {F V} ge0 gl ge m m',
  genv_next ge = Mem.nextblock m ->
  alloc_globals (F := F) (V := V) ge0 m gl = Some m' ->
  none_symbols_no_perm ge m ->
  none_symbols_no_perm (add_globals ge gl) m'.
Proof.
  induction gl; simpl.
  * inversion 2; subst; eauto.
  * intros.
    destruct (alloc_global ge0 m a) eqn:?; try discriminate.
    destruct a.
    eapply IHgl; eauto using alloc_global_genv_next', alloc_global_no_perm.
Qed.

Lemma init_mem_no_perm:
  forall {F V} p m',
  init_mem (F := F) (V := V) p = Some m' ->
  none_symbols_no_perm (Genv.globalenv p) m'.
Proof.
  unfold init_mem.
  intros.
  eapply alloc_globals_no_perm; eauto.
  rewrite Mem.nextblock_empty. reflexivity.
  intro. intros. eapply Mem.perm_empty; eauto.
Qed.
  
(** Proving that the initial state always exists. *)

Lemma store_zeros_exists:
  forall m b o n,
  Mem.range_perm m b o (o + n) Cur Writable ->
  exists m', store_zeros m b o n = Some m'.
Proof.
  intros until n.
  functional induction (store_zeros m b o n); eauto.
  * intros. apply IHo0.
    unfold Mem.range_perm in *. intros.
    eapply Mem.perm_store_1; eauto.
    eapply H. omega.
  * unfold Mem.range_perm. intros.
    exfalso.
    refine (_ (Mem.valid_access_store m Mint8unsigned b p Values.Vzero _)).
    destruct 1; congruence.
    split.
     simpl. unfold Mem.range_perm. intros.  apply H. omega.
     exists p. simpl. ring.
Qed.

End WITHMEM.

Section WITHGE.

Context (find_symbol: ident -> option Values.block).

Function init_data_valid (p: Z) (i: AST.init_data): bool :=
  match i with
    | Init_int8 _ => if Znumtheory.Zdivide_dec (align_chunk Mint8unsigned) p then true else false
    | Init_int16 _ => if Znumtheory.Zdivide_dec (align_chunk Mint16unsigned) p then true else false
    | Init_int32 _ => if Znumtheory.Zdivide_dec (align_chunk Mint32) p then true else false
    | Init_int64 _ => if Znumtheory.Zdivide_dec (align_chunk Mint64) p then true else false
    | Init_float32 _ => if Znumtheory.Zdivide_dec (align_chunk Mfloat32) p then true else false
    | Init_float64 _ => if Znumtheory.Zdivide_dec (align_chunk Mfloat64) p then true else false
    | Init_space _ => true
    | Init_addrof s _ =>
      match find_symbol s with
        | None => false
        | Some _ => if Znumtheory.Zdivide_dec (align_chunk Mptr) p then true else false
      end
  end.

Function init_data_list_valid (p: Z) (l: list AST.init_data) {struct l}: bool :=
  match l with
    | nil => true
    | a::l' =>
      if init_data_valid p a
      then init_data_list_valid (p+init_data_size a) l'
      else false
  end.

End WITHGE.

(** [init_data_valid] and [init_data_list_valid] are unchanged if symbols are preserved. *)

Section WITH2GE.

Global Instance init_data_valid_symbols_preserved:
  Monotonic init_data_valid ((- ==> eq) ==> - ==> - ==> eq).
Proof.
  unfold init_data_valid.
  solve_monotonic.
Qed.

Global Instance init_data_list_valid_symbols_preserved:
  Monotonic init_data_list_valid ((- ==> eq) ==> - ==> - ==> eq).
Proof.
  intros fs1 fs2 Hfs ofs l.
  revert ofs.
  induction l; simpl; intros ofs; repeat rstep; eauto.
Qed.

End WITH2GE.

Section WITHMEM2.
Context `{Hmem: Mem.MemoryModelX}.

Lemma store_init_data_exists:
  forall {F V} (ge: _ F V) o i,
    init_data_valid (find_symbol ge) o i = true ->
    forall m b,
      Mem.range_perm m b o (o + init_data_size i) Cur Writable ->
      exists m', store_init_data ge m b o i = Some m'.
Proof with try (intros; edestruct Mem.valid_access_store; eauto; split; auto; fail).
  functional inversion 1; subst; simpl; eauto...
  rewrite H1...
Qed.

Remark store_init_data_perm:
  forall {F V} (ge: _ F V),
  forall k prm b' q idl b m p m',
  store_init_data ge m b p idl = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros until m'.  
  assert (forall chunk v,
          Mem.store chunk m b p v = Some m' ->
          (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm)).
  {
    intros; split.
    eapply Mem.perm_store_1; eauto.
    eapply Mem.perm_store_2; eauto.
  }
  destruct idl; simpl in H; eauto.
  simpl. clear. split; congruence.
  simpl. destruct (find_symbol ge i). eauto. discriminate.
Qed.

Lemma store_init_data_list_exists:
  forall {F V} (ge: _ F V) l o,
    init_data_list_valid (find_symbol ge) o l = true ->
    forall m b,
      Mem.range_perm m b o (o + init_data_list_size l) Cur Writable ->
      exists m', store_init_data_list ge m b o l = Some m'.
Proof.
  intros until o.
  functional induction (init_data_list_valid (find_symbol ge) o l);
    try discriminate; intro; simpl; eauto.
  intros.
  exploit @store_init_data_exists; eauto.
  instantiate (2 := m). instantiate (1 := b).
  unfold Mem.range_perm in *. intros. apply H0.
  generalize (init_data_list_size_nonnegative l'). omega.
  destruct 1 as [? STORE].
  rewrite STORE.
  eapply IHb; eauto.
  unfold Mem.range_perm in *. intros.
  erewrite <- store_init_data_perm; eauto.
  eapply H0.
  generalize (init_data_size_nonnegative a).
  omega.
Qed.

Lemma alloc_global_exists:
  forall {F V} (ge: _ F V),
    forall m i g,
      (match g with
         | Some (Gvar v) =>
           init_data_list_valid (find_symbol ge) 0 (gvar_init v) = true
         | _ => True
       end) ->
      exists m', alloc_global ge m (i, g) = Some m'.
Proof.
  destruct g as [ [ | ] | ]; simpl.
  * (* function *)
    intros _.
    destruct (Mem.alloc m 0 1) eqn:?.
    edestruct Mem.range_perm_drop_2; eauto.
    intro. intros. eapply Mem.perm_alloc_2; eauto.
  * (* variable *)
    intro.
    destruct (Mem.alloc m 0 (init_data_list_size (gvar_init v))) as [m1 b] eqn:Halloc.
    generalize (Mem.perm_alloc_2 _ _ _ _ _ Halloc). intro PERM.
    exploit (store_zeros_exists m1 b 0 (init_data_list_size (gvar_init v))).
    {
      intro. intros. eapply Mem.perm_implies. eauto.
      constructor.
    }
    destruct 1 as [m2 STOREZEROS].
    rewrite STOREZEROS.
    refine (_ (store_init_data_list_exists ge (gvar_init v) 0 _ m2 b _)); eauto.
    destruct 1 as [m3 STOREINIT]. rewrite STOREINIT.
    edestruct Mem.range_perm_drop_2; eauto.
    intro. intros.
    erewrite <- store_init_data_list_perm by eassumption.
    erewrite <- store_zeros_perm; eauto.
    intro. intros.
    erewrite <- store_zeros_perm by eassumption.
    eapply Mem.perm_implies. eauto.
    constructor.
  * (* none *)
    destruct (Mem.alloc m 0 0); eauto.
Qed.

Lemma alloc_globals_exists:
  forall {F V} (ge: _ F V),
    forall l,
      (forall i v,
         In (i, Some (Gvar v)) l ->
         init_data_list_valid (find_symbol ge) 0 (gvar_init v) = true) ->
      forall m, exists m',
        alloc_globals ge m l = Some m'.
Proof.
  induction l; simpl; eauto.
  intros.
  destruct a as [i o].
  exploit (alloc_global_exists ge m i o).
   destruct o as [ [ | ] | ]; eauto.
  destruct 1 as [? ALLOC].
  rewrite ALLOC.
  eauto.
Qed.

Lemma init_mem_exists:
  forall {F V} (p: _ F V),
    (forall i v,
       In (i, Some (Gvar v)) (prog_defs p) ->
       init_data_list_valid (find_symbol (globalenv p)) 0 (gvar_init v) = true) ->
    exists m',
      init_mem p = Some m'.
Proof.
  unfold init_mem. intros.
  eapply alloc_globals_exists; eauto.
Qed.

(** Reciprocally, [init_data_list_valid] is necessary for [init_mem] to be well-defined. *)

Lemma store_init_data_valid:
  forall {F V} (ge: _ F V) o i m b m',
    store_init_data ge m b o i = Some m' ->
    init_data_valid (find_symbol ge) o i = true.
Proof with
  try (
      match goal with
        | [ |- context [ Znumtheory.Zdivide_dec ?i ?o ] ] =>
          intros;
          destruct (Znumtheory.Zdivide_dec i o);
          try reflexivity;
          intros;
          exploit Mem.store_valid_access_3; eauto;
          destruct 1;
          contradiction
      end
    ).
  unfold store_init_data; intros until m'.
  destruct i; simpl...
  * reflexivity.
  * destruct (find_symbol ge i); try discriminate...
Qed.

Lemma store_init_data_list_valid:
  forall {F V} (ge: _ F V) l o m b m',
    store_init_data_list ge m b o l = Some m'->
    init_data_list_valid (find_symbol ge) o l = true.
Proof.
  induction l; simpl; auto.
  intros until m'.
  destruct (store_init_data ge m b o a) eqn:STORE; try discriminate.
  erewrite store_init_data_valid; eauto.
Qed.

Lemma alloc_global_valid:
  forall {F V} (ge: _ F V),
    forall m i g m',
      alloc_global ge m (i, g) = Some m' ->
      (match g with
         | Some (Gvar v) =>
           init_data_list_valid (find_symbol ge) 0 (gvar_init v) = true
         | _ => True
       end).
Proof.
  unfold alloc_global.
  intros until m'.
  destruct g; auto.
  destruct g; auto.
  destruct (Mem.alloc m 0 (init_data_list_size (gvar_init v))); try discriminate.
  destruct (store_zeros m0 b 0 (init_data_list_size (gvar_init v))); try discriminate.
  destruct (store_init_data_list ge m1 b 0 (gvar_init v)) eqn:STORE; try discriminate.
  eauto using store_init_data_list_valid.
Qed.

Lemma alloc_globals_valid:
  forall {F V} (ge: _ F V),    
    forall l,
    forall m m',
      alloc_globals ge m l = Some m' ->
      (forall i v,
         In (i, Some (Gvar v)) l ->
         init_data_list_valid (find_symbol ge) 0 (gvar_init v) = true).
Proof.
  induction l; simpl; auto.
  intros.
  destruct (alloc_global ge m a) eqn:ALLOC; try discriminate.
  destruct H0; eauto.
  subst.
  exploit @alloc_global_valid; eauto.
Qed.

Lemma init_mem_valid:
  forall {F V} (p: _ F V),
  forall m',
    init_mem p = Some m' ->
    (forall i v,
       In (i, Some (Gvar v)) (prog_defs p) ->
       init_data_list_valid (find_symbol (globalenv p)) 0 (gvar_init v) = true).
Proof.
  unfold init_mem; eauto using alloc_globals_valid.
Qed.

End WITHMEM2.

End Genv.
