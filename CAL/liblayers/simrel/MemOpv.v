Require Export compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.common.Values.
Require Export compcertx.common.MemoryX.
Require Import ExtensionalityAxioms.
Require Import SimrelDefinition.


(** * Memory operation helpers *)

(** Define some more int-based operations in the flavour of Mem.loadv,
   Mem.storev, etc. *)

Module Mem.
  Export MemoryX.Mem.

  Section WITHMEMORYMODELOPS.
    Context `{memory_model_ops: MemoryModelOps}.

    (* Required for assign_loc by copy, and probably also memcpy *)

    Definition loadbytesv m v sz :=
      match v with
        | Vptr b o => loadbytes m b (Ptrofs.unsigned o) sz
        | _ => None
      end.

    Definition storebytesv m v v' :=
      match v with
        | Vptr b o => storebytes m b (Ptrofs.unsigned o) v'
        | _ => None
      end.

    (* We also define Val-style operations for perm, etc.
       but we need to ensure that they are true only if
       the pointer indeed has Cur Nonempty permissions,
       so that they can be preserved by pointer injection
       thanks to address_inject. *)

    Definition permv m v p :=
      match v with
        | Vptr b o => perm m b (Ptrofs.unsigned o) Cur p
        | _ => False
      end.

    Definition range_permv m v sz p :=
      match v with
        | Vptr b o =>
          range_perm m b (Ptrofs.unsigned o) (Ptrofs.unsigned o + sz) Cur p
        | _ =>
          False
      end.

    Definition disjoint_or_equal sz m (b1: block) ofs1 b2 ofs2 :=
      sz >= 0 /\
      Mem.range_perm m b1 ofs1 (ofs1 + sz) Cur Nonempty /\
      Mem.range_perm m b2 ofs2 (ofs2 + sz) Cur Nonempty /\
      (b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1).

    Definition disjoint_or_equalv sz m v1 v2 :=
      match v1 with
        | Vptr b1 o1 =>
          match v2 with
            | Vptr b2 o2 =>
              disjoint_or_equal sz m b1 (Ptrofs.unsigned o1) b2 (Ptrofs.unsigned o2)
            | _ => False
          end
        | _ => False
      end.

    Definition aligned_area al sz m b o :=
      (al = 1 \/ al = 2 \/ al = 4 \/ al = 8) /\
      (sz > 0 -> (al | sz)) /\
      Mem.range_perm m b o (o + sz) Cur Nonempty /\
      (sz > 0 -> (al | o)).

    Definition aligned_areav al sz m v :=
      match v with
        | Vptr b o => aligned_area al sz m b (Ptrofs.unsigned o)
        | _ => False
      end.

    (* Required for free_extcall_arg, and extcall_free_sem *)
    Definition freev m v sz :=
      match v with
        | Vptr b o => free m b (Ptrofs.unsigned o) (Ptrofs.unsigned o + sz)
        | _ => None
      end.

    (* Required for Val.cmpu *)
    Definition valid_pointerv m v :=
      match v with
        | Vptr b o => Mem.valid_pointer m b (Ptrofs.unsigned o)
        | _ => false
      end.

    Definition weak_valid_pointerv m v :=
      match v with
        | Vptr b o => Mem.weak_valid_pointer m b (Ptrofs.unsigned o)
        | _ => false
      end.

  End WITHMEMORYMODELOPS.

  Section WITHMEMORYMODELX.
    Context `{memory_model_x: MemoryModelX}.

    Lemma storebytes_nil m b o l:
      length l = 0%nat ->
      Mem.storebytes m b o l = Some m.
    Proof.
      intros H.
      destruct l; try discriminate.
      edestruct (Mem.range_perm_storebytes m b o nil) as [? MEM].
      {
        simpl.
        red.
        intros.
        omega.
      }
      generalize (storebytes_empty _ _ _ _ MEM).
      congruence.
    Qed.
  End WITHMEMORYMODELX.
End Mem.


(** * Monotonicity properties *)

Section SIMREL.
  Context `{HR: SimulationRelation}.
  Local Opaque mwd_ops.

  Global Instance simrel_permv p:
    Monotonic
      Mem.permv
      (match_mem R p ++> match_val R p ++> - ==> impl).
  Proof.
    repeat red.
    unfold Mem.permv.
    intros x y H x0 y0 H0 a H1.
    inversion H0; subst; try tauto.
    generalize H1.
    repeat rstep.
    eapply match_ptrbits_ptr; eauto.
  Qed.

  Global Instance simrel_loadbytesv p:
    Monotonic
      Mem.loadbytesv
      (match_mem R p ++> match_val R p ++> - ==>
       option_le (list_rel (match_memval R p))).
  Proof.
    repeat red. unfold Mem.loadbytesv.
    intros x y H x0 y0 H0 a.
    inversion H0; subst; try now constructor.
    destruct (Z_le_dec a 0) as [ LE | ] .
    {
      repeat erewrite Mem.loadbytes_empty by assumption.
      apply option_le_some_def.
      repeat constructor.
    }
    destruct (Mem.loadbytes x _ (Ptrofs.unsigned _) a) eqn:EQ; try now constructor.
    rewrite <- EQ.
    repeat rstep.
    eapply match_ptrbits_ptr; eauto.
    eapply Mem.loadbytes_range_perm; eauto.
    omega.
  Qed.

  Global Instance simrel_storebytesv p:
    Monotonic
      Mem.storebytesv
      (match_mem R p ++> match_val R p ++> list_rel (match_memval R p) ++>
       option_le (incr p (match_mem R p))).
  Proof.
    intros x y H x0 y0 H0 x1 y1 H1.
    inversion H0; subst; try now solve_monotonic.
    simpl.
    inversion H1; subst.
    {
      repeat rewrite Mem.storebytes_nil by reflexivity.
      solve_monotonic.
    }
    destruct (Mem.storebytes x _ (Ptrofs.unsigned _) _) eqn:EQ; try now solve_monotonic.
    rewrite <- EQ.
    repeat rstep.
    eapply match_ptrbits_ptr; eauto.
    eapply Mem.storebytes_range_perm; eauto.
    simpl length. rewrite Nat2Z.inj_succ. omega.
  Qed.

  Global Instance simrel_range_perm p:
    Monotonic
      Mem.range_perm
      (match_mem R p ++>
       rel_curry (rel_curry (match_ptrrange R p ++> - ==> - ==> impl))).
  Proof.
    repeat red.
    intros x y H.
    intros [[b0 lo0] hi0] [[b1 lo1] hi1] MATCH.
    simpl.
    intros a a0.
    inversion MATCH; subst.
    unfold Mem.range_perm.
    intros H0 ofs H2.
    inversion H1; subst.
    match goal with
        _: simrel_meminj _ _ _ = Some (_, ?d) |- _ =>
        replace ofs with (ofs - d + d)%Z by omega;
        specialize (H0 (ofs - d)%Z)
    end.
    match type of H0 with
        ?Z -> _ =>
        assert Z as U by omega;
          generalize (H0 U);
          clear H0 U
    end.
    solve_monotonic.
    constructor; eauto.
  Qed.

  Global Instance simrel_range_permv p:
    Monotonic
      Mem.range_permv
      (match_mem R p ++> match_val R p ++> - ==> - ==> impl).
  Proof.
    intros x y H x0 y0 H0 a a0 H1.
    inversion H0; subst; try contradiction.
    destruct (Z_le_dec a 0).
    {
      red. intros ofs H3. omega.
    }
    generalize H1.
    simpl.
    (* solve_monotonic idtac. # loops forever *)
    eapply (fun q K => simrel_range_perm q _ _ K ((_, _), _) ((_, _), _)); eauto.
    constructor.
    eapply match_ptrbits_ptr; eauto.
    eapply H1.
    omega.
  Qed.

  Global Instance simrel_disjoint_or_equal p:
    Monotonic
      Mem.disjoint_or_equal
      (- ==>
       match_mem R p ++>
       rel_curry
         (match_ptr R p ++>
          rel_curry
            (match_ptr R p ++>
             impl))).
  Proof.
    repeat red.
    intros a x y H [b0 o0] [b0' o0'] H0 [b1 o1] [b1' o1'] H1.
    simpl.
    unfold Mem.disjoint_or_equal.
    intros (NONNEG & PERM0 & PERM1 & DISJ_OR_EQ).
    split; auto.
    split.
    {
      revert PERM0.
      (* solve_monotonic idtac. # loops forever *)
      eapply (fun q K => simrel_range_perm q _ _ K ((_, _), _) ((_, _), _)); eauto.
      constructor.
      assumption.
    }
    split.
    {
      revert PERM1.
      (* solve_monotonic idtac. # loops forever *)
      eapply (fun q K => simrel_range_perm q _ _ K ((_, _), _) ((_, _), _)); eauto.
      constructor.
      assumption.
    }
    destruct (Z_eq_dec a 0); try intuition omega.
    inversion H0; subst.
    inversion H1; subst.
    eapply (simrel_disjoint_or_equal_inject p); eauto.
    - eapply Mem.range_perm_max; eauto.
    - eapply Mem.range_perm_max; eauto.
    - omega.
  Qed.

  Global Instance simrel_disjoint_or_equalv p:
    Monotonic
      Mem.disjoint_or_equalv
      (- ==> match_mem R p ++> match_val R p ++> match_val R p ++> impl).
  Proof.
    unfold Mem.disjoint_or_equalv.
    repeat red.
    intros a x y H x0 y0 H0 x1 y1 H1 H2.
    inversion H0; subst; try contradiction.
    inversion H1; subst; try contradiction.
    generalize H2.
    destruct H2 as (NONNEG & PERM0 & PERM1 & DISJ_OR_EQ).
    destruct (Z.eq_dec a 0).
    {
      subst.
      intros _.
      red.
      split; auto with zarith.
      split.
      { red. intros; omega. }
      split.
      { red. intros; omega. }
      right; omega.
    }
    assert (Params (@Mem.disjoint_or_equal) 6) by constructor.
    repeat rstep.
    {
      eapply match_ptrbits_ptr; eauto.
      eapply PERM0. omega.
    }
    {
      eapply match_ptrbits_ptr; eauto.
      eapply PERM1. omega.
    }
  Qed.

  Global Instance simrel_aligned_area p:
    Monotonic
      Mem.aligned_area
      (- ==> - ==> match_mem R p ++> rel_curry (match_ptr R p ++> impl)).
  Proof.
    repeat red.
    intros a a0 x y H [b o] [b' o'] H0.
    simpl.
    unfold Mem.aligned_area.
    destruct 1 as (AL_EQ & ALIGN_SZ & PERM & ALIGN).
    split; auto.
    split; auto.
    split.
    {
      revert PERM.
      (* solve_monotonic. # loops forever. *)
      eapply (fun q K => simrel_range_perm q _ _ K ((_, _), _) ((_, _), _)); eauto.
      constructor.
      assumption.
    }
    inversion H0; subst.
    intros H1.
    eapply (simrel_aligned_area_inject p); eauto.
  Qed.

  Global Instance simrel_aligned_areav p:
    Monotonic
      Mem.aligned_areav
      (- ==> - ==> match_mem R p ++> match_val R p ++> impl).
  Proof.
    repeat red.
    unfold Mem.aligned_areav.
    intros a a0 x y H x0 y0 H0 H1.
    inversion H0; subst; try contradiction.
    destruct (Z_gt_dec a0 0).
    {
      generalize H1.
      assert (Params (@Mem.aligned_area) 5) by constructor.
      repeat rstep.
      eapply match_ptrbits_ptr; eauto.
      eapply H1.
      omega.
    }
    unfold Mem.aligned_area in *.
    unfold Mem.range_perm.
    intuition omega.
  Qed.

  Global Instance simrel_freev p:
    Monotonic
      Mem.freev
      (match_mem R p ++> match_val R p ++> - ==>
       option_le (incr p (match_mem R p))).
  Proof.
    intros x y H x0 y0 H0 a.
    inversion H0; subst; try now solve_monotonic.
    simpl.
    destruct (Mem.free x _ _ _) eqn:FREE; try now solve_monotonic.
    destruct (Z_le_dec a 0).
    {
      exploit (Mem.free_range x); eauto.
      destruct 1; subst; try omega.
      destruct (Mem.range_perm_free y b2 (Ptrofs.unsigned ofs2) (Ptrofs.unsigned ofs2 + a)) as [? FREE2].
      {
        red. intros ofs H2. omega.
      }
      exploit (Mem.free_range y); eauto.
      destruct 1; subst; try omega.
      rewrite FREE2.
      solve_monotonic.
    }
    rewrite <- FREE.
    (* solve_monotonic idtac. # loops forever *)
    apply (fun K => simrel_free _ _ _ K ((_, _), _) ((_, _), _)); auto.
    constructor.
    eapply match_ptrbits_ptr; eauto.
    eapply Mem.free_range_perm; eauto.
    omega.
  Qed.

  Global Instance mem_valid_pointerv_match p:
    Monotonic
      Mem.valid_pointerv
      (match_mem R p ++> match_val R p ++> Bool.leb).
  Proof.
    unfold Mem.valid_pointerv.
    intros m1 m2 Hm v1 v2 Hv.
    inversion Hv; subst; try now constructor.
    destruct (Mem.valid_pointer m1 _ _) eqn:VALID; try now constructor.
    rewrite <- VALID.
    repeat rstep.
    eapply match_ptrbits_ptr; eauto.
    eapply Mem.valid_pointer_nonempty_perm.
    assumption.
  Qed.

  (** The following is NOT a consequence of other
      [mem_valid_pointer_match], but rather follows from the
      [weak_valid_pointer_inject_val] requirement. *)

  Global Instance mem_weak_valid_pointerv_match p:
    Monotonic
      Mem.weak_valid_pointerv
      (match_mem R p ++> match_val R p ++> Bool.leb).
  Proof.
    intros m1 m2 Hm v1 v2 Hv.
    destruct (Mem.weak_valid_pointerv m1 _) eqn:VALID; try reflexivity.
    simpl.
    inversion Hv; subst; try discriminate.
    eapply (simrel_weak_valid_pointer_inject_val p); eauto.
  Qed.
End SIMREL.

Global Instance: Params (@Mem.loadbytesv) 3.
Global Instance: Params (@Mem.storebytesv) 3.
Global Instance: Params (@Mem.permv) 3.
Global Instance: Params (@Mem.disjoint_or_equal) 6.
Global Instance: Params (@Mem.disjoint_or_equalv) 4.
Global Instance: Params (@Mem.aligned_area) 5.
Global Instance: Params (@Mem.aligned_areav) 4.
Global Instance: Params (@Mem.freev) 3.
Global Instance: Params (@Mem.valid_pointerv) 2.
Global Instance: Params (@Mem.weak_valid_pointerv) 2.
Global Instance: Params (@Mem.range_perm) 6.
Global Instance: Params (@Mem.range_permv) 4.
