Require Import LogicalRelations.
Require Import SimulationRelation.
Require Import OptionOrders.
Require Import Cop.
Require Import SimValues.

(*
Module REWRITE.
  Definition sem_sub v1 t1 v2 t2 :=
    match classify_sub t1 t2 with
      | sub_case_pi ty =>
        match v1, v2 with
          | Vptr _ _, Vint _ =>
                Some (Val.sub v1 (Val.mul (Vint (Int.repr (Ctypes.sizeof ty))) v2))
          | _, _ => None
        end
      | sub_case_pp ty =>
        match v1, v2 with
          | Vptr _ _, Vptr _ _ =>
            Val.divu (Val.sub v1 v2) (Vint (Int.repr (Ctypes.sizeof ty)))
          | _, _ => None
        end
      | sub_case_pl ty =>
        match v1, v2 with
          | Vptr _ _, Vlong n2 =>
            let n3 := Int.repr (Int64.unsigned n2) in
            Some (Val.sub v1 (Vint (Int.mul (Int.repr (Ctypes.sizeof ty)) n3)))
          | _, _ => None
        end
      | sub_default =>
        sem_binarith
          (fun (_ : Ctypes.signedness) (n1 n2 : int) =>
             Some (Vint (Int.sub n1 n2)))
          (fun (_ : Ctypes.signedness) (n1 n2 : int64) =>
             Some (Vlong (Int64.sub n1 n2)))
          (fun n1 n2 : Floats.float => Some (Vfloat (Floats.Float.sub n1 n2))) v1
          t1 v2 t2
    end.

  Lemma sem_sub_eq:
    Cop.sem_sub = sem_sub.
  Proof.
    apply FunctionalExtensionality.functional_extensionality. intro v1.
    apply FunctionalExtensionality.functional_extensionality. intro t1.
    apply FunctionalExtensionality.functional_extensionality. intro v2.
    apply FunctionalExtensionality.functional_extensionality. intro t2.
    unfold Cop.sem_sub, sem_sub.
    destruct (classify_sub t1 t2);
      destruct v1;
      destruct v2;
      try reflexivity.
    unfold Val.sub.
    destruct (eq_block _ _); reflexivity.
  Qed.
End REWRITE.
*)

Instance flex_option_le_true {A B} (R: rel A B):
  Related (option_le R) (flex_option_le True R) subrel.
Proof.
  destruct 1; constructor; eauto.
Qed.

Section COP_MONOTONIC.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).
 
  Global Instance bool_val_match p:
    Monotonic
      Cop.bool_val
      (match_val R p ++> - ==> match_mem R p ++> option_le eq).
  Proof.
    unfold bool_val.
    rewrite !weak_valid_pointer_eq.
    repeat rstep.
  Qed.

  Global Instance: Params (@Cop.bool_val) 3.

  Global Instance sem_switch_arg_match p:
    Monotonic
      (@Cop.sem_switch_arg)
      (match_val R p ++> - ==> simrel_option_le R eq).
  Proof.
    unfold Cop.sem_switch_arg.
    rauto.
  Qed.

  Global Instance sem_unary_operation_match p:
    Monotonic
      Cop.sem_unary_operation
      (- ==> match_val R p ++> - ==> match_mem R p ==> option_le (match_val R p)).
  Proof.
    unfold Cop.sem_unary_operation,
    Cop.sem_notbool,
    Cop.sem_notint,
    Cop.sem_absfloat,
    Cop.sem_neg.
    clear. (* erase MemoryModelX, not to be used by solve_monotonic *)
    solve_monotonic.
    congruence.
  Qed.

  Global Instance: Params (@Cop.sem_unary_operation) 4.

  Global Instance sem_cast_match p:
    Monotonic
      Cop.sem_cast
      (match_val R p ++> - ==> - ==> match_mem R p ++>
       option_le (match_val R p)).
  Proof.
    unfold Cop.sem_cast.
    clear. (* erase MemoryModelX, not to be used by solve_monotonic *)
    rewrite !weak_valid_pointer_eq.
    solve_monotonic.
    - rdestruct_assert; [ apply eq_refl | rauto ]. (* XXX: fix in coqrel *)
    - rdestruct_assert; [ apply eq_refl | rauto ]. (* XXX: fix in coqrel *)
  Qed.

  Global Instance: Params (@Cop.sem_cast) 4.

  Local Instance simrel_option_le_subrel {A B: Type} (RAB: rel A B):
    Related
      (simrel_option_le R RAB)
      (option_le RAB)
      subrel.
  Proof.
    intros o1 o2 Ho.
    inversion Ho; constructor; auto.
  Qed.

  Lemma match_ptrbits_shift_sub p b1 ofs1 b2 ofs2 delta:
    match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
    match_ptrbits R p (b1, Ptrofs.sub ofs1 delta) (b2, Ptrofs.sub ofs2 delta).
  Proof.
    rewrite !Ptrofs.sub_add_opp.
    apply match_ptrbits_shift.
  Qed.

  Global Instance sem_binarith_match p:
    Monotonic
      Cop.sem_binarith
      ((- ==> - ==> - ==> option_le (match_val R p)) ++>
       (- ==> - ==> - ==> option_le (match_val R p)) ++>
       (- ==> - ==> option_le (match_val R p)) ++>
       (- ==> - ==> option_le (match_val R p)) ++>
       match_val R p ++> - ==>
       match_val R p ++> - ==>
       match_mem R p ++>
       option_le (match_val R p)).
  Proof.
    unfold Cop.sem_binarith.
    clear. (* erase MemoryModelX, not to be used by solve_monotonic *)
    solve_monotonic.
  Qed.

  Global Instance: Params (@Cop.sem_binarith) 9.

  Remove Hints funext_mor4 : typeclass_instances.

  Global Instance cmp_ptr_match p:
    Related
      (@Cop.cmp_ptr (mwd D1) Mem.valid_pointer)
      (@Cop.cmp_ptr (mwd D2) Mem.valid_pointer)
      (match_mem R p ++> - ==> match_val R p ++> match_val R p ++>
       option_le (match_val R p)).
  Proof.
    unfold cmp_ptr.
    rauto.
  Qed.

  Global Instance: Params (@cmp_ptr) 4.

  Global Instance sem_cmp_match p:
    Monotonic
     Cop.sem_cmp
     (- ==>
      match_val R p ++> - ==>
      match_val R p ++> - ==>
      match_mem R p ++>
       option_le (match_val R p)).
  Proof.
    unfold sem_cmp.
    solve_monotonic.
  Qed.

  Global Instance: Params (@Cop.sem_cmp) 6.

  Global Instance sem_shift_match p:
    Monotonic
      Cop.sem_shift
      (- ==>
       - ==>
       match_val R p ++> - ==>
       match_val R p ++> - ==>
       option_le (match_val R p)).
  Proof.
    unfold Cop.sem_shift.
    clear. (* erase MemoryModelX, not to be used by solve_monotonic *)
    solve_monotonic.
  Qed.

  Global Instance: Params (@Cop.sem_shift) 6.

  Global Instance sem_binary_operation_match p:
    Monotonic
      Cop.sem_binary_operation
      (- ==> - ==>
       match_val R p ++> - ==>
       match_val R p ++> - ==>
       match_mem R p ++>
       option_le (match_val R p)).
  Proof.
    unfold Cop.sem_binary_operation.
    (*repeat rewrite REWRITE.sem_sub_eq.*)
    unfold
    sem_add,
    sem_add_ptr_int,
    sem_add_ptr_long,
    (*REWRITE.*)sem_sub,
    sem_mul,
    sem_div,
    sem_mod,
    sem_and,
    sem_or,
    sem_xor,
    sem_shl,
    sem_shr.
    solve_monotonic;
      auto using match_ptrbits_shift, match_ptrbits_shift_sub.
    - destruct b4; try rauto.
      assert (Ptrofs.sub ofs1 ofs0 = Ptrofs.sub ofs2 ofs3).
      {
        subst.
        inv H4; inv H5.
        replace delta0 with delta in * by congruence.
        symmetry.
        apply Ptrofs.sub_shifted.
      }
      pose proof BoolRel.andb_leb. (* XXX andb_flex_leb has unconstrained evar *)
      repeat rstep; congruence.
  Qed.

  Global Instance: Params (@Cop.sem_binary_operation) 7.
End COP_MONOTONIC.
