Require SelectLongproof.
Import Coqlib.
Import AST.
Import Values.
Import Memory.
Import Events.
Import SplitLong.
Import SplitLongproof.

Ltac norepet_inv :=
  match goal with
  | [ K: list_norepet (?a :: ?l) |- _] =>
    let Z1 := fresh "Z" in
    let Z2 := fresh "Z" in
    let K1 := fresh "K" in
    let K2 := fresh "K" in
    inversion K as [| Z1 Z2 K1 K2];
    clear K;
    subst Z1 Z2;
    simpl in K1
  end.

Ltac norepet_solve :=
  repeat norepet_inv;
  exfalso;
  now intuition eauto using eq_sym.

(** In this file, we provide an instantiation of builtin_functions_sem
that contains I64 builtins.

For now, we do not reflect the behavior of CompCert's builtins
(defined in ../compcert/ia32/PrintAsm.ml: [print_builtin_inline]). We
should do it later at some point.
 *)

Open Scope string_scope.

Inductive builtin_functions_sem
          `{memory_model_ops: Mem.MemoryModelOps}
  : String.string -> signature -> Globalenvs.Senv.t ->
    list val -> mem -> trace -> val -> mem -> Prop
  :=

  | builtin_sem_i64_neg ge sg
      (Hsg: sg = sig_l_l)
      x z
      (Hy: z = Val.negl x)
      m :
      builtin_functions_sem "__builtin_negl" sg ge (x :: nil) m E0 z m

  | builtin_sem_i64_add ge sg
      (Hsg: sg = sig_ll_l)
      x y z
      (Hy: z = Val.addl x y)
      m :
      builtin_functions_sem "__builtin_addl" sg ge (x :: y :: nil) m E0 z m

  | builtin_sem_i64_sub ge sg
      (Hsg: sg = sig_ll_l)
      x y z
      (Hy: z = Val.subl x y)
      m :
      builtin_functions_sem "__builtin_subl" sg ge (x :: y :: nil) m E0 z m

  | builtin_sem_i64_mul ge sg
      (Hsg: sg = sig_ii_l)
      x y z
      (Hy: z = Val.mull' x y)
      m :
      builtin_functions_sem "__builtin_mull" sg ge (x :: y :: nil) m E0 z m

.

Inductive runtime_functions_sem
            `{memory_model_ops: Mem.MemoryModelOps}
  :
    forall
            (i: String.string) (sg: signature)
            (ge: Globalenvs.Senv.t),
    list val -> mem -> trace -> val -> mem -> Prop
    :=

  | runtime_sem_i64_dtos
      sg ge
      (Hsg: sg = sig_f_l)
      x z
      (Hz: Val.longoffloat x = Some z)
      m :
      runtime_functions_sem "__i64_dtos" sg ge (x :: nil) m E0 z m

  | runtime_sem_i64_dtou
      sg ge
      (Hsg: sg = sig_f_l)
      x z
      (Hz: Val.longuoffloat x = Some z)
      m :
      runtime_functions_sem "__i64_dtou" sg ge (x :: nil) m E0 z m

  | runtime_sem_i64_stod
      sg ge
      (Hsg: sg = sig_l_f)
      x z
      (Hz: Val.floatoflong x = Some z)
      m :
      runtime_functions_sem "__i64_stod" sg ge (x :: nil) m E0 z m

  | runtime_sem_i64_utod
      sg ge
      (Hsg: sg = sig_l_f)
      x z
      (Hz: Val.floatoflongu x = Some z)
      m :
      runtime_functions_sem "__i64_utod" sg ge (x :: nil) m E0 z m

  | runtime_sem_i64_stof
      sg ge
      (Hsg: sg = sig_l_s)
      x z
      (Hz: Val.singleoflong x = Some z)
      m :
      runtime_functions_sem "__i64_stof" sg ge (x :: nil) m E0 z m

  | runtime_sem_i64_utof
      sg ge
      (Hsg: sg = sig_l_s)
      x z
      (Hz: Val.singleoflongu x = Some z)
      m :
      runtime_functions_sem "__i64_utof" sg ge (x :: nil) m E0 z m

  | runtime_sem_i64_sdiv
      sg ge
      (Hsg: sg = sig_ll_l)
      x y z
      (Hz: Val.divls x y = Some z)
      m :
      runtime_functions_sem "__i64_sdiv" sg ge (x :: y :: nil) m E0 z m

  | runtime_sem_i64_udiv
      sg ge
      (Hsg: sg = sig_ll_l)
      x y z
      (Hz: Val.divlu x y = Some z)
      m :
      runtime_functions_sem "__i64_udiv" sg ge (x :: y :: nil) m E0 z m

  | runtime_sem_i64_smod
      sg ge
      (Hsg: sg = sig_ll_l)
      x y z
      (Hz: Val.modls x y = Some z)
      m :
      runtime_functions_sem "__i64_smod" sg ge (x :: y :: nil) m E0 z m

  | runtime_sem_i64_umod
      sg ge
      (Hsg: sg = sig_ll_l)
      x y z
      (Hz: Val.modlu x y = Some z)
      m :
      runtime_functions_sem "__i64_umod" sg ge (x :: y :: nil) m E0 z m

  | runtime_sem_i64_shl
      sg ge
      (Hsg: sg = sig_li_l)
      x y z
      (Hz: z = Val.shll x y)
      m :
      runtime_functions_sem "__i64_shl" sg ge (x :: y :: nil) m E0 z m

  | runtime_sem_i64_shr
      sg ge
      (Hsg: sg = sig_li_l)
      x y z
      (Hz: z = Val.shrlu x y)
      m :
      runtime_functions_sem "__i64_shr" sg ge (x :: y :: nil) m E0 z m

  | runtime_sem_i64_sar
      sg ge
      (Hsg: sg = sig_li_l)
      x y z
      (Hz: z = Val.shrl x y)
      m :
      runtime_functions_sem "__i64_sar" sg ge (x :: y :: nil) m E0 z m

  | runtime_sem_i64_umulh
      sg ge
      (Hsg: sg = sig_ll_l)
      x y z
      (Hz: z = Val.mullhu x y)
      m :
      runtime_functions_sem "__i64_umulh" sg ge (x :: y :: nil) m E0 z m

  | runtime_sem_i64_smulh
      sg ge
      (Hsg: sg = sig_ll_l)
      x y z
      (Hz: z = Val.mullhs x y)
      m :
      runtime_functions_sem "__i64_smulh" sg ge (x :: y :: nil) m E0 z m
                            
.

Section WITHMEM.
  Context `{memory_model: Mem.MemoryModel}.
  Context `{symbols_inject: SymbolsInject}.

  Theorem builtin_functions_properties i sg:
    extcall_properties (builtin_functions_sem i sg) sg.
  Proof.
    constructor.

    + (* type *)
      inversion 1; subst; simpl.
      destruct x; simpl; eauto.
      destruct x; destruct y; simpl; destruct Archi.ptr64; simpl; eauto.
      destruct x; destruct y; simpl; destruct Archi.ptr64; simpl; eauto.
      destruct eq_block; simpl; auto.
      destruct x; destruct y; simpl; eauto.

    + (* symbols_preserved *)
      inversion 2; subst; econstructor; eauto.

    + (* valid_block *)
      inversion 1; subst; eauto.

    + (* perm *)
      inversion 1; subst; eauto.

    + (* unchanged on not writable *)
      inversion 1; subst; eapply Mem.unchanged_on_refl.

    + (* extends *)
      inversion 1; subst.
       - (* neg *)
         inversion 2; subst. inv H6.
         esplit. esplit. split.
         eapply builtin_sem_i64_neg; eauto.
         split.
         inv H4; eauto.
         split; auto using Mem.unchanged_on_refl.
       - (* add *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply builtin_sem_i64_add; eauto.
         split.
         inv H4; inv H5; simpl; eauto.
         destruct v2; simpl; eauto.
         split; auto using Mem.unchanged_on_refl.
       - (* sub *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply builtin_sem_i64_sub; eauto.
         split.
         inv H4; inv H5; simpl; eauto.
         destruct v2; simpl; eauto.
         split; auto using Mem.unchanged_on_refl.
       - (* mul *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply builtin_sem_i64_mul; eauto.
         split.
         inv H4; inv H5; simpl; eauto.
         destruct v2; simpl; eauto.
         split; auto using Mem.unchanged_on_refl.

     + (* inject *)
       inversion 2; subst.

       - (* neg *)
         inversion 2; subst.
         inv H7.
         exists f. esplit. esplit. split.
         eapply builtin_sem_i64_neg; eauto.
         split.
         inversion H5; simpl; eauto.
         split; auto.
         split; auto using Mem.unchanged_on_refl.
         split; auto using Mem.unchanged_on_refl.
         split; auto.
         unfold inject_separated. congruence.

       - (* add *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply builtin_sem_i64_add; eauto.
         split.
         eapply Val.addl_inject; eauto.
         split; auto.
         split; auto using Mem.unchanged_on_refl.
         split; auto using Mem.unchanged_on_refl.
         split; auto.
         unfold inject_separated. congruence.

       - (* sub *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply builtin_sem_i64_sub; eauto.
         split.
         eapply Val.subl_inject; eauto.
         split; auto.
         split; auto using Mem.unchanged_on_refl.
         split; auto using Mem.unchanged_on_refl.
         split; auto.
         unfold inject_separated. congruence.

       - (* mul *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply builtin_sem_i64_mul; eauto.
         split.
         inversion H5; inversion H6; simpl; eauto.
         split; auto.
         split; auto using Mem.unchanged_on_refl.
         split; auto using Mem.unchanged_on_refl.
         split; auto.
         unfold inject_separated. congruence.

     + (* trace length *)
       inversion 1; subst; simpl; omega.

     + (* receptive *)
       inversion 1; subst; inversion 1; subst; eauto.

     + (* determinate *)
       inversion 1; subst; inversion 1; subst; clear; intuition (apply match_traces_E0 || congruence).
  Qed.

  Theorem runtime_functions_properties i sg:
    extcall_properties (runtime_functions_sem i sg) sg.
  Proof.
    constructor.

    + (* type *)
      inversion 1; subst; simpl.
      - destruct x; simpl; try discriminate; eauto. simpl in Hz. destruct (Floats.Float.to_long _); try discriminate. inv Hz. constructor.
      - destruct x; simpl; try discriminate; eauto. simpl in Hz. destruct (Floats.Float.to_longu _); try discriminate. inv Hz. constructor.
      - destruct x; simpl; try discriminate; eauto. simpl in Hz. inv Hz. constructor.
      - destruct x; simpl; try discriminate; eauto. simpl in Hz. inv Hz. constructor.
      - destruct x; simpl; try discriminate; eauto. simpl in Hz. inv Hz. constructor.
      - destruct x; simpl; try discriminate; eauto. simpl in Hz. inv Hz. constructor.
      - destruct x; destruct y; simpl; try discriminate; eauto.
        simpl in Hz.
        destruct (_ || _ && _); try discriminate.
        inv Hz. constructor.
      - destruct x; destruct y; simpl; try discriminate; eauto.
        simpl in Hz.
        destruct (Integers.Int64.eq _ _); try discriminate.
        inv Hz. constructor.
      - destruct x; destruct y; simpl; try discriminate; eauto.
        simpl in Hz.
        destruct (_ || _ && _); try discriminate.
        inv Hz. constructor.
      - destruct x; destruct y; simpl; try discriminate; eauto.
        simpl in Hz.
        destruct (Integers.Int64.eq _ _); try discriminate.
        inv Hz. constructor.
      - destruct x; destruct y; simpl; eauto.
        destruct (Integers.Int.ltu _ _); constructor.
      - destruct x; destruct y; simpl; eauto.
        destruct (Integers.Int.ltu _ _); constructor.
      - destruct x; destruct y; simpl; eauto.
        destruct (Integers.Int.ltu _ _); constructor.
      - destruct x; destruct y; simpl; eauto.
      - destruct x; destruct y; simpl; eauto.

    + (* symbols_preserved *)
      inversion 2; subst; econstructor; eauto.

    + (* valid_block *)
      inversion 1; subst; eauto.

    + (* perm *)
      inversion 1; subst; eauto.

    + (* unchanged on not writable *)
      inversion 1; subst; eapply Mem.unchanged_on_refl.

    + (* extends *)
      inversion 1; subst.
       - (* dtos *)
         inversion 2; subst. inv H6.
         inv H4; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_dtos; eauto.
         auto using Mem.unchanged_on_refl.
       - (* dtou *)
         inversion 2; subst. inv H6.
         inv H4; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_dtou; eauto.
         auto using Mem.unchanged_on_refl.
       - (* stod *)
         inversion 2; subst. inv H6.
         inv H4; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_stod; eauto.
         auto using Mem.unchanged_on_refl.
       - (* utod *)
         inversion 2; subst. inv H6.
         inv H4; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_utod; eauto.
         auto using Mem.unchanged_on_refl.
       - (* stof *)
         inversion 2; subst. inv H6.
         inv H4; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_stof; eauto.
         auto using Mem.unchanged_on_refl.
       - (* utof *)
         inversion 2; subst. inv H6.
         inv H4; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_utof; eauto.
         auto using Mem.unchanged_on_refl.
       - (* sdiv *)
         inversion 2; subst. inv H6. inv H8.
         inv H4; try discriminate.
         destruct v2; try discriminate.
         inv H5; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_sdiv; eauto.
         auto using Mem.unchanged_on_refl.
       - (* udiv *)
         inversion 2; subst. inv H6. inv H8.
         inv H4; try discriminate.
         destruct v2; try discriminate.
         inv H5; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_udiv; eauto.
         auto using Mem.unchanged_on_refl.
       - (* smod *)
         inversion 2; subst. inv H6. inv H8.
         inv H4; try discriminate.
         destruct v2; try discriminate.
         inv H5; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_smod; eauto.
         auto using Mem.unchanged_on_refl.
       - (* umod *)
         inversion 2; subst. inv H6. inv H8.
         inv H4; try discriminate.
         destruct v2; try discriminate.
         inv H5; try discriminate.
         esplit. esplit. split.
         eapply runtime_sem_i64_umod; eauto.
         auto using Mem.unchanged_on_refl.
       - (* shl *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply runtime_sem_i64_shl; eauto.
         split; auto using Mem.unchanged_on_refl.
         inv H4; try constructor.
         inv H5; try constructor.
         destruct v2; constructor.
       - (* shr *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply runtime_sem_i64_shr; eauto.
         split; auto using Mem.unchanged_on_refl.
         inv H4; try constructor.
         inv H5; try constructor.
         destruct v2; constructor.
       - (* sar *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply runtime_sem_i64_sar; eauto.
         split; auto using Mem.unchanged_on_refl.
         inv H4; try constructor.
         inv H5; try constructor.
         destruct v2; constructor.
       - (* umulh *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply runtime_sem_i64_umulh; eauto.
         split; auto using Mem.unchanged_on_refl.
         inv H4; try constructor.
         inv H5; try constructor.
         destruct v2; constructor.         
       - (* umuls *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply runtime_sem_i64_smulh; eauto.
         split; auto using Mem.unchanged_on_refl.
         inv H4; try constructor.
         inv H5; try constructor.
         destruct v2; constructor.         
         
     + (* inject *)
       inversion 2; subst.

       - (* dtos *)
         inversion 2; subst.
         inv H7.
         inv H5; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_dtos; eauto.
         inv Hz.
         destruct (Floats.Float.to_long _); try discriminate.
         inv H4.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* dtou *)
         inversion 2; subst.
         inv H7.
         inv H5; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_dtou; eauto.
         inv Hz.
         destruct (Floats.Float.to_longu _); try discriminate.
         inv H4.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* stod *)
         inversion 2; subst.
         inv H7.
         inv H5; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_stod; eauto.
         inv Hz.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* utod *)
         inversion 2; subst.
         inv H7.
         inv H5; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_utod; eauto.
         inv Hz.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* stof *)
         inversion 2; subst.
         inv H7.
         inv H5; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_stof; eauto.
         inv Hz.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* utof *)
         inversion 2; subst.
         inv H7.
         inv H5; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_utof; eauto.
         inv Hz.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* sdiv *)
         inversion 2; subst.
         inv H7. inv H9.
         inv H5; try discriminate.
         inv H6; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_sdiv; eauto.
         simpl in Hz. destruct (_ || _ && _); try discriminate.
         inv Hz.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* udiv *)
         inversion 2; subst.
         inv H7. inv H9.
         inv H5; try discriminate.
         inv H6; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_udiv; eauto.
         simpl in Hz. destruct (Integers.Int64.eq _ _); try discriminate.
         inv Hz.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* smod *)
         inversion 2; subst.
         inv H7. inv H9.
         inv H5; try discriminate.
         inv H6; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_smod; eauto.
         simpl in Hz. destruct (_ || _ && _); try discriminate.
         inv Hz.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* umod *)
         inversion 2; subst.
         inv H7. inv H9.
         inv H5; try discriminate.
         inv H6; try discriminate.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_umod; eauto.
         simpl in Hz. destruct (Integers.Int64.eq _ _); try discriminate.
         inv Hz.
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* shl *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_shl; eauto.
         split.
         {
           inv H5; simpl; auto.
           inv H6; simpl; auto.
           destruct (Integers.Int.ltu _ _); auto.
         }
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* shr *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_shr; eauto.
         split.
         {
           inv H5; simpl; auto.
           inv H6; simpl; auto.
           destruct (Integers.Int.ltu _ _); auto.
         }
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* sar *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_sar; eauto.
         split.
         {
           inv H5; simpl; auto.
           inv H6; simpl; auto.
           destruct (Integers.Int.ltu _ _); auto.
         }
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* umulh *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_umulh; eauto.
         split.
         {
           inv H5; simpl; auto.
           inv H6; simpl; auto.
         }
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.

       - (* smulh *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply runtime_sem_i64_smulh; eauto.
         split.
         {
           inv H5; simpl; auto.
           inv H6; simpl; auto.
         }
         intuition auto using Mem.unchanged_on_refl.
         unfold inject_separated. congruence.
         
     + (* trace length *)
       inversion 1; subst; simpl; omega.

     + (* receptive *)
       inversion 1; subst; inversion 1; subst; eauto.

     + (* determinate *)
       inversion 1; subst; inversion 1; subst;
       (repeat
          match goal with
              K: _ = Some _ |- _ =>
              revert K
          end);
       clear;
       intuition (apply match_traces_E0 || congruence).
  Qed.

End WITHMEM.

(**
We now expose an [ExternalCallsOpsX] class that only contains
external_calls_sem, so that ExternalCalls can be constructed from the
builtins defined here (and no inline assembly functions).  *)

Class ExternalCallsOpsX
      (mem: Type)
      `{memory_model_ops: Mem.MemoryModelOps mem}
  : Type :=
  {
    external_functions_sem: String.string -> signature -> extcall_sem
  }.

Class ExternalCallsPropsX
      (mem: Type)
      `{external_calls_ops_x: ExternalCallsOpsX mem}
      `{symbols_inject_instace: SymbolsInject}
  : Prop :=
  {
    external_functions_properties:
      forall id sg, extcall_properties (external_functions_sem id sg) sg
  }.

Global Instance external_calls_ops_x_to_external_calls_ops
       (mem: Type)
       `{external_calls_ops_x: ExternalCallsOpsX mem}
  : ExternalCallsOps mem :=
  {|
    Events.external_functions_sem := external_functions_sem;
    Events.builtin_functions_sem := builtin_functions_sem;
    Events.runtime_functions_sem := runtime_functions_sem;
    Events.inline_assembly_sem := fun _ _ _ _ _ _ _ _ => False
  |}.

Global Instance external_calls_ops_x_to_external_calls
       (mem: Type)
       `{memory_model: Mem.MemoryModel mem}
       `{external_calls_ops_x: !ExternalCallsOpsX mem}
       `{symbols_inject_instace: SymbolsInject}
       `{external_calls_x: !ExternalCallsPropsX mem}
  : ExternalCallsProps mem.
Proof.
  constructor.
  apply external_functions_properties.
  apply builtin_functions_properties.
  apply runtime_functions_properties.
  constructor; simpl; contradiction.
Qed.

 Global Instance external_calls_ops_x_helpers_correct
         (mem: Type)
         `{external_calls_ops_x: ExternalCallsOpsX mem}
         `{memory_model : !Mem.MemoryModel mem}
         `{SymbolsInject}
  :
    I64HelpersCorrect mem.
 Proof.
   constructor.
   intuition (constructor; auto).
 Qed.