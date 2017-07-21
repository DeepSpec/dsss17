Require compcert.backend.SelectLongproof.

Import Coqlib.
Import Errors.
Import AST.
Import Values.
Import Globalenvs.
Import Events.
Import SelectLong.
Export SelectLongproof.

(** In this file, we extend the results of
[helper_implements_preserved] for languages other than
Cminor/CminorSel.

In fact, there are two distinct requirements:

1. one *semantic* requirement on the semantics of external functions, and
2. one *syntactic* requirement on the program being compiled.

We first properly formalize the first requirement here. The second one
depends on the language.
*)

Section WITHHELPER.

(** 1. Requirement on the semantics of external functions and builtins.

 These requirements do not need to change across languages. *)

(** We need to constrain the global environment, because CompCertiKOS
does not guarantee that the i64 primitives always have a well-defined
semantics. *)

  Class GenvValidOps: Type :=
    {
      genv_valid {F V} (ge: Genv.t F V): Prop
    }.

  Class GenvValid `{genv_valid_ops: GenvValidOps}: Prop :=
    {
      genv_valid_preserved
        {F1 V1 F2 V2} (ge1: _ F1 V1) (ge2: _ F2 V2)
        (symbols_preserved:
           forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i)
        (genv_next_preserved: Genv.genv_next ge2 = Genv.genv_next ge1)
        (block_is_volatile_preserved:
           forall b o, block_is_volatile ge1 b = Some o ->
                       block_is_volatile ge2 b = Some o)
        (VALID: genv_valid ge1):
        genv_valid ge2
    }.
  
Definition extcall_pure_sem
           `{genv_valid_ops: GenvValidOps}
           `{memory_model_ops : Memtype.Mem.MemoryModelOps}
           (external_functions_sem: ident -> signature -> extcall_sem)
           (i: ident) (sg: signature) (args: list val) (res: val)
: Prop :=
  forall {F V} (ge: _ F V) m,
    forall VALID: genv_valid ge,
    external_functions_sem i sg _ _ ge args m E0 res m.

Lemma extcall_pure_sem_implements
           `{genv_valid_ops: GenvValidOps}
      `{external_calls_ops: ExternalCallsOps}
  (i: ident) (sg: signature) (args: list val) (res: val):
  extcall_pure_sem external_functions_sem i sg args res ->
  forall (F V: Type) (ge: Genv.t (AST.fundef F) V),
    forall VALID: genv_valid ge,
    (forall m : mem,
       external_call (EF_external i sg) ge args m E0 res m).
Proof.
  unfold extcall_pure_sem; intros; simpl; eauto.
Qed.

Class
  ExternalCallI64Helpers
  `{genv_valid_ops: GenvValidOps}
  `{memory_model_ops : Memtype.Mem.MemoryModelOps}
  (external_functions_sem: ident -> signature -> extcall_sem)  
  (hf: helper_functions)
: Prop := 
  {
    ec_helper_i64_dtos:   (forall x z, Val.longoffloat x = Some z -> extcall_pure_sem external_functions_sem hf.(i64_dtos) sig_f_l (x::nil) z);
    ec_helper_i64_dtou:   (forall x z, Val.longuoffloat x = Some z -> extcall_pure_sem external_functions_sem hf.(i64_dtou) sig_f_l (x::nil) z);
    ec_helper_i64_stod:   (forall x z, Val.floatoflong x = Some z -> extcall_pure_sem external_functions_sem hf.(i64_stod) sig_l_f (x::nil) z);
    ec_helper_i64_utod:   (forall x z, Val.floatoflongu x = Some z -> extcall_pure_sem external_functions_sem hf.(i64_utod) sig_l_f (x::nil) z);
    ec_helper_i64_stof:   (forall x z, Val.singleoflong x = Some z -> extcall_pure_sem external_functions_sem hf.(i64_stof) sig_l_s (x::nil) z);
    ec_helper_i64_utof:   (forall x z, Val.singleoflongu x = Some z -> extcall_pure_sem external_functions_sem hf.(i64_utof) sig_l_s (x::nil) z);
    ec_helper_i64_sdiv:   (forall x y z, Val.divls x y = Some z -> extcall_pure_sem external_functions_sem hf.(i64_sdiv) sig_ll_l (x::y::nil) z);
    ec_helper_i64_udiv:   (forall x y z, Val.divlu x y = Some z -> extcall_pure_sem external_functions_sem hf.(i64_udiv) sig_ll_l (x::y::nil) z);
    ec_helper_i64_smod:   (forall x y z, Val.modls x y = Some z -> extcall_pure_sem external_functions_sem hf.(i64_smod) sig_ll_l (x::y::nil) z);
    ec_helper_i64_umod:   (forall x y z, Val.modlu x y = Some z -> extcall_pure_sem external_functions_sem hf.(i64_umod) sig_ll_l (x::y::nil) z);
    ec_helper_i64_shl:   (forall x y, extcall_pure_sem external_functions_sem hf.(i64_shl) sig_li_l (x::y::nil) (Val.shll x y));
    ec_helper_i64_shr:   (forall x y, extcall_pure_sem external_functions_sem hf.(i64_shr) sig_li_l (x::y::nil) (Val.shrlu x y));
    ec_helper_i64_sar:   (forall x y, extcall_pure_sem external_functions_sem hf.(i64_sar) sig_li_l (x::y::nil) (Val.shrl x y))
  }.

Definition builtin_pure_sem
           `{memory_model_ops : Memtype.Mem.MemoryModelOps}
           (builtin_functions_sem: ident -> signature -> extcall_sem)
  (i: ident) (sg: signature) (args: list val) (res: val)
: Prop :=
  forall {F V} (ge: _ F V) m,
    builtin_functions_sem i sg _ _ ge args m E0 res m.

Lemma builtin_pure_sem_implements
      `{external_calls_ops: ExternalCallsOps}
  (i: ident) (sg: signature) (args: list val) (res: val):
  builtin_pure_sem builtin_functions_sem i sg args res ->
  forall (F V: Type) (ge: Genv.t (AST.fundef F) V),
  builtin_implements ge i sg args res.
Proof.
  unfold builtin_pure_sem, builtin_implements. simpl.
  intros. firstorder.
Qed.

Class
  ExternalCallI64Builtins
  `{memory_model_ops : Memtype.Mem.MemoryModelOps}
  (builtin_functions_sem: ident -> signature -> extcall_sem)  
  (hf: helper_functions)
: Prop :=
  {
    ec_builtin_i64_neg:   (forall x, builtin_pure_sem builtin_functions_sem hf.(i64_neg) sig_l_l (x::nil) (Val.negl x));
    ec_builtin_i64_add:   (forall x y, builtin_pure_sem builtin_functions_sem hf.(i64_add) sig_ll_l (x::y::nil) (Val.addl x y));
    ec_builtin_i64_sub:   (forall x y, builtin_pure_sem builtin_functions_sem hf.(i64_sub) sig_ll_l (x::y::nil) (Val.subl x y));
    ec_builtin_i64_mul:  (forall x y, builtin_pure_sem builtin_functions_sem hf.(i64_mul) sig_ii_l (x::y::nil) (Val.mull' x y))
  }.

End WITHHELPER.

(** 2. Syntactic requirement on programs *)

(** The following definition lists the identifiers of external helpers
(not builtins) and their signatures. *)

Definition helper_idents_sigs (h: helper_functions): list (ident * signature) :=
(i64_dtos h, sig_f_l) ::
(i64_dtou h, sig_f_l) ::
(i64_stod h, sig_l_f) ::
(i64_utod h, sig_l_f) ::
(i64_stof h, sig_l_s) ::
(i64_utof h, sig_l_s) ::
(i64_sdiv h, sig_ll_l) ::
(i64_udiv h, sig_ll_l) ::
(i64_smod h, sig_ll_l) ::
(i64_umod h, sig_ll_l) ::
(i64_shl h, sig_li_l) ::
(i64_shr h, sig_li_l) ::
(i64_sar h, sig_li_l) ::
nil.

(** We define the requirement on languages from Csharpminor to
Asm. (Clight uses another representation for external functions, see
../cfrontend/ClightI64helpers.v) *)

Definition genv_contains_helpers
           (h: helper_functions)
           {F V: Type}
           (ge: Genv.t (AST.fundef F) V)
: Prop :=
  forall i sg, In (i, sg) (helper_idents_sigs h) ->
               exists b, Genv.find_symbol ge i = Some b /\
                         Genv.find_funct_ptr ge b = Some (External (EF_external i sg)).

Theorem get_helpers_correct
        `{genv_valid_ops: GenvValidOps}
        `{external_calls_ops: ExternalCallsOps}
        h
        `{external_calls_i64_helpers: !ExternalCallI64Helpers external_functions_sem h}
        `{external_calls_i64_builtins: !ExternalCallI64Builtins builtin_functions_sem h}
        {F V: Type}
        (ge: Genv.t (AST.fundef F) V)
        (Hge: genv_contains_helpers h ge)
        (VALID: genv_valid ge)
:
  i64_helpers_correct ge h.
Proof.
  intros.
  unfold i64_helpers_correct.
  repeat (match goal with
            | |- ?A /\ ?B => split
          end);
    try (intros; inversion external_calls_i64_builtins; eapply builtin_pure_sem_implements; eauto; fail);
  intros;
    match goal with
      |- helper_implements _ ?i ?sg _ _ =>
      assert (In (i, sg) (helper_idents_sigs h)) by (unfold helper_idents_sigs; simpl; tauto);
        exploit Hge; eauto;
        let b := fresh "b" in
        destruct 1 as [b [? ?]];
          exists b;
          exists (EF_external i sg);
          simpl;
          inversion external_calls_i64_helpers;
          unfold extcall_pure_sem in *;
          eauto
    end.
Qed.

(** We now design a way to preserve this syntactic requirement by
compilation. *)

Theorem genv_contains_helpers_preserved
        {F1 V1 F2 V2: Type}
        (ge: Genv.t (AST.fundef F1) V1)
        (tge: Genv.t (AST.fundef F2) V2)
        (symbols_preserved:
           forall i,
             Genv.find_symbol tge i = Genv.find_symbol ge i)
        (external_functions_translated:
           forall i b,
             Genv.find_symbol ge i = Some b ->
             forall ef, Genv.find_funct_ptr ge b = Some (External ef) ->
                        Genv.find_funct_ptr tge b = Some (External ef))
        h
        (ge_contains_helpers:
           genv_contains_helpers h ge)
:
  genv_contains_helpers h tge.
Proof.
  unfold genv_contains_helpers in *.
  intros.
  rewrite symbols_preserved.
  exploit ge_contains_helpers; eauto.
  destruct 1 as [? [? ?]].
  eauto.
Qed.
