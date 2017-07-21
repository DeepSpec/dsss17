Require Stacklayout.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Locations.

(* Free all argument memory locations to consider the
   semantics of the C-style primitive being implemented
   and compiled in a C-style context
*)

Section WITHMEMORYMODEL.
Context `{memory_model: Mem.MemoryModel}.

Definition free_extcall_arg sp m e :=
  match e with
    | S Outgoing ofs ty =>
      match sp with
        | Vptr b o =>
          let of :=(Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)))) in
          Mem.free m b of (of + size_chunk (chunk_of_type ty))
        | _ => None
      end
    | _ => Some m (* provide for other calling conventions *)
  end.

Fixpoint free_extcall_args sp m l :=
  match l with
    | nil => Some m
    | e :: l' =>
      match free_extcall_arg sp m e with
        | Some m' =>
          free_extcall_args sp m' l'
        | _ => None
      end
  end.

Lemma free_extcall_arg_extends  sp m e m':
  free_extcall_arg sp m e = Some m' ->
  Mem.extends m' m.
Proof.
  destruct e.
  {
    simpl.
    inversion 1; subst.
    apply Mem.extends_refl.
  }
  unfold free_extcall_arg.
  destruct sl; try discriminate.
  { inversion 1; subst; apply Mem.extends_refl. }
  { inversion 1; subst; apply Mem.extends_refl. }
  destruct sp; try discriminate.
  intros. eapply Mem.free_left_extends; eauto.
  apply Mem.extends_refl.
Qed.

Corollary free_extcall_args_extends sp l:
  forall m m',
  free_extcall_args sp m l = Some m' ->
  Mem.extends m' m.
Proof.
  induction l; simpl.
  {
    inversion 1; subst.
    apply Mem.extends_refl.
  }
  intros m m' H.
  destruct (free_extcall_arg sp m a) eqn:FREE ; try discriminate.
  eapply Mem.extends_extends_compose; eauto.
  eapply free_extcall_arg_extends; eauto.
Qed.  

Lemma free_extcall_args_parallel_extends sp sp_
      (LESSDEF: Val.lessdef sp sp_)
      l:
  forall m m',
    free_extcall_args sp m l = Some m' ->
    forall m_,
      Mem.extends m m_ ->
      exists m'_,
        free_extcall_args sp_ m_ l = Some m'_ /\
        Mem.extends m' m'_.
Proof.
  induction l; simpl.
  {
    inversion 1; subst; eauto.
  }
  unfold free_extcall_arg.
  destruct a; auto.
  destruct sl; auto.
  destruct sp; try discriminate.
  inversion LESSDEF; subst.
  set (o := Ptrofs.unsigned
              (Ptrofs.add i (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos)))).
  intros m m' H m_ H0.
  destruct (Mem.free m b o (o + size_chunk (chunk_of_type ty))) eqn:FREE; try discriminate.
  exploit Mem.free_parallel_extends; eauto.
  destruct 1 as (? & FREE_ & EXT).
  rewrite FREE_.
  eauto.
Qed.

End WITHMEMORYMODEL.