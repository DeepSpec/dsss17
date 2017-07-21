Require compcert.backend.ValueDomain.

Import Coqlib.
Import Integers.
Import Maps.
Import Values.
Import Memory.
Import Globalenvs.
Import RTL.
Export ValueDomain.

(** How to construct the initial memory abstraction for value analysis.

CompCert assumes whole-program compilation, so the initial memory abstraction
is related to [Genv.init_mem prog], for a source program [prog]. By contrast,
here, in CompCertX, we need to consider any memory [m] being passed to
the function that we are compiling, and for which we consider the
per-function/per-module semantics.

Fortunately, we assume [Mem.inject_neutral m]. Thanks to this hypothesis,
we can prove memory abstraction with some abstract memory state. However,
we do not know anything else, so this abstract memory state will be [mtop].
The practical performance impact on the produced code is not known so far.

We also know that the memory has more blocks than the global environment. This is
necessary as [ValueAnalysis.sound_state] requires all blocks associated to global
symbols to be mapped to BCglob.
*)

Program Definition init_bc (ge: RTL.genv) (n: block) : block_classification :=
  {|    
    bc_img b :=
      match Genv.invert_symbol ge b with
        | Some s => BCglob s
        | None => if plt b n then BCother else BCinvalid
      end
  |}.
Next Obligation.
  destruct (Genv.invert_symbol ge b1) eqn:?; try discriminate.
  destruct (plt b1 n); discriminate.
Qed.
Next Obligation.
  destruct (Genv.invert_symbol ge b1) eqn:?.
  exploit Genv.invert_find_symbol; eauto.
  intros.
  destruct (Genv.invert_symbol ge b2) eqn:?.
  exploit Genv.invert_find_symbol; eauto.
  intros.
  congruence.
  destruct (plt b2 n); discriminate.
  destruct (plt b1 n); discriminate.
Qed.

Section WITHMEM.
Context `{memory_model: Mem.MemoryModel}.

Lemma mmatch_inject_neutral_top:
  forall m ge,
    Mem.inject_neutral (Mem.nextblock m) m -> 
    Ple (Genv.genv_next ge) (Mem.nextblock m) ->
    mmatch (init_bc ge (Mem.nextblock m)) m mtop.
Proof.
  intros.
  eapply mmatch_inj_top.
  replace (inj_of_bc (init_bc ge (Mem.nextblock m)))
          with (Mem.flat_inj (Mem.nextblock m)).
  eapply Mem.neutral_inject.
  assumption.
  apply FunctionalExtensionality.functional_extensionality.
  unfold Mem.flat_inj, inj_of_bc, init_bc; simpl.
  intro b.
  destruct (Genv.invert_symbol ge b) eqn:?;
  destruct (plt b (Mem.nextblock m)); 
  try reflexivity.
  (* global variable *)
  exfalso.
  exploit Genv.invert_find_symbol; eauto.
  intro.
  exploit Genv.genv_symb_range; eauto.
  xomega.
Qed.

(** CompCert's whole-program value analysis is based on an abstraction
    of read-only memory for `const' global variables to be propagated,
    to avoid spurious memory reads.

    In CompCertX, however, the caller is any arbitrary piece of
    assembly code. We could have tried to prove that assembly code
    also preserves the invariant that memory blocks corresponding to
    `const' global variables have no write permissions and their
    contents is always equal to their initial data. But this change
    would be too invasive in the proofs of the clients of CompCertX.

    For this reason, we do not consider any optimization on `const'
    global variables, so the read-only memory abstraction will be
    empty.
*)

Definition rmtop: romem := PTree.empty _.

Lemma romatch_top:
  forall bc m,
    romatch bc m rmtop.
Proof.
  unfold rmtop, romatch.
  intros.
  rewrite PTree.gempty in H0.
  discriminate.
Qed.

End WITHMEM.

(** We also know that values inject into themselves, so we can also abstract them.

    As we also know that arguments are well-typed with respect to the
    signature of the function being compiled, we could also have taken
    advantage of their type to construct a precise value abstraction.
    However, [ValueAnalysis.sound_state] does not require anything about the type
    of the arguments, and only requires that they match Vtop.

    NOTE: the following [vmatch_inject_neutral_top] is slightly different from
    [ValueDomain.vmatch_inj_top], because we have no proof that
    [inj_of_bc (init_bc ge n) = Mem.flat_inj n]
    if we do not know that [Ple (Genv.genv_next ge) n].
*)

Lemma vmatch_inject_neutral_top:
  forall ge v n,
    Val.inject (Mem.flat_inj n) v v ->
    vmatch (init_bc ge n) v Vtop.
Proof.
  inversion 1; try subst; try (econstructor; fail).
  (* case pointer *)
  unfold Mem.flat_inj in H3. destruct (plt b1 n); try discriminate.
  inversion H3.
  subst delta.
  rewrite Ptrofs.add_zero in H4.
  subst.
  econstructor.
  constructor.
  unfold init_bc; simpl.
  destruct (Genv.invert_symbol ge b1); try discriminate.
  destruct (plt b1 n); congruence.
Qed.

Corollary vmatch_list_inject_neutral_top:
  forall l n,
    Val.inject_list (Mem.flat_inj n) l l ->
    forall v, In v l ->
              forall ge,
              vmatch (init_bc ge n) v Vtop.
Proof.
  induction l; inversion 1; subst; simpl.
   tauto.
  destruct 1; subst; eauto using vmatch_inject_neutral_top.
Qed.
