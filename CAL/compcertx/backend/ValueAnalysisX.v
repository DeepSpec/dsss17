Require compcert.backend.ValueAnalysis.
Require ValueDomainX.
Require RTLX.

Import Coqlib.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import ValueDomainX.
Export ValueAnalysis.

(** How to prove that the per-function initial state for RTL is sound for
    value analysis with respect to the initial memory abstraction
    constructed in [ValueDomainX].

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

We also know that the arguments inject into themselves.
*)

Program Definition romem_for_empty_instance: ROMemFor :=
  {|
    romem_for p := rmtop
  |}.

Section WITHMEM.
Context `{memory_model: Mem.MemoryModel}.

Variables (p: RTL.program) (i: ident) (m: mem) (sg: signature) (args: list val) (s: RTL.state).

Let ge := Genv.globalenv p.

Hypotheses
         (INITIAL: RTLX.initial_state p i m sg args s)
         (INJECT_NEUTRAL: Mem.inject_neutral (Mem.nextblock m) m)
         (GENV_NEXT: Ple (Genv.genv_next ge) (Mem.nextblock m))
         (ARGS_INJECT_NEUTRAL: Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args).

Lemma genv_match_initial:
  genv_match (init_bc ge (Mem.nextblock m)) ge.
Proof.
  unfold genv_match; split.
  * intros.
    unfold init_bc.
    simpl.
    split.
    + intro; erewrite Genv.find_invert_symbol; eauto.
    + destruct (Genv.invert_symbol ge b) eqn:?;
               try (destruct (plt b (Mem.nextblock m)); discriminate).
      inversion 1; subst. eauto using Genv.invert_find_symbol.
  * unfold init_bc; simpl. split.
    + destruct (Genv.invert_symbol ge b); try discriminate.
      destruct (plt b (Mem.nextblock m)); try discriminate.
      exfalso; xomega.
    + destruct (Genv.invert_symbol ge b); try discriminate.
      destruct (plt b (Mem.nextblock m)); discriminate.
Qed.

Lemma init_bc_nostack:
  bc_nostack (init_bc ge (Mem.nextblock m)).
Proof.
  unfold bc_nostack, init_bc; simpl.
  intros.
  destruct (Genv.invert_symbol ge b); try discriminate.
  destruct (plt b (Mem.nextblock m)); discriminate.
Qed.

Local Existing Instance romem_for_empty_instance.

Theorem sound_initial:
  sound_state p s.
Proof.
  inversion INITIAL; subst.
  intros.
  econstructor.
  intros cunit H.
  econstructor.
  * constructor.
  * intros; eapply vmatch_list_inject_neutral_top; eauto.
  * apply romatch_top.
  * apply mmatch_inject_neutral_top; eauto.
  * apply genv_match_initial.
  * apply init_bc_nostack.
Qed.

End WITHMEM.
