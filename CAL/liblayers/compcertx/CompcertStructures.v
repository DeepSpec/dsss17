Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Memtype.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.x86.Asm.
Require Export compcertx.common.MemoryX.
Require Import liblayers.lib.Decision.
Require Export liblayers.logic.Structures.
Require Export liblayers.logic.OptionOrders.
Require Export liblayers.compcertx.ErrorMonad.
Require Import Coq.Classes.RelationPairs.


(** * Prerequisites *)

(** This is not a particularly good place for this, but they fit here
  in terms of the dependency graph. *)

Require Export ExtensionalityAxioms.

Lemma eqrel_eq {A B}:
  subrel (@eqrel A B) (@eq (rel A B)).
Proof.
  intros R S [HRS HSR].
  eapply functional_extensionality; intro x.
  eapply functional_extensionality; intro y.
  eapply prop_ext; split; eauto.
Qed.

(** Some properties based on [eqrel_eq]. *)

Lemma prod_rel_eq A B:
  prod_rel (@eq A) (@eq B) = eq.
Proof.
  eapply eqrel_eq; split.
  - intros [x1 y1] [x2 y2] [Hx Hy]; simpl in *.
    congruence.
  - intros x1 x2 H.
    split; congruence.
Qed.

Lemma list_rel_eq {A}:
  list_rel (@eq A) = eq.
Proof.
  eapply eqrel_eq.
  split.
  - induction 1; congruence.
  - intros l1 l2 H.
    subst.
    induction l2; constructor; eauto.
Qed.


(** * Relations on programs and global environments *)

(** ** The [glob_threshold] constant *)

(** We enforce a 1:1 mapping between global identifiers and memory
  blocks, by reserving block identifies up to [glob_threshold] for
  globals. The Compcert programs we construct all have the same
  stucture, and consist in a sequence of [glob_threshold] definitions
  (most of which are empty). The definitions in modules and layers
  should use identifiers below this threshold.

  Because this fixes the [ident] to [block] mapping, this means our
  primitive semantics don't depend on the Compcert global environment,
  which simplifies lots of things. *)

Definition glob_threshold: block := 10000%positive.

(** In order to make it easier to express the inveriants involved in
  the process of building programs or turning them into global
  environments, the definitions below usually proceed in two steps.
  First, we define a more general [foo_upto n] that enforces the
  property up to a given threshold [n], then define [foo] as [foo_upto
  glob_threshold].

  Note that this is not very efficient computationally speaking, since
  [make_program] has to repeatedly append one element to the end of
  the list of definition (hence is O(n^2)). However it is the most
  straightforward way to reason about it. *)

(** ** Programs *)

(** Now we define relations over programs and global environments.
  These relations enforce our fixed structure and are parametrized
  by the more elementary relations [RF] and [RV] over individual
  function and variable definitions. [RF] and [RV] are indexed by
  identifiers, so that they can encode much details about the
  program. Consequently, many properties of [make_program] or
  [Genv.globalenv] can be captured by some form of relational
  parametricity over [Rf] and [RV]. *)

Section PROGRAM_REL.
  Context {F1 F2 V1 V2: Type}.
  Context (RF: ident -> rel (option F1) (option F2)).
  Context (RV: ident -> rel (option (globvar V1)) (option (globvar V2))).

  (** There is one subtlety involved with relating global definitions.
    Since it is expected that both [RF] and [RV] apply at each
    identifier over the whole program and/or global environment, for two
    function definitions (say) to be related, we also need to know
    that it's okay for it to be no variable definitions at that identifier.
    To enforce this, we not only require that the two function
    definitions be related by [RF]; we also require that [RV] allows
    [None] in both programs at that same identifier.

    Perhaps the extensional formulation below is clearer: we can
    project both an optional function definition and an optional
    variable definition out of an optional global definition (of
    course, at least one of them will be [None]). For two optional
    global definitions to be related at [i], both [RF i] and [RV i]
    should hold on the respective projections. *)

  Definition fun_of_globdef {F V} (d: globdef F V): option F :=
    match d with
      | Gfun fd => Some fd
      | Gvar _ => None
    end.

  Definition var_of_globdef {F V} (d: globdef F V): option (globvar V) :=
    match d with
      | Gfun _ => None
      | Gvar vd => Some vd
    end.

  Definition globdef_rel i:
    rel (option (globdef F1 V1)) (option (globdef F2 V2)) :=
      RF i @@ bind fun_of_globdef /\
      RV i @@ bind var_of_globdef.

  (** Consequently, it is somewhat awkward to define relational
    properties directly on the constructors of [globdef] that are
    convenient to use. Rather, the following function allows us to
    directly build optional global definitions in a way that is more
    amnenable to straightforward relational reasoning. *)

  Definition make_globdef {F V} ofd ovd: res (option (globdef F V)) :=
    match ofd, ovd with
      | OK None, OK None => OK None
      | OK (Some fd), OK None => OK (Some (Gfun fd))
      | OK None, OK (Some vd) => OK (Some (Gvar vd))
      | _, _ => Error (MSG "make_globdef: overdefinition" :: nil)
    end.

  (** Note that in addition to requiring that the arguments be
    respectively related by [RF] and [RV], we also need to prevent a
    situation where [Some] on the left causes an overdefinition
    [Error] that is not matched by [None] on the right. We achieve
    this by "capping" [RF] and [RV] at [option_le ⊤], which relates
    everything to everything, except that [None] on the right is only
    related to [None] on the left. *)

  Global Instance make_globdef_rel i:
    Monotonic
      make_globdef
      (res_le (RF i /\ option_le ⊤) ++>
       res_le (RV i /\ option_le ⊤) ++>
       res_le (globdef_rel i)).
  Proof.
    intros fd1 fd2 Hfd vd1 vd2 Hvd.
    destruct Hfd as [fd1 fd2 [Hfd Hfd'] | ];
    destruct Hvd as [vd1 vd2 [Hvd Hvd'] | ];
    try constructor.
    - destruct fd2 as [fd2|], vd2 as [vd2|]; try solve [constructor];
      destruct fd1 as [fd1|]; try solve [ inversion Hfd' ];
      destruct vd1 as [vd1|]; try solve [ inversion Hvd' ];
      constructor;
      split; simpl; monad_norm; simpl; eauto.
    - simpl.
      destruct fd2; constructor.
  Qed.

  Global Instance make_globadef_rel_params:
    Params (@make_globdef) 2.

  (** Now we define what it means for two lists of program definitions
    to be related. Each entry associated an identifier with an
    optional global definition. For our programs, we enforce a
    structure where all symbols up to [glob_threshold] appear, in
    ascending order. [globdefs_rel] assert that two lists of
    definitions have this structure up to a given identifier, and that
    corresponding definitions are related by [globdef_rel]. *)

  Inductive globdefs_rel: ident -> rel (list (ident × option (globdef F1 V1)))
                                       (list (ident × option (globdef F2 V2))) :=
    | globdefs_rel_nil:
        Monotonic
          nil
          (globdefs_rel 1%positive)
    | globdefs_rel_app i:
        Monotonic
          (fun defs def => defs ++ (i, def) :: nil)
          (globdefs_rel i ++> globdef_rel i ++> globdefs_rel (Psucc i)).

  Global Existing Instance globdefs_rel_nil.
  Global Existing Instance globdefs_rel_app.
  Global Instance globdefs_rel_app_params: Params (@app) 2.

  Lemma globdefs_rel_in_l i thr defs1 defs2:
    globdefs_rel thr defs1 defs2 ->
    Pos.lt i thr ->
    exists d, In (i, d) defs1.
  Proof.
    induction 1 as [ | j defs1 defs2 Hdefs IHdefs].
    - intros Hi.
      eelim Pos.nlt_1_r; eauto.
    - intros Hi.
      apply Pos.lt_succ_r in Hi.
      apply Pos.lt_eq_cases in Hi.
      destruct Hi as [Hi | Hi].
      + edestruct IHdefs; eauto.
        eexists.
        apply in_app; eauto.
      + clear IHdefs.
        subst.
        exists x.
        apply in_app; simpl; eauto.
  Qed.

  (** Two programs to be related when their lists of definitions to be
    related in this way up to [glob_threshold], and their [main()]
    identifiers are the same. In addition, we require that [RF] and
    [RV] related all of the non-defined symbols as well. *)

  Inductive program_rel_upto thr: rel (AST.program F1 V1) (AST.program F2 V2) :=
    | program_rel_upto_intro:
        Monotonic
          (@AST.mkprogram _ _)
          (globdefs_rel thr ++> - ==> - ==> program_rel_upto thr).

  Global Existing Instance program_rel_upto_intro.
  Global Instance program_rel_upto_intro_params: Params (@AST.mkprogram) 3.

  Record program_rel p1 p2 :=
    {
      program_rel_upto_glob_threshold :>
        program_rel_upto glob_threshold p1 p2;
      program_rel_extra_function i:
        (glob_threshold <= i)%positive ->
        RF i None None;
      program_rel_extra_variable i:
        (glob_threshold <= i)%positive ->
        RV i None None;
      program_rel_global_public:
        AST.prog_public p1 = map fst (AST.prog_defs p1);
    }.

  Global Instance prog_defs_rel:
    Monotonic
      (AST.prog_defs (F:=_) (V:=_))
      (program_rel ++> globdefs_rel glob_threshold).
  Proof.
    intros p1 p2 [Hp _ _].
    destruct Hp; eauto.
  Qed.

  Global Instance prog_defs_rel_params:
    Params (@AST.prog_defs) 1.

  Global Instance prog_main_rel:
    Monotonic
      (AST.prog_main (F:=_) (V:=_))
      (program_rel ++> eq).
  Proof.
    intros p1 p2 [Hp _ _].
    destruct Hp; eauto.
  Qed.

  Global Instance prog_main_rel_params:
    Params (@AST.prog_main) 1.
End PROGRAM_REL.

Global Instance globdef_subrel {F1 F2 V1 V2}:
  Monotonic
    (@globdef_rel F1 F2 V1 V2)
    ((- ==> subrel) ++> (- ==> subrel) ++> - ==> subrel).
Proof.
  intros RF1 RF2 HRF RV1 RV2 HRV i.
  unfold globdef_rel.
  intros x y [HRFxy HRVxy].
  split.
  - destruct x as [x|], y as [y|]; monad_norm; eapply HRF; eauto.
  - destruct x as [x|], y as [y|]; monad_norm; eapply HRV; eauto.
Qed.

Global Instance globdef_subrel_params:
  Params (@globdef_subrel) 5.

Global Instance globdefs_subrel {F1 F2 V1 V2}:
  Monotonic
    (@globdefs_rel F1 F2 V1 V2)
    ((- ==> subrel) ++> (- ==> subrel) ++> - ==> subrel).
Proof.
  intros RF1 RF2 HRF RV1 RV2 HRV i.
  intros x y H.
  induction H.
  - constructor.
  - constructor; eauto.
    eapply globdef_subrel; eauto.
Qed.

Global Instance globdefs_subrel_params:
  Params (@globdefs_rel) 5.

Global Instance program_subrel_upto {F1 F2 V1 V2}:
  Monotonic
    (@program_rel_upto F1 F2 V1 V2)
    ((- ==> subrel) ++> (- ==> subrel) ++> - ==> subrel).
Proof.
  intros RF1 RF2 HRF RV1 RV2 HRV i.
  intros x y [defs1 defs2 Hdefs main].
  constructor.
  eapply globdefs_subrel; eauto.
Qed.

Global Instance program_subrel_upto_params:
  Params (@program_rel_upto) 5.

Global Instance program_subrel {F1 F2 V1 V2}:
  Monotonic
    (@program_rel F1 F2 V1 V2)
    ((- ==> subrel) ++> (- ==> subrel) ++> subrel).
Proof.
  intros RF1 RF2 HRF RV1 RV2 HRV.
  intros x y H.
  destruct H as [Hxy HRF' HRV'].
  split; intros; eauto.
  - eapply program_subrel_upto; eauto.
  - eapply HRF; eauto.
  - eapply HRV; eauto.
Qed.

Global Instance program_subrel_params:
  Params (@program_rel) 4.

(** ** Global environments *)

Section GLOBALENV_DEFS.
  Context {F V: Type}.

  (** Thanks to our fixed structure, the mapping between identifiers
    and blocks is always the following one. *)

  Definition find_symbol_upto (thr: ident) (i: ident): option block :=
    if decide (i < thr)%positive then Some i else None.

  Definition find_symbol :=
    find_symbol_upto glob_threshold.

  (** Based on this fixed structure, we can defined a general notion
    of a global block. *)

  Definition block_is_global b :=
    (b < glob_threshold)%positive.

  Global Instance block_is_global_dec b:
    Decision (block_is_global b) := _.

  Lemma block_is_global_find_symbol b:
    block_is_global b ->
    exists i, find_symbol i = Some b.
  Proof.
    exists b.
    unfold find_symbol, find_symbol_upto.
    destruct (decide _); eauto.
    contradiction.
  Qed.

  Lemma find_symbol_block_is_global i b:
    find_symbol i = Some b ->
    block_is_global b.
  Proof.
    unfold find_symbol, find_symbol_upto.
    destruct (decide _); try discriminate.
    congruence.
  Qed.

  (** The 1:1 mapping replaced our use of so-called "stencils", which
    placed constraints on the structures of the global environments we
    use. We no longer use stencils, but these definitions are convenient
    for updating code that used to rely on [stencil_matches], and
    capture the "fixed structure" part of our relation on global
    environments. *)

  Record stencil_matches_upto (thr: ident) (ge: Senv.t) :=
    {
      stencil_matches_symbols_upto i:
        Senv.find_symbol ge i = find_symbol_upto thr i;
      stencil_matches_senv_next:
        Senv.nextblock ge = thr
    }.

  Record stencil_matches ge :=
    {
      stencil_matches_upto_glob_threshold :>
        stencil_matches_upto glob_threshold ge;
      stencil_matches_global_public i b:
        find_symbol i = Some b ->
        Senv.public_symbol ge i = true;
    }.

  Global Instance stencil_matches_upto_equiv:
    Monotonic stencil_matches_upto (- ==> Senv.equiv ++> iff).
  Proof.
    repeat rstep.
    red in H.
    decompose [and] H.
    split; destruct 1; constructor; eauto; congruence.
  Qed.

  Global Instance stencil_matches_equiv:
    Monotonic stencil_matches (Senv.equiv ++> iff).
  Proof.
    repeat rstep.
    pose proof H as H'.
    destruct H' as (? & ? & ? & ?).
    split; destruct 1 as [Hu Hp]; constructor; eauto.
    - rewrite <- H; eauto.
    - revert Hu.
      rewrite H.
      tauto.
  Qed.

  Lemma stencil_matches_find_symbol ge:
    stencil_matches ge ->
    forall i, Senv.find_symbol ge i = find_symbol i.
  Proof.
    intros.
    apply stencil_matches_symbols_upto.
    apply H.
  Qed.

  Lemma stencil_matches_upto_genv_next thr (ge: Genv.t F V):
    stencil_matches_upto thr (Genv.to_senv ge) ->
    Genv.genv_next ge = thr.
  Proof.
    apply stencil_matches_senv_next.
  Qed.

  Lemma stencil_matches_genv_next (ge: Genv.t F V):
    stencil_matches (Genv.to_senv ge) ->
    Genv.genv_next ge = glob_threshold.
  Proof.
    intros.
    apply stencil_matches_upto_genv_next.
    apply H.
  Qed.

  Lemma stencil_matches_symbols (ge: Genv.t F V):
    stencil_matches (Genv.to_senv ge) ->
    forall i, Genv.find_symbol ge i = find_symbol i.
  Proof.
    apply stencil_matches_find_symbol.
  Qed.

  Lemma genv_find_symbol_block_is_global ge i b:
    stencil_matches ge ->
    Senv.find_symbol ge i = Some b ->
    block_is_global b.
  Proof.
    intros Hge Hb.
    rewrite stencil_matches_find_symbol in Hb; eauto.
    eapply find_symbol_block_is_global; eauto.
  Qed.

  Lemma find_funct_ptr_block_is_global (ge: Genv.t F V) b f:
    stencil_matches (Genv.to_senv ge) ->
    Genv.find_funct_ptr ge b = Some f ->
    block_is_global b.
  Proof.
    intros Hge Hb.
    unfold Genv.find_funct_ptr in Hb.
    destruct (Genv.find_def ge b) eqn:Hb'; try discriminate.
    apply Genv.genv_defs_range in Hb'.
    erewrite stencil_matches_genv_next in Hb' by eassumption.
    assumption.
  Qed.

  Lemma find_var_info_block_is_global (ge: Genv.t F V) b gv:
    stencil_matches (Genv.to_senv ge) ->
    Genv.find_var_info ge b = Some gv ->
    block_is_global b.
  Proof.
    intros Hge Hb.
    unfold Genv.find_var_info in Hb.
    destruct (Genv.find_def ge b) eqn:Hb'; try discriminate.
    apply Genv.genv_defs_range in Hb'.
    erewrite stencil_matches_genv_next in Hb' by eassumption.
    assumption.
  Qed.

  Lemma block_not_global_find_var_info (ge: Genv.t F V) b:
    stencil_matches (Genv.to_senv ge) ->
    ~ block_is_global b ->
    Genv.find_var_info ge b = None.
  Proof.
    intros Hge Hb.
    pose proof (find_var_info_block_is_global ge b).
    destruct (Genv.find_var_info ge b).
    - exfalso; eauto.
    - reflexivity.
  Qed.
End GLOBALENV_DEFS.

(** Now we can define the relation on global environments. *)

Section GLOBALENV_REL.
  Context {F1 F2 V1 V2: Type}.
  Context (RF: ident -> rel (option F1) (option F2)).
  Context (RV: ident -> rel (option (globvar V1)) (option (globvar V2))).

  Record genv_rel_upto thr (ge1 ge2: Genv.t _ _): Prop :=
    {
      genv_rel_upto_stencil_matches_l:
        stencil_matches_upto thr ge1;
      genv_rel_upto_stencil_matches_r:
        stencil_matches_upto thr ge2;
      genv_rel_upto_find_funct_ptr i b:
        find_symbol_upto thr i = Some b ->
        RF i (Genv.find_funct_ptr ge1 b)
             (Genv.find_funct_ptr ge2 b);
      genv_rel_upto_find_var_info i b:
        find_symbol_upto thr i = Some b ->
        RV i (Genv.find_var_info ge1 b)
             (Genv.find_var_info ge2 b)
    }.

  Record genv_rel ge1 ge2 :=
    {
      genv_rel_upto_glob_threshold :>
        genv_rel_upto glob_threshold ge1 ge2;
      genv_rel_extra_function i:
        find_symbol i = None ->
        RF i None None;
      genv_rel_extra_variable i:
        find_symbol i = None ->
        RV i None None;
      genv_rel_public:
        Genv.genv_public ge1 = Genv.genv_public ge2;
      genv_rel_global_public_l i b:
        find_symbol i = Some b ->
        Genv.public_symbol ge1 i = true;
    }.

  Instance genv_public_symbol_rel:
    Monotonic (@Genv.public_symbol _ _) (genv_rel ++> - ==> eq)%rel.
  Proof.
    intros ge1 ge2 Hge i.
    unfold Genv.public_symbol.
    change (Genv.find_symbol ge1 i) with
           (Senv.find_symbol (Genv.to_senv ge1) i).
    erewrite stencil_matches_symbols_upto
      by (eapply genv_rel_upto_stencil_matches_l, genv_rel_upto_glob_threshold;
          eauto).
    change (Genv.find_symbol ge2 i) with
           (Senv.find_symbol (Genv.to_senv ge2) i).
    erewrite stencil_matches_symbols_upto
      by (eapply genv_rel_upto_stencil_matches_r, genv_rel_upto_glob_threshold;
          eauto).
    destruct (find_symbol_upto _); eauto.
    erewrite genv_rel_public; eauto.
  Qed.

  Instance genv_public_symbol_rel_params:
    Params (@Genv.public_symbol) 2.

  Lemma genv_rel_global_public_r ge1 ge2:
    genv_rel ge1 ge2 ->
    forall i b,
      find_symbol i = Some b ->
      Genv.public_symbol ge2 i = true.
  Proof.
    intros.
    cut (Genv.public_symbol ge1 i = true); [rauto|].
    eapply genv_rel_global_public_l; eauto.
  Qed.

  Lemma genv_le_stencil_matches_l ge1 ge2:
    genv_rel ge1 ge2 ->
    stencil_matches ge1.
  Proof.
    intros Hge.
    split.
    - eapply genv_rel_upto_stencil_matches_l; eauto.
      eapply genv_rel_upto_glob_threshold; eauto.
    - eapply genv_rel_global_public_l; eauto.
  Qed.

  Lemma genv_le_stencil_matches_r ge1 ge2:
    genv_rel ge1 ge2 ->
    stencil_matches ge2.
  Proof.
    intros Hge.
    split.
    - eapply genv_rel_upto_stencil_matches_r; eauto.
      eapply genv_rel_upto_glob_threshold; eauto.
    - eapply genv_rel_global_public_r; eauto.
  Qed.

  (** We can combine the properties about global identifiers and
    out-of-range identifiers in the following way. *)

  Lemma genv_rel_find_funct_ptr ge1 ge2 i:
    genv_rel ge1 ge2 ->
    RF i (b <- Genv.find_symbol ge1 i; Genv.find_funct_ptr ge1 b)
         (b <- Genv.find_symbol ge2 i; Genv.find_funct_ptr ge2 b).
  Proof.
    intros Hge.
    pose proof (genv_le_stencil_matches_l ge1 ge2 Hge) as Hge1.
    pose proof (genv_le_stencil_matches_r ge1 ge2 Hge) as Hge2.
    rewrite !stencil_matches_symbols by eauto.
    destruct (find_symbol i) eqn:Hi; monad_norm.
    - eapply genv_rel_upto_find_funct_ptr.
      eapply genv_rel_upto_glob_threshold; eauto.
      assumption.
    - eapply genv_rel_extra_function; eauto.
  Qed.

  Lemma genv_rel_find_var_info ge1 ge2 i:
    genv_rel ge1 ge2 ->
    RV i (b <- Genv.find_symbol ge1 i; Genv.find_var_info ge1 b)
         (b <- Genv.find_symbol ge2 i; Genv.find_var_info ge2 b).
  Proof.
    intros Hge.
    pose proof (genv_le_stencil_matches_l ge1 ge2 Hge) as Hge1.
    pose proof (genv_le_stencil_matches_r ge1 ge2 Hge) as Hge2.
    rewrite !stencil_matches_symbols by eauto.
    destruct (find_symbol i) eqn:Hi; monad_norm.
    - eapply genv_rel_upto_find_var_info.
      eapply genv_rel_upto_glob_threshold; eauto.
      assumption.
    - eapply genv_rel_extra_variable; eauto.
  Qed.

  (** TODO: we could generalize the properties for [find_symbol] and
    [genv_next] to [genv_rel_upto] rather than only declare them for
    [genv_le] below. *)

  (** ** Monotonicity of [Genv.globalenv] *)

  (** Now we prove the monotonicity of [Genv.globalenv] in terms of
    the relations defined above. First we show that [Genv.add_global]
    preserves the relevant invariants. Because its definition is
    somewhat low-level and complicated, this is somewhat painful, but
    once we're done with that the rest follows the structure of our
    relations nicely. *)

  Lemma genv_add_global_stencil_matches_upto {F V} (ge: Genv.t F V) i def:
    stencil_matches_upto i ge ->
    stencil_matches_upto (Psucc i) (Genv.add_global ge (i, def)).
  Proof.
    intros [Hsymb Hnext].
    split; simpl.
    - unfold Genv.find_symbol, Genv.add_global; simpl.
      intros j.
      destruct (decide (j = i)) as [Hij|Hij].
      + rewrite Hij in *; clear j Hij.
        rewrite Maps.PTree.gss.
        unfold find_symbol_upto.
        pose proof (Pos.lt_succ_diag_r i).
        destruct (decide _); try contradiction.
        f_equal.
        assumption.
      + rewrite Maps.PTree.gso by assumption.
        unfold find_symbol_upto in *.
        specialize (Hsymb j).
        destruct (decide (j < i)%positive) as [Hij'|Hij'];
        destruct (decide (j < Psucc i)%positive) as [Hij''|Hij''];
        try xomega;
        try assumption.
        * apply Pos.le_nlt in Hij'.
          apply Pos.lt_succ_r in Hij''.
          elim Hij.
          apply Pos.le_antisym; assumption.
    - unfold Genv.add_global; simpl.
      f_equal.
      assumption.
  Qed.

  Lemma genv_add_global_rel i:
    Monotonic
      (fun ge def => Genv.add_global ge (i, def))
      (genv_rel_upto i ++> globdef_rel RF RV i ++> genv_rel_upto (Psucc i)).
  Proof.
    intros ge1 ge2 Hge def1 def2 Hdef.
    destruct Hge as [Hge1 Hge2 Hf Hv]; split.
    - eapply genv_add_global_stencil_matches_upto; assumption.
    - eapply genv_add_global_stencil_matches_upto; assumption.
    - intros j b.
      specialize (Hf j b).
      clear Hv.
      unfold find_symbol_upto in *.
      destruct (decide (j < Pos.succ i)%positive); try discriminate.
      intros Hjb; inversion Hjb; clear Hjb; subst.
      destruct (decide (b = i)) as [Hbi|Hbi]; subst.
      + clear Hf l.
        unfold Genv.find_funct_ptr, Genv.find_def, Genv.add_global; simpl.
        erewrite !stencil_matches_upto_genv_next by eassumption.
        assert (Hf1: Maps.PTree.get i (Genv.genv_defs ge1) = None).
        {
          pose proof (Genv.genv_defs_range ge1 i) as H1.
          destruct (Maps.PTree.get i (Genv.genv_defs ge1)); try reflexivity.
          specialize (H1 g eq_refl).
          erewrite stencil_matches_upto_genv_next in H1 by eassumption.
          xomega.
        }
        assert (Hf2: Maps.PTree.get i (Genv.genv_defs ge2) = None).
        {
          pose proof (Genv.genv_defs_range ge2 i) as H2.
          destruct (Maps.PTree.get i (Genv.genv_defs ge2)); try reflexivity.
          specialize (H2 g eq_refl).
          erewrite stencil_matches_upto_genv_next in H2 by eassumption.
          xomega.
        }
        destruct Hdef as [Hf _].
        destruct def1 as [[|]|], def2 as [[|]|];
          rewrite ?Maps.PTree.gss, ?Hf1, ?Hf2;
          assumption.
      + unfold Genv.find_funct_ptr, Genv.add_global; simpl.
        assert (b < i)%positive.
        {
          apply Pos.lt_succ_r in l.
          destruct (decide (b < i))%positive; eauto.
          eapply Pos.le_nlt in n.
          elim Hbi; apply Pos.le_antisym; eauto.
        }
        destruct (decide (b < i))%positive; try contradiction.
        specialize (Hf eq_refl).
        pose proof (stencil_matches_upto_genv_next _ _ Hge1).
        pose proof (stencil_matches_upto_genv_next _ _ Hge2).
        destruct def1 as [[|]|], def2 as [[|]|];
          unfold Genv.find_def;
          simpl;
          rewrite ?Maps.PTree.gso by congruence;
          try assumption.
    - intros j b.
      specialize (Hv j b).
      clear Hf.
      unfold find_symbol_upto in *.
      destruct (decide (j < Pos.succ i)%positive); try discriminate.
      intros Hjb; inversion Hjb; clear Hjb; subst.
      destruct (decide (b = i)) as [Hbi|Hbi]; subst.
      + clear Hv l.
        unfold Genv.find_var_info, Genv.find_def, Genv.add_global; simpl.
        erewrite !stencil_matches_upto_genv_next by eassumption.
        assert (Hv1: Maps.PTree.get i (Genv.genv_defs ge1) = None).
        {
          pose proof (Genv.genv_defs_range ge1 i) as H1.
          destruct (Maps.PTree.get i (Genv.genv_defs ge1)); try reflexivity.
          specialize (H1 g eq_refl).
          erewrite stencil_matches_upto_genv_next in H1 by eassumption.
          xomega.
        }
        assert (Hv2: Maps.PTree.get i (Genv.genv_defs ge2) = None).
        {
          pose proof (Genv.genv_defs_range ge2 i) as H2.
          destruct (Maps.PTree.get i (Genv.genv_defs ge2)); try reflexivity.
          specialize (H2 g eq_refl).
          erewrite stencil_matches_upto_genv_next in H2 by eassumption.
          xomega.
        }
        destruct Hdef as [_ Hv].
        destruct def1 as [[|]|], def2 as [[|]|];
          rewrite ?Maps.PTree.gss, ?Hv1, ?Hv2;
          assumption.
      + unfold Genv.find_var_info, Genv.add_global; simpl.
        assert (b < i)%positive.
        {
          apply Pos.lt_succ_r in l.
          destruct (decide (b < i))%positive; eauto.
          eapply Pos.le_nlt in n.
          elim Hbi; apply Pos.le_antisym; eauto.
        }
        destruct (decide (b < i))%positive; try contradiction.
        specialize (Hv eq_refl).
        pose proof (stencil_matches_upto_genv_next _ _ Hge1).
        pose proof (stencil_matches_upto_genv_next _ _ Hge2).
        destruct def1 as [[|]|], def2 as [[|]|];
          unfold Genv.find_def;
          simpl;
          rewrite ?Maps.PTree.gso by congruence;
          assumption.
  Qed.

  Lemma genv_empty_genv_stencil_matches {F V} pub:
    stencil_matches_upto 1%positive (Genv.empty_genv F V pub).
  Proof.
    split.
    - unfold Genv.find_symbol, find_symbol_upto.
      intro i.
      destruct (decide (i < 1)%positive); try xomega.
      simpl.
      apply Maps.PTree.gempty.
    - reflexivity.
  Qed.

  Global Instance genv_empty_genv_rel pub:
    Monotonic
      (Genv.empty_genv _ _ pub)
      (genv_rel_upto 1%positive).
  Proof.
    split.
    - apply genv_empty_genv_stencil_matches.
    - apply genv_empty_genv_stencil_matches.
    - intros i b.
      unfold find_symbol_upto.
      destruct (decide (i < 1)%positive); try xomega.
      discriminate.
    - intros i b.
      unfold find_symbol_upto.
      destruct (decide (i < 1)%positive); try xomega.
      discriminate.
  Qed.

  Global Instance genv_add_globals_rel n:
    Monotonic
      (@Genv.add_globals _ _)
      (genv_rel_upto 1%positive ++> globdefs_rel RF RV n ++> genv_rel_upto n).
  Proof.
    intros ge1 ge2 Hge.
    eapply Pos.peano_ind with (p := n); clear n.
    - inversion 1; subst; simpl.
      + assumption.
      + eelim Pos.succ_not_1; eauto.
    - intros n IHn.
      inversion 1; subst; simpl.
      + eelim Pos.succ_not_1; eauto.
      + eapply Pos.succ_inj in H0; subst.
        unfold Genv.add_globals in *.
        rewrite !fold_left_app; simpl.
        eapply genv_add_global_rel; eauto.
  Qed.

  Global Instance genv_add_globals_rel_params:
    Params (@Genv.add_globals) 2.

  Lemma genv_globalenv_rel_upto n:
    Monotonic
      (@Genv.globalenv _ _)
      (program_rel_upto RF RV n ++> genv_rel_upto n).
  Proof.
    intros ? ? [p1 p2 Hp pub i].
    unfold Genv.globalenv; simpl.
    solve_monotonic.
  Qed.

  Global Instance genv_globalenv_rel:
    Monotonic
      (@Genv.globalenv _ _)
      (program_rel RF RV ++> genv_rel).
  Proof.
    intros p1 p2 [Hp Hef Hev Hpub].
    constructor.
    - apply genv_globalenv_rel_upto.
      assumption.
    - unfold find_symbol, find_symbol_upto.
      intros i.
      destruct (decide (i < glob_threshold)%positive); inversion 1.
      eapply Hef; xomega.
    - unfold find_symbol, find_symbol_upto.
      intros i.
      destruct (decide (i < glob_threshold)%positive); inversion 1.
      eapply Hev; xomega.
    - rewrite ! Genv.globalenv_public. inv Hp. reflexivity.
    - unfold find_symbol.
      intros i b Hib.
      assert (Hib': Senv.find_symbol (Genv.globalenv p1) i = Some b).
      {
        erewrite stencil_matches_symbols_upto; eauto.
        eapply genv_globalenv_rel_upto; eauto.
      }
      simpl in Hib'.
      unfold find_symbol_upto in Hib.
      destruct (decide (i < glob_threshold)%positive); inversion Hib.
      subst b; clear Hib.
      unfold Genv.public_symbol.
      rewrite Hib'.
      destruct (in_dec _ _ _) as [Hi|Hi].
      + reflexivity.
      + elim Hi; clear Hi.
        rewrite Genv.globalenv_public.
        rewrite Hpub.
        destruct Hp as [defs1 defs2 Hdefs pub main]; simpl in *.
        edestruct (globdefs_rel_in_l RF RV) as [d Hd]; eauto.
        eapply (in_map fst) in Hd; eauto.
  Qed.

  Global Instance genv_globalenv_rel_params:
    Params (@Genv.globalenv) 1.
End GLOBALENV_REL.

Hint Resolve program_rel_upto_glob_threshold.
Hint Resolve genv_rel_upto_glob_threshold.
Hint Resolve genv_le_stencil_matches_l.
Hint Resolve genv_le_stencil_matches_r.
Hint Resolve find_symbol_block_is_global.
Hint Resolve genv_find_symbol_block_is_global.
Hint Resolve find_funct_ptr_block_is_global.
Hint Resolve find_var_info_block_is_global.


(** ** Additional definitions *)

(** Most of the time we don't need the full flexibility of [genv_rel]
  and [program_rel]. The following specialization is a common pattern
  that is sufficient for most of our uses and that has better
  properties: both programs are of the same kind, the relations are
  obtained with [option_le] so that definitions can be freely added to
  the right-hand side. *)

Definition program_le {F V} Rf :=
  @program_rel F F V V
    (fun i => option_le (Rf i))
    (fun i => option_le eq).

Definition genv_le {F V} Rf :=
  @genv_rel F F V V
    (fun i => option_le (Rf i))
    (fun i => option_le eq).

Lemma genv_symb_range i b:
  find_symbol i = Some b ->
  Plt b glob_threshold.
Proof.
  unfold find_symbol, find_symbol_upto.
  destruct (Decision.decide _); try discriminate.
  inversion 1; subst.
  assumption.
Qed.

Lemma genv_vars_inj id1 id2 b:
  find_symbol id1 = Some b ->
  find_symbol id2 = Some b ->
  id1 = id2.
Proof.
  unfold find_symbol, find_symbol_upto.
  destruct (decide (id1 < glob_threshold))%positive; try discriminate.
  destruct (decide (id2 < glob_threshold))%positive; try discriminate.
  congruence.
Qed.

Global Opaque find_symbol block_is_global.

(** While [genv_le] is not reflexive, global environments which
  satisfy [stencil_matches] are proper elements. *)

Lemma genv_le_proper {F V} (ge: Genv.t F V):
  stencil_matches ge ->
  Proper (genv_le (fun _ => ⊤))%rel ge.
Proof.
  intros [Hge Hpub].
  split; [split | ..]; eauto.
  - intros.
    destruct (Genv.find_funct_ptr ge b); constructor.
    constructor.
  - intros.
    destruct (Genv.find_var_info ge b); repeat constructor.
  - constructor.
  - repeat constructor.
Qed.

Global Instance genv_le_trans {F V} R:
  (forall i, Transitive (R i)) ->
  Transitive (@genv_le F V R).
Proof.
  intros HR ge1 ge2 ge3 [Hge12 _ _] [Hge23 Hef Hev].
  split; eauto.
  destruct Hge12 as [Hl12 Hr12 Hf12 Hv12], Hge23 as [Hl23 Hr23 Hf23 Hv23].
  constructor; eauto.
  - intros; ehtransitivity; eauto.
  - intros i b Hi.
    etransitivity; eauto.
  - congruence.
Qed.

(** XXX: we should use [option_rel] here and rely on subrelation support *)
Global Instance genv_find_symbol_le {F V} R:
  Monotonic (@Genv.find_symbol F V) (genv_le R ++> - ==> option_le eq).
Proof.
  intros ge1 ge2 [[Hge1 Hge2 _ _] _ _] i.
  change (Genv.find_symbol ge1) with (Senv.find_symbol ge1).
  change (Genv.find_symbol ge2) with (Senv.find_symbol ge2).
  erewrite !stencil_matches_symbols_upto by eassumption.
  reflexivity.
Qed.

Global Instance: Params (@Genv.find_symbol) 2.

Global Instance genv_public_symbol_leb {F V} R:
  Monotonic (@Genv.public_symbol F V) (genv_le R ++> - ==> leb).
Proof.
  intros ge1 ge2 GR i. inv GR.
  destruct (Genv.public_symbol ge1 i) eqn:?; simpl in *; eauto.
  unfold Genv.public_symbol in *.
  inv genv_rel_upto_glob_threshold0.
  inv genv_rel_upto_stencil_matches_l0.
  inv genv_rel_upto_stencil_matches_r0.
  change (Genv.find_symbol ge1) with (Senv.find_symbol ge1) in Heqb.
  change (Genv.find_symbol ge2) with (Senv.find_symbol ge2).
  rewrite stencil_matches_symbols_upto0 in Heqb.
  rewrite stencil_matches_symbols_upto1.
  rewrite <- genv_rel_public0. auto.
Qed.

Global Instance: Params (@Genv.public_symbol) 2.

(* The statement of these lemmas conflate [ident] and [block].
  We may want to update that at some point. *)

Global Instance genv_find_funct_ptr_le {F V} R:
  Monotonic
    (@Genv.find_funct_ptr F V)
    (genv_le R ++> forallr - @ b, option_le (R b)).
Proof.
  intros ge1 ge2 Hge i.
  pose proof (genv_rel_upto_find_funct_ptr _ _ _ _ _ Hge i i).
  unfold find_symbol_upto in *.
  destruct (decide (i < glob_threshold)%positive) as [Hi|Hi].
  - eauto.
  - clear H.
    destruct (Genv.find_funct_ptr ge1 i) eqn:Hi1; try constructor.
    eapply find_funct_ptr_block_is_global in Hi1.
    + elim Hi.
      eassumption.
    + eapply genv_le_stencil_matches_l.
      eassumption.
Qed.

Global Instance: Params (@Genv.find_funct_ptr) 2.

Global Instance genv_find_var_info_le {F V} R:
  Monotonic (@Genv.find_var_info F V) (genv_le R ++> - ==> option_le eq).
Proof.
  intros ge1 ge2 Hge i.
  pose proof (genv_rel_upto_find_var_info _ _ _ _ _ Hge i i).
  unfold find_symbol_upto in *.
  destruct (decide (i < glob_threshold)%positive) as [Hi|Hi].
  - eauto.
  - clear H.
    destruct (Genv.find_var_info ge1 i) eqn:Hi1; try constructor.
    eapply find_var_info_block_is_global in Hi1.
    + elim Hi.
      eassumption.
    + eapply genv_le_stencil_matches_l.
      eassumption.
Qed.

Global Instance: Params (@Genv.find_var_info) 2.

Global Instance genv_next_le {F V} R:
  Monotonic (@Genv.genv_next F V) (genv_le R ++> eq).
Proof.
  intros ge1 ge2 Hge.
  erewrite !stencil_matches_genv_next.
  - reflexivity.
  - eapply genv_le_stencil_matches_r; eauto.
  - eapply genv_le_stencil_matches_l; eauto.
Qed.

Global Instance: Params (@Genv.genv_next) 1.

(* XXX Need block_is_volatile update in Compcert *)
(*
Global Instance block_is_volatile_le {F V} R:
  Monotonic (@Genv.block_is_volatile F V) (genv_le R ++> - ==> option_le eq).
Proof.
  intros ge1 ge2 Hge i.
  pose proof (genv_rel_upto_find_var_info _ _ _ _ _ Hge i i).
  pose proof (genv_rel_upto_find_funct_ptr _ _ _ _ _ Hge i i) as U.
  unfold find_symbol_upto in *.
  unfold Events.block_is_volatile.
  erewrite stencil_matches_genv_next by (eapply genv_rel_upto_stencil_matches_l; eauto).
  erewrite stencil_matches_genv_next by (eapply genv_rel_upto_stencil_matches_r; eauto).
  destruct (decide (i < glob_threshold)%positive) as [Hi|Hi].
  - destruct (Genv.find_var_info ge1 i) eqn:VAR.
    { transport VAR. subst. rewrite H0. reflexivity. }
    destruct (Genv.find_funct_ptr ge1 i) eqn:FUN.
    { transport FUN. rewrite H0.
      destruct (Genv.find_var_info ge2 i) eqn:VAR2; try reflexivity.
      exploit Genv.genv_funs_vars; eauto. contradiction.
    }
    destruct (plt i glob_threshold); try contradiction.
    constructor.
  - clear H.
    clear U.
    destruct (Genv.find_var_info ge1 i) eqn:Hi1.
    {
      eapply Genv.genv_vars_range in Hi1.
      erewrite stencil_matches_genv_next in Hi1.
      + elim Hi.
        eassumption.
      + eapply genv_le_stencil_matches_l.
        eassumption.
    }
    destruct (Genv.find_var_info ge2 i) eqn:Hi2.
    {
      eapply Genv.genv_vars_range in Hi2.
      erewrite stencil_matches_genv_next in Hi2.
      + elim Hi.
        eassumption.
      + eapply genv_le_stencil_matches_r.
        eassumption.
    }
    destruct (Genv.find_funct_ptr ge1 i) eqn:FUN.
    {
      eapply Genv.genv_funs_range in FUN.
      erewrite stencil_matches_genv_next in FUN.
      + elim Hi.
        eassumption.
      + eapply genv_le_stencil_matches_l.
        eassumption.
    }
    destruct (Genv.find_funct_ptr ge2 i) eqn:FUN2.
    {
      eapply Genv.genv_funs_range in FUN2.
      erewrite stencil_matches_genv_next in FUN2.
      + elim Hi.
        eassumption.
      + eapply genv_le_stencil_matches_r.
        eassumption.
    }
    reflexivity.
Qed.

Global Instance: Params (@Events.block_is_volatile) 2.
*)

Lemma genv_le_find_symbol_some {F V} R (ge ge': Genv.t F V) i b:
  genv_le R ge ge' ->
  Genv.find_symbol ge i = Some b ->
  Genv.find_symbol ge' i = Some b.
Proof.
  intros ? FIND.
  transport FIND.
  congruence.
Qed.

Lemma genv_le_find_var_info_some {F V} R (ge ge': Genv.t F V) b v:
  genv_le R ge ge' ->
  Genv.find_var_info ge b = Some v ->
  Genv.find_var_info ge' b = Some v.
Proof.
  intros LE VAR.
  transport VAR.
  congruence.
Qed.

Lemma genv_le_find_funct_ptr_some {F V} (ge ge': Genv.t F V) b f:
  genv_le (fun _ => eq) ge ge' ->
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr ge' b = Some f.
Proof.
  intros LE FUN.
  transport FUN.
  congruence.
Qed.


(** * Clight signatures *)

Record csignature :=
  {
    csig_args: Ctypes.typelist;
    csig_res: Ctypes.type;
    csig_cc: calling_convention
  }.

(** ** Decision procedures *)

Instance int_dec: EqDec int := Int.eq_dec.
Instance int64_dec: EqDec int64 := Int64.eq_dec.
Instance float_dec: EqDec float := Float.eq_dec.
Instance float32_dec: EqDec float32 := Float32.eq_dec.
Instance ptrofs_dec: EqDec ptrofs := Ptrofs.eq_dec.

Instance init_data_dec:
  EqDec AST.init_data.
Proof.
  intros id1 id2.
  red; decide equality; apply (decide _).
Defined.

Instance globvar_dec {V} `{EqDec V}:
  EqDec (globvar V).
Proof.
  intros v1 v2.
  red; decide equality; apply (decide _).
Defined.

Instance globdef_dec {F V} `{EqDec F} `{EqDec V}:
  EqDec (globdef F V).
Proof.
  intros d1 d2.
  red; decide equality; apply (decide _).
Defined.

Global Instance calling_convention_eq_dec: EqDec calling_convention :=
  fun cc1 cc2 =>
    if decide (cc_vararg cc1 = cc_vararg cc2 /\
               cc_unproto cc1 = cc_unproto cc2 /\
               cc_structret cc1 = cc_structret cc2) then left _ else right _.
Proof.
  abstract (destruct a as (? & ? & ?), cc1, cc2; f_equal; assumption).
  abstract (intro; subst; auto).
Defined.

Global Instance typ_eq_dec: EqDec typ := typ_eq.
Global Instance type_eq_dec: EqDec type := type_eq.
Global Instance typelist_eq_dec: EqDec typelist := typelist_eq.

Global Instance csig_eq_dec:
  EqDec csignature.
Proof.
  intros sig1 sig2.
  destruct sig1 as [args1 res1 cc1].
  destruct sig2 as [args2 res2 cc2].
  destruct (decide (args1 = args2 /\ res1 = res2 /\ cc1 = cc2)).
  * left.
    abstract (f_equal; tauto).
  * right.
    abstract (injection 1; tauto).
Defined.

(** ** Helper functions *)

Definition mkcsig (args: Ctypes.typelist) (res: Ctypes.type): csignature :=
  {|
    csig_args := args;
    csig_res := res;
    csig_cc := cc_default
  |}.

Definition csig_union (sig1 sig2: csignature): res csignature :=
  _ <- eassert (MSG "signature mismatch" :: nil) (sig1 = sig2);
  ret sig1.

Definition csig_sig (csig: csignature): signature :=
  signature_of_type (csig_args csig) (csig_res csig) (csig_cc csig).


(** * Injection-related properties *)

Section INJECT.
  Context `{Hmem: Mem.MemoryModelX}.

  Global Instance val_inject_lessdef f:
    Proper (Val.lessdef --> Val.lessdef ++> impl) (Val.inject f).
  Proof.
    intros v1' v1 Hv1 v2' v2 Hv2 Hv.
    apply val_inject_lessdef in Hv1.
    apply val_inject_lessdef in Hv2.
    replace f with (compose_meminj inject_id (compose_meminj f inject_id)).
    * eapply val_inject_compose; eauto.
      eapply val_inject_compose; eauto.
    * apply Axioms.functional_extensionality.
      intros b.
      unfold compose_meminj, inject_id.
      destruct (f b) as [[]|]; eauto.
      replace (0 + (z + 0))%Z with z by xomega.
      reflexivity.
  Qed.

  Global Instance flat_inj_incr:
    Proper (Pos.le ++> inject_incr) Mem.flat_inj.
  Proof.
    unfold Mem.flat_inj.
    intros m n Hmn b b' delta Hmb.
    destruct (plt b m); inversion Hmb; subst.
    destruct (plt b' n); eauto.
    xomega.
  Qed.

  Global Instance pregmap_set_inject f:
    Monotonic
      (@Pregmap.set val)
      (eq ==> Val.inject f ++> (- ==> Val.inject f) ++> (- ==> Val.inject f)).
  Proof.
    intros r1 r Hr v1 v2 Hv rs1 rs2 Hrs r'; subst.
    unfold Pregmap.set.
    destruct (PregEq.eq r' r); subst; eauto.
  Qed.

  Lemma list_val_inject_eq_val_list_inject f:
    Val.inject_list f = list_rel (Val.inject f).
  Proof.
    apply eqrel_eq.
    split;
    intros l1 l2 Hl;
    induction Hl;
    constructor;
    eauto.
  Qed.

  Global Instance list_val_inject_val_list_inject f:
    Related (Val.inject_list f) (list_rel (Val.inject f)) subrel.
  Proof.
    rewrite list_val_inject_eq_val_list_inject.
    red.
    reflexivity.
  Qed.

  (** ** Lemmas about [extcall_arguments] *)

  Lemma extcall_arg_arg_inject f loc rs1 rs2 m1 m2 v1 v2:
    extcall_arg rs1 m1 loc v1 ->
    extcall_arg rs2 m2 loc v2 ->
    (- ==> Val.inject f)%rel rs1 rs2 ->
    Mem.inject f m1 m2 ->
    Val.inject f v1 v2.
  Proof.
    intros Hv1 Hv2 Hrs Hm.
    destruct Hv1; inversion Hv2; subst.
    * apply Hrs.
    * edestruct Mem.loadv_inject as (v2' & Hv2' & Hv); eauto.
      + apply Val.offset_ptr_inject; eauto.
      + congruence.
  Qed.

  Lemma extcall_arg_arg_pair_inject f loc rs1 rs2 m1 m2 v1 v2:
    extcall_arg_pair rs1 m1 loc v1 ->
    extcall_arg_pair rs2 m2 loc v2 ->
    (- ==> Val.inject f)%rel rs1 rs2 ->
    Mem.inject f m1 m2 ->
    Val.inject f v1 v2.
  Proof.
    intros Hv1 Hv2 Hrs Hm.
    destruct Hv1; inversion Hv2; subst.
    * eapply extcall_arg_arg_inject; eauto.
    * eapply Val.longofwords_inject;
      eapply extcall_arg_arg_inject; eauto.
  Qed.

  Lemma extcall_arguments_vargs_inject f sg rs1 rs2 m1 m2 vargs1 vargs2:
    (- ==> Val.inject f)%rel rs1 rs2 ->
    Mem.inject f m1 m2 ->
    extcall_arguments rs1 m1 sg vargs1 ->
    extcall_arguments rs2 m2 sg vargs2 ->
    Val.inject_list f vargs1 vargs2.
  Proof.
    unfold extcall_arguments.
    revert vargs1 vargs2.
    induction (Conventions1.loc_arguments sg) as [ | loc locs IHlocs];
    intros vargs1 vargs2 Hrs Hm Hargs1 Hargs2.
    * inversion Hargs1.
      inversion Hargs2.
      constructor.
    * inversion Hargs1 as [ | loc1 locs1 v1 vargs1' Hv1 Hvargs1']; subst.
      inversion Hargs2 as [ | loc2 locs2 v2 vargs2' Hv2 Hvargs2']; subst.
      constructor; eauto.
      eapply extcall_arg_arg_pair_inject; eauto.
  Qed.

  Lemma extcall_arg_inject f rs1 m1 rs2 m2 loc varg1:
    (forall r, Val.inject f (rs1 r) (rs2 r)) ->
    Mem.inject f m1 m2 ->
    extcall_arg rs1 m1 loc varg1 ->
    exists varg2,
      Val.inject f varg1 varg2 /\
      extcall_arg rs2 m2 loc varg2.
  Proof.
    intros Hrs Hm Hvarg1.
    destruct Hvarg1 as [r | ofs ty bofs v1 Hbofs Hmv1].
    * exists (rs2 (preg_of r)).
      split; eauto.
      constructor.
    * edestruct Mem.loadv_inject as (v2 & Hmv2 & Hv); eauto.
      + eapply Val.offset_ptr_inject; eauto.
      + exists v2.
        split; eauto.
        econstructor; eauto.
  Qed.

  Lemma extcall_arg_pair_inject f rs1 m1 rs2 m2 loc varg1:
    (forall r, Val.inject f (rs1 r) (rs2 r)) ->
    Mem.inject f m1 m2 ->
    extcall_arg_pair rs1 m1 loc varg1 ->
    exists varg2,
      Val.inject f varg1 varg2 /\
      extcall_arg_pair rs2 m2 loc varg2.
  Proof.
    intros Hrs Hm Hvarg1.
    destruct Hvarg1 as [l bv H | hi lo vhi vlo H1 H2].
    * eapply extcall_arg_inject in H; eauto.
      decompose [ex and] H.
      eauto using extcall_arg_one.
    * eapply extcall_arg_inject in H1; eauto.
      eapply extcall_arg_inject in H2; eauto.
      decompose [ex and] H1.
      decompose [ex and] H2.
      exists (Val.longofwords x x0).
      split.
      + apply Val.longofwords_inject; eauto.
      + constructor; eauto.
  Qed.

  Lemma extcall_arguments_inject sg f rs1 m1 rs2 m2 vargs1:
    (forall r, Val.inject f (rs1 r) (rs2 r)) ->
    Mem.inject f m1 m2 ->
    extcall_arguments rs1 m1 sg vargs1 ->
    exists vargs2,
      Val.inject_list f vargs1 vargs2 /\
      extcall_arguments rs2 m2 sg vargs2.
  Proof.
    intros Hrs Hm.
    revert vargs1.
    unfold extcall_arguments.
    induction (Conventions1.loc_arguments sg) as [ | loc locs IHlocs].
    * inversion 1; subst.
      exists nil.
      split; constructor.
    * inversion 1 as [ | xloc xlocs v1 vargs1' Hv1 Hvargs1']; subst.
      edestruct extcall_arg_pair_inject as (v2 & Hv & Hv2); eauto.
      edestruct IHlocs as (vargs2 & Hvargs & Hvargs2); eauto.
      + exists (v2 :: vargs2).
        split; eauto.
        constructor; eauto.
  Qed.
End INJECT.


(** * Names of external functions *)

(** In recent version of Compcert, external functions defined as
  [EF_external] are specified by giving their names as strings rather
  than [ident] values. To addapt our definitions we assume there is an
  injective mapping from [ident] values to [string]s. *)

Axiom name_of_ident : ident -> String.string.
Axiom name_of_ident_inj: forall i j (EQ: name_of_ident i = name_of_ident j), i = j.


(** * Lists *)

Lemma list_forall2_list_rel {A B}:
  @list_forall2 A B = @list_rel A B.
Proof.
  apply FunctionalExtensionality.functional_extensionality.
  intro rel.
  apply eqrel_eq.
  split;
  intros l1 l2;
  induction 1; constructor; auto.
Qed.
