Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.ExtensionalityAxioms.
Require Import liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.MakeProgramSpec.
Require Import liblayers.compcertx.InitMem.

(** * Monotonicity of [Genv.alloc_global] *)

(** Because the definition of [Genv.alloc_global] is somewhat
  complicated, it is inconvenient to prove an associated relational
  properties.

  In what follows we provide a skeleton for the proof that can be
  instantiated by providing an instance of the new typeclass
  [InitMemRelations]. In addition to a relation on memories and
  relations on function and variable definitions, we use an
  intermediate relation [RI] to handle initialization. Then we let the
  user prove that the individual operations involved in allocating a
  new global definition preserve the relations. Given two related
  initial memories, the following cases should produce two related
  final ones, assuming they're allowed by [RF] and [RV]:

    - two empty definitions;
    - two related function definitions;
    - two related variable definitions;
    - a new function on the right-hand side;
    - a new variable on the right-hand side.

  The cases involving variables are more complicated, because the
  process of allocating and initializing a global variable is somewhat
  involved:

    - allocating a new block for the global variable and initializing
      it with zeroes should take memories related by [RM i] to
      memories related by [RI i nil];
    - writing each new item [idatum] of the initialization list will
      take memories related by [RI i base] to memories related by
      [RI i (base ++ idatum :: nil)];
    - finalizing the allocation and initialization by setting the
      permissions of the new block will take memories related by
      [RI i init] to memories related by [RM (Pos.succ i)]. *)

(** ** Helper definitions *)

(** In order to state the monotonicity conditions in a way that is
  most natural to the user and consistent with the rest of our code,
  we define the following components of [Genv.alloc_global] in terms
  of optional function and variable definitions. *)

Section ALLOC_GLOBAL_COMPONENTS.
  Context `{Hmem: Mem.MemoryModelX} {F V : Type}.

  Definition alloc_none (m: mem) :=
    let '(m, b) := Mem.alloc m 0 0 in Some m.

  Definition alloc_fun (m: mem) :=
    let '(m, b) := Mem.alloc m 0 1 in Mem.drop_perm m b 0 1 Nonempty.

  Definition alloc_var_zeros v m :=
    let init := gvar_init (V:=V) v in
    let sz := init_data_list_size init in
    let '(m, b) := Mem.alloc m 0 sz in
    store_zeros m b 0 sz.

  Definition alloc_var_perm v m b :=
    let init := gvar_init (V:=V) v in
    let sz := init_data_list_size init in
    Mem.drop_perm m b 0 sz (Genv.perm_globvar v).

  Definition alloc_var (v: globvar V) (ge: Genv.t F V) m b :=
    m <- alloc_var_zeros v m;
    m <- Genv.store_init_data_list ge m b 0 (gvar_init v);
    alloc_var_perm v m b.

  Definition alt_alloc_global ge m (idef: ident * option (globdef F V)) :=
    let '(i, def) := idef in
    match def with
      | Some (Gfun f) => alloc_fun m
      | Some (Gvar v) => alloc_var v ge m i
      | None => alloc_none m
    end.

  (** To show the monotonicity of [Genv.alloc_global], we first
    translate it into this altenate form. We need to maintain the
    invariant that the input [Mem.nextblock] is equal to the
    identifier being allocated. *)

  Lemma alt_alloc_global_eq (ge: Genv.t F V) m i def:
    Mem.nextblock m = i ->
    Genv.alloc_global ge m (i, def) = alt_alloc_global ge m (i, def).
  Proof.
    intros Hm.
    unfold Genv.alloc_global, alt_alloc_global.
    destruct def as [[f|v]|].
    - reflexivity.
    - unfold alloc_var, alloc_var_zeros, alloc_var_perm.
      destruct (Mem.alloc _ _ _) eqn:Halloc.
      assert (b = i).
      {
        apply Mem.alloc_result in Halloc.
        congruence.
      }
      subst b.
      destruct (store_zeros _ _ _ _); monad_norm; eauto.
    - reflexivity.
  Qed.

  Lemma alt_alloc_global_nextblock (ge: Genv.t F V) m i def m':
    Mem.nextblock m = i ->
    alt_alloc_global ge m (i, def) = Some m' ->
    Mem.nextblock m' = Pos.succ i.
  Proof.
    intros Hi H.
    destruct def as [[f|v]|]; simpl in *.
    - unfold alloc_fun in H.
      destruct (Mem.alloc m _ _) as [mi b] eqn:Hmi.
      apply Mem.nextblock_alloc in Hmi.
      apply Mem.nextblock_drop in H.
      congruence.
    - unfold alloc_var, alloc_var_zeros, alloc_var_perm in H.
      destruct (Mem.alloc m _ _) as [mi b] eqn:Hmi.
      apply Mem.nextblock_alloc in Hmi.
      inv_monad H.
      apply Genv.store_zeros_nextblock in H2.
      apply Genv.store_init_data_list_nextblock in H3.
      apply Mem.nextblock_drop in H1.
      congruence.
    - unfold alloc_none in H.
      destruct (Mem.alloc m _ _) as [mi b] eqn:Hmi.
      apply Mem.nextblock_alloc in Hmi.
      congruence.
  Qed.
End ALLOC_GLOBAL_COMPONENTS.

(** ** Requirements *)

(** With this reformulation of [Genv.alloc_global], we can
  conveniently express the requirements on our relations as
  monotonicity properties for the basic components of
  [alt_alloc_global]. *)

Section INIT_MEM_REL.
  Context {mem1 mem1_ops} `{Hmem1: @Mem.MemoryModelX mem1 mem1_ops}.
  Context {mem2 mem2_ops} `{Hmem2: @Mem.MemoryModelX mem2 mem2_ops}.
  Context {F1 F2} (RF: ident -> rel (option F1) (option F2)).
  Context {V1 V2} (RV: ident -> rel (option (globvar V1)) (option (globvar V2))).

  (** Our proof is parametrized by a family of relations over the
    partially constructed initial memory state. Specifically, the two
    memory states are related by:

        [RM i init zp sz]

    where:

      - [i] is the identifier of the definition being processed, which
        in our case always coincides with the corresponding block
        number;
      - [sz] is the number of bytes that have been allocated for this
        definition: initially 0, then 1 for functions and a size
        computed by [init_data_list_size] for variables;
      - [zp] is the number of zero bytes that have been written by
        [Genv.store_zeros] to this block (this is initially [0] and
        will eventually equal [sz]);
      - [init] is the list of [init_data] entries that have been
        written to this block so far.

    It is expected that:

        [0 <= init_data_list_size init <= zp <= sz]

    As the initial memories are constructed, we follow the process
    step-by-step and use user-provided proofs to make sure that the
    relation is preserved by each step. For each definition [i],
    initially we're in a state where [RM i nil 0 0] holds. In the case
    of a variable, we will then:

      - Allocate [sz] bytes, resulting in memories that are related by
        [RM i nil 0 sz].
      - Next, [Genv.store_zeros] will write [Vzero] into each byte in
        the block at successive positions [zp], and at each step the
        relation [RM i nil zp sz] will hold, meaning bytes at offsets
        [0 <= ofs < zp] have been written.
      - When [zp] reaches [sz], we start writing the initial
        data. Suppose we have written the partial list of initial data
        [base] so far; writing the datum [next] will take us from
        memories related by [RM i base sz sz] to memories related by
        [RM i (base ++ next :: nil) sz sz].
      - When all of the initial data have been written, we set the
        block persmissions and obtain memories related by
        [RM (Pos.succ i) nil 0 0], ready to process the next
        definition. *)

  Context (RM: ident -> list init_data -> Z -> Z -> rel mem1 mem2).

  (** The complicated cases are variables, which can be either a new
    variable on the right-hand side, or two equivalent variables on
    each side. *)

  Class InitMemNewVariableProps (i: ident) (v: globvar V2) :=
    {
      initmem_rel_none_var_valid:
        Genv.init_data_list_valid find_symbol 0%Z (gvar_init v) = true;
      initmem_rel_none_var_alloc sz:
        sz = init_data_list_size (gvar_init v) ->
        Related
          (fun m => fst (Mem.alloc m 0 0))
          (fun m => fst (Mem.alloc m 0 sz))
          (RM i nil 0 0 ++> RM i nil 0 sz);
      initmem_rel_none_var_zero zp sz m1 m2 m2':
        sz = init_data_list_size (gvar_init v) ->
        (forall ofs k p, ~ Mem.perm m1 i ofs k p) ->
        Mem.store Mint8unsigned m2 i zp Vzero = Some m2' ->
        RM i nil zp sz m1 m2 ->
        RM i nil (zp+1) sz m1 m2';
      initmem_rel_none_var_store sz ge1 ge2 base id m1 m2 m2':
        sz = init_data_list_size (gvar_init v) ->
        (forall ofs k p, ~ Mem.perm m1 i ofs k p) ->
        genv_rel RF RV ge1 ge2 ->
        Genv.store_init_data ge2 m2 i
          (init_data_list_size base) id = Some m2' ->
        RM i base sz sz m1 m2 ->
        RM i (base ++ id :: nil) sz sz m1 m2';
      initmem_rel_none_var_perm sz m1 m2 m2':
        sz = init_data_list_size (gvar_init v) ->
        (forall ofs k p, ~ Mem.perm m1 i ofs k p) ->
        Mem.drop_perm m2 i 0 sz (Genv.perm_globvar v) = Some m2' ->
        RM i (gvar_init v) sz sz m1 m2 ->
        RM (Pos.succ i) nil 0 0 m1 m2'
    }.

  Section NEW_VARIABLE_PROPS.
    Context i v2 `{Hv: InitMemNewVariableProps i v2}.

    (** Generally useful lemmas. *)

    Lemma genv_init_data_list_size_app l1 l2:
      init_data_list_size (l1 ++ l2) =
      (init_data_list_size l1 + init_data_list_size l2)%Z.
    Proof.
      induction l1; eauto.
      simpl.
      rewrite <- Z.add_assoc.
      f_equal.
      assumption.
    Qed.

    Lemma genv_init_data_list_size_pos init:
      0 <= init_data_list_size init.
    Proof.
      induction init.
      - reflexivity.
      - simpl.
        pose proof (init_data_size_pos a).
        omega.
    Qed.

    (** We need to keep track of the invariant that [m1] has no
      permissions. *)

    Let isz := init_data_list_size (gvar_init v2).

    Definition newvar_perms (m1: mem1) (m2: mem2) :=
      (forall ofs k p, ~ Mem.perm m1 i ofs k p) /\
      (forall ofs, 0 <= ofs < isz -> Mem.perm m2 i ofs Cur Freeable).

    Global Instance initmem_none_alloc_var_zeros_rel:
      Related
        (alloc_none)
        (alloc_var_zeros v2)
        ((RM i nil 0 0 /\ req i @@ Mem.nextblock) ++>
         option_le (RM i nil isz isz /\ newvar_perms)).
    Proof.
      unfold alloc_var_zeros.
      change (init_data_list_size _) with isz.
      intros m1 m2 [Hm Hnb].
      red in Hnb.
      pose proof (initmem_rel_none_var_alloc isz eq_refl m1 m2 Hm) as Hm'.
      simpl in Hm'.
      unfold alloc_none.
      destruct (Mem.alloc m1 _ _) as [m1' b1] eqn:Halloc1; simpl in Hm'.
      destruct (Mem.alloc m2 _ _) as [m2' b2] eqn:Halloc2; simpl in Hm'.
      assert (Hb1: i = b1).
      {
        apply Mem.alloc_result in Halloc1.
        inversion Hnb; congruence.
      }
      assert (Hb2: i = b2).
      {
        apply Mem.alloc_result in Halloc2.
        inversion Hnb; congruence.
      }
      pose proof (Mem.perm_alloc_2 _ _ _ _ _ Halloc2) as Hperm2.
      clear Halloc2.
      pose proof (eq_refl isz) as H.
      rewrite <- Z.add_0_l in H at 1.
      revert H Hm'.
      generalize (genv_init_data_list_size_pos (gvar_init v2)).
      change (init_data_list_size _) with isz.
      generalize (Z.le_refl 0).
      generalize isz at 1 2 7.
      generalize 0 at 2 4 5 6.
      intros p n.
      functional induction (store_zeros m2' b2 p n).
      - intros Hp Hn Hpn Hm'.
        assert (p = isz) by omega.
        subst p.
        repeat constructor; eauto.
        + intros ofs k p Hofs.
          subst b1.
          eapply (Mem.perm_alloc_3 m1 0 0) in Hofs; eauto.
          omega.
      - intros Hp Hn Hpn Hm'.
        eapply IHo; eauto.
        + intros ofs k Hofs.
          eapply Mem.perm_store_1; eauto.
        + omega.
        + omega.
        + omega.
        + eapply initmem_rel_none_var_zero; eauto.
          intros ofs k perm Hofs.
          subst b1.
          eapply (Mem.perm_alloc_3 m1 0 0) in Hofs; eauto.
          omega.
      - intros Hp Hn Hpn Hm'.
        destruct (Mem.valid_access_store m0 Mint8unsigned i p Vzero).
        {
          split.
          - intros ofs Hofs.
            simpl in Hofs.
            eapply Mem.perm_implies.
            + apply Hperm2.
              omega.
            + constructor.
          - simpl.
            apply Z.divide_1_l.
        }
        congruence.
    Qed.

    Lemma initmem_rel_none_var_store_list_aux base init:
      Genv.init_data_list_valid find_symbol (init_data_list_size base) init
        = true ->
      init_data_list_size (base ++ init) <= isz ->
      Related
        (fun _ m _ _ _ => Some m)
        (Genv.store_init_data_list (F:=_) (V:=_))
        (genv_rel RF RV ++>
         (RM i base isz isz /\ newvar_perms) ++>
         req i ==> req (init_data_list_size base) ==> req init ==>
         option_le (RM i (base ++ init) isz isz /\ newvar_perms)).
    Proof.
      intros Hvld Hsz ge1 ge2 Hge m1 m2 Hm _ _ [] _ _ [] _ _ [].
      revert base m1 m2 Hvld Hsz Hm.
      induction init as [| a init IHinit]; simpl; intros base m1 m2 Hvld Hsz Hm.
      - rewrite app_nil_r.
        solve_monotonic.
      - assert (base ++ a :: init = (base ++ a :: nil) ++ init).
        {
          rewrite <- app_assoc.
          simpl.
          reflexivity.
        }
        rewrite H; clear H.
        destruct (Genv.init_data_valid _ _ _) eqn:Ha; [|discriminate].
        edestruct (Genv.store_init_data_exists ge2) as [m2'' Hm2''].
        + transitivity
            (Genv.init_data_valid find_symbol (init_data_list_size base) a).
          * eapply Genv.init_data_valid_symbols_preserved.
            intro s.
            apply stencil_matches_symbols; eauto.
          * apply Ha.
        + intros ofs Hofs.
          destruct Hm as (Hm & Hm1 & Hm2).
          eapply Mem.perm_implies; [eapply Hm2 | constructor].
          rewrite genv_init_data_list_size_app in Hsz.
          simpl in Hsz.
          pose proof (genv_init_data_list_size_pos base).
          pose proof (genv_init_data_list_size_pos init).
          omega.
        + rewrite Hm2''.
          specialize (IHinit (base ++ (a :: nil)) m1 m2'').
          rewrite genv_init_data_list_size_app in IHinit.
          simpl in IHinit.
          rewrite Z.add_0_r in IHinit.
          destruct Hm as (Hm & Hm1 & Hm2).
          eapply IHinit; eauto; repeat split.
          * rewrite <- app_assoc.
            simpl.
            assumption.
          * eapply initmem_rel_none_var_store; eauto.
          * eauto.
          * intros.
            erewrite <- Genv.store_init_data_perm; eauto.
    Qed.

    Global Instance initmem_rel_none_var_store_list:
      Related
        (fun _ m _ _ _ => Some m)
        (Genv.store_init_data_list (F:=_) (V:=_))
        (genv_rel RF RV ++>
         (RM i nil isz isz /\ newvar_perms) ++>
         req i ==> req 0 ==> req (gvar_init v2) ==>
         option_le (RM i (gvar_init v2) isz isz /\ newvar_perms)).
    Proof.
      eapply initmem_rel_none_var_store_list_aux.
      - eapply initmem_rel_none_var_valid.
      - reflexivity.
    Qed.

    Global Instance initmem_rel_none_alloc_var_perm:
      Related
        (fun m _ => Some m)
        (alloc_var_perm v2)
        ((RM i (gvar_init v2) isz isz /\ newvar_perms) ++>
         req i ==>
         option_le (RM (Pos.succ i) nil 0 0)).
    Proof.
      intros m1 m2 (Hm & Hm1 & Hm2) _ _ [].
      unfold alloc_var_perm.
      edestruct
        (Mem.range_perm_drop_2 m2 i 0 (init_data_list_size (gvar_init v2)))
        as [m2' Hm2'].
      {
        intros ofs Hofs.
        eauto.
      }
      rewrite Hm2'.
      constructor.
      eapply initmem_rel_none_var_perm; eauto.
    Qed.

    Global Instance initmem_rel_none_var:
      Related
        (fun ge m b => alloc_none m)
        (alloc_var v2)
        (genv_rel RF RV ++> (RM i nil 0 0 /\ req i @@Mem.nextblock) ++> req i ++>
         option_le (RM (Pos.succ i) nil 0 0)).
    Proof.
      unfold alloc_var.
      assert (Params (@alloc_none) 1) by constructor.
      assert (Params (@alloc_var_perm) 2) by constructor.
      assert (Params (@alloc_var_zeros) 1) by constructor.
      repeat rstep.
      rewrite <- (monad_bind_ret (alloc_none _)).
      repeat rstep.
      rewrite <- (monad_bind_ret (ret _)).
      repeat rstep.
      {
        eapply initmem_rel_none_alloc_var_perm; rauto.
      }
      assert (Params (Genv.store_init_data_list) 5) by constructor.
      unfold ret; simpl.
      eapply initmem_rel_none_var_store_list; repeat rstep.
    Qed.
  End NEW_VARIABLE_PROPS.

  (** Requirements for parallel variables. *)

  (* XXX: add to coqrel *)
  Definition option_ifsome_rel {A B} (R: rel A B): rel (option A) (option B) :=
    fun x y =>
      forall a b, x = Some a -> y = Some b -> R a b.

  (* XXX: add to coqrel *)
  Inductive option_issome_rel {A B} (R: rel A B): rel (option A) (option B) :=
    option_issome_rel_intro:
      subrel R (option_issome_rel R @@ Some).

  Class InitMemVariableProps (i: ident) (v1: globvar V1) (v2: globvar V2) :=
    {
      initmem_rel_var_init_eq:
        gvar_init v1 = gvar_init v2;
      initmem_rel_var_alloc sz:
        sz = init_data_list_size (gvar_init v2) ->
        Monotonic
          (fun m => Mem.alloc m 0 sz)
          (RM i nil 0 0 ++> RM i nil 0 sz @@ fst);
      initmem_rel_var_zero zp sz:
        Monotonic
          (fun m => Mem.store Mint8unsigned m i zp Vzero)
          (RM i nil zp sz ++> option_ifsome_rel (RM i nil (zp+1) sz));
      initmem_rel_var_store sz base next:
        sz = init_data_list_size (gvar_init v2) ->
        Monotonic
          (fun ge m =>
           Genv.store_init_data ge m i (init_data_list_size base) next)
          (genv_rel RF RV ++> RM i base sz sz ++>
           option_ifsome_rel (RM i (base++next::nil) sz sz));
      initmem_rel_var_perm sz :>
        sz = init_data_list_size (gvar_init v2) ->
        Related
          (alloc_var_perm v1)
          (alloc_var_perm v2)
          (RM i (gvar_init v2) sz sz ++> req i ++>
           option_ifsome_rel (RM (Pos.succ i) nil 0 0))
    }.

  Section OLD_VARIABLE_PROPS.
    Context i v1 v2 `{Hv: InitMemVariableProps i v1 v2}.

    Let isz := init_data_list_size (gvar_init v2).

    (** We need to keep track of the invariant that [m2] is freeable
      so that we know that [Mem.drop_perm] will succeed in the end. *)

    Definition samevar_perms (m1: mem1) (m2: mem2) :=
      Mem.range_perm m2 i 0 isz Cur Freeable.

    Global Instance initmem_rel_var_alloc_rel:
      Monotonic
        (fun m => Mem.alloc m 0 isz)
        ((RM i nil 0 0 /\ req i @@ Mem.nextblock) ++>
         (RM i nil 0 isz /\ samevar_perms) @@ fst).
    Proof.
      intros m1 m2 [Hm Hnb].
      split.
      - eapply initmem_rel_var_alloc; eauto.
      - red.
        destruct (Mem.alloc m2 _ _) as [m2' b2] eqn:Hm2'.
        simpl.
        assert (b2 = i).
        {
          apply Mem.alloc_result in Hm2'.
          red in Hnb.
          destruct Hnb.
          assumption.
        }
        subst.
        intros ofs Hofs.
        eapply Mem.perm_alloc_2; eauto.
    Qed.

    Global Instance initmem_rel_var_store_init_data base next:
      let pos := init_data_list_size base in
      pos + init_data_size next <= isz ->
      Monotonic
        (Genv.store_init_data (F:=_) (V:=_))
        (genv_rel RF RV ++>
         (RM i base isz isz /\ samevar_perms) ++>
         req i ++> req pos ==> req next ==>
         option_le (RM i (base ++ next :: nil) isz isz /\ samevar_perms)).
    Proof.
      intros pos Hpos ge1 ge2 Hge m1 m2 [Hm Hm2] _ _ [] _ _ [] _ _ [].
      destruct (Genv.store_init_data ge1 _ _ _ _) as [m1'|] eqn:Hm1'.
      - edestruct (Genv.store_init_data_exists ge2 pos next); eauto.
        + assert (H:(-==>eq)%rel (Genv.find_symbol ge1) (Genv.find_symbol ge2)).
          {
            intro j.
            rewrite !stencil_matches_symbols by eauto.
            reflexivity.
          }
          (** XXX: should be able to use rewrite with H but coqrel loops *)
          assert (Genv.init_data_valid (Genv.find_symbol ge1) pos next = true).
          {
            eapply (Genv.store_init_data_valid (mem := mem1)); eauto.
          }
          revert H0.
          assert (forall A, Monotonic (@eq A) (- ==> - ==> iff)) by (clear; firstorder).
          assert (Params (@eq) 2) by constructor.
          rauto.
        + intros ofs Hofs.
          red in Hm2.
          eapply Mem.perm_implies.
          * eapply Hm2.
            assert (0 <= pos).
            {
              eapply genv_init_data_list_size_pos.
            }
            omega.
          * constructor.
        + rewrite H.
          constructor.
          split.
          * eapply initmem_rel_var_store; eauto.
          * intros ofs Hofs.
            erewrite <- Genv.store_init_data_perm; eauto.
      - constructor.
    Qed.

    Global Instance initmem_rel_var_store_init_data_params:
      Params (@Genv.store_init_data) 5.

    Global Instance initmem_rel_var_store_list:
      Monotonic
        (Genv.store_init_data_list (F:=_) (V:=_))
        (genv_rel RF RV ++> (RM i nil isz isz /\ samevar_perms) ++>
         req i ==> req 0 ==> req (gvar_init v2) ==>
         option_le (RM i (gvar_init v2) isz isz /\ samevar_perms)).
    Proof.
      generalize (eq_refl (gvar_init v2)).
      generalize (gvar_init v2) at 1 3 4; intros init.
      change 0 with (init_data_list_size nil).
      change init with (nil ++ init) at 1 3.
      generalize (@nil init_data); intros base.
      intros Hinit ge1 ge2 Hge m1 m2 Hm _ _ [] _ _ [] _ _ [].
      revert base Hinit m1 m2 Hm.
      induction init;
      intros base Hinit m1 m2 Hm.
      - rewrite app_nil_r.
        simpl.
        rauto.
      - replace (base ++ a :: init) with ((base ++ a :: nil) ++ init).
        + simpl.
          pose proof (initmem_rel_var_store_init_data base a) as H.
          assert
            (init_data_list_size base + init_data_size a <=
             init_data_list_size (gvar_init v2)) as H'.
          {
            rewrite <- Hinit.
            rewrite genv_init_data_list_size_app.
            simpl.
            pose proof (genv_init_data_list_size_pos init).
            omega.
          }
          specialize (H H'); clear H'.
          repeat rstep; eauto.
          replace (init_data_list_size base + init_data_size a)%Z
            with (init_data_list_size (base ++ a :: nil)).
          * eapply IHinit; eauto.
            rewrite <- app_assoc.
            simpl.
            assumption.
          * rewrite genv_init_data_list_size_app.
            simpl.
            rewrite Z.add_0_r.
            reflexivity.
        + rewrite <- app_assoc.
          simpl.
          reflexivity.
    Qed.

    Global Instance initmem_rel_var_store_list_params:
      Params (@Genv.store_init_data_list) 5.

    Global Instance initmem_alloc_var_zeros_rel:
      Related
        (alloc_var_zeros v1)
        (alloc_var_zeros v2)
        ((RM i nil 0 0 /\ req i @@ Mem.nextblock) ++>
         option_le (RM i nil isz isz /\ samevar_perms)).
    Proof.
      unfold alloc_var_zeros.
      intros m1 m2 [Hm Hnb].
      red in Hnb.
      unfold samevar_perms in *.
      generalize (initmem_rel_var_alloc_rel m1 m2 (conj Hm Hnb)).
      rewrite initmem_rel_var_init_eq.
      generalize (genv_init_data_list_size_pos (gvar_init v2)).
      change (init_data_list_size _) with isz.
      generalize isz; intro sz.
      destruct (Mem.alloc m1 _ _) as [m1' b1] eqn:Halloc1; simpl.
      destruct (Mem.alloc m2 _ _) as [m2' b2] eqn:Halloc2; simpl.
      assert (Hb1: b1 = i).
      {
        apply Mem.alloc_result in Halloc1.
        inversion Hnb; congruence.
      }
      assert (Hb2: b2 = i).
      {
        apply Mem.alloc_result in Halloc2.
        inversion Hnb; congruence.
      }
      subst.
      pose proof (Mem.perm_alloc_2 _ _ _ _ _ Halloc1) as Hperm1; clear Halloc1.
      pose proof (Mem.perm_alloc_2 _ _ _ _ _ Halloc2) as Hperm2; clear Halloc2.
      intros Hsz.
      pattern 0 at 1 3 4.
      rewrite <- (Z.sub_diag sz).
      generalize (Z.le_refl sz).
      revert Hsz.
      generalize sz at 1 2 5 11 12 14 15; intro r.
      intros Hr.
      revert m1' m2' Hperm1 Hperm2.
      pattern r.
      apply Z.right_induction with (z := 0); eauto; clear r Hr.
      - typeclasses eauto.
      - rewrite Z.sub_0_r.
        intros m1' m2' Hm1' Hm2' Hr [Hm' Hmp]; simpl in Hm', Hmp.
        rewrite !store_zeros_equation.
        destruct (zle _ _); try omega.
        constructor.
        constructor; eauto.
        red.
        eauto.
      - intros r Hr IHr m1' m2' Hperm1 Hperm2 Hsr [Hm' Hmp]; simpl in Hm', Hmp.
        rewrite !store_zeros_equation.
        destruct (zle _ _); try omega.
        edestruct (Mem.valid_access_store m1' Mint8unsigned i (sz - Z.succ r))
          as (m1'' & Hm1''); eauto.
        {
          split.
          - intros ofs Hofs.
            simpl in Hofs.
            eapply Mem.perm_implies.
            + apply Hperm1; omega.
            + constructor.
          - simpl.
            apply Z.divide_1_l.
        }
        edestruct (Mem.valid_access_store m2' Mint8unsigned i (sz - Z.succ r))
          as (m2'' & Hm2''); eauto.
        {
          split.
          - intros ofs Hofs.
            simpl in Hofs.
            eapply Mem.perm_implies.
            + apply Hperm2; omega.
            + constructor.
          - simpl.
            apply Z.divide_1_l.
        }
        rewrite Hm1'', Hm2''.
        replace (sz - Z.succ r + 1)%Z with (sz - r)%Z by omega.
        replace (Z.succ r - 1)%Z with r by omega.
        apply IHr; eauto.
        + intros ofs k Hofs.
          eapply Mem.perm_store_1; eauto.
        + intros ofs k Hofs.
          eapply Mem.perm_store_1; eauto.
        + omega.
        + replace (sz - r) with (sz - Z.succ r + 1)%Z by omega.
          split; simpl.
          * eapply initmem_rel_var_zero; eauto.
          * intros ofs Hofs.
            eapply Mem.perm_store_1; eauto.
    Qed.

    Global Instance alloc_var_zeros_rel_params:
      Params (@alloc_var_zeros) 1.

    Global Instance alloc_var_rel:
      Related
        (alloc_var v1)
        (alloc_var v2)
        (genv_rel RF RV ++> (RM i nil 0 0 /\ req i @@Mem.nextblock) ++> req i ==>
         option_le (RM (Pos.succ i) nil 0 0)).
    Proof.
      unfold alloc_var.
      intros ge1 ge2 Hge m1 m2 [Hm Hnb] _ _ [].
      repeat rstep.
      - destruct H0.
        red in H1.
        unfold alloc_var_perm.
        destruct (Mem.drop_perm x0 _ _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
        edestruct Mem.range_perm_drop_2 as [m2' Hm2']; eauto.
        rewrite Hm2'.
        unfold isz in Hm2'.
        constructor.
        red in Hnb.
        eapply initmem_rel_var_perm; destruct Hnb; eauto; rauto.
      - rewrite initmem_rel_var_init_eq; eauto; rauto.
    Qed.
  End OLD_VARIABLE_PROPS.

  (** Requirements for the monotonicity of [Genv.init_mem]. *)

  Class InitMemRelations :=
    {
      initmem_rel_fun_fw i :>
        OptionRelationForward (RF i);
      initmem_rel_var_fw i :>
        OptionRelationForward (RV i);

      (** Starting point *)
      initmem_rel_empty :>
        Monotonic Mem.empty (RM 1%positive nil 0 0);

      (** No definition *)
      initmem_rel_none i:
        RF i None None ->
        RV i None None ->
        Monotonic
          alloc_none
          (RM i nil 0 0 ++> option_le (RM (Pos.succ i) nil 0 0));

      (** New function *)
      initmem_rel_none_fun i f:
        RF i None (Some f) ->
        RV i None None ->
        Related
          alloc_none
          alloc_fun
          (RM i nil 0 0 ++> option_le (RM (Pos.succ i) nil 0 0));

      (** New variable *)
      initmem_rel_none_var_props i v:
        RF i None None ->
        RV i None (Some v) ->
        InitMemNewVariableProps i v;

      (** Both functions *)
      initmem_rel_fun i f1 f2:
        RF i (Some f1) (Some f2) ->
        RV i None None ->
        Monotonic
          alloc_fun
          (RM i nil 0 0 ++> option_le (RM (Pos.succ i) nil 0 0));

      (** Both variables *)
      initmem_rel_var_props i v1 v2:
        RF i None None ->
        RV i (Some v1) (Some v2) ->
        InitMemVariableProps i v1 v2
    }.

  Context `{HR: InitMemRelations}.

  Lemma genv_alloc_global_rel_mem i:
    Monotonic
      (Genv.alloc_global (F:=_) (V:=_))
      (genv_rel RF RV ++>
       (RM i nil 0 0 /\ req i @@ Mem.nextblock) ++>
       req i * globdef_rel RF RV i ++>
       option_le (RM (Pos.succ i) nil 0 0)).
  Proof.
    intros ge1 ge2 Hge m1 m2 Hm [i1 d1] [i2 d2] [Hi Hd].
    pose proof Hm as Hmnb.
    destruct Hm as [Hm Hnb].
    unfold fst, snd in *.
    destruct Hi.
    assert (Hnb1: Mem.nextblock m1 = i) by (inversion Hnb; congruence).
    assert (Hnb2: Mem.nextblock m2 = i) by (inversion Hnb; congruence).
    rewrite !alt_alloc_global_eq by assumption.
    unfold alt_alloc_global.
    destruct Hd as [Hdf Hdv].
    unfold rel_pull in *.
    destruct d1 as [[f1|v1]|], d2 as [[f2|v2]|]; monad_norm; simpl in *.
    - eapply initmem_rel_fun; eauto.
    - apply option_rel_fw in Hdf; eauto; discriminate.
    - apply option_rel_fw in Hdf; eauto; discriminate.
    - apply option_rel_fw in Hdv; eauto; discriminate.
    - eapply alloc_var_rel; eauto; try rauto.
      apply initmem_rel_var_props; eauto.
    - apply option_rel_fw in Hdv; eauto; discriminate.
    - eapply initmem_rel_none_fun; eauto.
    - eapply initmem_rel_none_var; eauto; try rauto.
      apply initmem_rel_none_var_props; eauto.
    - eapply initmem_rel_none; eauto.
  Qed.

  Global Instance genv_alloc_global_rel i:
    Monotonic
      (Genv.alloc_global (F:=_) (V:=_))
      (genv_rel RF RV ++>
       (RM i nil 0 0 /\ req i @@ Mem.nextblock) ++>
       req i * globdef_rel RF RV i ++>
       option_le (RM (Pos.succ i) nil 0 0 /\ req (Pos.succ i) @@ Mem.nextblock)).
  Proof.
    intros ge1 ge2 Hge m1 m2 Hm def1 def2 Hdef.
    pose proof (genv_alloc_global_rel_mem i ge1 ge2 Hge m1 m2 Hm def1 def2 Hdef).
    destruct (Genv.alloc_global ge1 m1 def1) as [m1'|] eqn:Hm1';
    destruct (Genv.alloc_global ge2 m2 def2) as [m2'|] eqn:Hm2';
    inversion H; clear H; subst;
    constructor.
    split; eauto.
    destruct def1 as [i1 def1], def2 as [i2 def2], Hdef as [Hi Hdef].
    destruct Hm as [Hm Hnb].
    unfold fst, snd in *.
    destruct Hi.
    assert (Hnb1: Mem.nextblock m1 = i) by (inversion Hnb; congruence).
    assert (Hnb2: Mem.nextblock m2 = i) by (inversion Hnb; congruence).
    rewrite alt_alloc_global_eq in Hm1'; eauto.
    rewrite alt_alloc_global_eq in Hm2'; eauto.
    apply alt_alloc_global_nextblock in Hm1'; eauto.
    apply alt_alloc_global_nextblock in Hm2'; eauto.
    red.
    rewrite Hm1', Hm2'.
    constructor.
  Qed.

  Global Instance genv_alloc_global_rel_params:
    Params (@Genv.alloc_global) 3.

  (** * Relational property for [Genv.init_mem] *)

  Local Opaque Genv.alloc_global.

  (** The [globdefs_rel] relation from [CompcertStructures] is defined
    in a way that matches [make_program] (which appends definitions at
    the end one by one), but not [Genv.alloc_globals] (which scans
    definitions starting at the beginning of the list). The following
    relation is similar in spirit to [globdefs_rel] but follows the
    structure of [Genv.alloc_globals]. *)

  Inductive globdefs_bw_rel thr:
    ident -> rel (list (ident × option (globdef F1 V1)))
                 (list (ident × option (globdef F2 V2))) :=
    | globdefs_bw_rel_nil:
        Monotonic
          nil
          (globdefs_bw_rel thr thr)
    | globdefs_rel_app i: (* XXX name *)
        Monotonic
          (fun def defs => (i, def) :: defs)
          (globdef_rel RF RV i ++>
           globdefs_bw_rel thr (Pos.succ i) ++>
           globdefs_bw_rel thr i).

  Lemma globdefs_bw_rel_app i j k defs1a defs1b defs2a defs2b:
    globdefs_bw_rel j i defs1a defs2a ->
    globdefs_bw_rel k j defs1b defs2b ->
    globdefs_bw_rel k i (defs1a ++ defs1b) (defs2a ++ defs2b).
  Proof.
    intros Hij Hjk.
    revert k defs1b defs2b Hjk.
    induction Hij as [ | i d1 d2 Hd defs1a defs2a Hdefsa IHdefsa].
    - simpl.
      tauto.
    - intros k defs1b defs2b Hjk.
      change ((i, d1) :: defs1a) with (((i, d1) :: nil) ++ defs1a).
      change ((i, d2) :: defs2a) with (((i, d2) :: nil) ++ defs2a).
      rewrite <- !app_assoc.
      constructor; eauto.
  Qed.

  Global Instance globdefs_fw_bw_rel thr:
    Related (globdefs_rel RF RV thr) (globdefs_bw_rel thr 1%positive) subrel.
  Proof.
    intros defs1 defs2 Hdefs.
    induction Hdefs.
    - constructor.
    - eapply globdefs_bw_rel_app; eauto.
      constructor; eauto.
      constructor.
  Qed.

  Lemma globdefs_fw_rel_app i j defs1a defs1b defs2a defs2b:
    globdefs_rel RF RV i defs1a defs2a ->
    globdefs_bw_rel j i defs1b defs2b ->
    globdefs_rel RF RV j (defs1a ++ defs1b) (defs2a ++ defs2b).
  Proof.
    intros Hbase H.
    revert defs1a defs2a Hbase.
    induction H as [ | i def1 def2 Hdef defs1b defs2b Hdefsb IHdefsb].
    - intros defs1a defs2a Hdefsa.
      rewrite !app_nil_r.
      eauto.
    - intros defs1a defs2a Hdefsa.
      change ((i, def1) :: defs1b) with (((i, def1) :: nil) ++ defs1b).
      change ((i, def2) :: defs2b) with (((i, def2) :: nil) ++ defs2b).
      rewrite !app_assoc.
      eapply IHdefsb.
      constructor; eauto.
  Qed.

  Lemma globdefs_bw_fw_rel thr:
    subrel (globdefs_bw_rel thr 1%positive) (globdefs_rel RF RV thr).
  Proof.
    intros defs1 defs2 Hdefs.
    eapply (globdefs_fw_rel_app 1%positive thr nil defs1 nil defs2).
    - constructor.
    - assumption.
  Qed.

  Lemma globdefs_fw_bw_rel_eq thr:
    globdefs_rel RF RV thr = globdefs_bw_rel thr 1%positive.
  Proof.
    apply eqrel_eq.
    split.
    - apply globdefs_fw_bw_rel.
    - apply globdefs_bw_fw_rel.
  Qed.

  Global Instance genv_alloc_globals_rel i:
    Monotonic
      (Genv.alloc_globals (F:=_) (V:=_))
      (genv_rel RF RV ++>
       (RM i nil 0 0 /\ req i @@ Mem.nextblock) ++>
       globdefs_bw_rel glob_threshold i ++>
       option_le
         (RM glob_threshold nil 0 0 /\ req glob_threshold @@ Mem.nextblock)).
  Proof.
    intros ge1 ge2 Hge m1 m2 Hm defs1 defs2 Hdefs.
    revert m1 m2 Hm.
    induction Hdefs as [ | i d1 d2 Hd defs1 defs2 Hdefs IHdefs].
    - simpl.
      constructor.
      assumption.
    - simpl.
      intros m1 m2 Hm.
      repeat rstep; eauto.
  Qed.

  Global Instance genv_alloc_globals_rel_params:
    Params (@Genv.alloc_globals) 3.

  Global Instance genv_init_mem_rel:
    Monotonic
      (Genv.init_mem (F:=_) (V:=_))
      (program_rel RF RV ++>
       option_le
         (RM glob_threshold nil 0 0 /\ req glob_threshold @@ Mem.nextblock)).
  Proof.
    unfold Genv.init_mem.
    repeat rstep.
    split.
    - apply initmem_rel_empty.
    - red.
      rewrite !Mem.nextblock_empty.
      constructor.
  Qed.

  Global Instance genv_init_mem_rel_params:
    Params (@Genv.init_mem) 1.
End INIT_MEM_REL.
