(**
 * Stack.v
 *
 * A layer implementing a bounded stack using a bounded counter.
 *)

(** Compcert helper lib *)
Require Import Coqlib.
(** Compcert types and semantics *)
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Clight.
Require Import Ctypes.
Require Import Cop.
Require Import Smallstep.
(** CertiKOS layer library *)
Require Import Semantics.
Require Import Structures.
Require Import GenSem.
Require Import CGenSem.
Require Import CPrimitives.
Require Import SimulationRelation.
Require Import SimrelInvariant.
Require Import LayerLogicImpl.
Require Import ClightModules.
Require Import ClightXSemantics.
Require Import AbstractData.
Require Import AbstractionRelation.

Require Import TutoLib.
Require Import Counter.

(** This file is meant to continue demonstrating how the layer calculus used in
  CertiKOS works by implementing a new layer on top of an existing one. This
  layer consists of a global stack variable [STACK] that can be manipulated
  with [push] and [pop] primitives as well as have its size checked with
  [get_size]. The stack is implemented as an array where the index of the
  next open slot is tracked by the [COUNTER] variable. This guarantees that
  one cannot [pop] from an empty stack or [push] to a full one. The underlay
  upon which this layer is built is the [counter_L] defined in Counter.v. The
  overlay consists of the primitives described above, and an abstract state
  containing a [stack] of type [list Z] with the invariant that the length of
  the stack is not greater than [MAX_COUNTER]. *)

Open Scope Z_scope.

Opaque MAX_COUNTER.

Definition get_size : ident := 5%positive.
Definition push : ident := 6%positive.
Definition pop : ident := 7%positive.
Definition STACK : ident := 8%positive.

Section Stack.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.

  (** ** Abstract Data *)
  Section AbsData.
    (** We want our layer to abstract a stack of signed integers, so our
      abstract data will represent this as a [list Z]. We then provide the
      initial state and our invariant and wrap it in [layerdata] as before. *)
    Record stack_data : Type := { stack: list Z }.

    Instance stack_data_data_ops : AbstractDataOps stack_data :=
      {|
        init_data := {| stack := nil |};
        data_inv := fun d => (length (stack d) <= MAX_COUNTER)%nat;
        data_inject := fun f d1 d2 => True
      |}.

    Instance stack_data_data : AbstractData stack_data.
    Proof.
      repeat constructor.
      cbn; omega.
    Qed.

    Definition stack_layerdata : layerdata :=
      {|
        ldata_type := stack_data;
        ldata_ops  := stack_data_data_ops;
        ldata_prf  := stack_data_data
      |}.

  End AbsData.

  (** ** High Level Specifications *)
  Section HighSpec.
    (** [get_size] returns the current number of items on the stack, which is
      just the length of the list in the abstract data. *)
    Definition get_size_high_spec (abs: stack_layerdata) : nat :=
      (length (stack abs)).

    Global Instance get_size_preserves_invariant :
      GenSemPreservesInvariant stack_layerdata get_size_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      inv_monad H2.
      inv H2.
      assumption.
    Qed.

    Definition get_size_high_sem : cprimitive stack_layerdata :=
      cgensem stack_layerdata get_size_high_spec.

    Definition get_size_layer : clayer stack_layerdata :=
      get_size ↦ get_size_high_sem.

    (** [push] needs a value to add to the stack, so the spec reflects that by
      having an additional argument after [stack_data]. As usual we encode
      the potential failure by making the return type [option stack_data] and
      returning [None] in case of an error. *)
    (** N.B. The [x] argument must come before [abs] because while the type
      [Zsign -> stack_data -> option stack_data] is declared as an instance of
      [SemOf], [stack_data -> Zsign -> option stack_data] is not.
      Also, [Zsign] is simply a wrapper type around [Z] in order to allow
      both signed and unsigned versions of [Z -> T] to be instances of
      [SemOf]. *)
    Definition push_high_spec (x: Zsign) (abs: stack_layerdata) :
        option stack_layerdata :=
      if decide (length (stack abs) < MAX_COUNTER)%nat
        then Some {| stack := Zsign2Z x :: (stack abs) |}
        else None.

    Global Instance push_preserves_invariant :
      GenSemPreservesInvariant stack_layerdata push_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      unfold push_high_spec in Hsem.
      inv_generic_sem Hsem. inv H2.
      destruct (decide (length (stack d) < MAX_COUNTER)%nat); inv H3; auto.
    Qed.

    Definition push_high_sem : cprimitive stack_layerdata :=
      cgensem stack_layerdata push_high_spec.

    Definition push_layer : clayer stack_layerdata :=
      push ↦ push_high_sem.

    Definition pop_high_spec (abs: stack_layerdata) :
        option (stack_layerdata * Zsign) :=
      match stack abs with
      | nil => None
      | x :: stack' => Some ({| stack := stack' |}, VZS x)
      end.

    Global Instance pop_preserves_invariant :
      GenSemPreservesInvariant stack_layerdata pop_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? Hinv.
      inv_generic_sem Hsem.
      unfold pop_high_spec in H1.
      destruct (stack d) eqn:Hstck; inv H1; auto.
      cbn in *.
      rewrite Hstck in Hinv.
      cbn in Hinv; omega.
    Qed.

    Definition pop_high_sem : cprimitive stack_layerdata :=
      cgensem stack_layerdata pop_high_spec.

    Definition pop_layer : clayer stack_layerdata :=
      pop ↦ pop_high_sem.

  End HighSpec.

  (** ** Module Implementation *)
  Section Code.

    (** [f_get_size] simply returns the current value of [COUNTER] because that
      always equals the number of items on the stack. *)
    (**
<<
unsigned int get_size() {
  return get_counter();
}
>> *)

    (** These identifiers are used as function temporaries and parameters. *)
    Definition get_size_ret : ident := 9%positive.

    Definition f_get_size :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := (get_size_ret, tuint) :: nil;
        fn_body :=
          Ssequence
            (Scall (Some get_size_ret) (Evar get_counter (Tfunction Ctypes.Tnil tuint cc_default)) nil)
            (Sreturn (Some (Etempvar get_size_ret tuint)))
      |}.

    Program Definition inlinable_f_get_size : function :=
      inline f_get_size _.

    (** [f_push] queries the current index with [get_counter], moves it ahead
      with [incr_counter], and stores [x] into [STACK] at the index. It does
      not have to check whether the index is in range because [incr_counter]
      will already fail if it is not. *)
    (**
<<
void push(int x) {
  unsigned int idx = get_counter();
  incr_counter();
  STACK[idx] = x;
}
>> *)

    Definition push_x : ident := 10%positive.
    Definition push_idx : ident := 11%positive.

    Definition f_push :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := (push_x, tint) :: nil;
        fn_vars := nil;
        fn_temps := (push_idx, tuint) :: nil;
        fn_body :=
          Ssequence
            (Scall (Some push_idx) (Evar get_counter (Tfunction Ctypes.Tnil tuint cc_default)) nil)
            (Ssequence
              (Scall None (Evar incr_counter (Tfunction Ctypes.Tnil tuint cc_default)) nil)
              (Sassign
                (Ederef (Ebinop Oadd (Evar STACK (tarray tint (Z.of_nat MAX_COUNTER)))
                                     (Etempvar push_idx tuint)
                                     (tptr tint))
                        tint)
                (Etempvar push_x tint)))
      |}.

    Program Definition inlinable_f_push : function :=
      inline f_push _.

    (**
<<
int pop() {
  unsigned int idx = decr_counter();
  return STACK[idx];
}
>> *)

    Definition pop_idx : ident := 12%positive.

    Definition f_pop :=
      {|
        fn_return := tint;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := (pop_idx, tuint) :: nil;
        fn_body :=
          Ssequence
            (Scall (Some pop_idx) (Evar decr_counter (Tfunction Ctypes.Tnil tuint cc_default)) nil)
            (Sreturn (Some (Ederef
                             (Ebinop Oadd (Evar STACK (tarray tint (Z.of_nat MAX_COUNTER)))
                                          (Etempvar pop_idx tuint)
                                          (tptr tint))
                              tint)))
      |}.

    Program Definition inlinable_f_pop : function :=
      inline f_pop _.

    Definition Msize : cmodule := get_size ↦ inlinable_f_get_size.
    Definition Mpush : cmodule := push ↦ inlinable_f_push.
    Definition Mpop : cmodule := pop ↦ inlinable_f_pop.

  End Code.

  (** ** Low Level Specifications *)
  Section LowSpec.

    (** Because this layer is built on top of the counter layer, we can write
      the low level specs in terms of primitives from [counter_L] instead of
      dealing with the memory directly. This simplifies both the specification
      and the refinement proofs. *)

    Definition get_size_csig := mkcsig Ctypes.Tnil tuint.

    Inductive get_size_step :
      csignature -> list val * mwd counter_layerdata -> val * mwd counter_layerdata -> Prop :=
    | get_size_step_intro m d sb sz:
        (** The [STACK] global variable is stored at some memory block [sb] *)
        forall (HSb: find_symbol STACK = Some sb),
        (** Because we have access to the counter layer abstract data, we
          can read the counter value using the [get_counter] high level
          spec instead of loading from memory *)
        get_counter_high_spec d = Z.to_nat (Int.unsigned sz) ->
        (** [get_size] takes no arguments, returns [sz], and does not change
          memory or abstract state *)
        get_size_step get_size_csig (nil, (m, d)) (Vint sz, (m, d)).

    Definition push_csig := mkcsig (type_of_list_type (tint :: nil)) tvoid.

    Inductive push_step :
      csignature -> list val * mwd counter_layerdata -> val * mwd counter_layerdata -> Prop :=
    | push_step_intro m d sb d' m' idx idx' x:
        (** The [STACK] global variable is stored at some memory block [sb] *)
        forall (HSb: find_symbol STACK = Some sb),
        (** We again use the high level spec of a counter layer primitive *)
        get_counter_high_spec d = Z.to_nat (Int.unsigned idx) ->
        (** We can also use the high level spec for [incr_counter] *)
        incr_counter_high_spec d = Some (d', Z.to_nat (Int.unsigned idx')) ->
        (** Storing [x] at [STACK[idx]] returns some new memory [m'] *)
        Mem.store Mint32 m sb (4 * Int.unsigned idx) (Vint x) = Some m' ->
        (** [push] takes one argument, returns nothing and changes both the
          memory and abstract state *)
        push_step push_csig ((Vint x :: nil), (m, d)) (Vundef, (m', d')).

    Definition pop_csig := mkcsig Ctypes.Tnil tint.

    Inductive pop_step :
      csignature -> list val * mwd counter_layerdata -> val * mwd counter_layerdata -> Prop :=
    | pop_step_intro m d d' x sb idx:
        forall (HSb: find_symbol STACK = Some sb),
        decr_counter_high_spec d = Some (d', Z.to_nat (Int.unsigned idx)) ->
        Mem.load Mint32 m sb (4 * Int.unsigned idx) = Some (Vint x) ->
        pop_step pop_csig (nil, (m, d)) (Vint x, (m, d')).

    Program Definition get_size_cprimitive : cprimitive counter_layerdata :=
      mkcprimitive _ get_size_step get_size_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition push_cprimitive : cprimitive counter_layerdata :=
      mkcprimitive _ push_step push_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition pop_cprimitive : cprimitive counter_layerdata :=
      mkcprimitive _ pop_step pop_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    (** We will find out later in this file that the code proof of [pop] will
      make use of the invariants of the counter layer. This will require that
      we show that the low level specs preserve these invariants. More
      explanation later on. *)
    Global Instance get_size_cprim_pres_inv :
      CPrimitivePreservesInvariant _ get_size_cprimitive.
    Proof.
      constructor; intros.
      - inv H0. inv H1. constructor; auto.
      - inv H0; reflexivity.
    Qed.

    Global Instance push_cprim_pres_inv :
      CPrimitivePreservesInvariant _ push_cprimitive.
    Proof.
      constructor; intros.
      - inv H0. unfold incr_counter_high_spec in H10.
        destr_in H10; try discriminate. inv H10.
        inv H1. cbn in cprimitive_inv_init_state_data_inv.
        constructor; auto; cbn.
        + omega.
        + intros. eapply Mem.store_valid_block_1; eauto.
        + erewrite Mem.nextblock_store; eauto.
          eapply Mem.store_inject_neutral; eauto.
          apply find_symbol_block_is_global in HSb.
          apply cprimitive_inv_init_state_valid in HSb.
          eauto.
      - inv H0. eapply Mem.nextblock_store in H11. rewrite H11; reflexivity.
    Qed.

    Global Instance pop_cprim_pres_inv :
      CPrimitivePreservesInvariant _ pop_cprimitive.
    Proof.
      constructor; intros.
      - inv H0. unfold decr_counter_high_spec in H5.
        destr_in H5; try discriminate. inv H5.
        inv H1. cbn in cprimitive_inv_init_state_data_inv.
        constructor; auto; cbn.
        omega.
      - inv H0; reflexivity.
    Qed.

  End LowSpec.

  (** ** Code Proofs *)
  Section CodeLowSpecSim.

    Context `{ce: ClightCompositeEnv}.

    Lemma get_size_code :
      counter_L ⊢ (id, Msize) : (get_size ↦ get_size_cprimitive).
    Proof.
      code_proof_tac.
      (** We will need the function pointer for the following primitive later
         on. This tactic pulls it out of the layer and into the current
         context. *)
      find_prim get_counter.
      inv CStep.
      cprim_step. repeat step_tac.
      rewrite H2. reflexivity.
    Qed.

    Lemma push_code :
      counter_L ⊢ (id, Mpush) : (push ↦ push_cprimitive).
    Proof.
      Opaque Z.mul. (** so (4 * _) not unfolded *)
      code_proof_tac.
      find_prim get_counter.
      find_prim incr_counter.
      inv CStep.
      unfold incr_counter_high_spec in H8. destr_in H8; inv H8.
      assert (Hidx: Int.unsigned idx = Z.of_nat (counter d)).
      { generalize (Int.unsigned_range idx); intros.
        unfold get_counter_high_spec in H5.
        rewrite <- (Z2Nat.id (Int.unsigned _)); omega.
      }
      cprim_step. repeat step_tac.
      - (** [get_counter] return value *)
          rewrite H5. reflexivity.
      - (** [incr_counter] return value *)
          unfold incr_counter_high_spec. rewrite Heqs; rewrite H2. reflexivity.
      - (** Storing into [STACK] *)
          pose proof MAX_COUNTER_range as Hmc_range.
          pose proof int_ptrofs_max as Hint_ptr.
          unfold lift. cbn.
          rewrite Ptrofs.add_zero_l.
          unfold Ptrofs.mul, Ptrofs.of_intu, Ptrofs.of_int.
          repeat rewrite Ptrofs.unsigned_repr; try omega.
          rewrite H9, H2. reflexivity.
    Qed.

    (** In order to prove that [f_pop] is correct with respect to its low spec,
      we need to know that the [idx] returned by [get_counter] is bounded
      above by [Int.max_unsigned]. In the proof of [f_push] this wasn't a
      problem because we use [incr_counter] which gives us the tighter upper
      bound of [idx <= MAX_COUNTER], and we also know that
      [4 * MAX_COUNTER <= Int.max_unsigned]. With [f_pop] however, we call
      [decr_counter], which only gives us a lower bound of [0 <= idx].
      Fortunately, the invariant of the counter layer is that
      [counter <= MAX_COUNTER]. However, in order to use this fact, we have to
      strengthen our simulation diagram to reflect the fact that if the
      invariant holds in the initial states, it is preserved in the final
      state. This means we have to show that the semantics of the Clight
      function [f_pop] evaluated on [counter_L] preserves the invariants
      of [counter_L]. As it turns out, it is sufficient to show that all of the
      primitives in [counter_L] preserve the invariant due to the monotonicity
      of the semantics. *)
    Lemma pop_code :
      counter_L ⊢ (inv, Mpop) : (pop ↦ pop_cprimitive).
    Proof.
      code_proof_tac.
      - (** [counter_L] preserves invariants *)
        apply counter_pres_inv.
      - (** simulation where invariant holds for the initial state *)
        find_prim decr_counter.
        inv Hmatch; inv CStep.
        pose proof H3 as Hidx.
        unfold decr_counter_high_spec in Hidx.
        destr_in Hidx; inv Hidx.
        apply (f_equal Z.of_nat) in H2.
        generalize (Int.unsigned_range idx); intros.
        rewrite Z2Nat.id in H2; [| omega].
        rewrite Nat2Z.inj_sub in H2; [| omega].
        cprim_step. repeat step_tac.
        + (** [decr_counter] return value *)
          unfold lift; cbn.
          rewrite Ptrofs.add_zero_l.
          pose proof MAX_COUNTER_range as Hmc_range.
          pose proof int_ptrofs_max as Hint_ptr.
          unfold Ptrofs.mul, Ptrofs.of_intu, Ptrofs.of_int.
          repeat rewrite Ptrofs.unsigned_repr; try omega; eauto.
        + reflexivity.
    Qed.

  End CodeLowSpecSim.

  (** ** Layer Relation *)
  Section LowHighSpecRel.

    (** We relate the overlay's abstract data and the underlay's concrete
      memory by requiring that for every item in the abstract [stack], the
      same item can be found at the appropriate place in memory. *)
    Inductive match_stack : mem -> block -> nat -> list Z -> Prop :=
    | match_stack_nil:
        forall m b,
          match_stack m b 0 nil
    | match_stack_intro:
        forall m b idx s x,
          Mem.load Mint32 m b (4 * Z.of_nat idx) = Some (Vint (Int.repr x)) ->
          match_stack m b idx s ->
          match_stack m b (S idx) (x :: s).

    Inductive match_data : stack_layerdata -> mem -> Prop :=
    | match_data_intro b:
        forall m (abs: stack_layerdata),
          find_symbol STACK = Some b ->
          match_stack m b (length (stack abs)) (stack abs) ->
          match_data abs m.

    (** This time our relation between the high and low abstract data is not
      empty. We require that the size of the stack is equal to the value of
      the counter. *)
    Record relate_data (hadt: stack_layerdata) (ladt: counter_layerdata) :=
      mkrelate_data {
        stack_counter_len: length (stack hadt) = counter ladt
      }.

    Definition abrel_components_stack_counter :
      abrel_components stack_layerdata counter_layerdata :=
      {|
        abrel_relate := relate_data;
        abrel_match  := match_data;
        abrel_new_glbl :=
          (STACK, Init_space (4 * Z.of_nat MAX_COUNTER) :: nil) ::
          nil
      |}.

    Global Instance rel_ops :
      AbstractionRelation _ _ abrel_components_stack_counter.
    Proof.
      constructor.
      - constructor; reflexivity.
      - intros.
        inv_abrel_init_props.
        econstructor; eauto.
        constructor.
      - repeat red; cbn. intros.
        inv H1; econstructor; eauto.
        generalize dependent y.
        induction (stack a); intros.
        + constructor.
        + inv H3.
          cbn; constructor; eauto.
          eapply Mem.load_unchanged_on; eauto.
          intros. red.
          exists STACK; eexists. cbn; split; auto.
      - decision.
    Qed.

    Definition abrel_stack_counter : abrel stack_layerdata counter_layerdata :=
      {|
        abrel_ops := abrel_components_stack_counter;
        abrel_prf := rel_ops
      |}.

    Definition stack_R : simrel _ _ := abrel_simrel _ _ abrel_stack_counter.

    (** These lemmas about [match_stack] will be useful later to show that the
      relation still holds after pushing a new item to the stack. *)

    (** If two memories [m1] and [m2] have the same values at every offset
      below some [idx], and the [match_stack] relation holds for stack [s] on
      [m1] up to [idx], then [match_stack] also holds for [s] on [m2] up to
      [idx]. *)
    Lemma match_stack_load_same : forall m1 m2 b idx s,
      (forall idx' x,
        (idx' < idx)%nat ->
        Mem.load Mint32 m1 b (4 * Z.of_nat idx') = Some (Vint x) ->
        Mem.load Mint32 m2 b (4 * Z.of_nat idx') = Some (Vint x)) ->
      match_stack m1 b idx s ->
      match_stack m2 b idx s.
    Proof.
      intros; induction H1; constructor; auto.
    Qed.

    (** If [match_stack] holds for stack [s] on [m1] up to [idx], and [m2] is
      the result of storing [x] at [idx] in [m1], then [match_stack] holds for
      [x] pushed onto [s] on [m2] up to [idx + 1]. *)
    Lemma match_stack_store : forall m1 m2 b idx s x,
      match_stack m1 b idx s ->
      Mem.store Mint32 m1 b (4 * Z.of_nat idx) (Vint x) = Some m2 ->
      match_stack m2 b (Datatypes.S idx) (Int.signed x :: s).
    Proof.
      intros.
      constructor.
      - rewrite Int.repr_signed. eapply Mem.load_store_same in H1; assumption.
      - inv H0.
        + constructor.
        + eapply (match_stack_load_same m1 m2); eauto.
          * intros.
            eapply (Mem.load_store_other Mint32 m1 b _ _ m2) in H1.
            rewrite H1; assumption.
            right. rewrite Nat2Z.inj_succ. unfold size_chunk. omega.
          * constructor; assumption.
    Qed.

  End LowHighSpecRel.

  (** ** Refinement Proofs *)
  Section LowHighSpecSim.

    Context `{ce: ClightCompositeEnv}.

    Lemma get_size_refine :
      (get_size ↦ get_size_cprimitive) ⊢ (stack_R, ∅) : get_size_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8. inv_monad H0. inv H0.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold get_size_high_spec in H4.
      do 3 eexists; split.
      - econstructor; eauto.
        unfold get_counter_high_spec.
        rewrite <- stack_counter_len0.
        eassumption.
      - split; constructor; eauto.
    Qed.

    Lemma push_refine :
      (push ↦ push_cprimitive) ⊢ (stack_R, ∅) : push_layer.
    Proof.
      Opaque Z.mul. (** here again to prevent cbn expanding 4 * _ *)
      refine_proof_tac.
      inv CStep. inv_generic_sem H8. inv H0. inv_monad H1.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold push_high_spec in H2.
      destr_in H2; inv H2.
      destruct (Mem.valid_access_store ym Mint32 b (4 * Z.of_nat (counter yd)) (Vint i))
        as (m' & Hstore).
      { split.
        - eapply (abrel_match_mem_perms _ _ _ 0 Cur Writable) in H0; eauto.
          cbn in H0; rewrite Z.add_0_r in H0; rewrite Zmax_left in H0; [| omega].
          red; cbn; intros. apply H0. omega.
        - apply Z.divide_factor_l.
      }
      do 3 eexists; split.
      - generalize MAX_COUNTER_range; intros.
        econstructor; eauto.
        + unfold get_counter_high_spec.
          rewrite <- (Nat2Z.id (counter _)); f_equal.
          rewrite <- (Int.unsigned_repr (Z.of_nat _)); [reflexivity | omega].
        + unfold incr_counter_high_spec. destr; [| omega].
          repeat f_equal.
          rewrite <- (Nat2Z.id (_ + _)); f_equal.
          rewrite <- (Int.unsigned_repr (Z.of_nat _)); [reflexivity |].
          rewrite Nat2Z.inj_add; cbn; omega.
        + rewrite Int.unsigned_repr; [eassumption | omega].
      - split.
        + constructor.
        + cbn. split.
          * eapply Mem.store_outside_extends; eauto.
            intros. eapply abrel_match_mem_perms in H2; eauto.
          * constructor.
            { constructor; cbn. omega.
            }
            { econstructor; cbn; eauto.
              rewrite <- stack_counter_len0 in Hstore.
              eapply match_stack_store; eauto.
            }
            { cbn; intros.
              specialize (abrel_match_mem_perms _ _ _ ofs k p H2 H3).
              destruct abrel_match_mem_perms as (NP & P).
              split; auto.
              red; intros. eapply Mem.perm_store_1; eauto.
            }
            { rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore).
              eauto.
            }
    Qed.

    (** Here again we find that we need the invariant to hold in order to
      complete the proof. This time we express the invariant preservation
      property by composing the relation [inv] with [stack_R] on both the left
      and right. This means that we want the invariants in both the over- and
      underlay to be preserved. Here is where the proofs that the high and low
      level specs preserve the invariants come into play, but because we
      declared them as typeclass instances these goals are solved automatically
      by [refine_proof_tac]. *)
    Lemma pop_refine :
      (pop ↦ pop_cprimitive) ⊢ (inv ∘ stack_R ∘ inv, ∅) : pop_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8. inv_monad H0.
      inverse_hyps.
      inv InvHi. cbn in cprimitive_inv_init_state_data_inv.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold pop_high_spec in H2.
      destr_in H2; inv H2.
      inv H1.
      do 3 eexists; split.
      - generalize MAX_COUNTER_range; intros.
        econstructor; eauto.
        + unfold decr_counter_high_spec. destr; [| omega].
          repeat f_equal.
          rewrite <- (Nat2Z.id (_ - _)); f_equal.
          rewrite <- (Int.unsigned_repr (Z.of_nat _)); [reflexivity |].
          rewrite Nat2Z.inj_sub; cbn; omega.
        + rewrite Int.unsigned_repr; [| xomega].
          rewrite <- stack_counter_len0; cbn; rewrite Nat.sub_0_r. eassumption.
      - split.
        + cbn. rewrite Int.repr_signed. constructor.
        + cbn. split; auto.
          constructor; cbn; auto.
          * constructor; cbn. omega.
          * econstructor; cbn; eauto.
    Qed.

  End LowHighSpecSim.

  (** ** Linking *)
  Section Linking.

    Definition stack_L : clayer stack_layerdata :=
      get_size_layer ⊕ push_layer ⊕ pop_layer.

    Definition stack_Σ : clayer counter_layerdata :=
      (get_size ↦ get_size_cprimitive
       ⊕ push ↦ push_cprimitive
       ⊕ pop ↦ pop_cprimitive).

    Definition stack_M : cmodule := Msize ⊕ Mpush ⊕ Mpop.

    Hint Resolve get_size_code get_size_refine
                 push_code push_refine
                 pop_code pop_refine : linking.

    Hint Resolve counter_pres_inv : linking.

    Theorem stack_link :
      counter_L ⊢ (inv ∘ stack_R ∘ inv, stack_M) : stack_L.
    Proof. link_tac stack_Σ. Qed.

    Lemma stack_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) stack_L.
    Proof. unfold stack_L. typeclasses eauto. Qed.

    Hint Resolve counter_link stack_link : linking.

    (** The final result we want to prove is that the behaviors allowed by the
      stack high level primitives are refined by the counter and stack C code
      evaluated on the base (empty) layer. *)
    Theorem stack_counter_link :
      base_L ⊢ (counter_R ∘ inv ∘ stack_R ∘ inv, counter_M ⊕ stack_M) : stack_L.
    Proof.
      apply (vdash_rel_equiv _ _ (counter_R ∘ (inv ∘ stack_R ∘ inv))).
      rewrite cat_compose_assoc; rewrite cat_compose_assoc; reflexivity.
      eapply vcomp_rule; auto with linking.
    Qed.

  End Linking.

End Stack.
