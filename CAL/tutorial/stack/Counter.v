(**
 * Counter.v
 *
 * A single layer implementing a bounded counter.
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
Require Import PseudoJoinReflection.
Require Import ClightModules.
Require Import ClightXSemantics.
Require Import AbstractData.
Require Import AbstractionRelation.

(** This file makes use of some tactics and lemmas defined in a library created
  for this tutorial. It is not necessary for you to read this file in order to
  follow the tutorial. *)
Require Import TutoLib.

(** This file is meant to demonstrate how the layer calculus used in CertiKOS
  works by implementing a simple layer consisting of a global counter variable
  [COUNTER] that can be accessed and manipulated by the primitives
  [get_counter], [incr_counter], and [decr_counter]. The counter variable is
  bounded within in the range [0] to [MAX_COUNTER] and the semantics are such
  that calling [incr_counter] (or [decr_counter]) when [COUNTER] is at its high
  (or low) bound results in an error. The underlay upon which this layer is
  built contains no abstract data or primitives. The overlay consists of the
  primitives described above and a [counter] of type [nat] as abstract data
  with the invariant that [counter <= MAX_COUNTER]. *)

Open Scope Z_scope.

(** The only constraint on the value of [MAX_COUNTER] is that it is less than
  the maximum unsigned integer divided by [4] since it will be used as an array
  index later on. We mark it [Opaque] to ensure that later proofs do not depend
  directly on its value. *)
Definition MAX_COUNTER : nat := 10.
Fact MAX_COUNTER_range : 4 * Z.of_nat MAX_COUNTER <= Int.max_unsigned.
Proof.
(** TUTORIAL: complete proof. Possible in 1 tactic. *)
Admitted.
Global Opaque MAX_COUNTER.

(** These are the identifiers for the primitives and the global counter
  variable. *)
Definition get_counter : ident := 1%positive.
Definition incr_counter : ident := 2%positive.
Definition decr_counter : ident := 3%positive.
Definition COUNTER : ident := 4%positive.

Notation MAX_COUNTER_i := (Int.repr (Z.of_nat MAX_COUNTER)).

Section Counter.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.

  (** ** Abstract Data *)
  Section AbsData.
    (** *** Underlay **)

    (** The underlay has no abstract data, we model this as [unit] and declare
      [unit] as layer data through the two typeclasses [AbstractDataOps] and
      [AbstractData].

      [AbstractDataOps] requires several fields. First, an initial element of
      the desired type ([unit] in our case). The other fields are predicates
      and invariants that we can simply instantiate with [True] predicates for
      the moment.

      The field [data_inv] specifies an invariant of the abstract data that
      must be preserved by all operations on abstract data.

      The field [data_inject] specifies how data is injected, i.e. how
      injections relate these abstract data, in a manner close to CompCert's
      [val_inject]. The only time this begins to get interesting is when you
      are dealing with pointers. *)
    Instance base_data_ops : AbstractDataOps unit :=
      {|
        init_data := tt;
        data_inv := fun _ => True;
        data_inject := fun _ _ _ => True
      |}.

    (** Now, we prove some properties of the aforementioned predicates. This is
       trivial in our case since we chose [True]. *)
    Instance base_data : AbstractData unit.
    Proof. repeat constructor. Qed.

    (** We now pack those into a [layerdata] record. *)
    Definition base_layerdata : layerdata :=
      {|
        ldata_type := unit;
        ldata_ops  := base_data_ops;
        ldata_prf  := base_data
      |}.

    (** We can now define the underlay, [base_L], as the empty layer
      interface. *)
    Definition base_L : clayer base_layerdata := ∅.

    (** *** Overlay **)

    (** We want our overlay to abstract a counter, hence our abstract data will
      consist of a record [counter_data] that encapsulates this counter as a
      natural number. Then, we declare this abstract data as appropriate layer
      data, as before. *)
    Record counter_data : Type := { counter: nat }.

    (** We initialize [counter] to [0] and require that it is never greater
      than [MAX_COUNTER]. *)
    Instance counter_data_data_ops : AbstractDataOps counter_data :=
      {|
        init_data := {| counter := 0 |};
        data_inv := fun d => (counter d <= MAX_COUNTER)%nat;
        data_inject := fun f d1 d2 => True
      |}.

    (** This time we must prove that the initial abstract state ([counter = 0])
      satisfies the invariants ([0 <= MAX_COUNTER]). *)
    Instance counter_data_data : AbstractData counter_data.
    Proof.
      repeat constructor.
      cbv; omega.
    Qed.

    Definition counter_layerdata : layerdata :=
      {|
        ldata_type := counter_data;
        ldata_ops  := counter_data_data_ops;
        ldata_prf  := counter_data_data
      |}.

  End AbsData.

  (** ** High Level Specifications *)
  Section HighSpec.
    (** We now specify the behaviour of the primitives we will expose through
      our new layer. These are expressed as functions from [counter_data] to
      some other type. *)

    (** [get_counter] simply returns the current value of the counter. *)
    Definition get_counter_high_spec (abs: counter_layerdata) : nat :=
      counter abs.

    (** We prove that our high level specs preserve the invariant
      ([counter <= MAX_COUNTER]) by declaring them as instances of
      [GenSemPreservesInvariant]. This is important so we can make use of
      the invariant later on in the code or refinement proofs. In particular,
      the code proof of the [pop] primitive in the Stack layer relies on this
      fact. *)
    Global Instance get_counter_preserves_invariant :
      GenSemPreservesInvariant counter_layerdata get_counter_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv Hsem.
      inv_monad H2.
      inv H2.
      assumption.
    Qed.

    (** To incorporate this specification in a layer interface, we must wrap it
      as a [cprimitive]. A [cprimitive] is merely a relation between inputs
      (list of arguments and starting memory state) and outputs (return value
      and resulting memory state), along with some properties. The [cgensem]
      function automatically discharges some proof obligations for us, provided
      that the specification is of a certain form ([SemOf]). *)
    Definition get_counter_high_sem : cprimitive counter_layerdata :=
      cgensem counter_layerdata get_counter_high_spec.

    (** We can then define a layer consisting of just the [get_counter]
      primitive. *)
    Definition get_counter_layer : clayer counter_layerdata :=
      get_counter ↦ get_counter_high_sem.

    (** Because [incr_counter] can fail, it returns a value of type
      [option (counter_data * nat)]. In the case where the counter is not
      already at its maximum value it returns a new abstract data with the
      incremented counter, along with the value of the incremented counter.
      Otherwise it returns [None], representing an error. *)
    Definition incr_counter_high_spec (abs: counter_layerdata) :
        option (counter_layerdata * nat) :=
      if decide (counter abs < MAX_COUNTER)%nat
        then Some ({| counter := counter abs + 1 |}, (counter abs + 1)%nat)
        else None.

    Global Instance incr_counter_preserves_invariant :
      GenSemPreservesInvariant counter_layerdata incr_counter_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      inv_monad H2.
      unfold incr_counter_high_spec in H4.
      destruct (decide (counter d < MAX_COUNTER)%nat).
      - inv H4.
        cbn.
        omega.
      - discriminate H4.
    Qed.

    Definition incr_counter_high_sem : cprimitive counter_layerdata :=
      cgensem counter_layerdata incr_counter_high_spec.

    Definition incr_counter_layer : clayer counter_layerdata :=
      incr_counter ↦ incr_counter_high_sem.

    (** [decr_counter] is defined similarly to [incr_counter]. *)
    Definition decr_counter_high_spec (abs: counter_layerdata) :
        option (counter_layerdata * nat) :=
      if decide (0 < counter abs)%nat
        then Some ({| counter := counter abs - 1 |}, (counter abs - 1)%nat)
        else None.

    Global Instance decr_counter_preserves_invariant :
      GenSemPreservesInvariant counter_layerdata decr_counter_high_spec.
    Proof.
      (** TUTORIAL: Prove that decr_counter preserves the layer invariant *)
    Admitted.

    Definition decr_counter_high_sem : cprimitive counter_layerdata :=
      cgensem counter_layerdata decr_counter_high_spec.

    Definition decr_counter_layer : clayer counter_layerdata :=
      decr_counter ↦ decr_counter_high_sem.

  End HighSpec.

  (** ** Module Implementation *)
  Section Code.
    (** We now provide implementations of our primitives as Clight functions.
      Functions are encoded in records with their return type in field
      [fn_return], the types of their parameters, local variables and temporary
      variables in [fn_params], [fn_vars] and [fn_temps] respectively, and the
      function body in [fn_body].

      The difference between local and temporaries variables is that the former
      are stored inside the memory while the latter are part of an abstract
      semantic environment which is not part of the memory.

      We omit a description of the field [fn_callconv] here, as it is not
      relevant to this tutorial.

      The corresponding C code for each function is also provided. *)

    (** [f_get_counter] is implemented as expected. *)
    (**
<<
int get_counter() {
  return COUNTER;
}
>> *)
    Definition f_get_counter :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body := Sreturn (Some (Evar COUNTER tuint))
      |}.

    Program Definition inlinable_f_get_counter : function :=
      inline f_get_counter _.

    (** [f_incr_counter] handles the case where [counter < MAX_COUNTER] as
      expected. It handles the failure case by not incrementing [COUNTER] and
      returning an error code represented by [MAX_COUNTER + 1]. *)
    (**
<<
int incr_counter() {
  if (counter < MAX_COUNTER) {
    COUNTER = COUNTER + 1;
    return COUNTER;
  } else {
    return MAX_COUNTER + 1;
  }
}
>> *)
    Definition f_incr_counter :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sifthenelse (Ebinop Olt (Evar COUNTER tuint) (Econst_int MAX_COUNTER_i tuint) tuint)
                      (Ssequence
                        (Sassign (Evar COUNTER tuint)
                                 (Ebinop Oadd
                                         (Evar COUNTER tuint)
                                         (Econst_int (Int.repr 1) tuint)
                                         tuint))
                        (Sreturn (Some (Evar COUNTER tuint))))
                      (Sreturn (Some (Ebinop Oadd
                                             (Econst_int MAX_COUNTER_i tuint)
                                             (Econst_int (Int.repr 1) tuint)
                                             tuint)))
      |}.

    Program Definition inlinable_f_incr_counter : function :=
      inline f_incr_counter _.

    (** [f_decr_counter] handles failure in the same way as
      [f_incr_counter]. *)
    (**
<<
int decr_counter() {
  if (0 < counter) {
    COUNTER = COUNTER - 1;
    return COUNTER;
  } else {
    return MAX_COUNTER + 1;
  }
}
>> *)
    Definition f_decr_counter :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tuint) (Evar COUNTER tuint) tuint)
                      (Ssequence
                        (Sassign (Evar COUNTER tuint)
                                 (Ebinop Osub
                                         (Evar COUNTER tuint)
                                         (Econst_int (Int.repr 1) tuint)
                                         tuint))
                        (Sreturn (Some (Evar COUNTER tuint))))
                      (Sreturn (Some (Ebinop Oadd
                                             (Econst_int MAX_COUNTER_i tuint)
                                             (Econst_int (Int.repr 1) tuint)
                                             tuint)))
      |}.

    Program Definition inlinable_f_decr_counter : function :=
      inline f_decr_counter _.

    (** Similar to the layers we defined for each of the primitive high specs,
      we can also define modules consisting of the Clight implementations of
      the primitives. *)
    Definition Mget : cmodule := get_counter ↦ inlinable_f_get_counter.
    Definition Mincr : cmodule := incr_counter ↦ inlinable_f_incr_counter.
    Definition Mdecr : cmodule := decr_counter ↦ inlinable_f_decr_counter.

  End Code.

  (** ** Low Level Specifications *)
  Section LowSpec.
    (** Next we define a low-level specification of each primitive, i.e. a
      specification with respect to the underlay. We define those as transition
      relations [step] of type [list val -> mem -> val -> mem -> Prop]. The
      meaning of [step args (m, d) res (m', d')] is the following:
      given arguments [args] and starting from a memory state [m] with
      abstract data [d], the primitive returns a value [res], the memory state
      is updated to [m'] and the abstract data is now [d']. *)

    Definition get_counter_csig := mkcsig Ctypes.Tnil tuint.

    Inductive get_counter_step :
      csignature -> list val * mwd base_layerdata -> val * mwd base_layerdata -> Prop :=
    | get_counter_step_intro m d cb i:
        (** The [COUNTER] global variable is stored at some memory block [sb] *)
        forall (HCb: find_symbol COUNTER = Some cb),
        (** The value at block [cb] is an integer [i] *)
        Mem.load Mint32 m cb 0 = Some (Vint i) ->
        (** [get_counter] takes no arguments, returns [i], and makes no changes
          to abstract state or memory *)
        get_counter_step get_counter_csig (nil, (m, d)) (Vint i, (m, d)).

    Definition incr_counter_csig := mkcsig Ctypes.Tnil tuint.

    (** TUTORIAL: Replace the four Falses in this inductive definition with appropriate hypotheses *)
    Inductive incr_counter_step :
      csignature -> list val * mwd base_layerdata -> val * mwd base_layerdata -> Prop :=
    | incr_counter_step_intro m d cb (i : int) j m':
        (** The [COUNTER] global variable is stored at some memory block [cb] *)
        forall (HCb: find_symbol COUNTER = Some cb),
        (** The value at block [cb] is an integer [i] *)
        False ->
        (** [i] is less than [MAX_COUNTER] *)
        False ->
        (** A new integer [j] is defined as [i + 1] *)
        False ->
        (** Storing [j] at block [cb] results in a new memory [m'] *)
        False ->
        (** [incr_counter] takes no arguments, returns [j], changes [m] to
          [m'], and makes no change to abstract state *)
        incr_counter_step incr_counter_csig (nil, (m, d)) (Vint j, (m', d)).

    Definition decr_counter_csig := mkcsig Ctypes.Tnil tuint.

    Inductive decr_counter_step :
      csignature -> list val * mwd base_layerdata -> val * mwd base_layerdata -> Prop :=
    | decr_counter_step_intro m d cb i j m':
        (** The [COUNTER] global variable is stored at some memory block [cb] *)
        forall (HCb: find_symbol COUNTER = Some cb),
        (** The value at block [cb] is an integer [i] *)
        Mem.load Mint32 m cb 0 = Some (Vint i) ->
        (** [i] is greater than [0] *)
        0 < Int.unsigned i ->
        (** A new integer [j] is defined as [i - 1] *)
        j = Int.sub i Int.one ->
        (** Storing [j] at block [cb] results in a new memory [m'] *)
        Mem.store Mint32 m cb 0 (Vint j) = Some m' ->
        (** [decr_counter] takes no arguments, returns [j], changes [m] to
          [m'], and makes no change to abstract state *)
        decr_counter_step decr_counter_csig (nil, (m, d)) (Vint j, (m', d)).

    (** As with the high-level specifications, to use the low-level specs in a
      layer definition, we must wrap it in a [cprimitive] using the
      [mkcprimitive] function. This generates a proof obligation that says the
      return value has the appropriate type. *)
    Program Definition get_counter_cprimitive : cprimitive base_layerdata :=
      mkcprimitive _ get_counter_step get_counter_csig _.
    Next Obligation.
      inv H0. cbn. trivial.
    Qed.

    Program Definition incr_counter_cprimitive : cprimitive base_layerdata :=
      mkcprimitive _ incr_counter_step incr_counter_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition decr_counter_cprimitive : cprimitive base_layerdata :=
      mkcprimitive _ decr_counter_step decr_counter_csig _.
    Next Obligation.
      now inv H0.
    Qed.

  End LowSpec.

  (** ** Code Proofs *)
  Section CodeLowSpecSim.
    (** Now we want to show that these implementations are correct with respect
      to the underlay and overlay. We will do that in two steps for each
      primitive. First, we prove that the module implementation together with
      the underlay refines the low-level specification. Later, we will prove
      that the low-level specification refines the high-level specification. *)

    Context `{ce: ClightCompositeEnv}.

    (** We state our theorems in the form [underlay ⊢ (R, module) : overlay]
      which says that the code in the module executed on the underlay refines
      the overlay with respect to some relation R. What we actually want to
      prove, however, is a simulation diagram like the following:

      (hargs, hstate)    high_spec_step   (hresult, hstate')
          ||            --------------->        ||
      R   ||                                    ||  R
          ||                                    ||
          \/            --------------->        \/
      (largs, lstate)    low_spec_step     (lresult, lstate')

      In the code proofs, the overlay is the low level spec of some C
      primitive, and R is typically [id]. In this case we can simplify the
      diagram into:

                      high_spec_step
      (args, state)  ---------------> (result, state')
                      low_spec_step

      The tactic [code_proof_tac] will automatically convert the goal into
      the appropriate simulation diagram. You will then have to prove that the
      [cprimitive_step] relation holds between the initial and final states.
      [cprim_step] will convert this goal into one that states that the final
      state is reachable in a sequence of Clight steps. The [step_tac] tactic
      will try to prove all of the Clight smallstep semantics details and just
      leave you with a few remaining goals. *)

    Lemma get_counter_code :
      base_L ⊢ (id, Mget) : (get_counter ↦ get_counter_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      cprim_step. repeat step_tac.
    Qed.

    Lemma incr_counter_code :
      base_L ⊢ (id, Mincr) : (incr_counter ↦ incr_counter_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      contradiction.
      (** TUTORIAL: Replace invalid contradiction with an actual proof. *)
    Admitted.

    Lemma decr_counter_code :
      base_L ⊢ (id, Mdecr) : (decr_counter ↦ decr_counter_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      cprim_step. repeat step_tac.
      - cbn. change (Int.repr 0) with Int.zero.
        instantiate (1 := Int.ltu Int.zero i).
        destruct (Int.ltu Int.zero i); reflexivity.
      - destr.
        + (** 0 < i *)
          repeat step_tac.
          * (** Storing i - 1 gives m' *)
            unfold lift; cbn.
            rewrite Ptrofs.unsigned_zero.
            unfold Int.one in H10. rewrite H10. reflexivity.
          * (** Loading m' gives i - 1 *)
            unfold lift; cbn.
            rewrite Ptrofs.unsigned_zero.
            eapply Mem.load_store_same; eauto.
          * (** Return value is i - 1 *)
            reflexivity.
        + (** 0 >= i *)
          unfold Int.ltu in Heqb. destr_in Heqb; [discriminate | contradiction].
    Qed.

  End CodeLowSpecSim.

  (** ** Layer Relation *)
  Section LowHighSpecRel.
    (** Finally, we want to match the high-level specifications of our
      primitives to the low-level specifications.

      To achieve this, we need to build an abstraction relation ([abrel]),
      which requires two components:

      - [match_data]: a matching relation between the abstract data in the
        overlay and the memory state in the underlay

      - [relate_data]: a relation between high and low abstract data *)

    (** In our case, the [match_data] predicate states that the memory
      associated with the [COUNTER] variable must match [counter] in the high
      abstract data. *)

    Inductive match_data : counter_layerdata -> mem -> Prop :=
    | match_data_intro:
        forall m b i (abs: counter_layerdata),
          (** The [COUNTER] global variable is stored at some memory block [b] *)
          find_symbol COUNTER = Some b ->
          (** The value at block [b] is an integer [i] *)
          Mem.load Mint32 m b 0 = Some (Vint i) ->
          (** The value of [counter] in the abstract data equals [i] *)
          counter abs = Z.to_nat (Int.unsigned i) ->
          match_data abs m.

    (** Since the abstract data of the underlay is just [unit], [relate_data]
      is trivial. *)
    Record relate_data (hadt: counter_layerdata) (ladt: base_layerdata) :=
      mkrelate_data {
        (** In a more complicated example we might have relations like:

          var1 hadt = var1 ladt

          or

          var1 hadt = var2 ladt + var3 ladt *)
      }.

    (** We now wrap our relations and a list of the global variables'
      initialization information intro an [abrel_components] record and declare
      it an instance of [AbstractionRelation]. We must now prove the following
      properties:

      - The [init_data] of the high and low abstract data types must be related
        by [abrel_relate].

      - Given information about the newly-introduced globals, we must show that
        the initial abstract data matches the initial low memory state.

      - [abrel_match] should be preserved by [Mem.unchanged_on] in the part of
        memory where the global variables are stored. In other words, the match
        relation should only depend on the memory used by the global variables.

      (** TODO: why is there a threshold at all? *)
      - The newly-introduced global variables must have identifiers lower than
        the global threshold. *)

    Definition abrel_components_counter_base :
      abrel_components counter_layerdata base_layerdata :=
      {|
        abrel_relate := relate_data;
        abrel_match  := match_data;
        abrel_new_glbl :=
          (COUNTER, AST.Init_int32 Int.zero :: nil) ::
          nil
      |}.

    Global Instance rel_ops :
      AbstractionRelation _ _ abrel_components_counter_base.
    Proof.
      constructor.
      - (** Initial abs data matches *)
        constructor.
      - (** Initial high abs data matches initial low memory *)
        intros.
        inv_abrel_init_props.
        cbn.
        econstructor; eauto.
        + eapply aip_load; eauto.
        + cbn; rewrite Int.unsigned_zero; reflexivity.
      - (** If global variable memory is unchanged, [abrel_match] is preserved *)
        repeat red; cbn. intros.
        inv H1; econstructor; eauto.
        eapply Mem.load_unchanged_on; eauto.
        cbn; intros; red.
        exists COUNTER; eexists. cbn; split; auto.
      - (** Global variable identifiers are lower than [glob_threshold] *)
        decision.
    Qed.

    (** Finally we wrap everything into an [abrel] record, which just
      contains the [abrel_components] plus the proof that they are an instance
      of [AbstractionRelation]. *)
    Definition abrel_counter_base : abrel counter_layerdata base_layerdata :=
      {|
        abrel_ops := abrel_components_counter_base;
        abrel_prf := rel_ops
      |}.

    (** TODO: explain simrel vs abrel? Try to hide it somehow? *)
    (** It will be convenient to wrap this into a simrel with abrel_simrel. *)
    Definition counter_R : simrel _ _ := abrel_simrel _ _ abrel_counter_base.

  End LowHighSpecRel.

  (** ** Refinement Proofs *)
  Section LowHighSpecSim.

    Context `{ce: ClightCompositeEnv}.

    (** We can finally prove a simulation between the overlay (with the
      high-level specification of our primitive) and the low-level
      specification of the primitive. In these proofs, the module is empty
      ([∅]) because it is purely an abstraction; no additional code is needed.
      The [refine_proof_tac] tactic is similar to [code_proof_tac] and will
      also convert your goal into a simulation diagram. *)

    Lemma get_counter_refine :
      (get_counter ↦ get_counter_cprimitive) ⊢ (counter_R, ∅) : get_counter_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8. inv_monad H0. inv H0.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      unfold get_counter_high_spec in H4.
      assert (Hz: z = i).
      { rewrite H4 in H2.
        apply Z2Nat.inj in H2; try apply Int.unsigned_range.
        rewrite <- (Int.repr_unsigned z), <- (Int.repr_unsigned i).
        f_equal; assumption.
      }
      subst z.
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + constructor.
        + split; auto.
    Qed.

    Lemma incr_counter_refine :
      (incr_counter ↦ incr_counter_cprimitive) ⊢ (counter_R, ∅) : incr_counter_layer.
    Proof.
      (** TUTORIAL: Prove that incr_counter_layer simulates the C implementation of incr_counter *)
    Admitted.

    Lemma decr_counter_refine :
      (decr_counter ↦ decr_counter_cprimitive) ⊢ (counter_R, ∅) : decr_counter_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8. inv_monad H0.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      unfold decr_counter_high_spec in H2.
      destr_in H2; inv H2.
      assert (Hi_lower: 0 < Int.unsigned i).
      { pose proof l as Hcounter_lower; rewrite H3 in Hcounter_lower.
        apply Nat2Z.inj_lt in Hcounter_lower. rewrite Z2Nat.id in Hcounter_lower.
        - assumption.
        - apply Int.unsigned_range.
      }
      assert (Hz: z = Int.sub i Int.one).
      { unfold Int.sub, Int.one.
        generalize (Int.unsigned_range z); intros.
        rewrite Int.unsigned_repr; [| cbn; omega].
        rewrite <- (Int.repr_unsigned z); f_equal.
        apply Z2Nat.inj; try omega.
        rewrite <- H6. rewrite H3.
        rewrite Z2Nat.inj_sub; [reflexivity | omega].
      }
      subst z.
      destruct (Mem.valid_access_store ym Mint32 b 0 (Vint (Int.sub i Int.one)))
        as (m' & Hstore).
      { split.
        - eapply (abrel_match_mem_perms _ _ _ 0 Cur Writable) in H0; now eauto.
        - apply Z.divide_0_r.
      }
      do 3 eexists; split.
      - econstructor; eauto.
      - split; cbn.
        + constructor.
        + split.
          * eapply Mem.store_outside_extends; eauto.
            intros. eapply abrel_match_mem_perms in H2; eauto.
          * constructor.
            { (** Abs data relate *)
              constructor.
            }
            { (** High abs data matches low memory *)
              cbn. econstructor; eauto.
              erewrite Mem.load_store_same; cbn; eauto.
              reflexivity.
            }
            { (** Global variable permissions *)
              cbn; intros.
              specialize (abrel_match_mem_perms _ _ _ ofs k p H2 H4).
              destruct abrel_match_mem_perms as (NP & P).
              split; auto.
              red; intros. eapply Mem.perm_store_1; eauto.
            }
            { (** Global variable memory blocks are valid *)
              rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore).
              eauto.
            }
    Qed.

  End LowHighSpecSim.

  (** ** Linking *)
  Section Linking.

    (** We can now define the complete Counter layer by composing the high
      level specs. *)
    Definition counter_L : clayer counter_layerdata :=
      get_counter_layer ⊕ incr_counter_layer ⊕ decr_counter_layer.

    (** The low level specs (often represented as [σ], hence [Σ] for their
      composition) also form an intermediate layer between [base_L] and
      [counter_L]. *)
    Definition counter_Σ : clayer base_layerdata :=
      (get_counter ↦ get_counter_cprimitive
       ⊕ incr_counter ↦ incr_counter_cprimitive
       ⊕ decr_counter ↦ decr_counter_cprimitive).

    Definition counter_M : cmodule := Mget ⊕ Mincr ⊕ Mdecr.

    (** As a last step, we must horizontally and vertically compose the
      code and refinement proofs we have done so far for individual primitives.
      The result is a statement that the C code in [counter_M] evaluated on top
      of [base_L] refines the behaviours specified by the specs in [counter_L].
      This means that other layers that build on this one can write primitives
      in terms of the high level specs in [counter_L] and be sure that any
      properties proved will still hold in the C implementation. *)

    (** This linking step is usually fairly mechanical and can be largely
      automated using custom tactics and hint databases. Here we show the proof
      both with and without automation. *)

    Theorem counter_link :
      base_L ⊢ (counter_R, counter_M) : counter_L.
    Proof.
      (** We want to prove the linking in two steps:
        - [base_L ⊢ (id, counter_M) : counter_Σ]
        - [counter_Σ ⊢ (counter_R, ∅) : counter_L]

        So first we must rewrite [counter_R] so it is composed with [id] on the
        left, and [counter_M] so it is composed with the empty module on the
        right. *)
      apply (vdash_rel_equiv _ _ (id ∘ counter_R)).
      { apply cat_compose_id_left. }
      apply (vdash_module_le _ _ _ _ _ (counter_M ⊕ ∅)).
      constructor.
      reflexivity.
      (** Now we can use the vertical composition rule to split our goal. *)
      apply (vcomp_rule _ _ _ _ _ _ counter_Σ).
      constructor.
      - (** Then we want to split the modules and low level specs into
          the individual primitives so we can apply the code proofs
          we did before. *)
        apply hcomp_rule.
        constructor.
        + apply get_counter_code.
        + apply hcomp_rule.
          constructor.
          apply incr_counter_code.
          apply decr_counter_code.
      - (** For the refinement portion we have the empty module because no
          extra code is needed to abstract from the low to the high level
          specs. [pjr] is a reflection tactic that can solve goals involving
          [⊕] and [≤]. *)
        unfold counter_Σ.
        apply (vdash_module_le _ _ _ _ _ (∅ ⊕ ∅)).
        constructor.
        reflexivity.
        apply hcomp_rule.
        constructor.
        + eapply conseq_le_left.
          constructor.
          * apply get_counter_refine.
          * pjr.
        + apply (vdash_module_le _ _ _ _ _ (∅ ⊕ ∅)).
          constructor.
          reflexivity.
          apply hcomp_rule.
          constructor.
          * eapply conseq_le_left.
            constructor.
            -- apply incr_counter_refine.
            -- pjr.
          * eapply conseq_le_left.
            constructor.
            -- apply decr_counter_refine.
            -- pjr.
    Qed.

    Hint Resolve get_counter_code get_counter_refine
                 incr_counter_code incr_counter_refine
                 decr_counter_code decr_counter_refine : linking.

    (** The tactic [link_tac] essentially repeats the steps seen in the manual
      proof as many times as necessary and uses the [linking] Hint database to
      figure out which code and refinement proofs to use. *)
    Theorem counter_link_auto :
      base_L ⊢ (counter_R, counter_M) : counter_L.
    Proof. link_tac counter_Σ. Qed.

    (** [ForallPrimitive] allows us to state properties that hold for every
      primitive in a layer. We want to use it here to check that everything in
      the layer preserves its invariants. This can be solved automatically with
      [typeclasses eauto] (assuming of course that an instance of
      [CPrimitivePreservesInvariant] actually exists for each primitive. A
      little unfolding might be necessary to help the proof search recognize
      the structure of the layer. *)

    Lemma base_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) base_L.
    Proof. typeclasses eauto. Qed.

    Lemma counter_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) counter_L.
    Proof. unfold counter_L. typeclasses eauto. Qed.

    Hint Resolve base_pres_inv counter_pres_inv counter_link : linking.

    (** Although we did not need to make use of the layer invariant in order to
      complete our simulation proofs, because we know that each of our
      primitives preserves the invariants, we can prove that the linking still
      holds when we require that the invariants of the under- and overlay are
      preserved. *)
    Theorem counter_link_inv :
      base_L ⊢ (inv ∘ counter_R ∘ inv, counter_M) : counter_L.
    Proof.
      apply conseq_rule with base_L counter_L; [constructor | | |]; auto with linking.
    Qed.

  End Linking.

End Counter.
