Require Export compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.common.AST.
Require Export compcert.common.Values.
Require Export compcert.common.AST.
Require Export compcert.common.Globalenvs.
Require Export compcert.common.Memdata.
Require Export compcertx.common.MemoryX. (* for storebytes_empty, free_range *)
Require Export liblayers.lib.Decision.
Require Export liblayers.logic.Structures.
Require Export liblayers.logic.LayerData.
Require Export liblayers.compcertx.CompcertStructures.
Require Export liblayers.compcertx.InitMem.
Require Export AbstractData.
Require Export MemWithData.


(** * Preliminaries *)

(** Specialize [rel_incr] to use [(≤)]. *)

Notation "'incr' p R" := (rel_incr (≤) (fun p => R) p)
  (at level 100, p at level 0, R at level 0)
  : rel_scope.


(** * Simulation relations blueprints *)

Section DEFINITION.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2: layerdata}.
  Local Opaque mwd_ops.

  (** ** Components *)

  (** This is the most general definition of a simulation relation
    toolkit that we use. We are given two memory models, and a carrier
    type for the relation (which generalizes [meminj]). We also have
    two basic relation components, indexed by elements of the carrier
    type: [match_mem] specifies how memory states should be related,
    whereas [match_block] specifies how block identifiers should be
    related. From these two components, it is possible to build up
    ways to relate more complex states such as [Clight.state] or
    [Asm.state]. The carrier type ensures that the constituent memory
    state, values, pointers, etc. are related in a consistent way.

    We also specify a preorder on the carrier type (which generalizes
    [inject_incr]), which [match_block] (and derived relations) should
    be consistent with. This is because the simulation diagram of some
    memory operations (namely [Mem.alloc]) use a final parameter
    [p' : param] different from the initial parameter [p : param].
    To ensure that other components of the state remain related, in
    such cases we require that [p ≤ p'].

    Finally, the relations on Compcert values ([val], [memval]) are
    built from [match_block] in nearly the same way for all of our
    simulation relations (identical values are related, as well as
    pointers with related block identifiers and identical offsets).
    But there is one aspect that differs between different simulation
    relations: with some relations we want [Vundef] and [Undef] on the
    left to be related to any values on the right (ie. be bottom
    elements), whereas for other relations we only want them to be
    related to themselves. The obvious solution is to specify for each
    relation a flag indicating which case we're in. However this is
    incompatible with composition. Consider a relation [R1] which
    relates [Vundef] to anything (flag set), and a relation [R2] which
    only relates it to itself (flag cleared). The composite relation
    [R1;R2] will relate [Vundef] to most values, but there may be a
    block b' on the right such that there is no b related to it on the
    left by [R2] (∀ b, ¬ b R2 b'). In this case [Vundef] on the left
    will not be related by [R1;R2] to [Vptr b' 0] on the right,
    because there is no intermediate value for the composition to use.
    Because of these contradictory situations, there is no
    setting for the flag that describes the composite relation
    appropriately.

    To address this, we generalize from there and split the flag into
    two part: the proposition [simrel_undef_matches_values] determines
    whether [Vundef] matches all non-pointer values, and the predicate
    [simrel_undef_matches_pointer] indicates which pointer values
    [Vundef] additionnaly matches. If some pointer are related to
    [Vundef], then non-pointer values should all be related to
    [Vundef] as well. Conversely, if [simrel_undef_matches_values] is
    set, then any block [b2] related to some block [b1] on the left by
    [match_block] should be related to [Vundef] as well. *)

  Record simrel_components :=
    {
      simrel_world: Type;
      simrel_acc :> Le simrel_world;
      simrel_undef_matches_values_bool: bool;
      simrel_undef_matches_block: simrel_world -> block -> Prop;
      simrel_new_glbl: list (ident * list AST.init_data);
      simrel_meminj: simrel_world -> meminj;
      match_mem: simrel_world -> rel (mwd D1) (mwd D2)
    }.

  Global Existing Instance simrel_acc.

  (** In what follows we declare many typeclass instances with a
    [simrel_undef_matches_*] premise. To make sure they work as
    expected, we declare them as typeclasses. We also show that
    [simrel_undef_matches_values] is decidable, since it is defined
    from a boolean. *)

  Existing Class simrel_undef_matches_block.

  Class simrel_undef_matches_values (R: simrel_components) :=
    simrel_undef_matches_values_true:
      simrel_undef_matches_values_bool R = true.

  Global Instance simrel_undef_matches_values_dec R:
    Decision (simrel_undef_matches_values R) :=
      decide_booleq _ _.

  (** ** Relations derived from [simrel_meminj] *)

  (** Compcert usually passes pointers around as separate block and
    offset arguments. Since we can't relate those independently
    (because the offset shift is specific to each block), we instead
    relate (block, offset) pairs and use [rel_curry] to construct our
    [Monotonicity} relations.

    Relating pointers is complicated because of the interaction
    between the abstract [Z] offsets that are used by the memory model
    and the [ptrofs] concrete machine representations that are used to
    build [val]ues. The basic relation [match_ptr] relates abstract
    pointers in the obvious way, while [match_ptrbits] relates
    concrete pointers as is done in [Val.inject]. *)

  Inductive match_ptr R p: relation (block * Z)%type :=
    match_ptr_intro b1 ofs1 b2 delta:
      simrel_meminj R p b1 = Some (b2, delta) ->
      match_ptr R p (b1, ofs1) (b2, ofs1 + delta)%Z.

  Inductive match_ptrbits R p: relation (block * ptrofs)%type :=
    match_ptrbits_intro b1 ofs1 b2 delta:
      simrel_meminj R p b1 = Some (b2, delta) ->
      match_ptrbits R p (b1, ofs1) (b2, Ptrofs.add ofs1 (Ptrofs.repr delta)).

  (** For [Mem.free] we need to relate a whole range of abstract
    pointers in the form of an (ofs, lo, hi) triple. *)

  Inductive match_ptrrange R p: relation (block * Z * Z)%type :=
    match_ptrrange_intro b1 ofs1 b2 ofs2 sz:
      RIntro
        (match_ptr R p (b1, ofs1) (b2, ofs2))
        (match_ptrrange R p) (b1, ofs1, ofs1+sz)%Z (b2, ofs2, ofs2+sz)%Z.

  Global Existing Instance match_ptrrange_intro.

  (** For operations that manipulate blocks, we can use the two
    relations below: the weaker [match_block] relates two blocks
    according to [simrel_meminj], no matter what the offset shift
    is. The stronger [match_block_sameofs] only relates blocks that
    correspond to one another with no shift in offset. *)

  Definition match_block R p b1 b2 :=
    exists delta, simrel_meminj R p b1 = Some (b2, delta).

  Definition match_block_sameofs R p b1 b2 :=
    simrel_meminj R p b1 = Some (b2, 0%Z).

  Lemma match_block_sameofs_match_ptr R p b1 b2 o:
    match_block_sameofs R p b1 b2 ->
    match_ptr R p (b1, o) (b2, o).
  Proof.
    intros H.
    replace o with (o + 0)%Z at 2 by omega.
    constructor.
    assumption.
  Qed.

  Lemma match_block_sameofs_match_ptrbits R p b1 b2 o:
    match_block_sameofs R p b1 b2 ->
    match_ptrbits R p (b1, o) (b2, o).
  Proof.
    intros H.
    replace o with (Ptrofs.add o Ptrofs.zero) at 2
      by (rewrite Ptrofs.add_zero; reflexivity).
    constructor.
    assumption.
  Qed.

  (** From [match_ptr] and [simrel_undef_matches_*], we can derive
    relation for [val] and [memval]. *)

  Inductive match_val R (p: simrel_world R): rel val val :=
    | match_val_int:
        Monotonic (@Vint) (- ==> match_val R p)
    | match_val_long:
        Monotonic (@Vlong) (- ==> match_val R p)
    | match_val_float:
        Monotonic (@Vfloat) (- ==> match_val R p)
    | match_val_single:
        Monotonic (@Vsingle) (- ==> match_val R p)
    | match_val_ptr_def b1 ofs1 b2 ofs2:
        match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
        match_val R p (Vptr b1 ofs1) (Vptr b2 ofs2)
    | match_val_undef:
        Monotonic (@Vundef) (match_val R p)
    | match_val_undef_int i:
        simrel_undef_matches_values R ->
        Related (@Vundef) (Vint i) (match_val R p)
    | match_val_undef_long i:
        simrel_undef_matches_values R ->
        Related (@Vundef) (Vlong i) (match_val R p)
    | match_val_undef_float f:
        simrel_undef_matches_values R ->
        Related (@Vundef) (Vfloat f) (match_val R p)
    | match_val_undef_single f:
        simrel_undef_matches_values R ->
        Related (@Vundef) (Vsingle f) (match_val R p)
    | match_val_undef_ptr b ofs:
        simrel_undef_matches_block R p b ->
        Related (@Vundef) (Vptr b ofs) (match_val R p).

  Global Instance match_val_ptr R p:
    Monotonic (@Vptr) (rel_curry (match_ptrbits R p ++> match_val R p)).
  Proof.
    intros [b1 ofs1] [b2 ofs2].
    apply match_val_ptr_def.
  Qed.

  Global Existing Instance match_val_int.
  Global Existing Instance match_val_long.
  Global Existing Instance match_val_float.
  Global Existing Instance match_val_single.
  Global Existing Instance match_val_ptr.
  Global Existing Instance match_val_undef.
  Global Existing Instance match_val_undef_int.
  Global Existing Instance match_val_undef_long.
  Global Existing Instance match_val_undef_float.
  Global Existing Instance match_val_undef_single.
  Global Existing Instance match_val_undef_ptr.

  (** Note that in the [Undef] case, even though we use [match_val] we
    still need a [simrel_undef_matches_values] guard. This is because
    we want to exclude [match_memval Undef (Fragment Vundef _ _)] when
    the guard is not satisfied, otherwise for example we lose the fact
    that [match_memval id = eq]. *)

  Inductive match_memval R (p: simrel_world R): rel memval memval :=
    | match_memval_byte:
        Monotonic (@Byte) (- ==> match_memval R p)
    | match_memval_fragment:
        Monotonic (@Fragment) (match_val R p ++> - ==> - ==> match_memval R p)
    | match_memval_undef:
        Monotonic (@Undef) (match_memval R p)
    | match_memval_undef_byte b:
        simrel_undef_matches_values R ->
        Related (@Undef) (@Byte b) (match_memval R p)
    | match_memval_undef_fragment v q n:
        simrel_undef_matches_values R ->
        RIntro
          (match_val R p Vundef v)
          (match_memval R p) Undef (Fragment v q n).

  Global Existing Instance match_memval_byte.
  Global Existing Instance match_memval_fragment.
  Global Existing Instance match_memval_undef.
  Global Existing Instance match_memval_undef_byte.
  Global Existing Instance match_memval_undef_fragment.

  (** ** [simrel_option_le] *)

  (** This is a version of [option_le] sensitive to the
    [simrel_undef_matches_values] component of a given simulation
    relation. It is particularly useful in the [SimValues] library.

    Some operations are formulated in terms of intermediate [option]
    results. Often when some input is [Vundef], these intermediate
    results are set to [None]. Then [Val.of_optbool] maps [None] back
    to [Vundef]. This means that whether we want [None] to act as a
    bottom element depend on whether [Vundef] does -- [option_le] is
    in general too weak and [option_rel] is too strong. To solve this
    problem we introduce this relator, which behaves like one or the
    other depending on [simrel_undef_matches_values].

    Note that it still might be too weak in some corner cases, because
    it does not take [simrel_undef_matches_block] into account.
    Fortunately, so far this has not been an issue because it seems
    in practice [option val] is never used with pointers. The one
    function that cannot be characterized is [Val.make_total],
    fortunately it is only used in a few places where it can be worked
    around fairly easily. *)

  (** To define [simrel_option_le], we start with a more general
    [flex_option_le] parametrized with a proposition [P] which
    determines whether [None] is allowed as a bottom element. *)

  Inductive flex_option_le {A B} (P: Prop) RAB: rel (option A) (option B) :=
    | flex_option_le_some_def:
        Monotonic Some (RAB ++> flex_option_le P RAB)
    | flex_option_le_none_def:
        Monotonic None (flex_option_le P RAB)
    | flex_option_le_none_lb:
        P ->
        LowerBound (flex_option_le P RAB) None.

  Global Instance option_rel_flex_option_le_subrel {A B} P (R: rel A B):
    Related (option_rel R) (flex_option_le P R) subrel.
  Proof.
    destruct 1; constructor; auto.
  Qed.

  Global Instance flex_option_le_option_le {A B} P (R: rel A B) :
    Related (flex_option_le P R) (option_le R) subrel.
  Proof.
    destruct 1; constructor; auto.
  Qed.

  Global Existing Instance flex_option_le_none_lb.

  (** Assuming [P] is a known typeclass, [flex_option_le_none_lb] can
    be used when using [lower_bound] directly. However the path to
    [RAuto] through [Related] does not work. This is because in that
    context, the relation from the goal is not available during the
    [LowerBound] search; instead we search for a [LowerBound] instance
    for an arbitrary relation, which is lated connected to the
    relation in the goal through a [subrel] search. This works great
    with most relations, but in this case this means that at
    [LowerBound] resolution time, the value of [P] is unknown, and we
    cannot resolve the corresponding premise in [flex_option_le_none_lb].

    We can work around this issue with the following [RIntro] hint. *)

  Global Instance flex_option_le_none_lb_rintro {A B} (P: Prop) (RAB: rel A B) y:
    P ->
    RIntro True (flex_option_le P RAB) None y.
  Proof.
    intros H _.
    apply flex_option_le_none_lb.
    assumption.
  Qed.

  Global Instance flex_option_le_refl {A} P (RA: relation A):
    Reflexive RA ->
    Reflexive (flex_option_le P RA).
  Proof.
    intros HRA x.
    destruct x; constructor.
    reflexivity.
  Qed.

  Global Instance flex_option_map_rel P:
    Monotonic
      (@option_map)
      (forallr S, forallr T,
        (S ++> T) ++> flex_option_le P S ++> flex_option_le P T).
  Proof.
    unfold option_map.
    repeat rstep.
    constructor; eauto.
  Qed.

  (** For similar reasons, we will also need a corresponding version
    of [leb] to relate the results of operations such as
    [Mem.valid_pointer], which are involved in pointer comparisons. *)

  Inductive flex_leb (P: Prop) : rel bool bool :=
    | flex_leb_refl : Reflexive (flex_leb P)
    | flex_leb_false_true : P -> LowerBound (flex_leb P) false.

  Global Existing Instance flex_leb_refl.
  Global Existing Instance flex_leb_false_true.

  Instance flex_leb_leb P:
    Related (flex_leb P) leb subrel.
  Proof.
    destruct 1; reflexivity.
  Qed.

  Global Instance andb_flex_leb:
    forall P, Monotonic andb (flex_leb P ++> flex_leb P ++> flex_leb P).
  Proof.
    intros P x1 x2 Hx y1 y2 Hy.
    destruct Hx, Hy; simpl; try constructor; eauto.
    destruct x; constructor; eauto.
  Qed.

  (** Then, we use [simrel_undef_matches_values] as the parameter in
    order to obtain the behavior we want for [simrel_option_le]. We
    use a notation so that the instances defined above for
    [flex_option_le] can apply directly. *)

  Notation simrel_option_le R :=
    (flex_option_le (simrel_undef_matches_values R)).

  Notation simrel_leb R :=
    (flex_leb (simrel_undef_matches_values R)).

  (** ** Initial memory *)

  (** The [simrel_new_glbl] field is enough to formulate a sufficient
    condition on programs for the initial memory states to be related.
    Here we use [program_rel] to express this condition.

    Note that we're careful to define [simrel_program_rel] in such a
    way that, when applied to [simrel_components] which have the same
    [simrel_new_glbl] and [simrel_undef_matches_values_bool], the
    results will be convertible. This is why the components are
    parametrized by those directly, rather than by the
    [simrel_components] under consideration.

    The relation on function definitions is straightforward. If [R]
    permits [Vundef] as a bottom element, we also allow new function
    definitions to be introduced on the right-hand side. Otherwise,
    the function definitions should either both be [None], or both use
    [Some]. Since the initial memory is constructed in a way does not
    actually depend on the details of a function definition, we don't
    enforce any other requirements. *)

  Definition simrel_fundef_rel {F1 F2} b: ident -> rel (option F1) (option F2) :=
    fun _ => flex_option_le (b = true) ⊤%rel.

  (** For variables, we need to distinguish two cases depending on
    whether they're listed in [simrel_new_glbl] or not.

    If they are, then the variable must not appear on the left-hand
    side, and must appear on the right-hand side, and contain the
    specified initialization data. Note that for composition to work,
    we need to make sure that the variable does not appear twice in
    [simrel_new_glbl].  Otherwise, it would be possible to have a
    situation where [v] appears in both [R12] and [R23], and
    [None [R23 ∘ R12] (Some v)] holds as a result, but there would be
    no intermediate value [x] that would satisfy both [None [R12] x]
    and [x [R23] (Some v)].

    For variables not in [simrel_new_glbl], we allow new variables on
    the right-hand side if [simrel_undef_matches_values], and
    otherwise require that the definitions be identical. *)

  Definition test (P: Prop) `{Decision P}: bool :=
    if decide P then true else false.

  Definition simrel_new_glbl_for (ng: list (ident * list AST.init_data)) i :=
    filter (fun def => test (fst def = i)) ng.

  Definition simrel_newvar_ok ng b (i: ident) init :=
    (simrel_new_glbl_for ng i = (i, init)::nil) \/
    (simrel_new_glbl_for ng i = nil /\ b = true).

  Definition simrel_not_new_glbl ng i :=
    simrel_new_glbl_for ng i = nil.

  Inductive simrel_vardef_rel {V} ng b i: relation (option (globvar V)) :=
    | simrel_vardef_rel_none:
        simrel_not_new_glbl ng i ->
        simrel_vardef_rel ng b i None None
    | simrel_vardef_rel_some v:
        simrel_not_new_glbl ng i ->
        simrel_vardef_rel ng b i (Some v) (Some v)
    | simrel_vardef_rel_newvar v init:
        simrel_newvar_ok ng b i init ->
        Genv.init_data_list_valid find_symbol 0 init = true ->
        simrel_vardef_rel ng b i None
          (Some
             {| gvar_info := v;
                gvar_init := init;
                gvar_readonly := false;
                gvar_volatile := false |}).

  Definition simrel_program_rel {F1 F2 V} R :=
    program_rel
      (@simrel_fundef_rel F1 F2 (simrel_undef_matches_values_bool R))
      (@simrel_vardef_rel V (simrel_new_glbl R) (simrel_undef_matches_values_bool R)).

  (** ** Properties *)

  (* The expectation is that the basic relation components should be
    compatible with the basic memory operations, in a way that is
    consistent with the carrier order, as explained above.

    Although the definition below is a good start, we will also need
    to know that the builtin functions work well. One option would be
    to characterize the buitins in terms of the memory operations so
    that we can come up with a generic proof for them.

    It is also unclear how the initial memory is going to work out.
    One option would be to give a relation on programs in
    [SimulationRelationOps] (parametric in the types of function and
    variable definitions), and require a corresponding relational
    property for [Genv.init_mem].
   *)

  Class SimulationRelation R :=
    {
      (** Properties of the accessibility relation. *)

      simrel_acc_preorder:
        @PreOrder (simrel_world R) (≤);

      simrel_acc_undef_matches_pointer:
        Monotonic (simrel_undef_matches_block R) ((≤) ++> - ==> impl);

      simrel_acc_meminj:
        Monotonic (simrel_meminj R) ((≤) ++> - ==> option_le eq);

      (** Consistency of [simrel_undef_matches_values] and
        [simrel_undef_matches_block]. *)

      simrel_undef_matches_values_also_block p ptr1 b2 ofs2:
        simrel_undef_matches_values R ->
        match_ptrbits R p ptr1 (b2, ofs2) ->
        simrel_undef_matches_block R p b2;

      simrel_undef_matches_block_also_values p b2:
        simrel_undef_matches_block R p b2 ->
        simrel_undef_matches_values R;

      (** The following condition is necessary for the subtraction
          and comparison of two pointers. *)
      simrel_undef_matches_block_or_injective p b2:
        forall b1 b1',
          b1' <> b1 ->
          match_block R p b1 b2 ->
          match_block R p b1' b2 ->
          simrel_undef_matches_block R p b2;

      (* The following conditions are necessary for comparing
         invalid pointers with Val.cmpu* *)
      simrel_undef_matches_block_invalid_weak p m1 m2 b1 ofs1 b2 ofs2:
        match_mem R p m1 m2 ->
        Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = false ->
        match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
        Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned ofs2) = true ->
        simrel_undef_matches_block R p b2;

      simrel_undef_matches_block_invalid p m1 m2 b1 ofs1 b2 ofs2:
        match_mem R p m1 m2 ->
        Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = false ->
        match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
        Mem.valid_pointer m2 b2 (Ptrofs.unsigned ofs2) = true ->
        simrel_undef_matches_block R p b2;

      (** Properties of [match_block_delta]. *)

      match_global_block_sameofs p b:
        block_is_global b ->
        Proper (match_block_sameofs R p) b;

      (** Initial memory *)

      simrel_init_mem {F V}:
        Monotonic
          (Genv.init_mem (F:=F) (V:=V))
          (simrel_program_rel R ++>
           option_le (rexists w, match_mem R w));

      (** Properties for memory operations. *)

      simrel_alloc p:
        Monotonic
          Mem.alloc
          (match_mem R p ++> - ==> - ==>
           incr p (match_mem R p * match_block_sameofs R p));

      simrel_free p:
        Monotonic
          Mem.free
          (match_mem R p ++> rel_curry (rel_curry (match_ptrrange R p ==>
           option_le (incr p (match_mem R p)))));

      simrel_load p:
        Monotonic
          Mem.load
          (- ==> match_mem R p ++> rel_curry (match_ptr R p ++>
           option_le (match_val R p)));

      simrel_store p:
        Monotonic
          Mem.store
          (- ==> match_mem R p ++> rel_curry (match_ptr R p ++>
           match_val R p ++> option_le (incr p (match_mem R p))));

      simrel_loadbytes p:
        Monotonic
          Mem.loadbytes
          (match_mem R p ++> rel_curry (match_ptr R p ++> - ==>
           option_le (list_rel (match_memval R p))));

      simrel_storebytes p:
        Monotonic
          Mem.storebytes
          (match_mem R p ++>
           rel_curry (match_ptr R p ++> list_rel (match_memval R p) ++>
           option_le (incr p (match_mem R p))));

      simrel_perm p:
        Monotonic
          Mem.perm
          (match_mem R p ++> rel_curry (match_ptr R p ++> - ==> - ==> impl));

      simrel_valid_block p:
        Monotonic
          Mem.valid_block
          (match_mem R p ++> match_block R p ++> iff);

      (* similar to Mem.different_pointers_inject. Necessary for
         comparing valid pointers of different memory blocks that inject
         into the same block. *)
      simrel_different_pointers_inject
        p m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2:
        match_mem R p m m' ->
        b1 <> b2 ->
        Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
        Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
        simrel_meminj R p b1 = Some (b1', delta1) ->
        simrel_meminj R p b2 = Some (b2', delta2) ->
        b1' <> b2' \/
        Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2));

      (* similar to Mem.weak_valid_pointer_inject_val, but cannot be deduced
         from Mem.address_inject. Needed for Val.cmpu* *)
      simrel_weak_valid_pointer_inject_val p m1 m2 b1 ofs1 b2 ofs2:
        match_mem R p m1 m2 ->
        Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
        match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
        Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned ofs2) = true;

      (** When comparing two weakly valid pointers of the same block
       using Val.cmpu, we need to compare their offsets, and so
       comparing the injected offsets must have the same result. To
       this end, it is necessary to show that all weakly valid
       pointers be shifted by the same mathematical (not machine)
       integer amount. However, contrary to the situation with
       Mem.address_inject for valid pointers, here for weakly valid
       pointers we do not know whether this amount is delta. The best
       we know, thanks to Mem.weak_valid_pointer_inject_no_overflow,
       is that Ptrofs.unsigned (Ptrofs.repr delta) works, but proving
       composition would be much harder than for the following
       weak version:
      *)

      simrel_weak_valid_pointer_address_inject_weak p m1 m2 b1 b2 delta:
        match_mem R p m1 m2 ->
        simrel_meminj R p b1 = Some (b2, delta) ->
        exists delta',
          forall ofs1,
            Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
            Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
            (Ptrofs.unsigned ofs1 + delta')%Z;

      (* similar to Mem.address_inject for memory injections.
         Needed at least by Clight assign_of (By_copy) and memcpy,
         but I guess at many other places. *)
      simrel_address_inject p m1 m2 b1 ofs1 b2 delta pe:
        match_mem R p m1 m2 ->
        Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur pe ->
        simrel_meminj R p b1 = Some (b2, delta) ->
        Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
        (Ptrofs.unsigned ofs1 + delta)%Z;

      (* similar to Mem.aligned_area_inject for memory injections.
         Needed by Clight assign_of (By_copy) and memcpy. *)
      simrel_aligned_area_inject p m m' b ofs al sz b' delta:
        match_mem R p m m' ->
        (al = 1 \/ al = 2 \/ al = 4 \/ al = 8) ->
        sz > 0 ->
        (al | sz) ->
        Mem.range_perm m b ofs (ofs + sz) Cur Nonempty ->
        (al | ofs) ->
        simrel_meminj R p b = Some (b', delta) ->
        (al | ofs + delta);

      (* similar to Mem.disjoint_or_equal_inject for memory injections.
         Needed by Clight assign_of (By_copy) and memcpy. *)
      simrel_disjoint_or_equal_inject
        p m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz:
        match_mem R p m m' ->
        simrel_meminj R p b1 = Some (b1', delta1) ->
        simrel_meminj R p b2 = Some (b2', delta2) ->
        Mem.range_perm m b1 ofs1
                       (ofs1 + sz) Max Nonempty ->
        Mem.range_perm m b2 ofs2
                       (ofs2 + sz) Max Nonempty ->
        sz > 0 ->
        b1 <> b2 \/
        ofs1 = ofs2 \/
        ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
        b1' <> b2' \/
        (ofs1 + delta1 = ofs2 + delta2)%Z \/
        ofs1 + delta1 + sz <= ofs2 + delta2 \/
        ofs2 + delta2 + sz <= ofs1 + delta1
    }.

  Global Existing Instances simrel_acc_preorder.
  Global Existing Instances simrel_acc_undef_matches_pointer.
  Global Existing Instances simrel_acc_meminj.
  Global Existing Instances simrel_alloc.
  Local  Existing Instances simrel_free. (* strengthened version below *)
  Global Existing Instances simrel_load.
  Global Existing Instances simrel_store.
  Global Existing Instances simrel_loadbytes.
  Global Existing Instances simrel_storebytes.
  Global Existing Instances simrel_perm.
  Global Existing Instances simrel_valid_block.

  (* NB: Those need to be redeclared outside of the section. *)
  Global Instance: Params (@simrel_undef_matches_block) 2.
  Global Instance: Params (@simrel_meminj) 2.

  Global Instance: Params (@Genv.init_mem) 1.
  Global Instance: Params (@Mem.empty) 0.
  Global Instance: Params (@Mem.alloc) 3.
  Global Instance: Params (@Mem.free) 4.
  Global Instance: Params (@Mem.load) 4.
  Global Instance: Params (@Mem.store) 5.
  Global Instance: Params (@Mem.loadbytes) 4.
  Global Instance: Params (@Mem.storebytes) 4.
  Global Instance: Params (@Mem.loadv) 3.
  Global Instance: Params (@Mem.storev) 4.
  Global Instance: Params (@Mem.perm) 5.
  Global Instance: Params (@Mem.valid_block) 2.

  (** ** Packaging them up *)

  (** Though it is convenient to be able to define a simulation
    relation's operations and proofs separately, in most other contexts
    it is simpler to have a single object which bundles them together.

    Because simrel_ops is a coercion, a [simrel] can be used with
    [match_val], [match_block], etc. One thing to keep in mind is that
    if a parameter of your definition is only used in conjunction with
    one of these, its type will be inferred as [simrel_components],
    not [simrel].
   *)

  Record simrel :=
    {
      simrel_ops :> simrel_components;
      simrel_prf: SimulationRelation simrel_ops
    }.

  Global Existing Instance simrel_prf.

  (** ** Properties of derived relations *)

  Context `{HR: SimulationRelation}.

  (** *** Compatibility with the accessibility relation *)

  (* NB: Need to redeclare outside of the section *)
  Global Instance: Params (@match_ptr) 3.
  Global Instance: Params (@match_ptrbits) 3.
  Global Instance: Params (@match_ptrrange) 3.
  Global Instance: Params (@match_block) 3.
  Global Instance: Params (@match_block_sameofs) 3.
  Global Instance: Params (@match_val) 3.
  Global Instance: Params (@match_memval) 3.

  Global Instance match_ptr_acc:
    Monotonic (match_ptr R) ((≤) ++> subrel).
  Proof.
    intros p1 p2 Hp ptr1 ptr2 Hptr.
    destruct Hptr as [b1 ofs1 b2 delta Hb].
    transport Hb; subst.
    constructor; eauto.
  Qed.

  Global Instance match_ptrbits_acc:
    Monotonic (match_ptrbits R) ((≤) ++> subrel).
  Proof.
    intros p1 p2 Hp ptr1 ptr2 Hptr.
    destruct Hptr as [b1 ofs1 b2 delta Hb].
    transport Hb; subst.
    constructor; eauto.
  Qed.

  Global Instance match_ptrrange_acc:
    Monotonic (match_ptrrange R) ((≤) ++> subrel).
  Proof.
    intros p1 p2 Hp ptr1 ptr2 Hptr.
    destruct Hptr as [b1 ofs1 b2 ofs2 sz Hb].
    constructor; eauto.
    revert Hb.
    apply match_ptr_acc.
    assumption.
  Qed.

  Global Instance match_block_acc:
    Monotonic (match_block R) ((≤) ++> subrel).
  Proof.
    intros p1 p2 Hp b1 b2 [delta Hb].
    transport Hb; subst.
    eexists; eauto.
  Qed.

  Global Instance match_block_sameofs_acc:
    Monotonic (match_block_sameofs R) ((≤) ++> subrel).
  Proof.
    intros p1 p2 Hp b1 b2 Hb.
    transport Hb; subst.
    eauto.
  Qed.

  Global Instance match_val_acc:
    Monotonic (match_val R) ((≤) ++> subrel).
  Proof.
    intros p p' Hp x y Hxy.
    destruct Hxy; constructor; eauto.
    - rauto.
    - revert H; rauto.
  Qed.

  Global Instance match_memval_acc:
    Monotonic (match_memval R) ((≤) ++> subrel).
  Proof.
    intros p p' Hp x y Hxy.
    destruct Hxy; constructor; eauto.
    - rauto.
    - revert H0; rauto.
  Qed.

  (** *** Functionality *)

  Lemma match_ptr_functional p ptr ptr1 ptr2:
    match_ptr R p ptr ptr1 ->
    match_ptr R p ptr ptr2 ->
    ptr1 = ptr2.
  Proof.
    intros [b ofs b1 delta1 Hb1] Hb2'.
    inversion Hb2' as [xb xofs b2 delta2 Hb2]; clear Hb2'; subst.
    congruence.
  Qed.

  Lemma match_ptrbits_functional p ptr ptr1 ptr2:
    match_ptrbits R p ptr ptr1 ->
    match_ptrbits R p ptr ptr2 ->
    ptr1 = ptr2.
  Proof.
    intros [b ofs b1 delta1 Hb1] Hb2'.
    inversion Hb2' as [xb xofs b2 delta2 Hb2]; clear Hb2'; subst.
    congruence.
  Qed.

  Lemma match_ptrrange_functional p ptr ptr1 ptr2:
    match_ptrrange R p ptr ptr1 ->
    match_ptrrange R p ptr ptr2 ->
    ptr1 = ptr2.
  Proof.
    intros Hptr1 Hptr2.
    destruct Hptr1 as [b ofs b1 ofs1 sz1 H1].
    inversion Hptr2 as [xb xofs b2 ofs2 sz2]; clear Hptr2; subst.
    pose proof (match_ptr_functional p (b, ofs) (b1, ofs1) (b2, ofs2) H1 H).
    assert (sz1 = sz2).
    {
      eapply Z.add_reg_l; eauto.
    }
    congruence.
  Qed.

  Lemma match_block_functional p b b1 b2:
    match_block R p b b1 ->
    match_block R p b b2 ->
    b1 = b2.
  Proof.
    intros [d1 Hb1] [d2 Hb2].
    congruence.
  Qed.

  Lemma match_block_sameofs_functional p b b1 b2:
    match_block_sameofs R p b b1 ->
    match_block_sameofs R p b b2 ->
    b1 = b2.
  Proof.
    unfold match_block_sameofs.
    congruence.
  Qed.

  (** *** Shift-invariance *)

  Lemma match_ptr_shift p b1 ofs1 b2 ofs2 delta:
    match_ptr R p (b1, ofs1) (b2, ofs2) ->
    match_ptr R p (b1, ofs1 + delta)%Z (b2, ofs2 + delta)%Z.
  Proof.
    inversion 1; subst.
    rewrite <- Z.add_assoc.
    rewrite (Z.add_comm delta0 delta).
    rewrite Z.add_assoc.
    constructor; eauto.
  Qed.

  Lemma match_ptrbits_shift p b1 ofs1 b2 ofs2 delta:
    match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
    match_ptrbits R p (b1, Ptrofs.add ofs1 delta) (b2, Ptrofs.add ofs2 delta).
  Proof.
    inversion 1; subst.
    rewrite Ptrofs.add_assoc.
    rewrite (Ptrofs.add_commut (Ptrofs.repr _)).
    rewrite <- Ptrofs.add_assoc.
    constructor; eauto.
  Qed.

  Lemma match_ptrrange_shift p b1 ofs1 sz1 b2 ofs2 sz2 delta:
    match_ptrrange R p (b1, ofs1, sz1) (b2, ofs2, sz2) ->
    match_ptrrange R p (b1, ofs1 + delta, sz1)%Z (b2, ofs2 + delta, sz2)%Z.
  Proof.
    inversion 1; subst.
    replace (ofs1 + sz)%Z with ((ofs1 + delta) + (sz - delta))%Z by omega.
    replace (ofs2 + sz)%Z with ((ofs2 + delta) + (sz - delta))%Z by omega.
    constructor.
    eapply match_ptr_shift; eauto.
  Qed.

  (** *** Relationships between [match_foo] relations *)

  (** We call each lemma [match_foo_bar] that establishes [match_bar]
    from a [match_foo] premise. When this can be done in several ways,
    we add a suffix to disambiguate. *)

  Lemma add_repr ofs1 delta:
    Ptrofs.repr (ofs1 + delta) =
    Ptrofs.add (Ptrofs.repr ofs1) (Ptrofs.repr delta).
  Proof.
      rewrite Ptrofs.add_unsigned.
      auto using Ptrofs.eqm_samerepr,
      Ptrofs.eqm_add, Ptrofs.eqm_unsigned_repr.
  Qed.    

  Lemma match_ptr_ptrbits_repr p b1 ofs1 b2 ofs2:
    match_ptr R p (b1, ofs1) (b2, ofs2) ->
    match_ptrbits R p (b1, Ptrofs.repr ofs1) (b2, Ptrofs.repr ofs2).
  Proof.
    inversion 1; subst.
    rewrite add_repr.
    constructor.
    assumption.
  Qed.

  Lemma match_ptr_ptrbits_unsigned p b1 ofs1 b2 ofs2:
    match_ptr R p (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs2) ->
    match_ptrbits R p (b1, ofs1) (b2, ofs2).
  Proof.
    intros H.
    rewrite <- (Ptrofs.repr_unsigned ofs1), <- (Ptrofs.repr_unsigned ofs2).
    apply match_ptr_ptrbits_repr; eauto.
  Qed.

  Lemma match_ptr_ptrrange p b1 lo1 hi1 b2 lo2 hi2:
    match_ptr R p (b1, lo1) (b2, lo2) ->
    hi1 - lo1 = hi2 - lo2 ->
    match_ptrrange R p (b1, lo1, hi1) (b2, lo2, hi2).
  Proof.
    intros Hlo Hhi.
    replace hi1 with (lo1 + (hi1 - lo1))%Z by omega.
    replace hi2 with (lo2 + (hi1 - lo1))%Z by omega.
    constructor; eauto.
  Qed.

  Lemma match_ptr_block p b1 ofs1 b2 ofs2:
    match_ptr R p (b1, ofs1) (b2, ofs2) ->
    match_block R p b1 b2.
  Proof.
    inversion 1.
    red.
    eauto.
  Qed.

  Lemma match_ptr_block_sameofs p b1 b2 ofs:
    match_ptr R p (b1, ofs) (b2, ofs) ->
    match_block_sameofs R p b1 b2.
  Proof.
    inversion 1.
    assert (delta = 0) by omega.
    red.
    congruence.
  Qed.

  Lemma match_ptrbits_ptr p m1 m2 b1 o1 b2 o2 pe:
    match_mem R p m1 m2 ->
    match_ptrbits R p (b1, o1) (b2, o2) ->
    Mem.perm m1 b1 (Ptrofs.unsigned o1) Cur pe ->
    match_ptr R p (b1, Ptrofs.unsigned o1) (b2, Ptrofs.unsigned o2).
  Proof.
    intros H H0 H1.
    inversion H0; subst.
    erewrite simrel_address_inject; eauto.
    constructor.
    assumption.
  Qed.

  Lemma match_ptrbits_block p b1 ofs1 b2 ofs2:
    match_ptrbits R p (b1, ofs1) (b2, ofs2) ->
    match_block R p b1 b2.
  Proof.
    inversion 1.
    red.
    eauto.
  Qed.

  Lemma match_ptrrange_ptr p ptr1 hi1 ptr2 hi2:
    match_ptrrange R p (ptr1, hi1) (ptr2, hi2) ->
    match_ptr R p ptr1 ptr2.
  Proof.
    inversion 1.
    assumption.
  Qed.

  Lemma match_block_ptr p b1 b2 ofs1:
    match_block R p b1 b2 ->
    exists ofs2, match_ptr R p (b1, ofs1) (b2, ofs2).
  Proof.
    intros [delta H].
    exists (ofs1 + delta)%Z.
    constructor; eauto.
  Qed.

  Lemma match_block_ptrbits p b1 b2 ofs1:
    match_block R p b1 b2 ->
    exists ofs2, match_ptrbits R p (b1, ofs1) (b2, ofs2).
  Proof.
    intros [delta H].
    exists (Ptrofs.add ofs1 (Ptrofs.repr delta)).
    constructor; eauto.
  Qed.

  Lemma match_block_ptrrange p b1 b2 lo1 hi1:
    match_block R p b1 b2 ->
    exists lo2 hi2, match_ptrrange R p (b1, lo1, hi1) (b2, lo2, hi2).
  Proof.
    intros [delta H].
    exists (lo1 + delta)%Z, ((lo1 + delta) + (hi1 - lo1))%Z.
    pattern hi1 at 1.
    replace hi1 with (lo1 + (hi1 - lo1))%Z by omega.
    constructor.
    constructor.
    assumption.
  Qed.

  Lemma match_block_sameofs_ptr p b1 ofs1 b2 ofs2:
    match_block_sameofs R p b1 b2 ->
    ofs1 = ofs2 ->
    match_ptr R p (b1, ofs1) (b2, ofs2).
  Proof.
    intros Hb Hofs.
    red in Hb.
    destruct Hofs.
    pattern ofs1 at 2.
    replace ofs1 with (ofs1 + 0)%Z by omega.
    constructor; eauto.
  Qed.

  Lemma match_block_sameofs_ptrbits p b1 ofs1 b2 ofs2:
    match_block_sameofs R p b1 b2 ->
    ofs1 = ofs2 ->
    match_ptrbits R p (b1, ofs1) (b2, ofs2).
  Proof.
    intros Hb Hofs.
    red in Hb.
    destruct Hofs.
    pattern ofs1 at 2.
    replace ofs1 with (Ptrofs.add ofs1 (Ptrofs.repr 0%Z)).
    - constructor; eauto.
    - change (Ptrofs.repr 0) with Ptrofs.zero.
      apply Ptrofs.add_zero.
  Qed.

  Lemma match_block_sameofs_ptrrange p b1 lo1 hi1 b2 lo2 hi2:
    match_block_sameofs R p b1 b2 ->
    lo1 = lo2 ->
    hi1 = hi2 ->
    match_ptrrange R p (b1, lo1, hi1) (b2, lo2, hi2).
  Proof.
    intros Hb Hlo Hhi.
    red in Hb.
    subst.
    eapply match_ptr_ptrrange; eauto.
    eapply match_block_sameofs_ptr; eauto.
  Qed.

  Global Instance match_block_sameofs_block p:
    Related (match_block_sameofs R p) (match_block R p) subrel.
  Proof.
    clear.
    firstorder.
  Qed.

  (** *** Global blocks *)

  Lemma match_global_ptr p b ofs:
    block_is_global b ->
    Monotonic (b, ofs) (match_ptr R p).
  Proof.
    intros Hb.
    eapply match_block_sameofs_ptr; eauto.
    eapply match_global_block_sameofs; eauto.
  Qed.

  Lemma match_global_ptrbits p b ofs:
    block_is_global b ->
    Monotonic (b, ofs) (match_ptrbits R p).
  Proof.
    intros Hb.
    eapply match_block_sameofs_ptrbits; eauto.
    eapply match_global_block_sameofs; eauto.
  Qed.

  Lemma match_global_ptrrange p b lo hi:
    block_is_global b ->
    Monotonic (b, lo, hi) (match_ptrrange R p).
  Proof.
    intros Hb.
    eapply match_block_sameofs_ptrrange; eauto.
    eapply match_global_block_sameofs; eauto.
  Qed.

  Lemma match_global_block p b:
    block_is_global b ->
    Monotonic b (match_block R p).
  Proof.
    intros Hb.
    eapply match_block_sameofs_block.
    eapply match_global_block_sameofs; eauto.
  Qed.

  (** *** Miscellaneous *)

  Lemma match_val_weaken_to_undef p v1 v2:
    simrel_undef_matches_values R ->
    match_val R p v1 v2 ->
    match_val R p Vundef v2.
  Proof.
    intros HRundef Hv.
    destruct Hv; try rauto.
    constructor.
    eapply simrel_undef_matches_values_also_block; eauto.
  Qed.

  (** ** Properties of derived memory operations *)

  Global Instance simrel_loadv p:
    Monotonic
      Mem.loadv
      (- ==> match_mem R p ++> match_val R p ++> option_le (match_val R p)).
  Proof.
    repeat red.
    intros a x y H x0 y0 H0.
    inversion H0; subst; simpl; try now constructor.
    destruct (Mem.load a x _ (Ptrofs.unsigned _)) eqn:LOAD; try now constructor.
    rewrite <- LOAD.
    repeat rstep.
    eapply match_ptrbits_ptr; eauto.
    eapply Mem.load_valid_access; eauto.
    generalize (size_chunk_pos a); omega.
  Qed.

  Global Instance simrel_loadv_params:
    Params (@Mem.loadv) 3.

  Global Instance simrel_storev p:
    Monotonic
      Mem.storev
      (- ==> match_mem R p ++> match_val R p ++> match_val R p ++>
       option_le (incr p (match_mem R p))).
  Proof.
    intros a x y H x0 y0 H0 x1 y1 H1.
    destruct (Mem.storev a x _ _) eqn:STORE; [ | solve_monotonic ].
    rewrite <- STORE.
    inversion H0; subst; simpl; try rauto.
    simpl in * |- *.
    repeat rstep.
    eapply match_ptrbits_ptr; eauto.
    eapply Mem.store_valid_access_3; eauto.
    generalize (size_chunk_pos a); omega.
  Qed.

  Global Instance simrel_storev_params:
    Params (@Mem.storev) 4.

  (** XXX: Use a separate SimGlobalenvs.v ? *)
  Global Instance genv_find_symbol_match {F V Rf} p:
    Monotonic
      (Globalenvs.Genv.find_symbol (F:=F) (V:=V))
      (genv_le Rf ++> - ==> option_rel (match_block_sameofs R p)).
  Proof.
    intros ge1 ge2 Hge i.
    rewrite !stencil_matches_symbols by eauto.
    destruct (find_symbol i) eqn:Hi.
    - constructor.
      eapply match_global_block_sameofs.
      eapply find_symbol_block_is_global.
      eassumption.
    - constructor.
  Qed.

  Global Instance genv_find_symbol_match_params:
    Params (@Globalenvs.Genv.find_symbol) 2.

  (** Maybe it's possible to prove [simrel_storebytes] from [simrel_store]
    as well. But if it is, it's tricky. *)

  Global Instance simrel_free_list p:
    Monotonic
      Mem.free_list
      (match_mem R p ++> list_rel (match_ptrrange R p) ++>
       option_le (incr p (match_mem R p))).
  Proof.
    intros m1 m2 Hm l1 l2 Hl.
    revert p l2 Hl m1 m2 Hm.
    induction l1; inversion 1; subst; simpl; intros.
    - rauto.
    - rstep; rstep.
      rstep; rstep.
      + rauto.
      + split_hyp H4. (* XXX: need to update split_hyps to include rel_incr *)
        (* XXX: for whatever reason Coq needs to be reminded of this ?! *)
        Existing Instance rel_incr_subrel.
        exploit IHl1; [ | rauto | ]; try rauto.
  Qed.

  Global Instance simrel_free_list_params:
    Params (@Mem.free_list) 2.

  Global Instance mem_valid_pointer_match p:
    Monotonic
      Mem.valid_pointer
      (match_mem R p ++> rel_curry (match_ptr R p ++> Bool.leb)).
  Proof.
    intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hp.
    simpl.
    destruct (Mem.valid_pointer m1 b1 ofs1) eqn:Hp1; simpl; eauto.
    revert Hp1.
    rewrite !Mem.valid_pointer_nonempty_perm.
    solve_monotonic.
  Qed.

  Global Instance mem_valid_pointer_match_params:
    Params (@Mem.valid_pointer) 3.

  Global Instance mem_weak_valid_pointer_match p:
    Monotonic
      Mem.weak_valid_pointer
      (match_mem R p ++> rel_curry (match_ptr R p ++> Bool.leb)).
  Proof.
    intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hp.
    simpl.
    unfold Mem.weak_valid_pointer.
    repeat rstep.
    apply match_ptr_shift.
    assumption.
  Qed.

  Global Instance mem_weak_valid_pointer_match_params:
    Params (@Mem.weak_valid_pointer) 3.

  (** ** Strengthened properties for memory operations *)

  Definition ptrrange_perm `{Mem.MemoryModelOps} m k p: relation _ :=
    lsat (fun r => match r with (b, lo, hi) => Mem.range_perm m b lo hi k p end).

  Global Instance simrel_free_perm p:
    Monotonic
      Mem.free
      (forallr m1 m2 : match_mem R p,
         % % rel_impl (ptrrange_perm m1 Cur Freeable) (match_ptrrange R p) ==>
         option_le (incr p (match_mem R p))).
  Proof.
    rstep.
    repeat rstep.
    destruct x as [[b1 lo1] hi1], y as [[b2 lo2] hi2]; simpl.
    destruct (Mem.free v1 b1 lo1 hi1) eqn:Hfree; repeat rstep.
    assert (ptrrange_perm v1 Cur Freeable (b1, lo1, hi1) (b2, lo2, hi2)).
    {
      eapply Mem.free_range_perm.
      eassumption.
    }
    rewrite <- Hfree.
    rauto.
  Qed.

  (** When pointers are extracted from Compcert [val]ues, they use
    machine integers and we know related values contain pointers that
    are related by [match_ptrbits]. Often we then convert this machine
    pointer with offset [ofs] into an mathematical pointer with offset
    [Ptrofs.unsigned ofs]. This is made explicit for our block-offset
    pair pointers using the following function. *)

  Definition ptrofbits (p: block * ptrofs) :=
    let '(b, ofs) := p in (b, Ptrofs.unsigned ofs).

  (** Unfortunately we can't establish that the results of this
    process are related by [match_ptr] without proving the side
    conditions of [match_ptrbits_ptr]. However if the side-conditions
    can't be proved directly from the context, we can use the relation
    [match_ptrbits !! ptrofbits] to remember that they were
    constructed in this way instead.

    For many memory operations this is enough, because the success of
    whichever memory operation we will use the pointer with will be
    sufficient to prove the side-conditions for [match_ptrbits_ptr]. *)

  Require Import BoolRel.

  Global Instance match_ptrofbits_rintro p b1 ofs1 b2 ofs2:
    RIntro
      (match_ptrbits R p (b1, ofs1) (b2, ofs2))
      ((match_ptrbits R p) !! ptrofbits)
      (b1, Ptrofs.unsigned ofs1)
      (b2, Ptrofs.unsigned ofs2).
  Proof.
    intros H.
    change (b1, Ptrofs.unsigned ofs1) with (ptrofbits (b1, ofs1)).
    change (b2, Ptrofs.unsigned ofs2) with (ptrofbits (b2, ofs2)).
    constructor; eauto.
  Qed.

  Global Instance valid_pointer_match p:
    Monotonic
      Mem.valid_pointer
      (match_mem R p ++> % (match_ptrbits R p) !! ptrofbits ++>
       flex_leb (simrel_undef_matches_values R)).
  Proof.
    intros m1 m2 Hm _ _ [[b1 ofs1] [b2 ofs2] H].
    simpl.
    destruct (Mem.valid_pointer m1 _ _) eqn:H1.
    - assert (match_ptr R p (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs2)).
      {
        eapply match_ptrbits_ptr; repeat rstep.
        eapply Mem.valid_pointer_nonempty_perm; eauto.
      }
      transport H1.
      rewrite H1.
      constructor.
    - destruct (Mem.valid_pointer m2 _ _) eqn:H2; repeat rstep.
      constructor.
      eapply simrel_undef_matches_block_also_values.
      eapply simrel_undef_matches_block_invalid; eauto.
  Qed.

  Global Instance weak_valid_pointer_match p:
    Monotonic
      Mem.weak_valid_pointer
      (match_mem R p ++> % (match_ptrbits R p) !! ptrofbits ++>
       flex_leb (simrel_undef_matches_values R)).
  Proof.
    intros m1 m2 Hm _ _ [[b1 ofs1] [b2 ofs2] Hptr].
    change ((flex_leb (simrel_undef_matches_values R))
              (Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1))
              (Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned ofs2))).
    destruct (Mem.weak_valid_pointer m1 _ _) eqn:Hwvp1.
    - erewrite (simrel_weak_valid_pointer_inject_val p); eauto.
      constructor.
    - destruct (Mem.weak_valid_pointer m2 _ _) eqn:Hwbp2.
      + constructor.
        eapply simrel_undef_matches_block_also_values.
        eapply simrel_undef_matches_block_invalid_weak; eauto.
      + constructor.
  Qed.

  Global Instance valid_pointer_weaken_match p:
    Related
      Mem.valid_pointer
      Mem.weak_valid_pointer
      (match_mem R p ++> % (match_ptrbits R p) !! ptrofbits ++> leb).
  Proof.
    intros m1 m2 Hm _ _ [[b1 ofs1] [b2 ofs2] H].
    simpl.
    transitivity (Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1)).
    - unfold Mem.weak_valid_pointer.
      apply left_upper_bound.
    - rauto.
  Qed.
End DEFINITION.

(** We make the memory models involved with a given simulation
  relation kit explicit. *)

Global Arguments simrel_components {_} D1 D2.
Global Arguments simrel {_} D1 D2.

(** We need to make sure those are out of the section so that no
  arguments are generalized at section exit. *)

Global Instance: Params (@simrel_undef_matches_block) 2.
Global Instance: Params (@simrel_meminj) 2.
Global Instance: Params (@match_mem) 3.
Global Instance: Params (@match_ptr) 3.
Global Instance: Params (@match_ptrbits) 3.
Global Instance: Params (@match_ptrrange) 3.
Global Instance: Params (@match_block) 3.
Global Instance: Params (@match_block_sameofs) 3.
Global Instance: Params (@match_val) 3.
Global Instance: Params (@match_memval) 3.

(** Make sure we can use the relationship between
  [simrel_undef_matches_values] and [simrel_undef_matches_block]
  during typeclass instance resolution. *)

Hint Extern 2 (simrel_undef_matches_block ?R ?p ?b2) =>
  eapply simrel_undef_matches_values_also_block; eassumption
  : typeclass_instances.

Hint Extern 1 (simrel_undef_matches_values ?R) =>
  eapply simrel_undef_matches_block_also_values; eassumption
  : typeclass_instances.

(** Re-register the [simrel_option_le] notation outside of the section. *)

Global Notation simrel_option_le R :=
  (flex_option_le (simrel_undef_matches_values R)).

Global Notation simrel_leb R :=
  (flex_leb (simrel_undef_matches_values R)).


(** * Tactics *)

(** Here we define some tactics which may be useful when building up
  on our simulation relation tookits. *)

(* Inverse hypothese for some relations when the left-hand side has a
  specific form. For now, we use an ad-hoc tactic, but maybe we could
  find a way to strengthen the relators associated with [nil], [cons],
  [Vint], [Vptr], etc. to express the properties used here. *)

Ltac inverse_hyps :=
  repeat
    lazymatch goal with
      | H: list_rel ?R (?x :: ?xs) ?yl |- _ =>
        inversion H; clear H; subst
      | H: list_rel ?R nil ?yl |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vint _) ?y |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vlong _) ?y |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vfloat _) ?y |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vsingle _) ?y |- _ =>
        inversion H; clear H; subst
      | H: match_val ?R ?p (Vptr _ _) ?y |- _ =>
        inversion H; clear H; subst
    end.

(** Another common need is to solve a goal which consists in [set_rel]
  used in conjunction with an inductive type. The [deconstruct] tactic
  destructs a hypothesis [H], and for each generated subgoal passes
  the corresponding constructor to the continuation k. *)

Ltac head m :=
  lazymatch m with
    | ?x _ => head x
    | ?x => constr:(x)
  end.

Ltac deconstruct H k :=
  let HH := fresh in
  destruct H eqn:HH;
  lazymatch type of HH with
    | _ = ?cc =>
      let c := head cc in
      clear HH; k c
  end.

(** We can use that to build a systematic way to solve goals which
  related two elements of an inductive type with [set_rel]. Namely,
  destruct the hypothesis which states the left-hand side is in the
  set, then for each branch transport all of the premises and apply
  the same constructor again. *)

Ltac solve_set_rel :=
  lazymatch goal with
    | |- set_rel _ _ _ =>
      let H := fresh in
      let reconstruct c :=
        idtac "Using constructor" c;
        clear H;
        split_hyps;
        inverse_hyps;
        transport_hyps;
        try (eexists; split; [eapply c; eauto | repeat rstep]) in
      intros ? H;
      deconstruct H reconstruct
    | |- impl _ _ =>
      let H := fresh in
      let reconstruct c :=
        idtac "Using constructor" c;
        clear H;
        split_hyps;
        inverse_hyps;
        transport_hyps;
        try (eapply c; eauto) in
      intros H;
      deconstruct H reconstruct
    | |- _ =>
      intro; solve_set_rel
  end.

(** This can be useful when [rel_curry] is involved *)
Ltac eexpair :=
  lazymatch goal with
    | |- @ex (prod ?T1 ?T2) _ =>
      let xv := fresh in evar (xv: T1);
      let x := eval red in xv in clear xv;
      let yv := fresh in evar (yv: T2);
      let y := eval red in yv in clear yv;
      exists (x, y); simpl
  end.
