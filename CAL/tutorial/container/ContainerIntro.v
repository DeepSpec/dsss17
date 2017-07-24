(**
 * ContainerIntro.v
 *
 * Getter/setter layer.
 *)

(** Compcert helper lib *)
Require Import Coqlib.
Require Import Maps.
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
Require Import ContainerType.

(** In this file we will build a layer that implements the getters and setters
  for a 'container' object. See [ContainerType] for an explanation of what a
  container is. We implement ony 4 getters, and 2 setters because the remaining
  fields are not modified after initialization. *)

Open Scope Z_scope.

Definition boot_init : ident := 1%positive.
Definition container_node_init : ident := 2%positive.
Definition container_get_quota : ident := 3%positive.
Definition container_get_usage : ident := 4%positive.
Definition container_get_parent : ident := 5%positive.
Definition container_get_nchildren : ident := 6%positive.
Definition container_set_usage : ident := 7%positive.
Definition container_set_nchildren : ident := 8%positive.
Definition CONTAINER_POOL : ident := 9%positive.

Section ContainerIntro.

  Context `{Hmem: BaseMemoryModel}.
  Context `{MakeProgramSpec.MakeProgram}.

  (** ** Abstract Data *)
  Section AbsData.

    (** *** Underlay *)

    (** In this example, instead of making the bottom later empty, we assume
      we have a [boot_init] primitive whose only function is to set [init_flag]
      to true. We do this to more closely mirror the actual implementation of
      containers in CertiKOS.

      Another difference from the stack example is that each of the layers uses
      the same abstract data representation. This also matches CertiKOS where
      the same data type is used throughout, just with different invariants. *)

    Instance boot_data_ops : AbstractDataOps container_data :=
      {|
        init_data := container_data_init;
        data_inv := fun _ => True;
        data_inject := fun _ _ _ => True
      |}.

    Instance boot_data_data : AbstractData container_data.
    Proof. repeat constructor. Qed.

    Definition boot_layerdata : layerdata :=
      {|
        ldata_type := container_data;
        ldata_ops  := boot_data_ops;
        ldata_prf  := boot_data_data
      |}.

    Definition boot_init_high_spec (abs: container_data) : container_data :=
      {|
        init_flag := true;
        cpool := cpool abs
      |}.

    Definition boot_init_high_sem : cprimitive boot_layerdata :=
      cgensem boot_layerdata boot_init_high_spec.

    Definition boot_L : clayer boot_layerdata := boot_init ↦ boot_init_high_sem.

    (** *** Overlay *)

    (** Our invariant requires that until [boot_init] has been called, the
      container pool must remain in its initial state. *)
    Record container_intro_data_inv (d: container_data) : Prop := {
      preinit_inv: init_flag d = false -> cpool d = ZMap.init container_unused
    }.

    Instance container_intro_data_ops : AbstractDataOps container_data :=
      {|
        init_data := {| init_flag := false;
                        cpool := ZMap.init container_unused |};
        data_inv := container_intro_data_inv;
        data_inject := fun _ _ _ => True
      |}.

    Instance container_intro_data_data : AbstractData container_data.
    Proof. repeat constructor. Qed.

    Definition container_intro_layerdata : layerdata :=
      {|
        ldata_type := container_data;
        ldata_ops  := container_intro_data_ops;
        ldata_prf  := container_intro_data_data
      |}.

  End AbsData.

  (** ** High Level Specifications *)
  Section HighSpec.

    (** [node_init] initializes a particular container with a given quota and
      parent. *)
    Definition container_node_init_high_spec (id: Z) (quota: Z) (parent: Z)
                                             (abs: container_intro_layerdata)
                                             : option container_intro_layerdata :=
      if init_flag abs
        then if decide (0 <= id < NUM_ID)
          then let c := mkContainer quota 0 parent nil true in
            Some {| init_flag := (init_flag abs); cpool := ZMap.set id c (cpool abs) |}
          else None
        else None.

    Definition container_node_init_high_sem : cprimitive container_intro_layerdata :=
      cgensem container_intro_layerdata container_node_init_high_spec.

    Definition container_node_init_layer : clayer container_intro_layerdata :=
      container_node_init ↦ container_node_init_high_sem.

    Global Instance container_node_init_pres_inv :
      GenSemPreservesInvariant container_intro_layerdata container_node_init_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      unfold container_node_init_high_spec in H3.
      repeat destr_in H3; try discriminate. inv H3.
      constructor; cbn. discriminate.
    Qed.

    Definition container_get_quota_high_spec (id: Z) (abs: container_intro_layerdata)
                                             : option Z :=
      if decide (0 <= id < NUM_ID)
        then let c := ZMap.get id (cpool abs) in
          if cused c
            then Some (cquota c)
            else None
        else None.

    Definition container_get_quota_high_sem : cprimitive container_intro_layerdata :=
      cgensem container_intro_layerdata container_get_quota_high_spec.

    Definition container_get_quota_layer : clayer container_intro_layerdata :=
      container_get_quota ↦ container_get_quota_high_sem.

    Global Instance container_get_quota_pres_inv :
      GenSemPreservesInvariant container_intro_layerdata container_get_quota_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      assumption.
    Qed.

    Definition container_get_usage_high_spec (id: Z) (abs: container_intro_layerdata)
                                             : option Z :=
      if decide (0 <= id < NUM_ID)
        then let c := ZMap.get id (cpool abs) in
          if cused c
            then Some (cusage c)
            else None
        else None.

    Definition container_get_usage_high_sem : cprimitive container_intro_layerdata :=
      cgensem container_intro_layerdata container_get_usage_high_spec.

    Definition container_get_usage_layer : clayer container_intro_layerdata :=
      container_get_usage ↦ container_get_usage_high_sem.

    Global Instance container_get_usage_pres_inv :
      GenSemPreservesInvariant container_intro_layerdata container_get_usage_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      assumption.
    Qed.

    Definition container_get_parent_high_spec (id: Z) (abs: container_intro_layerdata)
                                              : option Z :=
      if decide (0 <= id < NUM_ID)
        then let c := ZMap.get id (cpool abs) in
          if cused c
            then Some (cparent c)
            else None
        else None.

    Definition container_get_parent_high_sem : cprimitive container_intro_layerdata :=
      cgensem container_intro_layerdata container_get_parent_high_spec.

    Definition container_get_parent_layer : clayer container_intro_layerdata :=
      container_get_parent ↦ container_get_parent_high_sem.

    Global Instance container_get_parent_pres_inv :
      GenSemPreservesInvariant container_intro_layerdata container_get_parent_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      assumption.
    Qed.

    Definition container_get_nchildren_high_spec (id: Z) (abs: container_intro_layerdata)
                                                 : option Z :=
      if decide (0 <= id < NUM_ID)
        then let c := ZMap.get id (cpool abs) in
          if cused c
            then Some (Z.of_nat (length (cchildren c)))
            else None
        else None.

    Definition container_get_nchildren_high_sem : cprimitive container_intro_layerdata :=
      cgensem container_intro_layerdata container_get_nchildren_high_spec.

    Definition container_get_nchildren_layer : clayer container_intro_layerdata :=
      container_get_nchildren ↦ container_get_nchildren_high_sem.

    Global Instance container_get_nchildren_pres_inv :
      GenSemPreservesInvariant container_intro_layerdata container_get_nchildren_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      assumption.
    Qed.

    Definition container_set_usage_high_spec (id: Z) (usage: Z)
                                             (abs: container_intro_layerdata)
                                             : option container_intro_layerdata :=
      if decide (0 <= id < NUM_ID)
        then let c := ZMap.get id (cpool abs) in
          if decide (0 <= usage <= cquota c)
            then match init_flag abs, cused c with
            | true, true =>
                let c' := mkContainer (cquota c) usage (cparent c) (cchildren c) (cused c) in
                Some {| init_flag := init_flag abs; cpool := ZMap.set id c' (cpool abs) |}
            | _, _ => None
            end
            else None
        else None.

    Definition container_set_usage_high_sem : cprimitive container_intro_layerdata :=
      cgensem container_intro_layerdata container_set_usage_high_spec.

    Definition container_set_usage_layer : clayer container_intro_layerdata :=
      container_set_usage ↦ container_set_usage_high_sem.

    Global Instance container_set_usage_pres_inv :
      GenSemPreservesInvariant container_intro_layerdata container_set_usage_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      unfold container_set_usage_high_spec in H3.
      repeat destr_in H3; try discriminate.
      inv H3.
      constructor; cbn. discriminate.
    Qed.

    Definition container_set_nchildren_high_spec (id: Z) (next_child: Z)
                                                 (abs: container_intro_layerdata)
                                                 : option container_intro_layerdata :=
      if decide (0 <= id < NUM_ID)
        then let c := ZMap.get id (cpool abs) in
          if decide (Z.of_nat (length (cchildren c)) <= MAX_CHILDREN)
            then match init_flag abs, cused c with
            | true, true =>
                let c' := mkContainer (cquota c) (cusage c) (cparent c)
                                      (next_child :: cchildren c) (cused c) in
                Some {| init_flag := init_flag abs; cpool := ZMap.set id c' (cpool abs) |}
            | _, _ => None
            end
            else None
        else None.

    Definition container_set_nchildren_high_sem : cprimitive container_intro_layerdata :=
      cgensem container_intro_layerdata container_set_nchildren_high_spec.

    Definition container_set_nchildren_layer : clayer container_intro_layerdata :=
      container_set_nchildren ↦ container_set_nchildren_high_sem.

    Global Instance container_set_nchildren_pres_inv :
      GenSemPreservesInvariant container_intro_layerdata container_set_nchildren_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      unfold container_set_nchildren_high_spec in H3.
      repeat destr_in H3; try discriminate.
      inv H3.
      constructor; cbn. discriminate.
    Qed.

  End HighSpec.

  (** ** Module Implementation *)
  Section Code.

    (** Information about structs and unions are stored in [Composite]
      types in Compcert. *)
    Definition t_container : ident := 9%positive.
    Definition t_container_quota : ident := 10%positive.
    Definition t_container_usage : ident := 11%positive.
    Definition t_container_parent : ident := 12%positive.
    Definition t_container_nchildren : ident := 13%positive.
    Definition t_container_used : ident := 14%positive.
    Notation t_container_struct := (Tstruct t_container noattr).

    Definition t_container_comp : composite_definition :=
      Composite t_container Struct
               ((t_container_quota, tuint) ::
                (t_container_usage, tuint) ::
                (t_container_parent, tuint) ::
                (t_container_nchildren, tuint) ::
                (t_container_used, tuint) :: nil)
               noattr.

    Definition cni_id : ident := 15%positive.
    Definition cni_quota : ident := 16%positive.
    Definition cni_parent : ident := 17%positive.

    Definition f_container_node_init :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := (cni_id, tuint) :: (cni_quota, tuint) :: (cni_parent, tuint) :: nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                    (Etempvar cni_id tuint) (tptr t_container_struct))
                  t_container_struct) t_container_quota tuint)
              (Etempvar cni_quota tuint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                      (Etempvar cni_id tuint) (tptr t_container_struct))
                    t_container_struct) t_container_usage tuint)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                        (Etempvar cni_id tuint) (tptr t_container_struct))
                      t_container_struct) t_container_parent tuint)
                  (Etempvar cni_parent tuint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                          (Etempvar cni_id tuint) (tptr t_container_struct))
                        t_container_struct) t_container_nchildren tuint)
                    (Econst_int (Int.repr 0) tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                          (Etempvar cni_id tuint) (tptr t_container_struct))
                        t_container_struct) t_container_used tuint)
                    (Econst_int (Int.repr 1) tint)))))
      |}.

    Program Definition inlinable_f_container_node_init : function :=
      inline f_container_node_init _.

    Definition cgq_id : ident := 18%positive.

    Definition f_container_get_quota :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := ((cgq_id, tuint) :: nil);
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          (Sreturn (Some (Efield
                           (Ederef
                             (Ebinop Oadd
                               (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                               (Etempvar cgq_id tuint) (tptr t_container_struct))
                             t_container_struct) t_container_quota tuint)))
      |}.

    Program Definition inlinable_f_container_get_quota : function :=
      inline f_container_get_quota _.

    Definition cgu_id : ident := 19%positive.

    Definition f_container_get_usage :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := ((cgu_id, tuint) :: nil);
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          (Sreturn (Some (Efield
                           (Ederef
                             (Ebinop Oadd
                               (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                               (Etempvar cgu_id tuint) (tptr t_container_struct))
                             t_container_struct) t_container_usage tuint)))
      |}.

    Program Definition inlinable_f_container_get_usage : function :=
      inline f_container_get_usage _.

    Definition cgp_id := 20%positive.

    Definition f_container_get_parent :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := ((cgp_id, tuint) :: nil);
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          (Sreturn (Some (Efield
                           (Ederef
                             (Ebinop Oadd
                               (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                               (Etempvar cgp_id tuint) (tptr t_container_struct))
                             t_container_struct) t_container_parent tuint)))
      |}.

    Program Definition inlinable_f_container_get_parent : function :=
      inline f_container_get_parent _.

    Definition cgn_id := 21%positive.

    Definition f_container_get_nchildren :=
      {|
        fn_return := tuint;
        fn_callconv := cc_default;
        fn_params := ((cgn_id, tuint) :: nil);
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          (Sreturn (Some (Efield
                           (Ederef
                             (Ebinop Oadd
                               (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                               (Etempvar cgn_id tuint) (tptr t_container_struct))
                             t_container_struct) t_container_nchildren tuint)))
      |}.

    Program Definition inlinable_f_container_get_nchildren : function :=
      inline f_container_get_nchildren _.

    Definition csu_id := 22%positive.
    Definition csu_usage := 23%positive.

    Definition f_container_set_usage :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := ((csu_id, tuint) :: (csu_usage, tuint) :: nil);
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                  (Etempvar csu_id tuint) (tptr t_container_struct))
                t_container_struct) t_container_usage tuint)
            (Etempvar csu_usage tuint))
      |}.

    Program Definition inlinable_f_container_set_usage : function :=
      inline f_container_set_usage _.

    Definition csn_id : ident := 24%positive.
    Definition csn_next_child : ident := 25%positive.

    Definition f_container_set_nchildren :=
      {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := ((csn_id, tuint) :: (csn_next_child, tuint) :: nil);
        fn_vars := nil;
        fn_temps := nil;
        fn_body :=
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                  (Etempvar csn_id tuint) (tptr t_container_struct))
                t_container_struct) t_container_nchildren tuint)
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Evar CONTAINER_POOL (tarray t_container_struct NUM_ID))
                    (Etempvar csn_id tuint) (tptr t_container_struct))
                  t_container_struct) t_container_nchildren tuint)
              (Econst_int (Int.repr 1) tint) tuint))
      |}.

    Program Definition inlinable_f_container_set_nchildren : function :=
      inline f_container_set_nchildren _.

    Definition Minit : cmodule := container_node_init ↦ inlinable_f_container_node_init.
    Definition Mgquota : cmodule := container_get_quota ↦ inlinable_f_container_get_quota.
    Definition Mgusage : cmodule := container_get_usage ↦ inlinable_f_container_get_usage.
    Definition Mgparent : cmodule := container_get_parent ↦ inlinable_f_container_get_parent.
    Definition Mgnchild : cmodule := container_get_nchildren ↦ inlinable_f_container_get_nchildren.
    Definition Msusage : cmodule := container_set_usage ↦ inlinable_f_container_set_usage.
    Definition Msnchild : cmodule := container_set_nchildren ↦ inlinable_f_container_set_nchildren.

  End Code.

  (** ** Low Level Specifications *)
  Section LowSpec.

    Definition container_node_init_csig :=
      mkcsig (type_of_list_type (tuint :: tuint :: tuint :: nil)) tvoid.

    Inductive container_node_init_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | container_node_init_step_into m d cpb i q p m1 m2 m3 m4 m':
        forall (Hcpb: find_symbol CONTAINER_POOL = Some cpb),
        0 <= Int.unsigned i < NUM_ID ->
        Mem.store Mint32 m cpb (con_sz * Int.unsigned i + quo_off) (Vint q) = Some m1 ->
        Mem.store Mint32 m1 cpb (con_sz * Int.unsigned i + usg_off) (Vint Int.zero) = Some m2 ->
        Mem.store Mint32 m2 cpb (con_sz * Int.unsigned i + par_off) (Vint p) = Some m3 ->
        Mem.store Mint32 m3 cpb (con_sz * Int.unsigned i + nch_off) (Vint Int.zero) = Some m4 ->
        Mem.store Mint32 m4 cpb (con_sz * Int.unsigned i + use_off) (Vint Int.one) = Some m' ->
        container_node_init_step container_node_init_csig
                                 (Vint i :: Vint q :: Vint p :: nil, (m, d))
                                 (Vundef, (m', d)).

    Definition container_get_quota_csig := mkcsig (type_of_list_type (tuint :: nil)) tuint.

    Inductive container_get_quota_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | container_get_quota_step_into m d cpb i q:
        forall (Hcpb: find_symbol CONTAINER_POOL = Some cpb),
        0 <= Int.unsigned i < NUM_ID ->
        Mem.load Mint32 m cpb (con_sz * Int.unsigned i + quo_off) = Some (Vint q) ->
        container_get_quota_step container_get_quota_csig
                                 (Vint i :: nil, (m, d))
                                 (Vint q, (m, d)).

    Definition container_get_usage_csig := mkcsig (type_of_list_type (tuint :: nil)) tuint.

    Inductive container_get_usage_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | container_get_usage_step_into m d cpb i u:
        forall (Hcpb: find_symbol CONTAINER_POOL = Some cpb),
        0 <= Int.unsigned i < NUM_ID ->
        Mem.load Mint32 m cpb (con_sz * Int.unsigned i + usg_off) = Some (Vint u) ->
        container_get_usage_step container_get_usage_csig
                                 (Vint i :: nil, (m, d))
                                 (Vint u, (m, d)).

    Definition container_get_parent_csig := mkcsig (type_of_list_type (tuint :: nil)) tuint.

    Inductive container_get_parent_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | container_get_parent_step_into m d cpb i p:
        forall (Hcpb: find_symbol CONTAINER_POOL = Some cpb),
        0 <= Int.unsigned i < NUM_ID ->
        Mem.load Mint32 m cpb (con_sz * Int.unsigned i + par_off) = Some (Vint p) ->
        container_get_parent_step container_get_parent_csig
                                  (Vint i :: nil, (m, d))
                                  (Vint p, (m, d)).

    Definition container_get_nchildren_csig := mkcsig (type_of_list_type (tuint :: nil)) tuint.

    Inductive container_get_nchildren_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | container_get_nchildren_step_into m d cpb i n:
        forall (Hcpb: find_symbol CONTAINER_POOL = Some cpb),
        0 <= Int.unsigned i < NUM_ID ->
        Mem.load Mint32 m cpb (con_sz * Int.unsigned i + nch_off) = Some (Vint n) ->
        container_get_nchildren_step container_get_nchildren_csig
                                     (Vint i :: nil, (m, d))
                                     (Vint n, (m, d)).

    Definition container_set_usage_csig :=
      mkcsig (type_of_list_type (tuint :: tuint :: nil)) tvoid.

    Inductive container_set_usage_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | container_set_usage_step_into m d cpb i u m':
        forall (Hcpb: find_symbol CONTAINER_POOL = Some cpb),
        0 <= Int.unsigned i < NUM_ID ->
        Mem.store Mint32 m cpb (con_sz * Int.unsigned i + usg_off) (Vint u) = Some m' ->
        container_set_usage_step container_set_usage_csig
                                 (Vint i :: Vint u :: nil, (m, d))
                                 (Vundef, (m', d)).

    Definition container_set_nchildren_csig :=
      mkcsig (type_of_list_type (tuint :: tuint :: nil)) tvoid.

    Inductive container_set_nchildren_step :
      csignature -> list val * mwd boot_layerdata -> val * mwd boot_layerdata -> Prop :=
    | container_set_nchildren_step_into m d cpb i cur nxt m':
        forall (Hcpb: find_symbol CONTAINER_POOL = Some cpb),
        0 <= Int.unsigned i < NUM_ID ->
        Mem.load Mint32 m cpb (con_sz * Int.unsigned i + nch_off) = Some (Vint cur) ->
        Mem.store Mint32 m cpb (con_sz * Int.unsigned i + nch_off) (Vint (Int.add cur Int.one)) = Some m' ->
        container_set_nchildren_step container_set_nchildren_csig
                                     (Vint i :: Vint nxt :: nil, (m, d))
                                     (Vundef, (m', d)).

    Program Definition container_node_init_cprimitive : cprimitive boot_layerdata :=
      mkcprimitive _ container_node_init_step container_node_init_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition container_get_quota_cprimitive : cprimitive boot_layerdata :=
      mkcprimitive _ container_get_quota_step container_get_quota_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition container_get_usage_cprimitive : cprimitive boot_layerdata :=
      mkcprimitive _ container_get_usage_step container_get_usage_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition container_get_parent_cprimitive : cprimitive boot_layerdata :=
      mkcprimitive _ container_get_parent_step container_get_parent_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition container_get_nchildren_cprimitive : cprimitive boot_layerdata :=
      mkcprimitive _ container_get_nchildren_step container_get_nchildren_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition container_set_usage_cprimitive : cprimitive boot_layerdata :=
      mkcprimitive _ container_set_usage_step container_set_usage_csig _.
    Next Obligation.
      now inv H0.
    Qed.

    Program Definition container_set_nchildren_cprimitive : cprimitive boot_layerdata :=
      mkcprimitive _ container_set_nchildren_step container_set_nchildren_csig _.
    Next Obligation.
      now inv H0.
    Qed.

  End LowSpec.

  (** ** Code Proofs *)
  Section CodeLowSpecSim.

    (** Get our struct definition into the context. *)
    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce : build_composite_env (t_container_comp :: nil) = OK ce.

    (** The code proofs are made fairly short by using the
      [container_fields_(store|load)_ok] lemmas from [ContainerType]. *)

    Lemma container_node_init_code :
      boot_L ⊢ (id, Minit) : (container_node_init ↦ container_node_init_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step.
      repeat step_tac; unfold lift; cbn;
        erewrite container_fields_store_ok; unfold_fields; try omega; eauto.
      reflexivity.
    Qed.

    Lemma container_get_quota_code :
      boot_L ⊢ (id, Mgquota) : (container_get_quota ↦ container_get_quota_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      - unfold lift; cbn.
        erewrite container_fields_load_ok; unfold_fields; try omega; eauto.
      - reflexivity.
    Qed.

    Lemma container_get_usage_code :
      boot_L ⊢ (id, Mgusage) : (container_get_usage ↦ container_get_usage_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      - unfold lift; cbn.
        erewrite container_fields_load_ok; unfold_fields; try omega; eauto.
      - reflexivity.
    Qed.

    Lemma container_get_parent_code :
      boot_L ⊢ (id, Mgparent) : (container_get_parent ↦ container_get_parent_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      - unfold lift; cbn.
        erewrite container_fields_load_ok; unfold_fields; try omega; eauto.
      - reflexivity.
    Qed.

    Lemma container_get_nchildren_code :
      boot_L ⊢ (id, Mgnchild) : (container_get_nchildren ↦ container_get_nchildren_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      - unfold lift; cbn.
        erewrite container_fields_load_ok; unfold_fields; try omega; eauto.
      - reflexivity.
    Qed.

    Lemma container_set_usage_code :
      boot_L ⊢ (id, Msusage) : (container_set_usage ↦ container_set_usage_cprimitive).
    Proof.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      unfold lift; cbn.
      erewrite container_fields_store_ok; unfold_fields; try omega; eauto.
      reflexivity.
    Qed.

    Lemma container_set_nchildren_code :
      boot_L ⊢ (id, Msnchild) : (container_set_nchildren ↦ container_set_nchildren_cprimitive).
    Proof.
      Opaque Z.mul.
      code_proof_tac.
      inv CStep.
      inv Hce.
      cprim_step. repeat step_tac.
      - unfold lift; cbn.
        erewrite container_fields_load_ok; unfold_fields; try omega; eauto.
        change (align 0 4) with 0; cbn.
        change (align 4 4) with 4; cbn.
        change (align 8 4) with 8; cbn.
        change (align 12 4) with 12; cbn.
        omega.
      - reflexivity.
      - reflexivity.
      - unfold lift; cbn.
        erewrite container_fields_store_ok; unfold_fields; try omega; eauto.
        reflexivity.
        change (align 0 4) with 0; cbn.
        change (align 4 4) with 4; cbn.
        change (align 8 4) with 8; cbn.
        change (align 12 4) with 12; cbn.
        omega.
    Qed.

  End CodeLowSpecSim.

  (** ** Layer Relation *)
  Section LowHighSpecRel.

    (** We say our high level abstract data matches a memory state if every
      field of every container is writable, and if the values stored there
      match the values in the abstract [container_abs] representation. *)
    Inductive match_container : container_abs -> val -> val -> val -> val -> val -> Prop :=
    | match_container_unused: forall q u p c qv uv pv cv,
        match_container (mkContainer q u p c false) qv uv pv cv Vfalse
    | match_container_used: forall q u p c qv uv pv cv,
        qv = Vint (Int.repr q) ->
        uv = Vint (Int.repr u) ->
        pv = Vint (Int.repr p) ->
        cv = Vint (Int.repr (Z.of_nat (length c))) ->
        match_container (mkContainer q u p c true) qv uv pv cv Vtrue.

    Inductive match_data : container_intro_layerdata -> mem -> Prop :=
    | match_data_intro:
        forall m (abs: container_intro_layerdata) cpb
               (Hcpb: find_symbol CONTAINER_POOL = Some cpb),
          (forall i, 0 <= i < NUM_ID ->
            (exists quo usg par nch use,
              Mem.load Mint32 m cpb (con_sz * i + quo_off) = Some (Vint quo) /\
              Mem.load Mint32 m cpb (con_sz * i + usg_off) = Some (Vint usg) /\
              Mem.load Mint32 m cpb (con_sz * i + par_off) = Some (Vint par) /\
              Mem.load Mint32 m cpb (con_sz * i + nch_off) = Some (Vint nch) /\
              Mem.load Mint32 m cpb (con_sz * i + use_off) = Some (Vint use) /\
              Mem.valid_access m Mint32 cpb (con_sz * i + quo_off) Writable /\
              Mem.valid_access m Mint32 cpb (con_sz * i + usg_off) Writable /\
              Mem.valid_access m Mint32 cpb (con_sz * i + par_off) Writable /\
              Mem.valid_access m Mint32 cpb (con_sz * i + nch_off) Writable /\
              Mem.valid_access m Mint32  cpb (con_sz * i + use_off) Writable /\
              match_container (ZMap.get i (cpool abs))
                              (Vint quo) (Vint usg) (Vint par) (Vint nch) (Vint use))) ->
          match_data abs m.

    Record relate_data (hadt: container_intro_layerdata) (ladt: boot_layerdata) :=
      mkrelate_data {
        init_rel: init_flag hadt = init_flag ladt
      }.

    Definition abrel_components_container_intro_boot :
      abrel_components container_intro_layerdata boot_layerdata :=
      {|
        abrel_relate := relate_data;
        abrel_match  := match_data;
        abrel_new_glbl :=
          (CONTAINER_POOL, Init_space (NUM_ID * con_sz) :: nil) ::
          nil
      |}.

    Global Instance rel_ops :
      AbstractionRelation _ _ abrel_components_container_intro_boot.
    Proof.
      constructor.
      - constructor; reflexivity.
      - intros.
        inv_abrel_init_props.
        econstructor; eauto.
        intros.
        Opaque Z.mul.
        pose NUM_ID_range as nid_range; destruct nid_range as [nid_lo nid_hi].
        cbn in *.
        unfold_fields.
        rewrite Zmax_left in aip_perm by omega.
        destruct aip_load as [aip_load ?].
        do 5 eexists.
        repeat match goal with
        | |- _ /\ _ => split
        | |- Mem.load _ _ _ _ = Some _ =>
          apply aip_load; [omega | apply container_fields_align; auto | try omega]
        | |- (4 | ?x * 20) => exists (5*x); omega
        | |- Mem.valid_access _ _ _ (20 * i + ?off) _ =>
            split; cbn;
            [red; intros; apply aip_perm; omega |
             apply container_fields_align; auto]
        end.
        rewrite ZMap.gi.
        constructor.
      - repeat red; cbn. intros d m1 m2 Hunchange Hmatch1.
        inv Hmatch1; econstructor; eauto.
        intros i Hi; specialize (H0 i Hi).
        destruct H0 as (quo & usg & par & nch & use & ? & ? & ? & ? & ? & ? &
                        ? & ? & ? & ? & ?).
        repeat match goal with
        | [H: Mem.valid_access _ _ _ _ _ |- _] => destruct H; red in H
        end.
        do 5 eexists.
        repeat match goal with
        | |- _ /\ _ => split
        | |- Mem.load _ _ _ _ = Some _ =>
          eapply Mem.load_unchanged_on; eauto; red; cbn; eauto
        | |- Mem.valid_access _ _ _ _ _ =>
          split;
          [red; intros; eapply Mem.perm_unchanged_on; eauto; red; cbn; eauto |
           eauto]
        end.
        assumption.
      - decision.
    Qed.

    Definition abrel_container_intro_boot :
        abrel container_intro_layerdata boot_layerdata :=
      {|
        abrel_ops := abrel_components_container_intro_boot;
        abrel_prf := rel_ops
      |}.

    Definition container_intro_R : simrel _ _ :=
      abrel_simrel _ _ abrel_container_intro_boot.

  End LowHighSpecRel.

  (** ** Refinement Proofs *)
  Section LowHighSpecSim.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce : build_composite_env (t_container_comp :: nil) = OK ce.

    Local Ltac destr_match H :=
      destruct H as (?quo & ?usg & ?par & ?nch & ?use &
                     ?HLquo & ?HLusg & ?HLpar & ?HLnch & ?HLuse &
                     ?HVquo & ?HVusg & ?HVpar & ?HVnch & ?HVuse &
                     ?Hcon_match).

    (** The proofs involving setting a field get fairly long because it
      introduces more memory states to convert between. But after proving the
      refinement here, higher layer primitives need not directly refer to
      memory at all. *)

    Lemma container_node_init_refine :
      (container_node_init ↦ container_node_init_cprimitive) ⊢ (container_intro_R, ∅) : container_node_init_layer.
    Proof.
      Opaque Z.mul.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_node_init_high_spec in H1.
      repeat destr_in H1; inv H1.
      pose proof H0 as Hmatch.
      specialize (H0 (Int.unsigned i) a).
      destr_match H0.
      pose proof HVquo as HVquo'.
      pose proof HVusg as HVusg'.
      pose proof HVpar as HVpar'.
      pose proof HVnch as HVnch'.
      pose proof HVuse as HVuse'.
      eapply Mem.valid_access_store in HVquo; destruct HVquo as (m1 & HSquo).
      eapply Mem.store_valid_access_1 in HVusg; eauto.
      eapply Mem.valid_access_store in HVusg; destruct HVusg as (m2 & HSusg).
      eapply Mem.store_valid_access_1 in HVpar; eauto.
      eapply Mem.store_valid_access_1 in HVpar; eauto.
      eapply Mem.valid_access_store in HVpar; destruct HVpar as (m3 & HSpar).
      eapply Mem.store_valid_access_1 in HVnch; eauto.
      eapply Mem.store_valid_access_1 in HVnch; eauto.
      eapply Mem.store_valid_access_1 in HVnch; eauto.
      eapply Mem.valid_access_store in HVnch; destruct HVnch as (m4 & HSnch).
      eapply Mem.store_valid_access_1 in HVuse; eauto.
      eapply Mem.store_valid_access_1 in HVuse; eauto.
      eapply Mem.store_valid_access_1 in HVuse; eauto.
      eapply Mem.store_valid_access_1 in HVuse; eauto.
      eapply Mem.valid_access_store in HVuse; destruct HVuse as (m5 & HSuse).
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + constructor.
        + cbn; split.
          * assert (Mem.extends xm' m1).
            { eapply Mem.store_outside_extends; eauto.
              intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
            }
            assert (Mem.extends xm' m2).
            { eapply Mem.store_outside_extends; eauto.
              intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
            }
            assert (Mem.extends xm' m3).
            { eapply Mem.store_outside_extends; eauto.
              intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
            }
            assert (Mem.extends xm' m4).
            { eapply Mem.store_outside_extends; eauto.
              intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
            }
            eapply Mem.store_outside_extends; eauto.
            intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
          * constructor.
            -- constructor; auto.
            -- econstructor; eauto.
               intros ? Hi.
               unfold_fields.
               destr_eq i2 (Int.unsigned i).
               ++ subst.
                  do 5 eexists.
                  repeat match goal with
                  | |- _ /\ _ => split
                  | |- Mem.valid_access _ _ _ _ _ =>
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSuse);
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSnch);
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSpar);
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSusg);
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSquo);
                    assumption
                  end.
                  { (** Load quota *)
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSuse).
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSnch).
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSpar).
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSusg).
                    apply (Mem.load_store_same _ _ _ _ _ _ HSquo).
                    all: right; cbn; omega.
                  }
                  { (** Load usage *)
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSuse).
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSnch).
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSpar).
                    apply (Mem.load_store_same _ _ _ _ _ _ HSusg).
                    all: right; cbn; omega.
                  }
                  { (** Load parent *)
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSuse).
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSnch).
                    apply (Mem.load_store_same _ _ _ _ _ _ HSpar).
                    all: right; cbn; omega.
                  }
                  { (** Load nchildren *)
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSuse).
                    apply (Mem.load_store_same _ _ _ _ _ _ HSnch).
                    right; cbn; omega.
                  }
                  { (** Load used *)
                    apply (Mem.load_store_same _ _ _ _ _ _ HSuse).
                  }
                  cbn. rewrite ZMap.gss. unfold Int.zero, Int.one.
                  constructor; try rewrite Int.repr_unsigned; reflexivity.
               ++ specialize (Hmatch i2 Hi).
                  destr_match Hmatch.
                  do 5 eexists.
                  repeat match goal with
                  | |- _ /\ _ => split
                  | |- Mem.load _ _ _ _ = Some _ =>
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSuse);
                      [| right; cbn; omega];
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSnch);
                      [| right; cbn; omega];
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSpar);
                      [| right; cbn; omega];
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSusg);
                      [| right; cbn; omega];
                    rewrite (Mem.load_store_other _ _ _ _ _ _ HSquo);
                      [eassumption | right; cbn; omega]
                  | |- Mem.valid_access _ _ _ _ _ =>
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSuse);
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSnch);
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSpar);
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSusg);
                    eapply (Mem.store_valid_access_1 _ _ _ _ _ _ HSquo);
                    assumption
                  end.
                  cbn. rewrite ZMap.gso; assumption.
            -- cbn; intros.
               specialize (abrel_match_mem_perms _ _ _ ofs k p H0 H1).
               destruct abrel_match_mem_perms as (NP & P).
               split; auto.
               red; intros. repeat (eapply Mem.perm_store_1; eauto).
            -- rewrite (Mem.nextblock_store _ _ _ _ _ _ HSuse).
               rewrite (Mem.nextblock_store _ _ _ _ _ _ HSnch).
               rewrite (Mem.nextblock_store _ _ _ _ _ _ HSpar).
               rewrite (Mem.nextblock_store _ _ _ _ _ _ HSusg).
               rewrite (Mem.nextblock_store _ _ _ _ _ _ HSquo).
               eauto.
    Qed.

    Lemma container_get_quota_refine :
      (container_get_quota ↦ container_get_quota_cprimitive) ⊢ (container_intro_R, ∅) : container_get_quota_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_get_quota_high_spec in H2.
      repeat destr_in H2; inv H2.
      specialize (H0 (Int.unsigned i) a).
      destr_match H0.
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + cbn.
          inv Hcon_match.
          * rewrite <- H1 in Heqb. discriminate.
          * rewrite <- H0 in H3. cbn in H3; subst.
            rewrite H2. rewrite Int.repr_unsigned. constructor.
        + split; eauto.
    Qed.

    Lemma container_get_usage_refine :
      (container_get_usage ↦ container_get_usage_cprimitive) ⊢ (container_intro_R, ∅) : container_get_usage_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_get_usage_high_spec in H2.
      repeat destr_in H2; inv H2.
      specialize (H0 (Int.unsigned i) a).
      destr_match H0.
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + cbn.
          inv Hcon_match.
          * rewrite <- H1 in Heqb. discriminate.
          * rewrite <- H0 in H3. cbn in H3; subst.
            rewrite H4. rewrite Int.repr_unsigned. constructor.
        + split; eauto.
    Qed.

    Lemma container_get_parent_refine :
      (container_get_parent ↦ container_get_parent_cprimitive) ⊢ (container_intro_R, ∅) : container_get_parent_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_get_parent_high_spec in H2.
      repeat destr_in H2; inv H2.
      specialize (H0 (Int.unsigned i) a).
      destr_match H0.
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + cbn.
          inv Hcon_match.
          * rewrite <- H1 in Heqb. discriminate.
          * rewrite <- H0 in H3. cbn in H3; subst.
            rewrite H5. rewrite Int.repr_unsigned. constructor.
        + split; eauto.
    Qed.

    Lemma container_get_nchildren_refine :
      (container_get_nchildren ↦ container_get_nchildren_cprimitive) ⊢ (container_intro_R, ∅) : container_get_nchildren_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_get_nchildren_high_spec in H2.
      repeat destr_in H2; inv H2.
      specialize (H0 (Int.unsigned i) a).
      destr_match H0.
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + cbn.
          inv Hcon_match.
          * rewrite <- H1 in Heqb. discriminate.
          * rewrite <- H0 in H3. cbn in H3.
            rewrite H10. rewrite H3. rewrite Int.repr_unsigned. constructor.
        + split; eauto.
    Qed.

    Lemma container_set_usage_refine :
      (container_set_usage ↦ container_set_usage_cprimitive) ⊢ (container_intro_R, ∅) : container_set_usage_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_set_usage_high_spec in H1.
      repeat destr_in H1; inv H1.
      pose proof H0 as Hmatch.
      specialize (H0 (Int.unsigned i) a).
      destr_match H0.
      inv Hcon_match; cbn.
      rewrite <- H1 in Heqb0; discriminate.
      pose proof HVusg as HVusg'.
      eapply Mem.valid_access_store in HVusg; destruct HVusg as (m1 & HSusg).
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + constructor.
        + split; cbn.
          * eapply Mem.store_outside_extends; eauto.
            intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
          * constructor.
            -- constructor. cbn; auto.
            -- econstructor; eauto.
               intros ? Hi.
               unfold_fields.
               destr_eq i1 (Int.unsigned i).
               ++ subst.
                  do 5 eexists.
                  repeat match goal with
                  | |- _ /\ _ => split
                  | |- Mem.load _ _ _ _ = Some _ =>
                      try (rewrite (Mem.load_store_other _ _ _ _ _ _ HSusg);
                      [eassumption | right; cbn; omega])
                  | |- Mem.valid_access _ _ _ _ _ =>
                      eapply Mem.store_valid_access_1; eauto
                  end.
                  rewrite (Mem.load_store_same _ _ _ _ _ _ HSusg); reflexivity.
                  cbn. rewrite ZMap.gss.
                  constructor; auto.
                  rewrite Int.repr_unsigned; reflexivity.
               ++ specialize (Hmatch i1 Hi).
                  destr_match Hmatch.
                  do 5 eexists.
                  repeat match goal with
                  | |- _ /\ _ => split
                  | |- Mem.load _ _ _ _ = Some _ =>
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HSusg);
                      [eassumption | right; cbn; omega]
                  | |- Mem.valid_access _ _ _ _ _ =>
                      eapply Mem.store_valid_access_1; eauto
                  end.
                  cbn. rewrite ZMap.gso; assumption.
            -- cbn; intros.
               specialize (abrel_match_mem_perms _ _ _ ofs k p0 H1 H5).
               destruct abrel_match_mem_perms as (NP & P).
               split; auto.
               red; intros. eapply Mem.perm_store_1; eauto.
            -- rewrite (Mem.nextblock_store _ _ _ _ _ _ HSusg); eauto.
    Qed.

    Lemma container_set_nchildren_refine :
      (container_set_nchildren ↦ container_set_nchildren_cprimitive) ⊢ (container_intro_R, ∅) : container_set_nchildren_layer.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      inv abrel_match_mem_relate.
      unfold container_set_nchildren_high_spec in H1.
      repeat destr_in H1; try discriminate.
      inv H1.
      pose proof H0 as Hmatch.
      specialize (H0 (Int.unsigned i) a).
      destr_match H0.
      inv Hcon_match; cbn.
      rewrite <- H1 in Heqb0; discriminate.
      pose proof HVnch as HVnch'.
      eapply Mem.valid_access_store in HVnch; destruct HVnch as (m1 & HSnch).
      do 3 eexists; split.
      - econstructor; eauto.
      - split.
        + constructor.
        + split; cbn.
          * eapply Mem.store_outside_extends; eauto.
            intros ? Hperm; eapply abrel_match_mem_perms in Hperm; eauto.
          * constructor.
            -- constructor. cbn; auto.
            -- econstructor; eauto.
               intros ? Hi.
               unfold_fields.
               destr_eq i1 (Int.unsigned i).
               ++ subst.
                  do 5 eexists.
                  repeat match goal with
                  | |- _ /\ _ => split
                  | |- Mem.load _ _ _ _ = Some _ =>
                      try (rewrite (Mem.load_store_other _ _ _ _ _ _ HSnch);
                      [eassumption | right; cbn; omega])
                  | |- Mem.valid_access _ _ _ _ _ =>
                      eapply Mem.store_valid_access_1; eauto
                  end.
                  rewrite (Mem.load_store_same _ _ _ _ _ _ HSnch); reflexivity.
                  cbn. rewrite ZMap.gss.
                  pose proof l as Hchild_range.
                  rewrite <- H0 in Hchild_range; cbn in Hchild_range.
                  pose MAX_CHILDREN_range as Hmaxchild_range.
                  constructor; auto.
                  inversion H9.
                  cbn; unfold Int.add.
                  rewrite Int.unsigned_one; rewrite Zpos_P_of_succ_nat.
                  rewrite <- Z.add_1_r.
                  repeat f_equal.
                  rewrite Int.unsigned_repr; [reflexivity | omega].
               ++ specialize (Hmatch i1 Hi).
                  destr_match Hmatch.
                  do 5 eexists.
                  repeat match goal with
                  | |- _ /\ _ => split
                  | |- Mem.load _ _ _ _ = Some _ =>
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HSnch);
                      [eassumption | right; cbn; omega]
                  | |- Mem.valid_access _ _ _ _ _ =>
                      eapply Mem.store_valid_access_1; eauto
                  end.
                  cbn. rewrite ZMap.gso; assumption.
            -- cbn; intros.
               specialize (abrel_match_mem_perms _ _ _ ofs k p0 H1 H5).
               destruct abrel_match_mem_perms as (NP & P).
               split; auto.
               red; intros. eapply Mem.perm_store_1; eauto.
            -- rewrite (Mem.nextblock_store _ _ _ _ _ _ HSnch); eauto.
    Qed.

  End LowHighSpecSim.

  (** ** Linking *)
  Section Linking.

    Context `{ce: ClightCompositeEnv}.
    Hypothesis Hce : build_composite_env (t_container_comp :: nil) = OK ce.

    Definition container_intro_L' : clayer container_intro_layerdata :=
      container_node_init_layer
      ⊕ container_get_quota_layer
      ⊕ container_get_usage_layer
      ⊕ container_get_parent_layer
      ⊕ container_get_nchildren_layer
      ⊕ container_set_usage_layer
      ⊕ container_set_nchildren_layer.

    Definition container_intro_Σ : clayer boot_layerdata :=
      container_node_init ↦ container_node_init_cprimitive
      ⊕ container_get_quota ↦ container_get_quota_cprimitive
      ⊕ container_get_usage ↦ container_get_usage_cprimitive
      ⊕ container_get_parent ↦ container_get_parent_cprimitive
      ⊕ container_get_nchildren ↦ container_get_nchildren_cprimitive
      ⊕ container_set_usage ↦ container_set_usage_cprimitive
      ⊕ container_set_nchildren ↦ container_set_nchildren_cprimitive.

    Definition container_intro_M : cmodule :=
      Minit
      ⊕ Mgquota
      ⊕ Mgusage
      ⊕ Mgparent
      ⊕ Mgnchild
      ⊕ Msusage
      ⊕ Msnchild.

    Hint Resolve container_node_init_code container_node_init_refine
                 container_get_quota_code container_get_quota_refine
                 container_get_usage_code container_get_usage_refine
                 container_get_parent_code container_get_parent_refine
                 container_get_nchildren_code container_get_nchildren_refine
                 container_set_usage_code container_set_usage_refine
                 container_set_nchildren_code container_set_nchildren_refine : linking.

    Theorem container_intro_link' :
      boot_L ⊢ (container_intro_R, container_intro_M) : container_intro_L'.
    Proof. link_tac container_intro_Σ. Qed.

    (** The [container_init] primitive in the Container layer will need to call
      [boot_init], so in order to expose it, we redefine it here as part of the
      ContainerIntro layer. *)
    Definition boot_init_high_sem' : cprimitive container_intro_layerdata :=
      cgensem container_intro_layerdata boot_init_high_spec.

    Global Instance boot_init_pres_inv :
      GenSemPreservesInvariant container_intro_layerdata boot_init_high_spec.
    Proof.
      split; auto.
      intros ? ? ? ? ? Hsem ? ?.
      inv_generic_sem Hsem.
      unfold boot_init_high_spec in H2.
      inv H2.
      constructor; cbn. discriminate.
    Qed.

    Definition boot_L' : clayer container_intro_layerdata := boot_init ↦ boot_init_high_sem'.

    Theorem boot_refine :
      boot_L ⊢ (container_intro_R, ∅) : boot_L'.
    Proof.
      refine_proof_tac.
      inv CStep. inv_generic_sem H8.
      inverse_hyps.
      inversion MemRel.
      inv abrel_match_mem_match.
      unfold boot_init_high_spec in H0. inv H0.
      do 3 eexists; split; repeat (econstructor; eauto).
    Qed.

    Hint Resolve container_intro_link' boot_refine : linking.

    Definition container_intro_L : clayer container_intro_layerdata :=
      container_intro_L' ⊕ boot_L'.

    Theorem container_intro_link :
      boot_L ⊢ (container_intro_R, container_intro_M) : container_intro_L.
    Proof.
      apply (vdash_module_le _ _ _ _ _ (container_intro_M ⊕ ∅)); [constructor | reflexivity |].
      apply hcomp_rule; auto with linking.
    Qed.

    Lemma container_intro_pres_inv :
      ForallPrimitive _ (CPrimitivePreservesInvariant _) container_intro_L.
    Proof.
      unfold container_intro_L, container_intro_L', boot_L'. typeclasses eauto.
    Qed.

  End Linking.

End ContainerIntro.
