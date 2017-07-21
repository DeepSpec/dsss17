Require Export compcert.lib.Coqlib.
Require Export compcert.common.Values.
Require Export compcert.common.AST.
Require Export compcert.common.Globalenvs.
Require Export liblayers.lib.OptionMonad.
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.Semantics. (* for noconflict *)
Require Export liblayers.compcertx.CompcertStructures.
Require Export liblayers.compcertx.ErrorMonad.


(** * Prerequisites *)
 
(** The class below specifies the prerequisites for our implementation
  of [MakeProgram]. Basically, we need to know how to convert the
  definition in modules and layers into Compcert program definitions.

  Note that the types of function and variable definitions in the
  produced program are not always related to the types of definitions
  in our modules and layers. For instance, in order to be able to use
  our layers to construct C as well as assembly programs, their global
  variable definitions need to store C-style typing information. When
  building assembly programs they will be converted into low-level
  types. Hence, we need to distinguish between to output program types
  [Fp] and [Vp], and the types used in the module and layer [Fm] and [Vm].

  Another difficulty that arises because of the discrepency between
  our view and Compcert's is related to what a function definitions is:
  Compcert's internal functions correspond to functions defined in our
  modules, whereas external functions correspond to the primitives
  defined in layer interfaces. 

  In our case, 

 *)

Class ProgramFormatOps {layerdata} (Fm Vm Fp Vp: Type)
    {module: Type}
    `{layer_ops: LayerOps layerdata AST.ident (V := AST.globvar Vm)}
    {module_ops: ModuleOps AST.ident Fm (AST.globvar Vm) module}
 :=
  {
    make_internal: Fm -> res Fp;
    make_external D: AST.ident -> primsem D -> res Fp;
    make_varinfo: globvar Vm -> res (globvar Vp)
  }.

Class ProgramFormat {layerdata simrel} Fm Vm Fp Vp
  `{pf_ops: ProgramFormatOps layerdata Fm Vm Fp Vp}
  `{rg_ops: !CategoryOps layerdata simrel}
  `{psim_ops: Sim layerdata simrel primsem}
  `{lsim_ops: Sim layerdata simrel layer} :=
  {
    make_external_monotonic {D} :>
    Monotonic (make_external D) (eq ==> (≤) ++> res_le eq)
  }.

(** Often used when defining [make_varinfo] *)
Definition globvar_map {Vm Vp} (f: Vm -> Vp) gt :=
  {|
    AST.gvar_info := f (AST.gvar_info gt);
    AST.gvar_init := AST.gvar_init gt;
    AST.gvar_readonly := AST.gvar_readonly gt;
    AST.gvar_volatile := AST.gvar_volatile gt
  |}.


(** * Relations *)

(** The most important property of [make_program] takes the form a
  relational parametricity theorem: module-layer pairs that are
  related in a given way will yield programs that are related in a
  corresponding way. The devil is in the details of what we by
  "related in a given way" and "related in a corresponding way".

  If fact, we will use general specifications of how function
  definitions are to be related. From a relation this kind ([funrel]),
  we will derive both a relation on module-layer pairs (using
  [module_layer_rel] defined below), and a relation on programs
  (using an appropriate parameter for [program_le]).

  The first step is to define some accessors for handling module-layer
  pairs as a whole. *)

Section MODULE_LAYER_ACCESS.
  Context `{Hpf: ProgramFormat}.

  Definition res_option_inj {A B} (x: res (option A)) (y: res (option B)):
    res (option (A + B)) :=
    match x, y with
      | OK None, OK None => OK None
      | OK (Some a), OK None => OK (Some (inl a))
      | OK None, OK (Some b) => OK (Some (inr b))
      | _, _ => Error nil
    end.

  Definition get_module_layer_function {D} i (ML: module * layer D) :=
    res_option_inj
      (get_module_function i (fst ML))
      (get_layer_primitive i (snd ML)).

  Definition get_module_layer_variable {D} i (ML: module * layer D) :=
      (get_module_variable i (fst ML)) ⊕
      (get_layer_globalvar i (snd ML)).
End MODULE_LAYER_ACCESS.

(** Those should be moved to coqrel? *)

Class OptionRelationForward {A B} (R: rel (option A) (option B)) :=
  option_rel_fw x y: R x y -> y = None -> x = None.

Class HasImage {A1 A2 B1 B2} (RA: rel A1 A2) (π1: rel A1 B1) (π2: rel A2 B2) (RB: rel B1 B2) :=
  has_image: (π1 ++> π2 ++> impl)%rel RA RB.

Inductive rel_proj {A1 B1} (π1: rel A1 B1) {A2 B2} (π2: rel A2 B2) (R: rel A1 A2): rel B1 B2 :=
  rel_proj_intro:
    HasImage R π1 π2 (rel_proj π1 π2 R).

Global Existing Instance rel_proj_intro.

Global Instance rel_proj_rel:
  Monotonic
    (@rel_proj)
    (forallr -, forallr -, subrel ++>
     forallr -, forallr -, subrel ++> subrel ++> subrel).
Proof.
  clear.
  intros A1 A2 R R' HR B1 B2 π1 π1' Hπ1 π2 π2' Hπ2 x yi Hxy.
  destruct Hxy.
  econstructor; eauto.
Qed.

Lemma rel_proj_fw {A1 B1 A2 B2} R π1 π2:
  @OptionRelationForward A1 B1 R ->
  @OptionRelationForward A2 B2 (rel_proj (option_rel π1) (option_rel π2) R).
Proof.
  intros HR.
  intros a2 b2 H2 Hb2.
  destruct H2 as [a1 a2 Ha b1 b2 Hb H1].
  destruct Ha as [a1 a2 Ha|]; eauto.
  destruct Hb as [b1 b2 Hb|]; try discriminate.
  eapply option_rel_fw in H1; eauto.
  discriminate.
Qed.

Hint Extern 1 (OptionRelationForward (rel_proj _ _ _)) =>
  eapply rel_proj_fw : typeclass_instances.

Section RELATIONS.
  Context {ld1 Fm1 Vm1 Fp1 Vp1 module1 primsem1 layer1}
    `{pf_ops1: ProgramFormatOps ld1 Fm1 Vm1 Fp1 Vp1 module1 primsem1 layer1}.
  Context {ld2 Fm2 Vm2 Fp2 Vp2 module2 primsem2 layer2}
    `{pf_ops2: ProgramFormatOps ld2 Fm2 Vm2 Fp2 Vp2 module2 primsem2 layer2}.

  (** A function definition can either be an internal definition as
    found in modules (given by the type parameter [Fm] in
    [ProgramFormatOps]) or an external definition corresponding to a
    primitive specification (of the type [primsem]). We allow the user
    to specify a different relation at each identifier, which means we
    can have a fairly precise [funrel]. *)

  Definition funrel
      `{pf_ops1: !ProgramFormatOps Fm1 Vm1 Fp1 Vp1}
      `{pf_ops2: !ProgramFormatOps Fm2 Vm2 Fp2 Vp2}
    D1 D2 :=
      ident ->
      rel (option (Fm1 + primsem1 D1)%type) (option (Fm2 + primsem2 D2))%type.

  Definition varrel
      `{pf_ops1: !ProgramFormatOps Fm1 Vm1 Fp1 Vp1}
      `{pf_ops2: !ProgramFormatOps Fm2 Vm2 Fp2 Vp2}
    :=
      ident ->
      rel (option (globvar Vm1)) (option (globvar Vm2)).

  (** From such a relation (family) [Rf : funrel D1 D2], we can derive
    the corresponding relation on module-layer pairs,
    [module_layer_rel D1 D2 Rf]. *)

  Definition module_layer_rel D1 D2 (RF: funrel D1 D2) (RV: varrel):
    rel (module1 × layer1 D1)%type (module2 × layer2 D2)%type :=
    fun ML1 ML2 =>
      forall i,
        (res_le (RF i))
          (get_module_layer_function i ML1)
          (get_module_layer_function i ML2) /\
        (res_le (RV i))
          (get_module_layer_variable i ML1)
          (get_module_layer_variable i ML2).

  Global Instance get_module_layer_function_rel D1 D2 RF RV i:
    Monotonic
      (get_module_layer_function i)
      (module_layer_rel D1 D2 RF RV ++> res_le (RF i)).
  Proof.
    firstorder.
  Qed.

  Global Instance get_module_layer_function_rel_params:
    Params (@get_module_layer_function) 1.

  Global Instance get_module_layer_variable_rel D1 D2 RF RV i:
    Monotonic
      (get_module_layer_variable i)
      (module_layer_rel D1 D2 RF RV ++> res_le (RV i)).
  Proof.
    firstorder.
  Qed.

  Global Instance get_module_layer_variable_rel_params:
    Params (@get_module_layer_variable) 1.

  (** We can also derive a relation on program definitions, this time
    indexed by blocks, suitable for [program_le] or [genv_le]. *)

  Definition make_fundef `{ProgramFormatOps} D i (d: Fm + primsem D): res Fp :=
    match d with
      | inl fi => make_internal fi
      | inr fe => make_external D i fe
    end.

  Definition match_fundef `{ProgramFormatOps} D i d d' :=
    make_fundef D i d = OK d'.

  Definition match_vardef `{ProgramFormatOps} d d' :=
    make_varinfo d = OK d'.

  (** While we can use a wide range of [funrel] and [varrel] to encode
    different situations, we do have some restrictions. In particular,
    adding more definitions may trigger an error condition, which is
    only allowed by [res_le] to appear on the right, or both
    sides. Hence, while we allow [None] on the left to be related to
    [Some] on the right, we use [OptionRelationForward] to forbid the
    opposite situation.

    Then, we require that the relations on programs contain the image
    of the relations on modules as defined using [match_fundef] and
    [match_vardef]. *)

  Class MakeProgramRelations D1 D2 RFm RVm RFp RVp :=
    {
      make_program_function_relation_fw i :>
        OptionRelationForward (RFm i);
      make_program_variable_relation_fw i :>
        OptionRelationForward (RVm i);
      make_program_function_relations i :>
        HasImage
          (RFm i)
          (option_rel (match_fundef (Fm:=Fm1) D1 i))
          (option_rel (match_fundef (Fm:=Fm2) D2 i))
          (RFp i);
      make_program_variable_relations (i: ident) :>
        HasImage
          (RVm i)
          (option_rel (match_vardef (Vm:=Vm1)))
          (option_rel (match_vardef (Vm:=Vm2)))
          (RVp i);
      make_fundef_error i:
        Monotonic
          (make_fundef _ i)
          (RFm i @@ Some ++> impl @@ isError);
      make_vardef_error i:
        Monotonic
          make_varinfo
          (RVm i @@ Some ++> impl @@ isError);
    }.

  (** One specific way to construct relations which satisfy the
    [HasImage] constraints above is to simply use [rel_proj] to
    compute the image in question. *)

  Definition fundef_rel D1 D2 (RF: funrel D1 D2) i: rel (option _) (option _) :=
    rel_proj
      (option_rel (match_fundef D1 i))
      (option_rel (match_fundef D2 i))
      (RF i).

  Definition vardef_rel (RV: varrel) i: rel (option _) (option _) :=
    rel_proj
      (option_rel match_vardef)
      (option_rel match_vardef)
      (RV i).

  (** Establishing [MakeProgramRelations] then boils down to proving
    the [OptionRelationForward] conditions. *)

  Instance foodef_rel_mpr D1 D2 RFm RVm:
    (forall i, OptionRelationForward (RFm i)) ->
    (forall i, OptionRelationForward (RVm i)) ->
    (forall i, Monotonic (make_fundef _ i) (RFm i @@ Some ++> impl @@ isError)) ->
    (forall i, Monotonic make_varinfo (RVm i @@ Some ++> impl @@ isError)) ->
    MakeProgramRelations D1 D2 RFm RVm (fundef_rel D1 D2 RFm) (vardef_rel RVm).
  Proof.
    intros HRFm HRVm.
    split; first [ typeclasses eauto | eauto ].
  Qed.
End RELATIONS.

Hint Extern 2 (MakeProgramRelations _ _ _ _ (fundef_rel _ _ _) (vardef_rel _)) =>
  eapply foodef_rel_mpr : typeclass_instances.

(** * Specification of [make_program] *)

(** From and instance of [ProgramFormatOps] and a module-layer pair,
  [make_program] attempts to build a Compcert program. We also define
  the compound [make_globalenv], which builds a Compcert global
  environment from the program in quesion. *)

Class MakeProgramOps :=
  {
    make_program `{ProgramFormatOps} D: module * layer D -> res (program Fp Vp)
  }.

Definition make_globalenv `{MakeProgramOps} `{ProgramFormatOps} D ML :=
  p <- make_program D ML;
  ret (Genv.globalenv p).

(** For most part, the specification of [make_program] consists in a
  relational parametricity property expressed using the relations
  defined above. We also use the following inductive type to express
  the property that if [make_program] succeeds, then there should have
  been no conflict between the function and variables in the module
  and layer. *)

(** We are now ready to give the specification of [make_program]. *)

Class MakeProgram `{mkp_ops: MakeProgramOps} :=
  {
    make_program_rel `(MakeProgramRelations) :>
      Monotonic
        (make_program _)
        (module_layer_rel D1 D2 RFm RVm ++> res_le (program_rel RFp RVp));

    make_program_noconflict `{ProgramFormatOps} D M L p i:
      make_program D (M, L) = OK p ->
      noconflict
        (get_module_function i M)
        (get_module_variable i M)
        (get_layer_primitive i L)
        (get_layer_globalvar i L);

    make_program_public_incl `{ProgramFormatOps} D M L p:
      make_program D (M, L) = OK p ->
      incl (AST.prog_public p) (map fst (AST.prog_defs p));

    make_program_public_eq `{ProgramFormatOps} D1 D2 M1 M2 L1 L2 p1 p2:
      make_program D1 (M1, L1) = OK p1 ->
      make_program D2 (M2, L2) = OK p2 ->
      AST.prog_public p1 = AST.prog_public p2
  }.

Global Instance make_program_rel_params:
  Params (@make_program) 1.

Global Instance make_globalenv_rel `{MakeProgram} `(MakeProgramRelations):
  Monotonic
    (make_globalenv _)
    (module_layer_rel D1 D2 RFm RVm ++> res_le (genv_rel RFp RVp)).
Proof.
  unfold make_globalenv.
  rauto.
Qed.

Global Instance make_globalenv_rel_params:
  Params (@make_globalenv) 1.

(** We can also introduce variants of the relational property based on
  [program_le] and [genv_le], which are less general but more
  convenient to use in many contexts. *)

Definition module_layer_le `{ProgramFormatOps} D1 D2 RF :=
  module_layer_rel D1 D2 (fun i => option_le (RF i)) (fun i => option_le eq).

Definition fundef_le `{ProgramFormatOps} D1 D2 RF :=
  fun i => rel_proj (match_fundef D1 i) (match_fundef D2 i) (RF i).

Instance option_le_has_image {A1 B1} (π1: rel A1 B1) {A2 B2} (π2: rel A2 B2) R R':
  HasImage R π1 π2 R' ->
  HasImage (option_le R) (option_rel π1) (option_rel π2) (option_le R').
Proof.
  intros H x1 y1 H1 x2 y2 H2 Hx.
  destruct H1, H2; inversion Hx; constructor.
  eapply has_image; eauto.
Qed.

Global Instance option_le_fw {A B} (R: rel A B):
  OptionRelationForward (option_le R).
Proof.
  intros ? ? [x | x y Hxy];
  congruence.
Qed.

(** We're careful not to register these instances of [MakeProgramRelations]
  too widely because otherwise it's used for solving [ident ->
  OptionRelationForward (option_le eq)] and leave us with
  uninstantiated evars as a result. *)

Local Instance option_le_mpr `{Hpf: ProgramFormat} D1 D2 RFm RFp:
  (forall i, HasImage (RFm i) (match_fundef D1 i) (match_fundef D2 i) (RFp i)) ->
  (forall i, Monotonic (make_fundef _ i) (RFm i ++> impl @@ isError)) ->
  MakeProgramRelations D1 D2
    (fun i => option_le (RFm i))
    (fun i => option_le eq)
    (fun i => option_le (RFp i))
    (fun i => option_le eq).
Proof.
  intros Himg Herr.
  split; try typeclasses eauto.
  - intros i v1m v1p Hv1 v2m v2p Hv2 Hvm.
    destruct Hv1, Hv2; inversion Hvm; constructor; congruence.
  - intros i f1 f2 Hf.
    inversion Hf as [ | xf1 xf2 Hf']; clear Hf; subst.
    eapply Herr; eauto.
  - intros i v1 v2 Hv.
    inversion Hv; clear Hv; subst.
    reflexivity.
Qed.

Local Instance fundef_le_mpr `{Hpf: ProgramFormat} D1 D2 RFm:
  (forall i, Monotonic (make_fundef _ i) (RFm i ++> impl @@ isError)) ->
  MakeProgramRelations D1 D2
    (fun i => option_le (RFm i))
    (fun i => option_le eq)
    (fun i => option_le (fundef_le D1 D2 RFm i))
    (fun i => option_le eq).
Proof.
  typeclasses eauto.
Qed.

Global Instance make_program_le `{Hmkp: MakeProgram} `{Hpf: ProgramFormat}:
  forall D1 D2 (RFm: ident -> (rel (Fm + primsem D1) (Fm + primsem D2))%type) RFp,
    (forall i, HasImage (RFm i) (match_fundef D1 i) (match_fundef D2 i) (RFp i)) ->
    (forall i, Monotonic (make_fundef _ i) (RFm i ++> impl @@ isError)) ->
    Monotonic
      (make_program _)
      (module_layer_le D1 D2 RFm ++> res_le (program_le RFp)).
Proof.
  intros D1 D2 RFm RFp HRF HRFerr ML1 ML2 HML.
  unfold program_le.
  solve_monotonic.
Qed.

Global Instance make_globalenv_le `{MakeProgram} `{ProgramFormat} {D1 D2}:
  forall {RFm: ident -> (rel (Fm + primsem D1) (Fm + primsem D2))%type} {RFp}
    `{forall i, HasImage (RFm i) (match_fundef D1 i) (match_fundef D2 i) (RFp i)}
    `{forall i, Monotonic (make_fundef _ i) (RFm i ++> impl @@ isError)},
  Monotonic
    (make_globalenv _)
    (module_layer_le D1 D2 RFm ++> res_le (genv_le RFp)).
Proof.
  intros.
  unfold make_globalenv.
  rauto.
Qed.
