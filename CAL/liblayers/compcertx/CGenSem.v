Require Import AbstractData.
Require Export CPrimitives.
Require Export GenSem.
Require Import MemWithData.
Require Import SimrelDefinition SimValues SimrelLessdef SimrelInject.

Section WITHMEM.
  Context `{Hmem: BaseMemoryModel}.

  Inductive csemof  
            (D: layerdata) {T: Type}
            {targs tres}
            `{semof_ops: GenSem.Semof D T targs tres}
            (f: T): 
    csignature ->
    list val × mwd D -> val × mwd D -> Prop :=
  | csemof_intro args m d res d':
      forall csg,
      csg = {| csig_args := targs; csig_res := tres; csig_cc := AST.cc_default |} ->
      semof f args d res d' ->
      csemof D f csg (args, (m, d)) (res, (m, d')).

  Program
  Definition
    cgensem
    (D: layerdata) {T: Type}
    {targs tres}
    `{semof_ops: Semof D T targs tres}
    {semprops: Semprops T}
    (f: T): cprimitive D :=
    mkcprimitive D
      (csemof D f)
      {| csig_args := targs;
         csig_res  := tres;
         csig_cc   := AST.cc_default |}
      _.
  Next Obligation.
    inversion H; subst.
    eapply semprops_well_typed; eauto.
  Qed.

  Global Instance semprops_to_cprimitive_extcall_props
         {D: layerdata} {T targs tres} (f: T):
    forall (semof_ops: Semof D T targs tres)
           (semprops: Semprops T),
      CPrimitiveExtcallProperties D (cgensem D f).
  Proof.
    intros semof PROPS.
    inversion PROPS.
    constructor.
    + (* ec_mem_extends *)
      constructor; [ | unfold incl; simpl; eauto ].
      intros p sg [args1 [m1 d1]] [args2 [m2 d2]] .
      inversion 1; subst.
      simpl in H0.
      rewrite match_strong_extends_val in H0.
      assert (Val.lessdef_list args1 args2) as LESSDEF.
      {
        revert H0.
        clear.
        induction 1; auto.
      }
      intros [res1 [m1' d1']].
      inversion 1; subst.
      exploit semprops_lessdef; eauto.
      intro; subst.
      simpl in H1.
      exploit (strong_extends_elim (D:=D)); eauto.
      lift_simpl.
      destruct 1; subst.
      esplit.
      split.
      {
        econstructor; eauto.
      }
      assert (Mem.extends (m1', d1') (m2, d1')).
      {
        lift_simpl; auto.
      }
      edestruct (strong_extends_le_intro (D := D)) as [ ? [? ?]] ; eauto.
      {
        lift_simpl. apply Mem.unchanged_on_refl.
      }
      {
        lift_simpl. apply Mem.unchanged_on_refl.
      }        
      esplit.
      split; eauto.
      constructor; simpl.
      {
        rewrite match_strong_extends_val.
        reflexivity.
      }
      {
        lift_simpl; auto.
      }

    + (* ec_mem_inject *)
      constructor; [ | unfold incl; simpl; eauto ].
      intros p sg [args1 [m1 d1]] [args2 [m2 d2]] .
      inversion 1; subst.
      simpl in H0.
      rewrite match_val_strong_inject in H0.
      assert (Val.inject_list (simrel_inject_meminj (strong_inject_meminj p)) args1 args2) as INJECT.
      {
        revert H0.
        clear.
        induction 1; auto.
      }
      intros [res1 [m1' d1']].
      inversion 1; subst.
      exploit semprops_inject; eauto.
      intro; subst.
      simpl in H1.
      exploit (strong_inject_elim' (D := D)); eauto.
      intro INJ'.
      exploit (simrel_inject_match_mem_base (D := D)); eauto.
      lift_simpl.
      destruct 1; subst.
      esplit.
      split.
      {
        econstructor; eauto.
      }
      assert (Mem.inject (simrel_inject_meminj (strong_inject_meminj p)) (m1', d1') (m2, d1')) as INJ_POST.
      {
        lift_simpl; auto.
      }      
      edestruct (strong_inject_acc_intro (D := D)) as [ ? [? [? ?]]] ; eauto.
      {
        red. congruence.
      }
      {
        lift_simpl. apply Mem.unchanged_on_refl.
      }
      {
        lift_simpl. apply Mem.unchanged_on_refl.
      }        
      esplit.
      split; eauto.
      constructor; simpl.
      {
        rewrite match_val_strong_inject.
        eauto.
      }
      {
        lift_simpl; auto.
      }

    + (* determ_sg *)
      simpl. clear. intros. intuition congruence.

    + (* determ *)
      inversion 1; subst.
      inversion 1; subst.
      match goal with
          U: GenSem.semof _ _ _ _ _,
          V: GenSem.semof _ _ _ _ _
          |- _ =>
          generalize (semprops_determ _ _ _ _ _ _ _ U V)
      end.
      clear. intuition congruence.
  Qed.

  Class GenSemPreservesInvariant
        (D: layerdata) {T: Type}
        {targs tres}
        `{semof_ops: GenSem.Semof D T targs tres}
        (f: T)
    :=
      {
        gensem_preserves_invariant_data_inv args d res d' j:
          semof f args d res d' ->
          data_inject j d d ->
          data_inv d ->
          data_inv d';
        gensem_preserves_invariant_data_inject args d res d' j:
          semof f args d res d' ->
          data_inject j d d ->
          data_inv d ->
          data_inject j d' d'
      }.

  Global Instance gensem_to_cprimitive_preserves_invariant
         (D: layerdata) {T: Type}
         {targs tres}
         `{semof_ops: GenSem.Semof D T targs tres}
         {semprops: Semprops T}
         (f: T):
    GenSemPreservesInvariant D f ->
    CPrimitivePreservesInvariant D (cgensem D f).
  Proof.
    constructor; inversion 1; subst.
    + inversion 1; subst.
      split; auto.
      - eapply gensem_preserves_invariant_data_inv; eauto.
      - eapply gensem_preserves_invariant_data_inject; eauto.
      - eapply semprops_inject_neutral; eauto.
    + intros; reflexivity.
  Qed.

End WITHMEM.

Ltac inv_generic_sem H :=
  lazymatch type of H with

  (** FIXME: probably not the right number of arguments *)
  | external_call _ _ _ _ _ _ _ =>

    simpl in H;
    inv_generic_sem H

  | semof ?f _ _ _ _ =>

    unfold semof in H;
    inv_generic_sem H

  | semof_nil_void _ _ _ _ _ =>

    let f := fresh "f" in
    let d := fresh "d" in
    let d' := fresh "d'" in
    let Hfd := fresh "Hfd" in
    let Hf := fresh "Hf" in
    let Hargs := fresh "Hargs" in
    let Hd := fresh "Hd" in
    let Hv := fresh "Hv" in
    let Hd' := fresh "Hd'" in
    inversion H as [f d d' Hfd Hf Hargs Hd Hv Hd'];
    subst;
    clear H;
    rename Hfd into H;
    inv_generic_sem H

  | semof_nil_int _ _ _ _ _ =>

    let f := fresh "f" in
    let d := fresh "d" in
    let z := fresh "z" in
    let d' := fresh "d'" in
    let Hfd := fresh "Hfd" in
    let Hf := fresh "Hf" in
    let Hargs := fresh "Hargs" in
    let Hd := fresh "Hd" in
    let Hv := fresh "Hv" in
    let Hd' := fresh "Hd'" in
    inversion H as [f d z d' Hfd Hf Hargs Hd Hv Hd'];
    subst;
    clear H;
    rename Hfd into H;
    inv_generic_sem H

  | semof_nil_int_pure _ _ _ _ _ =>

    unfold semof_nil_int_pure in H;
    inv_generic_sem H

  | semof_nil_int_pure_total _ _ _ _ _ =>

    unfold semof_nil_int_pure_total in H;
    inv_generic_sem H

  | semof_cons _ _ _ _ _ =>

    let f := fresh "f" in
    let i := fresh "i" in
    let args := fresh "args" in
    let d := fresh "d" in
    let v := fresh "v" in
    let d' := fresh "d'" in
    let Hfd := fresh "Hfd" in
    let Hf := fresh "Hf" in
    let Hargs := fresh "Hargs" in
    let Hd := fresh "Hd" in
    let Hv := fresh "Hv" in
    let Hd' := fresh "Hd'" in
    inversion H as [f i args d v d' Hfd Hf Hargs Hd Hv Hd'];
    subst;
    clear H;
    rename Hfd into H;
    inv_generic_sem H

  | semof_nil_int64 _ _ _ _ _ =>

    let f := fresh "f" in
    let d := fresh "d" in
    let z := fresh "z" in
    let d' := fresh "d'" in
    let Hfd := fresh "Hfd" in
    let Hf := fresh "Hf" in
    let Hargs := fresh "Hargs" in
    let Hd := fresh "Hd" in
    let Hv := fresh "Hv" in
    let Hd' := fresh "Hd'" in
    inversion H as [f d z d' Hfd Hf Hargs Hd Hv Hd'];
    subst;
    clear H;
    rename Hfd into H;
    inv_generic_sem H

  | semof_nil_int64_pure _ _ _ _ _ =>

    unfold semof_nil_int64_pure in H;
    inv_generic_sem H

  | semof_nil_int64_pure_total _ _ _ _ _ =>

    unfold semof_nil_int64_pure_total in H;
    inv_generic_sem H

  | semof_cons64 _ _ _ _ _ =>

    let f := fresh "f" in
    let i := fresh "i" in
    let args := fresh "args" in
    let d := fresh "d" in
    let v := fresh "v" in
    let d' := fresh "d'" in
    let Hfd := fresh "Hfd" in
    let Hf := fresh "Hf" in
    let Hargs := fresh "Hargs" in
    let Hd := fresh "Hd" in
    let Hv := fresh "Hv" in
    let Hd' := fresh "Hd'" in
    inversion H as [f i args d v d' Hfd Hf Hargs Hd Hv Hd'];
    subst;
    clear H;
    rename Hfd into H;
    inv_generic_sem H

  (** When all else fail, fall back on more generic inversion
      tactics. This is useful not only as a base case, but sometimes
      we mix generic semantics with manually defined ones in a given
      layer, in which case it's more convenient if a single inversion
      tactic works and yield similar results for both kinds. *)

  | _ =>

    try (inv_monad H);
    try inv H

  end.