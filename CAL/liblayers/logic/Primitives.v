Require Import LayerData.
Require Import Structures.
Require Import OptionMonad.
Require Import ErrorMonad.
Require Import OptionOrders.
Require Import PseudoJoin.

Section PRIMITIVES.
  Context `{VEops: CategoryOps}.

  Class PrimitiveOps (primsem: V -> Type) :=
    {
      prim_union v :> Oplus (primsem v)
    }.

  Class Primitives (primsem: V -> Type)
      `{primsem_ops: PrimitiveOps primsem}
      `{primsem_sim_op: Sim V E primsem} :=
    {
      prim_quiv_sim_prf :>
        CategorySim V E primsem;
      prim_union_join :>
        SimJoin V E primsem
    }.

  Global Instance prim_sim
      `{primsem_ops: PrimitiveOps}
      `{primsem_sim_op: Sim V E primsem}:
    Sim E _ :=
    {
      simRR v1 v2 e := res_le (option_le (sim e))
    }.

  Global Instance prim_sim_prf `{Hprim: Primitives}:
    CategorySim V E (fun v => res (option (primsem v))).
  Proof.
    split.
    - eapply cat_sim_cat; typeclasses eauto.
    - simpl; solve_monotonic.
    - simpl; typeclasses eauto.
    - typeclasses eauto.
  Qed.

  Context `{Hprim: Primitives}.

  Global Instance prim_oplus v: Oplus (res (option (primsem v))) :=
    {
      oplus p1 p2 :=
        match p1, p2 with
          | Error msg, _ => Error msg
          | _, Error msg => Error msg
          | _, OK None => p1
          | OK None, _ => p2
          | OK (Some σ1), OK (Some σ2) => OK (Some (σ1 ⊕ σ2))
        end
    }.

  Global Instance prim_oplus_isjoin:
    SimJoin V E (fun v => res (option (primsem v))) (Top := prim_oplus).
  Proof.
    split.
    - destruct x as [[x|]|], y as [[y|]|]; repeat constructor.
      + eapply hlub_ub_l.
      + reflexivity.
    - destruct x as [[x|]|], y as [[y|]|]; repeat constructor.
      + eapply hlub_ub_r.
      + reflexivity.
    - simpl in x, y.
      intros v' e z Hxz Hyz.
      destruct Hxz as [? ? Hxz' | ]; [ | constructor].
      inversion Hyz as [? ? Hyz' | ]; clear Hyz; subst.
      destruct Hxz' as [ | ? ? Hxz''];
      inversion Hyz'; clear Hyz'; subst;
      simpl; repeat constructor; eauto.
      eapply hlub_intro; eauto.
  Qed.

  Global Instance prim_oplus_id_left v:
    LeftIdentity eq (⊕) (OK (@None (primsem v))).
  Proof.
    intros [[|]|]; simpl; try reflexivity.
  Qed.

  Global Instance prim_oplus_id_right v:
    RightIdentity eq (⊕) (OK (@None (primsem v))).
  Proof.
    intros [[|]|]; simpl; try reflexivity.
  Qed.

  Global Instance prim_oplus_pjoin:
    SimPseudoJoin V E _ (Toplus := prim_oplus) (fun _ => OK None).
  Proof.
    eapply simjoin_pjoin; typeclasses eauto.
  Qed.
End PRIMITIVES.
