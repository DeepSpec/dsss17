Require Export SimrelDefinition.
Require Export InitMemRel.

Section SIMREL_INIT_MEM.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2: layerdata}.
  Context {F1 F2 V: Type}.

  Definition simrel_newfun_ok ng b (i: ident) :=
    b = true /\ simrel_not_new_glbl ng i.

  Class InitMemSimrel ng b (RM: _ -> _ -> _ -> _ -> rel (mwd D1) (mwd D2)) :=
    {
      (** Starting point *)
      initmem_simrel_empty :>
        Monotonic Mem.empty (RM 1%positive nil 0 0);

      (** No definition *)
      initmem_simrel_none i:
        simrel_not_new_glbl ng i ->
        Monotonic 
          alloc_none
          (RM i nil 0 0 ++> option_le (RM (Pos.succ i) nil 0 0));

      (** New function *)
      initmem_simrel_none_fun i:
        simrel_newfun_ok ng b i ->
        Related
          alloc_none
          alloc_fun
          (RM i nil 0 0 ++> option_le (RM (Pos.succ i) nil 0 0));

      (** New variable *)
      initmem_simrel_none_var i (v: globvar V):
        simrel_newvar_ok ng b i (gvar_init v) ->
        Genv.init_data_list_valid find_symbol 0 (gvar_init v) = true ->
        InitMemNewVariableProps
          (simrel_fundef_rel (F1:=F1) (F2:=F2) b)
          (simrel_vardef_rel (V:=V) ng b)
          RM i v;

      (** Both functions *)
      initmem_simrel_fun i:
        Monotonic
          alloc_fun
          (RM i nil 0 0 ++> option_le (RM (Pos.succ i) nil 0 0));

      (** Both variables *)
      initmem_simrel_var i (v: globvar V):
        simrel_not_new_glbl ng i ->
        InitMemVariableProps
          (simrel_fundef_rel (F1:=F1) (F2:=F2) b)
          (simrel_vardef_rel (V:=V) ng b)
          RM i v v
    }.

  Global Instance initmem_simrel_rel ng b RM:
    InitMemSimrel ng b RM ->
    InitMemRelations
      (simrel_fundef_rel (F1:=F1) (F2:=F2) b)
      (simrel_vardef_rel (V:=V) ng b)
      RM.
  Proof.
    assert
      (forall i,
         simrel_vardef_rel (V:=V) ng b i None None ->
         simrel_not_new_glbl ng i)
      as Hvar_none.
    {
      intros i Hi.
      inversion Hi.
      assumption.
    } 

    assert
      (forall i f2,
         simrel_fundef_rel (F1:=F1) (F2:=F2) b i None (Some f2) ->
         simrel_vardef_rel (V:=V) ng b i None None ->
         simrel_newfun_ok ng b i)
      as Hnew_fun.
    {
      intros i f2 Hf Hv.
      red.
      inversion Hf; clear Hf; subst.
      inversion Hv; clear Hv; subst.
      eauto.
    }

    assert
      (forall i v,
         simrel_fundef_rel (F1:=F1) (F2:=F2) b i None None ->
         simrel_vardef_rel (V:=V) ng b i None (Some v) ->
         simrel_newvar_ok ng b i (gvar_init v))
      as Hnew_var.
    {
      intros i v Hf Hv.
      red.
      inversion Hv; clear Hv; subst; eauto.
    }

    assert
      (forall i v,
         simrel_fundef_rel (F1:=F1) (F2:=F2) b i None None ->
         simrel_vardef_rel (V:=V) ng b i None (Some v) ->
         Genv.init_data_list_valid find_symbol 0 (gvar_init v) = true)
      as Hnew_var'.
    {
      intros i v Hf Hv.
      inversion Hv; clear Hv; subst; eauto.
    }

    assert
      (forall i v1 v2,
         simrel_vardef_rel (V:=V) ng b i (Some v1) (Some v2) ->
         v1 = v2)
      as Hvar_eq.
    {
      intros i v1 v2 Hv.
      inversion Hv.
      reflexivity.
    }

    assert
      (forall i v1 v2,
         simrel_vardef_rel (V:=V) ng b i (Some v1) (Some v2) ->
         simrel_not_new_glbl ng i)
      as Hvar.
    {
      intros i v1 v2 Hv.
      inversion Hv; eauto.
    }

    intros H.
    destruct H.
    split; intros; eauto.
    - intros f1 f2 Hf.
      destruct Hf; congruence.
    - intros v1 v2 Hv.
      destruct Hv as [ | | ]; congruence.
    - assert (v1 = v2) by eauto; subst; eauto.
  Qed.

  Global Instance genv_init_mem_simrel_withnextblock R RM:
    InitMemSimrel
      (simrel_new_glbl R)
      (simrel_undef_matches_values_bool R)
      RM ->
    subrel
      (RM glob_threshold nil 0 0 /\ req glob_threshold @@ Mem.nextblock)
      (rexists w, match_mem R w) ->
    Monotonic
      (Genv.init_mem (F:=_) (V:=V))
      (simrel_program_rel (F1:=F1) (F2:=F2) R ++>
       option_le ((rexists w, match_mem R w) /\
                  (req glob_threshold @@ Mem.nextblock))).
  Proof.
    intros HR HRM.
    solve_monotonic.
  Qed.

  Lemma genv_init_mem_simrel R RM:
    InitMemSimrel
      (simrel_new_glbl R)
      (simrel_undef_matches_values_bool R)
      RM ->
    subrel
      (RM glob_threshold nil 0 0 /\ req glob_threshold @@ Mem.nextblock)
      (rexists w, match_mem R w) ->
    Monotonic
      (Genv.init_mem (F:=_) (V:=V))
      (simrel_program_rel (F1:=F1) (F2:=F2) R ++>
       option_le (rexists w, match_mem R w)).
  Proof.
    intros HR HRM.
    solve_monotonic.
  Qed.
End SIMREL_INIT_MEM.
