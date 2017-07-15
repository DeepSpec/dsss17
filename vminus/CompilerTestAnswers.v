Require Import List.
Import ListNotations.
Require Import String.
Require Import Arith.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.Stmon.
Require Import Vminus.Vminus.
Require Import Vminus.Atom.
Require Import Vminus.CFG.
Require Import Vminus.ListCFG.
Require Import Vminus.Imp.
Require Import Vminus.Compiler.

Require Import Vminus.ImpGen.
Require Import Vminus.VminusGen.
Require Import Vminus.OpSemGen.

Require Import Vminus.CompilerTest.
Require Import Vminus.VminusOpSem. (* More refactoring work to do *)
Import V.Opsem.


(**! Section test_compile_bexp extends compiler *)

(* Fatal error with stack overflow 
Definition comp_bop_correct_checker: Checker :=
  forAll arbitrary (fun (a1: aexp) =>
  forAll arbitrary (fun (a2: aexp) =>
  forAll arbitrary (fun (binop: bop) => 
    collect (binop, a1, a2) (comp_correct_checker 
      (comp_bop binop (comp_aexp a1) (comp_aexp a2))
      (fun m => V.Opsem.bop_denote binop (aeval a1 m) (aeval a2 m)))))).
 *)

Definition comp_bop_correct_checker: Checker :=
  forAll arbitrary (fun (a1: aexp) =>
  forAll arbitrary (fun (a2: aexp) =>
  forAll arbitrary (fun (binop: bop) => 
    collect binop (comp_correct_checker 
      (comp_bop binop (comp_aexp a1) (comp_aexp a2))
      (fun m => V.Opsem.bop_denote binop (aeval a1 m) (aeval a2 m)))))).

(* ! QuickChick comp_bop_correct_checker. *)

Definition comp_bexp_correct_checker : Checker :=
  forAll arbitrary (fun b: bexp => 
    comp_correct_checker (comp_bexp b) (fun m => if (beval b m) then 1 else 0)).

(* ! QuickChick comp_bexp_correct_checker. *)

(** Exercise: Now write a checker for the following.

Lemma comp_store_correct : 
  forall g a v le lr cs st,
  insns_at_pc g (block_entry le) (steval (comp_store a v lr) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = (block_entry lr) /\
    st_mem st' = (Memory.update (st_mem st) v (aeval a (st_mem st))).
*)

(*
Definition comp_store_correct_checker_inner'
           (a : aexp) (v: addr) (lr le: lbl) (cs: list uid)
           (vst: vminus_state)
  : Checker :=
  let st := V.Opsem.mkst (vst_mem vst) (block_entry le) (vst_loc vst)
                         (vst_ppc vst) (vst_ploc vst) in
  let vst := mk_vminus_state
               (vst_mem vst) (vst_mem_dom vst)
               (block_entry le)
               (vst_loc vst) (vst_loc_dom vst)
               (vst_ppc vst)
               (vst_ploc vst) (vst_ploc_dom vst) in
  let '(g, end_pc) :=
      wrap_code_in_cfg (block_entry le)
                       (Stmon.steval (comp_store a v lr) cs) [] in
  match (V.Opsem.eval_once_and_until_pc g st (block_entry lr) 1000) with
  | inl err => whenFail ("comp_store_correct: " ++ err) false
  | inr st' =>
    if (eq_dec_pc (V.Opsem.st_pc st') (block_entry lr)) then
      let new_dom := (v :: vst_mem_dom vst) in
      whenFail ("::: cfg is: " ++ show g ++
                " ::: initial state pc: " ++ show (vst_pc vst) ++
                " ::: le: " ++ show le ++ 
                " ::: lr: " ++ show lr ++
                " ::: store to " ++ show v ++
                " ::: curr pc: " ++ show (block_entry lr) ++
                " ::: final memory: " ++
                show_memory (V.Opsem.st_mem st') new_dom ++
                " ::: initial memory: " ++
                show_memory (V.Opsem.st_mem st) new_dom)
        (memory_on_domain_checker new_dom
          (V.Opsem.st_mem st')
          (V.Opsem.Memory.update (V.Opsem.st_mem st) v
                                 (aeval a (V.Opsem.st_mem st))))
    else whenFail "comp_store_correct: pc not expected" false
  end.
 *)

(*
Definition comp_store_correct_checker_inner
           (a : aexp) (v: addr) (lr le: lbl) (cs: list uid)
           (vst: vminus_state)
  : Checker :=
  let st := V.Opsem.mkst (vst_mem vst) (block_entry le) (vst_loc vst)
                         (vst_ppc vst) (vst_ploc vst) in
  let '(g, end_pc) :=
      wrap_code_in_cfg (block_entry le)
                       (steval (comp_store a v lr) cs) [] in
  match (V.Opsem.eval_once_and_until_pc g st (block_entry lr) 1000) with
  | inl err => whenFail ("comp_store_correct: " ++ err) false
  | inr st' =>
    if (eq_dec_pc (V.Opsem.st_pc st') (block_entry lr)) then
      let new_dom := (v :: vst_mem_dom vst) in
      whenFail 
        "comp_store_correct: memories mismatch"
        (memory_on_domain_checker new_dom
          (V.Opsem.st_mem st')
          (V.Opsem.Memory.update (V.Opsem.st_mem st) v
                                 (aeval a (V.Opsem.st_mem st))))
    else whenFail "comp_store_correct: pc not expected" false
  end.

Definition comp_store_correct_checker: Checker :=
  forAll arbitrary (fun (a: aexp) =>
  forAll arbitrary (fun (v: addr) =>
  forAll arbitrary (fun (lr: lbl) =>
  forAll arbitrary (fun (le: lbl) =>
  forAll arbitrary (fun (cs: list uid) =>
  forAll arbitrary (fun (vst: vminus_state) =>
    comp_store_correct_checker_inner a v lr le cs vst)))))).

(* ! QuickChick comp_store_correct_checker. *)


Definition comp_cond_correct_checker_inner
           (b: bexp) (cs: list uid) (le l1 l2: lbl)
           (vst: vminus_state)
  : Checker :=
  let st := V.Opsem.mkst (vst_mem vst) (block_entry le) (vst_loc vst)
                         (vst_ppc vst) (vst_ploc vst) in
  let '(g, end_pc) :=
      wrap_code_in_cfg (block_entry le)
                       (Stmon.steval (comp_cond b l1 l2) cs) [] in
  let l := (if beval b (V.Opsem.st_mem st) then l1 else l2) in  
  match (V.Opsem.eval_until_pc g st (block_entry l) 1000) with
  | inl err =>
    whenFail 
      ("::: cfg is: " ++ show g ++
       "::: comp_cond_correct: " ++ err ++
       "::: looking for pc: " ++ show end_pc
      )
      false
  | inr st' =>
    if (eq_dec_pc (V.Opsem.st_pc st') (block_entry l)) then 
      whenFail "comp_store_correct: memories mismatch"
               (memory_on_domain_checker (vst_mem_dom vst)
                                         (V.Opsem.st_mem st)
                                         (V.Opsem.st_mem st'))
    else whenFail "comp_cond_correct: pc not expected" false
  end.

Definition comp_cond_correct_checker : Checker :=
  forAll arbitrary (fun (b: bexp) =>
  forAll arbitrary (fun (le: lbl) =>
  forAll arbitrary (fun (l1: lbl) =>
  forAll arbitrary (fun (l2: lbl) =>
  forAll arbitrary (fun (cs: list uid) =>
  forAll arbitrary (fun (vst: vminus_state) =>
    comp_cond_correct_checker_inner b cs le l1 l2 vst)))))).

(* ! QuickChick comp_cond_correct_checker. *)

*)

(** *** NOT DONE 
Definition match_config_checker
           (c: Imp.com) ((g, l1 l2): cfg * lbl * lbl)
  : Checker :=
  match c with
  | SKIP => whenFail "match_config: labels not equal for skip"
                    (eq_dec_lbl l1 l2)
  | 


Inductive match_config : Imp.com -> (cfg * lbl * lbl) -> Prop :=
  | MC_Skip : forall bs l,
      match_config SKIP (bs, l, l)
  | MC_Ass : forall g l l' uid a cs,
      insns_at_pc g (block_entry l) (steval (comp_store a uid l') cs) ->
      match_config (CAss uid a) (g, l, l')
  | MC_Seq : forall g l1 l2 l3 c1 c2,
      match_config c1 (g, l1, l2) ->
      match_config c2 (g, l2, l3) ->
      match_config (CSeq c1 c2) (g, l1, l3)
  | MC_If : forall g le lr l1 l2 b c1 c2 cs,
      match_config c1 (g, l1, lr) ->
      match_config c2 (g, l2, lr) ->
      insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
      match_config (CIf b c1 c2) (g, le, lr)
  | MC_While : forall g le lb lr b c cs,
      match_config c (g, lb, le) ->
      insns_at_pc g (block_entry le) (steval (comp_cond b lb lr) cs) ->
      match_config (CWhile b c) (g, le, lr).

Inductive match_config : Imp.com -> (ListCFG.t * lbl * lbl) -> Prop :=
  | MC_Skip : forall bs l,
      match_config SKIP (bs, l, l)
  | MC_Ass : forall g l l' uid a cs,
      insns_at_pc g (block_entry l) (steval (comp_store a uid l') cs) ->
      match_config (CAss uid a) (g, l, l')
  | MC_Seq : forall g l1 l2 l3 c1 c2,
      match_config c1 (g, l1, l2) ->
      match_config c2 (g, l2, l3) ->
      match_config (CSeq c1 c2) (g, l1, l3)
  | MC_If : forall g le lr l1 l2 b c1 c2 cs,
      match_config c1 (g, l1, lr) ->
      match_config c2 (g, l2, lr) ->
      insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
      match_config (CIf b c1 c2) (g, le, lr)
  | MC_While : forall g le lb lr b c cs,
      match_config c (g, lb, le) ->
      insns_at_pc g (block_entry le) (steval (comp_cond b lb lr) cs) ->
      match_config (CWhile b c) (g, le, lr).

Inductive match_states (g:cfg) (r:lbl)
  : (com * Imp.state) -> Opsem.state -> Prop :=
  match_states_intro : forall c mem st l,
    match_config c (g, l, r) ->
    st_pc st = block_entry l ->
    st_mem st = mem ->
    match_states g r (c, mem) st.

Lemma simulation_step' :
  forall g c c' mem mem' st r,
  Imp.step (c, mem) (c', mem') ->
  match_states g r (c, mem) st ->
  exists st',
    star (Opsem.step g) st st' /\
    match_states g r (c', mem') st'.

Lemma simulation_step' :
  forall c mem mem' st r,
  let '(c', mem') := Imp.step (c, mem) in
  

  match_states g r (c, mem) st ->
  exists st',
    star (Opsem.step g) st st' /\
    match_states g r (c', mem') st'.

Lemma transl_sim_step_final :
  forall g r imp_st imp_st' vmn_st,
  Imp.step imp_st imp_st' ->
  match_states g r imp_st vmn_st ->
  exists vmn_st',
    (plus (Opsem.step g) vmn_st vmn_st' \/
     star (Opsem.step g) vmn_st vmn_st' /\ imp_size imp_st' < imp_size imp_st) /\
    match_states g r imp_st' vmn_st'.
*)