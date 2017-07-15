Require Import List.
Import ListNotations.
Require Import String.
Require Import Arith.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.Classes.
Require Import Vminus.Vminus.
Require Import Vminus.Atom.
Require Import Vminus.CFG.
Require Import Vminus.ListCFG.
Require Import Vminus.Imp.
Require Import Vminus.Compiler.
Require Import Vminus.VminusOpSem. (* More refactoring work to do *)
Import V.Opsem.

(* Exercise imports *)
Require Import Vminus.AtomGen.
Require Import Vminus.ImpGen.
Require Import Vminus.OpSemGen.
Require Import Vminus.Stmon.

(** ** QuickChick and Vellvm **************************************************)
(** One may expect a compiler for a language as simple as IMP to be relatively 
    straightforward, and a proof of its correctness to be correspondingly
    so. However, LLVM is a full-featured IR, and a faithful formalization 
    is necessarily complex and large. When the compiler is under development, 
    even stating the correctness of the compiler can be difficult, much 
    less prove it.

    But if we have interpreters for both the source and target, testing the 
    compiler is a much simpler affair. Moreover, the simplicity of the source 
    language, i.e. Imp. means that it is really easy to test! *)

(** This lecture shows how QuickChick can be used to test the compiler. For
    simplicity, the target language is the simplified SSA language Vminus, and
    we use a variant of Imp whose names are just memory addresses which can be 
    interpreted in the memory of Vminus states. Imp states and Vminus memory
    are hence essentially the same, and this makes it easy to state correct 
    compilation: after running the source program and its compilation, 
    every Imp variable/address is mapped to the same nat by both the Imp state 
    and Vminus memory. 

    A Vminus state consists of a memory (mapping addresses to nat), a program 
    counter, an environment mapping locals to nat, a "previous" program 
    counter, and a "previous" environment. The latter two are needed for
    executing phi nodes. A configuration consists of a Vminus state and a CFG,
    which "holds" Vminus instructions organized in basic blocks.
*)

(** Here's a look at what we mean. 

Theorem compile_program_correct_terminating:
  forall c m m' g le lr,
  (g, le, lr) = compile c ->
  imp_terminates c m m' ->
  vminus_terminates g m m'.

  This is one of the top-level correctness theorems for the compiler: for any 
  initial memory m, if the source program c terminates with memory (Imp state) 
  m', running the compilation result g (a control flow graph holding the 
  instructions) on the same initial memory m also results in termination, and
  with its final (Vminus) memory also being m. This is where the coincidence of 
  Imp states and Vminus memory comes into play.
  
  Terminating Imp programs are those that are evaluated to just SKIP, as the
  following definition shows. 

  Definition imp_terminates (c: com) (m m':mem) : Prop :=
    star Imp.step (c, m) (SKIP, m').

  For Vminus programs on the other hand, running them on an initial memory m 
  leads to termination with memory m' if execution reaches some uid x 
  associated with a return terminator.

  Definition vminus_terminates (g:ListCFG.t) (m m':mem) : Prop :=
    exists x st',
      insns_at_pc g st'.(st_pc) [(x, cmd_tmn tmn_ret)] /\
      st'.(st_mem) = m' /\
      star (step g) (init_state g m) st'.

  The variables x and st' here are determined by "running"/evaluation, as 
  indicated by "star (step g) (init_state g m) st'". So checking for their 
  existence is really verifying that an evaluation function reaches st' 
  satisfying the constraints. 
 *)

(** Let us try to write a Checker for the theorem. Looking at the universals, 
    it would appear that we need generators for Imp commands (c), Imp 
    states/memories (m, m'), control flow graphs (g) and labels (le, lr).
    However, note that g, le, and lr are computed by "compile c", so we 
    don't actually need generators for them. Moreover, we do not want just any 
    c and m', but only terminating Imp programs, and m' is obtained by running
    an Imp evaluator on m. Hence for generation, we only need:
    - A generator for mem. 
    - A generator for Imp programs that are guaranteed to terminate. 
    And for checking, we would need:
    - An evaluator for Imp that reaches termination, i.e. SKIP.
    - An evaluator for Vminus that reaches termination, i.e. a return 
      terminator. 
    - We also need to check that the final state st' that the Vminus evaluator 
      reaches has the desired memory.
*)

(** Let us first define an evaluator for Vminus. The evaluator stops when 
    a return terminator is reached. *)

Fixpoint vminus_eval (g: ListCFG.t) (s : state) (fuel: nat) : err state :=
  (* FILL IN HERE *)
  match fuel with
  | 0 => inl "out of fuel"
  | S n' =>
    match (ListCFG.fetch g (st_pc s)) with
    | Some instr =>
      if eq_dec_cmd (snd instr) (cmd_tmn tmn_ret) then inr s
      else
        match (eval_step g s) with
        | inr s' => vminus_eval g s' n'
        | inl err => inl err
        end
    | None => inl "no instr to fetch"
    end
  end.

(** It is likely that QuickChick will generate large enough Imp programs such 
    that vminus_eval can run out of fuel. (Think of large aexp expressions.)

    Exercise: Write an instance of GenSized for aexp and bexp such that 
    any size above a certain number, say 5, is rounded down to that. The 
    GenSized instance for bexp should make use of that for aexp. 
 *)

Derive Arbitrary for aexp.

Definition round_down_to (n: nat) (k: nat) :=
  if (lt_dec n k) then n else k.

Instance gen_small_aexp: GenSized aexp :=
  (* FILL IN HERE *)
  {| arbitrarySized n := @arbitrarySized aexp _ (round_down_to 5 n)
  |}.

Instance gen_small_bexp: GenSized bexp :=
  (* FILL IN HERE *)
  {| arbitrarySized n :=
       let fix gen_bexp_func n :=
           match n with
           | 0 => elems [BTrue ; BFalse]
           | S n' =>
             let beq_gen := liftGen2 BEq
                                     (arbitrarySized n)
                                     (arbitrarySized n) in
             let ble_gen := liftGen2 BLe
                                     (arbitrarySized n)
                                     (arbitrarySized n) in
           let bnot_gen := liftGen BNot (gen_bexp_func n') in
           let band_gen := liftGen2 BAnd (gen_bexp_func n') (gen_bexp_func n')
           in
           oneOf [ beq_gen ; ble_gen ; bnot_gen ; band_gen ]
           end in
       gen_bexp_func (round_down_to 5 n)
  |}.

(** For com, recall that the lemma applies only to terminating ones. Hence, 
    write two sized generators for com: 
    - one that generates only assignment statements and SKIPs, such that the 
      latter are generated with low probability.
    - one that generates IF-THEN-ELSE, assignments and SKIPs, but no loops.
 *)

Fixpoint gen_seq_com (n : nat) : G com :=
  (* FILL IN HERE *)
  match n with 
  | 0 => freq [(4, liftGen2 CAss arbitrary arbitrary); (1, returnGen SKIP)]
  | S n' =>
    let gen := gen_seq_com n' in
    liftGen2 CSeq gen gen
  end. 

Fixpoint gen_if_com (n: nat) : G com :=
  (* FILL IN HERE *)
  match n with
  | 0 => freq [(1, returnGen CSkip) ;
                (4, liftGen2 CAss arbitrary arbitrary)]
  | S n' =>
    let gen := gen_if_com n' in
    oneOf [liftGen3 CIf arbitrary gen gen; liftGen2 CSeq gen gen]
  end.

(** For your convenience, the Shows and Shrinks for aexp, bexp and com have 
    been defined. *)

(** The last thing we need a generator for is mem. One could generate this by 
    first generating a subset of its domain, i.e. Atom.t, and then generating 
    the image for this subset; the rest would be kept as some initial value. 
*)

(** Write a function that outputs a generator for mem, given a list of 
    atoms. 
*)

Definition gen_mem_from_atom_list
           (atom_list : list Atom.t) : G mem :=
  (* FILL IN HERE *)
  bindGen (vectorOf (List.length atom_list) arbitrary) (fun nat_list => 
  returnGen (fun (a : Atom.t) =>
               match (index_of_atom_in_list a atom_list) with
               | None => 0
               | Some i =>
                 List.nth i nat_list 0
               end)).

(** Now write a generator for Atom.t. You may find the function get_fresh_atoms
    useful: it takes in (n: nat) and a list of atoms, and outputs a list of n
    atoms that are distinct from the input. 
*)

Check get_fresh_atoms 6 [].

Instance gen_domain : Gen Atom.t :=
  (* FILL IN HERE *)  
  {| arbitrary :=
       let atom_store := get_fresh_atoms 100 [] in
       oneof (returnGen (Atom.fresh [])) (List.map returnGen atom_store)
  |}.

(** It would be convenient to show memory too. *)

Check show_memory.

(** With generation out of the way, we can now return to checking. 
    The Vminus evaluator defined earlier solves a part of the puzzle, namely
    the question of how to check the existence of st' and x. However, we also 
    need to check that st' has the desired memory. Because memories here are 
    total maps, we can only check for equality of memories for a specified 
    domain. 
*)

Fixpoint memory_on_domain_checker
         (dom: list addr) (mem1 mem2 : V.Opsem.mem) : Checker :=
  match dom with
  | [] => checker true
  | (a :: l) =>
    if Nat.eqb (mem1 a) (mem2 a) then
      memory_on_domain_checker l mem1 mem2
    else
      whenFail
        ("memory_equal: memory at " ++ (show a)
                                    ++ " not equal:"
                                    ++ " mem1 has " ++ (show (mem1 a))
                                    ++ "; mem2 has " ++ (show (mem2 a))
        )%string
        false
  end.

(** This lets us assemble the termination checker for Vminus in full. *)
Definition vminus_termination_checker
           (g: ListCFG.t) (m m': mem) (dom: list addr) : Checker :=
  (* FILL IN HERE *)
  match vminus_eval g (init_state g m) 10000 with
  | inr final_state =>
    whenFail "vminus_termination_check: memories not equal"
             (memory_on_domain_checker dom (st_mem final_state) m')
  | inl err =>
    whenFail ("vminus_termination_check: " ++ err) false
  end.

(** And therefore, the Checker for the lemma in full. *)

Definition compile_program_correct_terminating_checker: Checker :=
  forAll (gen_seq_com 5) (fun (c : Imp.com) =>
  forAll arbitrary (fun (dom : list Atom.t) => 
  forAllShrinkShow (gen_mem_from_atom_list dom)
                   (fun x => []) (* dummy shrinker *)
                   (fun m => show_memory m dom) (* show just for the domain *)
                   (fun m => 
  let '(g, le, lr) := compile c in
    match imp_eval c m 100 with
    | Some s' =>
      vminus_termination_checker g m s' dom
    | None => whenFail "compile_program_termination: cannot eval imp to Skip"
                      false
    end))).

(** Note the use of forAllShrinkShow here, which lets us choose the specific 
    Show we want to use; it is needed here because we don't have a Show 
    instance for total maps like mem. *)

(* ! QuickChick compile_program_correct_terminating_checker. *)

(** For the next part, let us go into the sort of lemmas that would be needed 
    to prove the top-level correctness theorems like the one above. Here's one.

Lemma comp_aexp_correct : forall (a:aexp),
    comp_correct (comp_aexp a) (aeval a).

Definition comp_correct (comp : ectmon (val * list insn))
           (eval : mem -> nat) : Prop :=
  forall (cs cs': list uid) (g: ListCFG.t) (st: V.Opsem.state)
    (is k: list insn) (v: val), 
    (cs', (v, is)) = comp cs ->
    insns_at_pc g (st_pc st) (is ++ k) ->
    exists st',
      st_mem st' = st_mem st /\
      insns_at_pc g (st_pc st') k /\
      star (Opsem.step g) st st' /\
      ids_preserved cs st st' /\
      good_return cs' v /\
      ctx_incr cs cs' /\
      eval_val (st_loc st') v = Some (eval (st_mem st)).
*)

(** That is, compiling Imp aexp is correct if:
    - for any compilation run on an initial list of uids, 
    - wherever we place the compilation result "is" in the CFG, as long
      as the pc is pointed to it, (insns_at_pc g (st_pc) (is ++ k)),
    - we can run to the end of compilation (insns_at_pc g (st_pc st') k),
    - and in this state st', the memory is the same as above; but evaluating 
      the result of the expression in this state (eval_val (st_loc st') v)
      is exactly the same as evaluating it according to the Imp state
      (eval (st_mem st)). 
    - This last fact may not be obvious from the body of comp_correct. But note 
      comp_aexp_correct; the evaluation function passed to it is Imp's aeval, 
      and this is where the coincidence of Imp states and Vminus memory comes 
      into play.
    There is a bunch of other things that we need here, so as to prove correct
    compilation for com. But the above description is the crux.
*)

(** Looking at comp_correct, it is clear that we need to generate more than 
    just the things we had before. In particular, it would seem that we need 
    generators for the following:
    - uid
    - CFG
    - Vminus states
    - Vminus instructions
    - values
    But note again that the only value v (with cs', is) is computed by comp 
    rather than generated, so we don't actually need a generator for value. 
    Moreover, the CFG g should not be generated randomly the same way we do 
    others, because it has to satisfy insns_at_pc; it is unlikely for just 
    "any" CFG to satisfy this precondition of the lemma. *)

(**
    Exercise: Generators and Shows for uid and Vminus instructions, using 
    automation as much as possible. (It is however useful to have custom Shows 
    that are more descriptive.) *)

(* FILL IN HERE *)

(** For Vminus states, we already have a generator for mem. We have defined a 
    generator and show for loc for you. *)

Check gen_loc_from_atom_list.
Check show_locals.

(** Hence, write a generator and a show function for Vminus states, 
    given domains for mem and loc. For simplicity, we can use the same 
    domain for ploc. 
 *)

Definition gen_vminus_state
           (mem_dom: list Atom.t)
           (loc_dom: list Atom.t) : G state :=
  (* FILL IN HERE *)
       let gmem := gen_mem_from_atom_list mem_dom in
       let gloc := gen_loc_from_atom_list mem_dom in
       bindGen gmem (fun mem =>
       bindGen arbitrary (fun pc =>
       bindGen gloc (fun loc =>
       bindGen arbitrary (fun ppc =>
       bindGen gloc (fun prev_loc =>
         returnGen
           (mkst mem
                 pc
                 loc
                 ppc
                 prev_loc)))))).

Definition show_vminus_state
           (mem_dom: list Atom.t)
           (loc_dom: list Atom.t)
           (st: state) : string :=
  (* FILL IN HERE *)
  (show_memory (st_mem st) mem_dom ++ ", " ++
               "pc: " ++ show (st_pc st) ++ ", " ++
               show_locals (st_loc st) loc_dom ++ ", " ++
               "ppc: " ++ show (st_ppc st) ++ ", " ++
               "prev_loc: " ++ show_locals (st_ploc st) loc_dom)%string.

(** With these out of the way, we can now address the remaining gaps. In its 
    current form, comp_correct is inefficient and challenging for testing. 
    Firstly, some of the quantities are computed by a function, so it is 
    unnecessary to generate them in the first place, although seemingly 
    suggested by "forall". Secondly, the CFG g is not just any CFG, but one 
    that satisfies insns_at_pc for the compilation result - random generation 
    in the usual way is very, very unlikely to meet this condition, so most
    checks would end up being vacuously true. Thirdly, a Checker for the 
    the existence of st' really needs to compute it, and this is not part of
    the lemma itself. 

    Hence the first order of affairs is to massage the lemma into a 
    Checker-friendly version.
 *)

(** Firstly, let us drop the unnecessary variables, and note the generation 
    of state.

    Definition comp_correct (comp : ectmon (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (g: ListCFG.t) (k: list insn),
      forall (mem_dom: list Atom.t) (loc_dom: list Atom.t) (st: state),

      let (cs', (v, is)) := comp cs in

      insns_at_pc g (st_pc st) (is ++ k) ->
      exists st',
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\
        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs' /\
        eval_val (st_loc st') v = Some (eval (st_mem st)).

    This is of course not accepted by Coq, but we will eventually get to a
    Checker.
 *)

(** Secondly, we need to write a custom generator that generates CFGs 
    satisfying insns_at_pc. An easier option is to just construct a CFG that 
    loads the instructions at a given pc. 

    Let us call this wrap_code_in_cfg' pc is k, in correspondence with 
    insns_at_pc g (st_pc st) (is ++ k).

    However, because pc may have a positive offset into the block, we should 
    also fill the initial instructions with some dummy instructions (that won't
    be executed). So make wrap_code_in_cfg' do this. 
*)

(* Returns a CFG with a single block containing instrs ++ instrs_after, 
    and the pc in that block that begins at instrs_after *)
Definition wrap_code_in_cfg' (p: pc) (instrs instrs_after: list insn)
  : ListCFG.t :=
  (* FILL IN HERE *)
  let empty_cfg := [] in
  let '(lbl, offset) := p in
  let blocks :=
      ListCFG.update empty_cfg lbl
                     ((generate_dummy_insns offset)
                        ++ instrs ++ instrs_after) in
  (lbl, blocks).

(** The to-be-Checkable lemma is thus:

    Definition comp_correct (comp : ectmon (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (k: list insn),
      forall (mem_dom: list Atom.t) (loc_dom: list Atom.t) (st: state),

      let (cs', (v, is)) := comp cs in
      let g := wrap_code_in_cfg (st_pc st) is k in

      exists st',
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\
        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs' /\
        eval_val (st_loc st') v = Some (eval (st_mem st)). 
*)

(** Thirdly, if we have grasped the meaning of the lemma, we know that st'
    is given by executing the compilation result; this is the point of 
    "loading" the compilation result at the current pc in g, and is of course 
    also stated by "star (Opsem.step g) st st'". So we need an executable 
    evaluator for Vminus. The state st' is obtained by running this evaluator 
    until we reach (the start of) k. 
    
    The simplest way of doing so is to stop at the program counter that begins
    k, and this is actually determined by the CFG that loaded (is ++ k). 
*)

(** Exercise: Change wrap_code_in_cfg to return (g, pc), where the latter is 
    the pc that begins k. *)

Definition wrap_code_in_cfg (p: pc) (instrs instrs_after: list insn)
  : ListCFG.t * pc :=
  (* FILL IN HERE *)
  let empty_cfg := [] in
  let '(lbl, offset) := p in
  let blocks :=
      ListCFG.update empty_cfg lbl
                     ((generate_dummy_insns offset)
                        ++ instrs ++ instrs_after) in
  ((lbl, blocks), (lbl, offset + List.length instrs)).

(** Now we need the evaluator itself, which we have defined for you. *)

Check V.Opsem.eval_until_pc.
Check V.Opsem.eval_step.

(** Now the lemma is:

    Definition comp_correct (comp : ectmon (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (k: list insn),
      forall (mem_dom: list Atom.t) (loc_dom: list Atom.t) (st: state),

      let (cs', (v, is)) := comp cs in
      let (g, endpoint) := wrap_code_in_cfg (st_pc st) is k in

      match V.Opsem.eval_until_pc g st cutpoint 1000 with
      | inl err => false (* either out of fuel or no st' *)
      | inr st' => 
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\
        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs' /\
        eval_val (st_loc st') v = Some (eval (st_mem st))
      end.
 *)

(** And with this, the major obstacles are out of the way, and we only have
    to write a Checker for the big conjunction. Because the conjunction is 
    huge, it is easier to write a Checker for each conjunct. That is, we would
    like to have:
    - A Checker that checks that two memories are the same. This has already 
      been done.
    - A Checker that checks for insns_at_pc g.
    - A Checker for ids_preserved.
    - A Checker for good_return.
    - A Checker for ctxt_incr.
    - A Checker that checks for equality between the two ways of evaluation.
    Note that "star (Opsem.step g) st st'" doesn't need checking, because it is
    implicit in eval_until_pc. With respect to correctness of aexp compilation 
    itself, the last is most relevant. 

    To give a headstart, most of these are defined below.
*)

Fixpoint loc_on_domain_checker
         (dom: list uid) (loc1 loc2 : loc) : Checker :=
  match dom with
  | [] => checker true
  | (a :: l) =>
    match loc1 a, loc2 a with
    | Some n1, Some n2 =>
      if Nat.eqb n1 n2 then loc_on_domain_checker l loc1 loc2
      else whenFail "loc_equal: locs disagree" false
    | None, None => loc_on_domain_checker l loc1 loc2
    | _, _ => whenFail "loc_equal: locs disagree" false
    end
  end.

Fixpoint insns_at_pc_checker `{Show pc}
         (g: ListCFG.t) (p: pc) (k : list insn) : Checker :=
  match k with
  | [] => checker true
  | (uid, cmd) :: instrs =>
    match ListCFG.fetch g p with
    | Some (uid', cmd') =>
      if eq_dec_uid uid uid' then
        if eq_dec_cmd cmd cmd' then insns_at_pc_checker g (incr_pc p) instrs
        else whenFail ("insns_at_pc: cmd at pc "
                         ++ (show p) ++ " not equal") false
      else whenFail ("insns_at_pc: uid at pc "
                       ++ (show p) ++ "not equal") false
    | None => whenFail "insns_at_pc: cannot fetch" false
    end
  end.

Definition eval_equal_checker (eval: mem -> nat) (st: state) (v: val)
  : Checker :=
  let run_result := eval_val (st_loc st) v in
  let expected_result := eval (st_mem st) in
  match run_result with
  | Some n =>
    whenFail "eval_equal: evaluation value not the same"
             (Nat.eqb n expected_result)
  | None => whenFail "eval_equal: run did not obtain any value" false
  end.

Definition ids_preserved_checker (cs : list uid) (st st': state)
  : Checker :=
  loc_on_domain_checker cs (st_loc st) (st_loc st').


Definition good_return_checker (cs: list uid) (v: val) : Checker :=
  match v with
  | val_uid uid =>
    whenFail "good_return: cannot find value" 
             (List.existsb
                (fun uid' => if eq_dec_uid uid uid' then true else false) cs)
  | val_nat n => checker true
  end.

Fixpoint ctx_incr_checker (cs cs': list uid) : Checker :=
  (* FILL IN HERE *)
  match cs with
  | [] => checker true
  | (uid :: uids) =>
    if (List.existsb
          (fun uid' => if eq_dec_uid uid uid' then true else false) cs') then
      ctx_incr_checker uids cs'
    else whenFail ("ctx_incr: " ++ show uid ++ " not found") false
  end.

(** We can now compose the checkers using QuickChick's conjoin combinator. *)
Definition expression_step_checker
           (eval: V.Opsem.mem -> nat)
           (g: ListCFG.t)
           (initial_state final_state: V.Opsem.state)
           (k: list insn) (end_of_expr: pc)
           (cs cs': list uid)
           (v : val) : Checker :=
  conjoin [ids_preserved_checker cs initial_state final_state;
             insns_at_pc_checker g end_of_expr k;
             good_return_checker cs' v;
             ctx_incr_checker cs cs';
             eval_equal_checker eval final_state v].

(** Finally, a Checker for comp_correct and comp_aexp could look like the 
    following. It is convenient to split the Checker into a part that does 
    only the generation, and a part that does the checking, because a type 
    error can cause the typechecker to get stuck trying to resolve the issue
    by looking for typeclass instances that don't exist.    
*)

Definition comp_correct_checker_inner
           (comp: ectmon (val * list insn)) (eval: V.Opsem.mem -> nat)
           (cs : list uid) (st: V.Opsem.state) (k: list insn)
  : Checker :=
  let '(cs', (v, instrs)) := comp cs in
  let '(g, endpoint) := wrap_code_in_cfg (V.Opsem.st_pc st) instrs k in
  match V.Opsem.eval_until_pc g st endpoint 1000 with
  | inl err => whenFail ("comp_correct_checker: " ++ err) false
  | inr st' => 
    expression_step_checker eval g st st' k endpoint cs cs' v
  end.

Definition comp_correct_checker
           (comp: ectmon (val * list insn)) (eval: V.Opsem.mem -> nat)
  : Checker :=
  forAll arbitrary (fun (cs : list uid) =>
  forAll arbitrary (fun (extra_insn : list insn) =>
  forAll arbitrary (fun (mem_dom: list Atom.t) =>
  forAll arbitrary (fun (loc_dom: list Atom.t) =>
  forAllShrinkShow (gen_vminus_state mem_dom loc_dom)
                   (fun x => [])
                   (show_vminus_state mem_dom loc_dom)
                   (fun (start_state: state) => 
    comp_correct_checker_inner
      comp eval
      cs start_state extra_insn))))).

(**! Section test_compile_aexp extends compiler *)

Definition comp_aexp_correct_checker :=
  forAll arbitrary (fun a: aexp =>
    (* collect a ( *) comp_correct_checker (comp_aexp a) (aeval a)).

(* ! QuickChick comp_aexp_correct_checker. *)

(** Since the compiler has already been proven correct, all tests should 
    succeed. However, they could be succeeding for rather vacuous reasons, and 
    it would be assuring to know that the Checker indeed fails when the 
    compiler is wrong. 

    Exercise: Add mutants to comp_aexp, and verify that they are causing 
    comp_aexp_correct_checker to fail. 
 *)

(** Exercise: Write a Checker for the following lemma, and run it.

Lemma comp_bop_correct : forall b comp1 comp2 eval1 eval2
    (IHa1: comp_correct comp1 eval1)
    (IHa2: comp_correct comp2 eval2),
    comp_correct (comp_bop b comp1 comp2)
                 (fun m => bop_denote b (eval1 m) (eval2 m)).
 *)

Definition comp_bop_correct_checker: Checker :=
  (* FILL IN HERE *)
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

(** Exercise: Write a Checker for the following lemma, and make sure that all 
    tests pass. 

Lemma comp_bexp_correct : forall (b:bexp),
  comp_correct (comp_bexp b) (fun m => b2n (beval b m)).
*)

(** Exercise: Write a Checker for the following lemma, and make sure that all 
    tests pass.

Lemma comp_store_correct : 
  forall g a v le lr cs st,
  insns_at_pc g (block_entry le) (steval (comp_store a v lr) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = (block_entry lr) /\
    st_mem st' = (Memory.update (st_mem st) v (aeval a (st_mem st))).
 *)

Definition comp_store_correct_checker_inner
           (a : aexp) (v: addr) (lr le: lbl) (cs: list uid)
           (mem_dom: list Atom.t) (loc_dom: list Atom.t) (vst: state)
  : Checker :=
  (* FILL IN HERE *)
  let st := mkst (st_mem vst) (block_entry le) (st_loc vst)
                 (st_ppc vst) (st_ploc vst) in
  let '(g, end_pc) :=
      wrap_code_in_cfg (block_entry le)
                       (steval (comp_store a v lr) cs) [] in
  match (V.Opsem.eval_once_and_until_pc g st (block_entry lr) 1000) with
  | inl err => whenFail ("comp_store_correct: " ++ err) false
  | inr st' =>
    if (eq_dec_pc (V.Opsem.st_pc st') (block_entry lr)) then
      let new_dom := (v :: mem_dom) in
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
  forAll arbitrary (fun (mem_dom: list Atom.t) =>
  forAll arbitrary (fun (loc_dom: list Atom.t) =>
  forAllShrinkShow (gen_vminus_state mem_dom loc_dom)                      
                   (fun x => [])
                   (show_vminus_state mem_dom loc_dom)
                   (fun (vst: state) => 
    comp_store_correct_checker_inner a v lr le cs mem_dom loc_dom vst)))))))).


(** Exercise: Write a Checker for the following lemma, and make sure that all 
    tests pass.

Lemma comp_cond_correct :
  forall g cs b le l1 l2 st,
  insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = block_entry (if beval b (st_mem st) then l1 else l2) /\
    st_mem st = st_mem st'.
*)

Definition comp_cond_correct_checker_inner
           (b: bexp) (cs: list uid) (le l1 l2: lbl)
           (mem_dom: list Atom.t) (loc_dom: list Atom.t) (vst: state)
  : Checker :=
  (* FILL IN HERE *)
  let st := mkst (st_mem vst) (block_entry le) (st_loc vst)
                 (st_ppc vst) (st_ploc vst) in
  let '(g, end_pc) :=
      wrap_code_in_cfg (block_entry le)
                       (steval (comp_cond b l1 l2) cs) [] in
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
               (memory_on_domain_checker mem_dom
                                         (st_mem st)
                                         (st_mem st'))
    else whenFail "comp_cond_correct: pc not expected" false
  end.

Definition comp_cond_correct_checker : Checker :=
  forAll arbitrary (fun (b: bexp) =>
  forAll arbitrary (fun (le: lbl) =>
  forAll arbitrary (fun (l1: lbl) =>
  forAll arbitrary (fun (l2: lbl) =>
  forAll arbitrary (fun (cs: list uid) =>
  forAll arbitrary (fun (mem_dom: list Atom.t) =>
  forAll arbitrary (fun (loc_dom: list Atom.t) =>
  forAllShrinkShow (gen_vminus_state mem_dom loc_dom)                      
                   (fun x => [])
                   (show_vminus_state mem_dom loc_dom)
                   (fun (vst: state) => 
    comp_cond_correct_checker_inner b cs le l1 l2 mem_dom loc_dom vst)))))))).

(* ! QuickChick comp_cond_correct_checker. *)