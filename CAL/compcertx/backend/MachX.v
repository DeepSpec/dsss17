Require compcert.backend.Mach.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import Events.
Import Smallstep.
Import Locations.
Import Conventions.
Export Mach.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

(** Execution of Mach functions with Asm-style arguments (long long 64-bit integers NOT allowed) *)

Inductive initial_state (lm: regset) (init_sp: val) (p: Mach.program) (i: ident) (sg: signature) (args: list val) (m: mem): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    (Hargs: extcall_arguments lm m init_sp sg args)    
  :
      initial_state lm init_sp p i sg args m (Callstate nil b lm m)
.

Definition get_pair (p: rpair mreg) (m: regset): val :=
  match p with
    | One l => m l
    | Twolong l1 l2 => Val.longofwords (m l1) (m l2)
  end.

Inductive final_state (lm: regset) (sg: signature): state -> (val * mem) -> Prop :=
| final_state_intro
    rs
    v
    (Hv: v = get_pair (loc_result sg) rs)
    (** Callee-save registers.
        We use Val.lessdef instead of eq because the Stacking pass does not exactly preserve their values. *)
    (CALLEE_SAVE: forall r,
       ~ In r destroyed_at_call ->
       Val.lessdef (lm r) (rs r))
    m :
    final_state lm sg (Returnstate nil rs m) (v, m)
.

Definition semantics
           (return_address_offset: function -> code -> ptrofs -> Prop)
           (lm: regset) (init_sp init_ra: val)
           (p: Mach.program) (i: ident) (sg: signature) (args: list val) (m: mem) :=
  Semantics
    (Mach.step init_sp init_ra return_address_offset)
    (initial_state lm init_sp p i sg args m)
    (final_state lm sg)
    (Genv.globalenv p).

End WITHCONFIG.
