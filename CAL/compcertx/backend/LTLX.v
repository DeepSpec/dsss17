Require compcert.backend.LTL.
Require EventsX.
Require Import LocationsX.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import EventsX.
Import Smallstep.
Import Locations.
Import Conventions.
Export LTL.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

(** Execution of LTL functions with Asm-style arguments (long long 64-bit integers NOT allowed) *)

Inductive initial_state (lm: locset) (p: LTL.program) (i: ident) (sg: signature) (args: list val) (m: mem): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (Hsig: sg = funsig f)
    (Hargs: args = map (fun pa => Locmap.getpair pa lm) (loc_arguments sg))
  :
      initial_state lm p i sg args m (Callstate nil f lm m)
.

Inductive final_state (lm: locset) (sg: signature): state -> (val * mem) -> Prop :=
| final_state_intro
    rs
    v
    (Hv: v = getpair (loc_result sg) rs)
    (** Callee-save registers *)
    (CALLEE_SAVE: forall r,
       ~ In r destroyed_at_call ->
       rs (R r) = lm (R r))
    m :
    final_state lm sg (Returnstate nil rs m) (v, m)
.

Definition semantics
           (lm: locset)
           (p: LTL.program) (i: ident) (sg: signature) (args: list val) (m: mem) :=
  Semantics (
      LTL.step lm
    ) (initial_state lm p i sg args m) (final_state lm sg) (Genv.globalenv p).

End WITHCONFIG.
