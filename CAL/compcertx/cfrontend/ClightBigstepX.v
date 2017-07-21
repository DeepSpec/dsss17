Require compcert.cfrontend.ClightBigstep.
Require EventsX.

Import Coqlib.
Import AST.
Import Globalenvs.
Import EventsX.
Import Ctypes.
Import Clight.
Export ClightBigstep.

Require Import ClightX.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Inductive bigstep_function_terminates' function_entry p i sg vargs (m: mem) t : Values.val * mem -> Prop :=
  | bigstep_function_terminates_intro b f targs tres cc vres m':
      let ge := Clight.globalenv p in
      Genv.find_symbol ge i = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction targs tres cc ->
      sg = signature_of_type targs tres cc ->
      eval_funcall ge function_entry m f vargs t m' vres ->
      bigstep_function_terminates' function_entry p i sg vargs m t (vres,  m').

Definition bigstep_function_terminates2 := bigstep_function_terminates' function_entry2.

Inductive bigstep_function_diverges' function_entry (p: program) i sg vargs m: traceinf -> Prop :=
  | bigstep_function_diverges_intro: forall b f targs tres cc t,
      let ge := globalenv p in
      Genv.find_symbol ge i = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction targs tres cc ->
      sg = signature_of_type targs tres cc ->
      evalinf_funcall ge function_entry m f vargs t ->
      bigstep_function_diverges' function_entry p i sg vargs m t.

Definition bigstep_function_diverges2 := bigstep_function_diverges' function_entry2.

Definition bigstep_function_semantics2 (p: program) i sg vargs m :=
  Smallstep.Bigstep_semantics
    (bigstep_function_terminates2 p i sg vargs m)
    (bigstep_function_diverges2 p i sg vargs m).

Theorem bigstep_function_semantics_sound prog i (sg: AST.signature) (vargs: list Values.val) m:
  Smallstep.bigstep_sound
    (bigstep_function_semantics2 prog i sg vargs m)
    (ClightX.semantics prog i m sg vargs).
Proof.
  constructor; simpl; intros.
(* termination *)
  inv H. econstructor; econstructor.
  split. econstructor; eauto.
  split. eapply eval_funcall_steps. eauto. red; auto.
  econstructor.
(* divergence *)
  inv H. econstructor.
  split. econstructor; eauto.
  eapply Smallstep.forever_N_forever with (order := order).
  red; intros. constructor; intros. red in H. elim H.
  eapply evalinf_funcall_forever; eauto.
Qed.


End WITHCONFIG.
