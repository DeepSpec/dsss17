Require compcert.backend.Locations.
Export AST.
Export Values.
Export Locations.

Definition getpair (p: rpair mreg) (m: Locmap.t): val :=
  match p with
    | One l => m (R l)
    | Twolong l1 l2 => Val.longofwords (m (R l1)) (m (R l2))
  end.

Lemma getpair_prop p:
  getpair p = Locmap.getpair (map_rpair R p).
Proof.
  destruct p; reflexivity.
Qed.