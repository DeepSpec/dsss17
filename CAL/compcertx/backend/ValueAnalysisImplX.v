(** In this file, we repackage an instance for
[compcert.backend.ValueDomain.MMatch] for the concrete memory
model implemented in [compcertx.common.MemimplX]. 

Indeed, those two memory models are different as they use different
implementations of [inject_neutral].

Fortunately, [MMatch] does not use [inject_neutral], so we have nothing to prove. We just need to unpack/repack.

Not even, thanks to reparameterization of ValueAnalysisImpl.
*)

Require compcert.backend.ValueAnalysisImpl.
Require ValueDomainImplX.

Import Coqlib.
Export ValueAnalysis.
Export MemimplX.
Export ValueAnalysisImpl.
