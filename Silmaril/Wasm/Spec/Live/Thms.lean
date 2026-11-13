module

public import Silmaril.Wasm.Spec.Live.Defs
public import Silmaril.Proofs.Wasm.Spec.Live.Basic
public import Silmaril.Proofs.Wasm.Spec.Live.Chain
public import Silmaril.Proofs.Wasm.Spec.Live.Ground
public import Silmaril.Proofs.Wasm.Spec.Live.Sound
public import Silmaril.Proofs.Wasm.Spec.Live.Litmus

@[expose] public section

/-!
# Liveness grounded in Core 3.0 divergence: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Live.*`. Every profile `P`; no determinism is assumed.

**The response formula** (`Basic`): `holdsFin_responds_iff`, `holdsInf_responds_iff`;
`not_sat_responds_of_witness`: a divergence witness refutes `responds` over maximal behaviours;
`sat_of_witness`: an `ltlMax` sentence holds of every divergence witness.

**Infinite words** (`Chain`): `chainWord`, the word of an increasing unbounded chain, with
`prefixList_chainWord`, `exists_prefixList_chainWord`, `chainWord_mem`.

**Core divergence is game divergence** (`Ground`), for total environments `K`:

* `diverges_cases`: a Core divergence of an export call under `hostOf X.imports K` is local
  divergence of the instance after a play agreeing with `K`, or infinite hidden chatter (an
  increasing unbounded chain of plays agreeing with `K` whose only export event is the call). From
  `ScalarInstance.mem_div_closedD_iff`, `closedD_eq_comp` and `DStrategy.mem_div_comp`;
* `diverges_of_local`: the converse for local divergence;
* `maximal_div`: divergence traces of `wasmDivSem` are maximal;
* **`diverges_witness`**: every Core divergence is a maximal behaviour of `wasmDivSem P` calling
  the export and returning nothing but `diverges` (`DivWitness`);
* `exists_trace_of_behaviour`: every terminating Core behaviour is a trace of `wasmDivSem P`
  (adequacy M2).

**Soundness** (`Sound`):

* **`not_diverges_of_terminates`**, `behaviours_ne_diverges`: if `p` satisfies `terminates j` in
  `inst ltlMax (wasmDivSem P)`, no Core invocation of `j` diverges against any total
  environment;
* `ltlMax_closed_world_div`, `ltlMax_closed_world`: every `ltlMax` sentence verified over
  `wasmDivSem P` holds of a maximal behaviour representing each Core behaviour, divergent or
  terminating.

**Litmus** (`Litmus`): `okRun_terminates`, `divRun_not_terminates`,
`chatterRun_not_terminates`, `chatterRun_neverCall_assert`, `trapEnv_total`.

Not covered: environments that may refuse to answer (their divergence is not the program's, and
`wasmDivSem` does not mark it); stateful hosts (`SEnv`) for divergence; a proof method for
liveness of concrete Core code (no real module is proved terminating here: the litmus tests use
the loose semantics); the component semantics, whose IR has no divergence.
-/
