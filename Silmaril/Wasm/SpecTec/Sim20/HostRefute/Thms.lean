module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.HostRefute

/-!
# Host calls in the forward 2.0 half: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.HostRefute`; see `docs/projects/spectec/README.md`, "fwd20".

* `not_typedV_store_host`: in every environment with the 2.0 types `state`, `store`, `funcinst`
  and `func` (`simEnv20`, `simEnv20S`, `simEnv20T`), a store holding a host function has no IL
  type: `_HOSTFUNC` is not a 2.0 `func`.
* `stuck_host`: so neither the corrected script nor the script with the `STORE` erratum has a step
  from the image of such a configuration.
* **`not_fwd_host`**: V2 calls a host function (`Step.callAddrHost`) where neither script has a
  step, at every builtins. The forward half is stated on host-free stores (`Whole.StoreOk`,
  `CallIndGood.StoreOkI`), and that is the restatement.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.HostRefute

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.HostRefute.not_typedV_store_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_typedV_store_host

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.HostRefute.stuck_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stuck_host

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.HostRefute.not_fwd_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_fwd_host

end Silmaril.Wasm.SpecTec.Sim20.HostRefute
