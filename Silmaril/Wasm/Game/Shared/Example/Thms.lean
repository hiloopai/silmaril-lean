module

public import Silmaril.Wasm.Game.Shared.Example.Defs
public import Silmaril.Wasm.Game.Shared.Thms
import Silmaril.Proofs.Wasm.Game.Shared.Example.Run

/-!
# A host that writes the module's memory: theorems

For **every** profile `P`, the export `get` of `exLog` (call the import `log`,
then return the byte at address `0` of the imported memory), run against
`logHost` (whose `log` writes byte `42` there):

* `exLogI_wellFormed`, `logHost_ok`, `logHost_keeps`: the instance is a
  well-formed spec instance, the host satisfies Core's host contract and keeps
  host functions typed, so `shAdequacy_host` applies;
* `get_behaviour`: Core 3.0 reduction under the host returns `i32 42`;
* `get_responds`: **the closed program of the store-passing game answers the
  export question `get` with `i32 42` in the written store `poke s₀`**, and
  `get_observes`: the behaviour `i32 42` is an observation of the composite
  `((SEnv.ofHost _ logHost).dstrategy ()).comp (exLogI.shDStrategy P)`. The value 42 is
  only in the store returned by the host's answer move: the module reads the
  host's write through the shared store.

Not shown: that `i32 42` is the *only* observation (uniqueness of the run under
an arbitrary profile).

Proofs: `Silmaril.Proofs.Wasm.Game.Shared.Example.*` (new).
-/

public section

namespace Silmaril.Wasm.Game.SharedExample

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem exLogI_wellFormed : exLogI.WellFormed exLogI.store :=
  Silmaril.Proofs.Wasm.Game.SharedExample.exLogI_wellFormed

theorem logHost_ok : HostOk logHost := Silmaril.Proofs.Wasm.Game.SharedExample.logHost_ok

theorem logHost_keeps : exLogI.HostKeeps logHost :=
  Silmaril.Proofs.Wasm.Game.SharedExample.logHost_keeps

/-- The function address of `get`. -/
theorem addr_get : exLogI.addr getQ.1 = 1 := by
  show (exportFuncAddrs exLogPrep.1.frame.module).getD 0 0 = 1
  rw [Silmaril.Proofs.Wasm.Game.SharedExample.exLog_addrs]
  rfl

/-- Core reduction of `get` under the memory-writing host, every profile. -/
theorem get_run (P : Profile) : ∃ c' : Config Nat,
    Steps P logHost (invoke getQ.2.1 (exLogI.addr getQ.1) getQ.2.2.1) c' ∧
      c'.store = poke exLogI.store ∧ c'.code = ans42.toResult.toAdmin := by
  obtain ⟨fi₀, fi₁, t, x, y, mi, h⟩ := Silmaril.Proofs.Wasm.Game.SharedExample.shape
  rw [addr_get]
  exact ⟨_, Silmaril.Proofs.Wasm.Game.SharedExample.run_get (P := P) h, rfl, rfl⟩

/-- **Core behaviour**: `get` returns `i32 42` under the host, every profile. -/
theorem get_behaviour (P : Profile) :
    ans42.toBehaviour ∈ behaviours P logHost getQ.2.1 (exLogI.addr getQ.1) getQ.2.2.1 := by
  obtain ⟨c', run, -, final⟩ := get_run P
  exact Or.inl ⟨c', _, run, final, rfl⟩

/-- **The game answers `i32 42` in the written store**, every profile. -/
theorem get_responds (P : Profile) :
    Responds (exLogI.closedSh P (SEnv.ofHost exLogI.imports logHost) ()) getQ
      (poke exLogI.store, ans42) := by
  obtain ⟨c', run, hstore, final⟩ := get_run P
  have run' := Silmaril.Proofs.Wasm.Game.Shared.shSteps_of_steps logHost_ok logHost_keeps
    (Silmaril.Proofs.Wasm.Game.Shared.shGood_invoke (f := getQ) exLogI_wellFormed) run
  exact ScalarInstance.responds_closedSh_iff.2
    ⟨c', (), _, run', final, hstore, Answer.ofResult?_toResult ans42⟩

/-- **The observation `i32 42` of the composite strategy**, every profile. -/
theorem get_observes (P : Profile) :
    ans42.toBehaviour ∈
      shDCompositeObs (exLogI.closedShD P (SEnv.ofHost exLogI.imports logHost) ()) getQ := by
  rw [← ScalarInstance.shAdequacy_host logHost_ok logHost_keeps exLogI_wellFormed]
  exact get_behaviour P

end Silmaril.Wasm.Game.SharedExample
