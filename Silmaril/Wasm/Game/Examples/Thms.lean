module

public import Silmaril.Wasm.Game.Examples.Defs
public import Silmaril.Wasm.Game.SpecInst.Thms
import Silmaril.Proofs.Wasm.Game.Examples.StartImport
import Silmaril.Proofs.Wasm.Game.Examples.MemImport

/-!
# A module whose start function calls an import: theorems

Non-vacuity of `Silmaril.Wasm.Game.SpecInst` on a concrete module whose actual
Wasm `start` field names a function that calls an import (`exStart`), for an
**arbitrary** profile `P`:

* `ex_isSpecInstance`: `IsSpecInstance exStart exMT exI exC₀` (validation and
  the spec's allocation computed by kernel evaluation);
* `ex_instantiate`: `exC₀` is the configuration of `$instantiate` of `exStart`
  for every profile and host;
* `ex_ready`: against the environment answering `values []`, the instantiation
  question is answered `ready`;
* `ex_diverges`: against the environment that never answers, instantiation
  diverges: the start function waits for its import call, so the import is
  called during instantiation;
* `ex_adequacy`: the instantiation observations are the Core 3.0 behaviours of
  `exC₀` (the headline `IsSpecInstance.adequacy_inst` instantiated).

Non-vacuity of `IsSpecInstanceAt` beyond function imports, on `exMem`, which
imports a memory and a function and has an active data segment:

* `exMem_isSpecInstanceAt`: `IsSpecInstanceAt exMemStore exMemXas exMem exMemMT
  exMemI exMemC₀`;
* `exMem_instantiate`: `exMemC₀` is its `$instantiate` configuration (five
  instructions of segment initialisation, then the start call,
  `exMemC₀_length`), and `exMem_adequacy` instantiates the headline.

Proofs: `Silmaril.Proofs.Wasm.Game.Examples.{StartImport,MemImport}`. New.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Examples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation

/-- **`exI` is the spec instance of `exStart`**, its instantiation configuration `exC₀`. -/
theorem ex_isSpecInstance : IsSpecInstance exStart exMT exI exC₀ :=
  Silmaril.Proofs.Wasm.Game.Examples.ex_isSpecInstance

/-- `exStart` has the start function `1`, whose body calls the import `0`. -/
theorem exStart_start : exStart.start = some ⟨1⟩ ∧
    exStart.funcs.map (·.body) = [[.call ⟨0⟩]] ∧ exStart.imports.length = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- `exC₀` is the configuration of `$instantiate`, for every profile and host. -/
theorem ex_instantiate (P : Profile) (host : HostSemantics Nat) :
    Instantiate P host (importStore (CExternType.funcs exMT.imports)) exStart (importAddrs exMT)
      exC₀ :=
  ex_isSpecInstance.instantiate P host

/-- **Instantiation succeeds against an environment answering the import**, every profile. -/
theorem ex_ready (P : Profile) : (exI.closedSpec P exC₀ exAnswer).InstReady :=
  Silmaril.Proofs.Wasm.Game.Examples.ex_ready

/-- **Instantiation diverges against an environment that never answers**, every profile: the
start function calls the import during instantiation. -/
theorem ex_diverges (P : Profile) : (exI.closedSpec P exC₀ (Env.silent _)).InstDiverges :=
  Silmaril.Proofs.Wasm.Game.Examples.ex_diverges

/-- The headline adequacy theorem, instantiated: the instantiation observations against any
environment throwing only existing exceptions are the Core 3.0 behaviours of `exC₀`. -/
theorem ex_adequacy (P : Profile) (K : Env exI.E) (hK : ThrowsBelow K exI.store.exns.length) :
    instObs (exI.closedSpec P exC₀ K) = behavioursOf P (hostOf exI.imports K) exC₀ :=
  ex_isSpecInstance.adequacy_inst P K hK

/-! ## A module importing a memory -/

/-- **`exMemI` is the spec instance of `exMem` at `exMemStore`**: a module importing a memory
and a function. -/
theorem exMem_isSpecInstanceAt :
    IsSpecInstanceAt exMemStore exMemXas exMem exMemMT exMemI exMemC₀ :=
  Silmaril.Proofs.Wasm.Game.Examples.exMem_isSpecInstanceAt

/-- `exMem` imports a memory first. -/
theorem exMem_imports_mem : ∃ d, exMemMT.imports = [.mem memTy, .func d] :=
  Silmaril.Proofs.Wasm.Game.Examples.exMem_imports

/-- `exMemC₀` is the configuration of `$instantiate` of `exMem`, every profile and host. -/
theorem exMem_instantiate (P : Profile) (host : HostSemantics Nat) :
    Instantiate P host exMemStore exMem exMemXas exMemC₀ :=
  exMem_isSpecInstanceAt.instantiate P host

/-- The configuration runs the segment initialisation (`i32.const 0`, `i32.const 0`,
`i32.const 0`, `memory.init`, `data.drop`) and then the start call. -/
theorem exMemC₀_length : exMemC₀.code.length = 6 := by
  have h : exMemPrep.1.code.length = 5 := Silmaril.Proofs.Wasm.Game.Examples.exMem_cl
  have hs : exMemPrep.2 = some ⟨1⟩ := by decide +kernel
  simp only [exMemC₀, hs, Config.withStart, List.length_append, h, List.length_singleton]

/-- The headline adequacy theorem for the memory-importing module. -/
theorem exMem_adequacy (P : Profile) (K : Env exMemI.E)
    (hK : ThrowsBelow K exMemI.store.exns.length) :
    instObs (exMemI.closedSpec P exMemC₀ K) = behavioursOf P (hostOf exMemI.imports K) exMemC₀ :=
  exMem_isSpecInstanceAt.adequacy_inst P K hK

end Silmaril.Wasm.Game.Examples
