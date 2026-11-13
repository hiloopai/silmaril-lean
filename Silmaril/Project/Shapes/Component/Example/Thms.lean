module

public import Silmaril.Project.Shapes.Component.Thms
public import Silmaril.Wasm.Component.Binary.Example.Defs
public import Silmaril.Wasm.Component.Example.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Thms
public import Silmaril.Wasi.Examples.Thms

/-! # Standard problem shapes: WebAssembly components (examples and rows)

Small proved instances of every component shape, on the library's existing example components:

* **valid, has world** (binary): the hand-built component `Binary.Example.compB` (import
  `get : func() -> u32`, export `run`) is well scoped (`compB_valid`) and its WIT projection is
  `compBWorld` (`compB_hasWorld`); refuted: it does not have the empty world
  (`compB_not_empty_world`). Both by kernel evaluation of the projection.
* **has IR world**: the toy IR component `Component.Example.compB ftU32` imports `get` and
  exports `run` (`toyB_hasIRWorld`).
* **WASI theory, every host**: the clock checker of `Silmaril.Wasi.Examples` meets
  "`check` returns `true`" under the monotonic clock theory (`checker_wasiSat`), hence over
  every host of the theory (`checker_everyHost`); refuted with no theory
  (`checker_not_wasiSat_top`).
* **refines a spec**: the checker refines the loosest model of its contract
  (`checker_refines_spec`).
* **upgrade-compatible**: the checker (world `clocksWorld`) is an upgrade of the loosest model
  of its contract at the larger world `clocksInCli` (all the imports of `wasi:cli`)
  (`checker_upgrades_spec`); and every release upgrades itself (`UpgradeCompatible.refl`).
* **behavioural equality**: for every IR component, its flattening (a different component, so
  a different digest) has the same WASI model under every core semantics and layout
  (`flatten_behaviourEq`); two releases with one format and one digest behave the same
  (`digestBehaviourEq_self`).

Rows (`silmaril instance`) of `wasi_sat` (SAT and UNS), `refines`, `upgrade_compatible`,
`valid` and `has_world` are registered under `silmaril.shapes.component.examples`, with the
group `silmaril.shapes.component` of the shapes.

Not here: rows on registered component *values* (bytes), which need the `wasm.component`
format; a byte-level example fails to reduce by `rfl` (`Binary.parse` does not evaluate in the
kernel), so the value rows wait for that format's decision procedure.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component.Example

open CategoryTheory Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Examples
open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Wasm.Wit.Project (WorldType)

/-! ## Binary components: valid, has world -/

/-- The world of `Binary.Example.compB`: the type `func() -> u32`, the import `get` and the
export `run` of that type. -/
def compBWorld : WorldType :=
  [.inst (.type Silmaril.Wasm.Component.Binary.Example.getTy), .import ↑"get" (.func 0),
    .inst (.export ↑"run" (.func 0))]

theorem compB_valid : CompValid Silmaril.Wasm.Component.Binary.Example.compB := by
  unfold CompValid
  decide +kernel

theorem compB_hasWorld : HasWorld Silmaril.Wasm.Component.Binary.Example.compB compBWorld :=
  ⟨compBWorld, rfl, rfl⟩

/-- A refutation: `compB` imports and exports something. -/
theorem compB_not_empty_world : ¬ HasWorld Silmaril.Wasm.Component.Binary.Example.compB [] := by
  rintro ⟨w, hw, hn⟩
  have h : w = compBWorld := Option.some.inj (hw.symm.trans rfl)
  subst h
  cases hn

/-- The toy consumer of the IR imports `get` and exports `run`. -/
theorem toyB_hasIRWorld :
    HasIRWorld (Silmaril.Wasm.Component.Example.compB Silmaril.Wasm.Component.Example.ftU32)
      ⟨[("get", Silmaril.Wasm.Component.Example.ftU32)],
        [("run", Silmaril.Wasm.Component.Example.ftU32)]⟩ :=
  rfl

/-! ## WASI theories -/

/-- **The clock checker under the monotonic clock theory** returns `true`. -/
theorem checker_wasiSat : WasiSat (ofBody checker) clockTh (onExp retTrue) := checker_sat

/-- **Over every host of the clock theory.** -/
theorem checker_everyHost : WasiEveryHost (ofBody checker) clockTh retTrue :=
  checker_wasiSat.everyHost

/-- A refutation: with no assumption on the clock, the checker can return `false`. -/
theorem checker_not_wasiSat_top : ¬ WasiSat (ofBody checker) topP (onExp retTrue) :=
  checker_needs_theory

/-! ## Refinement and upgrades -/

/-- **The checker refines the loosest model of its contract.** -/
theorem checker_refines_spec :
    Refines (ofBody checker) (agSpec (W := clocksWorld) clockTh (onExp retTrue)) :=
  Refines.of_wasiSat checker_wasiSat

/-- **An upgrade to a smaller world**: the checker (importing only the clock) is compatible
with the loosest model of its contract at the world importing all of `wasi:cli`. -/
theorem checker_upgrades_spec :
    UpgradeCompatible toClocks (ofBody checker) (agSpec (W := clocksInCli) clockTh (onExp retTrue)) :=
  Refines.of_wasiSat checker_in_cli

/-! ## Behavioural equality -/

/-- **Different components, one behaviour**: an IR component and its flattening have the same
WASI model under every core semantics and layout. -/
theorem flatten_behaviourEq {M : Type} [Silmaril.Wasm.Component.CoreModule M]
    (C : Silmaril.Wasm.Component.CoreSem M) (L : Layout) (c : Silmaril.Wasm.Component.Comp M) :
    BehaviourEq (L.view ((Silmaril.Wasm.Component.flatten c).denU C)) (L.compModel C c) :=
  congrArg L.view (Silmaril.Wasm.Component.denU_flatten' C c)

/-- **One digest, one behaviour**: a release that decodes behaves like itself under every
denotation (`DigestBehaviourEq.of_bytes_eq` with equal bytes). -/
theorem digestBehaviourEq_self {V : Type} {W : World} (den : V → W.Model) (X : Value V)
    (hp : X.Parses) : DigestBehaviourEq den X X :=
  DigestBehaviourEq.of_bytes_eq rfl rfl hp

end Silmaril.Project.Shapes.Component.Example

end

/-! ## Rows -/

silmaril instance silmaril.shapes.component.examples.comp_b.valid := silmaril.shapes.component.valid
  (c := Silmaril.Wasm.Component.Binary.Example.compB)
silmaril instance silmaril.shapes.component.examples.comp_b.world := silmaril.shapes.component.has_world
  (c := Silmaril.Wasm.Component.Binary.Example.compB)
  (W := Silmaril.Project.Shapes.Component.Example.compBWorld)
silmaril instance silmaril.shapes.component.examples.checker.clock (expect := "THM") :=
  silmaril.shapes.component.wasi_sat (σ := Silmaril.Wasi.ofBody Silmaril.Wasi.Examples.checker)
  (T := Silmaril.Wasi.clockTh) (G := Silmaril.Wasi.onExp Silmaril.Wasi.retTrue)
silmaril instance silmaril.shapes.component.examples.checker.no_theory (expect := "UNS") :=
  silmaril.shapes.component.wasi_sat (σ := Silmaril.Wasi.ofBody Silmaril.Wasi.Examples.checker)
  (T := Silmaril.Wasi.topP) (G := Silmaril.Wasi.onExp Silmaril.Wasi.retTrue)
silmaril instance silmaril.shapes.component.examples.checker.every_host :=
  silmaril.shapes.component.wasi_every_host (σ := Silmaril.Wasi.ofBody Silmaril.Wasi.Examples.checker)
  (T := Silmaril.Wasi.clockTh) (G := Silmaril.Wasi.retTrue)
silmaril instance silmaril.shapes.component.examples.checker.refines_spec :=
  silmaril.shapes.component.refines (impl := Silmaril.Wasi.ofBody Silmaril.Wasi.Examples.checker)
  (spec := Silmaril.Project.Shapes.Component.agSpec (W := Silmaril.Wasi.clocksWorld) Silmaril.Wasi.clockTh
    (Silmaril.Wasi.onExp Silmaril.Wasi.retTrue))
silmaril instance silmaril.shapes.component.examples.checker.upgrade :=
  silmaril.shapes.component.upgrade_compatible (f := Silmaril.Wasi.Examples.toClocks)
  (v₂ := Silmaril.Wasi.ofBody Silmaril.Wasi.Examples.checker)
  (v₁ := Silmaril.Project.Shapes.Component.agSpec (W := Silmaril.Wasi.Examples.clocksInCli)
    Silmaril.Wasi.clockTh (Silmaril.Wasi.onExp Silmaril.Wasi.retTrue))

@[answers "silmaril.shapes.component.examples.comp_b.valid" thm]
theorem Silmaril.Project.Shapes.Component.Example.row_compB_valid :
    silmaril.shapes.component.examples.comp_b.valid :=
  Silmaril.Project.Shapes.Component.Example.compB_valid

@[answers "silmaril.shapes.component.examples.comp_b.world" thm]
theorem Silmaril.Project.Shapes.Component.Example.row_compB_world :
    silmaril.shapes.component.examples.comp_b.world :=
  Silmaril.Project.Shapes.Component.Example.compB_hasWorld

@[answers "silmaril.shapes.component.examples.checker.clock" thm]
theorem Silmaril.Project.Shapes.Component.Example.row_checker_clock :
    silmaril.shapes.component.examples.checker.clock :=
  Silmaril.Project.Shapes.Component.Example.checker_wasiSat

@[answers "silmaril.shapes.component.examples.checker.no_theory" uns]
theorem Silmaril.Project.Shapes.Component.Example.row_checker_no_theory :
    ¬ silmaril.shapes.component.examples.checker.no_theory :=
  Silmaril.Project.Shapes.Component.Example.checker_not_wasiSat_top

@[answers "silmaril.shapes.component.examples.checker.every_host" thm]
theorem Silmaril.Project.Shapes.Component.Example.row_checker_every_host :
    silmaril.shapes.component.examples.checker.every_host :=
  Silmaril.Project.Shapes.Component.Example.checker_everyHost

@[answers "silmaril.shapes.component.examples.checker.refines_spec" thm]
theorem Silmaril.Project.Shapes.Component.Example.row_checker_refines_spec :
    silmaril.shapes.component.examples.checker.refines_spec :=
  Silmaril.Project.Shapes.Component.Example.checker_refines_spec

@[answers "silmaril.shapes.component.examples.checker.upgrade" thm]
theorem Silmaril.Project.Shapes.Component.Example.row_checker_upgrade :
    silmaril.shapes.component.examples.checker.upgrade :=
  Silmaril.Project.Shapes.Component.Example.checker_upgrades_spec

silmaril group silmaril.shapes.component.examples
  (title := "Wasm component shapes: rows on the library's example components")
  (children := [silmaril.shapes.component.examples.comp_b.valid,
    silmaril.shapes.component.examples.comp_b.world,
    silmaril.shapes.component.examples.checker.clock,
    silmaril.shapes.component.examples.checker.no_theory,
    silmaril.shapes.component.examples.checker.every_host,
    silmaril.shapes.component.examples.checker.refines_spec,
    silmaril.shapes.component.examples.checker.upgrade])

silmaril group silmaril.shapes.component
  (title := "Standard problem shapes: WebAssembly components")
  (children := [silmaril.shapes.component.valid, silmaril.shapes.component.has_world,
    silmaril.shapes.component.has_ir_world, silmaril.shapes.component.wasi_sat,
    silmaril.shapes.component.wasi_every_host, silmaril.shapes.component.refines,
    silmaril.shapes.component.upgrade_compatible, silmaril.shapes.component.behaviour_eq,
    silmaril.shapes.component.digest_behaviour_eq, silmaril.shapes.component.examples])

/-! Every node is `detached`: the single root is the project
self-test, and a node of a dumped module must be reachable from it or detached. -/
silmaril detached silmaril.shapes.component (reason := "shape library")
silmaril detached silmaril.shapes.component.behaviour_eq (reason := "shape library")
silmaril detached silmaril.shapes.component.digest_behaviour_eq (reason := "shape library")
silmaril detached silmaril.shapes.component.examples (reason := "shape library")
silmaril detached silmaril.shapes.component.examples.checker.clock (reason := "shape library")
silmaril detached silmaril.shapes.component.examples.checker.every_host (reason := "shape library")
silmaril detached silmaril.shapes.component.examples.checker.no_theory (reason := "shape library")
silmaril detached silmaril.shapes.component.examples.checker.refines_spec (reason := "shape library")
silmaril detached silmaril.shapes.component.examples.checker.upgrade (reason := "shape library")
silmaril detached silmaril.shapes.component.examples.comp_b.valid (reason := "shape library")
silmaril detached silmaril.shapes.component.examples.comp_b.world (reason := "shape library")
silmaril detached silmaril.shapes.component.has_ir_world (reason := "shape library")
silmaril detached silmaril.shapes.component.has_world (reason := "shape library")
silmaril detached silmaril.shapes.component.refines (reason := "shape library")
silmaril detached silmaril.shapes.component.upgrade_compatible (reason := "shape library")
silmaril detached silmaril.shapes.component.valid (reason := "shape library")
silmaril detached silmaril.shapes.component.wasi_every_host (reason := "shape library")
silmaril detached silmaril.shapes.component.wasi_sat (reason := "shape library")
