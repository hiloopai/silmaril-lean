module

public import Silmaril.Project.WasmComponents.Wac.Thms
public import Silmaril.Project.Shapes.Component.WacElab.Thms

/-!
# The Wasm components pilot: typed targets and behaviour of the WAC composition

**Typed targets** (shape `silmaril.shapes.component.wac_has_typed_world`, component subtyping as
wac-types' `validate_target` checks it). The typed world of `Wac.pilot` is computed once
(`pilot_typedWorld`: no imports, the export `run : func() -> u32`, typed from the WIT
projections of the two embedded packages); the rows compare it with four target worlds:

| row | world | verdict |
|---|---|---|
| `typed_app` | `app`: export `run: func() -> u32` | THM |
| `typed_app_with_log` | also imports `log: func(msg: u32)` | THM (the composition imports less) |
| `typed_app_u64` | export `run: func() -> u64` | UNS (by names and sorts it fits: `untyped_app_u64`) |
| `typed_app_and_stop` | also exports `stop: func()` | UNS |

`typed_app_u64` is where types matter: the names-and-sorts check of `wac_has_world` accepts
the world (`untyped_app_u64`, its world erases to `appWorld`), the typed check does not.
`typedApp_untyped` recovers the untyped row `has_world` from the typed one
(`WacHasTypedWorld.wacHasWorld`).

**Behaviour** (shape `silmaril.shapes.component.digest_behaviour_eq`): the composition
`wac.pilot.composed` and the hand-linked `gen.linked` (`Binary.Example.linked`, producer and
consumer in one component) have the same denotation `wacDen C L` under **every** core
semantics `C` and names `L` (`composed_linked_behaviourEq`): the WAC lowering of the
composition and the `Binary.lower` lowering of `linked` flatten to the same flat component
(`sameFlat`, one kernel evaluation), and flattening preserves the denotation
(`Silmaril.Wasm.Component.denU_flatten'`). The row takes `C = topSem` and the layout `runLayout`.
Two digests, one behaviour: the files differ (one nests two components, the other has two core
modules side by side).
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Wac

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Project.Shapes.Component
open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Wasm.Wac (Kind)
open Silmaril.Wasm.Wac.World (WorldK)

/-- `func() -> u32`. -/
def runSig : Wit.Binary.Sig := ⟨false, [], some (.prim .u32)⟩

/-- `func() -> u64`. -/
def runSigU64 : Wit.Binary.Sig := ⟨false, [], some (.prim .u64)⟩

/-- `func()`. -/
def stopSig : Wit.Binary.Sig := ⟨false, [], none⟩

/-- `func(msg: u32)`. -/
def logSig : Wit.Binary.Sig := ⟨false, [("msg", .prim .u32)], none⟩

/-- The typed world `app`: the export `run: func() -> u32`. -/
def appTyped : WorldK := ([], [("run", .func runSig)])

/-- `app` with the import `log: func(msg: u32)`. -/
def appWithLogTyped : WorldK := ([("log", .func logSig)], [("run", .func runSig)])

/-- The export `run: func() -> u64`. -/
def appU64Typed : WorldK := ([], [("run", .func runSigU64)])

/-- `app-and-stop`: the exports `run: func() -> u32` and `stop: func()`. -/
def appAndStopTyped : WorldK := ([], [("run", .func runSig), ("stop", .func stopSig)])

/-- The typed world of the composition. -/
def pilotTyped : WorldK := ([], [("run", .func runSig)])

theorem pilot_typedWorld_check :
    (match typedWorld [] pilot with
      | .ok cw => decide (cw = pilotTyped)
      | .error _ => false) = true := by decide +kernel

theorem pilot_typedWorld : typedWorld [] pilot = .ok pilotTyped := by
  have h := pilot_typedWorld_check
  split at h
  · rename_i cw hcw
    rw [hcw, of_decide_eq_true h]
  · cases h

theorem pilot_typed_iff (W : WorldK) :
    WacHasTypedWorld [] pilot W ↔ Wac.World.sat pilotTyped W = true := by
  rw [Wac.World.sat_iff]
  constructor
  · rintro ⟨_, cw, hcw, hs⟩
    rw [pilot_typedWorld] at hcw
    cases hcw
    exact hs
  · exact fun hs => ⟨pilot_profile, pilotTyped, pilot_typedWorld, hs⟩

/-- A row of `wac_has_typed_world` on the composed file, from one kernel `Bool`. -/
theorem composed_typed {W : WorldK} (h : Wac.World.sat pilotTyped W = true) :
    silmaril.wasm_components.wac.pilot.composed.Satisfies (fun c => WacHasTypedWorld [] c W) :=
  Silmaril.Project.Value.satisfies_of_is composed_is ((pilot_typed_iff W).mpr h)

/-- A refutation of `wac_has_typed_world` on the composed file, from one kernel `Bool`. -/
theorem composed_not_typed {W : WorldK} (h : Wac.World.sat pilotTyped W = false) :
    ¬ silmaril.wasm_components.wac.pilot.composed.Satisfies (fun c => WacHasTypedWorld [] c W) :=
  fun hs => by
    have := (pilot_typed_iff W).mp ((Silmaril.Project.Value.Is.satisfies_iff composed_is).mp hs)
    rw [h] at this
    cases this

/-- The untyped check accepts `run: func() -> u64`: it has the names and sorts of `app`. -/
theorem untyped_app_u64 : WacHasWorld pilot appWorld ∧
    Wac.World.erase (Wac.World.promoteEx appU64Typed.2) = Wac.Targets.exports appWorld := by
  exact ⟨pilot_hasWorld, by decide +kernel⟩

/-- The typed row gives the untyped one (`has_world`). -/
theorem typedApp_untyped : WacHasWorld pilot appWorld :=
  WacHasTypedWorld.wacHasWorld ((pilot_typed_iff appTyped).mpr (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

/-! ## Behaviour -/

/-- The layout of a component importing nothing and exporting one function `run`. -/
def runLayout : Silmaril.Wasi.Layout := ⟨[], [⟨"", "run"⟩]⟩

/-- The denotation of the rows: `wacDen` at the loosest core semantics and `runLayout`. -/
def pilotDen : Ast → runLayout.world.Model := wacDen Silmaril.Project.WasmComponents.topSem runLayout

/-- The composition and `linked` flatten to the same flat component. -/
theorem pilot_linked_sameFlat : sameFlat pilot Binary.Example.linked = true := by decide +kernel

/-- **The composition and `linked` behave the same, under every core semantics and names.** -/
theorem composed_linked_behaviourEq
    (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Silmaril.Wasi.Layout) :
    DigestBehaviourEq (wacDen C L) silmaril.wasm_components.wac.pilot.composed
      silmaril.wasm_components.gen.linked :=
  DigestBehaviourEq.of_sameFlat composed_is Silmaril.Project.WasmComponents.linked_is
    pilot_linked_sameFlat C L

end Silmaril.Project.WasmComponents.Wac

end

-- the rows
silmaril instance silmaril.wasm_components.wac.pilot.composed.typed_app (expect := "THM") :=
  silmaril.shapes.component.wac_has_typed_world (imps := []) (c := silmaril.wasm_components.wac.pilot.composed)
  (W := Silmaril.Project.WasmComponents.Wac.appTyped)
silmaril instance silmaril.wasm_components.wac.pilot.composed.typed_app_with_log (expect := "THM") :=
  silmaril.shapes.component.wac_has_typed_world (imps := []) (c := silmaril.wasm_components.wac.pilot.composed)
  (W := Silmaril.Project.WasmComponents.Wac.appWithLogTyped)
silmaril instance silmaril.wasm_components.wac.pilot.composed.typed_app_u64 (expect := "UNS") :=
  silmaril.shapes.component.wac_has_typed_world (imps := []) (c := silmaril.wasm_components.wac.pilot.composed)
  (W := Silmaril.Project.WasmComponents.Wac.appU64Typed)
silmaril instance silmaril.wasm_components.wac.pilot.composed.typed_app_and_stop (expect := "UNS") :=
  silmaril.shapes.component.wac_has_typed_world (imps := []) (c := silmaril.wasm_components.wac.pilot.composed)
  (W := Silmaril.Project.WasmComponents.Wac.appAndStopTyped)
silmaril instance silmaril.wasm_components.wac.pilot_linked.behaviour_eq (expect := "THM") :=
  silmaril.shapes.component.digest_behaviour_eq (den := Silmaril.Project.WasmComponents.Wac.pilotDen)
  (X := silmaril.wasm_components.wac.pilot.composed) (Y := silmaril.wasm_components.gen.linked)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Wac

@[answers "silmaril.wasm_components.wac.pilot.composed.typed_app" thm]
theorem row_typed_app : silmaril.wasm_components.wac.pilot.composed.typed_app :=
  composed_typed (by decide +kernel)

@[answers "silmaril.wasm_components.wac.pilot.composed.typed_app_with_log" thm]
theorem row_typed_app_with_log : silmaril.wasm_components.wac.pilot.composed.typed_app_with_log :=
  composed_typed (by decide +kernel)

@[answers "silmaril.wasm_components.wac.pilot.composed.typed_app_u64" uns]
theorem row_typed_app_u64 : ¬ silmaril.wasm_components.wac.pilot.composed.typed_app_u64 :=
  composed_not_typed (by decide +kernel)

@[answers "silmaril.wasm_components.wac.pilot.composed.typed_app_and_stop" uns]
theorem row_typed_app_and_stop : ¬ silmaril.wasm_components.wac.pilot.composed.typed_app_and_stop :=
  composed_not_typed (by decide +kernel)

@[answers "silmaril.wasm_components.wac.pilot_linked.behaviour_eq" thm]
theorem row_pilot_linked_behaviourEq : silmaril.wasm_components.wac.pilot_linked.behaviour_eq :=
  composed_linked_behaviourEq Silmaril.Project.WasmComponents.topSem runLayout

end Silmaril.Project.WasmComponents.Wac

end
