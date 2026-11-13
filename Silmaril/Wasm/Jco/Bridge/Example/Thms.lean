module

public import Silmaril.Wasm.Jco.Bridge.Thms

/-!
# The bridge on a litmus module

`adder` is the pure module exporting `add : [i32, i32] → [i32]`, and `addMeta` the world
`add: func(a: u32, b: u32) -> u32`. The common answer on `(2, 3)` is `5` (`pureCall_adder`, by
evaluation). So the IR component of the simple FFI style answers `vals [u32 5]`
(`adder_ir`), and `wrap addMeta` over the module's instance returns `5` (`adder_wrap`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Bridge.Example

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Fuse
open Silmaril.Wasm.Jco (PTy PVal Meta wrap)

/-- The `add` function on flat values. -/
def addFn : String → List Flat → Option (List Flat)
  | "add", [⟨.int .i32, a⟩, ⟨.int .i32, b⟩] => some [Flat.i32 (a + b)]
  | _, _ => none

/-- A pure module exporting `add`. -/
def adder : PMod := ⟨[("add", ⟨[.int .i32, .int .i32], [.int .i32]⟩)], addFn⟩

/-- The world `add: func(a: u32, b: u32) -> u32`. -/
def addMeta : Meta := { world := [⟨"add", [.val .u32, .val .u32], some (.val .u32)⟩] }

theorem addMeta_memFree : addMeta.memFree = true := rfl

theorem pureCall_adder :
    pureCall adder ⟨"add", [.val .u32, .val .u32], some (.val .u32)⟩ [.u32 2, .u32 3] =
      some (some (.val (.u32 5))) := by
  rfl

/-- The IR component answers `5`. -/
theorem adder_ir :
    (simpleComp [] (Meta.iface addMeta) adder).denU (baseSem pureSem) =
        Strategy.ofHandler (fun q => .pure (bridgeAns addMeta adder q)) ∧
      bridgeAns addMeta adder (0, .vals [.u32 2, .u32 3]) = some (.vals [.u32 5]) :=
  ⟨simpleComp_bridge addMeta adder addMeta_memFree, by rfl⟩

/-- `wrap addMeta` over the module's instance returns `5`. -/
theorem adder_wrap :
    (wrap addMeta).callExport adder.inst "add" ([Val.u32 2, .u32 3].map PVal.val) =
      Silmaril.Wasm.Jco.RM.ofOption (some (some (.val (.u32 5)))) := by
  rw [wrap_pure addMeta adder addMeta_memFree]
  rfl

end Silmaril.Wasm.Jco.Bridge.Example
