module

public import Silmaril.Project.WasmComponents.Versions.Defs
public import Silmaril.Project.Shapes.Component.Via.Thms
public import Silmaril.Wasi.Versions.Adapter.Defs

/-!
# WASI versions of registered releases: facts about the decoded terms

PROVED by kernel evaluation, on the terms of `Silmaril.Project.WasmComponents.Versions.Defs` (what
Silmaril's decoders give on the registered files, by compiled evaluation):

* `reactor_viaOk`, `command_viaOk`: both adapters' embedded worlds import only `wasi`
  interfaces on the `0.2` track, among them the interface of every function of the adapter slice
  (`Silmaril.Wasi.Versions.Adapter.importList`); every core import resolves to a world import at a
  compatible version that does not precede it; and every function of the slice is a core
  import.
* `reactor_mixed_versions`, `command_mixed_versions`: the core imports name exactly the versions
  `0.2.12` and `0.2.6`, and `0.2.6` only for `wasi:filesystem/preopens.get-directories`, which
  the world imports at `0.2.12`.
* `io_summary_upgrade`, `io_summary_not_downgrade`: the summary of `wasi:io@0.2.12` is an
  upgrade of that of `0.2.6`, and not conversely.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Versions

open Silmaril.Wasi Silmaril.Wasi.Versions
open Silmaril.Project.Shapes.Component
open Silmaril.Project.Components.SemVer

/-- The `0.2` version track, `0.2.0`. -/
abbrev v0_2 : Silmaril.Wasm.Wit.Version := ver 0 2 0

/-! ## The binaries' interfaces, on the decoded terms -/

theorem reactor_viaOk : ViaOk reactorWorld reactorImports "wasi" v0_2 Adapter.importList := by
  decide +kernel

theorem command_viaOk : ViaOk commandWorld commandImports "wasi" v0_2 Adapter.importList := by
  decide +kernel

/-- The core imports at the version `v`. -/
def importsAt (imps : List CoreImport) (v : String) : List CoreImport :=
  imps.filter fun p => p.1.bind (·.pkg.version) == some v

/-- Every interface import is at version `a` or `b`. -/
def onlyAt (imps : List CoreImport) (a b : String) : Bool :=
  imps.all fun p => p.1.all fun i => i.pkg.version == some a || i.pkg.version == some b

/-- `wasi:filesystem/preopens` at a version. -/
def preopens (v : String) : Silmaril.Wasm.Wit.Binary.IfaceName :=
  ⟨⟨"wasi", "filesystem", some v⟩, "preopens"⟩

/-- **Two WASI versions in one module**: the reactor's core imports name `0.2.12` and `0.2.6`,
the latter only for `get-directories`, whose interface the world imports at `0.2.12`. -/
theorem reactor_mixed_versions :
    onlyAt reactorImports "0.2.12" "0.2.6" = true ∧
    importsAt reactorImports "0.2.6" = [(some (preopens "0.2.6"), "get-directories")] ∧
    preopens "0.2.12" ∈ worldIfaces reactorWorld.2.2.1 := by
  decide +kernel

/-- The same for the command adapter. -/
theorem command_mixed_versions :
    onlyAt commandImports "0.2.12" "0.2.6" = true ∧
    importsAt commandImports "0.2.6" = [(some (preopens "0.2.6"), "get-directories")] ∧
    preopens "0.2.12" ∈ worldIfaces commandWorld.2.2.1 := by
  decide +kernel

/-! ## `wasi:io`: 0.2.12 upgrades 0.2.6 -/

theorem io_summary_upgrade : SummaryUpgrade io026Summary io0212Summary := by decide +kernel

theorem io_summary_not_downgrade : ¬ SummaryUpgrade io0212Summary io026Summary := by
  decide +kernel

end Silmaril.Project.WasmComponents.Versions

end
