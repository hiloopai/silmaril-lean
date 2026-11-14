module

public import Silmaril.Project.WasmComponents.Versions.Terms.Thms
public import Silmaril.Project.WasmComponents.Thms
public import Silmaril.Project.Shapes.Component.Via.Thms
public import Silmaril.Wasi.Versions.Adapter.Thms
public import Silmaril.Wasi.Versions.Adapter.Over.Thms

/-!
# WASI versions of registered releases: the preview1 adapters and `wasi:io` upgrades

Rows of the shapes `silmaril.shapes.component.{implements_via, imports_via,
release_implements_via, wit_upgrade}` (`Silmaril.Project.Shapes.Component.Via`) on the pilot's
releases (`docs/projects/wasm-wasi.md`):

* the `wasi_snapshot_preview1` reactor and command adapters of wasmtime v50.0.1, read under
  `wasm.module.world` (their embedded world) and `wasm.binary.core` (their core imports);
* `wasi:io@0.2.6` (new, fetched from OCI by digest with `sil project components add`) and
  `wasi:io@0.2.12`, read under `wit.binary`.

**PROVED** (kernel):

* `slice_implementsVia`, `slice_implementsVia_p2_9`: the adapter slice of `Silmaril.Wasi.Versions`
  (a transcription of the adapter's `lib.rs`) implements `P1.th` via the 0.2.12 theory
  `Adapter.p2Th`, and via the 0.2.9 theory `P2.p2Th .loose` with `extraTh`.
* On the decoded terms (`Silmaril.Project.WasmComponents.Versions.Terms.Thms`): the adapters'
  imports are on the `0.2` track (`reactor_viaOk`, `command_viaOk`), with `0.2.6` only for
  `get-directories` (`reactor_mixed_versions`, `command_mixed_versions`); `wasi:io@0.2.12`
  upgrades `0.2.6` (`io_summary_upgrade`, `io_summary_not_downgrade`).

**CONDITIONAL**, on frozen `Task`s stating that Silmaril's decoders give these terms on the
registered files (`silmaril conjecture …`, open; `examples/wasm-components/gen/Versions.lean`
checks them by compiled evaluation, the kernel does not evaluate the decoders on 15 KB to
51 KB files): `reactor_importsVia_of`, `reactor_implementsVia_of` (and `command_…`),
`io_upgrade_of`, `io_not_downgrade_of`, registered as decompositions of the rows.

What these do not say: that the slice is the semantics of the adapter's bytes (Silmaril has no
semantics of this core module); the rows tie the slice to the binary by names and versions
only.

A Silmaril addition.
-/

open Silmaril.Project (Value)

-- `sil project components add` writes the registry after a cached `Silmaril.Project.Defs`
silmaril_artifacts_refresh "silmaril/artifacts.toml"
silmaril load "silmaril/wasm-components/versions.toml"

@[expose] public section

namespace Silmaril.Project.WasmComponents.Versions

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions
open Silmaril.Project.Shapes.Component
open Silmaril.Project.Components.SemVer

/-! ## The adapter slice: preview1 via 0.2 -/

/-- **Preview1 via 0.2.12**: the adapter slice, over every host of the adapter's 0.2 theory. -/
theorem slice_implementsVia : ImplementsVia Adapter.adapter P1.th Adapter.p2Th :=
  fun _ _ hη => Adapter.adapter_model hη

/-- **Preview1 via 0.2.9**: over every host of the loose 0.2.9 theory and `extraTh`. -/
theorem slice_implementsVia_p2_9 :
    ImplementsVia Adapter.adapter P1.th ((P2.p2Th .loose).prod Adapter.extraTh) :=
  fun _ _ hη => Adapter.adapter_model_p2
    (fun s hs => ((Silmaril.Wasm.Resource.Protocol.accepts_prod_iff _ _ _).1 (hη s hs)).1)
    (fun s hs => ((Silmaril.Wasm.Resource.Protocol.accepts_prod_iff _ _ _).1 (hη s hs)).2)

end Silmaril.Project.WasmComponents.Versions

end

/-! ## Open: the decoders on the registered files -/

namespace Silmaril.Project.WasmComponents.Versions

open Silmaril.Project.Shapes.Component

silmaril conjecture silmaril.wasm_components.versions.reactor_world
  (title := "The reactor adapter's embedded world decodes to reactorWorld") :
  silmaril.wasm_components.adapter.reactor.world.parse = some reactorWorld
silmaril conjecture silmaril.wasm_components.versions.reactor_imports
  (title := "The reactor adapter's core imports decode to reactorImports") :
  silmaril.wasm_components.adapter.reactor.parse.map coreImports = some reactorImports
silmaril conjecture silmaril.wasm_components.versions.command_world
  (title := "The command adapter's embedded world decodes to commandWorld") :
  silmaril.wasm_components.adapter.command.world.parse = some commandWorld
silmaril conjecture silmaril.wasm_components.versions.command_imports
  (title := "The command adapter's core imports decode to commandImports") :
  silmaril.wasm_components.adapter.command.parse.map coreImports = some commandImports
silmaril conjecture silmaril.wasm_components.versions.io_0_2_6_summary
  (title := "wasi:io@0.2.6 decodes to a package with summary io026Summary") :
  silmaril.wasm_components.wasi.io.v0_2_6.oci.parse.map summary = some io026Summary
silmaril conjecture silmaril.wasm_components.versions.io_0_2_12_summary
  (title := "wasi:io@0.2.12 decodes to a package with summary io0212Summary") :
  silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parse.map summary = some io0212Summary

end Silmaril.Project.WasmComponents.Versions

/-! ## Rows -/

silmaril instance silmaril.wasm_components.adapter.slice.implements_via (expect := "THM") :=
  silmaril.shapes.component.implements_via (σ := Silmaril.Wasi.Versions.Adapter.adapter)
  (A := Silmaril.Wasi.Versions.P1.th) (B := Silmaril.Wasi.Versions.Adapter.p2Th)
silmaril instance silmaril.wasm_components.adapter.slice.implements_via_p2_9 (expect := "THM") :=
  silmaril.shapes.component.implements_via (σ := Silmaril.Wasi.Versions.Adapter.adapter)
  (A := Silmaril.Wasi.Versions.P1.th)
  (B := (Silmaril.Wasi.Versions.P2.p2Th .loose).prod Silmaril.Wasi.Versions.Adapter.extraTh)
silmaril instance silmaril.wasm_components.adapter.reactor.imports_via :=
  silmaril.shapes.component.imports_via (X := silmaril.wasm_components.adapter.reactor.world)
  (M := silmaril.wasm_components.adapter.reactor) (ns := "wasi")
  (v := Silmaril.Project.WasmComponents.Versions.v0_2) (L := Silmaril.Wasi.Versions.Adapter.importList)
silmaril instance silmaril.wasm_components.adapter.command.imports_via :=
  silmaril.shapes.component.imports_via (X := silmaril.wasm_components.adapter.command.world)
  (M := silmaril.wasm_components.adapter.command) (ns := "wasi")
  (v := Silmaril.Project.WasmComponents.Versions.v0_2) (L := Silmaril.Wasi.Versions.Adapter.importList)
silmaril instance silmaril.wasm_components.adapter.reactor.implements_via :=
  silmaril.shapes.component.release_implements_via (X := silmaril.wasm_components.adapter.reactor.world)
  (M := silmaril.wasm_components.adapter.reactor) (ns := "wasi")
  (v := Silmaril.Project.WasmComponents.Versions.v0_2) (L := Silmaril.Wasi.Versions.Adapter.importList)
  (σ := Silmaril.Wasi.Versions.Adapter.adapter) (A := Silmaril.Wasi.Versions.P1.th)
  (B := Silmaril.Wasi.Versions.Adapter.p2Th)
silmaril instance silmaril.wasm_components.adapter.command.implements_via :=
  silmaril.shapes.component.release_implements_via (X := silmaril.wasm_components.adapter.command.world)
  (M := silmaril.wasm_components.adapter.command) (ns := "wasi")
  (v := Silmaril.Project.WasmComponents.Versions.v0_2) (L := Silmaril.Wasi.Versions.Adapter.importList)
  (σ := Silmaril.Wasi.Versions.Adapter.adapter) (A := Silmaril.Wasi.Versions.P1.th)
  (B := Silmaril.Wasi.Versions.Adapter.p2Th)
silmaril instance silmaril.wasm_components.wasi.io.upgrade_0_2_6_to_0_2_12 :=
  silmaril.shapes.component.wit_upgrade (X₁ := silmaril.wasm_components.wasi.io.v0_2_6.oci)
  (X₂ := silmaril.wasm_components.wasi.io.v0_2_12.oci.package)
silmaril instance silmaril.wasm_components.wasi.io.upgrade_0_2_12_to_0_2_6 :=
  silmaril.shapes.component.wit_upgrade (X₁ := silmaril.wasm_components.wasi.io.v0_2_12.oci.package)
  (X₂ := silmaril.wasm_components.wasi.io.v0_2_6.oci)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Versions

open Silmaril.Project.Shapes.Component

@[answers "silmaril.wasm_components.adapter.slice.implements_via" thm]
theorem row_slice : silmaril.wasm_components.adapter.slice.implements_via := slice_implementsVia

@[answers "silmaril.wasm_components.adapter.slice.implements_via_p2_9" thm]
theorem row_slice_p2_9 : silmaril.wasm_components.adapter.slice.implements_via_p2_9 :=
  slice_implementsVia_p2_9

/-- The reactor's imports are on the `0.2` track, given the two decodings. -/
theorem reactor_importsVia_of (hw : Task.silmaril.wasm_components.versions.reactor_world)
    (hm : Task.silmaril.wasm_components.versions.reactor_imports) :
    silmaril.wasm_components.adapter.reactor.imports_via :=
  ImportsVia.of_eqs (w := reactorWorld) (imps := reactorImports) hw hm reactor_viaOk

theorem command_importsVia_of (hw : Task.silmaril.wasm_components.versions.command_world)
    (hm : Task.silmaril.wasm_components.versions.command_imports) :
    silmaril.wasm_components.adapter.command.imports_via :=
  ImportsVia.of_eqs (w := commandWorld) (imps := commandImports) hw hm command_viaOk

/-- **The reactor adapter implements preview1 via WASI 0.2.x**, given the two decodings. -/
theorem reactor_implementsVia_of (hw : Task.silmaril.wasm_components.versions.reactor_world)
    (hm : Task.silmaril.wasm_components.versions.reactor_imports) :
    silmaril.wasm_components.adapter.reactor.implements_via :=
  ReleaseImplementsVia.of_eqs (w := reactorWorld) (imps := reactorImports) hw hm reactor_viaOk slice_implementsVia

/-- **The command adapter implements preview1 via WASI 0.2.x**, given the two decodings. -/
theorem command_implementsVia_of (hw : Task.silmaril.wasm_components.versions.command_world)
    (hm : Task.silmaril.wasm_components.versions.command_imports) :
    silmaril.wasm_components.adapter.command.implements_via :=
  ReleaseImplementsVia.of_eqs (w := commandWorld) (imps := commandImports) hw hm command_viaOk slice_implementsVia

/-- **`wasi:io@0.2.12` is an upgrade of `wasi:io@0.2.6`**, given the two decodings. -/
theorem io_upgrade_of (h₁ : Task.silmaril.wasm_components.versions.io_0_2_6_summary)
    (h₂ : Task.silmaril.wasm_components.versions.io_0_2_12_summary) :
    silmaril.wasm_components.wasi.io.upgrade_0_2_6_to_0_2_12 :=
  WitUpgrade.of_summaries (s₁ := io026Summary) (s₂ := io0212Summary) h₁ h₂ io_summary_upgrade

/-- **And not conversely**, given the two decodings. -/
theorem io_not_downgrade_of (h₁ : Task.silmaril.wasm_components.versions.io_0_2_6_summary)
    (h₂ : Task.silmaril.wasm_components.versions.io_0_2_12_summary) :
    ¬ silmaril.wasm_components.wasi.io.upgrade_0_2_12_to_0_2_6 := by
  rintro ⟨p₂, e₂, p₁, e₁, h⟩
  have h₁' : silmaril.wasm_components.wasi.io.v0_2_6.oci.parse.map summary = some io026Summary := h₁
  have h₂' : silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parse.map summary =
      some io0212Summary := h₂
  rw [e₂] at h₂'
  rw [e₁] at h₁'
  rw [Option.some.inj h₁', Option.some.inj h₂'] at h
  exact io_summary_not_downgrade h

end Silmaril.Project.WasmComponents.Versions

end

namespace Silmaril.Project.WasmComponents.Versions

silmaril decomposition := Silmaril.Project.WasmComponents.Versions.reactor_importsVia_of
silmaril decomposition := Silmaril.Project.WasmComponents.Versions.command_importsVia_of
silmaril decomposition := Silmaril.Project.WasmComponents.Versions.reactor_implementsVia_of
silmaril decomposition := Silmaril.Project.WasmComponents.Versions.command_implementsVia_of
silmaril decomposition := Silmaril.Project.WasmComponents.Versions.io_upgrade_of

silmaril group silmaril.wasm_components.versions
  (title := "WASI versions of the pilot's releases: the preview1 adapters and wasi:io upgrades")
  (children := [silmaril.wasm_components.adapter.slice.implements_via,
    silmaril.wasm_components.adapter.slice.implements_via_p2_9,
    silmaril.wasm_components.adapter.reactor.imports_via,
    silmaril.wasm_components.adapter.command.imports_via,
    silmaril.wasm_components.adapter.reactor.implements_via,
    silmaril.wasm_components.adapter.command.implements_via,
    silmaril.wasm_components.wasi.io.upgrade_0_2_6_to_0_2_12,
    silmaril.wasm_components.wasi.io.upgrade_0_2_12_to_0_2_6,
    silmaril.wasm_components.adapter.reactor.world.parses,
    silmaril.wasm_components.adapter.command.world.parses,
    silmaril.wasm_components.wasi.io.v0_2_6.oci.parses,
    silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parses])


/-! Every node is `detached`, as for the pilot: Silmaril's single root is the project self-test. -/
silmaril detached silmaril.wasm_components.versions (reason := "a case study")
silmaril detached silmaril.shapes.component.implements_via (reason := "a case study")
silmaril detached silmaril.shapes.component.imports_via (reason := "a case study")
silmaril detached silmaril.shapes.component.release_implements_via (reason := "a case study")
silmaril detached silmaril.shapes.component.wit_upgrade (reason := "a case study")
silmaril detached silmaril.wasm_components.adapter.slice.implements_via (reason := "a case study")
silmaril detached silmaril.wasm_components.adapter.slice.implements_via_p2_9 (reason := "a case study")
silmaril detached silmaril.wasm_components.adapter.reactor.imports_via (reason := "a case study")
silmaril detached silmaril.wasm_components.adapter.command.imports_via (reason := "a case study")
silmaril detached silmaril.wasm_components.adapter.reactor.implements_via (reason := "a case study")
silmaril detached silmaril.wasm_components.adapter.command.implements_via (reason := "a case study")
silmaril detached silmaril.wasm_components.wasi.io.upgrade_0_2_6_to_0_2_12 (reason := "a case study")
silmaril detached silmaril.wasm_components.wasi.io.upgrade_0_2_12_to_0_2_6 (reason := "a case study")
silmaril detached silmaril.wasm_components.wasi.io.v0_2_6.oci.parses (reason := "a case study")
silmaril detached silmaril.wasm_components.versions.reactor_world (reason := "a case study")
silmaril detached silmaril.wasm_components.versions.reactor_imports (reason := "a case study")
silmaril detached silmaril.wasm_components.versions.command_world (reason := "a case study")
silmaril detached silmaril.wasm_components.versions.command_imports (reason := "a case study")
silmaril detached silmaril.wasm_components.versions.io_0_2_6_summary (reason := "a case study")
silmaril detached silmaril.wasm_components.versions.io_0_2_12_summary (reason := "a case study")

end Silmaril.Project.WasmComponents.Versions
