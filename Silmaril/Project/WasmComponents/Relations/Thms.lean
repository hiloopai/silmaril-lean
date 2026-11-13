module

public import Silmaril.Project.WasmComponents.Relations.Defs
public import Silmaril.Project.Shapes.Component.Via.Defs
public import Silmaril.Project.WasmComponents.Thms
public import Silmaril.Wasi.Versions.P3OverP2.Impl.Thms
public import Silmaril.Wasi.Versions.P2OverP3.Comp.Thms
public import Silmaril.Wasi.Versions.P2OverP3.Sep.Thms

/-!
# The Wasm components pilot: WASI 0.3 via 0.2, and 0.2 via 0.3

Rows of `silmaril.shapes.component.implements_via` and `silmaril.shapes.component.wasi_sat` for the
version relations (b) and (c) of `docs/projects/wasm-wasi.md`, whose components are the stateful
models `Silmaril.Wasi.Versions.P3OverP2.p3OverP2` (WASI 0.3 driven by 0.2 streams, pollables and a
poll loop) and `Silmaril.Wasi.Versions.P2OverP3.p2OverP3 cap` (0.2 stream resources over 0.3
stream and future pairs, buffer size `cap`). The modules of the WASI-versions work are copied
unchanged; these rows restate its theorems:

* `p3_over_p2.implements_via` (THM): `p3OverP2` implements the corrected 0.3 theory `p3Th F`
  via the loose 0.2 theory with file contents `F` (`p2ThF F`), here at `F = noFiles`
  (`p3OverP2_model`, which holds for every `F`);
* `p2_over_p3.implements_via` (THM): `p2OverP3 4096` implements the loose 0.2 theory via the
  0.3 theory `p3Th` (`p2OverP3_model_p3`, every `cap`); `p2_over_p3.implements_via_clock`
  (THM): via the 0.3 clock theory alone (`p2OverP3_model`);
* `p2_over_p3.loose` (THM) and `p2_over_p3.strict` (UNS): as a guarantee on its returns under
  the 0.3 theories, the loose 0.2 reading holds (`p2OverP3_sat`) and the **strict** reading is
  refuted (`p2OverP3_not_strict`, a reachable play whose 0.3 answers satisfy `p3Th`; its
  separating host answers are not ones the reference machine gives, `docs/projects/wasm-wasi.md`).

These are about the models, which transcribe the designs; there are no binaries of these
components, so nothing ties a registered file to them.
-/

-- the rows
silmaril instance silmaril.wasm_components.p3_over_p2.implements_via (expect := "THM") :=
  silmaril.shapes.component.implements_via (σ := Silmaril.Wasi.Versions.P3OverP2.p3OverP2)
  (A := Silmaril.Wasi.Versions.P3OverP2.p3Th Silmaril.Project.WasmComponents.Relations.noFiles)
  (B := Silmaril.Wasi.Versions.P3OverP2.p2ThF Silmaril.Project.WasmComponents.Relations.noFiles)
silmaril instance silmaril.wasm_components.p2_over_p3.implements_via (expect := "THM") :=
  silmaril.shapes.component.implements_via (σ := Silmaril.Wasi.Versions.P2OverP3.p2OverP3 4096)
  (A := Silmaril.Wasi.Versions.P2.p2Th .loose) (B := Silmaril.Wasi.Versions.P2OverP3.p3Th)
silmaril instance silmaril.wasm_components.p2_over_p3.implements_via_clock (expect := "THM") :=
  silmaril.shapes.component.implements_via (σ := Silmaril.Wasi.Versions.P2OverP3.p2OverP3 4096)
  (A := Silmaril.Wasi.Versions.P2.p2Th .loose) (B := Silmaril.Wasi.Versions.P3.clockTh3)
silmaril instance silmaril.wasm_components.p2_over_p3.loose (expect := "THM") :=
  silmaril.shapes.component.wasi_sat (σ := Silmaril.Project.WasmComponents.Relations.p2OverP3Model)
  (T := Silmaril.Wasi.Versions.P3.clockTh3)
  (G := Silmaril.Wasi.Versions.retG (Silmaril.Wasi.Versions.P2.p2Th .loose))
silmaril instance silmaril.wasm_components.p2_over_p3.strict (expect := "UNS") :=
  silmaril.shapes.component.wasi_sat (σ := Silmaril.Project.WasmComponents.Relations.p2OverP3Model)
  (T := Silmaril.Wasi.Versions.P2OverP3.p3Th)
  (G := Silmaril.Wasi.Versions.retG (Silmaril.Wasi.Versions.P2.p2Th .strict))

@[expose] public section

namespace Silmaril.Project.WasmComponents.Relations

@[answers "silmaril.wasm_components.p3_over_p2.implements_via" thm]
theorem row_p3OverP2 : silmaril.wasm_components.p3_over_p2.implements_via :=
  fun _ _ hη => Silmaril.Wasi.Versions.P3OverP2.p3OverP2_model noFiles hη

@[answers "silmaril.wasm_components.p2_over_p3.implements_via" thm]
theorem row_p2OverP3 : silmaril.wasm_components.p2_over_p3.implements_via :=
  fun _ _ hη => Silmaril.Wasi.Versions.P2OverP3.p2OverP3_model_p3 4096 hη

@[answers "silmaril.wasm_components.p2_over_p3.implements_via_clock" thm]
theorem row_p2OverP3_clock : silmaril.wasm_components.p2_over_p3.implements_via_clock :=
  fun _ _ hη => Silmaril.Wasi.Versions.P2OverP3.p2OverP3_model 4096 hη

@[answers "silmaril.wasm_components.p2_over_p3.loose" thm]
theorem row_p2OverP3_loose : silmaril.wasm_components.p2_over_p3.loose :=
  Silmaril.Wasi.Versions.P2OverP3.p2OverP3_sat 4096

@[answers "silmaril.wasm_components.p2_over_p3.strict" uns]
theorem row_p2OverP3_strict : ¬ silmaril.wasm_components.p2_over_p3.strict :=
  Silmaril.Wasi.Versions.P2OverP3.p2OverP3_not_strict

end Silmaril.Project.WasmComponents.Relations

end

silmaril load "silmaril/wasm-components/relations-dag.toml"
