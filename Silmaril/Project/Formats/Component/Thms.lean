module

public import Silmaril.Project.Formats.Component.Defs
public import Silmaril.Project.Formats.Wasm.Thms
public import Silmaril.Wasm.Component.Binary.Thms
public import Silmaril.Data.IncludeBytes

/-!
# Formats `wasm.component.*`: laws and examples

* `wasmComponent_sound` (law `sound` for `ComponentRel`) from `Binary.parse_sound`, and
  `ComponentRel.functional` (the grammar is unambiguous, `componentG_functional`): the value a
  component file denotes is determined by its bytes and the grammar alone, not by the parser.
* `wasmComponent_roundtrip` (law `roundtrip`) from `Binary.parse_encode`: whatever the encoder
  writes parses back to the encoded component.
* `wasmComponentIR_sound`, `wasmComponentWorld_sound` (law `sound`): the IR and the world are
  the lowering and the projection of the component the grammar relates to the bytes.
* Examples on `examples/project-formats/component-run.wasm` (136 bytes, written by the library's  encoder from `Component.Binary.Example.compB` with an ascribed export, `gen-components.lean`):
  it parses (one kernel evaluation, about 3 s). That it lowers to the IR and has a world is
  checked by compiled code only (`gen-components.lean`): in the kernel the lowering takes
  about 9 s and the projection about 14 s on this file, over the module budget.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm.Component

theorem wasmComponent_parse_eq {b : Silmaril.Formats.Bytes} {c : Binary.Ast} :
    wasmComponent.parse b = some c ↔ Binary.parse b.data = .ok c := by
  simp only [wasmComponent]
  split <;> simp_all

theorem wasmComponent_sound : wasmComponent.SoundFor ComponentRel :=
  fun _ _ h => Binary.parse_sound (wasmComponent_parse_eq.mp h)

/-- The grammar relates a file to at most one component. -/
theorem ComponentRel.functional {b : Silmaril.Formats.Bytes} {c c' : Binary.Ast}
    (h : ComponentRel b c) (h' : ComponentRel b c') : c = c' :=
  Binary.componentG_functional h h'

theorem wasmComponent_roundtrip : wasmComponent.RoundTrip := by
  intro p hp c b hb
  cases hp
  obtain ⟨bs, he, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact wasmComponent_parse_eq.mpr (Binary.parse_encode he)

theorem wasmComponentIR_sound : wasmComponentIR.SoundFor ComponentIRRel := by
  intro b m h
  simp only [wasmComponentIR, Silmaril.Project.Format.andThen, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, hm⟩ := h
  refine ⟨c, wasmComponent_sound _ _ hc, ?_⟩
  split at hm <;> simp_all

theorem wasmComponentWorld_sound : wasmComponentWorld.SoundFor ComponentWorldRel := by
  intro b w h
  simp only [wasmComponentWorld, Silmaril.Project.Format.andThen, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, hw⟩ := h
  exact ⟨c, wasmComponent_sound _ _ hc, hw⟩

/-- `examples/project-formats/component-run.wasm`: import `get`, export `run`. -/
def runComponent : Silmaril.Formats.Bytes :=
  ⟨include_bytes "../../../../examples/project-formats/component-run.wasm"⟩

theorem runComponent_parses : (wasmComponent.parse runComponent).isSome = true := by
  decide +kernel

end Silmaril.Project.Formats

silmaril format_law wasm.component.binary sound := Silmaril.Project.Formats.wasmComponent_sound
  (rel := Silmaril.Project.Formats.ComponentRel)
silmaril format_law wasm.component.binary roundtrip := Silmaril.Project.Formats.wasmComponent_roundtrip
silmaril format_law wasm.component.ir sound := Silmaril.Project.Formats.wasmComponentIR_sound
  (rel := Silmaril.Project.Formats.ComponentIRRel)
silmaril format_law wasm.component.world sound := Silmaril.Project.Formats.wasmComponentWorld_sound
  (rel := Silmaril.Project.Formats.ComponentWorldRel)
