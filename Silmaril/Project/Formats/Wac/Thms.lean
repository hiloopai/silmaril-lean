module

public import Silmaril.Project.Formats.Wac.Defs
public import Silmaril.Project.Formats.Component.Thms
public import Silmaril.Project.Formats.Wit.Thms
public import Silmaril.Wasm.Wac.Text.Thms

/-!
# Formats `wac.*`: laws

* `wacText_roundtrip` (law `roundtrip`), from `Wac.Text.parse_print`: a well-formed document
  prints to UTF-8 that parses back to the same document (no normal form is needed).
* `wacComposition_roundtrip` (law `roundtrip`), from `Binary.parse_encode`, and
  `wacComposition_sound` (law `sound` for `WacCompositionRel`): a component of the grammar, in
  the composition profile.
* `wacWorld_sound`, `wacIR_sound` (law `sound`): the value is the surface world / the IR
  lowering of that component.
* `wacComposition_parse_iff`: `wac.composition` is `wasm.component.binary` restricted to the
  profile, so the two formats agree on compositions (`wacComposition_wasmComponent`).
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm

theorem wacText_roundtrip : wacText.RoundTrip := by
  intro p hp d b hb
  cases hp
  by_cases hw : Wac.Text.wf d = true
  · simp only [hw, ite_true] at hb
    cases hb
    simp only [wacText, fromUTF8?_toUTF8, Option.bind_some]
    exact Wac.Text.parse_print d hw
  · simp [hw] at hb

theorem wacComposition_parse_iff {b : Silmaril.Formats.Bytes} {c : Component.Binary.Ast} :
    wacComposition.parse b = some c ↔ wasmComponent.parse b = some c ∧ Wac.Profile c := by
  simp only [wacComposition, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨c', hc', h⟩
    by_cases hp : Wac.isProfile c' = true
    · simp only [hp, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨hc', hp⟩
    · simp [hp] at h
  · rintro ⟨hc, hp⟩
    exact ⟨c, hc, by simp [show Wac.isProfile c = true from hp]⟩

/-- A composition read under `wac.composition` reads the same under `wasm.component.binary`. -/
theorem wacComposition_wasmComponent {b : Silmaril.Formats.Bytes} {c : Component.Binary.Ast}
    (h : wacComposition.parse b = some c) : wasmComponent.parse b = some c :=
  (wacComposition_parse_iff.mp h).1

theorem wacComposition_sound : wacComposition.SoundFor WacCompositionRel := by
  intro b c h
  obtain ⟨hc, hp⟩ := wacComposition_parse_iff.mp h
  exact ⟨wasmComponent_sound _ _ hc, hp⟩

theorem wacComposition_roundtrip : wacComposition.RoundTrip := by
  intro p hp c b hb
  cases hp
  by_cases hpc : Wac.isProfile c = true
  · simp only [hpc, ite_true] at hb
    obtain ⟨bs, he, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact wacComposition_parse_iff.mpr
      ⟨wasmComponent_parse_eq.mpr (Component.Binary.parse_encode he), hpc⟩
  · simp [hpc] at hb

theorem wacWorld_sound : wacWorld.SoundFor WacWorldRel := by
  intro b w h
  simp only [wacWorld, Silmaril.Project.Format.andThen, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨c, hc, hw⟩ := h
  exact ⟨c, wacComposition_sound _ _ hc, hw⟩

theorem wacIR_sound : wacIR.SoundFor WacIRRel := by
  intro b m h
  simp only [wacIR, Silmaril.Project.Format.andThen, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, hm⟩ := h
  refine ⟨c, wacComposition_sound _ _ hc, ?_⟩
  cases he : Wac.Lower.toCompCore c with
  | error e => simp [he, Except.toOption] at hm
  | ok m' => simp_all [Except.toOption]

end Silmaril.Project.Formats

silmaril format_law wac.text roundtrip := Silmaril.Project.Formats.wacText_roundtrip
silmaril format_law wac.composition roundtrip := Silmaril.Project.Formats.wacComposition_roundtrip
silmaril format_law wac.composition sound := Silmaril.Project.Formats.wacComposition_sound
  (rel := Silmaril.Project.Formats.WacCompositionRel)
silmaril format_law wac.world sound := Silmaril.Project.Formats.wacWorld_sound
  (rel := Silmaril.Project.Formats.WacWorldRel)
silmaril format_law wac.ir sound := Silmaril.Project.Formats.wacIR_sound
  (rel := Silmaril.Project.Formats.WacIRRel)
