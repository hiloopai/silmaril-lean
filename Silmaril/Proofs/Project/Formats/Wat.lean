module

public import Silmaril.Project.Formats.Wat.Defs
public import Silmaril.Project.Formats.Wasm.Thms
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound

/-! # Proofs of the `wat.sexp` lemmas (restated in `Silmaril.Project.Formats.Wat.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Project.Formats

open Silmaril.Wasm Silmaril.Wasm.Binaryen.Toolkit Silmaril.Project Silmaril.Project.Formats

theorem wat_sound : wat.SoundFor WatRel := by
  intro b m h
  cases hs : String.fromUTF8? b.data with
  | none => simp [wat, Format.andThen, sexpWat, hs] at h
  | some s =>
    cases hd : Silmaril.Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 s with
    | none => simp [wat, Format.andThen, sexpWat, hs, hd] at h
    | some doc =>
      simp only [wat, Format.andThen, sexpWat, hs, hd, Option.bind_eq_bind,
        Option.bind_some] at h
      exact ⟨s, hs, doc, Silmaril.Formats.SExpEncoding.Wat.sexpWat_of_fullExec hd,
        Wat.parseSupported?_sound h⟩

theorem wat_print_sound {p} (hp : wat.print = some p) {m : Silmaril.Wasm.Module}
    {b : Silmaril.Formats.Bytes} (h : p m = some b) :
    ∃ s, b = ⟨s.toUTF8⟩ ∧ Text.Core.Encodes s m := by
  cases hp
  cases hd : Wat.moduleSyntax? m with
  | none => simp [hd] at h
  | some doc =>
    cases hr : renderWatDocument? doc with
    | none => simp [hd, hr] at h
    | some s =>
      simp only [hd, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      cases h
      exact ⟨s, rfl, doc, renderWatDocument?_sound hr, Wat.moduleSyntax?_sound hd⟩

theorem wat_wasm_equivalent_of_encodes {a b : Silmaril.Formats.Bytes}
    (hb : (wasm.parse b).isSome = true)
    (he : ((wat.parse a).bind fun m => (Binaryen.Exe.encodeModule? m).toOption) =
      some b.toList) :
    Equivalent wat wasm a b := by
  cases ha : wat.parse a with
  | none => rw [ha] at he; cases he
  | some m =>
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hb
    rw [ha, Option.bind_some] at he
    have henc : Binary.Core.Encodes b.toList m := by
      cases hx : Binaryen.Exe.encodeModule? m with
      | error => simp [hx, Except.toOption] at he
      | ok bs =>
        simp only [hx, Except.toOption, Option.some.injEq] at he
        exact he ▸ Binaryen.Exe.encodeModule?_sound hx
    exact ⟨m, ha, hm'.trans (congrArg some (Binary.Core.functional (wasm_sound _ _ hm') henc))⟩

end Silmaril.Proofs.Project.Formats
