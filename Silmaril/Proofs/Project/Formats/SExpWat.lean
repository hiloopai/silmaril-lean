module

public import Silmaril.Project.Formats.SExpWat.Defs

/-! # Proof of the `sexp.wat` law (restated in `Silmaril.Project.Formats.SExpWat.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Project.Formats

open Silmaril.Formats.SExpEncoding Silmaril.Project Silmaril.Project.Formats

theorem sexpWat_sound : sexpWat.SoundFor SExpWatRel := by
  intro b doc h
  cases hs : String.fromUTF8? b.data with
  | none => simp [sexpWat, hs] at h
  | some s =>
    simp only [sexpWat, hs, Option.bind_eq_bind, Option.bind_some] at h
    exact ⟨s, hs, Wat.sexpWat_of_fullExec h⟩

end Silmaril.Proofs.Project.Formats
