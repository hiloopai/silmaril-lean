module

public import Silmaril.Project.Formats.SExp.Defs

/-! # Proofs of the S-expression format laws (restated in `Silmaril.Project.Formats.SExp.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Project.Formats

open Silmaril.Formats Silmaril.Project Silmaril.Project.Formats

theorem sexp_roundtrip : sexp.RoundTrip := by
  rintro p hp v a ha
  cases hp
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp ha
  change String.fromUTF8? s.toUTF8 >>= SExpParser.parseSExp? = some v
  rw [show String.fromUTF8? s.toUTF8 = some s by
    simp [String.fromUTF8?, String.fromUTF8, s.isValidUTF8]]
  exact SExpPrinter.printSExp?_sound hs

end Silmaril.Proofs.Project.Formats
