module

public import Silmaril.Formats.JsonWire.Concrete.Defs

/-! # Proofs: concrete syntax over bytes (`Silmaril.Formats.JsonWire.Concrete.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWire.Concrete

open Silmaril.Formats.JsonWire
open Silmaril.Formats (Bytes)

theorem concrete?_fields {Ast Kind : Type} {source : Bytes} {ast : Ast}
    {events : List (Located Kind)} {cst : Concrete Ast Kind}
    (h : concrete? source ast events = some cst) :
    cst.source = source ∧ cst.ast = ast ∧ cst.events = events := by
  unfold concrete? at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, rfl, rfl⟩
    · contradiction
  · contradiction

theorem restrict_sound {Ast : Type} {decode : Bytes → Option Ast} {p : Profile Ast}
    {bytes : Bytes} {ast : Ast} (h : restrict decode p bytes = some ast) :
    decode bytes = some ast ∧ p.accepts bytes ast = true := by
  unfold restrict at h
  cases ha : decode bytes with
  | none => simp [ha] at h
  | some a =>
    simp only [ha] at h
    change (if p.accepts bytes a then some a else none) = some ast at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, by assumption⟩
    · contradiction

end Silmaril.Proofs.Formats.JsonWire.Concrete

end
