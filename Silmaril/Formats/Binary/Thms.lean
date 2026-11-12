module
public import Silmaril.Formats.Binary.Defs
@[expose] public section
namespace Silmaril.Formats

/-- A concrete event stream has exactly one serialization. -/
theorem Concrete.serialization_unique {Ast Kind : Type} (cst : Concrete Ast Kind)
    {left right : Bytes} (hl : serialize? cst.source cst.events = some left)
    (hr : serialize? cst.source cst.events = some right) : left = right :=
  Option.some.inj (hl.symm.trans hr)

theorem Concrete.serialize {Ast Kind : Type} (cst : Concrete Ast Kind) :
    serialize? cst.source cst.events = some cst.source := cst.lossless

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

theorem restrict_slice {Ast : Type} {decode : Bytes → Option Ast} {p : Profile Ast}
    {bytes : Bytes} (h : IsSlice (restrict decode p) bytes) : IsSlice decode bytes := by
  obtain ⟨ast, ha⟩ := h
  exact ⟨ast, (restrict_sound ha).1⟩

end Silmaril.Formats
