module

public import Silmaril.Formats.JsonWire.Concrete.Defs
import Silmaril.Proofs.Formats.JsonWire.Concrete

/-! # Concrete syntax over bytes: lemmas

* `Concrete.serialize`, `Concrete.serialization_unique`: a concrete event stream serializes to
  its source, and to nothing else;
* `concrete?_fields`: the certified constructor keeps its arguments;
* `restrict_sound`, `restrict_slice`: a profile-restricted decoder returns what the decoder
  returns, accepted by the profile.
-/

@[expose] public section

namespace Silmaril.Formats.JsonWire

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
    cst.source = source ∧ cst.ast = ast ∧ cst.events = events :=
  Silmaril.Proofs.Formats.JsonWire.Concrete.concrete?_fields h

theorem restrict_sound {Ast : Type} {decode : Bytes → Option Ast} {p : Profile Ast}
    {bytes : Bytes} {ast : Ast} (h : restrict decode p bytes = some ast) :
    decode bytes = some ast ∧ p.accepts bytes ast = true :=
  Silmaril.Proofs.Formats.JsonWire.Concrete.restrict_sound h

theorem restrict_slice {Ast : Type} {decode : Bytes → Option Ast} {p : Profile Ast}
    {bytes : Bytes} (h : IsSlice (restrict decode p) bytes) : IsSlice decode bytes :=
  let ⟨ast, ha⟩ := h; ⟨ast, (restrict_sound ha).1⟩

end Silmaril.Formats.JsonWire

end
