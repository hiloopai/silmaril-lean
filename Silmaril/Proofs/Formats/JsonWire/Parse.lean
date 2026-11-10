module

public import Silmaril.Formats.JsonWire.Defs
import Silmaril.Formats.JsonWire.Concrete.Thms

/-! # Proofs: JSON on the wire (`Silmaril.Formats.JsonWire.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWire.Parse

open Silmaril.Formats.JsonWire
open Silmaril.Formats (Bytes)

theorem parseCst?_sound {dialect : Dialect} {bytes : Bytes} {cst : Cst}
    (h : parseCst? dialect bytes = some cst) : cst.source = bytes ∧ IsCst dialect cst := by
  unfold parseCst? at h
  cases hd : Internal.decode dialect bytes with
  | none => simp [hd] at h
  | some pair =>
    obtain ⟨ast, tokens⟩ := pair
    simp only [hd] at h
    change concrete? bytes ast tokens = some cst at h
    obtain ⟨hs, ha, ht⟩ := concrete?_fields h
    exact ⟨hs, by simpa only [IsCst, hs, ha, ht] using hd⟩

end Silmaril.Proofs.Formats.JsonWire.Parse

end
