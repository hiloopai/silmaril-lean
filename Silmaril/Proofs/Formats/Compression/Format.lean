module

public import Silmaril.Formats.Compression.Format.Defs

/-!
# Proofs of the format-layer laws

Stated in `Silmaril.Formats.Compression.Format.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Format

open Silmaril.Formats.Compression

theorem decode_ofDecoder (P : Type) (d : P → Decoder) (p : P) :
    (Format.ofDecoder P d).decode p = d p := by
  funext bytes
  simp only [Format.decode, Format.ofDecoder, Decoder.ofExcept]
  cases d p bytes <;> rfl

theorem all_iff {F : Format} : ∀ cs : List (Capability F), Capability.All cs ↔ ∀ c ∈ cs, c.Holds
  | [] => by simp [Capability.All]
  | c :: cs => by simp [Capability.All, all_iff cs]

theorem deterministic_of_spec {F : Format} {s : Scope F} {R : Rel F}
    (h : (Capability.spec s R).Holds) : (Capability.deterministic s R).Holds := by
  intro p hp input out rest out' rest' h₁ h₂
  have e := ((h p hp input out rest).mpr h₁).symm.trans ((h p hp input out' rest').mpr h₂)
  simpa using e

end Silmaril.Proofs.Formats.Compression.Format
