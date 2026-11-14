module

public import Silmaril.Formats.Compression.Format.Defs
public import Silmaril.Formats.Compression.Thms
import Silmaril.Proofs.Formats.Compression.Format

/-!
# Compressed formats: laws of the catalogue layer

Proved (standard axioms):

* `Format.decode_ofDecoder`: a format given by an `Option` decoder denotes it;
* `Capability.all_iff`, `Certified.of`, `Certified.holds`: a certificate is built
  from proofs of its listed claims, and each listed claim holds;
* `Capability.deterministic_of_spec`: a decoder that is exactly a relational
  spec makes that spec deterministic;
* `Capability.whole_of_roundTrip`, `Capability.members_of_roundTrip`: a claimed
  round trip decodes whole buffers and one-member files.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

theorem Format.decode_ofDecoder (P : Type) (d : P → Decoder) (p : P) :
    (Format.ofDecoder P d).decode p = d p :=
  Proofs.Formats.Compression.Format.decode_ofDecoder P d p

namespace Capability

variable {F : Format}

theorem all_iff (cs : List (Capability F)) : All cs ↔ ∀ c ∈ cs, c.Holds :=
  Proofs.Formats.Compression.Format.all_iff cs

theorem deterministic_of_spec {s : Scope F} {R : Rel F} (h : (spec s R).Holds) :
    (deterministic s R).Holds :=
  Proofs.Formats.Compression.Format.deterministic_of_spec h

theorem whole_of_roundTrip {E : Encoding F} (h : (roundTrip E).Holds) (e : E.EParams)
    (data : List UInt8) : (F.decode (E.params e)).whole (E.encode e data) = some data :=
  (h e).whole data

theorem members_of_roundTrip {E : Encoding F} (h : (roundTrip E).Holds) (e : E.EParams)
    (data : List UInt8) : (F.decode (E.params e)).members (E.encode e data) = some data :=
  (h e).members_single data

end Capability

namespace Certified

variable {F : Format}

/-- A certificate from proofs of exactly the listed claims. -/
def of (claims : List (Capability F)) (h : Capability.All claims) (security : Security := {}) :
    Certified F :=
  ⟨claims, (Capability.all_iff claims).mp h, security⟩

theorem holds (C : Certified F) {c : Capability F} (h : c ∈ C.claims) : c.Holds :=
  C.proofs c h

end Certified

end Silmaril.Formats.Compression
