module

public import Silmaril.X86.Ladder.LibMini.Defs
public import Silmaril.Machine.SystemV.Defs
/-!
# `libmini`: the C signatures of the certified routines

The C signatures of `memcpy`, `memset` and `strlen` (`Silmaril.C.Api.Signature`), and the
argument readings their System V certificates share. They need the System V model
(`Silmaril.Machine.SystemV`), which `Ladder.LibMini.Defs` does not import.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.LibMini

/-- `void *memcpy(void *, const void *, size_t)`. -/
def sigCopy : Silmaril.C.Api.Signature := ⟨[.pointer, .pointer, .uint64], some .pointer⟩
/-- `void *memset(void *, int, size_t)`. -/
def sigFill : Silmaril.C.Api.Signature := ⟨[.pointer, .int32, .uint64], some .pointer⟩
/-- `size_t strlen(const char *)`. -/
def sigScan : Silmaril.C.Api.Signature := ⟨[.pointer], some .uint64⟩

/-- `memcpy` and `memset` return their first argument. -/
def firstResult {k : List Silmaril.C.Api.Scalar} :
    Silmaril.C.Api.Arguments (.pointer :: k) → Silmaril.C.Api.ReturnValue (some .pointer)
  | .cons d _ => d

/-- `memcpy` and `memset` write `[d, d + n)`. -/
def blockWrites {k : Silmaril.C.Api.Scalar} :
    Silmaril.C.Api.Arguments [.pointer, k, .uint64] → Silmaril.Machine.SystemV.Footprint
  | .cons d (.cons _ (.cons n .nil)) => fun a => d.toNat ≤ a ∧ a < d.toNat + n.toNat

end Silmaril.X86.Ladder.LibMini
