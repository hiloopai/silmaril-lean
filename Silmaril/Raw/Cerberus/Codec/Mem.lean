module

public import Silmaril.Numeric.Ieee754
public import Silmaril.Cerberus.Mem.Defs
public import Silmaril.Cerberus.Codec.Ctype.Defs

/-! # The wire memory model

Wire format version 1 expresses provenance-free integers, null pointers and
function pointers and exact binary64 floating values. Memory objects have no
encoding. C types get decidable equality from their codec, which the memory model needs for pointer values.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec

open Silmaril.TaggedCodec Codec

/-- Structural equality of C types, decided by comparing encodings. -/
instance : DecidableEq Ctype := ctype.decEq rfl

/-- The provenance-free pointers supported by the wire format. -/
inductive WirePointer where
  | null : Ctype → WirePointer
  | function : Sym → WirePointer
  deriving DecidableEq, Repr

/-- The values that wire format version 1 can express. -/
abbrev wireModel : MemoryModel where
  PointerValue := WirePointer
  IntegerValue := Int
  FloatingValue := Numeric.Ieee754.F64
  MemValue := Empty
  Footprint := Empty

/-- A canonical unsigned integer spelling of exactly 64 IEEE interchange bits. -/
def floatBits : Codec UInt64 where
  enc b := nat.enc b.toNat
  dec t := do
    let n ← nat.dec t
    if n < UInt64.size then some (UInt64.ofNat n) else none
  error _ := ⟨[], "expected unsigned binary64 bits below 18446744073709551616"⟩
  canonical t b h := by
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨n, hn, h⟩ := h
    split at h
    · cases h
      rename_i hlt
      simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hlt] using nat.canonical t n hn
    · simp at h
  complete b _ := by
    simp [Codec.complete_of_budget (c := nat) rfl, b.toNat_lt_size, UInt64.ofNat_toNat]

/-- `($fv bits)` preserves signed zeros, infinities and every NaN payload. -/
-- F64 is a wire representation, not a Lem constructor in `Names`.
def floatingValue : Codec Numeric.Ieee754.F64 := ofAlts
  (fun f => node "$fv" [floatBits.enc f.bits])
  [ctorAlt% Numeric.Ieee754.F64.mk "$fv" floatBits]
  (by codec_nodup) (by codec_enc) (by codec_cover)

/-- Independent outer-tag identity pin. -/
example (b : UInt64) : floatingValue.dec (node "$fv" [floatBits.enc b]) =
    some (Numeric.Ieee754.F64.mk b) :=
  Codec.complete_of_budget (c := floatingValue) rfl ⟨b⟩

/-- Every binary64 interchange encoding decodes unchanged. -/
@[simp] theorem floatingValue_roundTrip (f : Numeric.Ieee754.F64) :
    floatingValue.dec (floatingValue.enc f) = some f :=
  Codec.complete_of_budget (c := floatingValue) rfl f

@[simp] theorem floatingValue_budget : floatingValue.budget = none := rfl

/-- `($iv n)`. -/
def integerValue : Codec Int := tagged "$iv" (.one int)

def encodeWirePointer : WirePointer → Tree
  | .null t => node "$ptr_null" [ctype.enc t]
  | .function s => node "$ptr_function" [sym.enc s]

/-- `($ptr_null ty)` or `($ptr_function sym)`. -/
-- These wire-only constructors have no Lem constructor entry in `Names`.
def pointerValue : Codec WirePointer := ofAlts encodeWirePointer
  [ctorAlt% WirePointer.null "$ptr_null" ctype,
   ctorAlt% WirePointer.function "$ptr_function" sym]
  (by codec_nodup) (by codec_enc) (by codec_cover)

/-- A literal wire tag pins the function constructor independently of its encoder. -/
example (s : Sym) : pointerValue.dec (node "$ptr_function" [sym.enc s]) =
    some (.function s) := Codec.complete_of_budget (c := pointerValue) rfl (.function s)

@[simp] theorem integerValue_budget : integerValue.budget = none := rfl
@[simp] theorem pointerValue_budget : pointerValue.budget = none := rfl

end Silmaril.Cerberus.Codec
