module

public import Silmaril.Formats.SExp.EncodingWat
public import Silmaril.Wasm.Types
public import Init.Data.Float.Model.Float32

/-!
# Text format of values (SpecTec `6.1-text.values`)

Values are read from the atoms produced by the lexical layer
(`Formats.SExpEncoding.Wat`): numbers, `inf`/`nan` and keywords are bare tokens
(`Atom.sym`) whose raw text is interpreted here; strings are `Atom.str` (bytes);
identifiers are `Atom.id`.

* `UN N`, `SN N`, `IN N` — `TuN`, `TsN`, `TiN` (decimal or `0x` hexadecimal,
  `_` separators between digits, range-checked);
* `FloatMag`, `FMag`, `floatBits` — `TfNmag`/`TfN`: decimal and hexadecimal
  floats, `inf`, `nan`, `nan:0x…`, rounded by the logical IEEE model of the Lean
  core (`Float.Model.UnpackedFloat`, round-to-nearest-even);
* `Name` — `Tname` (strings that are valid UTF-8);
* `Idx names` — `Tidx_(ids)`: a `u32` or an identifier bound in `names`.

These definitions are shared by the Core 3.0 and Wasm 1.0 grammars (the 2019
REC has the same value syntax).

Erratum T2: the SpecTec snapshot requires an exponent
in `Tfloat` and `Thexfloat` (so `1.5` would not be a float literal); the
exponent is optional here, as in the prose specification and all
implementations.  Bare integers such as `12345` are float literals too, as in
the 2.0 REC and `float_literals.wast:90`.
-/

@[expose] public section

namespace Silmaril.Wasm.Text

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Formats.SExpEncoding.Wat

/-- The S-expression AST of the lexical layer. -/
abbrev SExp := Formats.SExpEncoding.SExp

/-- A bare token with the given raw text. -/
abbrev K (s : String) : SExp := kw s

/-- A proper list node. -/
abbrev L (xs : List SExp) : SExp := listOf xs

/-! ## Integers -/

/-- `Tsign`. -/
def SignChars (cs : Chars) (s : Int) : Prop :=
  (cs = [] ∧ s = 1) ∨ (cs = ['+'] ∧ s = 1) ∨ (cs = ['-'] ∧ s = -1)

/-- `TuN(N)` on characters. -/
def UN (N : Nat) (cs : Chars) (n : Nat) : Prop :=
  (Num cs n ∨ ∃ ds, cs = '0' :: 'x' :: ds ∧ HexNum ds n) ∧ n < 2 ^ N

/-- `TsN(N)` on characters. -/
def SN (N : Nat) (cs : Chars) (i : Int) : Prop :=
  ∃ sc rest s n, cs = sc ++ rest ∧ SignChars sc s ∧ UN N rest n ∧ i = s * n ∧
    -(2 ^ (N - 1) : Int) ≤ i ∧ i < 2 ^ (N - 1)

/-- `TiN(N)`: unsigned, or signed and reinterpreted (`$inv_signed_`). -/
def IN (N : Nat) (cs : Chars) (b : BitVec N) : Prop :=
  (∃ n, UN N cs n ∧ b = BitVec.ofNat N n) ∨ (∃ i, SN N cs i ∧ b = BitVec.ofInt N i)

/-- A bare token read as `TuN(N)`. -/
def AtomU (N : Nat) (x : SExp) (n : Nat) : Prop := ∃ t, x = K t ∧ UN N t.toList n

/-- A bare token read as `TiN(N)`. -/
def AtomI (N : Nat) (x : SExp) (b : BitVec N) : Prop := ∃ t, x = K t ∧ IN N t.toList b

/-- `Tu32` as a `Fin (2^32)`. -/
def AtomU32 (x : SExp) (n : Fin (2 ^ 32)) : Prop := AtomU 32 x n.val

/-- `Tu64` as a `Fin (2^64)`. -/
def AtomU64 (x : SExp) (n : Fin (2 ^ 64)) : Prop := AtomU 64 x n.val

/-! ## Floats -/

/-- Float magnitudes as read from the text (before rounding). -/
inductive FloatMag where
  /-- `m * 10^e`. -/
  | dec (m : Nat) (e : Int)
  /-- `m * 2^e`. -/
  | hex (m : Nat) (e : Int)
  | inf
  /-- `nan`: the canonical NaN. -/
  | nan
  /-- `nan:0xn`. -/
  | nanPayload (n : Nat)
  deriving DecidableEq, Repr

/-- The number of digits (excluding `_`) of a digit string. -/
def digitCount (cs : Chars) : Nat := (cs.filter (· ≠ '_')).length

/-- `Tmant` (`hex = false`) or `Thexmant` (`hex = true`): value `m / radix^k`. -/
def Mant (hex : Bool) (cs : Chars) (m k : Nat) : Prop :=
  let R : Chars → Nat → Prop := if hex then HexNum else Num
  let radix := if hex then 16 else 10
  (R cs m ∧ k = 0) ∨ (∃ p, cs = p ++ ['.'] ∧ R p m ∧ k = 0) ∨
    ∃ p f n v, cs = p ++ '.' :: f ∧ R p n ∧ R f v ∧ k = digitCount f ∧ m = n * radix ^ k + v

/-- An optional exponent part `(E|e) Tsign Tnum` (or `(P|p) …` for hex floats). -/
def ExpPart (hex : Bool) (cs : Chars) (e : Int) : Prop :=
  (cs = [] ∧ e = 0) ∨
    ∃ mark sc ds s n, cs = mark :: (sc ++ ds) ∧
      (if hex then mark = 'p' ∨ mark = 'P' else mark = 'e' ∨ mark = 'E') ∧
      SignChars sc s ∧ Num ds n ∧ e = s * n

/-- `TfNmag` on characters. -/
def FMag (cs : Chars) (v : FloatMag) : Prop :=
  (∃ mc ec m k e, cs = mc ++ ec ∧ Mant false mc m k ∧ ExpPart false ec e ∧
      v = .dec m (e - k)) ∨
    (∃ mc ec m k e, cs = '0' :: 'x' :: (mc ++ ec) ∧ Mant true mc m k ∧ ExpPart true ec e ∧
      v = .hex m (e - 4 * k)) ∨
    (cs = "inf".toList ∧ v = .inf) ∨ (cs = "nan".toList ∧ v = .nan) ∨
    ∃ ds n, cs = "nan:0x".toList ++ ds ∧ HexNum ds n ∧ v = .nanPayload n

/-- The Lean core IEEE format of a Wasm float type. -/
def floatFormat : FloatType → Float.Model.Format
  | .f32 => .binary32
  | .f64 => .binary64

/-- Trailing significand width (`$signif`). -/
def signifBits : FloatType → Nat
  | .f32 => 23
  | .f64 => 52

/-- Exponent width. -/
def exponBits : FloatType → Nat
  | .f32 => 8
  | .f64 => 11

/-- The positive-infinity bit pattern. -/
def infBits (t : FloatType) : Nat := (2 ^ exponBits t - 1) * 2 ^ signifBits t

/-- `$ieee_` followed by packing, for a non-negative magnitude: `none` when a
finite literal rounds to infinity or a NaN payload is out of range. -/
def magBits (t : FloatType) : FloatMag → Option Nat
  | .inf => some (infBits t)
  | .nan => some (infBits t + 2 ^ (signifBits t - 1))
  | .nanPayload n => if 1 ≤ n ∧ n < 2 ^ signifBits t then some (infBits t + n) else none
  | .dec m e =>
      let b := ((Float.Model.UnpackedFloat.ofScientific (floatFormat t) m e).pack (floatFormat t)).toNat
      if b = infBits t then none else some b
  | .hex m e =>
      let b := (if m = 0 then 0 else
        ((Float.Model.UnpackedFloat.round (floatFormat t) .positive m e).pack (floatFormat t)).toNat)
      if b = infBits t then none else some b

/-- `TfN(N)` on characters: a sign and a magnitude. -/
def FN (t : FloatType) (cs : Chars) (b : BitVec t.width) : Prop :=
  ∃ sc mc s v n, cs = sc ++ mc ∧ SignChars sc s ∧ FMag mc v ∧ magBits t v = some n ∧
    b = BitVec.ofNat t.width (if s = -1 then n + 2 ^ (t.width - 1) else n)

/-- A bare token read as `TfN(N)`. -/
def AtomF (t : FloatType) (x : SExp) (b : BitVec t.width) : Prop := ∃ s, x = K s ∧ FN t s.toList b

/-! ## Names and identifiers -/

/-- `Tname`: a string atom that is valid UTF-8. -/
def Name (x : SExp) (n : String) : Prop :=
  ∃ bs, x = .atom (.str bs) ∧ Unicode.utf8? bs = some n

/-- `Tid?` as a (zero- or one-element) item list. -/
def IdOpt (xs : List SExp) (id : Option String) : Prop :=
  (xs = [] ∧ id = none) ∨ ∃ n, xs = [.atom (.id n)] ∧ id = some n

/-- `Tidx_(ids)`: an unsigned 32-bit numeral or a bound identifier. -/
def IdxIn (names : List (Option String)) (x : SExp) (i : Nat) : Prop :=
  (AtomU 32 x i) ∨ ∃ n, x = .atom (.id n) ∧ names[i]? = some (some n)

/-- `Tidx_` into a typed index space. -/
def Idx (names : List (Option String)) {k : IndexKind} (x : SExp) (i : Wasm.Idx k) : Prop :=
  IdxIn names x i.toNat

/-- Names in an index space are pairwise distinct (`$disjoint_`). -/
def Distinct (names : List (Option String)) : Prop :=
  (names.filterMap id).Nodup

end Silmaril.Wasm.Text
