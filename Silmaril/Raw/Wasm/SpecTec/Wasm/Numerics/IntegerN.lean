module

public import Silmaril.Wasm.Numerics.Integer
public import Silmaril.Wasm.Numerics.Relaxed

@[expose] public section

/-! # Width-parametric integer numerics (spec §3.1, §3.2 integer helpers)

A faithful transcription of the integer part of `3.1-numerics.scalar.spectec`
over `BitVec N` (the spec's `iN(N)`). Arithmetic definitions follow the spec's
`Nat`/`Int` formulas literally (through `toNat` and `signed_`); `IntegerN.Agreement`
proves they coincide with the `BitVec` operations and with the 32/64-bit
`Numerics.intUnOp`/`intBinOp`/`intRelOp`/`convert`.

Conventions:
* partial functions returning `iN(N)?` return `Option (BitVec N)`;
* functions returning `u32` return `BitVec 32`;
* shift counts (spec `u32`) are `Nat`;
* spec builtins (`iclz`, `ishl`, `iq15mulr_sat`, …) are defined from the prose spec;
* relaxed functions returning `iN(N)*` take the `$ND` flag `nd : Bool` and the
  builtin choice index, and return the (singleton) list of results.
-/

namespace Silmaril.Wasm.Numerics

/-! ## Signed interpretation -/

/-- `$signed_(N, i)`. -/
def signed_ (N : Nat) (i : Nat) : Int :=
  if i < 2 ^ (N - 1) then (i : Int) else (i : Int) - 2 ^ N

/-- `$inv_signed_(N, i)`. The spec is only defined on `[-2^(N-1), 2^(N-1))`; we
extend it totally by reduction modulo `2^N` (see `invSigned_of_nonneg` and
`invSigned_of_neg` for agreement on the spec's domain). -/
def invSigned_ (N : Nat) (i : Int) : Nat := (i % (2 ^ N : Nat)).toNat

theorem invSigned_of_nonneg {N : Nat} {i : Int} (h₀ : 0 ≤ i) (h₁ : i < 2 ^ (N - 1)) :
    invSigned_ N i = i.toNat := by
  unfold invSigned_
  have : (2 : Int) ^ (N - 1) ≤ 2 ^ N := by
    exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.sub_le N 1)
  rw [Int.emod_eq_of_lt h₀ (by push_cast; omega)]

theorem invSigned_of_neg {N : Nat} {i : Int} (h₀ : -2 ^ (N - 1) ≤ i) (h₁ : i < 0) :
    invSigned_ N i = (i + 2 ^ N).toNat := by
  unfold invSigned_
  have : (2 : Int) ^ (N - 1) ≤ 2 ^ N := by
    exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.sub_le N 1)
  have hN : (2 : Int) ^ N = ((2 ^ N : Nat) : Int) := by push_cast; rfl
  congr 1
  have e : i % ((2 ^ N : Nat) : Int) = (i + 2 ^ N) % ((2 ^ N : Nat) : Int) := by
    rw [hN, Int.add_emod_right]
  rw [e, ← hN]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-! ## Saturation -/

/-- `$sat_u_(N, i)`. -/
def sat_u_ (N : Nat) (i : Int) : Nat :=
  if i < 0 then 0 else if i > 2 ^ N - 1 then 2 ^ N - 1 else i.toNat

/-- `$sat_s_(N, i)`. -/
def sat_s_ (N : Nat) (i : Int) : Int :=
  if i < -2 ^ (N - 1) then -2 ^ (N - 1)
  else if i > 2 ^ (N - 1) - 1 then 2 ^ (N - 1) - 1 else i

/-- Saturate into `iN(N)` according to signedness (the prose `sat^sx_N`),
already encoded as a bit pattern. -/
def satBits_ (N : Nat) : Signedness → Int → BitVec N
  | .unsigned, i => BitVec.ofNat N (sat_u_ N i)
  | .signed, i => BitVec.ofNat N (invSigned_ N (sat_s_ N i))

/-- Interpret a bit pattern according to signedness. -/
def toIntSx (N : Nat) : Signedness → BitVec N → Int
  | .unsigned, i => (i.toNat : Int)
  | .signed, i => signed_ N i.toNat

/-- `$bool(b)`. -/
def bool_ : Bool → Nat
  | false => 0
  | true => 1

/-- A `u32` truth value. -/
def u32OfBool (b : Bool) : BitVec 32 := BitVec.ofNat 32 (bool_ b)

/-! ## Integer operations -/

variable (N : Nat)

def ineg_ (i : BitVec N) : BitVec N := BitVec.ofNat N ((2 ^ N - i.toNat) % 2 ^ N)

def iabs_ (i : BitVec N) : BitVec N := if signed_ N i.toNat ≥ 0 then i else ineg_ N i

/-- Builtin; the number of leading zero bits. -/
def iclz_ (i : BitVec N) : BitVec N := i.clz
/-- Builtin; the number of trailing zero bits. -/
def ictz_ (i : BitVec N) : BitVec N := i.ctz
/-- Builtin; the number of set bits. -/
def ipopcnt_ (i : BitVec N) : BitVec N := i.cpop

/-- `$iextend_(N, K, sx, i)`. -/
def iextend_ (K : Nat) : Signedness → BitVec N → BitVec N
  | .unsigned, i => BitVec.ofNat N (i.toNat % 2 ^ K)
  | .signed, i => BitVec.ofNat N (invSigned_ N (signed_ K (i.toNat % 2 ^ K)))

def iadd_ (i₁ i₂ : BitVec N) : BitVec N := BitVec.ofNat N ((i₁.toNat + i₂.toNat) % 2 ^ N)

def isub_ (i₁ i₂ : BitVec N) : BitVec N :=
  BitVec.ofNat N ((2 ^ N + i₁.toNat - i₂.toNat) % 2 ^ N)

def imul_ (i₁ i₂ : BitVec N) : BitVec N := BitVec.ofNat N ((i₁.toNat * i₂.toNat) % 2 ^ N)

/-- `$idiv_`. `$truncz` of a quotient of integers is `Int.tdiv` (`Nat` division
for nonnegatives). The spec's overflow test `j₁/j₂ = 2^(N-1)` (in ℚ) is stated on
the truncated quotient; the two agree because `|j₁| ≤ 2^(N-1)`, and in both cases
the only witness is `j₁ = -2^(N-1)`, `j₂ = -1`. -/
def idiv_ : Signedness → BitVec N → BitVec N → Option (BitVec N)
  | .unsigned, i₁, i₂ =>
      if i₂.toNat = 0 then none else some (BitVec.ofNat N (i₁.toNat / i₂.toNat))
  | .signed, i₁, i₂ =>
      if i₂.toNat = 0 then none
      else if (signed_ N i₁.toNat).tdiv (signed_ N i₂.toNat) = 2 ^ (N - 1) then none
      else some (BitVec.ofNat N (invSigned_ N ((signed_ N i₁.toNat).tdiv (signed_ N i₂.toNat))))

def irem_ : Signedness → BitVec N → BitVec N → Option (BitVec N)
  | .unsigned, i₁, i₂ =>
      if i₂.toNat = 0 then none
      else some (BitVec.ofNat N (i₁.toNat - i₂.toNat * (i₁.toNat / i₂.toNat)))
  | .signed, i₁, i₂ =>
      if i₂.toNat = 0 then none
      else
        let j₁ := signed_ N i₁.toNat
        let j₂ := signed_ N i₂.toNat
        some (BitVec.ofNat N (invSigned_ N (j₁ - j₂ * j₁.tdiv j₂)))

def imin_ : Signedness → BitVec N → BitVec N → BitVec N
  | .unsigned, i₁, i₂ => if i₁.toNat ≤ i₂.toNat then i₁ else i₂
  | .signed, i₁, i₂ => if signed_ N i₁.toNat ≤ signed_ N i₂.toNat then i₁ else i₂

def imax_ : Signedness → BitVec N → BitVec N → BitVec N
  | .unsigned, i₁, i₂ => if i₁.toNat ≥ i₂.toNat then i₁ else i₂
  | .signed, i₁, i₂ => if signed_ N i₁.toNat ≥ signed_ N i₂.toNat then i₁ else i₂

def iadd_sat_ : Signedness → BitVec N → BitVec N → BitVec N
  | .unsigned, i₁, i₂ => BitVec.ofNat N (sat_u_ N ((i₁.toNat : Int) + i₂.toNat))
  | .signed, i₁, i₂ =>
      BitVec.ofNat N (invSigned_ N (sat_s_ N (signed_ N i₁.toNat + signed_ N i₂.toNat)))

def isub_sat_ : Signedness → BitVec N → BitVec N → BitVec N
  | .unsigned, i₁, i₂ => BitVec.ofNat N (sat_u_ N ((i₁.toNat : Int) - i₂.toNat))
  | .signed, i₁, i₂ =>
      BitVec.ofNat N (invSigned_ N (sat_s_ N (signed_ N i₁.toNat - signed_ N i₂.toNat)))

/-- Builtin (prose): `iq15mulr_sat_s(i₁, i₂) = sat_s_N((j₁ · j₂ + 2^14) >> 15)`
with an arithmetic (flooring) shift. Only the signed variant occurs in Wasm; the
unsigned case is the analogous unsigned formula. -/
def iq15mulr_sat_ (sx : Signedness) (i₁ i₂ : BitVec N) : BitVec N :=
  satBits_ N sx ((toIntSx N sx i₁ * toIntSx N sx i₂ + 2 ^ 14) / 2 ^ 15)

/-- Builtin (prose, relaxed SIMD): when both operands are `-2^(N-1)` the result is
`relaxed(R_iq15mulr)[2^(N-1)-1, -2^(N-1)]`, otherwise `iq15mulr_sat`. -/
def irelaxed_q15mulr_ (nd : Bool) (r : Fin 2) (sx : Signedness) (i₁ i₂ : BitVec N) :
    List (BitVec N) :=
  if sx = .signed ∧ signed_ N i₁.toNat = -2 ^ (N - 1) ∧ signed_ N i₂.toNat = -2 ^ (N - 1) then
    [relaxed2 nd r (BitVec.ofNat N (invSigned_ N (2 ^ (N - 1) - 1)))
      (BitVec.ofNat N (invSigned_ N (-2 ^ (N - 1))))]
  else [iq15mulr_sat_ N sx i₁ i₂]

/-- Builtin (prose): `iavgr_u(i₁, i₂) = truncz((i₁ + i₂ + 1) / 2)`; the signed
case (unused by Wasm) floors the signed average. -/
def iavgr_ : Signedness → BitVec N → BitVec N → BitVec N
  | .unsigned, i₁, i₂ => BitVec.ofNat N ((i₁.toNat + i₂.toNat + 1) / 2)
  | .signed, i₁, i₂ =>
      BitVec.ofNat N (invSigned_ N ((signed_ N i₁.toNat + signed_ N i₂.toNat + 1) / 2))

def inot_ (i : BitVec N) : BitVec N := ~~~i
def iand_ (i₁ i₂ : BitVec N) : BitVec N := i₁ &&& i₂
def iandnot_ (i₁ i₂ : BitVec N) : BitVec N := i₁ &&& ~~~i₂
def ior_ (i₁ i₂ : BitVec N) : BitVec N := i₁ ||| i₂
def ixor_ (i₁ i₂ : BitVec N) : BitVec N := i₁ ^^^ i₂

/-- Builtin (prose): shift by `k mod N`. -/
def ishl_ (i : BitVec N) (k : Nat) : BitVec N := i <<< (k % N)

def ishr_ : Signedness → BitVec N → Nat → BitVec N
  | .unsigned, i, k => i >>> (k % N)
  | .signed, i, k => i.sshiftRight (k % N)

/-- Builtin (prose): rotate by `i₂ mod N` (`BitVec.rotateLeft` reduces its
amount modulo `N` itself). -/
def irotl_ (i₁ i₂ : BitVec N) : BitVec N := i₁.rotateLeft i₂.toNat
def irotr_ (i₁ i₂ : BitVec N) : BitVec N := i₁.rotateRight i₂.toNat

/-- Builtin (prose): `ibitselect(i₁, i₂, i₃) = (i₁ ∧ i₃) ∨ (i₂ ∧ ¬i₃)`. -/
def ibitselect_ (i₁ i₂ i₃ : BitVec N) : BitVec N := (i₁ &&& i₃) ||| (i₂ &&& ~~~i₃)

/-- Builtin (prose, relaxed SIMD): a mask that is all ones or all zeros selects
bitwise; otherwise `relaxed(R_laneselect)[ibitselect(i₁,i₂,i₃),
ibitselect(i₁,i₂,ishr_s(i₃, N-1))]`, i.e. either bitwise or by the top bit. -/
def irelaxed_laneselect_ (nd : Bool) (r : Fin 2) (i₁ i₂ i₃ : BitVec N) : List (BitVec N) :=
  if i₃ = BitVec.allOnes N ∨ i₃ = 0 then [ibitselect_ N i₁ i₂ i₃]
  else [relaxed2 nd r (ibitselect_ N i₁ i₂ i₃) (ibitselect_ N i₁ i₂ (ishr_ N .signed i₃ (N - 1)))]

def ieqz_ (i : BitVec N) : BitVec 32 := u32OfBool (i.toNat = 0)
def inez_ (i : BitVec N) : BitVec 32 := u32OfBool (i.toNat ≠ 0)
def ieq_ (i₁ i₂ : BitVec N) : BitVec 32 := u32OfBool (i₁ = i₂)
def ine_ (i₁ i₂ : BitVec N) : BitVec 32 := u32OfBool (i₁ ≠ i₂)

def ilt_ : Signedness → BitVec N → BitVec N → BitVec 32
  | .unsigned, i₁, i₂ => u32OfBool (i₁.toNat < i₂.toNat)
  | .signed, i₁, i₂ => u32OfBool (signed_ N i₁.toNat < signed_ N i₂.toNat)
def igt_ : Signedness → BitVec N → BitVec N → BitVec 32
  | .unsigned, i₁, i₂ => u32OfBool (i₁.toNat > i₂.toNat)
  | .signed, i₁, i₂ => u32OfBool (signed_ N i₁.toNat > signed_ N i₂.toNat)
def ile_ : Signedness → BitVec N → BitVec N → BitVec 32
  | .unsigned, i₁, i₂ => u32OfBool (i₁.toNat ≤ i₂.toNat)
  | .signed, i₁, i₂ => u32OfBool (signed_ N i₁.toNat ≤ signed_ N i₂.toNat)
def ige_ : Signedness → BitVec N → BitVec N → BitVec 32
  | .unsigned, i₁, i₂ => u32OfBool (i₁.toNat ≥ i₂.toNat)
  | .signed, i₁, i₂ => u32OfBool (signed_ N i₁.toNat ≥ signed_ N i₂.toNat)

/-! ## Conversions between widths -/

variable {N}

/-- `$wrap_(M, N, i) = i mod 2^N`. -/
def wrap_ (M N : Nat) (i : BitVec M) : BitVec N := BitVec.ofNat N (i.toNat % 2 ^ N)

/-- `$extend_(M, N, sx, i)`: zero- or sign-extension. -/
def extend_ (M N : Nat) : Signedness → BitVec M → BitVec N
  | .unsigned, i => BitVec.ofNat N i.toNat
  | .signed, i => BitVec.ofNat N (invSigned_ N (signed_ M i.toNat))

/-- `$narrow_(M, N, sx, i) = sat^sx_N(signed_M(i))`. -/
def narrow_ (M N : Nat) (sx : Signedness) (i : BitVec M) : BitVec N :=
  satBits_ N sx (signed_ M i.toNat)

/-! ## Operator dispatch (the integer cases of `$unop_`, `$binop_`, …) -/

variable (N)

def iunop_ : IntUnOp → BitVec N → BitVec N
  | .clz, i => iclz_ N i
  | .ctz, i => ictz_ N i
  | .popcnt, i => ipopcnt_ N i
  | .extend size, i => iextend_ N size.width .signed i

def ibinop_ : IntBinOp → BitVec N → BitVec N → Option (BitVec N)
  | .add, i₁, i₂ => some (iadd_ N i₁ i₂)
  | .sub, i₁, i₂ => some (isub_ N i₁ i₂)
  | .mul, i₁, i₂ => some (imul_ N i₁ i₂)
  | .div sx, i₁, i₂ => idiv_ N sx i₁ i₂
  | .rem sx, i₁, i₂ => irem_ N sx i₁ i₂
  | .and, i₁, i₂ => some (iand_ N i₁ i₂)
  | .or, i₁, i₂ => some (ior_ N i₁ i₂)
  | .xor, i₁, i₂ => some (ixor_ N i₁ i₂)
  | .shl, i₁, i₂ => some (ishl_ N i₁ i₂.toNat)
  | .shr sx, i₁, i₂ => some (ishr_ N sx i₁ i₂.toNat)
  | .rotl, i₁, i₂ => some (irotl_ N i₁ i₂)
  | .rotr, i₁, i₂ => some (irotr_ N i₁ i₂)

def itestop_ : IntTestOp → BitVec N → BitVec 32
  | .eqz, i => ieqz_ N i

def irelop_ : IntRelOp → BitVec N → BitVec N → BitVec 32
  | .eq, i₁, i₂ => ieq_ N i₁ i₂
  | .ne, i₁, i₂ => ine_ N i₁ i₂
  | .lt sx, i₁, i₂ => ilt_ N sx i₁ i₂
  | .gt sx, i₁, i₂ => igt_ N sx i₁ i₂
  | .le sx, i₁, i₂ => ile_ N sx i₁ i₂
  | .ge sx, i₁, i₂ => ige_ N sx i₁ i₂

/-! ## Lane-list helpers of §3.2 (dot products, pairwise add, relaxed swizzle) -/

/-- `$concat_` read backwards: split a list into consecutive pairs (a trailing
odd element is dropped; the spec never applies it to odd lengths). -/
def pairs {α : Type _} : List α → List (α × α)
  | a :: b :: rest => (a, b) :: pairs rest
  | _ => []

def ivadd_pairwise_ (is : List (BitVec N)) : List (BitVec N) :=
  (pairs is).map fun p => iadd_ N p.1 p.2

def ivmul_ (is₁ is₂ : List (BitVec N)) : List (BitVec N) := List.zipWith (imul_ N) is₁ is₂

def ivdot_ (is₁ is₂ : List (BitVec N)) : List (BitVec N) :=
  (pairs (ivmul_ N is₁ is₂)).map fun p => iadd_ N p.1 p.2

def ivdot_sat_ (is₁ is₂ : List (BitVec N)) : List (BitVec N) :=
  (pairs (ivmul_ N is₁ is₂)).map fun p => iadd_sat_ N .signed p.1 p.2

/-- The signedness of the second operand of `relaxed_dot`:
`$relaxed2($R_idot, sx, S, U)`. -/
def relaxedDotSx (nd : Bool) (r : Fin 2) : Signedness := relaxed2 nd r .signed .unsigned

/-- `$irelaxed_swizzle_lane_(N, c*, i)`. -/
def irelaxed_swizzle_lane_ (nd : Bool) (r : Fin 2) (cs : List (BitVec N)) (i : BitVec N) :
    BitVec N :=
  if i.toNat < cs.length then cs.getD i.toNat 0
  else if signed_ N i.toNat < 0 then 0
  else relaxed2 nd r 0 (cs.getD (i.toNat % cs.length) 0)

end Silmaril.Wasm.Numerics
