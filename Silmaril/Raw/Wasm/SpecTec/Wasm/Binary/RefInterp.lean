module

public import Silmaril.Wasm.Binary.Basic

/-! # The reference interpreter's UTF-8 and LEB128 decoders

An executable transcription of the decoders of the official WebAssembly reference
interpreter at `WebAssembly/spec@608711107b7f1edb13efd57b7d79b49477462d36`, and proofs
that the grammar relations of `Silmaril.Wasm.Binary.Basic` accept **exactly** the byte
strings these decoders accept, with the same results.

Sources (line numbers refer to the pinned commit):

* `interpreter/binary/utf8.ml`, lines 25–45 (`con`, `code`, `decode`, `decode'`);
* `interpreter/binary/decode.ml`, lines 85–109 (`uN`, `sN`, `u32`, `u64`, `s32`, `s33`,
  `s64`), 114–120 (`len32`, `string`) and 133–136 (`name`).

## Transcription conventions

* An OCaml exception (`Utf8.Utf8`, `EOS`, or `Code` raised by `require`/`error`) is
  `none`. Acceptance does not depend on which exception is raised nor on OCaml's
  evaluation order, since every exception aborts the whole decode.
* A decoder over a `stream` becomes a function on the remaining input returning the
  value and the unconsumed rest; `byte s` on an exhausted stream raises `EOS`.
* OCaml `int` byte values are `Nat`s (`Char.code`, `UInt8.toNat`), and the `land`
  masks are `Nat` `&&&`.
* `uN`/`sN` accumulate in `Int64` with `logor x (shift_left m 7)`. Since `x < 2^7`, the
  bits are disjoint and this is `x + 2^7 * m`; for `n ≤ 64` (all uses: `u32`, `u64`,
  `s32`, `s33`, `s64`) the result fits in 64 bits, so no wrap-around occurs, and we
  compute in `Nat`/`Int`. The terminal `logor x (logxor (-1L) 0x7fL)` is `x - 2^7`.
  (The Python oracle in `scripts/wasm-refinterp` mirrors the `Int64` arithmetic bit for
  bit, and agrees.)
* `sN`'s mask `(-1 lsl (n - 1)) land 0x7f` is `(0x7f >>> (n - 1)) <<< (n - 1)`; it is only
  consulted when `n < 7`.
* The recursion depth `n` is a `Nat`. The interpreter's `n - 7` may go negative, but the
  only tests on it are `n > 0` and `n ≥ 7`, so truncated subtraction is equivalent.
* `utf8.ml` returns code points (`int`); `refUtf8Decode` maps them to `Char`. Every
  code point `code` admits is a Unicode scalar value, so this loses nothing.

## Results

* `utf8_iff`: `Utf8 cs b ↔ refUtf8Decode b = some cs`.
* `name_iff`, `refName_eq_some_iff`: `Name` agrees with `name` (`len32`, then
  `get_string`, then `Utf8.decode`), as a whole-input and as a consumed-prefix statement.
  `len32` bounds the length by the input remaining before the length field and
  `get_string` by the input after it; only the second is ever binding.
* `un_iff`, `refUN_eq_some_iff` (and `u32_iff`, `u64_iff`): `UN N` agrees with `uN N` for
  every `N > 0`.
* `sn_iff`, `refSN_eq_some_iff` (and `s32_iff`, `s33_iff`, `s64_iff`): likewise `SN N`.
* `in_iff`, `i32_iff`, `i64_iff`: the uninterpreted `IN N` agrees with `sN N` followed by
  the two's-complement wrap (`I32.of_int_s`, i.e. `BitVec.ofInt`).

`N > 0` is needed only because `UN 0` and `SN 0` accept `0x00` (and `SN 0` also `0x7F`)
while `uN 0`/`sN 0` raise "integer representation too long"; the interpreter never calls
them with `0`, and the grammar only recurses at `N > 7` (so `N - 7 > 0`).

The executable oracle `scripts/wasm-refinterp/RefInterpOracle.lean` runs these functions
against the reference interpreter itself and an independent Python oracle; see
`scripts/wasm-refinterp/README.md` and `docs/projects/wasm.md`. -/

@[expose] public section

namespace Silmaril.Wasm.Binary.RefInterp

open Silmaril.Wasm.Binary

/-! ## `utf8.ml` -/

/-- `let con b = if b land 0xc0 = 0x80 then b land 0x3f else raise Utf8` (utf8.ml:25). -/
def con (b : Nat) : Option Nat :=
  if b &&& 0xc0 = 0x80 then some (b &&& 0x3f) else none

/-- `let code min n = if n < min || (0xd800 <= n && n < 0xe000) || n >= 0x110000 then
raise Utf8 else n` (utf8.ml:26–28). -/
def code (min n : Nat) : Option Nat :=
  if n < min ∨ (0xd800 ≤ n ∧ n < 0xe000) ∨ n ≥ 0x110000 then none else some n

/-- `decode'` (utf8.ml:31–45). OCaml tries the cases in order; a case whose pattern needs
more bytes than remain falls through to the next one, and every later case needs even
more bytes, so a too-short tail ends in the final `| _ -> raise Utf8`. -/
def decode' : List Nat → Option (List Nat)
  -- `| [] -> []` (l.32)
  | [] => some []
  | b1 :: bs =>
    -- `| b1::bs when b1 < 0x80 -> code 0x0 b1 :: decode' bs` (l.33–34)
    if b1 < 0x80 then
      (code 0x0 b1).bind fun c => (decode' bs).map (c :: ·)
    -- `| b1::bs when b1 < 0xc0 -> raise Utf8` (l.35–36)
    else if b1 < 0xc0 then none
    else match bs with
    | b2 :: bs₂ =>
      -- `| b1::b2::bs when b1 < 0xe0 -> code 0x80 ((b1 land 0x1f) lsl 6 + con b2) :: …`
      -- (l.37–38)
      if b1 < 0xe0 then
        ((con b2).bind fun c2 => code 0x80 (((b1 &&& 0x1f) <<< 6) + c2)).bind fun c =>
          (decode' bs₂).map (c :: ·)
      else match bs₂ with
      | b3 :: bs₃ =>
        -- `| b1::b2::b3::bs when b1 < 0xf0 ->`
        -- `code 0x800 ((b1 land 0x0f) lsl 12 + con b2 lsl 6 + con b3) :: …` (l.39–40)
        if b1 < 0xf0 then
          ((con b2).bind fun c2 => (con b3).bind fun c3 =>
            code 0x800 (((b1 &&& 0x0f) <<< 12) + (c2 <<< 6) + c3)).bind fun c =>
              (decode' bs₃).map (c :: ·)
        else match bs₃ with
        | b4 :: bs₄ =>
          -- `| b1::b2::b3::b4::bs when b1 < 0xf8 -> code 0x10000 ((b1 land 0x07) lsl 18 +`
          -- `con b2 lsl 12 + con b3 lsl 6 + con b4) :: decode' bs` (l.41–43)
          if b1 < 0xf8 then
            ((con b2).bind fun c2 => (con b3).bind fun c3 => (con b4).bind fun c4 =>
              code 0x10000 (((b1 &&& 0x07) <<< 18) + (c2 <<< 12) + (c3 <<< 6) + c4)).bind
                fun c => (decode' bs₄).map (c :: ·)
          -- `| _ -> raise Utf8` (l.44–45)
          else none
        | [] => none
      | [] => none
    | [] => none

/-- `let rec decode s = decode' (List.map Char.code (Lib.String.explode s))` (utf8.ml:30),
with the resulting code points read as `Char`s. -/
def refUtf8Decode (bs : List UInt8) : Option (List Char) :=
  (decode' (bs.map UInt8.toNat)).map (List.map Char.ofNat)

/-! ## `decode.ml` -/

/-- `uN n s` (decode.ml:85–90):
```
let rec uN n s =
  require (n > 0) s (pos s) "integer representation too long";
  let b = byte s in
  require (n >= 7 || b land 0x7f < 1 lsl n) s (pos s - 1) "integer too large";
  let x = Int64.of_int (b land 0x7f) in
  if b land 0x80 = 0 then x else Int64.(logor x (shift_left (uN (n - 7) s) 7))
``` -/
def refUN (n : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: s =>
    if ¬ n > 0 then none else
    let b := b.toNat
    if ¬ (n ≥ 7 ∨ b &&& 0x7f < 1 <<< n) then none else
    let x := b &&& 0x7f
    if b &&& 0x80 = 0 then some (x, s) else
    (refUN (n - 7) s).map fun (m, s') => (x + 2 ^ 7 * m, s')

/-- `sN n s` (decode.ml:92–101):
```
let rec sN n s =
  require (n > 0) s (pos s) "integer representation too long";
  let b = byte s in
  let mask = (-1 lsl (n - 1)) land 0x7f in
  require (n >= 7 || b land mask = 0 || b land mask = mask) s (pos s - 1)
    "integer too large";
  let x = Int64.of_int (b land 0x7f) in
  if b land 0x80 = 0
  then (if b land 0x40 = 0 then x else Int64.(logor x (logxor (-1L) 0x7fL)))
  else Int64.(logor x (shift_left (sN (n - 7) s) 7))
``` -/
def refSN (n : Nat) : List UInt8 → Option (Int × List UInt8)
  | [] => none
  | b :: s =>
    if ¬ n > 0 then none else
    let b := b.toNat
    let mask := (0x7f >>> (n - 1)) <<< (n - 1)
    if ¬ (n ≥ 7 ∨ b &&& mask = 0 ∨ b &&& mask = mask) then none else
    let x : Int := (b &&& 0x7f : Nat)
    if b &&& 0x80 = 0 then some (if b &&& 0x40 = 0 then x else x - 2 ^ 7, s) else
    (refSN (n - 7) s).map fun (i, s') => (x + 2 ^ 7 * i, s')

/-- `let u32 s = I32.of_int_u (I64.to_int_u (uN 32 s))` (decode.ml:104). -/
def refU32 : List UInt8 → Option (Nat × List UInt8) := refUN 32
/-- `let u64 s = uN 64 s` (decode.ml:105). -/
def refU64 : List UInt8 → Option (Nat × List UInt8) := refUN 64
/-- `let s32 s = I32.of_int_s (I64.to_int_s (sN 32 s))` (decode.ml:107), before the wrap. -/
def refS32 : List UInt8 → Option (Int × List UInt8) := refSN 32
/-- `let s33 s = Convert.I32_.wrap_i64 (sN 33 s)` (decode.ml:108), before the wrap. -/
def refS33 : List UInt8 → Option (Int × List UInt8) := refSN 33
/-- `let s64 s = sN 64 s` (decode.ml:109). -/
def refS64 : List UInt8 → Option (Int × List UInt8) := refSN 64

/-- An uninterpreted integer: `sN N` and the two's-complement bit pattern. -/
def refIN (N : Nat) (s : List UInt8) : Option (BitVec N × List UInt8) :=
  (refSN N s).map fun (i, s') => (BitVec.ofInt N i, s')

/-- `i32.const` reads `s32` and keeps the `I32` bit pattern (decode.ml:107). -/
def refI32 : List UInt8 → Option (BitVec 32 × List UInt8) := refIN 32
/-- `i64.const` reads `s64` and keeps the `I64` bit pattern (decode.ml:109). -/
def refI64 : List UInt8 → Option (BitVec 64 × List UInt8) := refIN 64

/-- `len32` (decode.ml:114–118):
```
let len32 s =
  let pos = pos s in
  let n = u32 s in
  if I32.le_u n (Int32.of_int (len s - pos)) then Int32.to_int n else
    error s pos "length out of bounds"
```
`len s - pos` is the input remaining *before* the length field. -/
def refLen32 (s : List UInt8) : Option (Nat × List UInt8) :=
  (refU32 s).bind fun (n, s') => if n ≤ s.length then some (n, s') else none

/-- `get_string n s` (decode.ml:25, with `skip`/`check` from lines 19–20): `n` more bytes,
or `EOS`. -/
def refGetString (n : Nat) (s : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ s.length then some (s.take n, s.drop n) else none

/-- `let name s = let pos = pos s in try Utf8.decode (string s) with Utf8.Utf8 -> error …`
with `let string s = let n = len32 s in get_string n s` (decode.ml:120, 133–136). -/
def refName (s : List UInt8) : Option (List Char × List UInt8) :=
  (refLen32 s).bind fun (n, s') => (refGetString n s').bind fun (str, s'') =>
    (refUtf8Decode str).map fun cs => (cs, s'')

/-! ## Byte arithmetic -/

private theorem byte_bits (b : Nat) (h : b < 256) :
    (b &&& 0x80 = 0 ↔ b < 0x80) ∧ b &&& 0x7f = b % 0x80 ∧
    (b &&& 0x40 = 0 ↔ b % 0x80 < 0x40) ∧
    (b &&& 0xc0 = 0x80 ↔ 0x80 ≤ b ∧ b < 0xc0) ∧
    (0x80 ≤ b → b &&& 0x3f = b - 0x80 ∨ 0xc0 ≤ b) ∧
    (0xc0 ≤ b → b < 0xe0 → b &&& 0x1f = b - 0xc0) ∧
    (0xe0 ≤ b → b < 0xf0 → b &&& 0x0f = b - 0xe0) ∧
    (0xf0 ≤ b → b < 0xf8 → b &&& 0x07 = b - 0xf0) := by
  revert b
  decide +kernel

private theorem cont_val (b : Nat) (h : b < 256) :
    con b = if 0x80 ≤ b ∧ b < 0xc0 then some (b - 0x80) else none := by
  have := byte_bits b h
  unfold con
  by_cases hc : 0x80 ≤ b ∧ b < 0xc0
  · rw [ite_eq_left (this.2.2.2.1.2 hc), ite_eq_left hc]
    rcases this.2.2.2.2.1 hc.1 with h' | h'
    · rw [h']
    · omega
  · rw [ite_eq_right (fun h' => hc (this.2.2.2.1.1 h')), ite_eq_right hc]

private theorem sn_mask (n b : Nat) (hn : 0 < n) (hn7 : n < 7) (hb : b < 256) :
    (b &&& ((0x7f >>> (n - 1)) <<< (n - 1)) = 0 ↔ b % 0x80 < 2 ^ (n - 1)) ∧
    (b &&& ((0x7f >>> (n - 1)) <<< (n - 1)) = (0x7f >>> (n - 1)) <<< (n - 1) ↔
      0x80 - 2 ^ (n - 1) ≤ b % 0x80) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have key : ∀ k, k < 6 → ∀ b, b < 256 →
      (b &&& ((0x7f >>> k) <<< k) = 0 ↔ b % 0x80 < 2 ^ k) ∧
      (b &&& ((0x7f >>> k) <<< k) = (0x7f >>> k) <<< k ↔ 0x80 - 2 ^ k ≤ b % 0x80) := by
    decide +kernel
  exact key k (by omega) b hb

/-! ## UTF-8 -/

private theorem char_toNat_ofNat {n : Nat} (h : n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dite_eq_left (show n.isValidChar from h)]
  rfl

private theorem char_of_valid {n : Nat} (h : n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)) :
    ∃ c : Char, c.toNat = n :=
  ⟨Char.ofNat n, char_toNat_ofNat h⟩

/-! ### `decode'` by cases on the leading byte -/

private theorem decode'_one {b1 : Nat} (bs : List Nat) (h : b1 < 0x80) :
    decode' (b1 :: bs) = (code 0x0 b1).bind fun c => (decode' bs).map (c :: ·) := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_left h]

private theorem decode'_bad {b1 : Nat} (bs : List Nat) (h : 0x80 ≤ b1) (h' : b1 < 0xc0) :
    decode' (b1 :: bs) = none := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_right (show ¬ b1 < 0x80 by omega), ite_eq_left h']

private theorem decode'_short1 {b1 : Nat} (h : 0xc0 ≤ b1) : decode' [b1] = none := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_right (show ¬ b1 < 0x80 by omega), ite_eq_right (show ¬ b1 < 0xc0 by omega)]

private theorem decode'_two {b1 b2 : Nat} (bs : List Nat) (h : 0xc0 ≤ b1) (h' : b1 < 0xe0) :
    decode' (b1 :: b2 :: bs) =
      ((con b2).bind fun c2 => code 0x80 (((b1 &&& 0x1f) <<< 6) + c2)).bind fun c =>
        (decode' bs).map (c :: ·) := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_right (show ¬ b1 < 0x80 by omega), ite_eq_right (show ¬ b1 < 0xc0 by omega),
    ite_eq_left h']

private theorem decode'_short2 {b1 b2 : Nat} (h : 0xe0 ≤ b1) : decode' [b1, b2] = none := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_right (show ¬ b1 < 0x80 by omega), ite_eq_right (show ¬ b1 < 0xc0 by omega),
    ite_eq_right (show ¬ b1 < 0xe0 by omega)]

private theorem decode'_three {b1 b2 b3 : Nat} (bs : List Nat) (h : 0xe0 ≤ b1) (h' : b1 < 0xf0) :
    decode' (b1 :: b2 :: b3 :: bs) =
      ((con b2).bind fun c2 => (con b3).bind fun c3 =>
        code 0x800 (((b1 &&& 0x0f) <<< 12) + (c2 <<< 6) + c3)).bind fun c =>
          (decode' bs).map (c :: ·) := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_right (show ¬ b1 < 0x80 by omega), ite_eq_right (show ¬ b1 < 0xc0 by omega),
    ite_eq_right (show ¬ b1 < 0xe0 by omega), ite_eq_left h']

private theorem decode'_short3 {b1 b2 b3 : Nat} (h : 0xf0 ≤ b1) :
    decode' [b1, b2, b3] = none := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_right (show ¬ b1 < 0x80 by omega), ite_eq_right (show ¬ b1 < 0xc0 by omega),
    ite_eq_right (show ¬ b1 < 0xe0 by omega), ite_eq_right (show ¬ b1 < 0xf0 by omega)]

private theorem decode'_four {b1 b2 b3 b4 : Nat} (bs : List Nat) (h : 0xf0 ≤ b1)
    (h' : b1 < 0xf8) :
    decode' (b1 :: b2 :: b3 :: b4 :: bs) =
      ((con b2).bind fun c2 => (con b3).bind fun c3 => (con b4).bind fun c4 =>
        code 0x10000 (((b1 &&& 0x07) <<< 18) + (c2 <<< 12) + (c3 <<< 6) + c4)).bind
          fun c => (decode' bs).map (c :: ·) := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_right (show ¬ b1 < 0x80 by omega), ite_eq_right (show ¬ b1 < 0xc0 by omega),
    ite_eq_right (show ¬ b1 < 0xe0 by omega), ite_eq_right (show ¬ b1 < 0xf0 by omega),
    ite_eq_left h']

private theorem decode'_high {b1 b2 b3 b4 : Nat} (bs : List Nat) (h : 0xf8 ≤ b1) :
    decode' (b1 :: b2 :: b3 :: b4 :: bs) = none := by
  conv => lhs; rw [decode'.eq_def]
  simp only [ite_eq_right (show ¬ b1 < 0x80 by omega), ite_eq_right (show ¬ b1 < 0xc0 by omega),
    ite_eq_right (show ¬ b1 < 0xe0 by omega), ite_eq_right (show ¬ b1 < 0xf0 by omega),
    ite_eq_right (show ¬ b1 < 0xf8 by omega)]

/-! ### `code` and `con` -/

private theorem code_eq_some {min n c : Nat} (h : code min n = some c) :
    c = n ∧ min ≤ n ∧ ¬ (0xd800 ≤ n ∧ n < 0xe000) ∧ n < 0x110000 := by
  unfold code at h
  split at h
  · cases h
  · rename_i hc
    cases h
    omega

private theorem code_of_valid {min n : Nat} (h₁ : min ≤ n)
    (h₂ : ¬ (0xd800 ≤ n ∧ n < 0xe000)) (h₃ : n < 0x110000) : code min n = some n := by
  unfold code
  rw [ite_eq_right (by omega)]

private theorem bind_con {α : Type} {b : Nat} (hb : b < 256) {f : Nat → Option α} {x : α}
    (h : (con b).bind f = some x) : (0x80 ≤ b ∧ b < 0xc0) ∧ f (b - 0x80) = some x := by
  rw [cont_val b hb] at h
  split at h
  · rename_i hc
    exact ⟨hc, h⟩
  · cases h

private theorem con_of_cont {b : UInt8} (h : IsCont b) : con b.toNat = some (b.toNat - 0x80) := by
  have hb := b.toNat_lt_size
  rw [cont_val _ hb, ite_eq_left (show 0x80 ≤ b.toNat ∧ b.toNat < 0xc0 from h)]

/-- The tail of a successful `decode'` step. -/
private theorem map_cons_eq_some {n : Nat} {r : Option (List Nat)} {ns : List Nat}
    (h : r.map (n :: ·) = some ns) : ∃ ns', r = some ns' ∧ ns = n :: ns' := by
  obtain ⟨ns', h', he⟩ := Option.map_eq_some_iff.mp h
  exact ⟨ns', h', he.symm⟩

/-! ### Soundness and completeness -/

/-- One step of `decode'` on the encoding of a single character. -/
private theorem decode'_char {c : Char} {b : Bytes} (h : Utf8Char c b) (rest : List Nat) :
    decode' (b.map UInt8.toNat ++ rest) = (decode' rest).map (c.toNat :: ·) := by
  have hv : c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) := c.valid
  cases h with
  | one b h e =>
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [decode'_one _ (by omega),
      code_of_valid (min := 0x0) (n := b.toNat) (by omega) (by omega) (by omega), ← e,
      Option.bind_some]
  | two b₁ b₂ lo hi h₁ h₂ e =>
    have hb₁ := b₁.toNat_lt_size
    simp only [UInt8.size] at hb₁
    simp only [Nat.reducePow] at e
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [decode'_two _ (by omega) (by omega), con_of_cont h₂, Option.bind_some,
      (byte_bits _ hb₁).2.2.2.2.2.1 (by omega) (by omega), Nat.shiftLeft_eq,
      show (b₁.toNat - 0xc0) * 2 ^ 6 + (b₂.toNat - 0x80) = c.toNat by omega,
      code_of_valid (min := 0x80) (n := c.toNat) (by omega) (by omega) (by omega), Option.bind_some]
  | three b₁ b₂ b₃ range h₁ h₂ h₃ e =>
    have hb₁ := b₁.toNat_lt_size
    simp only [UInt8.size] at hb₁
    simp only [Nat.reducePow] at e
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    have hlt : b₁.toNat < 0xf0 := by omega
    rw [decode'_three _ h₁ hlt, con_of_cont h₂, Option.bind_some,
      con_of_cont h₃, Option.bind_some, (byte_bits _ hb₁).2.2.2.2.2.2.1 h₁ hlt,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq,
      show (b₁.toNat - 0xe0) * 2 ^ 12 + (b₂.toNat - 0x80) * 2 ^ 6 + (b₃.toNat - 0x80) =
        c.toNat by omega,
      code_of_valid (min := 0x800) (n := c.toNat) (by omega) (by omega) (by omega),
      Option.bind_some]
  | four b₁ b₂ b₃ b₄ lo hi h₁ h₂ h₃ h₄ e =>
    have hb₁ := b₁.toNat_lt_size
    simp only [UInt8.size] at hb₁
    simp only [Nat.reducePow] at e
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    have hlt : b₁.toNat < 0xf8 := by omega
    rw [decode'_four _ h₁ hlt, con_of_cont h₂, Option.bind_some,
      con_of_cont h₃, Option.bind_some, con_of_cont h₄, Option.bind_some,
      (byte_bits _ hb₁).2.2.2.2.2.2.2 h₁ hlt, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
      Nat.shiftLeft_eq,
      show (b₁.toNat - 0xf0) * 2 ^ 18 + (b₂.toNat - 0x80) * 2 ^ 12 +
        (b₃.toNat - 0x80) * 2 ^ 6 +
        (b₄.toNat - 0x80) = c.toNat by omega,
      code_of_valid (min := 0x10000) (n := c.toNat) (by omega) (by omega) (by omega),
      Option.bind_some]

private theorem decode'_of_utf8 {cs : List Char} {b : Bytes} (h : Utf8 cs b) :
    decode' (b.map UInt8.toNat) = some (cs.map Char.toNat) := by
  induction h with
  | nil => rfl
  | cons hc _ ih =>
    rw [List.map_append, decode'_char hc, ih]
    rfl

/-- A successful `decode'` on a nonempty input decoded the encoding of one character. -/
private theorem decode'_cons_some {b₁ : UInt8} {t : Bytes} {ns : List Nat}
    (h : decode' ((b₁ :: t).map UInt8.toNat) = some ns) :
    ∃ c pre rest ns', b₁ :: t = pre ++ rest ∧ pre ≠ [] ∧ Utf8Char c pre ∧
      decode' (rest.map UInt8.toNat) = some ns' ∧ ns = c.toNat :: ns' := by
  have hb₁ := b₁.toNat_lt_size
  simp only [UInt8.size] at hb₁
  rw [List.map_cons] at h
  by_cases r1 : b₁.toNat < 0x80
  · rw [decode'_one _ r1] at h
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, hc⟩ := code_eq_some hn
    obtain ⟨ns', hns', rfl⟩ := map_cons_eq_some h
    obtain ⟨c, e⟩ := char_of_valid (n := b₁.toNat) (by omega)
    exact ⟨c, [b₁], t, ns', rfl, by simp, Utf8Char.one b₁ (by omega) e, hns', by rw [e]⟩
  by_cases r2 : b₁.toNat < 0xc0
  · rw [decode'_bad _ (by omega) r2] at h
    cases h
  match t with
  | [] => rw [List.map_nil, decode'_short1 (by omega)] at h; cases h
  | b₂ :: t =>
    have hb₂ := b₂.toNat_lt_size
    simp only [UInt8.size] at hb₂
    rw [List.map_cons] at h
    by_cases r3 : b₁.toNat < 0xe0
    · rw [decode'_two _ (by omega) r3, (byte_bits _ hb₁).2.2.2.2.2.1 (by omega) r3,
        Nat.shiftLeft_eq] at h
      obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨h₂, hn⟩ := bind_con hb₂ hn
      obtain ⟨hne, hc⟩ := code_eq_some hn
      obtain ⟨ns', hns', rfl⟩ := map_cons_eq_some h
      obtain ⟨c, e⟩ := char_of_valid (n := n) (by omega)
      exact ⟨c, [b₁, b₂], t, ns', rfl, by simp,
        Utf8Char.two b₁ b₂ (by omega) (by omega) (by omega) h₂
          (by rw [e, hne]; simp only [Nat.reducePow]; omega), hns', by rw [e]⟩
    match t with
    | [] => rw [List.map_nil, decode'_short2 (by omega)] at h; cases h
    | b₃ :: t =>
      have hb₃ := b₃.toNat_lt_size
      simp only [UInt8.size] at hb₃
      rw [List.map_cons] at h
      by_cases r4 : b₁.toNat < 0xf0
      · rw [decode'_three _ (by omega) r4, (byte_bits _ hb₁).2.2.2.2.2.2.1 (by omega) r4] at h
        simp only [Nat.shiftLeft_eq] at h
        obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨h₂, hn⟩ := bind_con hb₂ hn
        obtain ⟨h₃, hn⟩ := bind_con hb₃ hn
        obtain ⟨hne, hc⟩ := code_eq_some hn
        obtain ⟨ns', hns', rfl⟩ := map_cons_eq_some h
        obtain ⟨c, e⟩ := char_of_valid (n := n) (by omega)
        exact ⟨c, [b₁, b₂, b₃], t, ns', rfl, by simp,
          Utf8Char.three b₁ b₂ b₃ (by omega) (by omega) h₂ h₃
            (by rw [e, hne]; simp only [Nat.reducePow]; omega), hns', by rw [e]⟩
      match t with
      | [] => rw [List.map_nil, decode'_short3 (by omega)] at h; cases h
      | b₄ :: t =>
        have hb₄ := b₄.toNat_lt_size
        simp only [UInt8.size] at hb₄
        rw [List.map_cons] at h
        by_cases r5 : b₁.toNat < 0xf8
        · rw [decode'_four _ (by omega) r5, (byte_bits _ hb₁).2.2.2.2.2.2.2 (by omega) r5] at h
          simp only [Nat.shiftLeft_eq] at h
          obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨h₂, hn⟩ := bind_con hb₂ hn
          obtain ⟨h₃, hn⟩ := bind_con hb₃ hn
          obtain ⟨h₄, hn⟩ := bind_con hb₄ hn
          obtain ⟨hne, hc⟩ := code_eq_some hn
          obtain ⟨ns', hns', rfl⟩ := map_cons_eq_some h
          obtain ⟨c, e⟩ := char_of_valid (n := n) (by omega)
          exact ⟨c, [b₁, b₂, b₃, b₄], t, ns', rfl, by simp,
            Utf8Char.four b₁ b₂ b₃ b₄ (by omega) (by omega) (by omega) h₂ h₃ h₄
              (by rw [e, hne]; simp only [Nat.reducePow]; omega), hns', by rw [e]⟩
        · rw [decode'_high _ (by omega)] at h
          cases h

private theorem utf8_of_decode' :
    ∀ (b : Bytes) (ns : List Nat), decode' (b.map UInt8.toNat) = some ns →
      ∃ cs, Utf8 cs b ∧ ns = cs.map Char.toNat
  | [], ns, h => by
    rw [List.map_nil, decode'.eq_1, Option.some.injEq] at h
    exact ⟨[], Seq.nil, h.symm⟩
  | b₁ :: t, ns, h => by
    obtain ⟨c, pre, rest, ns', he, hne, hc, hr, rfl⟩ := decode'_cons_some h
    have : rest.length < (b₁ :: t).length := by
      rw [he, List.length_append]
      have := List.length_pos_iff.mpr hne
      omega
    obtain ⟨cs, hcs, rfl⟩ := utf8_of_decode' rest ns' hr
    exact ⟨c :: cs, he ▸ Seq.cons hc hcs, rfl⟩
  termination_by b => b.length

/-- `$utf8` (5.1:52–64, with the errata) agrees exactly with the reference
interpreter's `Utf8.decode`. -/
theorem utf8_iff (cs : List Char) (b : Bytes) : Utf8 cs b ↔ refUtf8Decode b = some cs := by
  have hid : (Char.ofNat ∘ Char.toNat) = id := funext Char.ofNat_toNat
  constructor
  · intro h
    rw [refUtf8Decode, decode'_of_utf8 h, Option.map_some, List.map_map, hid, List.map_id]
  · intro h
    obtain ⟨ns, hns, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨cs', hcs', rfl⟩ := utf8_of_decode' b ns hns
    rwa [List.map_map, hid, List.map_id]

/-! ## LEB128 -/

private theorem refUN_zero (s : List UInt8) : refUN 0 s = none := by
  cases s <;> simp [refUN]

/-- `uN n` consumes exactly a `BuN(n)` encoding (5.1:9–11), for every `n > 0`. -/
theorem refUN_eq_some_iff {N : Nat} (hN : 0 < N) (bs : List UInt8) (n : Nat) (r : List UInt8) :
    refUN N bs = some (n, r) ↔ ∃ b, bs = b ++ r ∧ UN N b n := by
  induction bs generalizing N n with
  | nil =>
    simp only [refUN, reduceCtorEq, List.nil_eq_append_iff, false_iff, not_exists, not_and]
    rintro b ⟨rfl, -⟩ h
    exact UN.ne_nil h
  | cons b s ih =>
    have hb := b.toNat_lt_size
    simp only [UInt8.size] at hb
    have bb := byte_bits b.toNat hb
    constructor
    · intro h
      simp only [refUN] at h
      rw [ite_eq_right (by omega)] at h
      split at h
      · simp at h
      rename_i hchk
      split at h
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlt' := bb.1.mp hlt
        refine ⟨[b], rfl, ?_⟩
        rw [bb.2.1, Nat.mod_eq_of_lt hlt']
        refine UN.byte b hlt' ?_
        rcases not_not.mp hchk with h7 | h7
        · exact Nat.lt_of_lt_of_le hlt' (by
            have := Nat.pow_le_pow_right (by decide : 0 < 2) h7
            simpa using this)
        · rw [bb.2.1, Nat.mod_eq_of_lt hlt', Nat.shiftLeft_eq, Nat.one_mul] at h7
          exact h7
      · rename_i hge
        obtain ⟨⟨m, s'⟩, hm, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hN7 : 7 < N := by
          by_contra hc
          rw [show N - 7 = 0 by omega, refUN_zero] at hm
          simp at hm
        obtain ⟨b', rfl, hb'⟩ := (ih (by omega) m).mp hm
        refine ⟨b :: b', rfl, ?_⟩
        have hge' : 0x80 ≤ b.toNat := by have := bb.1; omega
        have := UN.cont b (by simpa using hge') hN7 hb'
        convert this using 1
        rw [bb.2.1]
        simp only [Nat.reducePow]
        omega
    · rintro ⟨b', hbs, hb'⟩
      cases hb' with
      | byte n' h₁ h₂ =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at hbs
        obtain ⟨rfl, rfl⟩ := hbs
        simp only [Nat.reducePow] at h₁
        simp only [refUN]
        rw [ite_eq_right (by omega), ite_eq_right (by
          rw [bb.2.1, Nat.mod_eq_of_lt h₁, Nat.shiftLeft_eq, Nat.one_mul]
          omega), ite_eq_left (bb.1.mpr h₁), bb.2.1, Nat.mod_eq_of_lt h₁]
      | @cont _ n' b'' m h₁ h₂ rest =>
        simp only [List.cons_append, List.cons.injEq] at hbs
        obtain ⟨rfl, rfl⟩ := hbs
        simp only [Nat.reducePow] at h₁
        simp only [refUN]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by have := bb.1; omega),
          (ih (by omega) m).mpr ⟨b'', rfl, rest⟩]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
        rw [bb.2.1]
        simp only [Nat.reducePow]
        omega

theorem un_iff {N : Nat} (hN : 0 < N) (b : Bytes) (n : Nat) :
    UN N b n ↔ refUN N b = some (n, []) := by
  rw [refUN_eq_some_iff hN]
  simp

/-- `Bu32` agrees with the interpreter's `u32`. -/
theorem u32_iff (b : Bytes) (n : Nat) : U32 b n ↔ refU32 b = some (n, []) :=
  un_iff (by decide) b n

/-- `Bu64` agrees with the interpreter's `u64`. -/
theorem u64_iff (b : Bytes) (n : Nat) : U64 b n ↔ refU64 b = some (n, []) :=
  un_iff (by decide) b n

private theorem refSN_zero (s : List UInt8) : refSN 0 s = none := by
  cases s <;> simp [refSN]

/-- `sN n` consumes exactly a `BsN(n)` encoding (5.1:13–16), for every `n > 0`. -/
theorem refSN_eq_some_iff {N : Nat} (hN : 0 < N) (bs : List UInt8) (i : Int) (r : List UInt8) :
    refSN N bs = some (i, r) ↔ ∃ b, bs = b ++ r ∧ SN N b i := by
  induction bs generalizing N i with
  | nil =>
    simp only [refSN, reduceCtorEq, List.nil_eq_append_iff, false_iff, not_exists, not_and]
    rintro b ⟨rfl, -⟩ h
    cases h
  | cons b s ih =>
    have hb := b.toNat_lt_size
    simp only [UInt8.size] at hb
    have bb := byte_bits b.toNat hb
    -- The range check on a final byte, in arithmetic form.
    have hpow : ∀ k, 6 ≤ k → 2 ^ 6 ≤ 2 ^ k := fun k hk =>
      Nat.pow_le_pow_right (by decide) hk
    have hchk : ∀ (hlt : b.toNat < 0x80),
        (N ≥ 7 ∨ b.toNat &&& ((0x7f >>> (N - 1)) <<< (N - 1)) = 0 ∨
          b.toNat &&& ((0x7f >>> (N - 1)) <<< (N - 1)) = (0x7f >>> (N - 1)) <<< (N - 1)) ↔
        (b.toNat < 2 ^ 6 ∧ b.toNat < 2 ^ (N - 1) ∨
          2 ^ 6 ≤ b.toNat ∧ (2 : Int) ^ 7 - 2 ^ (N - 1) ≤ b.toNat) := by
      intro hlt
      by_cases h7 : N ≥ 7
      · have := hpow (N - 1) (by omega)
        have e : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
        rw [← e]
        simp only [Nat.reducePow] at this ⊢
        omega
      · have hm := sn_mask N b.toNat hN (by omega) hb
        rw [Nat.mod_eq_of_lt hlt] at hm
        rw [hm.1, hm.2]
        have hle : 2 ^ (N - 1) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
        have e : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
        rw [← e]
        simp only [Nat.reducePow] at hle ⊢
        omega
    constructor
    · intro h
      simp only [refSN] at h
      rw [ite_eq_right (by omega)] at h
      split at h
      · simp at h
      rename_i hck
      split at h
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlt' := bb.1.mp hlt
        refine ⟨[b], rfl, ?_⟩
        rw [bb.2.1, Nat.mod_eq_of_lt hlt']
        have hc := (hchk hlt').mp (not_not.mp hck)
        have h40 := bb.2.2.1
        rw [Nat.mod_eq_of_lt hlt'] at h40
        split
        · rename_i h6
          have h6' := h40.mp h6
          rcases hc with hc | hc
          · exact SN.pos b hc.1 hc.2
          · omega
        · rename_i h6
          have h6' : 2 ^ 6 ≤ b.toNat := by
            simp only [Nat.reducePow]
            exact Nat.le_of_not_lt (fun h' => h6 (h40.mpr h'))
          rcases hc with hc | hc
          · omega
          · exact SN.neg b hc.1 (by simpa using hlt') hc.2
      · rename_i hge
        obtain ⟨⟨m, s'⟩, hm, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hN7 : 7 < N := by
          by_contra hc
          rw [show N - 7 = 0 by omega, refSN_zero] at hm
          simp at hm
        obtain ⟨b', rfl, hb'⟩ := (ih (by omega) m).mp hm
        refine ⟨b :: b', rfl, ?_⟩
        have hge' : 0x80 ≤ b.toNat := by have := bb.1; omega
        have := SN.cont b (by simpa using hge') hN7 hb'
        convert this using 1
        rw [bb.2.1]
        simp only [Int.reducePow]
        omega
    · rintro ⟨b', hbs, hb'⟩
      cases hb' with
      | pos n' h₁ h₂ =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at hbs
        obtain ⟨rfl, rfl⟩ := hbs
        have hlt : b.toNat < 0x80 := by simp only [Nat.reducePow] at h₁; omega
        have h40 := bb.2.2.1
        rw [Nat.mod_eq_of_lt hlt] at h40
        simp only [refSN]
        rw [ite_eq_right (by omega),
          ite_eq_right (not_not.mpr ((hchk hlt).mpr (Or.inl ⟨h₁, h₂⟩))),
          ite_eq_left (bb.1.mpr hlt), ite_eq_left (h40.mpr (by simpa using h₁)), bb.2.1,
          Nat.mod_eq_of_lt hlt]
      | neg n' h₁ h₂ h₃ =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at hbs
        obtain ⟨rfl, rfl⟩ := hbs
        have hlt : b.toNat < 0x80 := by simp only [Nat.reducePow] at h₂; omega
        have h40 := bb.2.2.1
        rw [Nat.mod_eq_of_lt hlt] at h40
        simp only [refSN]
        rw [ite_eq_right (by omega),
          ite_eq_right (not_not.mpr ((hchk hlt).mpr (Or.inr ⟨h₁, h₃⟩))),
          ite_eq_left (bb.1.mpr hlt), ite_eq_right (fun h' => by
            have := h40.mp h'
            simp only [Nat.reducePow] at h₁
            omega), bb.2.1, Nat.mod_eq_of_lt hlt]
      | @cont _ n' b'' m h₁ h₂ rest =>
        simp only [List.cons_append, List.cons.injEq] at hbs
        obtain ⟨rfl, rfl⟩ := hbs
        simp only [Nat.reducePow] at h₁
        simp only [refSN]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by have := bb.1; omega),
          (ih (by omega) m).mpr ⟨b'', rfl, rest⟩]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
        rw [bb.2.1]
        simp only [Int.reducePow]
        omega

theorem sn_iff {N : Nat} (hN : 0 < N) (b : Bytes) (i : Int) :
    SN N b i ↔ refSN N b = some (i, []) := by
  rw [refSN_eq_some_iff hN]
  simp

/-- `Bs32 = BsN(32)` agrees with the interpreter's `s32` (before its `I32` wrap). -/
theorem s32_iff (b : Bytes) (i : Int) : SN 32 b i ↔ refS32 b = some (i, []) :=
  sn_iff (by decide) b i

/-- `Bs33` agrees with the interpreter's `s33` (before its `I32` wrap). -/
theorem s33_iff (b : Bytes) (i : Int) : S33 b i ↔ refS33 b = some (i, []) :=
  sn_iff (by decide) b i

/-- `Bs64 = BsN(64)` agrees with the interpreter's `s64`. -/
theorem s64_iff (b : Bytes) (i : Int) : SN 64 b i ↔ refS64 b = some (i, []) :=
  sn_iff (by decide) b i

/-- The uninterpreted `BiN(N)` (5.1:18–19, with erratum E1) agrees with `sN N` followed by
the two's-complement wrap, consuming a prefix. -/
theorem refIN_eq_some_iff {N : Nat} (hN : 0 < N) (bs : List UInt8) (v : BitVec N)
    (r : List UInt8) : refIN N bs = some (v, r) ↔ ∃ b, bs = b ++ r ∧ IN N b v := by
  unfold refIN
  constructor
  · intro h
    obtain ⟨⟨i, r'⟩, hi, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨b, rfl, hb⟩ := (refSN_eq_some_iff hN bs i r').mp hi
    exact ⟨b, rfl, IN.mk hb⟩
  · rintro ⟨b, rfl, ⟨hs⟩⟩
    rw [(refSN_eq_some_iff hN _ _ r).mpr ⟨b, rfl, hs⟩]
    rfl

theorem in_iff {N : Nat} (hN : 0 < N) (b : Bytes) (v : BitVec N) :
    IN N b v ↔ refIN N b = some (v, []) := by
  rw [refIN_eq_some_iff hN]
  simp

/-- `Bi32 = BiN(32)` agrees with the interpreter's `i32.const` immediate. -/
theorem i32_iff (b : Bytes) (v : BitVec 32) : IN 32 b v ↔ refI32 b = some (v, []) :=
  in_iff (by decide) b v

/-- `Bi64 = BiN(64)` agrees with the interpreter's `i64.const` immediate. -/
theorem i64_iff (b : Bytes) (v : BitVec 64) : IN 64 b v ↔ refI64 b = some (v, []) :=
  in_iff (by decide) b v

/-! ## Names -/

private theorem seq_byte_iff (b bs : Bytes) : Seq Byte b bs ↔ b = bs := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hb _ ih =>
      cases hb
      rw [ih]
      rfl
  · rintro rfl
    induction b with
    | nil => exact Seq.nil
    | cons x b ih => exact Seq.cons (b := [x]) (Byte.mk x) ih

/-- `Bname` consumes exactly what the interpreter's `name` consumes: a `u32` length `n`
not exceeding the remaining input, then `n` bytes that `Utf8.decode` accepts. -/
theorem refName_eq_some_iff (bs : List UInt8) (cs : List Char) (r : List UInt8) :
    refName bs = some (cs, r) ↔ ∃ b s, bs = b ++ r ∧ Name b s ∧ s.toList = cs := by
  unfold refName refLen32 refGetString refU32
  constructor
  · intro h
    obtain ⟨⟨n, s'⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨n', s''⟩, hn, he⟩ := Option.bind_eq_some_iff.mp hl
    dsimp only at he h
    by_cases hle' : n' ≤ bs.length
    · rw [ite_eq_left hle'] at he
      cases he
      obtain ⟨⟨str, rest⟩, hg, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at hg h
      by_cases hle : n ≤ s'.length
      · rw [ite_eq_left hle] at hg
        cases hg
        obtain ⟨cs', hd, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        obtain ⟨lb, rfl, hlb⟩ := (refUN_eq_some_iff (by decide) bs n s').mp hn
        refine ⟨lb ++ s'.take n, String.ofList cs, ?_, ?_, String.toList_ofList⟩
        · rw [List.append_assoc, List.take_append_drop]
        · refine Name.mk (bs := s'.take n) (Vec.mk ?_ ((seq_byte_iff _ _).mpr rfl)) ?_
          · rwa [List.length_take, Nat.min_eq_left hle]
          · rw [String.toList_ofList]
            exact (utf8_iff _ _).mpr hd
      · rw [ite_eq_right hle] at hg
        cases hg
    · rw [ite_eq_right hle'] at he
      cases he
  · rintro ⟨b, s, rfl, hn, rfl⟩
    rcases hn with ⟨v, u⟩
    rcases v with ⟨hl, hs⟩
    rw [seq_byte_iff] at hs
    subst hs
    rw [List.append_assoc, (refUN_eq_some_iff (by decide) _ _ _).mpr ⟨_, rfl, hl⟩,
      Option.bind_some]
    dsimp only
    rw [ite_eq_left (by simp only [List.length_append]; omega), Option.bind_some]
    dsimp only
    rw [ite_eq_left (by simp only [List.length_append]; omega), Option.bind_some]
    dsimp only
    rw [List.take_left, List.drop_left, (utf8_iff _ _).mp u]
    rfl

/-- `Bname` (5.1:66–67, with the errata) agrees with the interpreter's `name`. -/
theorem name_iff (b : Bytes) (s : String) : Name b s ↔ refName b = some (s.toList, []) := by
  rw [refName_eq_some_iff]
  constructor
  · intro h
    exact ⟨b, s, by simp, h, rfl⟩
  · rintro ⟨b', s', he, h, hs⟩
    rw [List.append_nil] at he
    subst he
    rwa [String.toList_injective hs] at h

/-! ## Examples

The errata of #650, on the interpreter's side (each by evaluation). -/

/-- `U+0080` is `C2 80`: `$cont` must admit `0x80` (erratum E2, 5.1:49). -/
example : refUtf8Decode [0xC2, 0x80] = some ['\u0080'] := by decide

/-- `U+10FFFF` is accepted and `U+110000` is not (erratum E3, 5.1:63). -/
example : refUtf8Decode [0xF4, 0x8F, 0xBF, 0xBF] = some [Char.ofNat 0x10FFFF] := by decide
example : refUtf8Decode [0xF4, 0x90, 0x80, 0x80] = none := by decide

/-- `41 7F` is `i32.const -1`: uninterpreted integers are signed (erratum E1, 5.1:31). -/
example : refI32 [0x7F] = some (BitVec.ofInt 32 (-1), []) := by decide

/-- The explicit leading-byte bound matters: `00 A0 80` is not `U+0800`. -/
example : refUtf8Decode [0x00, 0xA0, 0x80] = none := by decide

end Silmaril.Wasm.Binary.RefInterp
