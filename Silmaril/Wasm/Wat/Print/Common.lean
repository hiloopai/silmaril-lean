module

public import Silmaril.Wasm.Types
public import Silmaril.Wasm.V1.Types

/-! # WAT printing primitives

Shared, total, kernel-reducible text primitives for the WebAssembly text-format printers
(Lime1 and V1 modules, component-model WAT). `Silmaril/Wasm/Wat` is an elaboration-time
parser; this file is the independent printing side and imports no `meta` code.

Modelled (text grammar of the WebAssembly core specification, chapter "Text Format";
rendered at https://webassembly.github.io/spec/core/text/index.html, pinned in
`specs/wasm/core-3.0.json` at WebAssembly/spec 608711107b7f1edb13efd57b7d79b49477462d36,
sources `specification/wasm-3.0/6.1-text.values.spectec`, `6.2-text.types.spectec`,
`6.3-text.instructions.spectec`):
* integers and floats: https://webassembly.github.io/spec/core/text/values.html#integers
  and `#floating-point` (hexfloat `0x<hexnum>.<hexfrac>p<exp>`, `inf`, `nan:0x<hexnum>`);
* strings and names: https://webassembly.github.io/spec/core/text/values.html#strings and
  `#names` (`\hh` escapes; names are strings whose bytes are valid UTF-8);
* types: https://webassembly.github.io/spec/core/text/types.html;
* memory arguments: https://webassembly.github.io/spec/core/text/instructions.html
  `#memory-instructions` (`offset` defaults to 0, `align` to the natural alignment).

Printed forms:
* decimal naturals and signed integers (`nat`, `int`); integer constants print the
  *unsigned* value of the bit pattern (`i32Const`, `i64Const`), which the text grammar
  accepts for `i32.const`/`i64.const` (it wraps values in `[2^(N-1), 2^N)`);
* floats exactly from their IEEE-754 bit patterns (`f32Bits`, `f64Bits`):
  - zero: `0x0p+0` / `-0x0p+0`;
  - normal: `0x1p<e>` or `0x1.<hex>p<e>` with the fraction bits in lowercase hex,
    trailing zero digits removed (f32: the 23 fraction bits are shifted left by one to
    fill 6 hex digits; f64: 52 bits = 13 hex digits), exponent unbiased and always
    signed (`p+0`, `p-1`, `p+127`);
  - subnormal: `0x0.<hex>p-126` (f32) / `0x0.<hex>p-1022` (f64);
  - infinities `inf` / `-inf`; NaNs always as `nan:0x<payload>` / `-nan:0x<payload>`
    with the exact fraction field as payload (canonical NaNs are *not* abbreviated to
    `nan`), so every bit pattern is printed without loss;
* strings (`string`) over raw bytes: bytes `0x20..0x7e` other than `"` (0x22) and `\`
  (0x5c) are printed literally; every other byte is printed as `\hh` (two lowercase hex
  digits). No `\n`/`\t`/`\"`/`\u{..}` short forms are produced;
* names (`name`): the UTF-8 encoding of a Lean `String` printed by `string`;
* types: `numType`, `valType` (Core 3.0 `ValType`; nullable abstract reference types use
  their abbreviations such as `funcref`, other reference types print `(ref null? ht)`),
  `v1ValType`, `funcTypeText` for `V1.FuncType` (`(func (param i32 i32) (result i32))`,
  empty groups omitted, so `(func)` for `[] -> []`);
* `memarg offset alignExp naturalExp` (alignment stored as log2, as in the AST): prints
  `offset=N` only when `N ≠ 0` and `align=2^a` only when `a ≠ naturalExp`;
* layout helpers `paren`, `sexp`, `indent`, `lines`.

Not modelled / not claimed: no parser round-trip theorem is proved here (round-tripping
is the concern of the module printers and the external `wasm-tools` harness); no
injectivity theorem for `f32Bits`/`f64Bits` is stated. Identifiers (`$x`) are never printed:
printers use index references only. -/

@[expose] public section

namespace Silmaril.Wasm.Wat.Print

/-! ## Digits -/

/-- Lowercase hexadecimal digit for `n % 16`. -/
def hexDigit (n : Nat) : Char :=
  match n % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e'
  | _ => 'f'

/-- Digits of `n` in base `base` (most significant first), prepended to `acc`.
Structural recursion on `fuel`; `fuel ≥ n + 1` always suffices for `base ≥ 2`. -/
def digitsAux (base : Nat) : (fuel n : Nat) → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc := hexDigit (n % base) :: acc
    if n < base then acc else digitsAux base fuel (n / base) acc

/-- Digits of `n` in base `base` (`2 ≤ base ≤ 16`), without leading zeros; `0` is `['0']`. -/
def digits (base n : Nat) : List Char := digitsAux base (n + 1) n []

/-- Exactly `width` hexadecimal digits of `n % 16^width`, most significant first. -/
def hexFixed : (width n : Nat) → List Char → List Char
  | 0, _, acc => acc
  | w + 1, n, acc => hexFixed w (n / 16) (hexDigit n :: acc)

/-- Drop trailing `'0'` characters. -/
def dropTrailingZeros (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '0')).reverse

/-! ## Integers -/

/-- Decimal natural number. -/
def nat (n : Nat) : String := String.ofList (digits 10 n)

/-- Lowercase hexadecimal natural number with `0x` prefix. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (digits 16 n)

/-- Signed decimal integer (`-` for negatives, no `+`). -/
def int : Int → String
  | .ofNat n => nat n
  | .negSucc n => "-" ++ nat (n + 1)

/-- Unsigned decimal value of a bit pattern (accepted by `iN.const`). -/
def bitsConst {n : Nat} (b : BitVec n) : String := nat b.toNat

/-- `i32.const` immediate: the unsigned decimal value of the bit pattern. -/
def i32Const (b : BitVec 32) : String := bitsConst b

/-- `i64.const` immediate: the unsigned decimal value of the bit pattern. -/
def i64Const (b : BitVec 64) : String := bitsConst b

/-! ## Floats -/

/-- Exponent suffix `p+e` / `p-e` (always signed). -/
def expSuffix (e : Int) : String :=
  match e with
  | .ofNat n => "p+" ++ nat n
  | .negSucc n => "p-" ++ nat (n + 1)

/-- Exact hexfloat text of an IEEE-754 binary interchange bit pattern `bits` with
`expBits` exponent bits and `fracBits` fraction bits (see the module docstring for the
produced forms). `bits` is reduced modulo `2^(1 + expBits + fracBits)`. -/
def floatBits (expBits fracBits : Nat) (bits : Nat) : String :=
  let frac := bits % 2 ^ fracBits
  let expField := (bits / 2 ^ fracBits) % 2 ^ expBits
  let sign := if (bits / 2 ^ (fracBits + expBits)) % 2 = 1 then "-" else ""
  let maxExp := 2 ^ expBits - 1
  let bias : Nat := 2 ^ (expBits - 1) - 1
  -- fraction left-aligned to a whole number of hex digits
  let width := (fracBits + 3) / 4
  let aligned := frac * 2 ^ (4 * width - fracBits)
  let fracHex := String.ofList (dropTrailingZeros (hexFixed width aligned []))
  if expField = maxExp then
    if frac = 0 then sign ++ "inf" else sign ++ "nan:" ++ hex frac
  else if expField = 0 then
    if frac = 0 then sign ++ "0x0p+0"
    else sign ++ "0x0." ++ fracHex ++ expSuffix (1 - (bias : Int))
  else
    let mant := if frac = 0 then "0x1" else "0x1." ++ fracHex
    sign ++ mant ++ expSuffix ((expField : Int) - bias)

/-- Exact WAT text of an `f32` bit pattern. -/
def f32Bits (b : BitVec 32) : String := floatBits 8 23 b.toNat

/-- Exact WAT text of an `f64` bit pattern. -/
def f64Bits (b : BitVec 64) : String := floatBits 11 52 b.toNat

/-! ## Strings and names -/

/-- Whether a byte is printed literally inside a WAT string: printable ASCII except
`"` and `\`. -/
def literalByte (b : UInt8) : Bool :=
  0x20 ≤ b.toNat && b.toNat < 0x7f && b.toNat != 0x22 && b.toNat != 0x5c

/-- The characters for one byte inside a WAT string literal. -/
def byteChars (b : UInt8) : List Char :=
  if literalByte b then [Char.ofNat b.toNat] else ['\\', hexDigit (b.toNat / 16), hexDigit b.toNat]

/-- WAT string literal (with quotes) for a byte sequence; non-literal bytes use `\hh`. -/
def string (bs : List UInt8) : String :=
  String.ofList ('"' :: (bs.flatMap byteChars ++ ['"']))

/-- WAT string literal for a name: its UTF-8 bytes, escaped by `string`. -/
def name (s : String) : String := string s.toByteArray.data.toList

/-! ## Types -/

/-- Text of a numeric type. -/
def numType : NumType → String
  | .int .i32 => "i32"
  | .int .i64 => "i64"
  | .float .f32 => "f32"
  | .float .f64 => "f64"

/-- Text of a WebAssembly 1.0 / Lime1 value type (these are numeric types). -/
def v1ValType (t : V1.ValType) : String := numType t

/-- Text keyword of an abstract heap type. -/
def absHeapType : AbsHeapType → String
  | .any => "any" | .eq => "eq" | .i31 => "i31" | .struct => "struct" | .array => "array"
  | .none => "none" | .func => "func" | .nofunc => "nofunc" | .exn => "exn"
  | .noexn => "noexn" | .extern => "extern" | .noextern => "noextern"

/-- Abbreviation `(ref null ht)` = `htref` for nullable abstract heap types. -/
def absHeapTypeRef : AbsHeapType → String
  | .any => "anyref" | .eq => "eqref" | .i31 => "i31ref" | .struct => "structref"
  | .array => "arrayref" | .none => "nullref" | .func => "funcref"
  | .nofunc => "nullfuncref" | .exn => "exnref" | .noexn => "nullexnref"
  | .extern => "externref" | .noextern => "nullexternref"

/-- Text of a heap type (type indices print as decimal indices). -/
def heapType : HeapType → String
  | .abstract t => absHeapType t
  | .typeIdx i => nat i.value.val

/-- Text of a reference type. -/
def refType (t : RefType) : String :=
  match t.nullable, t.heap with
  | true, .abstract a => absHeapTypeRef a
  | true, h => "(ref null " ++ heapType h ++ ")"
  | false, h => "(ref " ++ heapType h ++ ")"

/-- Text of a Core 3.0 value type. -/
def valType : ValType → String
  | .num t => numType t
  | .vec .v128 => "v128"
  | .ref t => refType t

/-! ## Layout -/

/-- Join with a separator (structural; `String.intercalate` does not reduce in the kernel
from a module). -/
def joinSep (sep : String) : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ sep ++ joinSep sep rest

/-- Join with single spaces, skipping empty parts. -/
def spaced (parts : List String) : String :=
  joinSep " " (parts.filter (· != ""))

/-- `(s)`. -/
def paren (s : String) : String := "(" ++ s ++ ")"

/-- `(head arg₁ … argₙ)`, empty arguments skipped. -/
def sexp (head : String) (args : List String) : String := paren (spaced (head :: args))

/-- Prefix each line with `2 * depth` spaces. -/
def indent (depth : Nat) (ls : List String) : List String :=
  let pad := String.ofList (List.replicate (2 * depth) ' ')
  ls.map (pad ++ ·)

/-- Join lines with `\n` (no trailing newline). -/
def lines (ls : List String) : String := joinSep "\n" ls

/-- `(func (param …) (result …))`; empty `param`/`result` groups are omitted. -/
def funcTypeText (t : V1.FuncType) : String :=
  let params := if t.params.isEmpty then "" else sexp "param" (t.params.map v1ValType)
  let results := if t.results.isEmpty then "" else sexp "result" (t.results.map v1ValType)
  sexp "func" [params, results]

/-- Memory-argument text `offset=N align=M`, printing only non-default fields. The
alignment is given as its log2 `alignExp` (as stored in `MemArg`) and printed in bytes;
it is omitted when equal to the natural alignment `naturalExp`. Empty when both are
default. -/
def memarg (offset alignExp naturalExp : Nat) : String :=
  let o := if offset = 0 then "" else "offset=" ++ nat offset
  let a := if alignExp = naturalExp then "" else "align=" ++ nat (2 ^ alignExp)
  spaced [o, a]

/-! ## Lemmas and examples

`hexDigit_lt` is the only general lemma. The theorems after it are kernel-checked
examples (`f32Bits_one`,
`f32Bits_canonical_nan`, `f32Bits_neg_canonical_nan`, `f64Bits_neg_zero`,
`string_example`, `i32Const_max`) plus extra coverage of each printer. -/

/-- Hex digits are ASCII, so the escapes and hexfloats built from them stay ASCII. -/
theorem hexDigit_lt (n : Nat) : (hexDigit n).toNat < 128 := by
  unfold hexDigit
  have : n % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize n % 16 = m at this
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;>
    first | decide | omega

theorem f32Bits_one : f32Bits 0x3f800000#32 = "0x1p+0" := by decide +kernel
theorem f32Bits_one_half : f32Bits 0x3fc00000#32 = "0x1.8p+0" := by decide +kernel
theorem f32Bits_max : f32Bits 0x7f7fffff#32 = "0x1.fffffep+127" := by decide +kernel
theorem f32Bits_min_subnormal : f32Bits 0x00000001#32 = "0x0.000002p-126" := by
  decide +kernel
theorem f32Bits_canonical_nan : f32Bits 0x7fc00000#32 = "nan:0x400000" := by decide +kernel
theorem f32Bits_neg_canonical_nan : f32Bits 0xffc00000#32 = "-nan:0x400000" := by
  decide +kernel
theorem f32Bits_inf : f32Bits 0x7f800000#32 = "inf" := by decide +kernel
theorem f32Bits_neg_inf : f32Bits 0xff800000#32 = "-inf" := by decide +kernel
theorem f32Bits_zero : f32Bits 0#32 = "0x0p+0" := by decide +kernel
theorem f64Bits_neg_zero : f64Bits 0x8000000000000000#64 = "-0x0p+0" := by decide +kernel
theorem f64Bits_one : f64Bits 0x3ff0000000000000#64 = "0x1p+0" := by decide +kernel
theorem f64Bits_neg_two : f64Bits 0xc000000000000000#64 = "-0x1p+1" := by decide +kernel
theorem f64Bits_tenth : f64Bits 0x3fb999999999999a#64 = "0x1.999999999999ap-4" := by
  decide +kernel
theorem f64Bits_min_subnormal : f64Bits 1#64 = "0x0.0000000000001p-1022" := by
  decide +kernel
theorem f64Bits_nan : f64Bits 0x7ff8000000000000#64 = "nan:0x8000000000000" := by
  decide +kernel

/-- `[0x61, 0x22, 0x00]` prints as the 11-character text `"a\22\00"`. -/
theorem string_example : string [0x61, 0x22, 0x00] = "\"a\\22\\00\"" := by decide +kernel
theorem string_backslash : string [0x5c, 0x7f, 0x0a] = "\"\\5c\\7f\\0a\"" := by
  decide +kernel
theorem name_example : name "héllo" = "\"h\\c3\\a9llo\"" := by decide +kernel

theorem i32Const_max : i32Const 0xffffffff#32 = "4294967295" := by decide +kernel
theorem i64Const_max : i64Const (-1 : BitVec 64) = "18446744073709551615" := by
  decide +kernel
theorem nat_zero : nat 0 = "0" := by decide +kernel
theorem int_neg : int (-42) = "-42" := by decide +kernel
theorem hex_example : hex 0xabc = "0xabc" := by decide +kernel

theorem funcTypeText_example :
    funcTypeText ⟨[V1.ValType.i32, V1.ValType.i32], [V1.ValType.i32]⟩ =
      "(func (param i32 i32) (result i32))" := by decide +kernel
theorem funcTypeText_empty : funcTypeText ⟨[], []⟩ = "(func)" := by decide +kernel
theorem valType_funcref : valType (.ref ⟨true, .abstract .func⟩) = "funcref" := by
  decide +kernel
theorem valType_ref_idx : valType (.ref ⟨false, .typeIdx ⟨3⟩⟩) = "(ref 3)" := by
  decide +kernel

theorem memarg_default : memarg 0 2 2 = "" := by decide +kernel
theorem memarg_both : memarg 8 0 2 = "offset=8 align=1" := by decide +kernel
theorem lines_indent : lines (indent 1 ["a", "b"]) = "  a\n  b" := by decide +kernel

end Silmaril.Wasm.Wat.Print
