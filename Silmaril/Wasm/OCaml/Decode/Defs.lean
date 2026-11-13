module

public import Silmaril.Raw.Wasm.OCaml.RefInterp.Gen.Program
public import Silmaril.ML.OCaml.Interp.Defs
public import Silmaril.Wasm.SpecTec.Defs

/-!
# The reference interpreter's LEB128 decoders, imported from their OCaml source

`interpreter/binary/decode.ml` at `WebAssembly/spec@608711107b` and what its integer
decoders reach (`Wasm.Source`, `Wasm.Error`, `Wasm.Ixx`, `Wasm.I32`, `Wasm.I64` and 17 units
of the OCaml 5.4.1 standard library), imported by an OCaml-to-Lean import tool from the compiler's
typed trees (`specs/ml/refinterp-pin`) and linked by the semantics of `Silmaril.ML.OCaml`.

`decode.mli` exports only `decode` and `decode_with_custom`, so `uN`, `u32`, `sN`, `s32`,
`u64` and `s64` are appended to the export list of the unit `Wasm__Decode` (`decodeUnit`).
That adds fields at the end of the unit's module value and changes nothing else: no unit is
linked after it. The decoders read a

```
type stream = {name : string; bytes : string; pos : int ref}
```

which is an immutable record holding a `ref`: the block `[name, bytes, loc ℓ]`, with the
position in the store cell `ℓ` (`streamAt`). A decoding error raises `Code (region, msg)`,
the exception that the generative functor application `module Code = Error.Make ()`
allocated at link time (`codeExn`).
-/

@[expose] public section
namespace Silmaril.Wasm.OCaml.Decode

open Silmaril.ML.OCaml
open Silmaril.Wasm.OCaml.RefInterp.Gen

/-- The decoders, by position after `decode.mli`'s three exports. -/
inductive Decoder where
  | uN | u32 | sN | s32 | u64 | s64
  deriving DecidableEq, Repr

/-- The identifiers of the decoders in the import (name and type-checker stamp). -/
def Decoder.ident : Decoder → Ident
  | .uN => ⟨"uN", 822⟩
  | .u32 => ⟨"u32", 940⟩
  | .sN => ⟨"sN", 827⟩
  | .s32 => ⟨"s32", 949⟩
  | .u64 => ⟨"u64", 943⟩
  | .s64 => ⟨"s64", 971⟩

def Decoder.all : List Decoder := [.uN, .u32, .sN, .s32, .u64, .s64]

/-- `Wasm__Decode` with the decoders exported. -/
def decodeUnit : CUnit :=
  { WasmDecode.unit with exports := WasmDecode.unit.exports ++ Decoder.all.map Decoder.ident }

/-- The linked program: `RefInterp.Gen.program` with `decodeUnit` for its last unit. -/
def program : Program := RefInterp.Gen.program.dropLast ++ [decodeUnit]

/-- `decodeUnit` is the last unit of the generated program. -/
theorem program_last : RefInterp.Gen.program.getLast? = some WasmDecode.unit := rfl

def fuel : Nat := 1000000

/-- The store after linking. -/
def linked : Option Store :=
  match initProg .rtl fuel program with
  | .ok (.ret _) st => some st
  | _ => none

/-- The module value of `Wasm__Decode` after linking. -/
def decodeFields : Option (List Value) := do
  let st ← linked
  match st.globals.lookup "Wasm__Decode" with
  | some (.mod fs) => some fs
  | _ => none

def Decoder.index : Decoder → Nat
  | .uN => 0 | .u32 => 1 | .sN => 2 | .s32 => 3 | .u64 => 4 | .s64 => 5

/-- The closure a decoder denotes after linking. -/
def Decoder.value? (d : Decoder) : Option Value := do
  let fs ← decodeFields
  fs[3 + d.index]?

/-- The identity of `Code`, the exception that `module Code = Error.Make ()` allocated and
`exception Code = Code.Error` rebinds: `Wasm__Decode`'s first export (`decode.mli`). -/
def codeExnId? : Option Nat := do
  let fs ← decodeFields
  match fs[0]? with
  | some (Value.exnTag i _) => some i
  | _ => none

/-- The stream `{name = ""; bytes = bs; pos = ℓ}` with `!ℓ = p`, allocated in `st`. -/
def streamAt (bs : List UInt8) (p : Nat) (st : Store) : Value × Store :=
  let (l, st) := st.alloc (.fields [.ofInt p])
  (.block 0 [.str [], .str bs, .loc l], st)

/-- Apply decoder `d` to `args` and a fresh stream over `bs` at position `p`, after
linking. -/
def run (d : Decoder) (args : List Value) (bs : List UInt8) (p : Nat) : Res :=
  match linked, d.value? with
  | some st, some f =>
    let (s, st) := streamAt bs p st
    interp .rtl fuel st [] (.apply f (args ++ [s]))
  | _, _ => .stuck "link"

/-- What a decoder run did: returned a value with the stream at a new position, raised
`Code`, or anything else (another exception, stuck, out of fuel). -/
inductive Out where
  | ok (v : Value) (pos : Nat)
  | code
  | other

/-- The position cell is the last cell allocated (`streamAt`). -/
def out (r : Res) : Out :=
  match r with
  | .ok (.ret v) st => match st.cells.getLast? with
    | some (.fields [.int p]) => .ok v p.toNat
    | _ => .other
  | .ok (.exn (.exn i _ _)) _ => if codeExnId? = some i then .code else .other
  | _ => .other

/-! ## Agreement with silmaril-lean's transcription -/

open Silmaril.Wasm.Binary.RefInterp

/-- The run of an unsigned decoder agrees with `refUN N`. `mk` is how the decoder returns
the number. -/
def agreesU (N : Nat) (mk : Value → Option Nat) (r : Out) (bs : List UInt8) (p : Nat) : Bool :=
  match refUN N (bs.drop p), r with
  | some (m, rest), .ok v q => mk v == some m && q == bs.length - rest.length
  | none, .code => true
  | _, _ => false

/-- The run of a signed decoder agrees with `refSN N`, wrapped to `W` bits. -/
def agreesS (N : Nat) (mk : Value → Option Int) (r : Out) (bs : List UInt8) (p : Nat) : Bool :=
  match refSN N (bs.drop p), r with
  | some (i, rest), .ok v q => mk v == some i && q == bs.length - rest.length
  | none, .code => true
  | _, _ => false

def asU32 : Value → Option Nat | .int32 x => some x.toNat | _ => none
def asU64 : Value → Option Nat | .int64 x => some x.toNat | _ => none
def asS32 : Value → Option Int | .int32 x => some x.toInt | _ => none
def asS64 : Value → Option Int | .int64 x => some x.toInt | _ => none

/-- Test cases `(bytes, start position)` for `u32`: one-byte encodings, the largest value,
values one bit too large, an overlong encoding that is allowed (five bytes) and the first that
is too long (six), end of stream inside an encoding, a value above `2 ^ 31` (the path through
the 63-bit `int`: `I64.to_int_u` then `I32.of_int_u`), and starts behind a junk byte. -/
def u32Cases : List (List UInt8 × Nat) :=
  [([], 0), ([0x00], 0), ([0x7f], 0), ([0x80], 0), ([0x80, 0x01], 0), ([0xe5, 0x8e, 0x26], 0),
   ([0xff, 0xff, 0xff, 0xff, 0x0f], 0), ([0xff, 0xff, 0xff, 0xff, 0x1f], 0),
   ([0xff, 0xff, 0xff, 0xff, 0x10], 0), ([0x80, 0x80, 0x80, 0x80, 0x00], 0),
   ([0x80, 0x80, 0x80, 0x80, 0x80, 0x00], 0), ([0xff, 0xff, 0xff, 0xff], 0),
   ([0x83, 0x80, 0x80, 0x80, 0x08, 0x2a], 0), ([0x55, 0xe5, 0x8e, 0x26], 1), ([0x55, 0x80], 1)]

/-- Test cases for `u64`: the largest value (ten bytes), one bit too large, the longest
allowed overlong encoding and the first too long, end of stream, an offset start. -/
def u64Cases : List (List UInt8 × Nat) :=
  [([0x00], 0), ([0x7f], 0), ([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01], 0),
   ([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02], 0),
   ([0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00], 0),
   ([0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00], 0),
   ([0x80, 0x80, 0x80], 0), ([0x55, 0xe5, 0x8e, 0x26], 1)]

/-- Test cases for `s32`: positive and negative one-byte values, `FF 7E` (= -129;
silmaril-lean#803), the extreme values, values just out of range on either side, end of
stream, an offset start. -/
def s32Cases : List (List UInt8 × Nat) :=
  [([0x00], 0), ([0x3f], 0), ([0x40], 0), ([0x7f], 0), ([0x80, 0x7f], 0), ([0xff, 0x7e], 0),
   ([0xc0, 0xbb, 0x78], 0), ([0xff, 0xff, 0xff, 0xff, 0x07], 0),
   ([0x80, 0x80, 0x80, 0x80, 0x78], 0), ([0xff, 0xff, 0xff, 0xff, 0x0f], 0),
   ([0x80, 0x80, 0x80, 0x80, 0x70], 0), ([0x80, 0x80], 0), ([0x55, 0x7f], 1)]

/-- Test cases for `s64`: `-1` overlong, the extreme values (ten bytes; the last byte's mask
is `(-1 lsl 0) land 0x7f`), a last byte that is neither sign extension, end of stream. The
mask of the first byte is `(-1 lsl 63) land 0x7f`: a shift by `Sys.int_size`, which OCaml
defines. -/
def s64Cases : List (List UInt8 × Nat) :=
  [([0x7f], 0), ([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f], 0),
   ([0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f], 0),
   ([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00], 0),
   ([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01], 0), ([], 0)]

end Silmaril.Wasm.OCaml.Decode
