module

public import Silmaril.Wasm.Tools.Gen.API.Defs
public import Silmaril.Wasm.Models.Syntax.Defs

/-!
# The text form of generated modules, as `wasm-tools print` writes it

`printModule? m` writes the WebAssembly text of `m` in the layout of wasmprinter (wasm-tools
1.262.0) for the fragment that `smith` generates and `mutate` and `shrink` produce from it:
function types, function and global imports, `funcref` tables, memories, globals, exports, a
start function, active element segments, functions with scalar and reference code, and data
segments, SIMD (the operators `smith` generates), `call_indirect`, tail calls, several
memories and tables, and struct and array types, tags, `try_table`, table, GC,
exception and relaxed SIMD instructions, 64-bit memories, passive and declarative element
segments. Outside that fragment (recursion groups of several types, subtyping, typed
function references, non-dyadic float constants …) it returns `none`; the
subcommands then report that the text form is not supported (`docs/projects/wasm-components.md`, Known
limitations). The full printer is the cli track's (`wasm-tools print`).

The layout is checked against upstream by `tools/wasm-tools/tests/gen/fuzz.sh`: for every
seed, `wasm-tools-gen smith -t` equals upstream `wasm-tools print` of `wasm-tools-gen smith`.

Floats: `0x1.8p+0 (;=1.5;)`; the decimal comment is exact for the dyadic rationals
`k / 2^j` with `k < 2^11`, `j ≤ 3` (the shortest round-trip decimal Rust prints is the exact
one there), and `printModule?` refuses other non-zero finite values.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Print

open Silmaril.Wasm

/-- Hex digit. -/
def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD (n % 16) '0'

/-- Two lowercase hex digits. -/
def hex2 (n : Nat) : String := String.ofList [hexDigit (n / 16), hexDigit n]

/-- A string literal of data bytes: printable ASCII except `"` and `\` verbatim, others as
`\xx`. -/
def dataString (bs : List UInt8) : String :=
  "\"" ++ String.join (bs.map fun b =>
    let n := b.toNat
    if 0x20 ≤ n && n < 0x7f && n != 0x22 && n != 0x5c then String.singleton (Char.ofNat n)
    else "\\" ++ hex2 n) ++ "\""

/-- A name literal: only plain printable names are supported (`none` otherwise). -/
def nameString (s : String) : Option String :=
  if s.toList.all fun c => 0x20 ≤ c.toNat && c.toNat < 0x7f && c != '"' && c != '\\' then
    some ("\"" ++ s ++ "\"")
  else none

/-- A signed decimal of a `w`-bit pattern. -/
def signed (w : Nat) (n : Nat) : String :=
  if n ≥ 2 ^ (w - 1) then "-" ++ toString (2 ^ w - n) else toString n

def valType : ValType → Option String
  | .num (.int .i32) => some "i32"
  | .num (.int .i64) => some "i64"
  | .num (.float .f32) => some "f32"
  | .num (.float .f64) => some "f64"
  | .vec _ => some "v128"
  | .ref ⟨true, .abstract .func⟩ => some "funcref"
  | .ref ⟨true, .abstract .extern⟩ => some "externref"
  | .ref ⟨true, .abstract .exn⟩ => some "exnref"
  | .ref ⟨true, .abstract .any⟩ => some "anyref"
  | .ref ⟨true, .abstract .eq⟩ => some "eqref"
  | .ref ⟨true, .abstract .i31⟩ => some "i31ref"
  | .ref ⟨true, .abstract .struct⟩ => some "structref"
  | .ref ⟨true, .abstract .array⟩ => some "arrayref"
  | _ => none

def absHeap : AbsHeapType → String
  | .any => "any" | .eq => "eq" | .i31 => "i31" | .struct => "struct" | .array => "array"
  | .none => "none" | .func => "func" | .nofunc => "nofunc" | .exn => "exn"
  | .noexn => "noexn" | .extern => "extern" | .noextern => "noextern"

def heapType : HeapType → Option String
  | .abstract h => some (absHeap h)
  | .typeIdx i => some (toString i.toNat)

/-- A reference type in its long form `(ref null? heap)`. -/
def refTypeLong (r : RefType) : Option String := do
  return "(ref " ++ (if r.nullable then "null " else "") ++ (← heapType r.heap) ++ ")"

/-- `(param …) (result …)` with a leading space per group (empty groups omitted). -/
def sig (ft : FuncType) : Option String := do
  let ps ← ft.params.mapM valType
  let rs ← ft.results.mapM valType
  let p := if ps.isEmpty then "" else " (param " ++ " ".intercalate ps ++ ")"
  let r := if rs.isEmpty then "" else " (result " ++ " ".intercalate rs ++ ")"
  return p ++ r

/-! ## Floats -/

/-- The fraction digits of `num / 2^j` in decimal (`num < 2^j`), trailing zeros dropped. -/
def fracDigits : Nat → Nat → Nat → String
  | 0, _, _ => ""
  | fuel + 1, num, den =>
    if num = 0 then "" else
      let d := num * 10 / den
      String.singleton (hexDigit d) ++ fracDigits fuel (num * 10 % den) den

/-- Hex and decimal text of a float with `mbits` fraction bits and bias `bias`, `none` when
the decimal is not exact (see the module doc). -/
def floatText (w mbits bias : Nat) (bits : Nat) : Option String := do
  let neg := bits ≥ 2 ^ (w - 1)
  let mag := bits % 2 ^ (w - 1)
  let sgn := if neg then "-" else ""
  let ex := mag / 2 ^ mbits
  let frac := mag % 2 ^ mbits
  if mag = 0 then return s!"{sgn}0x0p+0 (;={sgn}0;)"
  if ex = 0 || ex = 2 ^ (w - 1 - mbits) - 1 then none
  let e : Int := (ex : Int) - bias
  -- hex: the fraction padded to a multiple of 4 bits, trailing zeros dropped
  let pad := (4 - mbits % 4) % 4
  let digits := (mbits + pad) / 4
  let f := frac * 2 ^ pad
  let hs := (List.range digits).reverse.map fun i => hexDigit (f / 16 ^ i)
  let hs := (hs.reverse.dropWhile (· == '0')).reverse
  let hexs := if hs.isEmpty then "0x1" else "0x1." ++ String.ofList hs
  let es := if e ≥ 0 then s!"p+{e}" else s!"p{e}"
  -- exact decimal of value = m / 2^(mbits - e): at most 11 significant bits, `|value| < 2^11`,
  -- and `8 · value` an integer
  let m := 2 ^ mbits + frac
  if m % 2 ^ (mbits - 10) != 0 || e > 10 then none
  let den := 2 ^ (mbits - e).toNat
  if m * 8 % den != 0 then none
  let ip := m / den
  let fnum := m % den
  let dec := toString ip ++ (if fnum = 0 then "" else "." ++ fracDigits 64 fnum den)
  return s!"{sgn}{hexs}{es} (;={sgn}{dec};)"

/-! ## Instructions -/

def sx : Signedness → String
  | .signed => "s"
  | .unsigned => "u"

def it : IntType → String
  | .i32 => "i32"
  | .i64 => "i64"

def ft : FloatType → String
  | .f32 => "f32"
  | .f64 => "f64"

def intBin : IntBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div s => "div_" ++ sx s
  | .rem s => "rem_" ++ sx s | .and => "and" | .or => "or" | .xor => "xor" | .shl => "shl"
  | .shr s => "shr_" ++ sx s | .rotl => "rotl" | .rotr => "rotr"

def intUn : IntUnOp → String
  | .clz => "clz" | .ctz => "ctz" | .popcnt => "popcnt"
  | .extend p => s!"extend{p.width}_s"

def intRel : IntRelOp → String
  | .eq => "eq" | .ne => "ne" | .lt s => "lt_" ++ sx s | .gt s => "gt_" ++ sx s
  | .le s => "le_" ++ sx s | .ge s => "ge_" ++ sx s

def floatUn : FloatUnOp → String
  | .abs => "abs" | .neg => "neg" | .sqrt => "sqrt" | .ceil => "ceil" | .floor => "floor"
  | .trunc => "trunc" | .nearest => "nearest"

def floatBin : FloatBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .min => "min"
  | .max => "max" | .copysign => "copysign"

def floatRel : FloatRelOp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .gt => "gt" | .le => "le" | .ge => "ge"

def convert : ConvertOp → String
  | .wrap => "i32.wrap_i64"
  | .extend s => "i64.extend_i32_" ++ sx s
  | .trunc a b s => s!"{it b}.trunc_{ft a}_{sx s}"
  | .truncSat a b s => s!"{it b}.trunc_sat_{ft a}_{sx s}"
  | .convert a b s => s!"{ft b}.convert_{it a}_{sx s}"
  | .demote => "f32.demote_f64"
  | .promote => "f64.promote_f32"
  | .reinterpretInt .f32 => "i32.reinterpret_f32"
  | .reinterpretInt .f64 => "i64.reinterpret_f64"
  | .reinterpretFloat .i32 => "f32.reinterpret_i32"
  | .reinterpretFloat .i64 => "f64.reinterpret_i64"

/-- ` offset=…` and ` align=…` when they differ from the defaults. -/
def memArg (natural : Nat) (a : MemArg) : String :=
  (if a.offset.val = 0 then "" else s!" offset={a.offset.val}") ++
  (if a.align.val = natural then "" else s!" align={2 ^ a.align.val}")

def packW : PackSize → Nat
  | .i8 => 8 | .i16 => 16 | .i32 => 32 | .i64 => 64

def packA : PackSize → Nat
  | .i8 => 0 | .i16 => 1 | .i32 => 2 | .i64 => 3

def intA : IntType → Nat
  | .i32 => 2 | .i64 => 3

def floatA : FloatType → Nat
  | .f32 => 2 | .f64 => 3

/-- A memory index operand: nothing for memory 0 (wasmprinter's default). -/
def memIx (x : MemIdx) : String := if x.toNat = 0 then "" else s!" {x.toNat}"

/-- The 32-bit hex lanes of a `v128` constant (`i32x4`, little-endian lanes). -/
def v128Text (b : BitVec 128) : String :=
  let n := b.toNat
  let lanes := (List.range 4).map fun k => (n / 2 ^ (32 * k)) % 2 ^ 32
  "v128.const i32x4" ++ String.join (lanes.map fun l =>
    " 0x" ++ String.ofList ((List.range 8).reverse.map fun i => hexDigit (l / 16 ^ i)))

def ishape : IntShape → String
  | .i8x16 => "i8x16" | .i16x8 => "i16x8" | .i32x4 => "i32x4" | .i64x2 => "i64x2"

def fshape : FloatShape → String
  | .f32x4 => "f32x4" | .f64x2 => "f64x2"

def shape : Shape → String
  | .int s => ishape s
  | .float s => fshape s

def halfName : Half → String
  | .low => "low"
  | .high => "high"

def vecIntBin : VecIntBinOp → Option String
  | .add => some "add" | .sub => some "sub" | .mul => some "mul"
  | .addSat s => some ("add_sat_" ++ sx s) | .subSat s => some ("sub_sat_" ++ sx s)
  | .avgrU => some "avgr_u" | .min s => some ("min_" ++ sx s) | .max s => some ("max_" ++ sx s)
  | .relaxedQ15mulrS => some "relaxed_q15mulr_s"
  | _ => none

def vecFloatBin : VecFloatBinOp → Option String
  | .add => some "add" | .sub => some "sub" | .mul => some "mul" | .div => some "div"
  | .min => some "min" | .max => some "max" | .pmin => some "pmin" | .pmax => some "pmax"
  | .relaxedMin => some "relaxed_min" | .relaxedMax => some "relaxed_max"

def vecIntUn : VecIntUnOp → String
  | .abs => "abs" | .neg => "neg" | .popcnt => "popcnt"

def vecShift : VecShiftOp → String
  | .shl => "shl" | .shr s => "shr_" ++ sx s

/-- The name of a vector load (after `v128.`) and the log2 of its natural alignment. -/
def vecLoadName : VecLoadOp → Option (String × Nat)
  | .full => some ("load", 4)
  | .extend8x8 sg => some ("load8x8_" ++ sx sg, 3)
  | .extend16x4 sg => some ("load16x4_" ++ sx sg, 3)
  | .extend32x2 sg => some ("load32x2_" ++ sx sg, 3)
  | .splat .i8 => some ("load8_splat", 0)
  | .splat .i16 => some ("load16_splat", 1)
  | .splat .i32 => some ("load32_splat", 2)
  | .splat .i64 => some ("load64_splat", 3)
  | .zero32 => some ("load32_zero", 2)
  | .zero64 => some ("load64_zero", 3)

/-- The name of a vector conversion. -/
def vecConvertName (src tgt : Shape) : VecConvertOp → Option String
  | .extend h sg => some s!"{shape tgt}.extend_{halfName h}_{shape src}_{sx sg}"
  | .convert none sg => some s!"{shape tgt}.convert_{shape src}_{sx sg}"
  | .convert (some h) sg => some s!"{shape tgt}.convert_{halfName h}_{shape src}_{sx sg}"
  | .truncSat sg z => some (s!"{shape tgt}.trunc_sat_{shape src}_{sx sg}" ++ if z then "_zero" else "")
  | .relaxedTrunc sg z =>
      some (s!"{shape tgt}.relaxed_trunc_{shape src}_{sx sg}" ++ if z then "_zero" else "")
  | .demoteZero => some "f32x4.demote_f64x2_zero"
  | .promoteLow => some "f64x2.promote_low_f32x4"

/-- A block type. -/
def blockType : BlockType → Option String
  | .empty => some ""
  | .value t => do return " (result " ++ (← valType t) ++ ")"
  | .typeIdx _ => none

/-- A branch label `l` at block depth `d`: the `(;@n;)` annotation when it names a block. -/
def label (d : Nat) (l : LabelIdx) : String :=
  if l.toNat < d then s!"{l.toNat} (;@{d - l.toNat};)" else toString l.toNat

/-- A plain instruction (no body), at block depth `d`. -/
def plain (d : Nat) : Instr → Option String
  | .nop => some "nop"
  | .unreachable => some "unreachable"
  | .drop => some "drop"
  | .select none => some "select"
  | .select (some [t]) => do return "select (result " ++ (← valType t) ++ ")"
  | .br l => some ("br " ++ label d l)
  | .brIf l => some ("br_if " ++ label d l)
  | .return_ => some "return"
  | .call f => some s!"call {f.toNat}"
  | .callIndirect x t =>
      some ("call_indirect" ++ (if x.toNat = 0 then "" else s!" {x.toNat}") ++ s!" (type {t.toNat})")
  | .returnCall f => some s!"return_call {f.toNat}"
  | .returnCallIndirect x t =>
      some ("return_call_indirect" ++ (if x.toNat = 0 then "" else s!" {x.toNat}") ++
        s!" (type {t.toNat})")
  | .localGet x => some s!"local.get {x.toNat}"
  | .localSet x => some s!"local.set {x.toNat}"
  | .localTee x => some s!"local.tee {x.toNat}"
  | .globalGet x => some s!"global.get {x.toNat}"
  | .globalSet x => some s!"global.set {x.toNat}"
  | .intLoad t none x a => some (s!"{it t}.load" ++ memIx x ++ memArg (intA t) a)
  | .intLoad t (some (p, s)) x a => some (s!"{it t}.load{packW p}_{sx s}" ++ memIx x ++ memArg (packA p) a)
  | .floatLoad t x a => some (s!"{ft t}.load" ++ memIx x ++ memArg (floatA t) a)
  | .intStore t none x a => some (s!"{it t}.store" ++ memIx x ++ memArg (intA t) a)
  | .intStore t (some p) x a => some (s!"{it t}.store{packW p}" ++ memIx x ++ memArg (packA p) a)
  | .floatStore t x a => some (s!"{ft t}.store" ++ memIx x ++ memArg (floatA t) a)
  | .vecLoad .full x a => some ("v128.load" ++ memIx x ++ memArg 4 a)
  | .vecStore x a => some ("v128.store" ++ memIx x ++ memArg 4 a)
  | .memorySize x => some ("memory.size" ++ memIx x)
  | .memoryGrow x => some ("memory.grow" ++ memIx x)
  | .memoryFill x => some ("memory.fill" ++ memIx x)
  | .memoryCopy x y =>
      some (if x.toNat = 0 && y.toNat = 0 then "memory.copy" else s!"memory.copy {x.toNat} {y.toNat}")
  | .vecConst b => some (v128Text b)
  | .vecUnOp .not => some "v128.not"
  | .vecBinOp .and => some "v128.and"
  | .vecBinOp .andnot => some "v128.andnot"
  | .vecBinOp .or => some "v128.or"
  | .vecBinOp .xor => some "v128.xor"
  | .vecTernOp .bitselect => some "v128.bitselect"
  | .vecTestOp .anyTrue => some "v128.any_true"
  | .vecAllTrue s => some (ishape s ++ ".all_true")
  | .vecBitmask s => some (ishape s ++ ".bitmask")
  | .tableGet x => some s!"table.get {x.toNat}"
  | .tableSet x => some s!"table.set {x.toNat}"
  | .tableSize x => some s!"table.size {x.toNat}"
  | .tableGrow x => some s!"table.grow {x.toNat}"
  | .tableFill x => some s!"table.fill {x.toNat}"
  | .tableCopy x y =>
      some (if x.toNat = 0 && y.toNat = 0 then "table.copy" else s!"table.copy {x.toNat} {y.toNat}")
  | .tableInit x e =>
      some (if x.toNat = 0 then s!"table.init {e.toNat}" else s!"table.init {x.toNat} {e.toNat}")
  | .elemDrop e => some s!"elem.drop {e.toNat}"
  | .memoryInit x d =>
      some (if x.toNat = 0 then s!"memory.init {d.toNat}" else s!"memory.init {x.toNat} {d.toNat}")
  | .dataDrop d => some s!"data.drop {d.toNat}"
  | .throw x => some s!"throw {x.toNat}"
  | .refEq => some "ref.eq"
  | .refTest r => do return "ref.test " ++ (← refTypeLong r)
  | .refI31 => some "ref.i31"
  | .i31Get sg => some ("i31.get_" ++ sx sg)
  | .structNew t => some s!"struct.new {t.toNat}"
  | .structNewDefault t => some s!"struct.new_default {t.toNat}"
  | .structGet none t i => some s!"struct.get {t.toNat} {i.toNat}"
  | .structGet (some sg) t i => some s!"struct.get_{sx sg} {t.toNat} {i.toNat}"
  | .structSet t i => some s!"struct.set {t.toNat} {i.toNat}"
  | .arrayNew t => some s!"array.new {t.toNat}"
  | .arrayNewDefault t => some s!"array.new_default {t.toNat}"
  | .arrayGet none t => some s!"array.get {t.toNat}"
  | .arrayGet (some sg) t => some s!"array.get_{sx sg} {t.toNat}"
  | .arraySet t => some s!"array.set {t.toNat}"
  | .arrayLen => some "array.len"
  | .vecLoad op x a => do
      let (n, nat) ← vecLoadName op
      return "v128." ++ n ++ memIx x ++ memArg nat a
  | .vecIntRelOp s op => some (ishape s ++ "." ++ intRel op)
  | .vecFloatRelOp s op => some (fshape s ++ "." ++ floatRel op)
  | .vecShuffle ls => some ("i8x16.shuffle" ++ String.join (ls.map fun l => s!" {l.val}"))
  | .vecNarrow src tgt sg => some s!"{ishape tgt}.narrow_{ishape src}_{sx sg}"
  | .vecReplaceLane sh l => some s!"{shape sh}.replace_lane {l.val}"
  | .vecConvert src tgt op => vecConvertName src tgt op
  | .vecSwizzle .relaxedSwizzle => some "i8x16.relaxed_swizzle"
  | .vecSwizzle .swizzle => some "i8x16.swizzle"
  | .vecIntTernOp s .relaxedLaneSelect => some (ishape s ++ ".relaxed_laneselect")
  | .vecFloatTernOp s .relaxedMadd => some (fshape s ++ ".relaxed_madd")
  | .vecFloatTernOp s .relaxedNmadd => some (fshape s ++ ".relaxed_nmadd")
  | .vecExtBinOp .i8x16 .i16x8 .relaxedDotS => some "i16x8.relaxed_dot_i8x16_i7x16_s"
  | .vecExtTernOp .i8x16 .i32x4 .relaxedDotAddS => some "i32x4.relaxed_dot_i8x16_i7x16_add_s"
  | .vecIntBinOp s op => do return ishape s ++ "." ++ (← vecIntBin op)
  | .vecFloatBinOp s op => do return fshape s ++ "." ++ (← vecFloatBin op)
  | .vecIntUnOp s op => some (ishape s ++ "." ++ vecIntUn op)
  | .vecFloatUnOp s op => some (fshape s ++ "." ++ floatUn op)
  | .vecShiftOp s op => some (ishape s ++ "." ++ vecShift op)
  | .vecSplat s => some (shape s ++ ".splat")
  | .vecExtractLane s sg l =>
      some (shape s ++ ".extract_lane" ++ (match sg with | some g => "_" ++ sx g | none => "") ++
        s!" {l.val}")
  | .refNull h => do return "ref.null " ++ (← heapType h)
  | .refIsNull => some "ref.is_null"
  | .refFunc f => some s!"ref.func {f.toNat}"
  | .intConst .i32 b => some ("i32.const " ++ signed 32 b.toNat)
  | .intConst .i64 b => some ("i64.const " ++ signed 64 b.toNat)
  | .floatConst .f32 b => do return "f32.const " ++ (← floatText 32 23 127 b.toNat)
  | .floatConst .f64 b => do return "f64.const " ++ (← floatText 64 52 1023 b.toNat)
  | .intUnOp t op => some s!"{it t}.{intUn op}"
  | .intBinOp t op => some s!"{it t}.{intBin op}"
  | .intTestOp t _ => some s!"{it t}.eqz"
  | .intRelOp t op => some s!"{it t}.{intRel op}"
  | .floatUnOp t op => some s!"{ft t}.{floatUn op}"
  | .floatBinOp t op => some s!"{ft t}.{floatBin op}"
  | .floatRelOp t op => some s!"{ft t}.{floatRel op}"
  | .convert op => some (convert op)
  | _ => none

/-- Indentation for block depth `d` inside a function. -/
def ind (d : Nat) : String := String.ofList (List.replicate (4 + 2 * d) ' ')

mutual

/-- The lines of an instruction at block depth `d`. -/
def instrLines (d : Nat) : Instr → Option (List String)
  | .block bt body => do
    let b ← blockType bt
    return [ind d ++ "block" ++ b ++ s!" ;; label = @{d + 1}"] ++ (← bodyLines (d + 1) body) ++
      [ind d ++ "end"]
  | .loop bt body => do
    let b ← blockType bt
    return [ind d ++ "loop" ++ b ++ s!" ;; label = @{d + 1}"] ++ (← bodyLines (d + 1) body) ++
      [ind d ++ "end"]
  | .if_ bt thn els => do
    let b ← blockType bt
    let t ← bodyLines (d + 1) thn
    let e ← bodyLines (d + 1) els
    return [ind d ++ "if" ++ b ++ s!" ;; label = @{d + 1}"] ++ t ++
      (if els.isEmpty then [] else [ind d ++ "else"] ++ e) ++ [ind d ++ "end"]
  | .tryTable bt cs body => do
    let b ← blockType bt
    let ct := String.join (cs.map fun
      | .catch_ x l => s!" (catch {x.toNat} {label d l})"
      | .catchRef x l => s!" (catch_ref {x.toNat} {label d l})"
      | .catchAll l => s!" (catch_all {label d l})"
      | .catchAllRef l => s!" (catch_all_ref {label d l})")
    return [ind d ++ "try_table" ++ b ++ ct ++ s!" ;; label = @{d + 1}"] ++
      (← bodyLines (d + 1) body) ++ [ind d ++ "end"]
  | i => do return [ind d ++ (← plain d i)]

/-- The lines of a sequence. -/
def bodyLines (d : Nat) : List Instr → Option (List String)
  | [] => some []
  | i :: is => do return (← instrLines d i) ++ (← bodyLines d is)

end

/-- A constant expression on one line. -/
def constExpr (e : Expr) : Option String := do
  let ps ← e.mapM (plain 0)
  return " ".intercalate ps

/-! ## Modules -/

/-- The function type of a single-member, final, supertype-free recursion group. -/
def plainFunc? (r : RecType) : Option FuncType :=
  match r.types with
  | [⟨true, [], .func f⟩] => some f
  | _ => none

/-- The body of a single-member, final, supertype-free recursion group. -/
def plainBody? (r : RecType) : Option CompositeType :=
  match r.types with
  | [⟨true, [], b⟩] => some b
  | _ => none

/-- A field type: `i32`, `i8`, `(mut i64)`. -/
def fieldText (f : FieldType) : Option String := do
  let st ← match f.storage with
    | .val t => valType t
    | .packed .i8 => some "i8"
    | .packed .i16 => some "i16"
  return if f.mutability == .var then s!"(mut {st})" else st

/-- A composite type: `(func …)`, `(struct (field …) …)`, `(array …)`. -/
def compText : CompositeType → Option String
  | .func f => do return s!"(func{← sig f})"
  | .struct fs => do
    let ts ← fs.mapM fieldText
    return "(struct" ++ String.join (ts.map (" (field " ++ · ++ ")")) ++ ")"
  | .array f => do return s!"(array {← fieldText f})"

/-- Lines tagged with the rank of their section (`Sections.rank`). -/
def tag (r : Nat) (ls : List String) : List (Nat × String) := ls.map ((r, ·))

/-- **The lines of a module** in wasmprinter's layout, each with the rank of the section it
comes from, `none` outside the supported fragment. -/
def printLines? (m : Module) : Option (List (Nat × String)) := do
  let bodies ← m.types.mapM plainBody?
  let types := bodies.map fun | .func f => f | _ => ⟨[], []⟩
  let tyOf (x : TypeIdx) : FuncType := types.getD x.toNat ⟨[], []⟩
  let mut lines : List (Nat × String) := []
  for (b, i) in bodies.zipIdx do
    lines := lines ++ tag 1 [s!"  (type (;{i};) {← compText b})"]
  let mut nf := 0
  let mut ng := 0
  for im in m.imports do
    let mn ← nameString im.moduleName
    let nm ← nameString im.name
    match im.type with
    | .func x =>
      if x.toNat ≥ types.length then none
      lines := lines ++ tag 2 [s!"  (import {mn} {nm} (func (;{nf};) (type {x.toNat}){← sig (tyOf x)}))"]
      nf := nf + 1
    | .global g =>
      let vt ← valType g.value
      let gt := if g.mutability == .var then s!"(mut {vt})" else vt
      lines := lines ++ tag 2 [s!"  (import {mn} {nm} (global (;{ng};) {gt}))"]
      ng := ng + 1
    | _ => none
  for (t, i) in m.tables.zipIdx do
    if t.type.address != .i32 then none
    let et ← valType (.ref t.type.element)
    match t.init with
    | [.refNull h] => if h != t.type.element.heap then none
    | _ => none
    let mx := match t.type.limits.max with | some x => s!" {x.val}" | none => ""
    lines := lines ++ tag 4 [s!"  (table (;{i};) {t.type.limits.min.val}{mx} {et})"]
  for (mt, i) in m.memories.zipIdx do
    let aty := if mt.address == .i64 then "i64 " else ""
    let mx := match mt.limits.max with | some x => s!" {x.val}" | none => ""
    lines := lines ++ tag 5 [s!"  (memory (;{i};) {aty}{mt.limits.min.val}{mx})"]
  for (x, i) in m.tags.zipIdx do
    if x.toNat ≥ types.length then none
    lines := lines ++ tag 6 [s!"  (tag (;{i};) (type {x.toNat}){← sig (tyOf x)})"]
  for g in m.globals do
    let vt ← valType g.type.value
    let gt := if g.type.mutability == .var then s!"(mut {vt})" else vt
    lines := lines ++ tag 7 [s!"  (global (;{ng};) {gt} {← constExpr g.init})"]
    ng := ng + 1
  for e in m.exports do
    let nm ← nameString e.name
    let x := match e.index with
      | .func i => s!"(func {i.toNat})"
      | .global i => s!"(global {i.toNat})"
      | .memory i => s!"(memory {i.toNat})"
      | .table i => s!"(table {i.toNat})"
      | .tag i => s!"(tag {i.toNat})"
    lines := lines ++ tag 8 [s!"  (export {nm} {x})"]
  if let some s := m.start then
    lines := lines ++ tag 9 [s!"  (start {s.toNat})"]
  for (e, i) in m.elems.zipIdx do
    let modeTxt : Option String := match e.mode with
      | .active x o => (constExpr o).map fun c =>
        (if x.toNat = 0 then "" else s!"(table {x.toNat}) ") ++ s!"({c}) "
      | .passive => some ""
      | .declarative => some "declare "
    let pre ← modeTxt
    let ys ← e.init.mapM fun
      | [.refFunc y] => some y.toNat
      | _ => none
    if e.type == ⟨false, .abstract .func⟩ then
      lines := lines ++ tag 10 [s!"  (elem (;{i};) {pre}func" ++
        String.join (ys.map fun y => s!" {y}") ++ ")"]
    else if e.type == ⟨true, .abstract .func⟩ then
      lines := lines ++ tag 10 [s!"  (elem (;{i};) {pre}funcref" ++
        String.join (ys.map fun y => s!" (ref.func {y})") ++ ")"]
    else none
  for f in m.funcs do
    if f.type.toNat ≥ types.length then none
    let head := s!"  (func (;{nf};) (type {f.type.toNat}){← sig (tyOf f.type)}"
    let ls ← f.locals.mapM valType
    let body ← bodyLines 0 f.body
    let localLine := if ls.isEmpty then [] else ["    (local " ++ " ".intercalate ls ++ ")"]
    if localLine.isEmpty && body.isEmpty then
      lines := lines ++ tag 12 [head ++ ")"]
    else
      lines := lines ++ tag 12 ([head] ++ localLine ++ body ++ ["  )"])
    nf := nf + 1
  for (d, i) in m.data.zipIdx do
    let bs := dataString d.bytes.data.toList
    match d.mode with
    | .active x o =>
      let mem := if x.toNat = 0 then "" else s!"(memory {x.toNat}) "
      lines := lines ++ tag 13 [s!"  (data (;{i};) {mem}({← constExpr o}) {bs})"]
    | .passive => lines := lines ++ tag 13 [s!"  (data (;{i};) {bs})"]
  return lines

/-- The module text around its field lines. -/
def assemble (lines : List String) : String :=
  if lines.isEmpty then "(module)\n" else "(module\n" ++ String.join (lines.map (· ++ "\n")) ++ ")\n"

/-- **The text of a module** in wasmprinter's layout, `none` outside the supported fragment. -/
def printModule? (m : Module) : Option String := do
  return assemble ((← printLines? m).map (·.2))

/-! ## Custom sections -/

/-- wasmprinter's name of the section of a rank (for `(after …)`); the data count section has
no name in the text format. -/
def rankName : Nat → Option String
  | 1 => some "type" | 2 => some "import" | 3 => some "func" | 4 => some "table"
  | 5 => some "memory" | 6 => some "tag" | 7 => some "global" | 8 => some "export"
  | 9 => some "start" | 10 => some "elem" | 12 => some "code" | 13 => some "data"
  | _ => none

/-- Custom sections wasmprinter prints in another form (names, producers, linking, …): not
supported here. -/
def specialCustom (n : String) : Bool :=
  n ∈ ["name", "producers", "target_features", "dylink.0", "dylink", "linking",
    "component-type", "metadata.code.branch_hint", "build_id", "sourceMappingURL"] ||
  n.startsWith "reloc." || n.startsWith "component-type" || n.startsWith "metadata.code." ||
  n.startsWith ".debug"

/-- Read an unsigned LEB128 (at most 5 bytes). -/
def readLeb : Nat → List UInt8 → Nat → Nat → Option (Nat × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, b :: bs, acc, sh =>
    let acc := acc + b.toNat % 128 * 2 ^ sh
    if b.toNat < 128 then some (acc, bs) else readLeb fuel bs acc (sh + 7)

/-- The `(@custom …)` line of a custom section payload anchored at rank `a`. -/
def customLine (a : Nat) (payload : List UInt8) : Option String := do
  let (n, rest) ← readLeb 5 payload 0 0
  if rest.length < n then none
  let name ← String.fromUTF8? ⟨(rest.take n).toArray⟩
  if specialCustom name then none
  let nm ← nameString name
  let place ← if a = 0 then some "(before first)" else (rankName a).map (s!"(after {·})")
  return s!"  (@custom {nm} {place} {dataString (rest.drop n)})"

/-- Insert anchored lines: each before the first line whose rank is above its anchor. -/
def insertAnchored : List (Nat × String) → List (Nat × String) → List String
  | cs, [] => cs.map (·.2)
  | cs, (r, l) :: ls =>
    let p := cs.span (·.1 < r)
    p.1.map (·.2) ++ l :: insertAnchored p.2 ls

/-- **The text of a module with custom sections** (each a payload anchored at the rank of
the section before it in the binary, `Sections.anchors`), `none` outside the fragment. -/
def printModuleC? (m : Module) (customs : List (Nat × List UInt8)) : Option String := do
  let lines ← printLines? m
  let cs ← customs.mapM fun (a, p) => do return (a, ← customLine a p)
  return assemble (insertAnchored cs lines)

end Silmaril.Wasm.Tools.Gen.Cmd.Print
