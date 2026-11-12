module

public import Silmaril.ML.OCaml.Compare.Defs

/-!
# Primitive operations

`primExec op args st` is the result of a saturated primitive application:
`some (outcome, store)`, or `none` when OCaml leaves the behaviour
unspecified or the model does not cover it (the evaluation is then stuck).
This table is a **trusted definition**: it is checked against OCaml only by
differential tests (`docs/projects/wasm-wasi.md`).

Unspecified behaviour that is stuck here: shift counts outside
`0 … width-1`; `==` on immutable boxed values; unsafe string/bytes accesses
out of bounds; floats; format conversions other than `d i u x X o` with
flags `- 0 + space` and a width.

Deviations, documented in `docs/projects/wasm-wasi.md`: `caml_create_bytes` fills with
zero bytes (OCaml leaves the contents unspecified), `%bytes_to_string` and
`%bytes_of_string` copy (OCaml shares, which is only observable by writing
to the bytes afterwards, which the manual forbids), and channel output is
unbuffered.
-/

@[expose] public section
namespace Silmaril.ML.OCaml

def primOk (v : Value) (st : Store) : Option (Outcome × Store) := some (.ret v, st)

def divByZero : Outcome := raiseNamed "Division_by_zero" []

/-! ## Integer formatting (`caml_format_int` and friends) -/

/-- A parsed `%[flags][width][l|L|n]conv` conversion. -/
structure FmtSpec where
  minus : Bool := false
  zero : Bool := false
  plus : Bool := false
  space : Bool := false
  width : Nat := 0
  conv : Char

def parseFlags : List Char → FmtSpec → List Char × FmtSpec
  | '-' :: cs, f => parseFlags cs { f with minus := true }
  | '0' :: cs, f => parseFlags cs { f with zero := true }
  | '+' :: cs, f => parseFlags cs { f with plus := true }
  | ' ' :: cs, f => parseFlags cs { f with space := true }
  | cs, f => (cs, f)

def parseWidth : List Char → Nat → List Char × Nat
  | c :: cs, w => if c.isDigit then parseWidth cs (10 * w + (c.toNat - '0'.toNat)) else (c :: cs, w)
  | [], w => ([], w)

def parseFmt (s : List Char) : Option FmtSpec :=
  match s with
  | '%' :: cs =>
    let (cs, f) := parseFlags cs { conv := 'd' }
    let (cs, w) := parseWidth cs 0
    let cs := match cs with
      | 'l' :: r | 'L' :: r | 'n' :: r => r
      | r => r
    match cs with
    | [c] => if c ∈ ['d', 'i', 'u', 'x', 'X', 'o'] then some { f with width := w, conv := c } else none
    | _ => none
  | _ => none

def digitChar (d : Nat) (upper : Bool) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d)
  else Char.ofNat ((if upper then 'A' else 'a').toNat + d - 10)

def natDigitsAux (base : Nat) (upper : Bool) : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc := digitChar (n % base) upper :: acc
    if n / base = 0 then acc else natDigitsAux base upper fuel (n / base) acc

/-- Digits of `n` in `base` (most significant first). -/
def natDigits (base : Nat) (upper : Bool) (n : Nat) : List Char :=
  natDigitsAux base upper (n + 1) n []

/-- Format an integer of `width` bits (signed value `s`, unsigned value `u`). -/
def formatIntSpec (f : FmtSpec) (s : Int) (u : Nat) : List Char :=
  let (sign, digits) : List Char × List Char :=
    match f.conv with
    | 'd' | 'i' =>
      let sg := if s < 0 then ['-'] else if f.plus then ['+'] else if f.space then [' '] else []
      (sg, natDigits 10 false s.natAbs)
    | 'u' => ([], natDigits 10 false u)
    | 'x' => ([], natDigits 16 false u)
    | 'X' => ([], natDigits 16 true u)
    | _ => ([], natDigits 8 false u)
  let len := sign.length + digits.length
  let pad := f.width - len
  if f.minus then sign ++ digits ++ List.replicate pad ' '
  else if f.zero then sign ++ List.replicate pad '0' ++ digits
  else List.replicate pad ' ' ++ sign ++ digits

def formatPrim (fmt : List UInt8) (s : Int) (u : Nat) : Option Value := do
  let f ← parseFmt (fmt.map fun b => Char.ofNat b.toNat)
  pure (.str ((formatIntSpec f s u).map fun c => c.toNat.toUInt8))

/-! ## Helpers -/

def intOf? : Value → Option (BitVec 63)
  | .int n => some n
  | _ => none

def boolArg? (v : Value) : Option Bool := v.toBool?

/-- Bytes of a string value or of a bytes cell. -/
def bytesOf? (st : Store) : Value → Option (List UInt8)
  | .str bs => some bs
  | .loc l => match st.get? l with
    | some (.bytes bs) => some bs
    | _ => none
  | _ => none

def byteValue (b : UInt8) : Value := .int (BitVec.ofNat 63 b.toNat)

def toByte? (v : Value) : Option UInt8 := (intOf? v).map fun n => n.toNat.toUInt8

/-- A non-negative index below `len`. -/
def index? (v : Value) (len : Nat) : Option Nat :=
  match v with
  | .int n => if 0 ≤ n.toInt ∧ n.toInt < len then some n.toNat else none
  | _ => none

def shiftCount? (v : Value) (w : Nat) : Option Nat :=
  match v with
  | .int c => if 0 ≤ c.toInt ∧ c.toInt < w then some c.toNat else none
  | _ => none

def blit (src : List UInt8) (so : Nat) (dst : List UInt8) (d : Nat) (len : Nat) : List UInt8 :=
  dst.take d ++ (src.drop so).take len ++ dst.drop (d + len)

/-- Comparison primitives on `compareValues`. -/
def comparePrim (st : Store) (msg : String) (a b : Value) (k : Ordering → Value) :
    Option (Outcome × Store) :=
  match compareValues st a b with
  | some (.ord o) => some (.ret (k o), st)
  | some .functional => some (invalidArg (msg ++ ": functional value"), st)
  | none => none

def ordToInt : Ordering → Value
  | .lt => .ofInt (-1)
  | .eq => .ofInt 0
  | .gt => .ofInt 1

def setCellField (st : Store) (l : Loc) (i : Nat) (v : Value) : Option Store :=
  match st.get? l with
  | some (.fields vs) => if i < vs.length then some (st.set l (.fields (vs.set i v))) else none
  | _ => none

def getField? (st : Store) (v : Value) (i : Nat) : Option Value :=
  match v with
  | .block _ fs => fs[i]?
  | .mod fs => fs[i]?
  | .exn _ _ args => if i = 0 then none else args[i - 1]?
  | .loc l => match st.get? l with
    | some (.fields vs) => vs[i]?
    | _ => none
  | _ => none

/-! ## The primitive table -/

def int32Bin (f : BitVec 32 → BitVec 32 → BitVec 32) (a b : Value) (st : Store) :
    Option (Outcome × Store) :=
  match a, b with
  | .int32 x, .int32 y => primOk (.int32 (f x y)) st
  | _, _ => none

def int64Bin (f : BitVec 64 → BitVec 64 → BitVec 64) (a b : Value) (st : Store) :
    Option (Outcome × Store) :=
  match a, b with
  | .int64 x, .int64 y => primOk (.int64 (f x y)) st
  | _, _ => none

def intBin (f : BitVec 63 → BitVec 63 → BitVec 63) (a b : Value) (st : Store) :
    Option (Outcome × Store) :=
  match a, b with
  | .int x, .int y => primOk (.int (f x y)) st
  | _, _ => none

/-- The integer a Zarith value denotes: a native `int` (small) or `Value.z` (large). -/
def zOf? : Value → Option Int
  | .int x => some x.toInt
  | .z n => some n
  | _ => none

/-- Zarith's representation of an integer: a native `int` when it fits in 63 bits. -/
def zVal (n : Int) : Value := if -2 ^ 62 ≤ n ∧ n < 2 ^ 62 then .ofInt n else .z n

def zBin (f : Int → Int → Int) (a b : Value) (st : Store) : Option (Outcome × Store) := do
  let x ← zOf? a; let y ← zOf? b; primOk (zVal (f x y)) st

def zRel (f : Int → Int → Value) (a b : Value) (st : Store) : Option (Outcome × Store) := do
  let x ← zOf? a; let y ← zOf? b; primOk (f x y) st

def primExec (op : PrimOp) (args : List Value) (st : Store) : Option (Outcome × Store) :=
  match op, args with
  -- native int (63-bit, wrapping)
  | .negint, [.int x] => primOk (.int (-x)) st
  | .succint, [.int x] => primOk (.int (x + 1)) st
  | .predint, [.int x] => primOk (.int (x - 1)) st
  | .addint, [a, b] => intBin (· + ·) a b st
  | .subint, [a, b] => intBin (· - ·) a b st
  | .mulint, [a, b] => intBin (· * ·) a b st
  | .divint, [.int x, .int y] => if y = 0 then some (divByZero, st) else primOk (.int (x.sdiv y)) st
  | .modint, [.int x, .int y] => if y = 0 then some (divByZero, st) else primOk (.int (x.srem y)) st
  | .andint, [a, b] => intBin (· &&& ·) a b st
  | .orint, [a, b] => intBin (· ||| ·) a b st
  | .xorint, [a, b] => intBin (· ^^^ ·) a b st
  -- `n lsl m` is unspecified if `m < 0` or `m > Sys.int_size` (`stdlib.mli`), so a count
  -- of 63 is defined (`-1 lsl 63 = 0`, used by `decode.ml`'s `sN 64`)
  | .lslint, [.int x, c] => (shiftCount? c 64).map fun k => (.ret (.int (x <<< k)), st)
  | .lsrint, [.int x, c] => (shiftCount? c 64).map fun k => (.ret (.int (x >>> k)), st)
  | .asrint, [.int x, c] => (shiftCount? c 64).map fun k => (.ret (.int (x.sshiftRight k)), st)
  -- comparison
  | .compare, [a, b] => comparePrim st "compare" a b ordToInt
  | .equal, [a, b] => comparePrim st "compare" a b fun o => .ofBool (o == .eq)
  | .notequal, [a, b] => comparePrim st "compare" a b fun o => .ofBool (o != .eq)
  | .lessthan, [a, b] => comparePrim st "compare" a b fun o => .ofBool (o == .lt)
  | .lessequal, [a, b] => comparePrim st "compare" a b fun o => .ofBool (o != .gt)
  | .greaterthan, [a, b] => comparePrim st "compare" a b fun o => .ofBool (o == .gt)
  | .greaterequal, [a, b] => comparePrim st "compare" a b fun o => .ofBool (o != .lt)
  | .eq, [a, b] => (physEq a b).map fun r => (.ret (.ofBool r), st)
  | .noteq, [a, b] => (physEq a b).map fun r => (.ret (.ofBool !r), st)
  -- booleans and control
  | .boolnot, [v] => (v.toBool?).map fun b => (.ret (.ofBool !b), st)
  | .sequand, [a, b] => do let x ← a.toBool?; let y ← b.toBool?; primOk (.ofBool (x && y)) st
  | .sequor, [a, b] => do let x ← a.toBool?; let y ← b.toBool?; primOk (.ofBool (x || y)) st
  | .identity, [v] => primOk v st
  | .ignore, [_] => primOk .unit st
  | .raise, [v] | .reraise, [v] | .raiseNotrace, [v] => some (.exn v, st)
  -- references and fields
  | .makemutable, [v] => let (l, st') := st.alloc (.fields [v]); primOk (.loc l) st'
  | .field0, [v] => (getField? st v 0).map fun w => (.ret w, st)
  | .field1, [v] => (getField? st v 1).map fun w => (.ret w, st)
  | .setfield0, [.loc l, v] => (setCellField st l 0 v).map fun st' => (.ret .unit, st')
  | .incr, [.loc l] => match st.get? l with
    | some (.fields [.int n]) => primOk .unit (st.set l (.fields [.int (n + 1)]))
    | _ => none
  | .decr, [.loc l] => match st.get? l with
    | some (.fields [.int n]) => primOk .unit (st.set l (.fields [.int (n - 1)]))
    | _ => none
  -- Int32
  | .int32Neg, [.int32 x] => primOk (.int32 (-x)) st
  | .int32Add, [a, b] => int32Bin (· + ·) a b st
  | .int32Sub, [a, b] => int32Bin (· - ·) a b st
  | .int32Mul, [a, b] => int32Bin (· * ·) a b st
  | .int32Div, [.int32 x, .int32 y] =>
    if y = 0 then some (divByZero, st) else primOk (.int32 (x.sdiv y)) st
  | .int32Mod, [.int32 x, .int32 y] =>
    if y = 0 then some (divByZero, st) else primOk (.int32 (x.srem y)) st
  | .int32And, [a, b] => int32Bin (· &&& ·) a b st
  | .int32Or, [a, b] => int32Bin (· ||| ·) a b st
  | .int32Xor, [a, b] => int32Bin (· ^^^ ·) a b st
  | .int32Lsl, [.int32 x, c] => (shiftCount? c 32).map fun k => (.ret (.int32 (x <<< k)), st)
  | .int32Lsr, [.int32 x, c] => (shiftCount? c 32).map fun k => (.ret (.int32 (x >>> k)), st)
  | .int32Asr, [.int32 x, c] =>
    (shiftCount? c 32).map fun k => (.ret (.int32 (x.sshiftRight k)), st)
  | .int32OfInt, [.int x] => primOk (.int32 (x.setWidth 32)) st
  | .int32ToInt, [.int32 x] => primOk (.int (x.signExtend 63)) st
  -- Int64
  | .int64Neg, [.int64 x] => primOk (.int64 (-x)) st
  | .int64Add, [a, b] => int64Bin (· + ·) a b st
  | .int64Sub, [a, b] => int64Bin (· - ·) a b st
  | .int64Mul, [a, b] => int64Bin (· * ·) a b st
  | .int64Div, [.int64 x, .int64 y] =>
    if y = 0 then some (divByZero, st) else primOk (.int64 (x.sdiv y)) st
  | .int64Mod, [.int64 x, .int64 y] =>
    if y = 0 then some (divByZero, st) else primOk (.int64 (x.srem y)) st
  | .int64And, [a, b] => int64Bin (· &&& ·) a b st
  | .int64Or, [a, b] => int64Bin (· ||| ·) a b st
  | .int64Xor, [a, b] => int64Bin (· ^^^ ·) a b st
  | .int64Lsl, [.int64 x, c] => (shiftCount? c 64).map fun k => (.ret (.int64 (x <<< k)), st)
  | .int64Lsr, [.int64 x, c] => (shiftCount? c 64).map fun k => (.ret (.int64 (x >>> k)), st)
  | .int64Asr, [.int64 x, c] =>
    (shiftCount? c 64).map fun k => (.ret (.int64 (x.sshiftRight k)), st)
  | .int64OfInt, [.int x] => primOk (.int64 (x.signExtend 64)) st
  | .int64ToInt, [.int64 x] => primOk (.int (x.setWidth 63)) st
  | .int64OfInt32, [.int32 x] => primOk (.int64 (x.signExtend 64)) st
  | .int64ToInt32, [.int64 x] => primOk (.int32 (x.setWidth 32)) st
  | .formatInt, [.str f, .int x] => (formatPrim f x.toInt x.toNat).map fun v => (.ret v, st)
  | .int32Format, [.str f, .int32 x] => (formatPrim f x.toInt x.toNat).map fun v => (.ret v, st)
  | .int64Format, [.str f, .int64 x] => (formatPrim f x.toInt x.toNat).map fun v => (.ret v, st)
  -- strings
  | .stringLength, [.str s] => primOk (.ofInt s.length) st
  | .stringSafeGet, [.str s, i] => match index? i s.length with
    | some k => primOk (byteValue (s.getD k 0)) st
    | none => some (invalidArg "index out of bounds", st)
  | .stringUnsafeGet, [.str s, i] => (index? i s.length).map fun k => (.ret (byteValue (s.getD k 0)), st)
  | .stringEqual, [.str s, .str t] => primOk (.ofBool (s == t)) st
  | .stringNotequal, [.str s, .str t] => primOk (.ofBool (s != t)) st
  | .stringCompare, [.str s, .str t] => primOk (ordToInt (compareBytes s t)) st
  -- bytes
  | .bytesLength, [v] => (bytesOf? st v).map fun bs => (.ret (.ofInt bs.length), st)
  | .bytesSafeGet, [v, i] => do
    let bs ← bytesOf? st v
    match index? i bs.length with
    | some k => primOk (byteValue (bs.getD k 0)) st
    | none => some (invalidArg "index out of bounds", st)
  | .bytesUnsafeGet, [v, i] => do
    let bs ← bytesOf? st v
    let k ← index? i bs.length
    primOk (byteValue (bs.getD k 0)) st
  | .bytesSafeSet, [.loc l, i, c] => do
    let bs ← bytesOf? st (.loc l)
    let b ← toByte? c
    match index? i bs.length with
    | some k => primOk .unit (st.set l (.bytes (bs.set k b)))
    | none => some (invalidArg "index out of bounds", st)
  | .bytesUnsafeSet, [.loc l, i, c] => do
    let bs ← bytesOf? st (.loc l)
    let b ← toByte? c
    let k ← index? i bs.length
    primOk .unit (st.set l (.bytes (bs.set k b)))
  | .createBytes, [.int n] =>
    if n.toInt < 0 then some (invalidArg "Bytes.create", st)
    else let (l, st') := st.alloc (.bytes (List.replicate n.toNat 0)); primOk (.loc l) st'
  | .blitString, [src, .int so, .loc l, .int d, .int len]
  | .blitBytes, [src, .int so, .loc l, .int d, .int len] => do
    let s ← bytesOf? st src
    let t ← bytesOf? st (.loc l)
    if 0 ≤ so.toInt ∧ 0 ≤ d.toInt ∧ 0 ≤ len.toInt ∧ so.toNat + len.toNat ≤ s.length ∧
        d.toNat + len.toNat ≤ t.length then
      primOk .unit (st.set l (.bytes (blit s so.toNat t d.toNat len.toNat)))
    else none
  | .fillBytes, [.loc l, .int o, .int len, c] => do
    let t ← bytesOf? st (.loc l)
    let b ← toByte? c
    if 0 ≤ o.toInt ∧ 0 ≤ len.toInt ∧ o.toNat + len.toNat ≤ t.length then
      primOk .unit (st.set l (.bytes (blit (List.replicate len.toNat b) 0 t o.toNat len.toNat)))
    else none
  | .bytesToString, [v] => (bytesOf? st v).map fun bs => (.ret (.str bs), st)
  | .bytesOfString, [.str s] => let (l, st') := st.alloc (.bytes s); primOk (.loc l) st'
  -- channels
  | .openDescriptorOut, [.int fd] | .openDescriptorIn, [.int fd] =>
    let (l, st') := st.alloc (.chan fd.toNat); primOk (.loc l) st'
  | .mlOutput, [.loc c, s, .int o, .int len] | .mlOutputBytes, [.loc c, s, .int o, .int len] =>
    match st.get? c, bytesOf? st s with
    | some (.chan fd), some bs =>
      if 0 ≤ o.toInt ∧ 0 ≤ len.toInt ∧ o.toNat + len.toNat ≤ bs.length then
        primOk .unit (st.output fd ((bs.drop o.toNat).take len.toNat))
      else none
    | _, _ => none
  | .mlOutputChar, [.loc c, b] => match st.get? c, toByte? b with
    | some (.chan fd), some x => primOk .unit (st.output fd [x])
    | _, _ => none
  | .mlFlush, [_] => primOk .unit st
  | .outChannelsList, [_] => primOk .nil st
  | .registerNamedValue, [_, _] => primOk .unit st
  -- atomics
  | .atomicLoad, [.loc l] => (getField? st (.loc l) 0).map fun v => (.ret v, st)
  | .atomicSet, [.loc l, v] => (setCellField st l 0 v).map fun st' => (.ret .unit, st')
  | .atomicExchange, [.loc l, v] => do
    let old ← getField? st (.loc l) 0
    let st' ← setCellField st l 0 v
    primOk old st'
  | .atomicCas, [.loc l, seen, v] => do
    let cur ← getField? st (.loc l) 0
    let same ← physEq cur seen
    if same then do let st' ← setCellField st l 0 v; primOk (.ofBool true) st'
    else primOk (.ofBool false) st
  | .atomicFetchAdd, [.loc l, .int d] => match getField? st (.loc l) 0 with
    | some (.int n) => (setCellField st l 0 (.int (n + d))).map fun st' => (.ret (.int n), st')
    | _ => none
  -- Zarith on `Int`, in Zarith's representation: an integer that fits in 63 bits is a
  -- native `int` (so `Z.of_int` is `%identity`), others are `Value.z` (see `zVal`).
  -- `Z.div`/`Z.rem` truncate toward zero, as in Zarith.
  | .zOfInt, [.int x] => primOk (.int x) st
  | .zFitsInt, [a] => (zOf? a).map fun n => (.ret (.ofBool (-2 ^ 62 ≤ n ∧ n < 2 ^ 62)), st)
  | .zToIntUnsafe, [a] => do
    let n ← zOf? a
    if -2 ^ 62 ≤ n ∧ n < 2 ^ 62 then primOk (.ofInt n) st else none
  | .zAdd, [a, b] => zBin (· + ·) a b st
  | .zSub, [a, b] => zBin (· - ·) a b st
  | .zMul, [a, b] => zBin (· * ·) a b st
  | .zDiv, [a, b] => do
    let x ← zOf? a; let y ← zOf? b
    if y = 0 then some (divByZero, st) else primOk (zVal (x.tdiv y)) st
  | .zRem, [a, b] => do
    let x ← zOf? a; let y ← zOf? b
    if y = 0 then some (divByZero, st) else primOk (zVal (x.tmod y)) st
  | .zNeg, [a] => (zOf? a).map fun n => (.ret (zVal (-n)), st)
  | .zAbs, [a] => (zOf? a).map fun n => (.ret (zVal n.natAbs), st)
  | .zSign, [a] => (zOf? a).map fun n => (.ret (.ofInt n.sign), st)
  -- `Z.pow x k` (`ml_z_pow`): `Invalid_argument` for a negative exponent, as Zarith
  | .zPow, [a, .int k] => (zOf? a).map fun n =>
    if k.toInt < 0 then (invalidArg "Z.pow: exponent must be nonnegative", st)
    else (.ret (zVal (n ^ k.toNat)), st)
  | .zCompare, [a, b] => zRel (fun x y => ordToInt (Ord.compare x y)) a b st
  | .zEqual, [a, b] => zRel (fun x y => .ofBool (x = y)) a b st
  | .zLt, [a, b] => zRel (fun x y => .ofBool (x < y)) a b st
  | .zLeq, [a, b] => zRel (fun x y => .ofBool (x ≤ y)) a b st
  | .zGt, [a, b] => zRel (fun x y => .ofBool (y < x)) a b st
  | .zGeq, [a, b] => zRel (fun x y => .ofBool (y ≤ x)) a b st
  | .zToString, [a] => (zOf? a).map fun n =>
    (.ret (.str (((if n < 0 then ['-'] else []) ++ natDigits 10 false n.natAbs).map
      fun c => c.toNat.toUInt8)), st)
  -- `Sys` constants, as `Translprim` substitutes them for x86-64 (`ocamlopt`)
  | .wordSize, [_] => primOk (.ofInt 64) st
  | .intSize, [_] => primOk (.ofInt 63) st
  | .maxWosize, [_] => primOk (.ofInt (2 ^ 54 - 1)) st
  | .bigEndian, [_] => primOk (.ofBool false) st
  | .ioBufferSize, [_] => primOk (.ofInt 65536) st
  | .raiseWithBacktrace, [v, _] => some (.exn v, st)
  | _, _ => none

end Silmaril.ML.OCaml
