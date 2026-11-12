-- Adapted from the pinned canonical C lowering; the imported snapshot stays unchanged.
-- Source: Silmaril/Compile/C/ToMir.lean (8ec7773f7338646762a5b5a9326bfe53d54b7c8ea10a977bb959ab3d80a9baf3).
module
public import Silmaril.Compiler.Native.IR.Defs
public import Silmaril.Compiler.Native.Analysis.Defs
public import Silmaril.Compiler.Native.Layout.Defs
public import Silmaril.Compiler.Native.Types.Registered.Defs
public import Silmaril.Compiler.Native.Varargs.Defs
public import Silmaril.Compiler.Native.X87.Literals.Defs
/-! Native-address C lowering. Calls retain typed ABI metadata; the backend owns
machine-stack frames, stack arguments and relocatable symbol addresses. This is
an intentional refinement of the frozen import, not an importer-owned copy.
Native va_list uses the actual LP64 record and saved argument-register areas.
-/
@[expose] public section

namespace Silmaril.Compiler.Native.Lower

open Silmaril.Compile
open Silmaril.Compile.C
open Silmaril.Cerberus
open Silmaril.Cerberus.Ail
open Silmaril.Machine
open Silmaril.Compile.Mir (Reg Symbol Instr)
open Silmaril.Cerberus.Mem.Concrete (Tags)

/-- The runtime control block (word 0: software stack pointer). -/
def ctlSymbol : Symbol := "__ccomp_ctl"

/-- The intrinsic for `trap`. -/
def trapSymbol : Symbol := "__ccomp_trap"

/-- Register budget shared by direct and indirect C calls. Mir's dispatcher needs
one additional register for its function pointer, so both forms use the same ABI. -/
def callRegBudget : Nat := Mir.maxArgs - 1

/-- Logical arguments retained in registers when a call needs an overflow area.
The last register carries the address of the remaining canonical 8-byte values. -/
def callRegPrefix : Nat := callRegBudget - 1

/-- The source name of a symbol. -/
def symName (s : Sym) : String :=
  match s.description with
  | .id n | .objectAddress n | .funArgValue n | .cnId n => n
  | _ => "anon"

abbrev FuncInfo := Silmaril.Compile.C.FuncInfo

/-- How floating point is lowered. -/
inductive FloatMode where
  /-- Lir's floating-point instructions (`Mir.Instr.fop`). -/
  | native
  /-- Calls of the soft-float routines of the runtime library. -/
  | soft
  deriving DecidableEq, Repr

/-- Lowering options, fixed for a whole build. -/
structure LowerOptions where
  float : FloatMode := .native

/-- Per-unit context. -/
structure Ctx where
  tags : Tags
  tag : String
  /-- The link symbol of every global object and function, by symbol number. -/
  names : Std.HashMap Nat Symbol
  funcs : Std.HashMap Nat FuncInfo
  opts : LowerOptions := {}

/-- Where a local lives. -/
inductive Home where
  | reg (r : Reg)
  /-- At this offset from the frame pointer. -/
  | mem (off : Nat)

/-- An lvalue: a register, or an address `base + off` in the linear memory. -/
inductive LV where
  | reg (r : Reg)
  | mem (base : Reg) (off : Nat)

/-- Unit-level state: data objects created while lowering (string literals). -/
structure UState where
  data : Array Mir.Data := #[]
  count : Nat := 0
  functions : Array Silmaril.Compiler.Native.FunctionInfo := #[]
  calls : Array Silmaril.Compiler.Native.CallInfo := #[]
  intrinsics : Array Silmaril.Compiler.Native.X87.Intrinsic := #[]
  deriving Inhabited

/-- Per-function state. -/
structure FState where
  blocks : Array (Option Mir.Block) := #[]
  cur : Nat := 0
  instrs : Array Instr := #[]
  nextReg : Nat := 2
  homes : Std.HashMap Nat (Home × Ctype) := {}
  frame : Nat := 0
  /-- The strictest alignment of a frame object; above 16 the prologue realigns. -/
  frameAlign : Nat := 16
  breakL : Option Nat := none
  contL : Option Nat := none
  cases : List Nat := []
  labels : Std.HashMap Nat Nat := {}
  retType : CType := .void
  /-- Caller-owned destination for an aggregate result (the first hidden parameter). -/
  retArea : Option Reg := none
  vaArea : Option Reg := none
  nativeVa : Option Silmaril.Compiler.Native.Varargs.Activation := none
  addrTaken : Std.HashSet Nat := {}
  unit : UState := {}
  /-- Address-taken parameters to store into the frame at entry. -/
  paramStores : List (Reg × Nat × CType) := []

abbrev M := ReaderT Ctx (StateT FState (Except String))

/-- The frame pointer. -/
def fpReg : Reg := 0
/-- The software stack pointer at entry. -/
def spReg : Reg := 1

def fail {α : Type} (msg : String) : M α := throw msg

def fresh : M Reg := modifyGet fun s => (s.nextReg, { s with nextReg := s.nextReg + 1 })

def emit (i : Instr) : M Unit := modify fun s => { s with instrs := s.instrs.push i }

def op (o : Lir.Op Reg) : M Unit := emit (.op o)

def newLabel : M Nat := modifyGet fun s => (s.blocks.size, { s with blocks := s.blocks.push none })

/-- End the current block with `t`. -/
def finish (t : Lir.Term Reg) : M Unit := modify fun s =>
  { s with blocks := s.blocks.set! s.cur (some ⟨s.instrs, t⟩), instrs := #[] }

def start (l : Nat) : M Unit := modify fun s => { s with cur := l }

def jumpTo (l : Nat) : M Unit := finish (.jump l)

/-- After a jump: continue in a fresh (unreachable) block. -/
def deadBlock : M Unit := do start (← newLabel)

def constReg (v : Int) : M Reg := do
  let r ← fresh
  op (.const r (BitVec.ofInt 64 v))
  return r

def binop (o : Lir.Binop) (a b : Reg) : M Reg := do
  let r ← fresh
  op (.binary o r a b)
  return r

def unop (o : Lir.Unop) (a : Reg) : M Reg := do
  let r ← fresh
  op (.unary o r a)
  return r

def addConst (a : Reg) (k : Int) : M Reg := do
  if k == 0 then return a
  binop .add a (← constReg k)

def liftE {α : Type} (x : Except String α) : M α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

def sizeOf (ty : Ctype) : M Nat := do return (← liftE (Silmaril.Compiler.Native.Layout.sizeAlign (← read).tags ty)).1

/-- `n` bytes of the frame, aligned. -/
def allocBytes (n align : Nat) : M Nat := do
  let s ← get
  let off := Mir.alignUp s.frame (max align 1)
  set { s with frame := off + max n 1, frameAlign := max s.frameAlign align }
  return off

/-- Native extended operations remain effectful through the existing Mir
optimizer. Memory destinations and every input are explicit SSA operands. -/
def x87 (operation : Silmaril.Compiler.Native.X87.Operation) (inputs : List Reg) : M Reg := do
  unless operation.supported do fail "unsupported native x87 operation/width"
  let destination ← if operation.memoryResult then
      addConst fpReg (← allocBytes 16 16)
    else fresh
  let operands := if operation.memoryResult then destination :: inputs else inputs
  let results := if operation.memoryResult then [] else [destination]
  let key := s!"__ccomp_x87.{(← read).tag}.{(← get).unit.intrinsics.size}"
  let intrinsic : Silmaril.Compiler.Native.X87.Intrinsic := ⟨key, operation⟩
  modify fun s => { s with unit.intrinsics := s.unit.intrinsics.push intrinsic }
  emit (.call key operands results)
  return destination

/-! ## Scalars -/

def normUnop : Nat → Bool → Option Lir.Unop
  | 1, true => some .sext8
  | 1, false => some .zext8
  | 2, true => some .sext16
  | 2, false => some .zext16
  | 4, true => some .sext32
  | 4, false => some .zext32
  | _, _ => none

/-- Re-normalize `r` to the integer type `(w, s)`. -/
def norm (r : Reg) (w : Nat) (s : Bool) : M Reg :=
  match normUnop w s with
  | some u => unop u r
  | none => pure r

/-- Call `callee args`; the result register when `ret`. -/
def callFn (callee : Symbol) (args : List Reg) (ret : Bool) : M (Option Reg) := do
  if ret then
    let r ← fresh
    emit (.call callee args [r])
    return some r
  else
    emit (.call callee args [])
    return none

/-- Call the runtime routine `name` (soft-float) for its one result. -/
def rtCall (name : Symbol) (args : List Reg) : M Reg := do
  let r ← fresh
  emit (.call name args [r])
  return r

/-- The letter of a floating format in the soft-float routine names. -/
def fsuf (w : Nat) : String := if w == 4 then "f" else "d"

/-- The Lir format of a floating type of `w` bytes. -/
def ffmt (w : Nat) : Lir.FFmt := if w == 4 then .f32 else .f64

/-- Whether floating point is lowered to Lir's floating-point instructions. -/
def native : M Bool := return (← read).opts.float == .native

/-- `op a b` into a fresh register; a unary operator reads `a` only. -/
def fop (o : Lir.FOp) (a b : Reg) : M Reg := do
  let r ← fresh
  emit (.fop o r a b)
  return r

/-- `if c ≠ 0 then b else a` for `c ∈ {0, 1}`, without a branch. -/
def select (c a b : Reg) : M Reg := do
  let m ← binop .sub (← constReg 0) c
  let nm ← binop .xor m (← constReg (-1))
  binop .or (← binop .and a nm) (← binop .and b m)

/-- The unsigned 64-bit integer `r` to format `f`, rounded once: `ofInt` when it is
below `2^63`, otherwise twice the conversion of `(r >> 1) | (r & 1)` (gcc's sequence;
the halving keeps a sticky bit, so the result is correctly rounded). -/
def u64ToFloat (f : Lir.FFmt) (r : Reg) : M Reg := do
  let lo ← fop (.ofInt f) r r
  let h ← binop .or (← binop .shru r (← constReg 1)) (← binop .and r (← constReg 1))
  let hc ← fop (.ofInt f) h h
  let hi ← fop (.add f) hc hc
  select (← binop .shru r (← constReg 63)) lo hi

/-- A binary64 value to an unsigned 64-bit integer, as gcc's sequence: values below
`2^63` (and NaN) truncate directly, the others truncate `x - 2^63` and set bit 63. -/
def f64ToU64 (r : Reg) : M Reg := do
  let two63 ← constReg 0x43E0000000000000
  let lo ← fop (.toInt .f64 true) r r
  let hi ← binop .xor (← fop (.toInt .f64 true) (← fop (.sub .f64) r two63) r)
    (← constReg (-0x8000000000000000))
  select (← fop (.cmp .f64 .le) two63 r) lo hi

/-- `x ≠ 0` for the encoding `r` of format `w`: false for both zeros, true for NaN. -/
def floatTruth (r : Reg) (w : Nat) : M Reg := do
  let sh ← binop .shl r (← constReg (if w == 4 then 33 else 1))
  binop (.cmp .ne) sh (← constReg 0)

/-- Convert the canonical value `r` of type `src` to type `dst`. Floating to integer
truncates as x86-64's `cvttsd2si` does (32-bit for `int` and narrower signed or
16/8-bit targets, 64-bit otherwise, gcc's sequence for `unsigned long`). -/
def conv (r : Reg) (src dst : CType) : M Reg := do
  if Silmaril.Compiler.Native.Types.addressScalar src || Silmaril.Compiler.Native.Types.addressScalar dst then
    if Silmaril.Compiler.Native.Types.addressFormat src == Silmaril.Compiler.Native.Types.addressFormat dst then
      return r
    else
      let source ← liftE (Silmaril.Compiler.Native.X87.Format.ofType src)
      let target ← liftE (Silmaril.Compiler.Native.X87.Format.ofType dst)
      return ← x87 (.convert source target) [r]
  match dst, src with
  | .bool, .float w => floatTruth r w
  | .bool, .bool => pure r
  | .bool, _ => do binop (.cmp .ne) r (← constReg 0)
  | .float w, .float v => do
    if (w == 4) == (v == 4) then pure r
    else if (← native) then fop (if w == 4 then .narrow else .widen) r r
    else rtCall (if w == 4 then "__ccomp_d2f" else "__ccomp_f2d") [r]
  | .float w, .int 8 false => do
    if (← native) then u64ToFloat (ffmt w) r else rtCall s!"__ccomp_u2{fsuf w}" [r]
  | .float w, _ => do
    if (← native) then fop (.ofInt (ffmt w)) r r else rtCall s!"__ccomp_i2{fsuf w}" [r]
  | .int w s, .float v => do
    -- 64-bit truncation for `long`, `unsigned long` (gcc's sequence) and `unsigned int`,
    -- 32-bit truncation otherwise
    if (← native) then
      let d ← if w == 8 && !s then f64ToU64 (← if v == 4 then fop .widen r r else pure r)
        else fop (.toInt (ffmt v) (w == 8 || (w == 4 && !s))) r r
      norm d w s
    else
      let d ← if v == 4 then rtCall "__ccomp_f2d" [r] else pure r
      let name := if w == 8 then (if s then "__ccomp_d2i" else "__ccomp_d2u")
        else if w == 4 && !s then "__ccomp_d2i" else "__ccomp_d2i32"
      norm (← rtCall name [d]) w s
  | .int w s, _ => norm r w s
  | _, _ => pure r

def width : Nat → Lir.Width
  | 1 => .b1
  | 2 => .b2
  | 4 => .b4
  | _ => .b8

/-- Load a scalar of type `t` from `base + off`. -/
def loadMem (t : CType) (base : Reg) (off : Nat) : M Reg := do
  match t with
  | .agg _ => addConst base off
  | .int .. | .bool | .ptr _ | .float _ =>
    let (w, s) := t.intShape
    let r ← fresh
    op (.load (width w) (if s then .sign else .zero) r base off)
    return r
  | _ => fail "load of a non-scalar"

def storeMem (t : CType) (base : Reg) (off : Nat) (v : Reg) : M Unit := do
  let (w, _) := t.intShape
  op (.store (width w) base off v)

/-- The address of a symbol. -/
def symAddr (sym : Symbol) : M Reg := do
  let r ← fresh
  emit (.addr r sym 0)
  return r

/-- Copy `n` bytes from `src` to `dst`. -/
def copyBytes (dst src : Reg) (n : Nat) : M Unit := do
  if n ≤ 64 then
    let mut i := 0
    while i + 8 ≤ n do
      let t ← fresh; op (.load .b8 .zero t src i); op (.store .b8 dst i t); i := i + 8
    while i < n do
      let t ← fresh; op (.load .b1 .zero t src i); op (.store .b1 dst i t); i := i + 1
  else
    let _ ← callFn "memcpy" [dst, src, ← constReg n] true

/-- Zero `n` bytes at `dst + off`. -/
def zeroBytes (dst : Reg) (off n : Nat) : M Unit := do
  if n ≤ 128 then
    let z ← constReg 0
    let mut i := 0
    while i + 8 ≤ n do
      op (.store .b8 dst (off + i) z); i := i + 8
    while i < n do
      op (.store .b1 dst (off + i) z); i := i + 1
  else
    let d ← addConst dst off
    let _ ← callFn "memset" [d, ← constReg 0, ← constReg n] true

/-- The control block's address. -/
def ctlAddr : M Reg := symAddr ctlSymbol

/-! ## Constants and string literals -/

def hexValue (ds : List Char) : Nat :=
  ds.foldl (fun a d => a * 16 + (if d.isDigit then d.toNat - 48 else d.toLower.toNat - 87)) 0

/-- The value of a character or escape sequence lexeme (a code point for a universal
character name `\u`, `\U`). -/
def escapeValue (s : List Char) : Option (Nat × List Char) :=
  match s with
  | '\\' :: c :: rest =>
    match c with
    | 'n' => some (10, rest) | 't' => some (9, rest) | 'r' => some (13, rest)
    | 'a' => some (7, rest) | 'b' => some (8, rest) | 'f' => some (12, rest)
    | 'v' => some (11, rest) | 'e' => some (27, rest)
    | '\\' => some (92, rest) | '\'' => some (39, rest) | '"' => some (34, rest)
    | '?' => some (63, rest)
    | 'x' =>
      let ds := rest.takeWhile Char.isHexDigit
      some (hexValue ds, rest.drop ds.length)
    | 'u' => let ds := (rest.take 4).takeWhile Char.isHexDigit; some (hexValue ds, rest.drop ds.length)
    | 'U' => let ds := (rest.take 8).takeWhile Char.isHexDigit; some (hexValue ds, rest.drop ds.length)
    | _ =>
      if c.isDigit then
        let ds := (c :: rest).take 3 |>.takeWhile fun d => '0' ≤ d ∧ d ≤ '7'
        some (ds.foldl (fun a d => a * 8 + (d.toNat - 48)) 0, (c :: rest).drop ds.length)
      else some (c.toNat, rest)
  | c :: rest => some (c.toNat, rest)
  | [] => none

/-- The width in bytes of a code unit of a string literal with this prefix: `char` for
none and `u8`, `char16_t` for `u`, `char32_t` for `U`, `wchar_t` (`int` on LP64 Linux)
for `L`. -/
def unitWidth : Option EncodingPrefix → Nat
  | some .utf16 => 2
  | some .utf32 | some .wide => 4
  | _ => 1

/-- Append the code unit `v`, truncated to `w` bytes, little-endian. -/
def pushUnit (w : Nat) (b : ByteArray) (v : Nat) : ByteArray :=
  (List.range w).foldl (fun b i => b.push ((v / 256 ^ i) % 256).toUInt8) b

/-- The code units of the code point `v` in UTF-8, UTF-16 or UTF-32 (`w` = 1, 2, 4). -/
def codeUnits (w v : Nat) : List Nat :=
  if w == 1 then
    if v < 0x80 then [v]
    else if v < 0x800 then [0xC0 + v / 64, 0x80 + v % 64]
    else if v < 0x10000 then [0xE0 + v / 4096, 0x80 + v / 64 % 64, 0x80 + v % 64]
    else [0xF0 + v / 262144, 0x80 + v / 4096 % 64, 0x80 + v / 64 % 64, 0x80 + v % 64]
  else if w == 2 && v ≥ 0x10000 then [0xD800 + (v - 0x10000) / 1024, 0xDC00 + (v - 0x10000) % 1024]
  else [v]

/-- Append source characters (UTF-8 bytes) as units of `w` bytes: copied when `w = 1`,
decoded otherwise (byte by byte when they are not valid UTF-8). -/
def pushSource (w : Nat) (b raw : ByteArray) : ByteArray :=
  if w == 1 then b ++ raw
  else match String.fromUTF8? raw with
    | some t => t.toList.foldl (fun b c => (codeUnits w c.toNat).foldl (pushUnit w) b) b
    | none => raw.toList.foldl (fun b x => pushUnit w b x.toNat) b

/-- The image of a string literal (STD §6.4.5, gcc's UTF-8 execution character set):
its code units of `unitWidth` bytes, little-endian, then a NUL unit. A source character
or a universal character name is encoded (UTF-8, UTF-16 or UTF-32); an octal or hex
escape is one unit. -/
def stringBytes (s : StringLiteral) : ByteArray := Id.run do
  let w := unitWidth s.1
  let mut b := ByteArray.empty
  let mut raw := ByteArray.empty
  for (_, lexemes) in s.2 do
    for lx in lexemes do
      match lx with
      | .bytes d => raw := raw ++ d
      | .utf8 t =>
        if t.startsWith "\\" then
          b := pushSource w b raw
          raw := ByteArray.empty
          match escapeValue t.toList with
          | some (v, _) =>
            b := if t.startsWith "\\u" || t.startsWith "\\U" then (codeUnits w v).foldl (pushUnit w) b
              else pushUnit w b v
          | none => pure ()
        else raw := raw ++ t.toUTF8
  return pushUnit w (pushSource w b raw) 0

/-- The value of a character constant (plain `char` is signed). A plain multi-character
constant packs its bytes; a prefixed one is its last character (gcc), as a `wchar_t`
(`int`), `char16_t` or `char32_t`. -/
def charValue (c : CharacterConstant) : Int :=
  let rec go (wide : Bool) (cs : List Char) (acc : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 => match escapeValue cs with
      | some (v, rest) => go wide rest (if wide then v else acc * 256 + v % 256) fuel
      | none => acc
  let text := match c.2 with
    | .utf8 t => t.toList
    | .bytes d => d.toList.map fun b => Char.ofNat b.toNat
  let v := go c.1.isSome text 0 text.length
  match c.1 with
  | none => if v < 256 then (if v ≥ 128 then (v : Int) - 256 else v) else v
  | some .wide => let u : Nat := v % 2 ^ 32; if u ≥ 2 ^ 31 then (u : Int) - 2 ^ 32 else (u : Int)
  | some .utf16 => ((v % 2 ^ 16 : Nat) : Int)
  | some .utf32 => ((v % 2 ^ 32 : Nat) : Int)

/-- Native integer bounds and literal values share their guarded native layout. -/
def intConstValue : IntegerConstant → Except String Int :=
  Silmaril.Compiler.Native.Types.integerConstantValue

/-- Integer initialization converts to the destination type before encoding its
storage. In particular, `_Bool` keeps truth rather than the integer's low byte. -/
def integerInitBits (ty : CType) (value : Int) : Nat :=
  match ty with
  | .bool => if value == 0 then 0 else 1
  | _ => (value % 2 ^ 64).toNat

/-- A new read-only data object holding the string literal `lit`. -/
def stringObject (lit : StringLiteral) : M Symbol := do
  let s ← get
  let name := s!".str.{(← read).tag}.{s.unit.count}"
  let bytes := stringBytes lit
  let d : Mir.Data := { name, size := bytes.size, align := unitWidth lit.1, init := bytes,
                        exported := false, readonly := true }
  set { s with unit := { s.unit with data := s.unit.data.push d, count := s.unit.count + 1 } }
  return name

/-- Write the constant `c` of type `ty` at `off` into an image. -/
def gConst (tags : Tags) (img : ByteArray) (off : Nat) (ty : Ctype) (c : Constant) :
    Except String ByteArray := do
  match c with
  | .array et cs =>
    let (esize, _) ← Silmaril.Compiler.Native.Layout.sizeAlign tags et
    cs.attach.zipIdx.foldlM (fun img (element, i) =>
      gConst tags img (off + i * esize) et element.val) img
  | .struct _ ms =>
    ms.attach.foldlM (fun img member =>
      match _memberValue : member.val with
      | (m, c) => do
        let (moff, mty) ← Silmaril.Compiler.Native.Layout.memberOf tags ty m
        gConst tags img (off + moff) mty c) img
  | .union _ m c =>
    let (moff, mty) ← Silmaril.Compiler.Native.Layout.memberOf tags ty m
    gConst tags img (off + moff) mty c
  | .indeterminate _ | .null => return img
  | .integer ic =>
      let (w, _) := (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty).intShape
      let value ← Silmaril.Compiler.Native.Types.Registered.integerConstantValue tags ic
      if Silmaril.Compiler.Native.Types.addressFormat (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty) == 1 then
        return Mir.writeLE img off 16 (Silmaril.Compiler.Native.X87.Literals.integer value)
      return Mir.writeLE img off w (integerInitBits (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty) value)
  | .character ch =>
      if Silmaril.Compiler.Native.Types.addressFormat (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty) == 1 then
        return Mir.writeLE img off 16 (Silmaril.Compiler.Native.X87.Literals.integer (charValue ch))
      let (w, _) := (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty).intShape
      return Mir.writeLE img off w
        (integerInitBits (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty) (charValue ch))
  | .predefined p =>
      let value := if p matches .true_ then 1 else 0
      if Silmaril.Compiler.Native.Types.addressFormat (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty) == 1 then
        return Mir.writeLE img off 16 (Silmaril.Compiler.Native.X87.Literals.integer value)
      return Mir.writeLE img off 1 value.toNat
  | .floating literal@(text, _) =>
    if Silmaril.Compiler.Native.Types.addressFormat (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty) == 1 then
      let some bits := Silmaril.Compiler.Native.X87.Literals.constant literal
        | throw s!"bad or unsupported native x87 literal {text}"
      return Mir.writeLE img off 16 bits
    let .float w := Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty | throw "floating constant of a non-floating type"
    match FloatConst.parse w text with
    | some b => return Mir.writeLE img off w b
    | none => throw s!"bad floating constant {text}"
termination_by SizeOf.sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have bound := List.sizeOf_lt_of_mem element.property; omega
    | have bound := List.sizeOf_lt_of_mem member.property
      rcases member with ⟨⟨identifier, constant⟩, membership⟩
      simp_all
      omega

/-- A new read-only data object of `size` bytes holding `img`. -/
def constObject (img : ByteArray) (size : Nat) : M Symbol := do
  let s ← get
  let name := s!".const.{(← read).tag}.{s.unit.count}"
  let d : Mir.Data := { name, size, align := 16, init := img, exported := false, readonly := true }
  set { s with unit := { s.unit with data := s.unit.data.push d, count := s.unit.count + 1 } }
  return name

/-- The link symbol of a global object or function. -/
def globalName (x : Sym) : M Symbol := do
  match (← read).names[x.number]? with
  | some n => return n
  | none => return symName x

/-! ## Frames -/

/-- A frame object of type `ty`, with its declared alignment if any. -/
def allocFrame (ty : Ctype) (align : Option Alignment := none) : M Nat := do
  let (size, align) ← liftE (Silmaril.Compiler.Native.Layout.objectLayout (← read).tags ty align)
  allocBytes size align

/-- Give a local its home. -/
def bindLocal (x : Sym) (ty : Ctype) (align : Option Alignment := none) : M Unit := do
  let tags := (← read).tags
  let t := Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty
  let taken := (← get).addrTaken.contains x.number
  let home ← if t.isScalar && !taken then pure (Home.reg (← fresh))
    else pure (Home.mem (← allocFrame ty align))
  modify fun s => { s with homes := s.homes.insert x.number (home, ty) }

/-- Restore the software stack pointer (before a return). -/
def epilogue : M Unit := pure ()

/-! ## Expressions -/

/-- The pointee size used by pointer arithmetic (`void` and functions: 1). -/
def pointeeSize : CType → M Nat
  | .ptr t => sizeOf t
  | _ => pure 1

/-- The comparison of a relational operator. -/
def relCond (op : BinaryOperator) (signed : Bool) : Option Lir.Cond :=
  match op with
  | .lt => some (if signed then .lts else .ltu)
  | .gt => some (if signed then .gts else .gtu)
  | .le => some (if signed then .les else .leu)
  | .ge => some (if signed then .ges else .geu)
  | .eq => some .eq
  | .ne => some .ne
  | _ => none

/-- Integer arithmetic on canonical values of type `(w, s)`. -/
def arith (aop : ArithmeticOperator) (w : Nat) (s : Bool) (a b : Reg) : M Reg := do
  let o : Lir.Binop := match aop with
    | .mul => .mul | .div => if s then .divs else .divu | .mod => if s then .rems else .remu
    | .add => .add | .sub => .sub | .shl => .shl | .shr => if s then .shrs else .shru
    | .band => .and | .bxor => .xor | .bor => .or
  norm (← binop o a b) w s

/-- `a op b` where `a : ta`, `b : tb` (already evaluated) and the result has type `t`. -/
def arithValues (aop : ArithmeticOperator) (t ta tb : CType) (a b : Reg) : M Reg := do
  match t with
  | .ptr _ =>
    -- pointer ± integer
    if ta.isPtr then
      let k ← pointeeSize ta
      let bb ← if k == 1 then pure b else binop .mul b (← constReg k)
      binop (if aop == .sub then .sub else .add) a bb
    else
      let k ← pointeeSize tb
      let aa ← if k == 1 then pure a else binop .mul a (← constReg k)
      binop .add aa b
  | .int w s =>
    if ta.isPtr && tb.isPtr then
      -- pointer difference
      let k ← pointeeSize ta
      let d ← binop .sub a b
      if k == 1 then return d else binop .divs d (← constReg k)
    else if aop == .shl || aop == .shr then
      arith aop w s (← conv a ta t) b
    else
      arith aop w s (← conv a ta t) (← conv b tb t)
  | .bool => do
    let r ← arith aop 8 false a b
    conv r (.int 8 false) .bool
  | .float w => do
    let a ← conv a ta t
    let b ← conv b tb t
    let name ← match aop with
      | .add => pure "add" | .sub => pure "sub" | .mul => pure "mul" | .div => pure "div"
      | _ => fail "floating operator"
    if (← native) then
      let f := ffmt w
      fop (match aop with | .add => .add f | .sub => .sub f | .mul => .mul f | _ => .div f) a b
    else rtCall s!"__ccomp_{fsuf w}{name}" [a, b]
  | .agg _ =>
    unless Silmaril.Compiler.Native.Types.addressFormat t == 1 do
      fail "arithmetic on an unsupported extended scalar"
    let operator ← match aop with
      | .add => pure Silmaril.Compiler.Native.X87.Arithmetic.add
      | .sub => pure .sub | .mul => pure .mul | .div => pure .div
      | _ => fail "unsupported native x87 arithmetic operator"
    x87 (.arithmetic operator) [← conv a ta t, ← conv b tb t]
  | _ => fail "arithmetic on an unsupported type"

/-- A relational or equality operator on two encodings of format `w`: a Lir
comparison (`>` and `≥` swap the operands), or from the routine `__ccomp_{d,f}cmp`:
0 (equal), 1 (less), 2 (greater) or 3 (unordered). -/
def floatCmp (bop : BinaryOperator) (w : Nat) (a b : Reg) : M Reg := do
  if (← native) then
    let f := ffmt w
    match bop with
    | .eq => return ← fop (.cmp f .eq) a b
    | .ne => return ← fop (.cmp f .ne) a b
    | .lt => return ← fop (.cmp f .lt) a b
    | .gt => return ← fop (.cmp f .lt) b a
    | .le => return ← fop (.cmp f .le) a b
    | .ge => return ← fop (.cmp f .le) b a
    | _ => fail "bad comparison"
  let c ← rtCall s!"__ccomp_{fsuf w}cmp" [a, b]
  match bop with
  | .eq => binop (.cmp .eq) c (← constReg 0)
  | .ne => binop (.cmp .ne) c (← constReg 0)
  | .lt => binop (.cmp .eq) c (← constReg 1)
  | .gt => binop (.cmp .eq) c (← constReg 2)
  | .le => binop (.cmp .leu) c (← constReg 1)
  | .ge => binop (.cmp .eq) (← binop .and c (← constReg 1)) (← constReg 0)
  | _ => fail "bad comparison"

/-! ## Statement analyses -/

/-- Collect the labels of the `case`s and `default` of a switch body, in order, with
their values (`none` for `default`), not entering nested switches. -/
abbrev switchCases := Silmaril.Compiler.Native.Analysis.switchCases

abbrev addrTakenS := Silmaril.Compiler.Native.Analysis.addrTakenStatement

/-- Preserve the previous nested helper's interface for direct consumers. -/
abbrev addrTakenS.addrTakenE := Silmaril.Compiler.Native.Analysis.addrTakenExpression

def labelOf (x : Sym) : M Nat := do
  match (← get).labels[x.number]? with
  | some l => return l
  | none =>
    let l ← newLabel
    modify fun s => { s with labels := s.labels.insert x.number l }
    return l

/-- Round a native address up without using the old linear-memory cursor. -/
def alignAddress (address : Reg) (alignment : Nat) : M Reg := do
  binop .and (← addConst address (alignment - 1)) (← constReg (-(alignment : Int)))

/-- Evaluate a native va_arg after its list expression has been evaluated once.
All reconstruction uses the same ABI eightbyte chunks as ordinary calls. -/
def nativeVaArg (cell : Reg) (type : CType) : M Reg := do
  let tags := (← read).tags
  let object ← liftE (Silmaril.Compiler.Native.Varargs.argumentObject tags type)
  let offset ← allocBytes object.size object.align
  let destination ← addConst fpReg offset
  zeroBytes destination 0 object.size
  let overflow : M Unit := do
    let cursor ← loadMem (.int 8 false) cell 8
    let source ← alignAddress cursor (max 8 object.align)
    copyBytes destination source object.size
    let next ← alignAddress (← addConst source object.size) 8
    storeMem (.int 8 false) cell 8 next
  if Silmaril.Compiler.Native.Varargs.onStack object then
    overflow
  else
    let pieces ← liftE (Silmaril.Compiler.Native.Varargs.pieces object)
    let gp ← loadMem (.int 4 false) cell 0
    let fp ← loadMem (.int 4 false) cell 4
    let gpAvailable ← binop (.cmp .leu) gp
      (← constReg (48 - 8 * Silmaril.Machine.SystemV.Abi.gpCount object))
    let fpAvailable ← binop (.cmp .leu) fp
      (← constReg (176 - 16 * Silmaril.Machine.SystemV.Abi.vectorCount object))
    let registers ← newLabel
    let stack ← newLabel
    let done ← newLabel
    finish (.branch (← binop .and gpAvailable fpAvailable) registers stack)
    start registers
    let saved ← loadMem (.int 8 false) cell 16
    for piece in pieces do
      let cursor := match piece.bank with | .gp => gp | .fp => fp
      let source ← addConst (← binop .add saved cursor) piece.saveOffset
      copyBytes (← addConst destination piece.objectOffset) source piece.bytes
    storeMem (.int 4 false) cell 0
      (← addConst gp (8 * Silmaril.Machine.SystemV.Abi.gpCount object))
    storeMem (.int 4 false) cell 4
      (← addConst fp (16 * Silmaril.Machine.SystemV.Abi.vectorCount object))
    jumpTo done
    start stack
    overflow
    jumpTo done
    start done
  loadMem type destination 0

/-! ## Expressions and statements

One mutual block: a GNU statement expression `({ … })` puts statements inside an
expression. -/

/-- Read an lvalue of type `t`. -/
def loadLV (lv : LV) (t : CType) : M Reg :=
  match lv with
  | .reg r => pure r
  | .mem b o => loadMem t b o

def storeLV (lv : LV) (t : CType) (v : Reg) : M Unit := do
  match lv, t with
  | .reg r, _ => op (.move r v)
  | .mem b o, .agg ty => copyBytes (← addConst b o) v (← sizeOf ty)
  | .mem b o, _ => storeMem t b o v

/-- The address of an lvalue. -/
def lvAddr (lv : LV) : M Reg :=
  match lv with
  | .mem b o => addConst b o
  | .reg _ => fail "address of a register local"

/-- The value of a constant of type `t`. -/
def constant (c : Constant) (t : CType) : M Reg := do
  let tags := (← read).tags
  match c with
  | .integer ic =>
      let (w, s) := t.intShape
      norm (← constReg (← liftE (Silmaril.Compiler.Native.Types.Registered.integerConstantValue tags ic))) w s
  | .character ch => constReg (charValue ch)
  | .null => constReg 0
  | .predefined .true_ => constReg 1
  | .predefined .false_ => constReg 0
  | .floating literal@(text, _) =>
    if Silmaril.Compiler.Native.Types.addressFormat t == 1 then
      let some bits := Silmaril.Compiler.Native.X87.Literals.constant literal
        | fail s!"bad or unsupported native x87 literal {text}"
      let image := Mir.writeLE (ByteArray.mk (Array.replicate 16 0)) 0 16 bits
      return ← symAddr (← constObject image 16)
    let .float w := t | fail "floating constant of a non-floating type"
    match FloatConst.parse w text with
    | some b => constReg b
    | none => fail s!"bad floating constant {text}"
  | _ => fail "unsupported constant"

theorem expressionNode_size_lt (e : TypedExpression) : SizeOf.sizeOf e.node < SizeOf.sizeOf e := by
  cases e
  simp [Expression.node]

theorem statementNode_size_lt (s : TypedStatement) : SizeOf.sizeOf s.node < SizeOf.sizeOf s := by
  cases s
  simp [Statement.node]

scoped macro "native_lowering_decreasing" : tactic => do
  let child := Lean.mkIdent `child
  let argument := Lean.mkIdent `argument
  let element := Lean.mkIdent `element
  let member := Lean.mkIdent `member
  let declaration := Lean.mkIdent `declaration
  let association := Lean.mkIdent `association
  let a := Lean.mkIdent `a
  let last := Lean.mkIdent `last
  `(tactic| (
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp_all [Prod.lex_def]
    all_goals try have _childSize := List.sizeOf_lt_of_mem ($child).property
    all_goals try have _argumentSize := List.sizeOf_lt_of_mem ($argument).property
    all_goals try have _elementSize := List.sizeOf_lt_of_mem ($element).property
    all_goals try have _memberSize := List.sizeOf_lt_of_mem ($member).property
    all_goals try have _declarationSize := List.sizeOf_lt_of_mem ($declaration).property
    all_goals try have _associationSize := List.sizeOf_lt_of_mem ($association).property
    all_goals try have _operandSize := expressionNode_size_lt ($a)
    all_goals try have _lastSize := List.sizeOf_lt_of_mem ($last).property
    all_goals try have _lastNodeSize := statementNode_size_lt ($last).val
    all_goals try simp_all
    all_goals omega
  ))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
mutual

/-- The lvalue designated by `e`. -/
def lval (e : TypedExpression) : M LV := do
  let tags := (← read).tags
  let .mk _ _ _ node := e
  match _rootNode : node with
  | .ident x =>
    match (← get).homes[x.number]? with
    | some (.reg r, _) => return .reg r
    | some (.mem off, _) => return .mem fpReg off
    | none => return .mem (← symAddr (← globalName x)) 0
  | .unary .indirection p => return .mem (← expr p) 0
  | .memberof a m =>
    let ty ← match a.annotation with
      | .lvalue _ ty _ => pure ty
      | .rvalue (.struct t) => pure (Ctype.mk [] (.struct t))
      | .rvalue (.union t) => pure (Ctype.mk [] (.union t))
      | _ => fail "member of a non-aggregate"
    let (off, _) ← liftE (Silmaril.Compiler.Native.Layout.memberOf (← read).tags ty m)
    match ← lvalOrAddr a with
    | .mem b o => return .mem b (o + off)
    | .reg _ => fail "member of a register"
  | .memberofptr p m =>
    let ty ← match Silmaril.Compiler.Native.Types.Registered.typeOf tags p with
      | .ptr t => pure t
      | _ => fail "-> on a non-pointer"
    let (off, _) ← liftE (Silmaril.Compiler.Native.Layout.memberOf (← read).tags ty m)
    return .mem (← expr p) off
  | .str s => return .mem (← symAddr (← stringObject s)) 0
  | .compound _ ty init =>
    let off ← allocFrame ty
    initAt fpReg off ty init
    return .mem fpReg off
  | .annot _ a => lval a
  | _ => fail s!"unsupported lvalue"
termination_by (SizeOf.sizeOf e, 0)
decreasing_by native_lowering_decreasing

/-- An lvalue, or the address of an aggregate rvalue (a struct returned by `?:`). -/
def lvalOrAddr (e : TypedExpression) : M LV := do
  match e.annotation with
  | .lvalue .. => lval e
  | .rvalue _ => return .mem (← expr e) 0
termination_by (SizeOf.sizeOf e, 2)
decreasing_by native_lowering_decreasing

/-- The truth of a scalar condition: a register that is nonzero exactly when `e` is. -/
def test (e : TypedExpression) : M Reg := do
  let tags := (← read).tags
  let type := Silmaril.Compiler.Native.Types.Registered.typeOf tags e
  if Silmaril.Compiler.Native.Types.addressScalar type then
    return ← conv (← expr e) type .bool
  let v ← expr e
  match type with
  | .float w => floatTruth v w
  | _ => pure v
termination_by (SizeOf.sizeOf e, 2)
decreasing_by native_lowering_decreasing

/-- Evaluate `e` and convert it to `t`. -/
def exprAs (e : TypedExpression) (t : CType) : M Reg := do
  let tags := (← read).tags
  conv (← expr e) (Silmaril.Compiler.Native.Types.Registered.typeOf tags e) t
termination_by (SizeOf.sizeOf e, 2)
decreasing_by native_lowering_decreasing

/-- The value of `e`: a canonical scalar, or the address of an aggregate.
The Ail atomic-value wrapper preserves the underlying value in the single-threaded
execution model; its operand is evaluated exactly once. Atomic builtins remain
unsupported. Intended theorem: this case has the same value and effects as the
wrapped expression, with the ordinary assignment conversion. -/
def expr (e : TypedExpression) : M Reg := do
  let tags := (← read).tags
  let .mk annotation annotations location node := e
  let e : TypedExpression := .mk annotation annotations location node
  let t := Silmaril.Compiler.Native.Types.Registered.typeOf tags e
  if let .unsupported why := t then fail why
  match _rootNode : node with
  | .rvalue a => loadLV (← lval a) t
  | .arrayDecay a => lvAddr (← lval a)
  | .functionDecay a =>
    match _hOperand : a.node with
    | .ident f => symAddr (← globalName f)
    | .unary .indirection p => expr p
    | _ => expr a
  | .ident x =>
    match (← get).homes[x.number]? with
    | some _ => loadLV (← lval e) t
    | none => symAddr (← globalName x)
  | .const c => constant c t
  | .str s => symAddr (← stringObject s)
  | .annot _ a => exprAs a t
  | .cast _ _ a => exprAs a t
  | .atomic a => exprAs a t
  | .unary uop a =>
    match _unaryOp : uop with
    | .plus => exprAs a t
    | .minus =>
      if Silmaril.Compiler.Native.Types.addressFormat t == 1 then
        return ← x87 .negate [← exprAs a t]
      if Silmaril.Compiler.Native.Types.addressScalar t then
        fail "extended native integer negation requires arithmetic lowering"
      match t with
      | .float w => binop .xor (← exprAs a t) (← constReg (FloatConst.signBit w))
      | _ =>
        let (w, s) := t.intShape
        norm (← binop .sub (← constReg 0) (← exprAs a t)) w s
    | .bnot =>
      if Silmaril.Compiler.Native.Types.addressScalar t then fail "bitwise operation on extended scalar"
      let (w, s) := t.intShape
      norm (← binop .xor (← exprAs a t) (← constReg (-1))) w s
    | .address =>
      match _hOperand : a.node with
      | .ident f =>
        if (← get).homes.contains f.number then lvAddr (← lval a)
        else symAddr (← globalName f)
      | _ => lvAddr (← lval a)
    | .indirection => loadLV (← lval e) t
    | .postfixIncr | .postfixDecr =>
      let lv ← lval a
      let ta := Silmaril.Compiler.Native.Types.Registered.typeOf tags a
      if Silmaril.Compiler.Native.Types.addressScalar ta then
        fail "extended native scalar increment requires arithmetic lowering"
      let old ← fresh
      op (.move old (← loadLV lv ta))
      let k ← if ta.isPtr then pointeeSize ta else pure 1
      let delta ← constReg (if uop == .postfixIncr then k else -(k : Int))
      let nw ← match ta with
        | .ptr _ => binop .add old delta
        | .bool => conv (← binop .add old delta) (.int 8 false) .bool
        | .float _ => arithValues .add ta ta (.int 8 true) old delta
        | _ => let (w, s) := ta.intShape; norm (← binop .add old delta) w s
      storeLV lv ta nw
      return old
  | .binary a bop b =>
    match bop with
    | .arithmetic aop => arithValues aop t (Silmaril.Compiler.Native.Types.Registered.typeOf tags a) (Silmaril.Compiler.Native.Types.Registered.typeOf tags b) (← expr a) (← expr b)
    | .comma => do let _ ← expr a; expr b
    | .and | .or => logical bop a b
    | _ =>
      let ta := Silmaril.Compiler.Native.Types.Registered.typeOf tags a
      let tb := Silmaril.Compiler.Native.Types.Registered.typeOf tags b
      if Silmaril.Compiler.Native.Types.addressFormat ta == 1 ||
          Silmaril.Compiler.Native.Types.addressFormat tb == 1 then
        let some ct := Silmaril.Compiler.Native.Types.floatCommon ta tb | fail "bad x87 comparison type"
        let condition ← match bop with
          | .eq => pure Silmaril.Compiler.Native.X87.Comparison.eq
          | .ne => pure .ne | .lt => pure .lt | .le => pure .le
          | .gt => pure .gt | .ge => pure .ge
          | _ => fail "unsupported native x87 comparison"
        return ← x87 (.compare condition) [← exprAs a ct, ← exprAs b ct]
      if Silmaril.Compiler.Native.Types.addressScalar ta || Silmaril.Compiler.Native.Types.addressScalar tb then
        fail "extended native integer comparison requires arithmetic lowering"
      if let some ct@(.float w) := Silmaril.Compiler.Native.Types.floatCommon ta tb then
        floatCmp bop w (← exprAs a ct) (← exprAs b ct)
      else if ta.isPtr || tb.isPtr then
        let some c := relCond bop false | fail "bad comparison"
        binop (.cmp c) (← expr a) (← expr b)
      else
        let (w, s) := usual ta.intShape tb.intShape
        let some c := relCond bop s | fail "bad comparison"
        binop (.cmp c) (← exprAs a (.int w s)) (← exprAs b (.int w s))
  | .assign l r =>
    let lv ← lval l
    let tl := Silmaril.Compiler.Native.Types.Registered.typeOf tags l
    let v ← exprAs r tl
    storeLV lv tl v
    return v
  | .compoundAssign l aop r =>
    let lv ← lval l
    let tl := Silmaril.Compiler.Native.Types.Registered.typeOf tags l
    let tr := Silmaril.Compiler.Native.Types.Registered.typeOf tags r
    -- the right operand first, then the stored value (as gcc does, PR c/58943)
    let v ← expr r
    let old ← loadLV lv tl
    let res ← match tl with
      | .ptr _ => arithValues aop tl tl tr old v
      | _ =>
        if let some ct := Silmaril.Compiler.Native.Types.floatCommon tl tr then
          conv (← arithValues aop ct tl tr old v) ct tl
        else
        let (w, s) := if aop == .shl || aop == .shr then promote tl.intShape
          else usual tl.intShape tr.intShape
        let r' ← arithValues aop (.int w s) tl tr old v
        conv r' (.int w s) tl
    storeLV lv tl res
    return res
  | .cond c a b =>
    let res ← fresh
    let v0 ← expr c
    let ct := Silmaril.Compiler.Native.Types.Registered.typeOf tags c
    let vc ← if Silmaril.Compiler.Native.Types.addressScalar ct then conv v0 ct .bool
      else match ct with
      | .float w => floatTruth v0 w
      | _ => pure v0
    let la ← newLabel
    let lb ← newLabel
    let lend ← newLabel
    finish (.branch vc la lb)
    start la
    let va ← match a with
      | some a => exprAs a t
      | none => conv v0 (Silmaril.Compiler.Native.Types.Registered.typeOf tags c) t
    op (.move res va)
    jumpTo lend
    start lb
    op (.move res (← exprAs b t))
    jumpTo lend
    start lend
    return res
  | .call f args => do
    match ← call f args with
    | some r => return r
    | none => constReg 0
  | .assert a =>
    let v ← test a
    let lok ← newLabel
    let lfail ← newLabel
    finish (.branch v lok lfail)
    start lfail
    let _ ← callFn "abort" [] false
    finish .trap
    start lok
    constReg 0
  | .sizeof _ ty => constReg (← sizeOf ty)
  | .alignof _ ty => constReg (← liftE (Silmaril.Compiler.Native.Layout.sizeAlign (← read).tags ty)).2
  | .sizeofExpr a =>
    match a.annotation with
    | .lvalue _ ty _ => constReg (← sizeOf ty)
    | .rvalue g => match Silmaril.Compiler.Native.Types.Registered.ofGenType tags g with
      | .agg ty => constReg (← sizeOf ty)
      | .ptr _ => constReg 8
      | s => constReg s.intShape.1
  | .offsetof ty m => constReg (← liftE (Silmaril.Compiler.Native.Layout.memberOf (← read).tags ty m)).1
  | .vaStart ap last =>
    let some activation := (← get).nativeVa
      | fail "va_start outside a native variadic function"
    unless activation.lastNamed.map (·.key) == some last.key do
      fail "va_start must name the final named parameter"
    liftE (Silmaril.Compiler.Native.Varargs.checkList tags
      (Silmaril.Compiler.Native.Types.Registered.typeOf tags ap))
    let cell ← expr ap
    storeMem (.int 4 false) cell 0 (← constReg (8 * activation.namedPlan.gpUsed))
    storeMem (.int 4 false) cell 4 (← constReg (48 + 16 * activation.namedPlan.vectorUsed))
    storeMem (.int 8 false) cell 8 (← symAddr "__ccomp_va_overflow")
    storeMem (.int 8 false) cell 16 (← addConst fpReg activation.saveOffset)
    constReg 0
  | .vaArg ap requested =>
    liftE (Silmaril.Compiler.Native.Varargs.checkList tags
      (Silmaril.Compiler.Native.Types.Registered.typeOf tags ap))
    let requested := Silmaril.Compiler.Native.Types.Registered.ofCtype tags requested
    conv (← nativeVaArg (← expr ap) requested) requested t
  | .vaEnd ap =>
    liftE (Silmaril.Compiler.Native.Varargs.checkList tags
      (Silmaril.Compiler.Native.Types.Registered.typeOf tags ap))
    let _ ← expr ap
    constReg 0
  | .vaCopy destination source =>
    liftE (Silmaril.Compiler.Native.Varargs.checkList tags
      (Silmaril.Compiler.Native.Types.Registered.typeOf tags destination))
    liftE (Silmaril.Compiler.Native.Varargs.checkList tags
      (Silmaril.Compiler.Native.Types.Registered.typeOf tags source))
    let destination ← expr destination
    let source ← expr source
    copyBytes destination source Silmaril.Compiler.Native.Varargs.recordBytes
    constReg 0
  | .generic _ (some i) assocs =>
    match assocs.attach[i]? with
    | some association =>
      match _hAssociation : association.val with
      | .type_ _ _ a | .default a => exprAs a t
    | none => fail "_Generic without selection"
  | .compound .. => lvAddr (← lval e)
  | .memberof .. | .memberofptr .. => loadLV (← lval e) t
  | .gccStatement bs ss =>
    -- GNU statement expression: its statements in order, in a block scope of their own;
    -- the value (unless `void`) is that of the final expression statement. Jumping out
    -- (break, continue, goto, return) is allowed; a `case` or `default` inside would
    -- jump in, so it is rejected (`switchCases` does not look into expressions).
    for (x, ((_, dur, _), _, _, ty)) in bs do
      if dur != .static then bindLocal x ty
    let saved := (← get).cases
    modify fun s => { s with cases := [] }
    let r ← match t with
      | .void =>
        for child in ss.attach do stmt child.val
        constReg 0
      | _ =>
        match _lastValue : ss.attach.getLast? with
        | some last =>
          match _lastNode : last.val.node with
          | .expr v =>
            for child in ss.attach.dropLast do stmt child.val
            exprAs v t
          | _ => fail "statement expression without a final expression"
        | none => fail "statement expression without a final expression"
    modify fun s => { s with cases := saved }
    return r
  | _ => fail "unsupported expression"
termination_by (SizeOf.sizeOf e, 1)
decreasing_by native_lowering_decreasing

/-- `&&` and `||`, short-circuit. -/
def logical (bop : BinaryOperator) (a b : TypedExpression) : M Reg := do
  let res ← fresh
  let va ← test a
  let ltest ← newLabel
  let lshort ← newLabel
  let lend ← newLabel
  if bop == .and then finish (.branch va ltest lshort) else finish (.branch va lshort ltest)
  start lshort
  op (.const res (if bop == .and then 0 else 1))
  jumpTo lend
  start ltest
  let vb ← test b
  op (.binary (.cmp .ne) res vb (← constReg 0))
  jumpTo lend
  start lend
  return res
termination_by (SizeOf.sizeOf a + SizeOf.sizeOf b, 3)
decreasing_by native_lowering_decreasing

/-- Snapshot an aggregate value in the caller's frame. The copy happens when its
argument is evaluated, before later arguments can mutate the original object. -/
def aggregateArg (a : TypedExpression) (ty : Ctype) : M Reg := do
  let tags := (← read).tags
  let src ← conv (← expr a) (Silmaril.Compiler.Native.Types.Registered.typeOf tags a)
    (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty)
  let dst ← addConst fpReg (← allocFrame ty)
  copyBytes dst src (← sizeOf ty)
  return dst
termination_by (SizeOf.sizeOf a, 2)
decreasing_by native_lowering_decreasing

/-- A call; its canonical scalar result or caller-owned aggregate address, unless
`void`. Aggregate results use a first hidden destination parameter and no register
result. Value parameters receive snapshots, which the callee copies into its frame;
thus neither mutations through aliases nor later calls change the argument value.
A call of `__ccomp_trap` is `trap`. -/
def call (f : TypedExpression) (args : List TypedExpression) : M (Option Reg) := do
  let tags := (← read).tags
  let direct : Option Sym := match f.node with
    | .functionDecay ⟨_, _, _, .ident g⟩ => some g
    | _ => none
  let fty ← match Silmaril.Compiler.Native.Types.Registered.typeOf tags f with
    | .ptr t => pure t
    | _ => fail "call of a non-function"
  let (ret, params, variadic) ← match fty with
    | .mk _ (.function (_, r) ps v) => pure (Silmaril.Compiler.Native.Types.Registered.ofCtype tags r, ps.map (·.2.1), v)
    | .mk _ (.functionNoParams (_, r)) => pure (Silmaril.Compiler.Native.Types.Registered.ofCtype tags r, [], true)
    | _ => fail "call of a non-function"
  if let some g := direct then
    if (← globalName g) == trapSymbol then
      finish .trap
      deadBlock
      return none
    -- `fabs` and `fabsf` are gcc builtins (clear the sign bit) even where the program
    -- defines them (a reserved identifier: undefined behaviour, STD §7.1.3#2)
    match _builtinArgs : (ret, args) with
    | (.float w, [a]) =>
      if ["fabs", "fabsf"].contains (← globalName g) then
        return some (← binop .and (← exprAs a ret) (← constReg (FloatConst.signBit w - 1)))
    | _ => pure ()
  -- arguments
  let mut fixed : Array Reg := #[]
  let mut argTypes : List CType := []
  for (argument, i) in args.attach.zipIdx do
    let a := argument.val
    match params[i]? with
    | some pty =>
      argTypes := argTypes ++ [Silmaril.Compiler.Native.Types.Registered.ofCtype tags pty]
      match Silmaril.Compiler.Native.Types.Registered.ofCtype tags pty with
      | .agg _ => fixed := fixed.push (← aggregateArg a pty)
      | .unsupported w => fail w
      | t => fixed := fixed.push (← exprAs a t)
    | none =>
      let ta := Silmaril.Compiler.Native.Types.Registered.typeOf tags a
      let v ← match ta with
        | .int .. | .bool => let (w, s) := promote ta.intShape; conv (← expr a) ta (.int w s)
        | .ptr _ => expr a
        | .agg ty => aggregateArg a ty
        | .float _ => exprAs a (.float 8)
        | _ => fail "unsupported variadic argument type"
      let promoted := match ta with
        | .int .. | .bool => let (w, s) := promote ta.intShape; CType.int w s
        | .float _ => CType.float 8
        | t => t
      argTypes := argTypes ++ [promoted]
      fixed := fixed.push v
  let mut argRegs := fixed.toList
  let resultArea ← match ret with
    | .agg ty => some <$> (addConst fpReg (← allocFrame ty))
    | .unsupported w => fail w
    | _ => pure none
  if let some dst := resultArea then argRegs := dst :: argRegs
  let hasRet := match ret with | .void | .agg _ => false | _ => true
  let res ← if hasRet then some <$> fresh else pure none
  let key := s!"__ccomp_call.{(← read).tag}.{(← get).unit.calls.size}"
  let callee ← match direct with
    | some g => globalName g
    | none => pure ""
  let indirectTarget ← match direct with
    | some _ => pure none
    | none => some <$> expr f
  let call : Silmaril.Compiler.Native.CallInfo := {
    key, callee, indirectTarget, arguments := argTypes, result := ret,
    namedCount := params.length, variadic, tags := (← read).tags }
  modify fun s => { s with unit.calls := s.unit.calls.push call }
  -- Include an indirect target among operands so SSA renaming tracks it.
  emit (.call key (indirectTarget.toList ++ argRegs) res.toList)
  return resultArea.or res
termination_by (SizeOf.sizeOf f + SizeOf.sizeOf args, 3)
decreasing_by native_lowering_decreasing

/-- Initialize the object of type `ty` at `base + off` with `init`. -/
def initAt (base : Reg) (off : Nat) (ty : Ctype) (init : TypedExpression) : M Unit := do
  let tags := (← read).tags
  let .mk annotation annotations location node := init
  let init : TypedExpression := .mk annotation annotations location node
  match _atomicNode : node with
  | .atomic a => initAt base off ty a
  | _ => do
    match Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty with
    | .agg _ =>
      match _rootNode : node with
      | .array _ _ elems =>
        let .mk _ (.array et _) := ty | fail "array initializer for a non-array"
        let esize ← sizeOf et
        zeroBytes base off (← sizeOf ty)
        for (element, i) in elems.attach.zipIdx do
          match _elementValue : element.val with
          | some x => initAt base (off + i * esize) et x
          | none => pure ()
      | .struct _ ms =>
        zeroBytes base off (← sizeOf ty)
        for member in ms.attach do
          match _memberValue : member.val with
          | (m, some x) =>
            let (moff, mty) ← liftE (Silmaril.Compiler.Native.Layout.memberOf (← read).tags ty m)
            initAt base (off + moff) mty x
          | (_, none) => pure ()
      | .union _ m el =>
        zeroBytes base off (← sizeOf ty)
        match _unionValue : el with
        | some x =>
          let (moff, mty) ← liftE (Silmaril.Compiler.Native.Layout.memberOf (← read).tags ty m)
          initAt base (off + moff) mty x
        | none => pure ()
      | .const c =>
        let n ← sizeOf ty
        let img ← liftE (gConst (← read).tags (ByteArray.mk (Array.replicate n 0)) 0 ty c)
        let name ← constObject img n
        copyBytes (← addConst base off) (← symAddr name) n
      | .str s =>
        let n ← sizeOf ty
        let bytes := stringBytes s
        zeroBytes base off n
        let z ← fresh
        for i in [0:min n bytes.size] do
          op (.const z (BitVec.ofNat 64 bytes[i]!.toNat))
          op (.store .b1 base (off + i) z)
      | _ =>
        let src ← conv (← expr init) (Silmaril.Compiler.Native.Types.Registered.typeOf tags init)
          (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty)
        copyBytes (← addConst base off) src (← sizeOf ty)
    | t => storeMem t base off (← exprAs init t)
termination_by (SizeOf.sizeOf init, 3)
decreasing_by native_lowering_decreasing

def stmt (s : TypedStatement) : M Unit := do
  let tags := (← read).tags
  let .mk _ _ _ node := s
  let mark := (← get).nextReg
  match _rootNode : node with
  | .skip => pure ()
  | .expr e => let _ ← expr e
  | .block bs ss =>
    for (x, ((_, dur, _), align, _, ty)) in bs do
      if dur != .static then bindLocal x ty align
    for child in ss.attach do stmt child.val
  | .if_ c a b =>
    let v ← test c
    let la ← newLabel
    let lb ← newLabel
    let lend ← newLabel
    finish (.branch v la lb)
    start la; stmt a; jumpTo lend
    start lb; stmt b; jumpTo lend
    start lend
  | .while_ c body _ =>
    let lh ← newLabel
    let lb ← newLabel
    let lx ← newLabel
    jumpTo lh
    start lh
    let v ← test c
    finish (.branch v lb lx)
    start lb
    stmt.loopBody body lx lh
    jumpTo lh
    start lx
  | .do_ body c _ =>
    let lb ← newLabel
    let lc ← newLabel
    let lx ← newLabel
    jumpTo lb
    start lb
    stmt.loopBody body lx lc
    jumpTo lc
    start lc
    let v ← test c
    finish (.branch v lb lx)
    start lx
  | .break_ =>
    let some l := (← get).breakL | fail "break outside a loop"
    jumpTo l; deadBlock
  | .continue_ =>
    let some l := (← get).contL | fail "continue outside a loop"
    jumpTo l; deadBlock
  | .returnVoid => epilogue; finish (.ret []); deadBlock
  | .return_ e =>
    let v ← exprAs e (← get).retType
    match (← get).retType with
    | .agg ty =>
      let some dst := (← get).retArea | fail "missing aggregate result destination"
      copyBytes dst v (← sizeOf ty)
      epilogue
      finish (.ret [])
    | _ =>
      epilogue
      finish (.ret [.reg v])
    deadBlock
  | .switch e body =>
    let te := Silmaril.Compiler.Native.Types.Registered.typeOf tags e
    let (w, sg) := promote te.intShape
    let v ← exprAs e (.int w sg)
    let cases := switchCases body #[]
    let mut labels : Array Nat := #[]
    for _ in cases do labels := labels.push (← newLabel)
    let lx ← newLabel
    let mut dflt := lx
    for (c, l) in cases.zip labels do
      match c with
      | none => dflt := l
      | some (lo, hi) =>
        let next ← newLabel
        if lo == hi then
          let k ← norm (← constReg lo) w sg
          finish (.branch (← binop (.cmp .eq) v k) l next)
        else
          let klo ← norm (← constReg lo) w sg
          let khi ← norm (← constReg hi) w sg
          let a ← binop (.cmp (if sg then .ges else .geu)) v klo
          let b ← binop (.cmp (if sg then .les else .leu)) v khi
          finish (.branch (← binop .and a b) l next)
        start next
    jumpTo dflt
    deadBlock
    let saved ← get
    modify fun s => { s with breakL := some lx, cases := labels.toList }
    stmt body
    jumpTo lx
    modify fun s => { s with breakL := saved.breakL, cases := saved.cases }
    start lx
  | .case_ _ b | .caseRangeGnu _ _ b | .default b =>
    let l ← match (← get).cases with
      | l :: rest => modify (fun s => { s with cases := rest }); pure l
      | [] => fail "case outside a switch"
    jumpTo l; start l
    stmt b
  | .label x b _ =>
    let l ← labelOf x
    jumpTo l; start l
    stmt b
  | .goto x => jumpTo (← labelOf x); deadBlock
  | .declaration ds =>
    for declaration in ds.attach do
      match _declarationValue : declaration.val with
      | (x, some e) =>
        match (← get).homes[x.number]? with
        | some (.reg r, ty) => op (.move r (← exprAs e (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty)))
        | some (.mem off, ty) => initAt fpReg off ty e
        | none => pure ()   -- a static local: initialized as a global
      | (_, none) => pure ()
  | .marker _ b => stmt b
  | _ => fail "unsupported statement"
  modify fun st => { st with nextReg := max mark (if st.nextReg > mark then mark else st.nextReg) }
termination_by (SizeOf.sizeOf s, 0)
decreasing_by native_lowering_decreasing

def stmt.loopBody (body : TypedStatement) (lbreak lcont : Nat) : M Unit := do
  let saved ← get
  modify fun s => { s with breakL := some lbreak, contL := some lcont }
  stmt body
  modify fun s => { s with breakL := saved.breakL, contL := saved.contL }
termination_by (SizeOf.sizeOf body, 1)
decreasing_by native_lowering_decreasing

end

/-! ## Functions -/

/-- Lower a body while retaining logical C parameters and typed ABI metadata.
Aggregates use internal addresses until native ABI emission. The object frame
is a machine-stack region, not the frozen compiler's software stack. -/
def compileFunc (name : Symbol) (info : FuncInfo) (fd : FunctionDefinition GenTypeCategory)
    (unit : UState) (exported : Bool) : ReaderT Ctx (Except String) (Mir.Func × UState) := do
  let tags := (← read).tags
  let ctx ← read
  let hidden := match info.ret with | .agg _ => 1 | _ => 0
  let paramCount := hidden + info.params.length
  let body : M Unit := do
    modify fun s => { s with retType := info.ret, addrTaken := addrTakenS fd.body {} }
    if info.variadic then
      let plan ← liftE (Silmaril.Compiler.Native.Abi.Planning.functionPlan {
        name, signature := info, tags, frameBytes := 0, frameAlign := 16 })
      let saveOffset ← allocBytes Silmaril.Compiler.Native.Varargs.saveBytes 16
      modify fun s => { s with nativeVa := some {
        saveOffset, namedPlan := plan, lastNamed := fd.params.getLast? } }
    let prologue ← newLabel
    let entry ← newLabel
    -- parameters
    if let .agg _ := info.ret then
      let r ← fresh
      modify fun s => { s with retArea := some r }
    for (x, ty) in fd.params.zip info.params do
      let r ← fresh
      match Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty with
      | .unsupported w => fail w
      | _ => pure ()
      if (Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty).isScalar && !(← get).addrTaken.contains x.number then
        modify fun s => { s with homes := s.homes.insert x.number (.reg r, ty) }
      else
        let off ← allocFrame ty
        modify fun s => { s with homes := s.homes.insert x.number (.mem off, ty),
                                 paramStores := s.paramStores ++ [(r, off, Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty)] }
    start entry
    stmt fd.body
    -- falling off the end
    epilogue
    match info.ret with
    | .void | .agg _ => finish (.ret [])
    | _ => finish (.ret [.reg (← constReg 0)])
    -- the prologue: allocate the frame, store address-taken parameters
    start prologue
    -- The native backend allocates the object frame on the machine stack.
    emit (.addr fpReg "__ccomp_frame" 0)
    for (r, off, t) in (← get).paramStores do
      match t with
      | .agg ty => copyBytes (← addConst fpReg off) r (← sizeOf ty)
      | _ => storeMem t fpReg off r
    jumpTo entry
    return ()
  match (body.run ctx).run { unit } with
  | .error e => throw s!"{name}: {e}"
  | .ok ((), s) =>
    let blocks := s.blocks.map fun b => b.getD ⟨#[], .trap⟩
    let logicalParams := (List.range paramCount).map (· + 2)
    let params := logicalParams
    let ust := { s.unit with functions := s.unit.functions.push {
      name, signature := info, tags := ctx.tags,
      frameBytes := s.frame, frameAlign := s.frameAlign,
      vaSaveOffset := s.nativeVa.map (·.saveOffset) } }
    let _ := ctx
    return ({ name, params, results := (match info.ret with | .void | .agg _ => 0 | _ => 1),
              blocks, exported }, ust)

/-! ## Global initializers -/

/-- A compile-time scalar: an integer, or a symbol's address plus an offset. -/
inductive CVal where
  | int (v : Int)
  | addr (sym : Symbol) (off : Int)

/-- Add a byte offset while retaining the link-time symbol. -/
def CVal.addOffset : CVal → Int → CVal
  | .int v, off => .int (v + off)
  | .addr s o, off => .addr s (o + off)

/-- Truth of an unresolved address is known only for pointer values. Arithmetic
on an integer converted from an address may produce zero after linking. -/
def CVal.truth (ty : CType) : CVal → Except String Bool
  | .int v => match ty with
    | .float w => .ok (v % (FloatConst.signBit w : Int) != 0)
    | _ => .ok (v != 0)
  | .addr .. => if ty.isPtr then .ok true
    else .error "truth of a symbolic integer address is unsupported"

abbrev G := ReaderT Ctx (StateT UState (Except String))

def gStringObject (lit : StringLiteral) : G Symbol := do
  let s ← get
  let name := s!".str.{(← read).tag}.{s.count}"
  let bytes := stringBytes lit
  set ({ data := s.data.push { name, size := bytes.size, align := unitWidth lit.1, init := bytes,
                               exported := false, readonly := true }, count := s.count + 1 } : UState)
  return name

def gName (x : Sym) : G Symbol := do
  return ((← read).names[x.number]?).getD (symName x)

scoped macro "native_global_decreasing" : tactic => do
  let e := Lean.mkIdent `e
  let t := Lean.mkIdent `t
  let valueType := Lean.mkIdent `_valueType
  let floatType := Lean.mkIdent `_floatType
  let operands := Lean.mkIdent `_operands
  let element := Lean.mkIdent `element
  let member := Lean.mkIdent `member
  `(tactic| (
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp only [$e:ident, $t:ident] at $valueType:ident
    all_goals try simp only [$e:ident] at $floatType:ident
    all_goals try rw [Prod.lex_def]
    all_goals try have _elementSize := List.sizeOf_lt_of_mem ($element).property
    all_goals try have _memberSize := List.sizeOf_lt_of_mem ($member).property
    all_goals try simp_all
    all_goals first
      | omega
      | (split at $operands:ident <;> simp_all <;> omega)
      | (split <;> simp_all <;> omega)
  ))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
mutual

/-- The address designated by a constant lvalue expression: a symbol plus a byte
offset, or an integer when the lvalue is reached through a pointer converted from
an integer (`&((char*)0)[n]`, `&((T*)0)->m`). Such an address is only computed,
never dereferenced, so it stays an integer without provenance. -/
def gAddrWithTags (tags : Tags) (e : TypedExpression) : G CVal := do
  let .mk _ _ _ node := e
  let member (ty : Ctype) (m : Identifier) : G Int := do
    match Silmaril.Compiler.Native.Layout.memberOf (← read).tags ty m with
    | .ok (off, _) => return off
    | .error err => throw err
  match _expressionNode : node with
  | .ident x => return .addr (← gName x) 0
  | .str s => return .addr (← gStringObject s) 0
  | .memberof a m =>
    let .lvalue _ ty _ := a.annotation | throw "member of a non-lvalue"
    return (← gAddrWithTags tags a).addOffset (← member ty m)
  | .memberofptr p m =>
    let .ptr ty := Silmaril.Compiler.Native.Types.Registered.typeOf tags p | throw "-> on a non-pointer"
    return (← gValWithTags tags p).addOffset (← member ty m)
  | .unary .indirection p => gValWithTags tags p
  | .arrayDecay a | .annot _ a => gAddrWithTags tags a
  | _ => throw "unsupported constant address"
termination_by (SizeOf.sizeOf e, 0)
decreasing_by native_global_decreasing

/-- The compile-time value of a scalar initializer. Logical operators evaluate
only the needed operand. Intended preservation: scalar values have their C
initialization value; pointer arithmetic retains a symbol and a byte addend until
linking, and address conversions not representable by an 8-byte relocation reject. -/
def gValWithTags (tags : Tags) (e : TypedExpression) : G CVal := do
  let .mk annotation annotations location node := e
  let e : TypedExpression := .mk annotation annotations location node
  let t := Silmaril.Compiler.Native.Types.Registered.typeOf tags e
  let normV (v : Int) : CVal := match t with
    | .int w s =>
      let m : Int := 2 ^ (8 * w)
      let u := v % m
      .int (if s && u ≥ m / 2 then u - m else u)
    | .bool => .int (if v == 0 then 0 else 1)
    | _ => .int v
  match _valueType : t with
  | .float w => return .int (← gFloatWithTags tags e w)
  | _ => do
    match _expressionNode : node with
    | .const (.integer ic) =>
        match Silmaril.Compiler.Native.Types.Registered.integerConstantValue tags ic with
        | .ok value => return normV value
        | .error why => throw why
    | .const (.character c) => return normV (charValue c)
    | .const .null => return .int 0
    | .cast _ _ a | .annot _ a | .atomic a =>
      if let .float v := Silmaril.Compiler.Native.Types.Registered.typeOf tags a then
        let x ← gFloatWithTags tags a v
        if t matches .bool then return .int (if x % FloatConst.signBit v == 0 then 0 else 1)
        match FloatConst.toInt? v x with
        | some n => return normV n
        | none => throw "constant conversion of a non-finite value"
      match ← gValWithTags tags a with
      | .int v => return normV v
      | x@(.addr ..) => match t with
        | .bool =>
          match x.truth (Silmaril.Compiler.Native.Types.Registered.typeOf tags a) with
          | .ok b => return .int (if b then 1 else 0)
          | .error err => throw err
        | .int w _ =>
          if w < 8 then throw "narrowing a constant address is unsupported"
          return x
        | .ptr _ => return x
        | _ => throw "cast of a constant address to an unsupported type"
    | .unary .plus a => gValWithTags tags a
    | .unary .minus a => match ← gValWithTags tags a with
      | .int v => return normV (-v)
      | _ => throw "negated address"
    | .unary .bnot a => match ← gValWithTags tags a with
      | .int v => return normV (-v - 1)
      | _ => throw "complemented address"
    | .binary a bop@(.and) b | .binary a bop@(.or) b =>
      let av ← gTruthWithTags tags a
      if bop == .and && !av then return .int 0
      if bop == .or && av then return .int 1
      return .int (if ← gTruthWithTags tags b then 1 else 0)
    -- `&*p` is `p`, also for a numeric pointer such as `&((char*)0)[X]` (gAddrWithTags tags).
    | .unary .address a | .arrayDecay a => gAddrWithTags tags a
    | .functionDecay ⟨_, _, _, .ident f⟩ => return .addr (← gName f) 0
    | .str s => return .addr (← gStringObject s) 0
    | .binary a (.arithmetic aop) b =>
      let scale (ty : CType) : G Int := do
        match ty with
        | .ptr pt => match Silmaril.Compiler.Native.Layout.sizeAlign (← read).tags pt with
          | .ok (n, _) => return n
          | .error err => throw err
        | _ => return 1
      -- C permits both p + i and i + p. Numeric pointer constants need the same
      -- element-size scaling as symbolic addresses.
      if t.isPtr then
        match _operands : if (Silmaril.Compiler.Native.Types.Registered.typeOf tags a).isPtr then (a, b) else (b, a) with
        | (p, i) => do
          if aop != .add && !(aop == .sub && (Silmaril.Compiler.Native.Types.Registered.typeOf tags a).isPtr) then
            throw "unsupported constant pointer arithmetic"
          let .int n ← gValWithTags tags i | throw "non-integer constant pointer offset"
          let base ← gValWithTags tags p
          let k ← scale (Silmaril.Compiler.Native.Types.Registered.typeOf tags p)
          return base.addOffset (if aop == .sub then -n * k else n * k)
      if (Silmaril.Compiler.Native.Types.Registered.typeOf tags a).isPtr && (Silmaril.Compiler.Native.Types.Registered.typeOf tags b).isPtr then
        -- pointer difference: elements, not bytes, within one object
        if aop != .sub then throw "unsupported constant pointer arithmetic"
        let k ← scale (Silmaril.Compiler.Native.Types.Registered.typeOf tags a)
        if k == 0 then throw "constant difference of pointers to a zero-size type"
        let d ← match ← gValWithTags tags a, ← gValWithTags tags b with
          | .int x, .int y => pure (x % 2 ^ 64 - y % 2 ^ 64)
          | .addr p x, .addr q y =>
            if p != q then throw "constant difference of addresses of distinct objects"
            pure (x - y)
          | _, _ => throw "unsupported constant pointer difference"
        if d % k != 0 then throw "constant pointer difference not a multiple of the element size"
        return normV (d / k)
      match ← gValWithTags tags a, ← gValWithTags tags b with
      | .int x, .int y =>
        let (w, signed) := t.intShape
        let canon (v : Int) : Int :=
          let u := v % (2 ^ (8 * w) : Int)
          if signed && u ≥ 2 ^ (8 * w - 1) then u - 2 ^ (8 * w) else u
        let x := canon x
        let y := if aop == .shl || aop == .shr then y else canon y
        if (aop == .div || aop == .mod) && y == 0 then
          throw "division by zero in constant initializer"
        if (aop == .shl || aop == .shr) && (y < 0 || y ≥ 8 * w) then
          throw "invalid shift in constant initializer"
        let bx := BitVec.ofInt 64 x
        let bitsB := BitVec.ofInt 64 y
        let r : Int := match aop with
          | .add => x + y | .sub => x - y | .mul => x * y
          | .div => x.tdiv y | .mod => x.tmod y
          | .shl => x * 2 ^ y.toNat | .shr => x / 2 ^ y.toNat
          | .band => (bx &&& bitsB).toNat | .bor => (bx ||| bitsB).toNat
          | .bxor => (bx ^^^ bitsB).toNat
        return normV r
      | .addr s o, .int y =>
        if aop != .add && aop != .sub then throw "unsupported arithmetic on a constant address"
        let k ← scale (Silmaril.Compiler.Native.Types.Registered.typeOf tags a)
        return .addr s (if aop == .sub then o - y * k else o + y * k)
      | _, _ => throw "unsupported constant arithmetic"
    | .sizeof _ ty => match Silmaril.Compiler.Native.Layout.sizeAlign (← read).tags ty with
      | .ok (n, _) => return .int n
      | .error err => throw err
    | .invalid _ why => throw s!"invalid constant initializer: {repr why}"
    | _ => throw "unsupported constant initializer"
termination_by (SizeOf.sizeOf e, match Silmaril.Compiler.Native.Types.Registered.typeOf tags e with | .float _ => 1 | _ => 0)
decreasing_by native_global_decreasing

/-- The compile-time encoding, in format `w`, of a constant arithmetic expression. -/
def gFloatWithTags (tags : Tags) (e : TypedExpression) (w : Nat) : G Nat := do
  let .mk annotation annotations location node := e
  let e : TypedExpression := .mk annotation annotations location node
  match _floatType : Silmaril.Compiler.Native.Types.Registered.typeOf tags e with
  | .unsupported why => throw why
  | .float v =>
    let x ← match _expressionNode : node with
      | .const (.floating (text, _)) => match FloatConst.parse v text with
        | some b => pure b
        | none => throw s!"bad floating constant {text}"
      | .cast _ _ a | .annot _ a | .atomic a | .unary .plus a => gFloatWithTags tags a v
      | .unary .minus a => pure ((← gFloatWithTags tags a v) ^^^ FloatConst.signBit v)
      | .binary a (.arithmetic aop) b =>
        match FloatConst.binary v aop (← gFloatWithTags tags a v) (← gFloatWithTags tags b v) with
        | some r => pure r
        | none => throw "unsupported constant arithmetic"
      | _ => throw "unsupported constant initializer"
    return FloatConst.convert v w x
  | .int .. | .bool | .ptr _ | .agg _ | .void | .func _ =>
    match ← gValWithTags tags e with
    | .int n => return FloatConst.ofInt w n
    | .addr .. => throw "address converted to a floating type"
termination_by (SizeOf.sizeOf e, match Silmaril.Compiler.Native.Types.Registered.typeOf tags e with | .float _ => 0 | _ => 1)
decreasing_by native_global_decreasing

def gTruthWithTags (tags : Tags) (x : TypedExpression) : G Bool := do
  match (← gValWithTags tags x).truth (Silmaril.Compiler.Native.Types.Registered.typeOf tags x) with
  | .ok b => return b
  | .error err => throw err
termination_by (SizeOf.sizeOf x, 2)
decreasing_by native_global_decreasing

end

/-- Evaluate with the exact implementation registry retained by this unit. -/
def gAddr (e : TypedExpression) : G CVal := do
  gAddrWithTags (← read).tags e

def gVal (e : TypedExpression) : G CVal := do
  gValWithTags (← read).tags e

def gFloat (e : TypedExpression) (w : Nat) : G Nat := do
  gFloatWithTags (← read).tags e w

def gVal.truth (e : TypedExpression) : G Bool := do
  gTruthWithTags (← read).tags e

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Write `init` for an object of type `ty` at `off` into an image, converting scalar
initializers to the destination type (Ail may retain the expression's original
type). Intended theorem: the bytes encode the value after C's initialization
conversion, including rounding when a `double` initializes a `float`. -/
def gInit (img : ByteArray) (relocs : Array Mir.Reloc) (off : Nat) (ty : Ctype)
    (init : TypedExpression) : G (ByteArray × Array Mir.Reloc) := do
  let .mk annotation annotations location node := init
  let init : TypedExpression := .mk annotation annotations location node
  match _atomicNode : node with
  | .atomic a => gInit img relocs off ty a
  | _ => do
    let tags := (← read).tags
    let lay (t : Ctype) : G (Nat × Nat) := match Silmaril.Compiler.Native.Layout.sizeAlign tags t with
      | .ok x => pure x
      | .error err => throw err
    match Silmaril.Compiler.Native.Types.Registered.ofCtype tags ty with
    | .agg _ =>
      match _initializerNode : node with
      | .invalid _ why => throw s!"invalid aggregate initializer: {repr why}"
      | .array _ _ elems =>
        let .mk _ (.array et _) := ty | throw "array initializer for a non-array"
        let (esize, _) ← lay et
        let mut st := (img, relocs)
        for (element, i) in elems.attach.zipIdx do
          match _elementValue : element.val with
          | some x => st ← gInit st.1 st.2 (off + i * esize) et x
          | none => pure ()
        return st
      | .struct _ ms =>
        let mut st := (img, relocs)
        for member in ms.attach do
          match _memberValue : member.val with
          | (m, some x) =>
            let (moff, mty) ← match Silmaril.Compiler.Native.Layout.memberOf tags ty m with
              | .ok x => pure x
              | .error err => throw err
            st ← gInit st.1 st.2 (off + moff) mty x
          | (_, none) => pure ()
        return st
      | .union _ m (some x) =>
        let (moff, mty) ← match Silmaril.Compiler.Native.Layout.memberOf tags ty m with
          | .ok x => pure x
          | .error err => throw err
        gInit img relocs (off + moff) mty x
      | .union _ _ none => return (img, relocs)
      | .const c => match gConst tags img off ty c with
        | .ok img => return (img, relocs)
        | .error err => throw err
      | .str s =>
        let (n, _) ← lay ty
        let bytes := stringBytes s
        let mut img := img
        for i in [0:min n bytes.size] do img := img.set! (off + i) bytes[i]!
        return (img, relocs)
      | _ => throw "unsupported aggregate initializer"
    | .unsupported why => throw why
    | .float w =>
      return (Mir.writeLE img off w (← gFloat init w), relocs)
    | t =>
      let (w, _) := t.intShape
      let v : CVal ← match Silmaril.Compiler.Native.Types.Registered.typeOf tags init with
        | .float fw =>
          let bits ← gFloat init fw
          if t matches .bool then
            pure (.int (if bits % FloatConst.signBit fw == 0 then 0 else 1))
          else
            match FloatConst.toInt? fw bits with
            | some n => pure (.int n)
            | none => throw "constant conversion of a non-finite value"
        | .unsupported why => throw why
        | _ => gVal init
      match v with
      | .int v => return (Mir.writeLE img off w (integerInitBits t v), relocs)
      | .addr s o =>
        if t matches .bool then
          match (CVal.addr s o).truth (Silmaril.Compiler.Native.Types.Registered.typeOf tags init) with
          | .ok b => return (Mir.writeLE img off 1 (if b then 1 else 0), relocs)
          | .error err => throw err
        if w != 8 then throw "narrowing a constant address is unsupported"
        return (img, relocs.push { offset := off, sym := s, addend := o })
termination_by SizeOf.sizeOf init
decreasing_by native_global_decreasing

/-! ## Units -/

/-- A definition kept in typed Ail until its link symbol is needed. -/
inductive PendingDefinition where
  | object (ty : Ctype) (align : Option Alignment) (readonly exported : Bool)
      (init : Option TypedExpression)
  | function (sym : Sym) (body : FunctionDefinition GenTypeCategory) (exported : Bool)

/-- The context and definitions of a translation unit, before lowering any body or
initializer. Merely declaring an unsupported type must not reject a whole link. -/
structure PreparedUnit where
  ctx : Ctx
  definitions : Array (Symbol × PendingDefinition)

/-- The type of an object's definition. A block-scope `extern T a[];` that redeclares a
file-scope array leaves the incomplete type as the symbol's declaration, while the
composite type (STD §6.2.7#4) stays visible at file scope and on the initializer. -/
def completeArray (ty : Ctype) (init : Option TypedExpression) : Ctype :=
  match ty, init with
  | .mk as (.array t none), some ⟨.rvalue (.array _ (some n)), _, _, _⟩ => .mk as (.array t (some n))
  | _, _ => ty

/-- Index declarations without evaluating initializers or lowering bodies. All names
and function signatures remain available, including forward and external references. -/
def prepareUnit (tag : String) (prog : TypedProgram) (opts : LowerOptions := {})
    (enumBindings : List (Sym × IntegerType) := []) :
    Except String PreparedUnit := do
  let σ := prog.2
  let tags ← Silmaril.Compiler.Native.Layout.tagsOf σ
  let tags := { tags with enums := Map.ofList enumBindings }
  let external : Std.HashSet Nat :=
    σ.externIdmap.foldl (fun s (_, (x, _)) => s.insert x.number) {}
  let defined : Std.HashMap Nat IdKind :=
    σ.externIdmap.foldl (fun s (_, (x, k)) => s.insert x.number k) {}
  let inits : Std.HashMap Nat TypedExpression :=
    σ.objectDefinitions.foldl (fun m (x, e) => m.insert x.number e) {}
  let bodies : Std.HashSet Nat :=
    σ.functionDefinitions.foldl (fun s (x, _) => s.insert x.number) {}
  -- A block-scope `extern` object or function that no file-scope declaration names has
  -- external linkage (STD §6.2.2#4) and is no definition. Cerberus records it only in
  -- `declarations`: not in `externIdmap` (file scope only), and not in
  -- `objectDefinitions`, where every static object, file-scope or local, has its
  -- initializer (an undefined function of internal linkage cannot be used, §6.9#3).
  let blockExtern : Std.HashSet Nat := σ.declarations.foldl (fun s (x, (_, _, d)) =>
    if external.contains x.number then s else
    match d with
    | .object (.static, _) .. => if inits.contains x.number then s else s.insert x.number
    | .function .. => if bodies.contains x.number then s else s.insert x.number
    | _ => s) {}
  let mut names : Std.HashMap Nat Symbol := {}
  let mut funcs : Std.HashMap Nat FuncInfo := {}
  for (x, (_, _, d)) in σ.declarations do
    let n := if external.contains x.number || blockExtern.contains x.number then symName x
      else s!"{symName x}.{tag}.{x.number}"
    names := names.insert x.number n
    if let .function hasProto (_, ret) ps v _ _ := d then
      funcs := funcs.insert x.number ⟨Silmaril.Compiler.Native.Types.Registered.ofCtype tags ret, ps.map (·.2.1), v, hasProto⟩
  let ctx : Ctx := { tags, tag, names, funcs, opts }
  let mut definitions := #[]
  for (x, (_, _, d)) in σ.declarations do
    if let .object (dur, _) align q ty := d then
      if dur == .automatic || blockExtern.contains x.number then continue
      let isDef := inits.contains x.number || !external.contains x.number ||
        defined[x.number]? != some .declaration
      if isDef then
        definitions := definitions.push (names[x.number]!,
          .object (completeArray ty inits[x.number]?) align q.const (external.contains x.number)
            inits[x.number]?)
  for (x, fd) in σ.functionDefinitions do
    definitions := definitions.push ((names[x.number]?).getD (symName x),
      .function x fd (external.contains x.number))
  return { ctx, definitions }

/-- Lower one demanded definition with the ordinary C lowering. Strings share the
unit's counter, so incrementally lowered definitions cannot alias string symbols.
The intended refinement is exactly that of `compileUnit`, restricted to this symbol. -/
def compileDefinition (ctx : Ctx) (name : Symbol) (d : PendingDefinition)
    (ust : UState) : Except String (Mir.Unit × UState) := do
  match d with
  | .object ty align readonly exported init =>
    let (size, align) ← (Silmaril.Compiler.Native.Layout.objectLayout ctx.tags ty align).mapError (fun e => s!"{name}: {e}")
    let img := ByteArray.mk (Array.replicate size 0)
    let ((img, relocs), ust) ← match init with
      | none => pure ((img, #[]), ust)
      | some e => (((gInit img #[] 0 ty e).run ctx).run ust).mapError (fun e => s!"{name}: {e}")
    return ({ data := #[{ name, size, align, init := img, relocs := relocs.toList,
                          exported, readonly }] }, ust)
  | .function x fd exported =>
    let some info := ctx.funcs[x.number]? | throw s!"no declaration for {name}"
    let (f, ust) ← (compileFunc name info fd ust exported).run ctx
    return ({ funcs := #[f] }, ust)

/-- Lower every definition of a typed-Ail unit. This remains the strict separate
compilation check: an object may subsequently be linked with any external roots. -/
def compileUnit (tag : String) (prog : TypedProgram) (opts : LowerOptions := {})
    (enumBindings : List (Sym × IntegerType) := []) :
    Except String Mir.Unit := do
  let p ← prepareUnit tag prog opts enumBindings
  let mut ust : UState := {}
  let mut unit : Mir.Unit := {}
  for (name, d) in p.definitions do
    let (piece, next) ← compileDefinition p.ctx name d ust
    unit := unit.append piece
    ust := next
  return { unit with data := unit.data ++ ust.data }

/-- Native separate compilation includes the ABI and object-frame metadata. -/
def compile (tag : String) (prog : TypedProgram) (opts : LowerOptions := {})
    (enumBindings : List (Sym × IntegerType) := []) :
    Except String Silmaril.Compiler.Native.Artifact := do
  let p ← prepareUnit tag prog opts enumBindings
  let mut ust : UState := {}
  let mut unit : Mir.Unit := {}
  for (name, d) in p.definitions do
    let (piece, next) ← compileDefinition p.ctx name d ust
    unit := unit.append piece
    ust := next
  let mir := { unit with data := unit.data ++ ust.data }
  return { mir, functions := ust.functions, calls := ust.calls, intrinsics := ust.intrinsics }

end Silmaril.Compiler.Native.Lower
