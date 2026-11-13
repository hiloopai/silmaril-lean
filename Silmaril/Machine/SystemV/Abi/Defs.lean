module

public import Silmaril.Machine.X86.CallingConvention.Defs
public import Silmaril.Cerberus.NativeTypes.Defs

/-! AMD64 LP64 classification and call planning, specified against
x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236,
low-level-sys-info.tex, Parameter Passing and Variable Argument Lists.
This is executable ABI data; it is not a native code-generation theorem.
-/

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi

open Silmaril.Cerberus.NativeTypes (Floating Scalar)
open Silmaril.X86 (Reg)

inductive Class where
  | noClass | integer | sse | sseUp | x87 | x87Up | complexX87 | memory
  deriving DecidableEq, BEq, Repr

/-- A complete native object layout together with its cleaned eightbyte classes.
`[memory]` denotes indirect/stack classification, not one byte of storage. -/
structure Object where
  size : Nat
  align : Nat
  classes : List Class
  deriving DecidableEq, Repr

inductive VectorLevel where
  | sse | avx | avx512
  deriving DecidableEq, Repr

structure Profile where
  vectors : VectorLevel := .sse
  deriving DecidableEq, Repr

def Profile.vectorBytes (profile : Profile) : Nat :=
  match profile.vectors with | .sse => 16 | .avx => 32 | .avx512 => 64

def eightbytes (size : Nat) : Nat := (size + 7) / 8

def alignUp (offset alignment : Nat) : Nat :=
  if alignment = 0 then offset else ((offset + alignment - 1) / alignment) * alignment

def validAlignment (alignment : Nat) : Bool :=
  alignment != 0 && (alignment &&& (alignment - 1)) == 0

/-- §3.2.3 field-class merge, in the specification's priority order. -/
def merge (first second : Class) : Class :=
  if first == second then first
  else if first == .noClass then second
  else if second == .noClass then first
  else if first == .memory || second == .memory then .memory
  else if first == .integer || second == .integer then .integer
  else if first == .x87 || first == .x87Up || first == .complexX87 ||
      second == .x87 || second == .x87Up || second == .complexX87 then .memory
  else .sse

def x87Pairs : Class → List Class → Bool
  | _, [] => true
  | previous, current :: rest =>
      (current != .x87Up || previous == .x87) && x87Pairs current rest

def repairSseUp : Class → List Class → List Class
  | _, [] => []
  | previous, current :: rest =>
      let current := if current == .sseUp && previous != .sse && previous != .sseUp
        then .sse else current
      current :: repairSseUp current rest

/-- Aggregate post-merge cleanup. Complex long double is a scalar exception and
is constructed separately, rather than sent through this aggregate cleanup. -/
def cleanup (size : Nat) (classes : List Class) : List Class :=
  if size > 64 || classes.contains .memory || !x87Pairs .noClass classes then [.memory]
  else if size > 16 && !(classes.head? == some .sse && (classes.drop 1).all (· == .sseUp))
    then [.memory]
  else repairSseUp .noClass classes

namespace Object

def memory (size align : Nat) : Object := ⟨size, align, [.memory]⟩
def pointer : Object := ⟨8, 8, [.integer]⟩

def integer (bytes : Nat) (alignment : Nat := bytes) : Object :=
  ⟨bytes, alignment, cleanup bytes (List.replicate (eightbytes bytes) .integer)⟩

def floating (format : Floating) : Object :=
  let layout := format.layout
  ⟨layout.size, layout.align, match format with
    | .x87 => [.x87, .x87Up]
    | .binary128 | .decimal128 => [.sse, .sseUp]
    | _ => [.sse]⟩

def vector (bytes : Nat) : Except String Object :=
  if bytes == 8 || bytes == 16 || bytes == 32 || bytes == 64 then
    .ok ⟨bytes, bytes, .sse :: List.replicate (eightbytes bytes - 1) .sseUp⟩
  else .error "native vector size must be 8, 16, 32 or 64 bytes"

def scalar (type : Scalar) : Except String Object := do
  let layout ← type.layout
  match type with
  | .floating format => return floating format
  | _ => return integer layout.size layout.align

/-- Ordinary object layouts need a nonzero power-of-two alignment and exactly
one class per eightbyte. The MEMORY and complex-x87 scalar forms are exceptions.
-/
def valid (object : Object) : Bool :=
  validAlignment object.align && object.size % object.align == 0 &&
    (object.classes == [.memory] ||
      (object.classes == [.complexX87] && object.size == 32 && object.align == 16) ||
      (object.classes.length == eightbytes object.size &&
        cleanup object.size object.classes == object.classes))

end Object

/-- Field offsets are in bits, so bit-fields can occupy partial eightbytes.
`bitWidth = some 0` is a zero-width field and contributes NO_CLASS. The layout
provider must separately validate language-specific placement and overlap. -/
structure Field where
  offsetBits : Nat
  object : Object
  bitWidth : Option Nat := none
  deriving DecidableEq, Repr

def fieldUnaligned (field : Field) : Bool :=
  match field.bitWidth with
  | some _ => false
  | none => field.object.align == 0 || field.offsetBits % (8 * field.object.align) != 0

def fieldClassAt (field : Field) (slot : Nat) : Class :=
  match field.bitWidth with
  | some 0 => .noClass
  | some width =>
      if field.offsetBits < (slot + 1) * 64 && slot * 64 < field.offsetBits + width
      then .integer else .noClass
  | none =>
      (field.object.classes.zipIdx).foldl (fun result (cls, index) =>
        let lo := field.offsetBits + index * 64
        let hi := min (field.offsetBits + field.object.size * 8) (lo + 64)
        if lo < (slot + 1) * 64 && slot * 64 < hi then merge result cls else result) .noClass

/-- Classify a layout-resolved aggregate or union. Union fields have the same
zero offset; ordinary struct/array fields retain their native offsets. -/
def aggregate (size alignment : Nat) (fields : List Field) : Object :=
  if size > 64 || fields.any fieldUnaligned || fields.any (fun field => field.bitWidth.isNone && field.object.classes.contains .memory) then
    .memory size alignment
  else
    let classes := (List.range (eightbytes size)).map fun slot =>
      fields.foldl (fun result field => merge result (fieldClassAt field slot)) .noClass
    ⟨size, alignment, cleanup size classes⟩

/-- Complex values are two components; only complex x87 has a special return
class. A complex binary128 is a 32-byte aggregate and is MEMORY classified. -/
def complex (format : Floating) : Object :=
  if format == .x87 then ⟨32, 16, [.complexX87]⟩
  else
    let component := Object.floating format
    aggregate (2 * component.size) component.align
      [⟨0, component, none⟩, ⟨8 * component.size, component, none⟩]

inductive Location where
  | gp (register : Reg)
  | vector (index byteOffset : Nat)
  | x87 (index : Nat)
  deriving DecidableEq, Repr

structure Chunk where
  offset : Nat
  bytes : Nat
  location : Location
  deriving DecidableEq, Repr

structure Argument where
  object : Object
  chunks : List Chunk
  /-- Byte offset from caller RSP immediately BEFORE CALL. At callee entry,
  this is `[rsp + 8 + stackOffset]`, after the pushed return address. -/
  stackOffset : Option Nat
  deriving DecidableEq, Repr

inductive Return where
  | void
  | direct (chunks : List Chunk)
  | indirect (size align : Nat)
  deriving DecidableEq, Repr

structure CallPlan where
  arguments : List Argument
  result : Return
  /-- Space reserved below the caller's pre-reservation RSP, including final
  high-address padding. The first stack argument starts at offset zero. -/
  stackSize : Nat
  stackAlign : Nat
  gpUsed : Nat
  vectorUsed : Nat
  /-- Exact used-vector count is a permitted upper bound for variadic AL. -/
  variadicAL : Option Nat
  deriving DecidableEq, Repr

def gpArguments : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
def gpReturns : List Reg := [.rax, .rdx]

def memoryClass (object : Object) : Bool :=
  object.classes.any fun cls => cls == .memory || cls == .x87 ||
    cls == .x87Up || cls == .complexX87

def gpCount (object : Object) : Nat := object.classes.count .integer
def vectorCount (object : Object) : Nat := object.classes.count .sse

def chunks (object : Object) (registers : List Reg) (gp vector : Nat) :
    Except String (List Chunk) := do
  let mut result := []
  let mut gp := gp
  let mut vector := vector
  let mut vectorOffset := 0
  for (cls, index) in object.classes.zipIdx do
    let offset := 8 * index
    let bytes := min 8 (object.size - offset)
    match cls with
    | .noClass => pure ()
    | .integer =>
        let some register := registers[gp]? | throw "INTEGER register capacity exceeded"
        result := result ++ [⟨offset, bytes, .gp register⟩]
        gp := gp + 1
        vectorOffset := 0
    | .sse =>
        result := result ++ [⟨offset, bytes, .vector vector 0⟩]
        vector := vector + 1
        vectorOffset := 8
    | .sseUp =>
        if vector == 0 then throw "orphan SSEUP class"
        result := result ++ [⟨offset, bytes, .vector (vector - 1) vectorOffset⟩]
        vectorOffset := vectorOffset + 8
    | _ => throw "non-register class in ordinary register chunks"
  return result

/-- Return classification includes x87 and complex-x87, and reserves a hidden
first INTEGER argument only for MEMORY results. RAX must echo that sret pointer.
-/
def planReturn (result : Option Object) : Except String Return := do
  let some object := result | return .void
  unless object.valid do throw "invalid native result layout/classes"
  if object.classes == [.memory] then return .indirect object.size object.align
  if object.classes == [.x87, .x87Up] then
    return .direct [⟨0, 10, .x87 0⟩]
  if object.classes == [.complexX87] then
    return .direct [⟨0, 10, .x87 0⟩, ⟨16, 10, .x87 1⟩]
  if gpCount object > 2 || vectorCount object > 2 then
    throw "invalid native result register demand"
  return .direct (← chunks object gpReturns 0 0)

def needsWideVector (object : Object) : Bool :=
  object.size > 16 && object.classes.head? == some .sse &&
    (object.classes.drop 1).all (· == .sseUp)

/-- Plan one native call. Each aggregate either acquires all required INTEGER
and vector registers or consumes none and goes to the stack. Unnamed 256/512-bit
vectors use the stack. Callers must apply C default argument promotions first.
-/
def plan (profile : Profile) (args : List Object) (result : Option Object)
    (namedCount : Nat) (variadic : Bool) : Except String CallPlan := do
  if namedCount > args.length then throw "named argument count exceeds actual argument count"
  if !variadic && namedCount != args.length then throw "fixed call requires all arguments named"
  if result.any (fun object => object.size > profile.vectorBytes &&
      object.classes.head? == some .sse && (object.classes.drop 1).all (· == .sseUp)) then
    throw "wide vector result requires the matching AVX/AVX512 profile"
  let resultPlan ← planReturn result
  let mut gp := match resultPlan with | .indirect .. => 1 | _ => 0
  let mut vector := 0
  let mut stack := 0
  let mut stackAlign := 16
  let mut arguments := []
  for (object, index) in args.zipIdx do
    unless object.valid do throw "invalid native argument layout/classes"
    if needsWideVector object && object.size > profile.vectorBytes then
      throw "wide vector ABI requires the matching AVX/AVX512 profile"
    let unnamedWide := variadic && index ≥ namedCount && needsWideVector object
    if memoryClass object || unnamedWide || gp + gpCount object > 6 ||
        vector + vectorCount object > 8 then
      let alignment := max 8 object.align
      let offset := alignUp stack alignment
      arguments := arguments ++ [⟨object, [], some offset⟩]
      stack := offset + alignUp object.size 8
      stackAlign := max stackAlign alignment
    else
      let assigned ← chunks object gpArguments gp vector
      arguments := arguments ++ [⟨object, assigned, none⟩]
      gp := gp + gpCount object
      vector := vector + vectorCount object
  return ⟨arguments, resultPlan, alignUp stack stackAlign, stackAlign,
    gp, vector, if variadic then some vector else none⟩

/-- Native va_list is a one-element array of this 24-byte LP64 record.
Pointers are native addresses; this is unrelated to the old integer cursor. -/
structure VaList where
  gpOffset : Nat
  fpOffset : Nat
  overflowArgArea : Nat
  regSaveArea : Nat
  deriving DecidableEq, Repr

/-- The fixed register-save area has six 8-byte GP slots followed by eight
16-byte vector slots. Unused slots need not contain initialized data. -/
def VaList.valid (state : VaList) : Prop :=
  state.gpOffset ≤ 48 ∧ state.gpOffset % 8 = 0 ∧
  48 ≤ state.fpOffset ∧ state.fpOffset ≤ 176 ∧ (state.fpOffset - 48) % 16 = 0

/-- Start offsets account for the named arguments and hidden sret argument. -/
def VaList.start (namedPlan : CallPlan) (overflow save : Nat) : VaList :=
  ⟨8 * namedPlan.gpUsed, 48 + 16 * namedPlan.vectorUsed, overflow, save⟩

inductive VaSource where
  | registers (gpOffset fpOffset : Nat)
  | stack (address : Nat)
  deriving DecidableEq, Repr

/-- Advance a va_list without reading memory. Mixed-class reconstruction and
actual object reads are separate FFI representation obligations. -/
def VaList.next (state : VaList) (object : Object) : VaSource × VaList :=
  if !memoryClass object && !needsWideVector object &&
      state.gpOffset + 8 * gpCount object ≤ 48 &&
      state.fpOffset + 16 * vectorCount object ≤ 176 then
    (.registers state.gpOffset state.fpOffset,
      { state with
        gpOffset := state.gpOffset + 8 * gpCount object
        fpOffset := state.fpOffset + 16 * vectorCount object})
  else
    let address := alignUp state.overflowArgArea (max 8 object.align)
    (.stack address, {state with overflowArgArea := alignUp (address + object.size) 8})

end Silmaril.Machine.SystemV.Abi
