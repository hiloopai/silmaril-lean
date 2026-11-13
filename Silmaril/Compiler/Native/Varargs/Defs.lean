module

public import Silmaril.Compiler.Native.Abi.Planning.Defs
public import Silmaril.Compiler.Native.Layout.Defs
/-! Native LP64 stdarg plans. These retain the System V record, separate GP/FP
register-save cursors, and unpadded named stack extent. They do not reuse the
frozen compiler's integer cursor or linear-memory calling convention. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Varargs

open Silmaril.Compile.C (CType)
open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi

def recordBytes : Nat := 24
def saveBytes : Nat := 176

/-- The high-address padding in `CallPlan.stackSize` is not a named argument.
The next variadic stack object starts after the last actual named stack slot. -/
def namedStackEnd (plan : CallPlan) : Nat :=
  plan.arguments.foldl (fun finish argument => match argument.stackOffset with
    | none => finish
    | some offset => max finish (offset + alignUp argument.object.size 8)) 0

structure Activation where
  saveOffset : Nat
  namedPlan : CallPlan
  lastNamed : Option Sym

inductive Bank where
  | gp | fp
  deriving DecidableEq, Repr

structure Piece where
  objectOffset : Nat
  bytes : Nat
  bank : Bank
  saveOffset : Nat
  deriving DecidableEq, Repr

/-- Use the actual ABI chunk assignment to reconstruct a register object from
its save area. SSEUP bytes use the same sixteen-byte saved vector slot. -/
def pieces (object : Object) : Except String (List Piece) := do
  let assigned ← chunks object gpArguments 0 0
  assigned.mapM fun chunk => do
    match chunk.location with
    | .gp register =>
        return ⟨chunk.offset, chunk.bytes, .gp, 8 * gpArguments.idxOf register⟩
    | .vector index offset =>
        return ⟨chunk.offset, chunk.bytes, .fp, 16 * index + offset⟩
    | .x87 _ => throw "x87 variadic objects are passed in the overflow area"

def onStack (object : Object) : Bool := memoryClass object || needsWideVector object

/-- `va_arg` names the type after default argument promotions. Narrow integer
and float requests are undefined C uses and are rejected explicitly. -/
def argumentObject (tags : Tags) (type : CType) : Except String Object := do
  match type with
  | .bool => throw "va_arg requires the promoted integer type"
  | .int bytes _ =>
      if bytes < 4 then throw "va_arg requires the promoted integer type"
  | .float bytes =>
      if bytes != 8 then throw "va_arg requires the promoted double type"
  | _ => pure ()
  let object ← Silmaril.Compiler.Native.Abi.objectOfCodeType tags type
  unless object.valid do throw "invalid native va_arg object"
  return object

/-- Accept a pointer to the real native record, including the array-to-pointer
decay of `va_list[1]`. An old Cerberus integer cursor cannot satisfy this check.
Field spelling is irrelevant; types, order, offsets, size and alignment matter. -/
def checkList (tags : Tags) (type : CType) : Except String Unit := do
  let .ptr record := type | throw "native va_list must point to its System V record"
  let layout ← layoutOfCtype tags record
  unless layout.object.size == recordBytes && layout.object.align == 8 do
    throw "native va_list must have its 24-byte System V layout"
  let [(_, gp, gpOffset), (_, fp, fpOffset), (_, overflow, overflowOffset),
      (_, save, saveOffset)] := layout.members
    | throw "native va_list must have four System V fields"
  unless gpOffset == 0 && fpOffset == 4 && overflowOffset == 8 && saveOffset == 16 do
    throw "native va_list field offsets do not match System V"
  let unsigned32 (type : Ctype) : Bool := match Types.Registered.ofCtype tags type with
    | .int 4 false => true
    | _ => false
  let pointer (type : Ctype) : Bool := match Types.Registered.ofCtype tags type with
    | .ptr _ => true
    | _ => false
  unless unsigned32 gp && unsigned32 fp && pointer overflow && pointer save do
    throw "native va_list field types do not match System V"

end Silmaril.Compiler.Native.Varargs
