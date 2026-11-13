module
public import Silmaril.Compiler.C.ToMir.Defs
public import Silmaril.Compiler.Native.X87.Defs
/-! Native compilation retains C signatures until ABI lowering. Mir alone loses
the information needed to distinguish integer, SSE and aggregate call operands.
-/
@[expose] public section
namespace Silmaril.Compiler.Native

open Silmaril.Compile
open Silmaril.Cerberus.Mem.Concrete (Tags)

structure FunctionInfo where
  name : String
  signature : C.FuncInfo
  tags : Tags
  frameBytes : Nat
  frameAlign : Nat
  /-- The native variadic register-save area within the object frame. -/
  vaSaveOffset : Option Nat := none

structure CallInfo where
  key : String
  callee : String
  indirectTarget : Option Mir.Reg
  arguments : List C.CType
  result : C.CType
  namedCount : Nat
  variadic : Bool
  tags : Tags

structure Artifact where
  mir : Mir.Unit
  functions : Array FunctionInfo
  calls : Array CallInfo
  /-- Effectful native instructions, referenced by Mir call keys. -/
  intrinsics : Array X87.Intrinsic := #[]

end Silmaril.Compiler.Native
