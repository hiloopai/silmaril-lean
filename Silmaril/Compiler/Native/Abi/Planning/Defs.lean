module

public import Silmaril.Compiler.Native.IR.Defs
public import Silmaril.Compiler.Native.Abi.Defs
public import Silmaril.Compiler.Native.Types.Registered.Defs
/-! Shared plans for the native function entry, calls and variadic activation.
The same retained source types and enum registry feed every ABI boundary. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Abi.Planning

open Silmaril.Compile
open Silmaril.Machine.SystemV.Abi

def resultObject (tags : Silmaril.Cerberus.Mem.Concrete.Tags) :
    C.CType → Except String (Option Object)
  | .void => return none
  | type => some <$> Silmaril.Compiler.Native.Abi.objectOfCodeType tags type

def functionPlan (info : FunctionInfo) : Except String CallPlan := do
  let arguments ← info.signature.params.mapM fun type =>
    Silmaril.Compiler.Native.Abi.objectOfCodeType info.tags
      (Types.Registered.ofCtype info.tags type)
  plan {} arguments (← resultObject info.tags info.signature.ret)
    arguments.length info.signature.variadic

def callPlan (info : CallInfo) : Except String CallPlan := do
  let arguments ← info.arguments.mapM (Silmaril.Compiler.Native.Abi.objectOfCodeType info.tags)
  plan {} arguments (← resultObject info.tags info.result) info.namedCount info.variadic

end Silmaril.Compiler.Native.Abi.Planning
