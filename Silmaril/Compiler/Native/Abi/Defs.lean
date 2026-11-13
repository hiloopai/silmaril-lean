module

public import Silmaril.Machine.SystemV.Abi.Ctypes.Defs
public import Silmaril.Compiler.C.Types.Defs

/-! The compiler-specific adapter stays in Compiler: Machine's ABI model does
not depend on the old C compiler's code-generation representation.
-/

@[expose] public section
namespace Silmaril.Compiler.Native.Abi

open Silmaril.Machine.SystemV.Abi
open Silmaril.Cerberus.Mem.Concrete (Tags)

/-- Translate the old compiler view when it retains sufficient native type
information. Unsupported strings are never parsed to guess a missing C type. -/
def objectOfCodeType (tags : Tags) : Silmaril.Compile.C.CType → Except String Object
  | .int bytes _ =>
      if bytes == 1 || bytes == 2 || bytes == 4 || bytes == 8 || bytes == 16 then
        .ok (.integer bytes bytes)
      else .error "code integer width has no ordinary LP64 scalar layout"
  | .bool => .ok (.integer 1 1)
  | .float 4 => .ok (.floating .binary32)
  | .float 8 => .ok (.floating .binary64)
  | .float _ => .error "floating code type needs its original native format"
  | .ptr _ => .ok .pointer
  | .agg type => objectOfCtype tags type
  | .void => .error "void is not an object; use no result in the call signature"
  | .func _ => .error "function designator needs pointer conversion before ABI classification"
  | .unsupported why => .error s!"original C type metadata was discarded: {why}"

end Silmaril.Compiler.Native.Abi
