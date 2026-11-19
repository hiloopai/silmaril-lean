module

public import Silmaril.Formats.Json.Fast.Defs

@[expose] public section
namespace Silmaril.Formats.Json.Fast

/-- Forget the index and convert each scalar string to wire UTF-16 units. The caller supplies
a container-depth budget. This does not take a stance on DASL-specific semantics. -/
def Value.toWire? : Nat → Value → Option JsonWire.Ast
  | _, .null => some (.scalar none)
  | _, .bool boolean => some (.scalar (some (.bool boolean)))
  | _, .number decimal => some (.scalar (some (.number decimal)))
  | _, .string text => some (.scalar (some (.string (JsonWire.stringUnits text))))
  | 0, .array _ | 0, .object _ _ => none
  | depth + 1, .array items => do
    let children ← items.toList.mapM (Value.toWire? depth)
    return .list (children.foldr .cons .nil)
  | depth + 1, .object entries _ => do
    let children ← entries.toList.mapM fun (key, child) => do
      return (JsonWire.stringUnits key, ← child.toWire? depth)
    return .map (children.foldr (fun (key, child) tail => .objCons key child tail) .objNil)

end Silmaril.Formats.Json.Fast
