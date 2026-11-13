module

public import Silmaril.Cerberus.Core.Dynamics.Defs

/-! Compact exit-value printing at b3e11ea3. The batch driver preserves the
Core value, backend/common/driver_ocaml.ml:31-52,159-172. Printing follows
ocaml_frontend/pprinters/pp_core.ml:275-336 and pp_core_ctype.ml:22-107.
Pp_utils.to_plain_string uses PPrint's compact renderer, without line wrapping. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics

/-- concrete/impl_mem.ml:414-437. Memory structs and arrays have distinct
representations from the Core object-value constructors. -/
def memoryText : Nat → Mem.Concrete.MemoryValue → Option String
  | 0, _ => none
  | fuel+1, v => match v with
    | .unspecified _ => some "UNSPEC"
    | .integer _ n => some (toString n)
    | .floating _ _ => none
    | .pointer _ p => do pure ("ptr(" ++ (← pointerText fuel p) ++ ")")
    | .array xs => do pure ("{" ++ String.intercalate ", " (← xs.mapM (memoryText fuel)) ++ "}")
    | .struct_ s xs => do
        let fields ← xs.mapM fun (.mk _ name, _, v) => do
          pure ("." ++ name ++ "= " ++ (← memoryText fuel v))
        pure ("(struct " ++ symbolText s ++ "){" ++ String.intercalate ", " fields ++ "}")

mutual
 def objectText : Nat → ObjectValue Mem.Concrete.model → Option String
  | 0, _ => none
  | fuel+1, v => match v with
    | .integer n => some (toString n)
    | .floating _ => none
    | .pointer p => pointerText fuel p
    | .array xs => do pure ("Array(" ++ String.intercalate ", " (← xs.mapM (loadedText fuel)) ++ ")")
    | .struct s xs => do
        let fields ← xs.mapM fun (.mk _ name, _, v) => do
          pure ("." ++ name ++ "= " ++ (← memoryText fuel v))
        pure ("(struct " ++ symbolText s ++ "){" ++ String.intercalate ", " fields ++ "}")
    | .union s (.mk _ name) v => do
        pure ("(union " ++ symbolText s ++ "){." ++ name ++ "= " ++ (← memoryText fuel v) ++ "}")
 def loadedText : Nat → LoadedValue Mem.Concrete.model → Option String
  | 0, _ => none
  | fuel+1, .specified v => do pure ("Specified(" ++ (← objectText fuel v) ++ ")")
  | fuel+1, .unspecified t => do pure ("Unspecified('" ++ (← typeText fuel t) ++ "')")
end

def valueText : Nat → Val → Option String
  | 0, _ => none
  | fuel+1, v => match v with
    | .unit => some "Unit" | .true => some "True" | .false => some "False"
    | .object v => objectText fuel v
    | .loaded v => loadedText fuel v
    | .list _ vs => do pure ("[" ++ String.intercalate ", " (← vs.mapM (valueText fuel)) ++ "]")
    | .tuple vs => do pure ("(" ++ String.intercalate ", " (← vs.mapM (valueText fuel)) ++ ")")
    -- Standalone Vctype uses the separate Ail declarator printer, not the
    -- Core type printer. It is outside the supported exit representation.
    | .ctype _ => none

end Silmaril.Cerberus.Core.Dynamics
