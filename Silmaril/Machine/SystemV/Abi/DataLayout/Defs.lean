module

public import Silmaril.Machine.SystemV.Abi.Ctypes.Defs
public import Silmaril.Data.Layout.Cerberus.Defs

/-!
# The native System V layout and `Silmaril.Data.Layout`

`layoutOfCtype` (the layout used by native lowering and ABI classification) and
`Silmaril.Data.Layout.declLayout sysvX86_64` are two models of the same psABI rule; `nativeLayout`
summarises the first on the Cerberus translation of a declaration environment
(`Silmaril.Data.Layout.Cerb.toTags`) in the shape of `Silmaril.Data.Layout.Cerb.ourLayout`.
Unlike Cerberus' concrete layout, both use the native floating sizes. Agreement: `Thms`.
-/

@[expose] public section

namespace Silmaril.Machine.SystemV.Abi.DataLayout

open Silmaril.Data.Layout Silmaril.Data.Layout.Cerb

/-- Size, alignment and `(member, offset)` of the native layout of struct or union `tag`. -/
def nativeLayout (env : Env) (k : Kind) (tag : String) : Option (Int × Int × List (String × Int)) :=
  (toTags env).bind fun tags =>
    match layoutOfCtype tags ⟨[], match k with
      | .struct => .struct (tagSym env .struct tag)
      | .union => .union (tagSym env .union tag)⟩ with
    | .ok l => some (l.object.size, l.object.align,
        match k with
        | .struct => l.members.map fun (i, _, o) => (i.name, (o : Int))
        | .union => [])
    | .error _ => none

end Silmaril.Machine.SystemV.Abi.DataLayout
