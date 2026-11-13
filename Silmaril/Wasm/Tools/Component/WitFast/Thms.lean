module

public import Silmaril.Wasm.Tools.Component.WitFast.Defs

/-!
# The fast path computes the specification

`packageUnique_eq`, `elaborateFast_eq`, `encodeDocsFast_eq`, `encodeTextFast_eq`,
`encodeTextXFast_eq`: each fast function equals the function of the verified elaborator and
encoder it replaces.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.WitFast

open Silmaril.Wasm.Wit

theorem interfaceUnique_eq (b : Binary.Interface) :
    interfaceUnique b = Elab.Interface.namesUniqueB b := rfl

theorem worldUnique_eq (w : Binary.World) : worldUnique w = Elab.World.namesUniqueB w := by
  unfold worldUnique Elab.World.namesUniqueB
  simp only [nodupB, interfaceUnique_eq]
  rfl

theorem packageUnique_eq (p : Binary.Package) : packageUnique p = Elab.Package.namesUniqueB p := by
  unfold packageUnique Elab.Package.namesUniqueB
  simp only [nodupB, interfaceUnique_eq, worldUnique_eq]

theorem elaborateFast_eq (U : Universe) (p : PackageName) (fs : List Name) :
    elaborateFast U p fs = Elab.elaborate U p fs := by
  unfold elaborateFast Elab.elaborate
  simp only [packageUnique_eq]

theorem encodeDocsFast_eq (d : Document) (ds : List Document) (fs : List Name) :
    encodeDocsFast d ds fs = Tool.encodeDocs d ds fs := by
  unfold encodeDocsFast Tool.encodeDocs Tool.elabDocs
  simp only [elaborateFast_eq]

theorem encodeTextFast_eq (m : String × String) (deps : List (String × String)) (fs : List Name) :
    encodeTextFast m deps fs = Tool.encodeText m deps fs := by
  unfold encodeTextFast Tool.encodeText
  simp only [encodeDocsFast_eq]

/-- **The fast path is the specification**: `encodeTextXFast` is `WitText.encodeTextXF`. -/
theorem encodeTextXFast_eq (main : List (String × String)) (deps : List (List (String × String)))
    (fs : List String) : encodeTextXFast main deps fs = WitText.encodeTextXF main deps fs := by
  unfold encodeTextXFast WitText.encodeTextXF
  simp only [encodeTextFast_eq, encodeDocsFast_eq]
  rfl

end Silmaril.Wasm.Tools.Component.WitFast
