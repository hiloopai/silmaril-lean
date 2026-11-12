module

public import Silmaril.Proofs.Data.Layout.Resolve

/-!
# Nested member designators (header)

PROVED in `Silmaril.Proofs.Data.Layout.Resolve` (namespace `Silmaril.Proofs.Data.Layout`):

* `layoutTy_mono`: layouts are monotone in fuel; `layoutTy_strip`: typedefs only consume fuel.
* `declLayout_field`: a member of a computed layout has the size of its type's layout, and the
  type's alignment divides the member's alignment.
* `resolve_wf`: under a well-formed data model, `resolve dm env t p = .ok (o, t', s')` and
  `layoutTy dm env defaultFuel t = .ok s` give `o + s'.size ≤ s.size`, `s'.align ∣ o` and
  `s'.align ∣ s.align`: a designated subobject (`a.b[i].c`) lies inside the object, and is
  aligned whenever the object is.
-/
