module

public import Silmaril.Wasm.Models.V2CoreInstDet.Thms
public import Silmaril.Proofs.Wasm.Models.V2CoreInstDom.Main

/-!
# The domain of the deterministic instantiation embedding is inhabited

An earlier step restated the `eq` instantiation embedding at `Profile.deterministic g` on the domain
`domInstDet g` (`Silmaril.Wasm.Models.V2CoreInstDet.v20InstEmbDet`) and left open whether any point
is in it. One is:

* **`domInstDet_emptyPt`**: the empty 2.0 store with the closed host (`emptyPt`) is in
  `domInstDet g` for every grow policy `g`. Core instantiates a call there only when it has no
  external addresses and the module has no imports (`not_externAddrOk_empty`); a 2.0-valid
  module without imports instantiates in the empty store (`instantiate_empty`: constant
  initialisers, `allocModule?` in range, segment bounds read off the Core image), its
  configuration is typed on a host-free store, and so it has a closed-host behaviour.
* `domInstDet_nonempty`: `∃ p, domInstDet g p`.

So `v20InstEmbDet g` is an `eq` embedding on a non-empty domain: at the empty store every
2.0-valid module with a Core image has equal spec and 2.0 instantiation observations
(`obs_eq_det`). Points with imports are not covered here; they need import typing to transfer
from Core back to 2.0.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstDom

open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
  Silmaril.Wasm.Models.V2CoreInstDet

/-- The empty 2.0 store with the closed host. -/
abbrev emptyPt : Pt Nat := Silmaril.Proofs.Wasm.Models.V2CoreInstDom.emptyPt

/-- **A valid 2.0 module without imports instantiates in the empty store**, under every host,
at every profile, given the segment bounds `$instantiate` assumes; the store it starts from is
host-free. -/
theorem instantiate_empty {H : Type} (P : Profile) {m : Silmaril.Wasm.V2.Module}
    {xt : List Silmaril.Wasm.V2.ExternType} (hm : Silmaril.Wasm.V2.Validation.ModuleOk m [] xt)
    (hb : Silmaril.Proofs.Wasm.Models.V2CoreInstDom.SegBounded m) :
    ∃ c : Silmaril.Wasm.V2.Execution.Config H,
      (∀ host, Silmaril.Wasm.V2.Execution.Instantiate P host ({} : Silmaril.Wasm.V2.Execution.Store H) m [] c) ∧
        Silmaril.Proofs.Wasm.Models.V2Sound.HostFree c.store :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstDom.instantiate_empty P hm hb

/-- **The empty store with the closed host is in `domInstDet g`.** -/
theorem domInstDet_emptyPt (g : GrowKind → Nat → Nat → Nat → Bool) : domInstDet g emptyPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstDom.domInstDet_emptyPt g

/-- **`domInstDet g` is not empty.** -/
theorem domInstDet_nonempty (g : GrowKind → Nat → Nat → Nat → Bool) : ∃ p, domInstDet g p :=
  ⟨emptyPt, domInstDet_emptyPt g⟩

/-! The axiom audit. -/

/--
info: 'Silmaril.Wasm.Models.V2CoreInstDom.domInstDet_emptyPt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms domInstDet_emptyPt

/--
info: 'Silmaril.Wasm.Models.V2CoreInstDom.instantiate_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms instantiate_empty

end Silmaril.Wasm.Models.V2CoreInstDom
