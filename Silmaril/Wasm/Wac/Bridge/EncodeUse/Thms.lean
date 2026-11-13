module

public import Silmaril.Wasm.Wac.Bridge.EncodeUse.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.EncodeUse.Res
public import Silmaril.Proofs.Wasm.Wac.Bridge.EncodeUse.Pkg
public import Silmaril.Wasm.Wac.Bridge.DecodeUse.Thms
public import Silmaril.Wasm.Wac.Bridge.DecodeItems.Thms

/-!
# WAC bridge: `decodePkgU` inverts the encoder variant `EncodeUse`

Proofs in `Silmaril.Proofs.Wasm.Wac.Bridge.EncodeUse.{Res,Body,Pkg}`.

* **Resource definitions** (`resComp rs`, any list of names):
  `decodePkgU_resComp`: every binary of `resComp rs` is read as `resPkg rs`, one resource
  definition per name. The projection writes each export of a resource as
  `(alias outer 0 k (type))` (`projectI_resComp`), which `decodePkgU` reads in the
  current scope. `decodePkg_resComp`: `decodePkg` rejects every binary of `resComp rs`
  for `rs ≠ []` (it reads `alias outer 0` in the enclosing scope, absent at the top);
  this generalizes `DecodeGaps.decodePkg_cRes`.
* **`use` across interfaces** (`usePkg items`, any list of interfaces satisfying
  `UIface.Ok`): `decodePkgU_usePkg`: every binary of `usePkg items` is read as
  `usePkgRd items`: each interface with its items `rdIface u`, the used types as
  `WitDecl.usedKind I t` (the elaborator's item for `use I.{t as l}`) and the handles of
  used resources owned by `I`.
* **The binaries of `Bridge.DecodeGaps`** are instances: `cRes_eq` (`cRes = resComp ["r"]`),
  `pkgAB_eq` (`pkgAB = usePkg itemsAB`); the general theorems give back
  `DecodeUse.decodePkgU_cRes` and `DecodeUse.decodePkgU_useAB` (`decodePkgU_cRes_of`,
  `decodePkgU_useAB_of`).

The encoder variant is separate from `Bridge.Encode`: its layout is wit-component's for
these two shapes, with every parameter type defined as a type of its own (`UIface`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary

namespace EncodeUse

open DecodeUse

theorem ok_bindE'' {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem pure_okE' {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

/-! ## Resource definitions -/

/-- **`decode ∘ encode` for components defining resources.** -/
theorem decodePkgU_resComp (rs : List String) (b : ByteArray) (hb : Component.Binary.encode (resComp rs) = some b) :
    decodePkgU b = .ok (resPkg rs, []) := by
  have hp : Component.Binary.parse b = .ok (resComp rs) := Component.Binary.parse_encode hb
  obtain ⟨u', hu, hn⟩ := decCDeclsU_resWorld 0 rs {} [] rfl
  simp only [decodePkgU, hp, pure_okE', ok_bindE'', projectI_resComp, pkgOfWorldU, hu]
  simp only [hn]
  simp [pkgWith, resPkg, unwrapU, unwrapDef, List.filter_map, List.filterMap_map, Function.comp_def]

/-- **`decodePkg` rejects every component defining a resource** (of this layout). -/
theorem decodePkg_resComp (r : String) (rs : List String) (b : ByteArray)
    (hb : Component.Binary.encode (resComp (r :: rs)) = some b) : ∃ e, decodePkg b = .error e := by
  have hp : Component.Binary.parse b = .ok (resComp (r :: rs)) := Component.Binary.parse_encode hb
  obtain ⟨e, he⟩ := decCDecls_resWorld r rs []
  refine ⟨e, ?_⟩
  simp only [decodePkg, hp, pure_okE', ok_bindE'', projectI_resComp, pkgOfWorld, he]
  rfl

/-! ## `use` across interfaces -/

theorem projectI_usePkg (items : List (String × UIface)) :
    Wit.Project.projectI (usePkg items) =
      some (Wit.Project.itemDecls 0 (items.map fun p => (p.1, ifaceDefU p.1 p.2))) :=
  Wit.Project.projectI_of_project (DecodeItems.project_itemsPackage _ []
    (by
      intro p hp
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      rfl) (by simp))

/-- **`decode ∘ encode` for packages of interfaces that use each other's resources.** -/
theorem decodePkgU_usePkg (items : List (String × UIface)) (hok : ∀ p ∈ items, p.2.Ok) (b : ByteArray)
    (hb : Component.Binary.encode (usePkg items) = some b) : decodePkgU b = .ok (usePkgRd items, []) := by
  have hp : Component.Binary.parse b = .ok (usePkg items) := Component.Binary.parse_encode hb
  simp only [decodePkgU, hp, pure_okE', ok_bindE'', projectI_usePkg, pkgOfWorldU_usePkg items hok]

/-! ## The binaries of `Bridge.DecodeGaps` -/

theorem cRes_eq : DecodeGaps.cRes = resComp ["r"] := rfl

theorem resPkg_r : resPkg ["r"] = cResPkg := rfl

/-- `foo:bar/a { resource t; }`. -/
def uA : UIface := { res := ["t"] }

/-- `foo:bar/b { use a.{t}; f: func(x: borrow<t>); }`. -/
def uB : UIface :=
  { uses := [{ iid := "foo:bar/a", I := ifA, t := "t", l := "t" }],
    funcs := [("f", [("x", .borrow (.used 0))])] }

def itemsAB : List (String × UIface) := [("foo:bar/a", uA), ("foo:bar/b", uB)]

theorem pkgAB_eq : DecodeGaps.pkgAB = usePkg itemsAB := rfl

theorem itemsAB_ok : ∀ p ∈ itemsAB, p.2.Ok := by
  intro p hp
  simp only [itemsAB, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨by simp [uA], by simp [uA]⟩
  · refine ⟨?_, ?_⟩
    · simp [uB, ifaceOf_a]
    · simp [uB, UPar.Ok, URes.Ok]

theorem usePkgRd_AB : usePkgRd itemsAB = pkgABU := rfl

/-- `DecodeUse.decodePkgU_cRes`, from the general theorem. -/
theorem decodePkgU_cRes_of (b : ByteArray) (hb : Component.Binary.encode DecodeGaps.cRes = some b) :
    decodePkgU b = .ok (cResPkg, []) := by
  rw [← resPkg_r]; exact decodePkgU_resComp ["r"] b hb

/-- `DecodeUse.decodePkgU_useAB`, from the general theorem. -/
theorem decodePkgU_useAB_of (b : ByteArray) (hb : Component.Binary.encode DecodeGaps.pkgAB = some b) :
    decodePkgU b = .ok (pkgABU, []) := by
  rw [← usePkgRd_AB]; exact decodePkgU_usePkg itemsAB itemsAB_ok b hb

end EncodeUse

end Silmaril.Wasm.Wac.Bridge
