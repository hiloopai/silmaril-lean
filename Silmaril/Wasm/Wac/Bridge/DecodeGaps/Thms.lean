module

public import Silmaril.Wasm.Wac.Bridge.DecodeGaps.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeItems.Thms

/-!
# WAC bridge: two packages outside `decodePkg`, what it does on them

* `decodePkg_cRes`: **refuted** that `decodePkg` reads a component defining a resource.
  For every binary `b` of `cRes`, `decodePkg b` fails (`.error`; the message is `outer scope 0`): the
  projection writes the component's export of the resource as `(alias outer 0 0 (type))`
  (`projectI_cRes`), and the decoder's `decAlias` reads an outer alias of count `c` in
  the outer scope `c - 1`, which for `c = 0` is the enclosing scope (there is none at
  the top), not the current one. `cRes_encodes`: `cRes` has a binary.
* `decodePkg_useAB`: for every binary of `pkgAB`, `decodePkg` returns `pkgABRead`: the
  interface `foo:bar/b`, which uses the type `t` of `foo:bar/a`, is **not read as an
  interface** but as the component type of its wrapper (`unwrapDef` unwraps only
  wrappers without imports), so a path `foo:bar/b` finds a component. `pkgAB_encodes`: `pkgAB` has a binary.
* *Restated* (`unwrapUse_b`): unwrapping that definition as well gives the interface
  `foo:bar/b` with items `tB`. These name `t` as `type t = own<t>`, a resource `t` of
  their own scope, not of `foo:bar/a`: kinds have local type names only, so the owner
  of a used type is not kept.

No `decode ∘ encode` theorem covers these packages: the encoder writes neither.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary

namespace DecodeGaps

attribute [local simp] DecodeEnc.ok_bind DecodeEnc.pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind DecodeNamed.throw_run

/-! ## A component that defines a resource -/

theorem projectI_cRes : Wit.Project.projectI cRes = some cResWorld := by rfl

/-- The decoder fails at the alias, looking for an outer scope that does not exist. -/
theorem pkgOfWorld_cRes : ∃ e, pkgOfWorld cResWorld = .error e := by
  simp [pkgOfWorld, cResWorld, decCDecls, decIDecl, decExtern, pushTy, decAlias, StateT.run_bind,
    StateT.run_modify, StateT.run_get]

theorem cRes_encodes : (Component.Binary.encode cRes).isSome = true := by decide +kernel

/-- **`decodePkg` rejects a component that defines and exports a resource.** -/
theorem decodePkg_cRes (b : ByteArray) (hb : Component.Binary.encode cRes = some b) :
    ∃ e, decodePkg b = .error e := by
  have hp : Component.Binary.parse b = .ok cRes := Component.Binary.parse_encode hb
  obtain ⟨e, he⟩ := pkgOfWorld_cRes
  refine ⟨e, ?_⟩
  simp only [decodePkg, hp, DecodeEnc.pure_ok, DecodeEnc.ok_bind, projectI_cRes, he]

/-! ## An interface that uses a type of another interface -/

theorem ifaceId_a : ifaceId "foo:bar/a" = some "foo:bar/a" := by simp [ifaceId]

theorem ifaceId_b : ifaceId "foo:bar/b" = some "foo:bar/b" := by simp [ifaceId]

theorem ifaceId_t : ifaceId "t" = none := by simp [ifaceId]

theorem projectI_pkgAB : Wit.Project.projectI pkgAB =
    some (Wit.Project.itemDecls 0 [("foo:bar/a", defA), ("foo:bar/b", defB)]) :=
  Wit.Project.projectI_of_project (DecodeItems.project_itemsPackage _ []
    (by simp [Wit.Project.isResource, defA, defB]) (by simp))

theorem pkgOfWorld_AB :
    pkgOfWorld (Wit.Project.itemDecls 0 [("foo:bar/a", defA), ("foo:bar/b", defB)]) = .ok (pkgABRead, []) := by
  simp [pkgOfWorld, Wit.Project.itemDecls, DecodeNamed.decDefType_norm, defA, defB, decDefType, inNested,
    decCDecls, decIDecl, decIDecls, decExtern, decAlias, typeAt, pushTy, namedInfo, addNom, typeKind,
    decDefVal, resAt, decFunc, decVal, decValOpt, ifaceId_a, ifaceId_b, ifaceId_t, tA, tB, pkgABRead,
    unwrapDef, StateT.run_map, StateT.run_set, Array.size_push, StateT.run_modify, StateT.run_bind,
    StateT.run_pure, StateT.run_get, Array.getElem?_push, Array.getElem_push, List.lookup]

theorem pkgAB_encodes : (Component.Binary.encode pkgAB).isSome = true := by decide +kernel

/-- **`decodePkg` reads an interface that uses another interface's type as a component
type.** -/
theorem decodePkg_useAB (b : ByteArray) (hb : Component.Binary.encode pkgAB = some b) :
    decodePkg b = .ok (pkgABRead, []) := by
  have hp : Component.Binary.parse b = .ok pkgAB := Component.Binary.parse_encode hb
  simp only [decodePkg, hp, DecodeEnc.pure_ok, DecodeEnc.ok_bind, projectI_pkgAB, pkgOfWorld_AB]

/-- The restated reading: `unwrapUse` gives the interface `foo:bar/b`. -/
theorem unwrapUse_b : unwrapUse (.comp (some "foo:bar/b") [("foo:bar/a", .inst (some "foo:bar/a") tA)]
    [("foo:bar/b", .inst (some "foo:bar/b") tB)]) = .inst (some "foo:bar/b") tB := rfl

end DecodeGaps

end Silmaril.Wasm.Wac.Bridge
