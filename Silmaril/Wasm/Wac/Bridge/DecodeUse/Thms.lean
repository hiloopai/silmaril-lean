module

public import Silmaril.Wasm.Wac.Bridge.DecodeUse.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeUse.Sim
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeUse.Enc
public import Silmaril.Wasm.Wac.Bridge.DecodeGaps.Thms
public import Silmaril.Wasm.Wac.Bridge.DecodeImpl.Thms
public import Silmaril.Wasm.Wac.Bridge.DecodeItems.Thms

/-!
# WAC bridge: `decodePkgU` reads resource definitions and used types

`decodePkgU` (`Bridge.DecodeUse.Defs`) is a variant of `decodePkg`. This module proves:

* **Agreement on the old fragment.** `pkgOfWorldU_eq`: on world declarations without
  aliases (`naCs`) whose type exports are not wrappers with imports (`noUseDefs`),
  `pkgOfWorldU` is `pkgOfWorld`; without the second hypothesis the two differ only in how
  definitions are unwrapped (`pkgOfWorldU_of`, `pkgOfWorld_of`).
* **The new readings** at any level: `decIDeclU_outer0` (`alias outer 0 i` is the current
  scope's type `i`), `decIDeclU_useRes` (a type alias of a resource export `t` of an
  interface instance `I` is the used resource `own ⟨I, t⟩`).
* **Decoding inverts encoding** for `decodePkgU` on the named fragment of
  `Bridge.DecodeNamed` (the encoder writes no alias, `encode_naCs`):
  `decode_encode_namedU` (component types, when no exported type item is a wrapper with
  imports), `decodePkgU_world` (WIT world packages, no extra hypothesis) and
  `decodePkgU_impl` (component binaries that implement the declarations),
  `decodePkgU_itemsPackage` (WIT packages of several interfaces and worlds).
* **The two packages of `Bridge.DecodeGaps`**, which `decodePkg` rejects or misreads:
  `decodePkgU_cRes`: every binary of `cRes`, a component that defines and exports a
  resource, is read as a package defining the resource `r`; `decodePkgU_useAB`: every
  binary of `pkgAB` is read as the two interfaces, `foo:bar/b` with the items `tBU`:
  `t` is `WitDecl.usedKind ifA "t"`, the elaborator's item for `use a.{t}`, and `f`
  takes `borrow<⟨foo:bar/a, t⟩>`; `usedBy_tBU`: the elaborator's implicit-import
  machinery finds `foo:bar/a` as the interface `b` uses.

No `decode ∘ encode` theorem covers resource definitions or `use` across interfaces: the
encoder writes neither (`Bridge.Encode`), so for them only these binaries are checked.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner IfaceName)
open Silmaril.Wasm.Component.Wat (normComponentDecls)

namespace DecodeUse

theorem ok_bindE' {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem pure_okE {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

attribute [local simp] ok_bindE' pure_okE Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind DecodeNamed.throw_run

/-! ## Agreement with `decodePkg` -/

theorem pkgOfWorld_of {w : List ComponentDecl} {is es : Externs} {δ : DScope}
    (h : (decCDecls w [] []).run {} = .ok ((is, es), δ)) :
    pkgOfWorld w = .ok (pkgWith unwrapDef is es, δ.nom) := by
  simp only [pkgOfWorld, h, ok_bindE', pure_okE]; rfl

/-- On declarations without aliases, `pkgOfWorldU` reads the items `decodePkg` reads,
unwrapping definitions by `unwrapU`. -/
theorem pkgOfWorldU_of {w : List ComponentDecl} (hw : naCs w = true) {is es : Externs} {δ : DScope}
    (h : (decCDecls w [] []).run {} = .ok ((is, es), δ)) :
    pkgOfWorldU w = .ok (pkgWith unwrapU is es, δ.nom) := by
  obtain ⟨ids, hU⟩ := decCDeclsU_of hw (good_empty {} rfl) #[] h
  simp only [pkgOfWorldU, show ((decCDeclsU w [] []).run {} : Except String _) =
    .ok ((is, es), { base := δ, ids := ids }) from hU, ok_bindE', pure_okE]

theorem unwrapU_eq {k : Kind} (h : isUseWrap k = false) : unwrapU k = unwrapDef k := by
  unfold isUseWrap at h
  unfold unwrapU
  split
  · simp at h
  · rfl

theorem pkgWith_noUse (is : Externs) : ∀ {es : Externs}, noUseDefs es = true →
    pkgWith unwrapU is es = pkgWith unwrapDef is es := by
  intro es h
  simp only [pkgWith, PkgType.mk.injEq, true_and]
  apply List.filterMap_congr
  intro p hp
  have hk := List.all_eq_true.mp h p hp
  obtain ⟨n, k⟩ := p
  cases k <;> simp_all [unwrapU_eq]

/-- **`pkgOfWorldU` is `pkgOfWorld`** on declarations without aliases whose type exports are
not wrappers with imports. -/
theorem pkgOfWorldU_eq {w : List ComponentDecl} (hw : naCs w = true) {is es : Externs} {δ : DScope}
    (h : (decCDecls w [] []).run {} = .ok ((is, es), δ)) (hu : noUseDefs es = true) :
    pkgOfWorldU w = pkgOfWorld w := by
  rw [pkgOfWorldU_of hw h, pkgOfWorld_of h, pkgWith_noUse is hu]

/-! ## The two new readings, in general -/

/-- **`alias outer 0 i` is the type `i` of the current scope**, at every level (where
`decAlias` reads the enclosing scope). -/
theorem decIDeclU_outer0 (i : Nat) (es : Externs) (u : UScope) {t : TInfo} (h : u.base.types[i]? = some t) :
    (decIDeclU (.alias ⟨.type, .outer 0 i⟩) es).run u =
      .ok (es, { u with base := { u.base with types := u.base.types.push t } }) := by
  simp [decIDeclU, decAliasU, StateT.run_bind, StateT.run_get, h, onBase_run, pushTy]

/-- **A type alias of an export of an interface instance is a used type** of that
interface: a resource `t` of `I` is kept as `own ⟨I, t⟩`. -/
theorem decIDeclU_useRes (i : Nat) (n r : String) (es : Externs) (u : UScope) {fs : Externs}
    {I : IfaceName} (hi : u.base.insts[i]? = some fs) (hI : u.ids[i]? = some (some I))
    (hn : fs.lookup n = some (.type (.resource r))) :
    (decIDeclU (.alias ⟨.type, .export i n⟩) es).run u =
      .ok (es, { u with base := { u.base with types := u.base.types.push (.val (.own ⟨.iface I, n⟩)) } }) := by
  simp [decIDeclU, decAliasU, StateT.run_bind, StateT.run_get, hi, hI, hn, onBase_run, pushTy, usedInfo]

/-! ## Decoding inverts encoding on the named fragment -/

open DecodeNamed (EsOk extend dks pkgOf)

/-- **`decode ∘ encode` for `decodePkgU`** on the named fragment, when no exported type
item is a wrapper with imports (which `decodePkgU` reads as an interface using others). -/
theorem decode_encode_namedU {N : NomTable} {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) (hu : noUseDefs (dks es) = true) :
    ∃ σ nt, ((do importDecls is; exportDecls es : TM Unit)).run { share := true, nom := N } =
        .ok ((), σ) ∧
      pkgOfWorldU σ.decls = .ok (pkgOf (dks is) (dks es), nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, δ', hr, hdec, hn⟩ := DecodeNamed.decls_encode (δ := {}) true his hes rfl
    (fun _ h => absurd h (by simp))
  refine ⟨σ, δ'.nom, hr, ?_, hn⟩
  rw [pkgOfWorldU_of (encode_naCs rfl hr) hdec, pkgWith_noUse _ hu]
  rfl

/-- **The byte level for components** with `decodePkgU`: a component that implements the
encoder's declarations of the named fragment is read back as `decodePkg` reads it. -/
theorem decodePkgU_impl {N : NomTable} (b : Bool) {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) (hu : noUseDefs (dks es) = true) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      ∀ (c : Ast) (bytes : ByteArray), DecodeImpl.Implements c σ.decls → Component.Binary.encode c = some bytes →
        ∃ nt, decodePkgU bytes = .ok (pkgOf (dks is) (dks es), nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, δ', hr, hdec, hn⟩ := DecodeNamed.decls_encode (N := N) b his hes (δ := {}) rfl
    (fun _ h => absurd h (by simp))
  refine ⟨σ, hr, fun c bytes hc hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse bytes = .ok c := Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (DecodeImpl.project_impl hc)
  have hdec' : (decCDecls (normComponentDecls σ.decls) [] []).run {} = .ok ((dks is, dks es), δ') := by
    rw [DecodeNamed.decCDecls_norm]; exact hdec
  have hna : naCs (normComponentDecls σ.decls) = true := by rw [naCs_norm]; exact encode_naCs rfl hr
  simp only [decodePkgU, hp, pure_okE, ok_bindE', hw]
  rw [pkgOfWorldU_of hna hdec', pkgWith_noUse _ hu]
  rfl

/-- **The byte level for WIT world packages** with `decodePkgU`: the world is read back as
the package's definition, as `decodePkg` reads it. -/
theorem decodePkgU_world {N : NomTable} {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) (id name : String) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { nom := N } = .ok ((), σ) ∧
      ∀ b, Component.Binary.encode (Wit.Project.worldPackage id name σ.decls) = some b →
        ∃ nt, decodePkgU b = .ok (DecodeNamed.worldPkg name id (dks is) (dks es), nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  let δ0 : DScope := { outer := [#[], #[]], nom := [] }
  obtain ⟨σ, δ', hr, hdec, hn⟩ := DecodeNamed.decls_encode (N := N) false his hes (δ := δ0) rfl
    (fun _ h => absurd h (by simp [δ0]))
  refine ⟨σ, hr, fun b hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse b = .ok (Wit.Project.worldPackage id name σ.decls) :=
    Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (Wit.Project.project_worldPackage id name σ.decls)
  have hdec' : (decCDecls (normComponentDecls σ.decls) [] []).run δ0 = .ok ((dks is, dks es), δ') := by
    rw [DecodeNamed.decCDecls_norm]; exact hdec
  have hna : naCs (normComponentDecls σ.decls) = true := by rw [naCs_norm]; exact encode_naCs rfl hr
  obtain ⟨ids, hU⟩ := decCDeclsU_of hna (good_empty δ0 rfl) #[] hdec'
  simp [decodePkgU, hp, hw, pkgOfWorldU, decCDeclsU, decIDeclU, decDefTypeU, inNestedU, onBase_run, pushTy,
    decExternU, decExtern, typeAt, hU, δ0, namedInfoU, isUsed, namedInfo, addNom, typeKindU, typeKind, unwrapU, unwrapDef,
    ifaceId, pkgWith, DecodeNamed.worldPkg]

/-! ## WIT packages of several items -/

open DecodeItems (PItem itemDef itemsDefs itemsPkg itemExt)

theorem run'_ok {α : Type} {m : TM α} {s : Scope} {x : α} (h : m.run' s = .ok x) :
    ∃ s', m.run s = .ok (x, s') := by
  change (Prod.fst <$> m.run s) = _ at h
  cases hq : m.run s with
  | error e => rw [hq] at h; cases h
  | ok q => rw [hq] at h; cases h; exact ⟨q.2, rfl⟩

/-- The declarations of a nested scope of the encoder have no alias. -/
theorem nested_naCs {b : Bool} {m : TM Unit} (hm : Pres m) {N : NomTable} {ds : List ComponentDecl}
    (h : (nested b m).run' { nom := N } = .ok ds) : naCs ds = true := by
  obtain ⟨s', hs⟩ := run'_ok h
  obtain ⟨-, σ, hσ, hds⟩ := nested_ok hs
  rw [hds]
  exact hm _ _ _ rfl hσ

theorem bind_okE {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem naD_itemDef {N : NomTable} {it : PItem} {d : DefType} (h : itemDef N it = .ok d) : naD d = true := by
  cases it with
  | iface id es =>
    obtain ⟨ds, hr, hd⟩ := bind_okE h
    have hna : naCs ds = true := nested_naCs (pres_exportDecls es) hr
    cases hd
    simp [naD, naCs, naC, naI, naIs_instDecls ds hna]
  | world id is es =>
    obtain ⟨ds, hr, hd⟩ := bind_okE h
    have hna : naCs ds = true := nested_naCs (pres_bind (pres_importDecls is) fun _ => pres_exportDecls es) hr
    cases hd
    simp [naD, naCs, naC, naI, hna]

theorem naD_itemsDefs {N : NomTable} : ∀ {items : List (String × PItem)} {defs : List (String × DefType)},
    itemsDefs N items = .ok defs → ∀ p ∈ defs, naD p.2 = true
  | [], defs, h => by simp only [itemsDefs] at h; cases h; simp
  | (n, it) :: rest, defs, h => by
    simp only [itemsDefs] at h
    cases h1 : itemDef N it with
    | error e => rw [h1] at h; cases h
    | ok d =>
      cases h2 : itemsDefs N rest with
      | error e => rw [h1, h2] at h; cases h
      | ok ds =>
        rw [h1, h2] at h
        cases h
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact naD_itemDef h1
        · exact naD_itemsDefs h2 p hp

theorem naCs_itemDecls : ∀ (k : Nat) (defs : List (String × DefType)), (∀ p ∈ defs, naD p.2 = true) →
    naCs (Wit.Project.itemDecls k defs) = true
  | _, [], _ => rfl
  | k, (n, d) :: rest, h => by
    have ih := naCs_itemDecls (k + 1) rest fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp [Wit.Project.itemDecls, naCs, naC, naI, naD_norm, h (n, d) List.mem_cons_self, ih]

theorem noUseDefs_items : ∀ items : List (String × PItem), noUseDefs (items.map itemExt) = true
  | [] => rfl
  | (n, it) :: rest => by
    have ih := noUseDefs_items rest
    cases it <;> simp_all [noUseDefs, itemExt, DecodeItems.infoP, typeKind, isUseWrap]

/-- **The byte level for WIT packages of several interfaces and worlds** with `decodePkgU`:
read back as `decodePkg` reads them. -/
theorem decodePkgU_itemsPackage {N : NomTable} {items : List (String × PItem)}
    (h : ∀ p ∈ items, p.2.Ok N) (cs : List Section) (hc : ∀ c ∈ cs, Wit.Project.isCode c = true) :
    ∃ defs, itemsDefs N items = .ok defs ∧
      ∀ b, Component.Binary.encode (Wit.Project.itemsPackage defs cs) = some b →
        ∃ nt, decodePkgU b = .ok (itemsPkg items, nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨defs, hdefs, hres, δ', hdec, hn⟩ :=
    DecodeItems.items_dec items 0 {} [] h rfl (fun _ hp => absurd hp (by simp))
  refine ⟨defs, hdefs, fun b hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse b = .ok (Wit.Project.itemsPackage defs cs) :=
    Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (DecodeItems.project_itemsPackage defs cs hres hc)
  have hna := naCs_itemDecls 0 defs (naD_itemsDefs hdefs)
  simp only [decodePkgU, hp, pure_okE, ok_bindE', hw]
  rw [pkgOfWorldU_eq hna hdec (by simpa using noUseDefs_items items)]
  exact DecodeItems.pkgOfWorld_items hdec

/-! ## The two packages of `Bridge.DecodeGaps` -/

open DecodeGaps

/-- The interface `foo:bar/a`. -/
def ifA : IfaceName := ⟨⟨"foo", "bar", none⟩, "a"⟩

/-- The items of `foo:bar/b { use a.{t}; f: func(x: borrow<t>); }` as `decodePkgU` reads
them: the elaborator's alias of the used type, and `borrow` of it. -/
def tBU : Externs := [("t", WitDecl.usedKind ifA "t"),
  ("f", .func { async := false, params := [("x", .borrow ⟨.iface ifA, "t"⟩)], result := none })]

/-- What `decodePkgU` reads from `pkgAB`: the two interfaces. -/
def pkgABU : PkgType :=
  { imports := [], exports := [],
    defs := [(defName "foo:bar/a", .type (.inst (some "foo:bar/a") tA)),
             (defName "foo:bar/b", .type (.inst (some "foo:bar/b") tBU))] }

/-- What `decodePkgU` reads from `cRes`: the resource `r` as a definition. -/
def cResPkg : PkgType := { imports := [], exports := [], defs := [(defName "r", .type (.resource "r"))] }

theorem ifaceOf_a : ifaceOf "foo:bar/a" = some ifA := by
  simp only [ifaceOf, ifaceId_a, Option.bind_some]; rfl

theorem ifaceOf_b : ifaceOf "foo:bar/b" = some ⟨⟨"foo", "bar", none⟩, "b"⟩ := by
  simp only [ifaceOf, ifaceId_b, Option.bind_some]; rfl

theorem pkgOfWorldU_cRes : pkgOfWorldU cResWorld = .ok (cResPkg, []) := by
  simp [pkgOfWorldU, cResWorld, decCDeclsU, decIDeclU, decExternU, decAliasU, onBase_run, decExtern, pushTy,
    StateT.run_bind, StateT.run_modify, StateT.run_get, pkgWith, cResPkg, unwrapU, unwrapDef]

/-- **`decodePkgU` reads a component that defines and exports a resource** (which
`decodePkg` rejects, `decodePkg_cRes`): the resource is the package's definition `r`. -/
theorem decodePkgU_cRes (b : ByteArray) (hb : Component.Binary.encode cRes = some b) :
    decodePkgU b = .ok (cResPkg, []) := by
  have hp : Component.Binary.parse b = .ok cRes := Component.Binary.parse_encode hb
  simp only [decodePkgU, hp, pure_okE, ok_bindE', projectI_cRes, pkgOfWorldU_cRes]

theorem pkgOfWorldU_AB :
    pkgOfWorldU (Wit.Project.itemDecls 0 [("foo:bar/a", defA), ("foo:bar/b", defB)]) = .ok (pkgABU, []) := by
  simp [pkgOfWorldU, Wit.Project.itemDecls, Component.Wat.normDefType, Component.Wat.normComponentDecls,
    Component.Wat.normComponentDecl, Component.Wat.normInstanceDecls, Component.Wat.normInstanceDecl,
    Component.Wat.normName, defA, defB, decDefTypeU, inNestedU, decCDeclsU, decIDeclU, decIDeclsU, decExternU,
    decExtern, decAlias, decAliasU, onBase_run, typeAt, pushTy, namedInfoU, isUsed, namedInfo, addNom,
    typeKindU, typeKind, decDefValU, usedRes, decDefVal, resAt, decFunc, decVal, decValOpt, ifaceId_a,
    ifaceId_b, ifaceId_t, ifaceOf_a, ifaceOf_b, tA, tBU, pkgABU, usedInfo, WitDecl.usedKind, pkgWith,
    unwrapU, unwrapDef, StateT.run_map, StateT.run_set, Array.size_push, StateT.run_modify, StateT.run_bind,
    StateT.run_pure, StateT.run_get, Array.getElem?_push, Array.getElem_push, List.lookup]

/-- **`decodePkgU` reads an interface that uses another interface's type as an
interface** (which `decodePkg` reads as a component type, `decodePkg_useAB`), with the
used type owned by `foo:bar/a`. -/
theorem decodePkgU_useAB (b : ByteArray) (hb : Component.Binary.encode pkgAB = some b) :
    decodePkgU b = .ok (pkgABU, []) := by
  have hp : Component.Binary.parse b = .ok pkgAB := Component.Binary.parse_encode hb
  simp only [decodePkgU, hp, pure_okE, ok_bindE', projectI_pkgAB, pkgOfWorldU_AB]

/-- The elaborator's implicit imports of used interfaces (`WitDecl.usedBy`) find
`foo:bar/a` in the items `decodePkgU` reads for `foo:bar/b`. -/
theorem usedBy_tBU : WitDecl.usedBy tBU = [ifA] := rfl

/-- The binaries exist (`DecodeGaps.cRes_encodes`, `pkgAB_encodes`), so both readings are
about actual binaries; `decodePkg` rejects the first and misreads the second. -/
theorem decodePkgU_gaps :
    (∃ b, Component.Binary.encode cRes = some b ∧ decodePkgU b = .ok (cResPkg, []) ∧
        ∃ e, decodePkg b = .error e) ∧
      ∃ b, Component.Binary.encode pkgAB = some b ∧ decodePkgU b = .ok (pkgABU, []) ∧
        decodePkg b = .ok (pkgABRead, []) := by
  obtain ⟨b1, h1⟩ := Option.isSome_iff_exists.mp cRes_encodes
  obtain ⟨b2, h2⟩ := Option.isSome_iff_exists.mp pkgAB_encodes
  exact ⟨⟨b1, h1, decodePkgU_cRes b1 h1, decodePkg_cRes b1 h1⟩, b2, h2, decodePkgU_useAB b2 h2,
    decodePkg_useAB b2 h2⟩

end DecodeUse

end Silmaril.Wasm.Wac.Bridge
