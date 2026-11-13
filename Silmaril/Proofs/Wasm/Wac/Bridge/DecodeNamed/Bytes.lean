module

public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeNamed.Lists
public import Silmaril.Wasm.Component.Binary.Thms
public import Silmaril.Wasm.Wit.Project.Thms
public import Silmaril.Wasm.Wit.Project.Infer.Thms

/-!
# WAC bridge: `decode ∘ encode` from a decoder scope, and the byte level

* `decls_encode`: the declarations the encoder writes for the imports and exports of the
  fragment (in either sharing mode) are read back by `decCDecls` from any empty decoder
  scope whose nominal table comes from `N`;
* `decCDecls_norm`: the decoder does not see the normal form of extern names
  (`Component.Wat.normComponentDecls`), which the projection applies;
* `decodePkg_worldPackage`: **the byte level** for the WIT package of a world
  (wit-component's layout, `Wit.Project.worldPackage`): if the package's binary is
  `b` (`Component.Binary.encode`), `decodePkg b` reads the world back as the package's
  definition, through `Component.Binary.parse` (`parse_encode`) and
  `Wit.Project.projectI` (`project_worldPackage`, `projectI_of_project`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normComponentDecls normInstanceDecls normDefType normInstanceDecl
  normComponentDecl normName)
open DecodeEnc (ok_bind pure_ok)

namespace DecodeNamed

attribute [local simp] ok_bind pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind throw_run

/-! ## From a decoder scope -/

/-- An empty decoder scope whose nominal table comes from `N` matches the empty encoder
scope. -/
theorem m_start (N : NomTable) (b : Bool) {δ : DScope} (hδ : δ.types = #[])
    (hn : ∀ p ∈ δ.nom, N.lookup p.1 = some p.2) : M N [] { share := b, nom := N } δ :=
  ⟨by simp [hδ], rfl, hn, fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp),
    fun _ _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp),
    fun _ => ⟨fun h => absurd h (by simp), fun h => by simp [hδ, IsRes] at h⟩, .nil⟩

/-- **The declarations of a package's items are read back** as `dks` of the items, from
any empty decoder scope. -/
theorem decls_encode {N : NomTable} (b : Bool) {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) {δ : DScope} (hδ : δ.types = #[])
    (hn : ∀ p ∈ δ.nom, N.lookup p.1 = some p.2) :
    ∃ σ δ', ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      (decCDecls σ.decls [] []).run δ = .ok ((dks is, dks es), δ') ∧
      ∀ p ∈ δ'.nom, N.lookup p.1 = some p.2 := by
  obtain ⟨σ1, E1, δ1, hr1, hd1, hm1, hreads1⟩ := (esOk_sim his _ _ (m_start N b hδ hn)).1
  obtain ⟨σ2, E2, δ2, hr2, hd2, hm2, hreads2, -⟩ := (esOk_sim hes σ1 δ1 hm1).2
  have e : σ2.decls = E1 ++ (E2 ++ []) := by rw [hd2, hd1]; simp
  have h2 : (decCDecls (E2 ++ []) ([] ++ dks is) []).run δ1 =
      (decCDecls [] ([] ++ dks is) ([] ++ dks es)).run δ2 := hreads2 [] _ []
  refine ⟨σ2, δ2, by simp [hr1, hr2], ?_, hm2.dnom⟩
  rw [e, hreads1, h2]
  simp [decCDecls]

/-! ## The normal form of names -/

mutual
theorem decDefType_norm : ∀ t : DefType, decDefType (normDefType t) = decDefType t
  | .val _ => rfl
  | .func _ => rfl
  | .component ds => by simp only [normDefType, decDefType, decCDecls_norm ds]
  | .instance ds => by simp only [normDefType, decDefType, decIDecls_norm ds]
  | .resource _ _ => rfl
theorem decIDecl_norm : ∀ (d : InstanceDecl) (es : Externs), decIDecl (normInstanceDecl d) es = decIDecl d es
  | .coreType _, _ => rfl
  | .type t, es => by simp only [normInstanceDecl, decIDecl, decDefType_norm t]
  | .alias _, _ => rfl
  | .export _ _, _ => rfl
theorem decIDecls_norm : ∀ (ds : List InstanceDecl) (es : Externs),
    decIDecls (normInstanceDecls ds) es = decIDecls ds es
  | [], _ => rfl
  | d :: ds, es => by simp only [normInstanceDecls, decIDecls, decIDecl_norm d, decIDecls_norm ds]
/-- **The decoder does not see the normal form of extern names.** -/
theorem decCDecls_norm : ∀ (ds : List ComponentDecl) (is es : Externs),
    decCDecls (normComponentDecls ds) is es = decCDecls ds is es
  | [], _, _ => rfl
  | .import _ _ :: ds, is, es => by simp only [normComponentDecls, normComponentDecl, decCDecls, normName,
      decCDecls_norm ds]
  | .inst d :: ds, is, es => by simp only [normComponentDecls, normComponentDecl, decCDecls,
      decIDecl_norm d, decCDecls_norm ds]
end

/-! ## The WIT package of a world -/

/-- What `decodePkg` reads from the WIT package of the world `(is, es)` named `id`: one
definition, the world. -/
def worldPkg (name id : String) (is es : Externs) : PkgType :=
  { imports := [], exports := [], defs := [(defName name, .type (.comp (some id) is es))] }

/-- **The byte level**: the binary `b` of the WIT package of a world of the fragment,
written by the encoder in a world scope (`share := false`, as `worldDef` does), is read
back by `decodePkg` as that world (`dks` of its items), with nominal definitions from
`N`. -/
theorem decodePkg_worldPackage {N : NomTable} {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) (id name : String) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { nom := N } = .ok ((), σ) ∧
      ∀ b, Component.Binary.encode (Wit.Project.worldPackage id name σ.decls) = some b →
        ∃ nt, decodePkg b = .ok (worldPkg name id (dks is) (dks es), nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  let δ0 : DScope := { outer := [#[], #[]], nom := [] }
  obtain ⟨σ, δ', hr, hdec, hn⟩ := decls_encode (N := N) false his hes (δ := δ0) rfl
    (fun _ h => absurd h (by simp [δ0]))
  refine ⟨σ, hr, fun b hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse b = .ok (Wit.Project.worldPackage id name σ.decls) :=
    Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (Wit.Project.project_worldPackage id name σ.decls)
  have hdec' : (decCDecls (normComponentDecls σ.decls) [] []).run δ0 = .ok ((dks is, dks es), δ') := by
    rw [decCDecls_norm]; exact hdec
  simp [decodePkg, hp, hw, pkgOfWorld, decCDecls, decIDecl, decDefType, inNested, pushTy, decExtern,
    typeAt, hdec', δ0, namedInfo, addNom, typeKind, unwrapDef, ifaceId, worldPkg]

end DecodeNamed

end Silmaril.Wasm.Wac.Bridge
