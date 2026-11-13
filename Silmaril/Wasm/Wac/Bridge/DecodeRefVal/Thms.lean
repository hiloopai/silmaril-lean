module

public import Silmaril.Wasm.Wac.Bridge.DecodeRefVal.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeRefVal.Lists
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeRefVal.Contain
public import Silmaril.Wasm.Wac.Bridge.DecodeImpl.Thms

/-!
# WAC bridge: `decode ∘ encode` with `ref` of resources at every level

For a package `(is, es)` of the fragment `EsOkR` (`Bridge.DecodeRefVal.Defs`): value types
may write a resource as `ref a` and a resource alias as `own<a>` (in function types, value
items and inside other types), alias type items may name a resource or an alias as
`own<a>` or `a`, at every level of nested instances and components; value items are
allowed everywhere. The decoder reads back `rdEs`, its own forms:

* `decode_encode_refVal`: `pkgOfWorld` reads the encoder's declarations (sharing scope)
  back as `pkgOf (dks (rdEs [] is)) (dks (rdEs (extendR [] is) es))`;
* `decodePkg_world_refVal`: the byte level for the WIT package of the world;
* `decodePkg_impl_refVal`: the byte level for component binaries that implement it;
* `decode_encode_exRV`: an example with `ref` of a resource in a function's parameters,
  `own<a>` of an alias inside a `list`, an alias of an alias, and a nested component
  type with two functions over the same resource written once as `ref s` and once as
  `own<s>` (two cache keys of the encoder, the same type for the decoder).
* `esOkR_of_esOk` (in `Silmaril/Proofs/Wasm/Wac/Bridge/DecodeRefVal/Contain.lean`): the
  fragment contains `DecodeNamed.EsOk`, where `rdEs` is the identity and `extendR` is
  `extend`; `decode_encode_named_of_refVal` recovers `DecodeNamed.decode_encode_named`.

The invariant is `DecodeNamed.M` up to the read-back (`MR`, in
`Silmaril/Proofs/Wasm/Wac/Bridge/DecodeRefVal/Val.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normComponentDecls)
open Silmaril.Wasm.Wit.Binary (Ty Sig)
open DecodeNamed (dks pkgOf worldPkg decCDecls_norm)

namespace DecodeRefVal

attribute [local simp] DecodeEnc.ok_bind DecodeEnc.pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind DecodeNamed.throw_run

/-- **Decoding inverts encoding up to the read-back** on packages of the fragment. -/
theorem decode_encode_refVal {N : NomTable} {is es : Externs} (his : EsOkR N [] is)
    (hes : EsOkR N (extendR [] is) es) :
    ∃ σ nt, ((do importDecls is; exportDecls es : TM Unit)).run { share := true, nom := N } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf (dks (rdEs [] is)) (dks (rdEs (extendR [] is) es)), nt) ∧
      ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, δ', hr, hdec, hn⟩ := decls_encodeR (δ := {}) true his hes rfl (fun _ h => absurd h (by simp))
  refine ⟨σ, δ'.nom, hr, ?_, hn⟩
  simp only [pkgOfWorld, hdec, pkgOf, DecodeEnc.ok_bind, DecodeEnc.pure_ok, Except.ok.injEq, Prod.mk.injEq,
    and_true]
  congr 1

/-- **The byte level for the WIT package of the world**, up to the read-back. -/
theorem decodePkg_world_refVal {N : NomTable} {is es : Externs} (his : EsOkR N [] is)
    (hes : EsOkR N (extendR [] is) es) (id name : String) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { nom := N } = .ok ((), σ) ∧
      ∀ b, Component.Binary.encode (Wit.Project.worldPackage id name σ.decls) = some b →
        ∃ nt, decodePkg b = .ok (worldPkg name id (dks (rdEs [] is)) (dks (rdEs (extendR [] is) es)), nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  let δ0 : DScope := { outer := [#[], #[]], nom := [] }
  obtain ⟨σ, δ', hr, hdec, hn⟩ := decls_encodeR (N := N) false his hes (δ := δ0) rfl
    (fun _ h => absurd h (by simp [δ0]))
  refine ⟨σ, hr, fun b hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse b = .ok (Wit.Project.worldPackage id name σ.decls) :=
    Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (Wit.Project.project_worldPackage id name σ.decls)
  have hdec' : (decCDecls (normComponentDecls σ.decls) [] []).run δ0 =
      .ok ((dks (rdEs [] is), dks (rdEs (extendR [] is) es)), δ') := by
    rw [decCDecls_norm]; exact hdec
  simp [decodePkg, hp, hw, pkgOfWorld, decCDecls, decIDecl, decDefType, inNested, pushTy, decExtern,
    typeAt, hdec', δ0, namedInfo, addNom, typeKind, unwrapDef, ifaceId, worldPkg]

/-- **The byte level for component binaries**, up to the read-back. -/
theorem decodePkg_impl_refVal {N : NomTable} (b : Bool) {is es : Externs} (his : EsOkR N [] is)
    (hes : EsOkR N (extendR [] is) es) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      ∀ (c : Ast) (bytes : ByteArray), DecodeImpl.Implements c σ.decls →
        Component.Binary.encode c = some bytes →
        ∃ nt, decodePkg bytes = .ok (pkgOf (dks (rdEs [] is)) (dks (rdEs (extendR [] is) es)), nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, δ', hr, hdec, hn⟩ := decls_encodeR (N := N) b his hes (δ := {}) rfl
    (fun _ h => absurd h (by simp))
  refine ⟨σ, hr, fun c bytes hc hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse bytes = .ok c := Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (DecodeImpl.project_impl hc)
  have hdec' : (decCDecls (normComponentDecls σ.decls) [] []).run {} =
      .ok ((dks (rdEs [] is), dks (rdEs (extendR [] is) es)), δ') := by
    rw [decCDecls_norm]; exact hdec
  simp only [decodePkg, hp, DecodeEnc.pure_ok, DecodeEnc.ok_bind, hw]
  simp only [pkgOfWorld, hdec', DecodeEnc.ok_bind, DecodeEnc.pure_ok, pkgOf]
  rfl

/-- `DecodeNamed.decode_encode_named`, from `decode_encode_refVal`. -/
theorem decode_encode_named_of_refVal {N : NomTable} {is es : Externs} (his : DecodeNamed.EsOk N [] is)
    (hes : DecodeNamed.EsOk N (DecodeNamed.extend [] is) es) :
    ∃ σ nt, ((do importDecls is; exportDecls es : TM Unit)).run { share := true, nom := N } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf (dks is) (dks es), nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  have hi : Contained N [] is := esOkR_of_esOk his
  have he : Contained N (extendR [] is) es := hi.2.2 ▸ esOkR_of_esOk hes
  obtain ⟨σ, nt, hr, hd, hn⟩ := decode_encode_refVal hi.1 he.1
  rw [he.2.1, hi.2.1] at hd
  exact ⟨σ, nt, hr, hd, hn⟩

/-! ## An example -/

/-- A function over `s`, written as `ref s` (`o = false`) or `own<s>` (`o = true`). -/
def sFn (o : Bool) : Kind :=
  .func { async := false, params := [("y", if o then .own ⟨.local, "s"⟩ else .ref ⟨.local, "s"⟩)],
          result := none }

/-- A resource `r`; `type r2 = r` (written as a reference); `type r3 = own<r2>` (an alias
of an alias); `f : (x : r) -> list<own<r2>>`; a component type `c` that imports a
resource `s` and exports `g : (y : s)` and `h : (y : own<s>)`; a value `v : option<r>`. -/
def exRV : Externs :=
  [("r", .type (.resource "r")),
   ("r2", .type (.value (.ref ⟨.local, "r"⟩))),
   ("r3", .type (.value (.own ⟨.local, "r2"⟩))),
   ("f", .func { async := false, params := [("x", .ref ⟨.local, "r"⟩)],
                 result := some (.list (.own ⟨.local, "r2"⟩)) }),
   ("c", .comp none [("s", .type (.resource "s"))] [("g", sFn false), ("h", sFn true)]),
   ("v", .value (.option (.ref ⟨.local, "r"⟩)))]

/-- What the decoder reads back: the forms of `DecodeNamed`. -/
def exRVBack : Externs :=
  [("r", .type (.resource "r")),
   ("r2", .type (.value (.own ⟨.local, "r"⟩))),
   ("r3", .type (.value (.own ⟨.local, "r"⟩))),
   ("f", .func { async := false, params := [("x", .own ⟨.local, "r"⟩)],
                 result := some (.list (.ref ⟨.local, "r2"⟩)) }),
   ("c", .comp none [("s", .type (.resource "s"))] [("g", sFn true), ("h", sFn true)]),
   ("v", .value (.option (.own ⟨.local, "r"⟩)))]

theorem exRV_rd : rdEs [] exRV = exRVBack := by decide +kernel

theorem ifaceId_c : ifaceId "c" = none := by simp [ifaceId]

theorem exRV_back : dks (rdEs [] exRV) = exRVBack := by
  rw [exRV_rd]
  simp [exRVBack, dks, DecodeNamed.dk, ifaceId_c, sFn]

theorem exRV_comp_ok : EsOkR [] [] [("s", .type (.resource "s"))] ∧
    EsOkR [] (extendR [] [("s", .type (.resource "s"))]) [("g", sFn false), ("h", sFn true)] := by
  refine ⟨.res .nil, .func ⟨?_, fun _ h => absurd h (by simp)⟩ (.func ⟨?_, fun _ h => absurd h (by simp)⟩ .nil)⟩
  · intro p hp
    rw [show p = ("y", .ref ⟨.local, "s"⟩) from List.mem_singleton.1 hp]
    exact .refRes rfl
  · intro p hp
    rw [show p = ("y", .own ⟨.local, "s"⟩) from List.mem_singleton.1 hp]
    exact .own rfl

theorem exRV_ok : EsOkR [] [] exRV := by
  refine .res (.tyRes (Or.inr rfl) rfl (.tyAli (Or.inl rfl) rfl (.func ⟨?_, ?_⟩
    (.comp exRV_comp_ok.1 exRV_comp_ok.2 (.value ?_ .nil)))))
  · intro p hp
    rw [show p = ("x", .ref ⟨.local, "r"⟩) from List.mem_singleton.1 hp]
    exact .refRes rfl
  · intro t ht
    rw [show t = .list (.own ⟨.local, "r2"⟩) from (Option.some.inj (Option.mem_def.1 ht)).symm]
    exact .list (.ownAlias rfl)
  · exact .option (.refRes rfl)

/-- `ref r` of a resource, `own<r2>` of an alias, an alias of an alias and a component
type whose two functions write `s` differently are read back in the decoder's forms. -/
theorem decode_encode_exRV :
    ∃ σ nt, ((do importDecls exRV; exportDecls [] : TM Unit)).run { share := true, nom := [] } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf exRVBack [], nt) := by
  obtain ⟨σ, nt, hr, hd, -⟩ := decode_encode_refVal exRV_ok .nil
  rw [exRV_back] at hd
  exact ⟨σ, nt, hr, hd⟩

end DecodeRefVal

end Silmaril.Wasm.Wac.Bridge
