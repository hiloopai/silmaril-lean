module

public import Silmaril.Wasm.Wac.Bridge.DecodeImpl.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeImpl

/-!
# WAC bridge: `decodePkg` on component (implementation) binaries

* `decodePkg_impl`: **the byte level for components**: encode the imports `is` and
  exports `es` of the named fragment (either sharing mode) as declarations `σ.decls`. Any
  component `c` whose sections declare exactly these declarations among silent ones
  (`Implements c σ.decls`: code, instantiations, aliases of functions, custom sections
  anywhere; exports of arbitrary items with these types), once encoded to bytes, is read
  back by `decodePkg` as the package `pkgOf (dks is) (dks es)`, the same as the package's
  component type (`DecodeNamed.decode_encode_named`). The projection does not need type
  inference here (`project_impl`, `Wit.Project.projectI_of_project`).
* `implements_shell`: a shell, code followed by one section per declaration
  (`shell`), implements its declarations when they are imports, exports and non-resource
  type definitions (`shellOk`).
* `decodePkg_exShell`: non-vacuity: for `DecodeNamed.exItems` (a resource, a record and a
  function over handles) the encoder's declarations are of that kind, so any shell of
  them with any code decodes back to `exItems`.

**Not covered**: components whose world the projection only finds by type inference
(exports without ascription other than types, aliases of exports of created instances),
components that define resources, and the relation of the shell's code to the world
(nothing here says the code implements the functions).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normComponentDecls)
open DecodeNamed

namespace DecodeImpl

/-- **The byte level for component binaries** that implement a package of the fragment. -/
theorem decodePkg_impl {N : NomTable} (b : Bool) {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      ∀ (c : Ast) (bytes : ByteArray), Implements c σ.decls → Component.Binary.encode c = some bytes →
        ∃ nt, decodePkg bytes = .ok (pkgOf (dks is) (dks es), nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, δ', hr, hdec, hn⟩ := decls_encode (N := N) b his hes (δ := {}) rfl
    (fun _ h => absurd h (by simp))
  refine ⟨σ, hr, fun c bytes hc hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse bytes = .ok c := Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (project_impl hc)
  have hdec' : (decCDecls (normComponentDecls σ.decls) [] []).run {} = .ok ((dks is, dks es), δ') := by
    rw [decCDecls_norm]; exact hdec
  simp only [decodePkg, hp, DecodeEnc.pure_ok, DecodeEnc.ok_bind, hw]
  simp only [pkgOfWorld, hdec', DecodeEnc.ok_bind, DecodeEnc.pure_ok, pkgOf]
  rfl

/-- The shell form of `decodePkg_impl`. -/
theorem decodePkg_shell {N : NomTable} (b : Bool) {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      ∀ (code : List Section), (∀ c ∈ code, Wit.Project.isCode c = true) → σ.decls.all shellOk = true →
        ∀ bytes, Component.Binary.encode (shell code σ.decls) = some bytes →
          ∃ nt, decodePkg bytes = .ok (pkgOf (dks is) (dks es), nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, hr, h⟩ := decodePkg_impl b his hes
  exact ⟨σ, hr, fun code hc hs bytes hb => h _ bytes (implements_shell hc hs) hb⟩

/-- The encoder's declarations for `exItems` are covered by `shellOk`. -/
theorem exItems_shellOk :
    (((do importDecls exItems; exportDecls [] : TM Unit)).run { share := true, nom := exNom }).toOption.map
      (fun p => p.2.decls.all shellOk) = some true := by
  decide +kernel

/-- **Non-vacuity**: any shell of `exItems`' declarations, with any code, decodes back to
`exItems`. -/
theorem decodePkg_exShell :
    ∃ σ, ((do importDecls exItems; exportDecls [] : TM Unit)).run { share := true, nom := exNom } = .ok ((), σ) ∧
      ∀ (code : List Section), (∀ c ∈ code, Wit.Project.isCode c = true) →
        ∀ bytes, Component.Binary.encode (shell code σ.decls) = some bytes →
          ∃ nt, decodePkg bytes = .ok (pkgOf exItems [], nt) ∧ ∀ p ∈ nt, exNom.lookup p.1 = some p.2 := by
  obtain ⟨σ, hr, h⟩ := decodePkg_shell true exItems_ok .nil
  have hs : σ.decls.all shellOk = true := by
    have e := exItems_shellOk
    rw [hr] at e
    change some (σ.decls.all shellOk) = some true at e
    exact Option.some.inj e
  exact ⟨σ, hr, fun code hc bytes hb => h code hc hs bytes hb⟩

end DecodeImpl

end Silmaril.Wasm.Wac.Bridge
