module

public import Silmaril.Wasm.Wac.Bridge.DecodeValue.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeValue

/-!
# WAC bridge: `decode ∘ encode` with value items

* `decode_encode_value`: `DecodeNamed.decode_encode_named` on the fragment with value
  items `EsOkV` (`esOkV_of_esOk`: it contains the named fragment): `pkgOfWorld` reads the
  encoder's declarations back as `pkgOf (dks is) (dks es)`, values as values;
* `decodePkg_implV`: the byte level for component binaries (`DecodeImpl.Implements`) on
  that fragment;
* `decodePkg_exValue`: non-vacuity, a package importing a value of a record type and
  exporting a value of a list type, decoded from any shell of its declarations.

The proofs are in `Silmaril/Proofs/Wasm/Wac/Bridge/DecodeValue.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normComponentDecls)
open DecodeNamed
open DecodeImpl (Implements shell shellOk)

namespace DecodeValue

/-- **Decoding inverts encoding** on packages with value items. -/
theorem decode_encode_value {N : NomTable} {is es : Externs} (his : EsOkV N [] is)
    (hes : EsOkV N (extend [] is) es) :
    ∃ σ nt, ((do importDecls is; exportDecls es : TM Unit)).run { share := true, nom := N } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf (dks is) (dks es), nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, δ', hr, hdec, hn⟩ := decls_encodeL (δ := {}) true (esOkV_sim his) (esOkV_sim hes) rfl
    (fun _ h => absurd h (by simp))
  refine ⟨σ, δ'.nom, hr, ?_, hn⟩
  simp only [pkgOfWorld, hdec, pkgOf, DecodeEnc.ok_bind, DecodeEnc.pure_ok]
  rfl

/-- **The byte level for component binaries**, with value items. -/
theorem decodePkg_implV {N : NomTable} (b : Bool) {is es : Externs} (his : EsOkV N [] is)
    (hes : EsOkV N (extend [] is) es) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      ∀ (c : Ast) (bytes : ByteArray), Implements c σ.decls → Component.Binary.encode c = some bytes →
        ∃ nt, decodePkg bytes = .ok (pkgOf (dks is) (dks es), nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, δ', hr, hdec, hn⟩ := decls_encodeL (δ := {}) b (esOkV_sim his) (esOkV_sim hes) rfl
    (fun _ h => absurd h (by simp))
  refine ⟨σ, hr, fun c bytes hc hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse bytes = .ok c := Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (DecodeImpl.project_impl hc)
  have hdec' : (decCDecls (normComponentDecls σ.decls) [] []).run {} = .ok ((dks is, dks es), δ') := by
    rw [decCDecls_norm]; exact hdec
  simp only [decodePkg, hp, DecodeEnc.pure_ok, DecodeEnc.ok_bind, hw]
  simp only [pkgOfWorld, hdec', DecodeEnc.ok_bind, DecodeEnc.pure_ok, pkgOf]
  rfl

/-! ## An example with values -/

/-- A record `point` (from `exNom`), an imported value of it, and an exported value of
`list<u8>`. -/
def exVImports : Externs :=
  [("point", .type (.value (.ref ⟨.local, "point"⟩))), ("origin", .value (.ref ⟨.local, "point"⟩))]

def exVExports : Externs := [("bytes", .value (.list (.prim .u8)))]

theorem exV_ok : EsOkV exNom [] exVImports ∧ EsOkV exNom (extend [] exVImports) exVExports := by
  refine ⟨.tyNom rfl rfl ?_ (.value (.refVal rfl) .nil), .value (.list (.prim _)) .nil⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> exact .prim _

theorem exV_shellOk :
    (((do importDecls exVImports; exportDecls exVExports : TM Unit)).run { nom := exNom }).toOption.map
      (fun p => p.2.decls.all shellOk) = some true := by
  decide +kernel

/-- **Non-vacuity**: any shell of the declarations of `exVImports`/`exVExports`, with any
code, decodes back to them, values included. -/
theorem decodePkg_exValue :
    ∃ σ, ((do importDecls exVImports; exportDecls exVExports : TM Unit)).run { nom := exNom } = .ok ((), σ) ∧
      ∀ (code : List Section), (∀ c ∈ code, Wit.Project.isCode c = true) →
        ∀ bytes, Component.Binary.encode (shell code σ.decls) = some bytes →
          ∃ nt, decodePkg bytes = .ok (pkgOf exVImports exVExports, nt) ∧
            ∀ p ∈ nt, exNom.lookup p.1 = some p.2 := by
  obtain ⟨σ, hr, h⟩ := decodePkg_implV false exV_ok.1 exV_ok.2
  have hs : σ.decls.all shellOk = true := by
    have e := exV_shellOk
    rw [hr] at e
    change some (σ.decls.all shellOk) = some true at e
    exact Option.some.inj e
  exact ⟨σ, hr, fun code hc bytes hb => h _ bytes (DecodeImpl.implements_shell hc hs) hb⟩

end DecodeValue

end Silmaril.Wasm.Wac.Bridge
