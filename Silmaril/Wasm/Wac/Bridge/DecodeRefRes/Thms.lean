module

public import Silmaril.Wasm.Wac.Bridge.DecodeRefRes.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeRefRes
public import Silmaril.Wasm.Wac.Bridge.DecodeImpl.Thms

/-!
# WAC bridge: `decode ∘ encode` with type items `type n = a` of a resource `a`

The package's own items (imports `is`, exports `es`) may write an alias of a resource as
`ref a` (`fixR` turns it into the fragment's `own<a>`); items inside instances and
components still follow `DecodeNamed.EsOk`.

* `run_fixR`: the encoder writes `(is, es)` exactly as it writes their fixed forms
  `(fixR [] is, fixR Γ₁ es)`, `Γ₁` the context after the fixed imports, in either
  sharing mode;
* `decode_encode_refRes`: so `pkgOfWorld` reads them back as `pkgOf` of `dks` of the fixed
  forms: an alias written `ref a` of a resource comes back as `own<a>`;
* `decodePkg_world_refRes` and `decodePkg_impl_refRes`: the same at the byte level, for
  the WIT package of the world and for component binaries;
* `exR_fix`, `decode_encode_exR`: an example, `type r2 = r` of a resource `r`.

**Not covered**: `ref a` of a resource as a value type (in a function's parameters or
results, or inside other types), and alias type items inside nested instances and
components: there the encoder's caches of function, instance and component types are
keyed by the types as written, and the invariant of `Bridge.DecodeNamed` relates each
cached type to the type the decoder reads, which would no longer be the same.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open DecodeNamed

namespace DecodeRefRes

/-- **The encoder writes a package as its fixed form.** -/
theorem run_fixR {N : NomTable} (b : Bool) {is es : Externs} (his : EsOk N [] (fixR [] is))
    (hes : EsOk N (extend [] (fixR [] is)) (fixR (extend [] (fixR [] is)) es)) :
    ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } =
      ((do importDecls (fixR [] is); exportDecls (fixR (extend [] (fixR [] is)) es) : TM Unit)).run
        { share := b, nom := N } := by
  have hm0 := m_start N b (δ := {}) rfl (fun _ h => absurd h (by simp))
  obtain ⟨σ1, E, δ1, hr1, -, hm1, -⟩ := (esOk_sim his _ _ hm0).1
  have hi := (fixR_run is [] _ _ his hm0).1
  simp only [StateT.run_bind, hi, hr1]
  exact (fixR_run es _ σ1 δ1 hes hm1).2

/-- **Decoding inverts encoding up to `fixR`.** -/
theorem decode_encode_refRes {N : NomTable} {is es : Externs} (his : EsOk N [] (fixR [] is))
    (hes : EsOk N (extend [] (fixR [] is)) (fixR (extend [] (fixR [] is)) es)) :
    ∃ σ nt, ((do importDecls is; exportDecls es : TM Unit)).run { share := true, nom := N } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf (dks (fixR [] is)) (dks (fixR (extend [] (fixR [] is)) es)), nt) ∧
      ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  rw [run_fixR true his hes]
  exact decode_encode_named his hes

/-- **The byte level for the WIT package of the world**, up to `fixR`. -/
theorem decodePkg_world_refRes {N : NomTable} {is es : Externs} (his : EsOk N [] (fixR [] is))
    (hes : EsOk N (extend [] (fixR [] is)) (fixR (extend [] (fixR [] is)) es)) (id name : String) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { nom := N } = .ok ((), σ) ∧
      ∀ b, Component.Binary.encode (Wit.Project.worldPackage id name σ.decls) = some b →
        ∃ nt, decodePkg b = .ok (worldPkg name id (dks (fixR [] is))
            (dks (fixR (extend [] (fixR [] is)) es)), nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  rw [run_fixR false his hes]
  exact decodePkg_world his hes id name

/-- **The byte level for component binaries**, up to `fixR`. -/
theorem decodePkg_impl_refRes {N : NomTable} (b : Bool) {is es : Externs} (his : EsOk N [] (fixR [] is))
    (hes : EsOk N (extend [] (fixR [] is)) (fixR (extend [] (fixR [] is)) es)) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      ∀ (c : Ast) (bytes : ByteArray), DecodeImpl.Implements c σ.decls →
        Component.Binary.encode c = some bytes →
        ∃ nt, decodePkg bytes = .ok (pkgOf (dks (fixR [] is)) (dks (fixR (extend [] (fixR [] is)) es)), nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  rw [run_fixR b his hes]
  exact DecodeImpl.decodePkg_impl b his hes

/-! ## An example -/

/-- A resource `r` and `type r2 = r`, written as a reference. -/
def exRImports : Externs :=
  [("r", .type (.resource "r")), ("r2", .type (.value (.ref ⟨.local, "r"⟩)))]

/-- A function over `borrow<r2>`. -/
def exRExports : Externs :=
  [("f", .func { async := false, params := [("x", .borrow ⟨.local, "r2"⟩)], result := none })]

theorem exR_fix : fixR [] exRImports =
    [("r", .type (.resource "r")), ("r2", .type (.value (.own ⟨.local, "r"⟩)))] := by
  decide +kernel

theorem exR_fix_exports : fixR (extend [] (fixR [] exRImports)) exRExports = exRExports := by
  decide +kernel

theorem exR_ok : EsOk [] [] (fixR [] exRImports) ∧
    EsOk [] (extend [] (fixR [] exRImports)) (fixR (extend [] (fixR [] exRImports)) exRExports) := by
  rw [exR_fix_exports, exR_fix]
  refine ⟨.res (.tyOwn rfl .nil), .func ⟨?_, ?_⟩ .nil⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact .borrowAlias rfl
  · intro t ht
    cases ht

/-- `type r2 = r` written as a reference is read back as `own<r>`. -/
theorem decode_encode_exR :
    ∃ σ nt, ((do importDecls exRImports; exportDecls exRExports : TM Unit)).run { share := true, nom := [] } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf [("r", .type (.resource "r")), ("r2", .type (.value (.own ⟨.local, "r"⟩)))]
        exRExports, nt) := by
  obtain ⟨σ, nt, hr, hd, -⟩ := decode_encode_refRes exR_ok.1 exR_ok.2
  rw [exR_fix_exports, exR_fix] at hd
  exact ⟨σ, nt, hr, hd⟩

end DecodeRefRes

end Silmaril.Wasm.Wac.Bridge
