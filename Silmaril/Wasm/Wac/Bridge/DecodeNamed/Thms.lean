module

public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeAnonIface.Thms
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeNamed.Bytes

/-!
# WAC bridge: decoding inverts encoding on the named fragment

`Bridge.DecodeAnonIface.decode_encode_anon_iface` proves `decode ∘ encode = id` for
packages of functions over anonymous value types and interfaces of them. This module
extends it to the fragment `DecodeNamed.EsOk` (`Bridge.DecodeNamed.Defs`): named type
references and handles (`own`, `borrow`, the encoder's caches `hcache` and `resIdx`),
records, variants, enums and flags (the nominal table `N`), type items, resources and
resource aliases, and instances and components nested arbitrarily.

* `decode_encode_named`: the declarations the encoder writes for the imports `is` and
  exports `es` (in a sharing scope with nominal table `N`, as for a package's component
  type) are read back by `pkgOfWorld` as the package `pkgOf (dks is) (dks es)`: the same
  items, each instance and component with the interface identifier its name carries
  (`dk`), type exports as definitions; every nominal definition the decoder records is
  `N`'s (`N.lookup n = some d`);
* `decode_encode_named_id`: when the identifiers already are those (`dks is = is`,
  `dks es = es`), exactly the items;
* `decodePkg_world`: **the byte level** for WIT world packages: for the binary of the
  WIT package of such a world (`Wit.Project.worldPackage`, `Component.Binary.encode`),
  `decodePkg` itself (`Component.Binary.parse`, `Wit.Project.projectI`, `pkgOfWorld`)
  returns the world as the package's one definition;
* `esOk_of_items2`, `dks_of_items2`: the fragment contains that of
  `decode_encode_anon_iface`, and `dks` agrees with its `fixEx` there.

The simulation is in `Silmaril/Proofs/Wasm/Wac/Bridge/DecodeNamed/`. **Not covered**: value
items (`(value …)`), types of one interface used in another (`use`, which the encoder
cannot write), a reference to a resource by `ref` (it decodes as `own`), alias type
items of resource aliases, the byte level of component (rather than WIT package)
binaries, and type sharing as wac does it (by identity; see the bridge in `docs/projects/wasm-components.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)
open DecodeIface (fixK fixEx)
open DecodeAnon (Anon AnonSig AnonFns)
open DecodeAnonIface (Item2 Items2)

namespace DecodeNamed

/-- **Decoding inverts encoding** on packages of the named fragment. -/
theorem decode_encode_named {N : NomTable} {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) :
    ∃ σ nt, ((do importDecls is; exportDecls es : TM Unit)).run { share := true, nom := N } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf (dks is) (dks es), nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, δ', hr, hdec, hn⟩ := decls_encode (δ := {}) true his hes rfl (fun _ h => absurd h (by simp))
  refine ⟨σ, δ'.nom, hr, ?_, hn⟩
  simp only [pkgOfWorld, hdec, pkgOf, DecodeEnc.ok_bind, DecodeEnc.pure_ok, Except.ok.injEq, Prod.mk.injEq,
    and_true]
  congr 1

/-- **`decode ∘ encode = id`** on packages of the named fragment whose instances and
components carry the identifiers of their names. -/
theorem decode_encode_named_id {N : NomTable} {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) (hi : dks is = is) (he : dks es = es) :
    ∃ σ nt, ((do importDecls is; exportDecls es : TM Unit)).run { share := true, nom := N } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf is es, nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨σ, nt, h1, h2, h3⟩ := decode_encode_named his hes
  exact ⟨σ, nt, h1, by rw [h2, hi, he], h3⟩

/-- **The byte level** for WIT world packages: `decodePkg` reads the binary of the WIT
package of a world of the fragment back as the world. -/
theorem decodePkg_world {N : NomTable} {is es : Externs} (his : EsOk N [] is)
    (hes : EsOk N (extend [] is) es) (id name : String) :
    ∃ σ, ((do importDecls is; exportDecls es : TM Unit)).run { nom := N } = .ok ((), σ) ∧
      ∀ b, Component.Binary.encode (Wit.Project.worldPackage id name σ.decls) = some b →
        ∃ nt, decodePkg b = .ok (worldPkg name id (dks is) (dks es), nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 :=
  decodePkg_worldPackage his hes id name

/-! ## The earlier fragments -/

theorem tyOk_of_anon {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : Anon t) : TyOk Γ t := by
  induction h with
  | prim p => exact .prim p
  | list _ ih => exact .list ih
  | fixedList n _ ih => exact .fixedList n ih
  | map _ _ ihk ihv => exact .map ihk ihv
  | option _ ih => exact .option ih
  | result _ _ iha ihb => exact .result iha ihb
  | tuple _ ih => exact .tuple ih
  | future _ ih => exact .future ih
  | stream _ ih => exact .stream ih

theorem sigOk_of_anon {Γ : Ctx} {s : Sig} (h : AnonSig s) : SigOk Γ s :=
  ⟨fun p hp => tyOk_of_anon (h.1 p hp), fun t ht => tyOk_of_anon (h.2 t ht)⟩

theorem esOk_of_anonFns {N : NomTable} {Γ : Ctx} : ∀ {es : Externs}, AnonFns es → EsOk N Γ es
  | [], _ => .nil
  | (n, k) :: es, h => by
    obtain ⟨s, hk, hs⟩ := h (n, k) List.mem_cons_self
    have ih : EsOk N Γ es := esOk_of_anonFns fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [show k = .func s from hk]
    exact .func (sigOk_of_anon hs) ih

/-- The fragment of `DecodeAnonIface.decode_encode_anon_iface` is contained in this one. -/
theorem esOk_of_items2 {N : NomTable} {Γ : Ctx} : ∀ {es : Externs}, Items2 es → EsOk N Γ es
  | [], _ => .nil
  | (n, k) :: es, h => by
    have ih : EsOk N Γ es := esOk_of_items2 fun p hp => h p (List.mem_cons_of_mem _ hp)
    rcases h (n, k) List.mem_cons_self with ⟨s, hk, hs⟩ | ⟨i, fs, hk, hfs⟩
    · rw [show k = .func s from hk]
      exact .func (sigOk_of_anon hs) ih
    · rw [show k = .inst i fs from hk]
      exact .inst (esOk_of_anonFns hfs) ih

theorem dks_of_anonFns : ∀ {es : Externs}, AnonFns es → dks es = es
  | [], _ => rfl
  | (n, k) :: es, h => by
    obtain ⟨s, hk, -⟩ := h (n, k) List.mem_cons_self
    have ih : dks es = es := dks_of_anonFns fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [show k = .func s from hk]
    simp [dks, dk, ih]

/-- On that fragment, `dks` is `DecodeIface.fixEx`. -/
theorem dks_of_items2 : ∀ {es : Externs}, Items2 es → dks es = fixEx es
  | [], _ => rfl
  | (n, k) :: es, h => by
    have ih : dks es = fixEx es := dks_of_items2 fun p hp => h p (List.mem_cons_of_mem _ hp)
    rcases h (n, k) List.mem_cons_self with ⟨s, hk, -⟩ | ⟨i, fs, hk, hfs⟩
    · rw [show k = .func s from hk]
      simp [dks, dk, ih, fixEx, fixK]
    · rw [show k = .inst i fs from hk]
      simp [dks, dk, ih, fixEx, fixK, dks_of_anonFns hfs]

/-! ## An example outside the earlier fragments -/

/-- A resource `r`, a record type `point` (from the nominal table), and a function
`f : (x : borrow<r>, p : point) -> own<r>`. -/
def exNom : NomTable := [("point", .record [("x", .prim .u32), ("y", .prim .u32)])]

def exItems : Externs :=
  [("r", .type (.resource "r")), ("point", .type (.value (.ref ⟨.local, "point"⟩))),
   ("f", .func { async := false, params := [("x", .borrow ⟨.local, "r"⟩), ("p", .ref ⟨.local, "point"⟩)],
                 result := some (.own ⟨.local, "r"⟩) })]

theorem exItems_ok : EsOk exNom [] exItems := by
  refine .res (.tyNom rfl rfl ?_ (.func ⟨?_, ?_⟩ .nil))
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact .prim _
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .borrowRes rfl
    · exact .refVal rfl
  · intro t ht
    cases ht
    exact .own rfl

/-- `decode_encode_named` applies to `exItems`, which uses a resource, handles and a
record; the earlier fragments contain none of them. -/
theorem decode_encode_exItems :
    ∃ σ nt, ((do importDecls exItems; exportDecls [] : TM Unit)).run { share := true, nom := exNom } =
        .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok (pkgOf exItems [], nt) ∧ ∀ p ∈ nt, exNom.lookup p.1 = some p.2 :=
  decode_encode_named_id exItems_ok .nil rfl rfl

end DecodeNamed

end Silmaril.Wasm.Wac.Bridge
