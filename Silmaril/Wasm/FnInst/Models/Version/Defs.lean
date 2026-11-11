module

public import Silmaril.Wasm.FnInst.Models.Inst.Defs
public import Mathlib.Order.Basic

/-!
# The language version in the signature

A **versioned** body language (`Versioned L V`) says which bodies a version `v` of a preorder `V`
allows (`Uses b v`), monotonically in `v` and independently of call indices. For Wasm, `V` is
the `FeatureSet` lattice and the named versions 1.0, 2.0, 3.0, Lime1 and WasmFX are points of it
(`Silmaril.Wasm.Models.Features`; the fragment instance is in `Frag`).

* `VSig U`: a version and a signature; `VSig.Hom`: a signature morphism *and* an inclusion of
  versions;
* `vInst S U`: sentences over `(v, T)` are the sentences whose bodies `v` allows; models are the
  partial modules of `bodyInst` (the semantics does not depend on the version). This is the
  *syntax-only* variant: a version restricts what can be written, not how the context behaves;
* `forget S U : vInst S U → bodyInst S`: forget the version (a comorphism).

The *context-restricting* variant gives each version a set of admissible behaviours `Adm v` of
the other functions (what a function written in `v` can do), and reads sentences over the
environments of admissible behaviours (`AdmValid`). It is not an institution along version
inclusions (a model of the bigger version has no reduct to the smaller one); `Thms` proves the
transfer that does hold (downwards) and `Frag.Thms` refutes the other direction.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models

open CategoryTheory Silmaril.Inst

/-- A body language whose bodies are allowed or not at each version. -/
structure Versioned (L : FnSyntax) (V : Type) [Preorder V] where
  /-- Version `v` allows body `b`. -/
  Uses : ∀ {n : ℕ}, L.Body n → V → Prop
  uses_mono : ∀ {n : ℕ} {b : L.Body n} {v w : V}, v ≤ w → Uses b v → Uses b w
  uses_rename : ∀ {n m : ℕ} (f : Fin n → Fin m) (b : L.Body n) (v : V),
    Uses (L.rename f b) v ↔ Uses b v

variable {L : FnSyntax} {V : Type} [Preorder V]

/-- A version allows a sentence when it allows all its bodies. -/
def Sen.Uses (U : Versioned L V) {n : ℕ} : Sen L n → V → Prop
  | .eq b b', v => U.Uses b v ∧ U.Uses b' v
  | .and φ ψ, v => Sen.Uses U φ v ∧ Sen.Uses U ψ v

theorem Sen.uses_mono (U : Versioned L V) {n : ℕ} {v w : V} (h : v ≤ w) :
    ∀ {φ : Sen L n}, φ.Uses U v → φ.Uses U w
  | .eq _ _, ⟨hb, hb'⟩ => ⟨U.uses_mono h hb, U.uses_mono h hb'⟩
  | .and _ _, ⟨hφ, hψ⟩ => ⟨Sen.uses_mono U h hφ, Sen.uses_mono U h hψ⟩

theorem Sen.uses_map (U : Versioned L V) {n m : ℕ} (f : Fin n → Fin m) {v : V} :
    ∀ {φ : Sen L n}, φ.Uses U v → (φ.map f).Uses U v
  | .eq _ _, ⟨hb, hb'⟩ => ⟨(U.uses_rename f _ v).2 hb, (U.uses_rename f _ v).2 hb'⟩
  | .and _ _, ⟨hφ, hψ⟩ => ⟨Sen.uses_map U f hφ, Sen.uses_map U f hψ⟩

/-- A versioned signature. -/
structure VSig (L : FnSyntax) (V : Type) where
  /-- The language version. -/
  ver : V
  /-- The signature. -/
  sig : Sig L

/-- A morphism of versioned signatures: a version inclusion and a signature morphism. -/
structure VSig.Hom (A B : VSig L V) where
  le : PLift (A.ver ≤ B.ver)
  h : Sig.Hom A.sig B.sig

/-- The identity morphism of versioned signatures. -/
def VSig.Hom.id (A : VSig L V) : VSig.Hom A A := ⟨⟨le_rfl⟩, Sig.Hom.id A.sig⟩

/-- Composition of morphisms of versioned signatures. -/
def VSig.Hom.comp {A B C : VSig L V} (σ : VSig.Hom A B) (τ : VSig.Hom B C) : VSig.Hom A C :=
  ⟨⟨le_trans σ.le.down τ.le.down⟩, σ.h.comp τ.h⟩

instance : Category (VSig L V) where
  Hom := VSig.Hom
  id := VSig.Hom.id
  comp := VSig.Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The plain presentation of the versioned institution (syntax-only variant). -/
def vPlain (S : FnSem L) (U : Versioned L V) : Plain (VSig L V) where
  Sen T := {φ : Sen L T.sig.n // φ.Uses U T.ver}
  map σ φ := ⟨Sen.map (VSig.Hom.h σ).c.f φ.1,
    Sen.uses_map U _ (Sen.uses_mono U (VSig.Hom.le σ).down φ.2)⟩
  map_id _ φ := Subtype.ext (Sen.map_id φ.1)
  map_comp σ τ φ := Subtype.ext (Sen.map_comp (VSig.Hom.h σ).c.f (VSig.Hom.h τ).c.f φ.1)
  Mod T := PMod T.sig
  reduct σ M := PMod.reduct (VSig.Hom.h σ) M
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M φ := SemSat S (M.den S) φ.1
  sat_map σ M φ := (bodyPlain S).sat_map (VSig.Hom.h σ) M φ.1

/-- The versioned institution (syntax-only variant). -/
abbrev vInst (S : FnSem L) (U : Versioned L V) : Institution₀ := (vPlain S U).toInst

/-- Forgetting versions on signatures. -/
def VSig.forget : VSig L V ⥤ Sig L where
  obj T := T.sig
  map σ := VSig.Hom.h σ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting the version: a comorphism into the fixed-syntax institution. -/
def forget (S : FnSem L) (U : Versioned L V) : Comorphism (vInst S U) (bodyInst S) :=
  Comorphism.ofPlain (P := vPlain S U) (Q := bodyPlain S) VSig.forget (fun _ φ => φ.1)
    (fun _ M => M) (fun _ _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The version inclusion `v ≤ w` at a fixed signature, as a morphism of versioned
signatures. -/
def VSig.up (T : Sig L) {v w : V} (h : v ≤ w) : (⟨v, T⟩ : VSig L V) ⟶ ⟨w, T⟩ :=
  ⟨⟨h⟩, Sig.Hom.id T⟩

/-- Context-restricting reading: `φ` holds in every environment of behaviours admissible at
`v`. -/
def AdmValid (S : FnSem L) (Adm : V → Set S.Den) (v : V) {n : ℕ} (φ : Sen L n) : Prop :=
  ∀ env : Env S n, (∀ i, env i ∈ Adm v) → Sen.Holds S env φ

end Silmaril.Wasm.FnInst.Models
