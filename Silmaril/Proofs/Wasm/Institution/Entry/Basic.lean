module

public import Silmaril.Wasm.Institution.Entry.Defs
public import Silmaril.Wasm.Equiv.Module

@[expose] public section

/-!
# Single-invocation logics: proofs

Validity is `Equiv.ModuleRefines`/`Equiv.ModuleEquiv`; translations along pullbacks of entry
points (lowering), contract closure and equivalence into refinement. Summary in
`Silmaril.Wasm.Institution.Entry.Thms`.
-/

namespace Silmaril.Wasm.Institution.Entry

open CategoryTheory Silmaril.Wasm ObsSemantics

variable {A V S : Type}

theorem refines_flip_eq_iff {X : Set A} {a b : Obj A V X} :
    Refines (fun x y : Behaviour V => y = x) a b ↔ Refines (· = ·) a b :=
  ⟨fun h x vs hok c hc => let ⟨c', hc', e⟩ := h x vs hok c hc; ⟨c', hc', e.symm⟩,
   fun h x vs hok c hc => let ⟨c', hc', e⟩ := h x vs hok c hc; ⟨c', hc', e.symm⟩⟩

theorem equiv_eq_iff {X : Set A} {a b : Obj A V X} :
    Equiv (· = ·) a b ↔ Refines (· = ·) a b ∧ Refines (· = ·) b a :=
  and_congr Iff.rfl refines_flip_eq_iff

/-- `a ⊑_R b` iff `a ⊑_Eq close R b`. -/
theorem refines_close_iff (R : Behaviour V → Behaviour V → Prop) {X : Set A}
    {a b : Obj A V X} : Refines (· = ·) a (close R b) ↔ Refines R a b := by
  constructor
  · intro h x vs hok c hc
    obtain ⟨c', ⟨c'', hc'', r⟩, rfl⟩ := h x vs hok c hc
    exact ⟨c'', hc'', r⟩
  · intro h x vs hok c hc
    exact ⟨c, h x vs hok c hc, rfl⟩

/-- Hiding preserves refinement. -/
theorem Refines.restrict {R : Behaviour V → Behaviour V → Prop} {X Y : Set A} (f : X ⟶ Y)
    {a b : Obj A V Y} (h : Refines R a b) : Refines R (a.restrict f) (b.restrict f) :=
  fun x vs hok => h ⟨x.1, f.le x.2⟩ vs hok

/-- At the full interface, refinement of denotations is `Equiv.ModuleRefines`. -/
theorem refines_den_univ_iff (E : Equiv.EntryPoints S A V) {R : Behaviour V → Behaviour V → Prop}
    {s s' : S} :
    Refines R (den E Set.univ s) (den E Set.univ s') ↔ Equiv.ModuleRefines E R s s' :=
  ⟨fun h a vs hok => h ⟨a, trivial⟩ vs hok, fun h x vs hok => h x.1 vs hok⟩

/-- **Validity of `s ⊑ s'` in the entry refinement logic is `Equiv.ModuleRefines E R`.** -/
theorem valid_entryRef_iff (E : Equiv.EntryPoints S A V) (R : Behaviour V → Behaviour V → Prop)
    (s s' : S) :
    (entryRef E R).Valid ((entryRef E R).leSen Set.univ s s') ↔ Equiv.ModuleRefines E R s s' :=
  ((entryRef E R).valid_leSen_iff _ _ _).trans (refines_den_univ_iff E)

/-- **Validity of `s ⊑ s'` in the entry equivalence logic is `Equiv.ModuleEquiv E R`.** -/
theorem valid_entryEquiv_iff (E : Equiv.EntryPoints S A V)
    (R : Behaviour V → Behaviour V → Prop) (s s' : S) :
    (entryEquiv E R).Valid ((entryEquiv E R).leSen Set.univ s s') ↔
      Equiv.ModuleEquiv E R s s' :=
  ((entryEquiv E R).valid_leSen_iff _ _ _).trans
    (and_congr (refines_den_univ_iff E) (refines_den_univ_iff E))

/-- **Pullback of entry points** (for Binaryen IR: lowering) is a translation. -/
def comapT (E : Equiv.EntryPoints S A V) {S' : Type} (g : S' → S)
    (Le : ∀ X : Set A, Obj A V X → Obj A V X → Prop) :
    Translation (𝟭 (Set A)) (mk (E.comap g) Le) (mk E Le) where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog := g
  sem_den _ _ := rfl
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .le t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := Iff.rfl

/-- **Change of programs**: a map `g : S → S'` with `den E' X (g s) = den E X s` is a
translation of entry logics. -/
def progT (E : Equiv.EntryPoints S A V) {S' : Type} (E' : Equiv.EntryPoints S' A V) (g : S → S')
    (hg : ∀ X s, den E' X (g s) = den E X s)
    (Le : ∀ X : Set A, Obj A V X → Obj A V X → Prop) :
    Translation (𝟭 (Set A)) (mk E Le) (mk E' Le) where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog := g
  sem_den X s := hg X s
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .le t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := Iff.rfl

theorem progT_surjective (E : Equiv.EntryPoints S A V) {S' : Type}
    (E' : Equiv.EntryPoints S' A V) (g : S → S') (hg : ∀ X s, den E' X (g s) = den E X s)
    (Le : ∀ X : Set A, Obj A V X → Obj A V X → Prop) (X : Set A) :
    Function.Surjective ((progT E E' g hg Le).sem X) := fun a => ⟨a, rfl⟩

/-- Contract closure: `R`-refinement into `Eq`-refinement, `t ⊑ u ↦ t ⊑ close R u`. -/
def closeT (E : Equiv.EntryPoints S A V) (R : Behaviour V → Behaviour V → Prop) :
    Translation (𝟭 (Set A)) (entryRef E R) (entryRef E (· = ·)) where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog p := p
  sem_den _ _ := rfl
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .le t (.app R u)
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := refines_close_iff R

/-- Equivalence into refinement: `t ≈ u ↦ t ≐ u`. -/
def equivT (E : Equiv.EntryPoints S A V) :
    Translation (𝟭 (Set A)) (entryEquiv E (· = ·)) (entryRef E (· = ·)) where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog p := p
  sem_den _ _ := rfl
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .eq t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := equiv_eq_iff.symm

theorem comapT_surjective (E : Equiv.EntryPoints S A V) {S' : Type} (g : S' → S)
    (Le : ∀ X : Set A, Obj A V X → Obj A V X → Prop) (X : Set A) :
    Function.Surjective ((comapT E g Le).sem X) := fun a => ⟨a, rfl⟩

theorem closeT_surjective (E : Equiv.EntryPoints S A V) (R : Behaviour V → Behaviour V → Prop)
    (X : Set A) : Function.Surjective ((closeT E R).sem X) := fun a => ⟨a, rfl⟩

theorem equivT_surjective (E : Equiv.EntryPoints S A V) (X : Set A) :
    Function.Surjective ((equivT E).sem X) := fun a => ⟨a, rfl⟩

end Silmaril.Wasm.Institution.Entry
