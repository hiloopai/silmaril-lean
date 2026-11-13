module

public import Silmaril.Wasm.Component.Algebra.Equiv.Defs
public import Silmaril.Wasm.Component.Env.Thms

/-!
# Equivalence of components: theorems

* `CompEquiv` is an equivalence relation (`compSetoid C`), `CompRefines` a preorder
  whose symmetric part is `CompEquiv` (`compEquiv_iff_refines`);
* a component traps outside its interface: `maskH_comp_denU`, `denU_comp_maskH`;
* the boundary handlers compose to a mask: `narrowH_comp_widenH`; hence
  `denU_eq_atIface`: the strategy of a component over `sigU` is its strategy at the
  interface, widened back to `sigU`;
* **the interface and the denotational notions agree**: `ifaceEquiv_iff`,
  `ifaceRefines_iff`.
-/

public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

/-! ## Equivalence relations -/

section
variable {M : Type}

theorem SameSizes.refl (c : Comp M) : SameSizes c c := ⟨rfl, rfl⟩

theorem SameSizes.symm {c c' : Comp M} (h : SameSizes c c') : SameSizes c' c :=
  ⟨h.1.symm, h.2.symm⟩

theorem SameSizes.trans {c₁ c₂ c₃ : Comp M} (h₁ : SameSizes c₁ c₂) (h₂ : SameSizes c₂ c₃) :
    SameSizes c₁ c₃ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

end

variable {M : Type} [CoreModule M]

theorem CompEquiv.refl (C : CoreSem M) (c : Comp M) : CompEquiv C c c := ⟨.refl c, rfl⟩

theorem CompEquiv.symm {C : CoreSem M} {c c' : Comp M} (h : CompEquiv C c c') :
    CompEquiv C c' c := ⟨h.1.symm, h.2.symm⟩

theorem CompEquiv.trans {C : CoreSem M} {c₁ c₂ c₃ : Comp M} (h₁ : CompEquiv C c₁ c₂)
    (h₂ : CompEquiv C c₂ c₃) : CompEquiv C c₁ c₃ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Denotational equivalence as a setoid. -/
def compSetoid (C : CoreSem M) : Setoid (Comp M) where
  r := CompEquiv C
  iseqv := ⟨CompEquiv.refl C, CompEquiv.symm, CompEquiv.trans⟩

theorem CompRefines.refl (C : CoreSem M) (c : Comp M) : CompRefines C c c := ⟨.refl c, le_rfl⟩

theorem CompRefines.trans {C : CoreSem M} {c₁ c₂ c₃ : Comp M} (h₁ : CompRefines C c₁ c₂)
    (h₂ : CompRefines C c₂ c₃) : CompRefines C c₁ c₃ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem CompEquiv.refines {C : CoreSem M} {c c' : Comp M} (h : CompEquiv C c c') :
    CompRefines C c c' := ⟨h.1, h.2.le⟩

/-- Equivalence is refinement both ways. -/
theorem compEquiv_iff_refines {C : CoreSem M} {c c' : Comp M} :
    CompEquiv C c c' ↔ CompRefines C c c' ∧ CompRefines C c' c :=
  ⟨fun h => ⟨h.refines, h.symm.refines⟩, fun h => ⟨h.1.1, le_antisymm h.1.2 h.2.2⟩⟩

theorem ParEquiv.refl (c : Comp M) : ParEquiv c c := fun C => .refl C c

theorem ParEquiv.symm {c c' : Comp M} (h : ParEquiv c c') : ParEquiv c' c :=
  fun C => (h C).symm

theorem ParEquiv.trans {c₁ c₂ c₃ : Comp M} (h₁ : ParEquiv c₁ c₂) (h₂ : ParEquiv c₂ c₃) :
    ParEquiv c₁ c₃ := fun C => (h₁ C).trans (h₂ C)

theorem IfaceEquiv.refl (C : CoreSem M) (c : Comp M) : IfaceEquiv C c c := ⟨.refl c, rfl⟩

/-! ## A component traps outside its interface -/

/-- Masking the imports below a component does not change it. -/
theorem maskH_comp_denU (C : CoreSem M) (c : Comp M) :
    (Strategy.ofHandler (maskH c.imports.length)).comp (c.denU C) = c.denU C := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [Comp.imports_mk, Comp.denU]
  rw [← Strategy.comp_assoc, denNodes_comp, ← Strategy.ofHandler_comp, maskH_comp_maskH]

/-- Masking the exports above a component does not change it. -/
theorem denU_comp_maskH (C : CoreSem M) (c : Comp M) :
    (c.denU C).comp (Strategy.ofHandler (maskH c.exports.length)) = c.denU C := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [Comp.exports_mk, Comp.denU]
  rw [Strategy.comp_assoc, ← Strategy.ofHandler_comp, ← List.length_map (f := Export.impl),
    exportsH_comp_maskH' ]
where
  exportsH_comp_maskH' : ∀ (e : Nat) (xs : List Export),
      (exportsH e xs).comp (maskH (xs.map Export.impl).length) = exportsH e xs := by
    intro e xs
    rw [List.length_map]
    exact exportsH_comp_maskH e xs

/-- The boundary `sigU → sigN n → sigU` is the mask of the first `n` functions. -/
theorem narrowH_comp_widenH (n : Nat) : (narrowH n).comp (widenH n) = maskH n := by
  funext q
  simp only [Handler.comp, widenH, maskH, Target.prog]
  by_cases hq : q.1 < n
  · simp only [hq, ↓reduceDIte, ↓reduceIte, Prog.interp_call, narrowH]
    rfl
  · simp only [hq, ↓reduceDIte, ↓reduceIte, Prog.interp_pure]

/-- The strategy of a component is its strategy at the interface, widened to `sigU`. -/
theorem denU_eq_atIface (C : CoreSem M) (c : Comp M) :
    c.denU C = ((Strategy.ofHandler (narrowH c.imports.length)).comp
      (atIface C c.imports.length c.exports.length c)).comp
        (Strategy.ofHandler (widenH c.exports.length)) := by
  have hb : ∀ n : Nat, (Strategy.ofHandler (narrowH n)).comp (Strategy.ofHandler (widenH n)) =
      Strategy.ofHandler (maskH n) := fun n => by
    rw [← Strategy.ofHandler_comp, narrowH_comp_widenH]
  simp only [atIface, atSizes, Strategy.comp_assoc]
  rw [← Strategy.comp_assoc (Strategy.ofHandler (narrowH _)), hb, hb, ← Strategy.comp_assoc,
    maskH_comp_denU, denU_comp_maskH]

/-! ## Interface and denotational notions agree -/

/-- **Behavioural equivalence at the interface is denotational equivalence.** -/
theorem ifaceEquiv_iff {C : CoreSem M} {c c' : Comp M} :
    IfaceEquiv C c c' ↔ CompEquiv C c c' := by
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨hs, ?_⟩
    rw [denU_eq_atIface C c, denU_eq_atIface C c', he, hs.1, hs.2]
  · rintro ⟨hs, he⟩
    exact ⟨hs, by simp only [atIface, he]⟩

/-- **Refinement at the interface is refinement.** -/
theorem ifaceRefines_iff {C : CoreSem M} {c c' : Comp M} :
    IfaceRefines C c c' ↔ CompRefines C c c' := by
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨hs, ?_⟩
    rw [denU_eq_atIface C c, denU_eq_atIface C c', ← hs.1, ← hs.2]
    exact Strategy.comp_mono (Strategy.comp_mono le_rfl he) le_rfl
  · rintro ⟨hs, he⟩
    exact ⟨hs, Strategy.comp_mono (Strategy.comp_mono le_rfl he) le_rfl⟩

end Silmaril.Wasm.Component.Algebra
