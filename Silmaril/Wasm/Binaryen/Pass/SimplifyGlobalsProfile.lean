module

public import Silmaril.Wasm.Binaryen.GlobReadProfileRun
public import Silmaril.Wasm.Binaryen.Pass.SimplifyGlobalsSound

@[expose] public section

/-! # SimplifyGlobals preserves observations under every numerical profile

The executable rewrite, eligibility check and typing argument are unchanged.
Instantiation establishes the same immutable-global invariant; the new
bidirectional run correspondence preserves each side's actual numeric choices.
The fold over function bodies then composes arbitrary-profile export equivalence.
-/

namespace Silmaril.Wasm.Binaryen.SimplifyGlobals

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.GlobRead

section instantiation

variable {H : Type} {P : Numerics.Profile}

/-- Corresponding instantiations for a single related function replacement,
using the same arbitrary numerical profile on both sides. -/
theorem instCorr_of_set_profile {lk : GlobalIdx → Option Instr} {M : Module} {g : Nat}
    {cL cR : Func} (hg : M.funcs[g]? = some cL) (hty : cR.type = cL.type)
    (hval : ∀ mt, ModuleOk M mt ↔ ModuleOk { M with funcs := M.funcs.set g cR } mt)
    (hgood : ∀ mi dg ag, GlobRead.PrmOk ⟨lk, mi, dg, ag, cL, cR⟩)
    (hinv : ∀ (s : Store H) xas c, Instantiate P closedHost s M xas c →
      GInv lk c.frame.module c.store) :
    GlobRead.InstCorr_profile (H := H) (P := P) M { M with funcs := M.funcs.set g cR } := by
  refine ⟨fun s xas c _ hi => ?_, fun s xas c' _ hi' => ?_⟩
  · obtain ⟨n₀, c', hi', hfr, hcode, hst, hA⟩ :=
      InlR.instantiate_set hg hty (fun mt h => (hval mt).mp h) hi
    obtain ⟨dg, hSR⟩ := sr_of_alloc (lk := lk) hg hA hst
    exact ⟨c', _, hgood _ _ _, hi', hfr, hcode, hSR, hinv s xas c hi⟩
  · have hlt := (List.getElem?_eq_some_iff.mp hg).1
    have hg' : (M.funcs.set g cR)[g]? = some cR := by simp [hlt]
    have hback : ({ ({ M with funcs := M.funcs.set g cR } : Module) with
        funcs := (M.funcs.set g cR).set g cL } : Module) = M := by
      have : (M.funcs.set g cR).set g cL = M.funcs := by
        rw [List.set_set]
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_set]
        by_cases hj : g = j
        · subst hj; simp [hlt, (List.getElem?_eq_some_iff.mp hg).2]
        · simp [hj]
      cases M
      simp only at this ⊢
      rw [this]
    obtain ⟨n₀, c, hi, hfr, hcode, hst, hA'⟩ :=
      InlR.instantiate_set (M := { M with funcs := M.funcs.set g cR }) hg' hty.symm
        (fun mt h => by
          rw [hback]
          obtain ⟨mt₀, h₀⟩ : ∃ mt₀, ModuleOk M mt₀ := by
            obtain ⟨xtE, xtI, hmt, -⟩ := hi'.valid
            exact ⟨_, (hval _).mpr hmt⟩
          have h₀' := (hval mt₀).mp h₀
          rw [ModuleOk.unique h h₀']
          exact h₀) hi'
    rw [hback] at hi
    obtain ⟨hA, hst'⟩ := InlR.funcAlloc_back hg hty hA' hfr hst
    obtain ⟨dg, hSR⟩ := sr_of_alloc (lk := lk) hg hA hst'
    exact ⟨c, _, hgood _ _ _, hi, hfr.symm, hcode.symm, hSR, hinv s xas c hi⟩

end instantiation

/-- Export equivalence of two layer-D modules under the closed host. -/
abbrev EEqProfile (H : Type) (P : Numerics.Profile) (a b : BModule) : Prop :=
  ExportEquiv (· = ·) P (closedHost (H := H)) a.lower b.lower

/-- **Rewriting one function body** of a valid module whose imports and globals are those
of `m₀` keeps validity and export equivalence under the closed host. -/
theorem step_sound_profile {m₀ m : BModule} (hb : m.base = m₀.base) {g : Nat} {fg : BFunc}
    (hfg : m.funcs[g]? = some fg) (hok : m.Ok) (P : Numerics.Profile)
    (H : Type) : (m.withBody g (exprs m₀ fg.body)).Ok ∧ EEqProfile H P (m.withBody g (exprs m₀ fg.body)) m := by
  obtain ⟨mt₀, hmt₀⟩ := hok
  have hL : m.lower.funcs[g]? = some (fg.mapBody BExpr.lowerList) := by
    simp [BModule.lower, hfg]
  unfold EEqProfile BModule.Ok
  rw [withBody_lower hfg]
  refine ⟨⟨mt₀, step_valid_mt hb hfg hmt₀⟩, GlobRead.exportEquiv_of_instCorr_profile
    (instCorr_of_set_profile (lk := lookup m₀) hL rfl (fun mt => ?_) (fun mi dg ag => ⟨rfl, ?_⟩)
      (fun s xas c hi => ?_))⟩
  · constructor
    · exact step_valid_mt hb hfg
    · intro h'
      have h₀ := step_valid_mt hb hfg hmt₀
      rw [ModuleOk.unique h' h₀]
      exact hmt₀
  · exact exprs_rel m₀ mi fg.body
  · exact inst_ginv (m := m₀) (by simp [BModule.lower, hb]) (by simp [BModule.lower, hb]) hi

theorem EEqProfile.trans {H : Type} {P : Numerics.Profile} {a b c : BModule}
    (h₁ : EEqProfile H P a b) (h₂ : EEqProfile H P b c) : EEqProfile H P a c :=
  ⟨h₁.1.trans (fun _ _ _ x y => x.trans y) h₂.1, h₂.2.trans (fun _ _ _ x y => y.trans x) h₁.2⟩

/-- **SimplifyGlobals is sound**: on a valid module, its output is valid and export
equivalent under the closed host. -/
theorem simplifyGlobals_sound_profile (m : BModule) (hm : m.Ok)
    (P : Numerics.Profile) (H : Type) :
    (simplifyGlobals m).Ok ∧ EEqProfile H P (simplifyGlobals m) m := by
  let F : BFunc → BFunc := fun f => { f with body := exprs m f.body }
  have key : ∀ k, ((List.range k).foldl (stepAt m) m).base = m.base ∧
      (∀ j, ((List.range k).foldl (stepAt m) m).funcs[j]? =
        if j < k then (m.funcs[j]?).map F else m.funcs[j]?) ∧
      ((List.range k).foldl (stepAt m) m).Ok ∧ EEqProfile H P ((List.range k).foldl (stepAt m) m) m := by
    intro k
    induction k with
    | zero =>
      refine ⟨rfl, fun j => by simp, hm, ?_⟩
      exact ⟨ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
        ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range k).foldl (stepAt m) m = mk at ih ⊢
      obtain ⟨hb, hf, hok, he⟩ := ih
      have hk : mk.funcs[k]? = m.funcs[k]? := by rw [hf]; simp
      unfold stepAt
      cases hmk : mk.funcs[k]? with
      | none =>
        refine ⟨hb, fun j => ?_, hok, he⟩
        rw [hf j]
        by_cases hj : j < k
        · simp [hj, show j < k + 1 by omega]
        · by_cases hjk : j = k
          · subst hjk
            rw [← hk, hmk]
            simp
          · simp [hj, show ¬ j < k + 1 by omega]
      | some fk =>
        have hfk : m.funcs[k]? = some fk := by rw [← hk, hmk]
        obtain ⟨hok', he'⟩ := step_sound_profile hb hmk hok P H
        refine ⟨hb, fun j => ?_, hok', he'.trans he⟩
        rw [withBody_eq_set hmk, List.getElem?_set]
        by_cases hjk : k = j
        · subst hjk
          simp [(List.getElem?_eq_some_iff.mp hmk).1, hfk, F]
        · simp only [hjk, ↓reduceIte]
          rw [hf j]
          by_cases hj : j < k
          · simp [hj, show j < k + 1 by omega]
          · simp [hj, show ¬ j < k + 1 by omega]
  obtain ⟨hb, hf, hok, he⟩ := key m.funcs.length
  generalize (List.range m.funcs.length).foldl (stepAt m) m = mk at hb hf hok he
  have heq : mk = simplifyGlobals m := by
    have hfs : mk.funcs = m.funcs.map F := by
      apply List.ext_getElem?
      intro j
      rw [hf j, List.getElem?_map]
      split
      · rfl
      · next hj => rw [List.getElem?_eq_none (by omega)]; rfl
    cases mk
    simp only at hb hfs
    subst hb hfs
    rfl
  subst heq
  exact ⟨hok, he⟩

end Silmaril.Wasm.Binaryen.SimplifyGlobals
