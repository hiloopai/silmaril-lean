module

public import Silmaril.Wasm.Binaryen.CodeFoldingSound
public import Silmaril.Wasm.Binaryen.InlUnwrapProfile

@[expose] public section

/-! The existing CodeFolding executable preserves exact closed-host export
observations at every numerical profile. Its guards and hoisted-tail fragment
are unchanged. Both run directions follow the actual chosen execution. -/

namespace Silmaril.Wasm.Binaryen.CodeFolding

open Execution.Core Validation Numerics

variable (P : Profile) (H : Type)

/-- **One function**: folding the body of function `g` keeps validity and is an export
equivalence under the closed host. -/
theorem withBody_sound_profile {m : BModule} {g : Nat} {fg : BFunc} (hfg : m.funcs[g]? = some fg)
    (hok : m.Ok) : (m.withBody g (exprs fg.body)).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        (m.withBody g (exprs fg.body)).lower m.lower := by
  have hrel := exprs_rel fg.body
  obtain ⟨mt₀, hmt₀⟩ := hok
  have hmt₀' : ModuleOk (m.withBody g fg.body).lower mt₀ := by rw [withBody_self' hfg]; exact hmt₀
  have hvalid : ModuleOk (m.withBody g (exprs fg.body)).lower mt₀ := Unwrap.ok_transfer_mt hrel.2 hmt₀'
  refine ⟨⟨mt₀, hvalid⟩, ?_⟩
  have hL : m.lower.funcs[g]? = some (fg.mapBody BExpr.lowerList) := by
    simp only [BModule.lower, List.getElem?_map, hfg]
    rfl
  have hRm : (m.withBody g (exprs fg.body)).lower =
      { m.lower with funcs := (m.lower.funcs.set g
        (({ fg with body := exprs fg.body } : BFunc).mapBody BExpr.lowerList)) } := by
    simp only [BModule.lower, withBody_eq_set hfg, List.map_set]
    rfl
  rw [hRm]
  refine Unwrap.exportEquiv_of_instCorr_profile (Unwrap.instCorr_of_set_profile (R := []) hL rfl
    (fun mt => ?_) (fun mi dg ag => ⟨rfl, hrel.1, ⟨fun _ => False, by simp⟩, rfl⟩))
  rw [← hRm]
  constructor
  · intro h; rw [ModuleOk.unique h hmt₀]; exact hvalid
  · intro h'; rw [ModuleOk.unique h' hvalid]; exact hmt₀

theorem prefixFold_sound_profile {m : BModule} (hm : m.Ok) : ∀ i, i ≤ m.funcs.length →
    (prefixFold m i).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (prefixFold m i).lower m.lower
  | 0, _ => by
    have e : prefixFold m 0 = m := by simp [prefixFold]
    rw [e]
    exact ⟨hm, Exe.exportEquiv_refl _⟩
  | i + 1, hi => by
    obtain ⟨hok, he⟩ := prefixFold_sound_profile hm i (by omega)
    obtain ⟨fg, hfg⟩ : ∃ fg, m.funcs[i]? = some fg := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hfg', heq⟩ := prefixFold_succ hfg
    obtain ⟨hok', he'⟩ := withBody_sound_profile P H hfg' hok
    rw [heq]
    exact ⟨hok', he'.1.trans (fun _ _ _ h₁ h₂ => h₁.trans h₂) he.1,
      he.2.trans (fun _ _ _ h₁ h₂ => h₂.trans h₁) he'.2⟩

/-- **CodeFolding keeps validity and is an export equivalence** under the closed host. -/
theorem codeFolding_sound_profile {m : BModule} (hm : m.Ok) :
    (codeFolding m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (codeFolding m).lower m.lower := by
  have h := prefixFold_sound_profile P H hm m.funcs.length le_rfl
  have e : prefixFold m m.funcs.length = codeFolding m := by
    simp [prefixFold, codeFolding, foldF]
  rwa [e] at h

end Silmaril.Wasm.Binaryen.CodeFolding
