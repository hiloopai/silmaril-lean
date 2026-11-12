module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.RegionReflection
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSAExternal

/-! # External divergence through finite tags and dispatch -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.SSAIter.External

open LetIter.LocallyNameless
open LetIter.Semantics (BoundEnv FreeEnv Config Eval extend)
open LetIter.Semantics.External (Diverges)

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
  {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}
  {prim : Φ → Value α → σ → Prop}

theorem diverges_underBinder_iff {n : Nat} {bound : BoundEnv α n}
    {body : Tm ν Φ (n + 1)} {payload intermediate : Value α} {s : σ} :
    Diverges instr free prim (.term (extend (extend bound intermediate) payload) body.underBinder s) ↔
      Diverges instr free prim (.term (extend bound payload) body s) :=
  Diverges.rename_iff (Fin.cases rfl (fun _ => rfl))

theorem inject_diverges_iff {k n : Nat} (i : Fin k) {bound : BoundEnv α n}
    {a : Tm ν Φ n} {s : σ} :
    Diverges instr free prim (.term bound (inject i a) s) ↔ Diverges instr free prim (.term bound a s) := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · constructor
      · intro h; cases h.unfold with | core h => cases h with | inl arg => exact arg
      · exact fun h => .fold_core (.inl h)
    · constructor
      · intro h; cases h.unfold with | core h => cases h with | inr arg => exact (ih j).mp arg
      · exact fun h => .fold_core (.inr ((ih j).mpr h))

theorem dispatch_diverges_iff {k n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n}
    {bs : Fin k → Tm ν Φ (n + 1)} {s : σ} :
    Diverges instr free prim (.term bound (dispatch a bs) s) ↔
      Diverges instr free prim (.term bound a s) ∨
        ∃ (i : Fin k) (payload : Value α) (mid : σ),
          Eval instr free bound a s (tagValue i payload) mid ∧
          Diverges instr free prim (.term (extend bound payload) (bs i) mid) := by
  induction k generalizing n s with
  | zero =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with | abort arg => exact Or.inl arg
    · rintro (h | ⟨i, _⟩)
      · exact .fold_core (.abort h)
      · exact i.elim0
  | succ k ih =>
    constructor
    · intro h
      cases h.unfold with | core h => cases h with
      | case_scrutinee arg => exact Or.inl arg
      | case_inl arg branch => exact Or.inr ⟨0, _, _, arg, branch⟩
      | case_inr arg branch =>
        rcases ih.mp branch with stuck | ⟨i, payload, mid, lookup, chosen⟩
        · cases stuck.unfold with | core h => cases h
        · cases lookup
          exact Or.inr ⟨i.succ, payload, _, arg, diverges_underBinder_iff.mp chosen⟩
    · rintro (h | ⟨i, payload, mid, arg, chosen⟩)
      · exact .fold_core (.case_scrutinee h)
      · revert arg chosen
        refine Fin.cases (fun arg chosen => ?_) (fun j arg chosen => ?_) i
        · exact .fold_core (.case_inl arg chosen)
        · exact .fold_core (.case_inr arg (ih.mpr (Or.inr
            ⟨j, payload, mid, .bv, diverges_underBinder_iff.mpr chosen⟩)))

theorem emitCFG_diverges_iff {count labels n : Nat} (i : Fin (count + labels))
    {bound : BoundEnv α n} {a : Tm Empty Φ n} {s : σ} {free : FreeEnv Empty α} :
    Diverges instr free prim (.term bound (emitCFG i a) s) ↔ Diverges instr free prim (.term bound a s) := by
  cases i using Fin.addCases with
  | left i =>
    simp only [emitCFG, Fin.addCases_left]
    constructor
    · intro h; cases h.unfold with | core h => cases h with | inr arg => exact (inject_diverges_iff i).mp arg
    · exact fun h => .fold_core (.inr ((inject_diverges_iff i).mpr h))
  | right i =>
    simp only [emitCFG, Fin.addCases_right]
    constructor
    · intro h; cases h.unfold with | core h => cases h with | inl arg => exact (inject_diverges_iff i).mp arg
    · exact fun h => .fold_core (.inl ((inject_diverges_iff i).mpr h))

end Silmaril.Isotope.Morphism.SSAIter.External
