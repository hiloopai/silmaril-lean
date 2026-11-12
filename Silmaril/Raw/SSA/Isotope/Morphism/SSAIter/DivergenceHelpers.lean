module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.RegionReflection
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.DivergenceStructural

/-! # Divergence through finite tags and dispatch -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless LetIter.Semantics

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
  {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

theorem diverges_underBinder_iff {n : Nat} {bound : BoundEnv α n}
    {body : Tm ν Φ (n + 1)} {payload intermediate : Value α} {s : σ} :
    Diverges instr free (.term (extend (extend bound intermediate) payload) body.underBinder s) ↔
      Diverges instr free (.term (extend bound payload) body s) :=
  Diverges.rename_iff (Fin.cases rfl (fun _ => rfl))

theorem inject_diverges_iff {k n : Nat} (i : Fin k) {bound : BoundEnv α n}
    {a : Tm ν Φ n} {s : σ} :
    Diverges instr free (.term bound (inject i a) s) ↔ Diverges instr free (.term bound a s) := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · constructor
      · intro h; cases h.unfold with | inl arg => exact arg
      · exact fun h => .fold (.inl h)
    · constructor
      · intro h; cases h.unfold with | inr arg => exact (ih j).mp arg
      · exact fun h => .fold (.inr ((ih j).mpr h))

theorem dispatch_diverges_iff {k n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n}
    {bs : Fin k → Tm ν Φ (n + 1)} {s : σ} :
    Diverges instr free (.term bound (dispatch a bs) s) ↔
      Diverges instr free (.term bound a s) ∨
        ∃ (i : Fin k) (payload : Value α) (mid : σ),
          Eval instr free bound a s (tagValue i payload) mid ∧
          Diverges instr free (.term (extend bound payload) (bs i) mid) := by
  induction k generalizing n s with
  | zero =>
    constructor
    · intro h; cases h.unfold with | abort arg => exact Or.inl arg
    · rintro (h | ⟨i, _⟩)
      · exact .fold (.abort h)
      · exact i.elim0
  | succ k ih =>
    constructor
    · intro h
      cases h.unfold with
      | case_scrutinee arg => exact Or.inl arg
      | case_inl arg branch => exact Or.inr ⟨0, _, _, arg, branch⟩
      | case_inr arg branch =>
        rcases ih.mp branch with stuck | ⟨i, payload, mid, lookup, chosen⟩
        · cases stuck.unfold
        · cases lookup
          exact Or.inr ⟨i.succ, payload, _, arg, diverges_underBinder_iff.mp chosen⟩
    · rintro (h | ⟨i, payload, mid, arg, chosen⟩)
      · exact .fold (.case_scrutinee h)
      · revert arg chosen
        refine Fin.cases (fun arg chosen => ?_) (fun j arg chosen => ?_) i
        · exact .fold (.case_inl arg chosen)
        · exact .fold (.case_inr arg (ih.mpr (Or.inr
            ⟨j, payload, mid, .bv, diverges_underBinder_iff.mpr chosen⟩)))

/-- Let-case has no internal looping; missing primitive outcomes remain stuck. -/
theorem caseIter_not_diverges {n : Nat} (t : LetCase.LocallyNameless.Tm ν Φ n)
    (bound : BoundEnv α n) (s : σ) :
    ¬ Diverges instr free (.term bound (CaseIter.embed t) s) := by
  induction t generalizing s with
  | fv | bv | unit => intro h; cases h.unfold
  | op f a ih => intro h; cases h.unfold with | op h => exact ih _ _ h
  | let₁ a b iha ihb =>
    intro h; cases h.unfold with
    | let₁_arg arg => exact iha _ _ arg
    | let₁_body _ body => exact ihb _ _ body
  | pair a b iha ihb =>
    intro h; cases h.unfold with
    | pair_left left => exact iha _ _ left
    | pair_right _ right => exact ihb _ _ right
  | let₂ a b iha ihb =>
    intro h; cases h.unfold with
    | let₂_arg arg => exact iha _ _ arg
    | let₂_body _ body => exact ihb _ _ body
  | inl a ih => intro h; cases h.unfold with | inl h => exact ih _ _ h
  | inr a ih => intro h; cases h.unfold with | inr h => exact ih _ _ h
  | abort a ih => intro h; cases h.unfold with | abort h => exact ih _ _ h
  | case e l r ihe ihl ihr =>
    intro h; cases h.unfold with
    | case_scrutinee arg => exact ihe _ _ arg
    | case_inl _ branch => exact ihl _ _ branch
    | case_inr _ branch => exact ihr _ _ branch

theorem emitCFG_diverges_iff {count labels n : Nat} (i : Fin (count + labels))
    {bound : BoundEnv α n} {a : Tm Empty Φ n} {s : σ} {free : FreeEnv Empty α} :
    Diverges instr free (.term bound (emitCFG i a) s) ↔ Diverges instr free (.term bound a s) := by
  cases i using Fin.addCases with
  | left i =>
    simp only [emitCFG, Fin.addCases_left]
    constructor
    · intro h; cases h.unfold with | inr arg => exact (inject_diverges_iff i).mp arg
    · exact fun h => .fold (.inr ((inject_diverges_iff i).mpr h))
  | right i =>
    simp only [emitCFG, Fin.addCases_right]
    constructor
    · intro h; cases h.unfold with | inl arg => exact (inject_diverges_iff i).mp arg
    · exact fun h => .fold (.inl ((inject_diverges_iff i).mpr h))

end Silmaril.Isotope.Morphism.SSAIter
