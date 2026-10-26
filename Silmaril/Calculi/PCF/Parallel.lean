module

public import Silmaril.Calculi.PCF.Denotation
public import Silmaril.Calculi.PCF.Por

/-! # Parallel boolean combinators in PCF+`por`

Derived term formers used to build definable elements:

* `Term.not t = if t then false else true`, the strict negation;
* `Term.pand t u = ¬por(¬t, ¬u)`, parallel and, which is `false` as soon as
  either argument is `false`, even if the other is `⊥`;
* `Term.porList` and `Term.pandList`, iterated parallel or and and;
* `Term.ifChain [(G₁, w₁), …, (Gₖ, wₖ)] = if G₁ then w₁ else … else Ω`;
* `Term.eqNum k t`, the test `t = k̄` on numerals.

Each comes with its denotation, stated for `denote` into the flat domains
`Part Bool` and `Part ℕ`.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

variable {p : Bool} {Γ : Ctx Base} {τ : Ty}

/-- Strict negation, `if t then false else true`. -/
def Term.not (t : Term p Γ .bool) : Term p Γ .bool := Term.ite t Term.ff Term.tt

/-- `⟦¬t⟧ = ¬⊥ ⟦t⟧`. -/
theorem denote_not (t : Term p Γ .bool) (ρ : (model p).Env Γ) :
    (denote (Term.not t) ρ : Part Bool) = Flat.map (!·) (denote t ρ : Part Bool) := by
  rw [Term.not, denote_ite]
  rcases part_bool_cases (denote t ρ : Part Bool) with h | h | h <;> rw [h]
  · rw [condFun_none, Flat.map_none]
    rfl
  · rw [condFun_true, Flat.map_some, Bool.not_true]
    rfl
  · rw [condFun_false, Flat.map_some, Bool.not_false]
    rfl

/-- Parallel and, `¬por(¬a, ¬b)`. -/
def Term.pand (t u : Term true Γ .bool) : Term true Γ .bool :=
  Term.not (Term.por (Term.not t) (Term.not u))

/-- The value of parallel and: `¬por(¬x, ¬y)`. -/
theorem denote_pand (t u : Term true Γ .bool) (ρ : (model true).Env Γ) :
    (denote (Term.pand t u) ρ : Part Bool) =
      Flat.map (!·) (porFun (Flat.map (!·) (denote t ρ : Part Bool))
        (Flat.map (!·) (denote u ρ : Part Bool))) := by
  rw [Term.pand, denote_not, denote_por, denote_not, denote_not]

/-- Parallel and is `true` exactly when both arguments are. -/
theorem denote_pand_eq_true_iff (t u : Term true Γ .bool) (ρ : (model true).Env Γ) :
    (denote (Term.pand t u) ρ : Part Bool) = .some true ↔
      denote t ρ = (.some true : Part Bool) ∧ denote u ρ = (.some true : Part Bool) := by
  rw [denote_pand]
  rcases part_bool_cases (denote t ρ : Part Bool) with h | h | h <;> rw [h] <;>
    rcases part_bool_cases (denote u ρ : Part Bool) with h' | h' | h' <;> rw [h'] <;>
    simp [Flat.some_true_ne_some_false.symm]

/-- Parallel and is `false` as soon as its left argument is. -/
theorem denote_pand_of_left_false {t u : Term true Γ .bool} {ρ : (model true).Env Γ}
    (h : denote t ρ = (.some false : Part Bool)) :
    (denote (Term.pand t u) ρ : Part Bool) = .some false := by
  rw [denote_pand, h]
  simp

/-- Parallel and is `false` as soon as its right argument is. -/
theorem denote_pand_of_right_false {t u : Term true Γ .bool} {ρ : (model true).Env Γ}
    (h : denote u ρ = (.some false : Part Bool)) :
    (denote (Term.pand t u) ρ : Part Bool) = .some false := by
  rw [denote_pand, h]
  simp

/-- Iterated parallel or, `por(t₁, por(t₂, … false))`. -/
def Term.porList : List (Term true Γ .bool) → Term true Γ .bool
  | [] => Term.ff
  | t :: l => Term.por t (Term.porList l)

/-- An iterated parallel or is `true` exactly when some disjunct is. -/
theorem denote_porList_eq_true_iff (l : List (Term true Γ .bool)) (ρ : (model true).Env Γ) :
    (denote (Term.porList l) ρ : Part Bool) = .some true ↔
      ∃ t ∈ l, denote t ρ = (.some true : Part Bool) := by
  induction l with
  | nil =>
    rw [Term.porList, denote_ff]
    exact iff_of_false Flat.some_true_ne_some_false.symm (by simp)
  | cons t l ih =>
    rw [Term.porList, denote_por]
    simp only [List.mem_cons, exists_eq_or_imp, ← ih]
    rcases part_bool_cases (denote t ρ : Part Bool) with h | h | h <;> rw [h] <;>
      rcases part_bool_cases (denote (Term.porList l) ρ : Part Bool) with h' | h' | h' <;>
      rw [h'] <;> simp [Flat.some_true_ne_some_false.symm]

/-- An iterated parallel or is `false` when every disjunct is. -/
theorem denote_porList_of_forall_false {l : List (Term true Γ .bool)} {ρ : (model true).Env Γ}
    (h : ∀ t ∈ l, denote t ρ = (.some false : Part Bool)) :
    (denote (Term.porList l) ρ : Part Bool) = .some false := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [Term.porList, denote_por, h t List.mem_cons_self,
      ih fun u hu => h u (List.mem_cons_of_mem _ hu)]
    simp

/-- Iterated parallel and, `pand(t₁, pand(t₂, … true))`. -/
def Term.pandList : List (Term true Γ .bool) → Term true Γ .bool
  | [] => Term.tt
  | t :: l => Term.pand t (Term.pandList l)

/-- An iterated parallel and is `true` exactly when every conjunct is. -/
theorem denote_pandList_eq_true_iff (l : List (Term true Γ .bool)) (ρ : (model true).Env Γ) :
    (denote (Term.pandList l) ρ : Part Bool) = .some true ↔
      ∀ t ∈ l, denote t ρ = (.some true : Part Bool) := by
  induction l with
  | nil =>
    rw [Term.pandList, denote_tt]
    simp
  | cons t l ih =>
    rw [Term.pandList, denote_pand_eq_true_iff, List.forall_mem_cons, ih]

/-- An iterated parallel and is `false` as soon as some conjunct is. -/
theorem denote_pandList_of_exists_false {l : List (Term true Γ .bool)}
    {ρ : (model true).Env Γ} (h : ∃ t ∈ l, denote t ρ = (.some false : Part Bool)) :
    (denote (Term.pandList l) ρ : Part Bool) = .some false := by
  induction l with
  | nil => simp at h
  | cons t l ih =>
    rw [Term.pandList]
    obtain ⟨u, hu, hf⟩ := h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact denote_pand_of_left_false hf
    · exact denote_pand_of_right_false (ih ⟨u, hu, hf⟩)

/-- `if G₁ then w₁ else if G₂ then w₂ … else Ω`. -/
def Term.ifChain : List (Term p Γ .bool × Term p Γ τ) → Term p Γ τ
  | [] => Term.omega τ
  | q :: l => Term.ite q.1 q.2 (Term.ifChain l)

/-- An if-chain whose guards are all defined, some `true`, and whose branches
under `true` guards agree, denotes that common value. -/
theorem denote_ifChain_eq {l : List (Term p Γ .bool × Term p Γ τ)} {ρ : (model p).Env Γ}
    {val : (model p).ty τ}
    (hall : ∀ q ∈ l, (denote q.1 ρ = (.some true : Part Bool) ∧ denote q.2 ρ = val) ∨
      denote q.1 ρ = (.some false : Part Bool))
    (hex : ∃ q ∈ l, denote q.1 ρ = (.some true : Part Bool)) :
    denote (Term.ifChain l) ρ = val := by
  induction l with
  | nil => simp at hex
  | cons q l ih =>
    rw [Term.ifChain, denote_ite]
    rcases hall q List.mem_cons_self with ⟨h1, h2⟩ | h1
    · rw [h1, condFun_true, h2]
    · rw [h1, condFun_false]
      refine ih (fun q' hq' => hall q' (List.mem_cons_of_mem _ hq')) ?_
      obtain ⟨q', hq', ht⟩ := hex
      rcases List.mem_cons.1 hq' with rfl | hq'
      · rw [h1] at ht; exact absurd ht Flat.some_true_ne_some_false.symm
      · exact ⟨q', hq', ht⟩

/-- An if-chain none of whose guards is `true` denotes `⊥`. -/
theorem denote_ifChain_eq_bot {l : List (Term p Γ .bool × Term p Γ τ)} {ρ : (model p).Env Γ}
    (h : ∀ q ∈ l, denote q.1 ρ ≠ (.some true : Part Bool)) :
    denote (Term.ifChain l) ρ = ⊥ := by
  induction l with
  | nil => exact denote_omega ρ
  | cons q l ih =>
    rw [Term.ifChain, denote_ite]
    rcases part_bool_cases (denote q.1 ρ : Part Bool) with h1 | h1 | h1
    · rw [h1, condFun_none]
    · exact absurd h1 (h q List.mem_cons_self)
    · rw [h1, condFun_false]
      exact ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')

/-- `⟦eqNum k t⟧ = (⟦t⟧ == k)`, strict in `⟦t⟧`. -/
theorem denote_eqNum (k : ℕ) (t : Term p Γ .nat) (ρ : (model p).Env Γ) :
    (denote (Term.eqNum k t) ρ : Part Bool) = Flat.map (· == k) (denote t ρ : Part ℕ) := by
  induction k generalizing t with
  | zero => rw [Term.eqNum, denote_isZero]
  | succ k ih =>
    rw [Term.eqNum, denote_ite, ih, denote_isZero, denote_pred]
    rcases Part.eq_none_or_eq_some (denote t ρ : Part ℕ) with h | ⟨m, h⟩ <;> rw [h]
    · rw [Flat.map_none, condFun_none, Flat.map_none]
      rfl
    · cases m with
      | zero =>
        rw [Flat.map_some, beq_self_eq_true, condFun_true, Flat.map_some]
        rfl
      | succ m => simp [predPart]

end Silmaril.Calculi.PCF
