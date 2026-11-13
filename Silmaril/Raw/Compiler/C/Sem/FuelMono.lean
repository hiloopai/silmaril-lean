module

public import Silmaril.Compiler.C.Sem.C0.Defs
@[expose] public section

/-!
# Fuel monotonicity, shared by the rungs

Every rung from C1 up is a fuel-indexed interpreter in `Except C0.Stop` whose only
fuel-dependent failure is `outOfFuel`. The flat approximation relation below treats
exhaustion as the only unfinished result and preserves every other error and every value.
Its bind and list-loop laws, packaged in the `fuel_mono` tactic, discharge each case of a
rung's simultaneous fuel induction (`C2Mono` … `C5Mono`).

The determinism argument is rung-independent: `subsingleton_or_univ` derives it for any
fuel-indexed `run` that is monotone, for the behaviour set shape every rung's `beh` has.
-/

namespace Silmaril.Compile.C.Sem.FuelMono

open C0 (Stop Result)

/-- A computation may become more defined only when it exhausted its fuel. -/
def Approx {α : Type} (a b : Except Stop α) : Prop :=
  a ≠ .error .outOfFuel → b = a

theorem approx_refl {α : Type} (a : Except Stop α) : Approx a a :=
  fun _ => rfl

theorem approx_bottom {α : Type} (a : Except Stop α) :
    Approx (.error .outOfFuel) a := fun h => False.elim (h rfl)

theorem approx_bind {α β : Type} {a b : Except Stop α}
    {f g : α → Except Stop β} (ha : Approx a b) (hf : ∀ x, Approx (f x) (g x)) :
    Approx (a >>= f) (b >>= g) := by
  cases a with
  | error e =>
    cases e <;> simp_all [Approx, Bind.bind, Except.bind]
  | ok x =>
    have hb := ha (by intro h; cases h)
    subst b
    exact hf x

theorem approx_forIn {α β : Type} (xs : List α) (b : β)
    (f g : α → β → Except Stop (ForInStep β))
    (h : ∀ x b, Approx (f x b) (g x b)) :
    Approx (forIn xs b f) (forIn xs b g) := by
  induction xs generalizing b with
  | nil => exact approx_refl _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply approx_bind (h x b)
    intro s
    cases s with
    | done b => exact approx_refl _
    | yield b => exact ih b

/-- A recursive call of a case: one application of an induction hypothesis, with no search
beyond the local hypotheses. -/
scoped macro "fuel_ih" : tactic => `(tactic|
  solve_by_elim (maxDepth := 1) (symm := false) (exfalso := false) (constructor := false) only [*])

/-- One case of a simultaneous fuel induction: split the interpreter's code and close each
leaf by reflexivity (fuel-free code) or an induction hypothesis (a recursive call, `fuel_ih`).
Reflexivity and hypothesis application stay at reducible transparency, so fuel-independent
prefixes (frame setup, initializers) are not unfolded. The full `solve_by_elim` runs only
after `split` has failed; it closes the branches `split` leaves with contradictory
hypotheses. -/
scoped macro "fuel_mono" : tactic => `(tactic|
  repeat' first
    | with_reducible exact approx_refl _
    | assumption
    | with_reducible fuel_ih
    | apply approx_bind
    | apply approx_forIn
    | split
    | with_reducible solve_by_elim (maxDepth := 3)
    | intro
)

/-- The behaviours every rung assigns to a fuel-indexed run (`C1.beh` … `C5.beh`). -/
def behOf (run : Nat → Result) : Set Obs := {o |
  (∃ n, run n = .done o) ∨ (∃ n why, run n = .undefined why) ∨
    (o = ⟨[], .diverges⟩ ∧ ∀ n, run n = .outOfFuel)}

/-- Two non-exhausted runs of a monotone interpreter agree. -/
theorem agree {run : Nat → Result}
    (mono : ∀ n k r, run n = r → r ≠ .outOfFuel → run (n + k) = r)
    {n m : Nat} {r s : Result} (hr : run n = r) (hs : run m = s)
    (hn : r ≠ .outOfFuel) (hm : s ≠ .outOfFuel) : r = s := by
  have h₁ := mono n m r hr hn
  have h₂ := mono m n s hs hm
  rw [Nat.add_comm m n] at h₂
  exact h₁.symm.trans h₂

/-- A monotone interpreter has at most one observation, unless it encounters undefined
behaviour. -/
theorem subsingleton_or_univ {run : Nat → Result}
    (mono : ∀ n k r, run n = r → r ≠ .outOfFuel → run (n + k) = r) :
    (behOf run).Subsingleton ∨ behOf run = Set.univ := by
  by_cases hu : ∃ n why, run n = .undefined why
  · exact .inr (Set.eq_univ_of_forall fun _ => .inr (.inl hu))
  · left
    intro o ho o' ho'
    rcases ho with ⟨n, hn⟩ | hu' | ⟨rfl, hn⟩
    · rcases ho' with ⟨m, hm⟩ | hu' | ⟨rfl, hm⟩
      · have h := agree mono hn hm (by intro h; cases h) (by intro h; cases h)
        cases h
        rfl
      · exact False.elim (hu hu')
      · have h := hn.symm.trans (hm n)
        cases h
    · exact False.elim (hu hu')
    · rcases ho' with ⟨m, hm⟩ | hu' | ⟨rfl, _⟩
      · have h := hm.symm.trans (hn m)
        cases h
      · exact False.elim (hu hu')
      · rfl

end Silmaril.Compile.C.Sem.FuelMono
