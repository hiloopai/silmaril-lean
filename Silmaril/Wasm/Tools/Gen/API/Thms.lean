module

public import Silmaril.Wasm.Tools.Gen.API.Defs
public import Mathlib.Data.Nat.Init

/-!
# Laws of the generic fuzzer API

* the shrinker's specification: `shrink_pred` (the predicate is kept), `shrink_size_le` (the
  size does not grow), `shrink_step_none`/`shrink_local_min` (the result is a local minimum: no
  strictly smaller candidate satisfies the predicate), `shrink_inv` (every invariant the
  accepted candidates keep is kept), `shrink_valid` (with a checker conjoined to the predicate,
  validity is kept);
* the fuel-bounded loop: `shrinkM_id` (in `Id`, with more fuel than the size, `shrinkM` is
  `shrink`);
* the guards: `Generator.guarded_run`, `Mutator.guarded_run` (the raw output exactly when it
  passes the checker).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen


namespace Shrinker

variable {S : Type} (sh : Shrinker S) (p : S → Bool)

theorem step_accept {x c : S} (h : sh.step p x = some c) : p c = true := by
  have := List.find?_some h
  simp only [accept, Bool.and_eq_true] at this
  exact this.2

theorem step_mem {x c : S} (h : sh.step p x = some c) : c ∈ sh.cands x :=
  List.mem_of_find?_eq_some h

theorem shrink_of_none {x : S} (h : sh.step p x = none) : sh.shrink p x = x := by
  rw [shrink]; split <;> simp_all

theorem shrink_of_some {x c : S} (h : sh.step p x = some c) :
    sh.shrink p x = sh.shrink p c := by
  rw [shrink]; split <;> simp_all

/-- **Invariants of accepted candidates are kept.** -/
theorem shrink_inv (Q : S → Prop) (hQ : ∀ x c, Q x → c ∈ sh.cands x → p c = true → Q c) :
    ∀ x, Q x → Q (sh.shrink p x) := by
  intro x
  induction hn : sh.size x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hx
    cases hs : sh.step p x with
    | none => rw [shrink_of_none sh p hs]; exact hx
    | some c =>
      rw [shrink_of_some sh p hs]
      exact ih _ (hn ▸ step_lt hs) c rfl (hQ x c hx (step_mem sh p hs) (step_accept sh p hs))

/-- **The predicate is kept.** -/
theorem shrink_pred {x : S} (hx : p x = true) : p (sh.shrink p x) = true :=
  sh.shrink_inv p (fun y => p y = true) (fun _ _ _ _ h => h) x hx

/-- **The size does not grow.** -/
theorem shrink_size_le (x : S) : sh.size (sh.shrink p x) ≤ sh.size x := by
  induction hn : sh.size x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases hs : sh.step p x with
    | none => rw [shrink_of_none sh p hs]; exact Nat.le_of_eq hn
    | some c =>
      rw [shrink_of_some sh p hs]
      have hlt := hn ▸ step_lt hs
      exact Nat.le_trans (ih _ hlt c rfl) (Nat.le_of_lt hlt)

/-- **The result is a fixed point of one step.** -/
theorem shrink_step_none (x : S) : sh.step p (sh.shrink p x) = none := by
  induction hn : sh.size x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases hs : sh.step p x with
    | none => rw [shrink_of_none sh p hs]; exact hs
    | some c =>
      rw [shrink_of_some sh p hs]
      exact ih _ (hn ▸ step_lt hs) c rfl

/-- **Local minimality**: no strictly smaller candidate of the result satisfies `p`. -/
theorem shrink_local_min (x : S) :
    ∀ c ∈ sh.cands (sh.shrink p x), sh.size c < sh.size (sh.shrink p x) → p c = false := by
  intro c hc hlt
  have h := List.find?_eq_none.1 (sh.shrink_step_none p x) c hc
  simp only [accept, Bool.and_eq_true, decide_eq_true_eq, not_and] at h
  simpa using h hlt

/-- **Checked shrinking keeps validity**: with the checker conjoined to the predicate. -/
theorem shrink_valid (L : DecLang) (sh : Shrinker L.Syn) (p : L.Syn → Bool) {x : L.Syn}
    (hv : L.Valid x) (hp : p x = true) :
    L.Valid (sh.shrink (fun c => L.check c && p c) x) ∧
      p (sh.shrink (fun c => L.check c && p c) x) = true := by
  have h := sh.shrink_pred (fun c => L.check c && p c)
    (x := x) (by simp [(L.check_iff x).2 hv, hp])
  simp only [Bool.and_eq_true] at h
  exact ⟨(L.check_iff _).1 h.1, h.2⟩

/-! ### The fuel-bounded loop -/

theorem shrinkM_first_id (x : S) :
    ∀ cs : List S, shrinkM.first (m := Id) sh p x cs = cs.find? (sh.accept p x)
  | [] => rfl
  | c :: cs => by
    have ih := shrinkM_first_id x cs
    by_cases hlt : sh.size c < sh.size x
    · cases hp : p c <;> simp [shrinkM.first, accept, hlt, hp, ih] <;> rfl
    · simp [shrinkM.first, accept, hlt, ih]

/-- **In `Id`, with fuel above the size, `shrinkM` is `shrink`.** -/
theorem shrinkM_id : ∀ (fuel : Nat) (x : S), sh.size x < fuel →
    sh.shrinkM (m := Id) p fuel x = sh.shrink p x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, x, h => by
    have hf := shrinkM_first_id sh p x (sh.cands x)
    cases hs : sh.step p x with
    | none =>
      rw [shrink_of_none sh p hs]
      simp only [step] at hs
      simp only [shrinkM, hf, hs]
      rfl
    | some c =>
      rw [shrink_of_some sh p hs]
      have hc := step_lt hs
      simp only [step] at hs
      simp only [shrinkM, hf, hs]
      exact shrinkM_id fuel c (by omega)

end Shrinker

/-! ## Guards -/

namespace Generator

theorem guarded_run (L : DecLang) (raw : Rng → Nat → L.Syn) (d : L.Syn) (hd : L.Valid d)
    (r : Rng) (n : Nat) :
    (guarded L raw d hd).run r n = if L.check (raw r n) then raw r n else d := rfl

theorem guarded_run_of_check (L : DecLang) {raw : Rng → Nat → L.Syn} {d : L.Syn}
    {hd : L.Valid d} {r : Rng} {n : Nat} (h : L.check (raw r n) = true) :
    (guarded L raw d hd).run r n = raw r n := by
  simp [guarded_run, h]

end Generator

namespace Mutator

theorem guarded_run (L : DecLang) (raw : Rng → L.Syn → L.Syn) (r : Rng) (x : L.Syn) :
    (guarded L raw).run r x = if L.check (raw r x) then raw r x else x := rfl

theorem guarded_run_of_check (L : DecLang) {raw : Rng → L.Syn → L.Syn} {r : Rng} {x : L.Syn}
    (h : L.check (raw r x) = true) : (guarded L raw).run r x = raw r x := by
  simp [guarded_run, h]

end Mutator

end Silmaril.Wasm.Tools.Gen
