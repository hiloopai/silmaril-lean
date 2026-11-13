module

public import Silmaril.Wasm.FX.Asyncify.Selective.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

/-!
# Completeness of the suspension analysis

`Selective.analyze Q n` iterates the refinement `refine Q n` (keep `f < n` when `f` is defined
and its body calls only functions still in the set) `n + 1` times from the full set, then checks
the result. This module shows that the check always passes and that the result is the
**greatest** certificate on the functions `< n`.

* `safeI_mono`, `okF_mono`: the refinement is monotone;
* `X k`: the `k`-th iterate; `X_succ`, `X_anti`, `X_lt`: it is a decreasing chain of subsets of
  `range n` from `k = 1` on;
* `le_X`: a post-fixpoint `T` (every `f ∈ T` is `< n` and `okF Q T f`) is below every iterate;
* `stable_from`, `count`, **`X_stable`**: a decreasing chain of subsets of `range n` is stable
  after `n + 1` rounds (each strict step loses an element);
* **`check_candidate`**: the check always passes, so `analyze Q n = candidate Q n`;
* **`analyze_complete`**: every certificate on the functions `< n` is contained in
  `analyze Q n`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Analysis

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.Selective

variable {V : Type}

/-- Inclusion of sets of functions. -/
def Sub (S S' : Nat → Bool) : Prop := ∀ f, S f = true → S' f = true

theorem safeI_mono {S S' : Nat → Bool} (h : Sub S S') (i : TIns V) (hi : safeI S i = true) :
    safeI S' i = true := by
  cases i with
  | call f => exact h f hi
  | cond f g =>
    have hfg : S f = true ∧ S g = true := by simpa only [safeI, Bool.and_eq_true] using hi
    show (S' f && S' g) = true
    rw [h f hfg.1, h g hfg.2]; rfl
  | _ => exact hi

theorem okF_mono (Q : Prog (TIns V)) {S S' : Nat → Bool} (h : Sub S S') (f : Nat)
    (hf : okF Q S f = true) : okF Q S' f = true := by
  unfold okF at hf ⊢
  cases hq : Q f with
  | none => rw [hq] at hf; exact hf
  | some x =>
    rw [hq] at hf
    exact List.all_eq_true.2 fun i hi => safeI_mono h i (List.all_eq_true.1 hf i hi)

theorem iter_succ' (r : (Nat → Bool) → Nat → Bool) (k : Nat) (T : Nat → Bool) :
    iter r (k + 1) T = r (iter r k T) := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih => exact ih (r T)

variable (Q : Prog (TIns V)) (n : Nat)

/-- The iterates of the refinement. -/
def X (k : Nat) : Nat → Bool := iter (refine Q n) k (fun _ => true)

theorem X_succ (k : Nat) : X Q n (k + 1) = refine Q n (X Q n k) := iter_succ' _ k _

theorem X_succ_iff (k f : Nat) :
    X Q n (k + 1) f = true ↔ f < n ∧ X Q n k f = true ∧ okF Q (X Q n k) f = true := by
  rw [X_succ]
  simp only [refine, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem X_anti (k : Nat) : Sub (X Q n (k + 1)) (X Q n k) :=
  fun f h => ((X_succ_iff Q n k f).1 h).2.1

theorem X_lt (k f : Nat) (h : X Q n (k + 1) f = true) : f < n := ((X_succ_iff Q n k f).1 h).1

/-- A post-fixpoint is below every iterate. -/
theorem le_X {T : Nat → Bool} (hT : ∀ f, T f = true → f < n ∧ okF Q T f = true) (k : Nat) :
    Sub T (X Q n k) := by
  induction k with
  | zero => exact fun _ _ => rfl
  | succ k ih =>
    intro f hf
    exact (X_succ_iff Q n k f).2 ⟨(hT f hf).1, ih f hf, okF_mono Q ih f (hT f hf).2⟩

/-- Once two consecutive iterates agree, all later ones do. -/
theorem stable_from {k : Nat} (h : X Q n (k + 1) = X Q n k) (j : Nat) :
    X Q n (k + 1 + j) = X Q n (k + j) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    have e1 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    have e2 : k + (j + 1) = (k + j) + 1 := by omega
    rw [e1, e2, X_succ, X_succ, ih]

/-- The number of elements of an iterate below `n`. -/
def cnt (k : Nat) : Nat := ((Finset.range n).filter fun f => X Q n k f = true).card

theorem cnt_lt {k : Nat} (h : X Q n (k + 2) ≠ X Q n (k + 1)) : cnt Q n (k + 2) < cnt Q n (k + 1) := by
  have hne : ∃ f, X Q n (k + 2) f ≠ X Q n (k + 1) f := by
    by_contra hall
    exact h (funext fun f => Classical.not_not.1 fun hf => hall ⟨f, hf⟩)
  obtain ⟨f, hf⟩ := hne
  have hk : X Q n (k + 1) f = true := by
    cases h2 : X Q n (k + 2) f with
    | true => exact X_anti Q n (k + 1) f h2
    | false => cases h1 : X Q n (k + 1) f <;> simp_all
  have hk2 : X Q n (k + 2) f = false := by
    cases h2 : X Q n (k + 2) f with
    | true => rw [h2, hk] at hf; exact absurd rfl hf
    | false => rfl
  have hsub : (Finset.range n).filter (fun f => X Q n (k + 2) f = true) ⊂
      (Finset.range n).filter (fun f => X Q n (k + 1) f = true) := by
    refine Finset.ssubset_iff_of_subset (fun g hg => ?_) |>.2 ⟨f, ?_, ?_⟩
    · have hg' := Finset.mem_filter.1 hg
      exact Finset.mem_filter.2 ⟨hg'.1, X_anti Q n (k + 1) g hg'.2⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (X_lt Q n k f hk), hk⟩
    · intro hm
      have hm' : X Q n (k + 2) f = true := (Finset.mem_filter.1 hm).2
      rw [hk2] at hm'; cases hm'
  exact Finset.card_lt_card hsub

theorem cnt_le (k : Nat) : cnt Q n k ≤ n :=
  (Finset.card_filter_le _ _).trans (Finset.card_range n).le

/-- Each strict step loses an element. -/
theorem count (j : Nat) (h : ∀ i < j, X Q n (i + 2) ≠ X Q n (i + 1)) : cnt Q n (j + 1) + j ≤ n := by
  induction j with
  | zero => exact cnt_le Q n 1
  | succ j ih =>
    have hj : cnt Q n (j + 1) + j ≤ n := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hlt : cnt Q n (j + 1 + 1) < cnt Q n (j + 1) := cnt_lt Q n (h j (Nat.lt_succ_self j))
    omega

/-- **The iteration is stable after `n + 1` rounds.** -/
theorem X_stable : X Q n (n + 2) = X Q n (n + 1) := by
  by_contra hne
  have hall : ∀ i < n + 1, X Q n (i + 2) ≠ X Q n (i + 1) := by
    intro i hi heq
    have hs : X Q n (i + 1 + 1 + (n - i)) = X Q n (i + 1 + (n - i)) := stable_from Q n heq (n - i)
    have e1 : i + 1 + 1 + (n - i) = n + 2 := by omega
    have e2 : i + 1 + (n - i) = n + 1 := by omega
    rw [e1, e2] at hs
    exact hne hs
  have hc : cnt Q n (n + 2) + (n + 1) ≤ n := count Q n (n + 1) hall
  omega

theorem candidate_eq : candidate Q n = X Q n (n + 1) := by
  funext f
  cases h : X Q n (n + 1) f with
  | true => simp only [candidate, X_lt Q n n f h, decide_true, Bool.true_and]; exact h
  | false => simp only [candidate, Bool.and_eq_false_iff]; exact .inr h

/-- **The check always passes.** -/
theorem check_candidate : check Q n (candidate Q n) = true := by
  rw [candidate_eq]
  refine List.all_eq_true.2 fun f _ => ?_
  cases h : X Q n (n + 1) f with
  | false => rfl
  | true =>
    have h2 : X Q n (n + 1 + 1) f = true := by rw [X_stable]; exact h
    exact ((X_succ_iff Q n (n + 1) f).1 h2).2.2

theorem analyze_eq : analyze Q n = candidate Q n := by
  simp only [analyze, check_candidate, ite_true]

/-- **Completeness**: every post-fixpoint on the functions `< n` is in the analysis. -/
theorem analyze_greatest {T : Nat → Bool} (hT : ∀ f, T f = true → f < n ∧ okF Q T f = true) :
    Sub T (analyze Q n) := by
  rw [analyze_eq, candidate_eq]
  exact le_X Q n hT (n + 1)

theorem okF_of_safe {S : Nat → Bool} (h : SafeProg S Q) (f : Nat) (hf : S f = true) :
    okF Q S f = true := by
  obtain ⟨np, body, hq, hb⟩ := h f hf
  simp only [okF, hq]
  exact List.all_eq_true.2 hb

/-- **Completeness for certificates**: a certificate on the functions `< n` is in the analysis. -/
theorem analyze_complete {T : Nat → Bool} (hT : SafeProg T Q) (hn : ∀ f, T f = true → f < n) :
    Sub T (analyze Q n) :=
  analyze_greatest Q n fun f hf => ⟨hn f hf, okF_of_safe Q hT f hf⟩

end Silmaril.Proofs.Wasm.FX.Asyncify.Analysis
