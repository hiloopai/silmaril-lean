module

public import Silmaril.X86.Concurrency.Cir.C11.Defs

/-!
# C11 litmus tests on CIR: the check from its slices

`C11Test.check` is `preOk` and `flagsOk` of the flags, and the flags are the union of the
flags of consecutive slices of the choices of runs. The generated corpus
(`Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus`) checks each part of a large test by its own
`decide +kernel` and joins them with these lemmas:

* `check_eq`: `c.check = (c.preOk && c.flagsOk (c.flagsFrom 0))`;
* `flagsFrom_split`: from `c.flagsSlice i k = v` and `i + k = j`,
  `c.flagsFrom i = v ||| c.flagsFrom j`;
* `flagsFrom_end`: past the last choice, `c.flagsFrom i = 0`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.C11Slice

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.C11

/-- A fold of unions from `a` is `a` united with the fold from `0`. -/
theorem foldl_lor {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat),
      l.foldl (fun acc x => acc ||| f x) a = a ||| l.foldl (fun acc x => acc ||| f x) 0
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons]
    rw [foldl_lor f l (a ||| f x), foldl_lor f l (0 ||| f x), Nat.zero_or, Nat.or_assoc]

theorem force_eq {α : Sort _} (v : Nat) (k : Nat → α) : Rc11.force v k = k v := by
  cases v <;> rfl

/-- The check in parts. -/
theorem check_eq (c : C11Test) : c.check = (c.preOk && c.flagsOk (c.flagsFrom 0)) := by
  unfold C11Test.check
  rw [force_eq]
  rfl

/-- Split off the slice of `k` choices of runs from the `i`-th. The next index `j` is a literal,
so that the next split matches syntactically: a kernel defeq check of `flagsFrom (i + k)`
against `flagsFrom j` under `|||` evaluates both sides. -/
theorem flagsFrom_split {c : C11Test} {i k j v : Nat} (h : c.flagsSlice i k = v) (hj : i + k = j) :
    c.flagsFrom i = v ||| c.flagsFrom j := by
  subst h hj
  unfold C11Test.flagsFrom C11Test.flagsSlice
  conv => lhs; rw [← List.take_append_drop k (c.combos.drop i)]
  rw [List.foldl_append, foldl_lor _ ((c.combos.drop i).drop k), List.drop_drop]

/-- No choice of runs from the `i`-th on. -/
theorem flagsFrom_end {c : C11Test} {i : Nat} (h : c.combos.length ≤ i) : c.flagsFrom i = 0 := by
  unfold C11Test.flagsFrom
  rw [List.drop_eq_nil_of_le h]
  rfl

end Silmaril.Proofs.X86.Concurrency.Cir.C11Slice
