module

public import Silmaril.Wasm.SpecTec.Broken.Defs

/-!
# Fuel: a definite answer at one fuel is the answer at every fuel

The evaluator is monotone in its fuel (`Sem.monoAt_of_le`): more fuel never changes a definite
answer.  So one concrete computation `premsHold 100 … = .error .undef` (or `callDef 100 …`), which
the kernel does by `rfl`, settles the question for every fuel.
-/

public section

namespace Silmaril.Wasm.SpecTec.Broken

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- A monotone fuel-indexed computation that is definitely undefined at one fuel has no value at
any fuel. -/
theorem ne_ok_of_undef {α : Type} {f : Nat → Res α}
    (hmono : ∀ m n, m ≤ n → Res.Le (f m) (f n)) {N : Nat} (h : f N = .error .undef) :
    ∀ m a, f m ≠ .ok a := by
  intro m a hm
  rcases Nat.le_total m N with hle | hle
  · rcases hmono m N hle with h₁ | h₁
    · rw [hm] at h₁; cases h₁
    · rw [hm, h] at h₁; cases h₁
  · rcases hmono N m hle with h₁ | h₁
    · rw [h] at h₁; cases h₁
    · rw [hm, h] at h₁; cases h₁

/-- Two definite values of a monotone fuel-indexed computation agree. -/
theorem ok_unique {α : Type} {f : Nat → Res α}
    (hmono : ∀ m n, m ≤ n → Res.Le (f m) (f n)) {N M : Nat} {a b : α}
    (ha : f N = .ok a) (hb : f M = .ok b) : a = b := by
  rcases Nat.le_total N M with hle | hle
  · have h := Res.Le.ok (hmono N M hle) ha
    rw [hb] at h
    exact (Except.ok.inj h).symm
  · have h := Res.Le.ok (hmono M N hle) hb
    rw [ha] at h
    exact Except.ok.inj h

/-- `PremsFail` from one undefined computation. -/
theorem premsFail_of_undef {s : Script} {ps : Option (List Prem)} {ρ : VarEnv}
    {prems : List Prem} {N : Nat} (hps : ps = some prems)
    (h : premsHold N (envOfScript s) ρ prems = .error .undef) : PremsFail s ps ρ :=
  ⟨prems, hps, ne_ok_of_undef (fun _ _ hle => (monoAt_of_le hle).premsHold _ _ _) h⟩

/-- Premises that hold do not fail. -/
theorem not_premsFail_of_premsHold {s : Script} {ps : Option (List Prem)} {ρ : VarEnv}
    (h : PremsHold s ps ρ) : ¬ PremsFail s ps ρ := by
  rintro ⟨prems', hps', hf⟩
  obtain ⟨prems, hps, N, ρ', hN⟩ := h
  rw [hps] at hps'
  cases hps'
  exact hf N ρ' hN

/-- `CallUndef` from one undefined computation. -/
theorem callUndef_of_undef {s : Script} {f : IL.Id} {args : List Arg} {N : Nat}
    (h : callDef N (envOfScript s) VarEnv.empty f args = .error .undef) : CallUndef s f args :=
  ne_ok_of_undef (fun _ _ hle => (monoAt_of_le hle).callDef _ _ _ _) h

/-- A call with a value is not undefined. -/
theorem not_callUndef_of_callIs {s : Script} {f : IL.Id} {args : List Arg} {v : Value}
    (h : CallIs s f args v) : ¬ CallUndef s f args := by
  obtain ⟨N, hN⟩ := h
  exact fun hu => hu N v hN

/-- A call has at most one value. -/
theorem callIs_unique {s : Script} {f : IL.Id} {args : List Arg} {v w : Value}
    (hv : CallIs s f args v) (hw : CallIs s f args w) : v = w := by
  obtain ⟨N, hN⟩ := hv
  obtain ⟨M, hM⟩ := hw
  exact ok_unique (fun _ _ hle => (monoAt_of_le hle).callDef _ _ _ _) hN hM

end Silmaril.Wasm.SpecTec.Broken
