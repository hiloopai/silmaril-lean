module

public import Silmaril.Machine.Abi.Infer.Defs
/-!
# ABI inference: soundness and exactness of the consistency check

Proofs for `Silmaril.Machine.Abi.Infer.Thms`.

* `consistentWith_iff`: the Boolean check unfolds to three set inclusions.
* `sound`: an accepted summary forces the register discipline on every function
  it summarises.
* `complete`: if every function with the summary respects the discipline, the
  check accepts. The witnesses take `Val = E = Bool`. This needs a well-formed
  summary (`defs ⊆ writes`) and a result register outside the allowed inputs.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.Infer

open Silmaril.Machine (CallingConvention)
open Silmaril.Machine.Abi.Infer

variable {R : Type} [DecidableEq R]

theorem consistentWith_iff (cc : CallingConvention R) (n : Nat) (returns : Bool) (u : Usage R) :
    consistentWith cc n returns u = true ↔
      (∀ r ∈ u.reads, r ∈ allowed cc n) ∧ (∀ r ∈ u.writes, r ∉ cc.calleeSaved) ∧
        (returns = true → ∀ r ∈ resultReg cc, r ∈ u.defs) := by
  cases returns <;>
    simp [consistentWith, List.all_eq_true, Option.all_eq_true, and_assoc]

theorem sound {cc : CallingConvention R} {n : Nat} {returns : Bool} {u : Usage R}
    (check : consistentWith cc n returns u = true) {Val E : Type}
    {f : (R → Val) → (R → Val) × E} (summary : Summarizes u f) : Respects cc n returns f := by
  obtain ⟨reads, writes, result⟩ := (consistentWith_iff cc n returns u).1 check
  refine ⟨?_, ?_, ?_⟩
  · intro s r saved
    exact summary.unchanged s r fun written => writes r written saved
  · intro s t agree
    exact summary.effects s t fun x read => agree x (reads x read)
  · intro yes s t agree r reg
    exact summary.defs s t (fun x read => agree x (reads x read)) r (result yes r reg)

/-- The witness: `defs` (and `extra`) are zeroed, everything else unchanged. -/
def witness (u : Usage R) (extra : R → Bool) (effect : (R → Bool) → Bool) :
    (R → Bool) → (R → Bool) × Bool :=
  fun s => (fun x => if x ∈ u.defs ∨ extra x = true then false else s x, effect s)

theorem witness_summarizes (u : Usage R) (wf : ∀ r ∈ u.defs, r ∈ u.writes)
    (extra : R → Bool) (extra_writes : ∀ r, extra r = true → r ∈ u.writes)
    (effect : (R → Bool) → Bool)
    (effect_reads : ∀ s t, (∀ x ∈ u.reads, s x = t x) → effect s = effect t) :
    Summarizes u (witness u extra effect) where
  unchanged s r fresh := by
    have h₁ : r ∉ u.defs := fun d => fresh (wf r d)
    have h₂ : extra r ≠ true := fun e => fresh (extra_writes r e)
    simp [witness, h₁, h₂]
  regs s t _ r same := by
    simp only [witness]
    split <;> simp [same]
  defs s t _ r d := by simp [witness, d]
  effects s t agree := by simp [witness, effect_reads s t agree]

theorem complete {cc : CallingConvention R} {n : Nat} {returns : Bool} {u : Usage R}
    (wf : ∀ r ∈ u.defs, r ∈ u.writes) (resultFree : ∀ r ∈ resultReg cc, r ∉ allowed cc n)
    (all : ∀ f : (R → Bool) → (R → Bool) × Bool, Summarizes u f → Respects cc n returns f) :
    consistentWith cc n returns u = true := by
  refine (consistentWith_iff cc n returns u).2 ⟨?_, ?_, ?_⟩
  · intro r read
    by_contra outside
    have respects := all (witness u (fun _ => false) (fun s => s r))
      (witness_summarizes u wf _ (by simp) _ fun s t agree => agree r read)
    have := respects.effects (fun _ => false) (Function.update (fun _ => false) r true)
      (fun x inside => by
        have : x ≠ r := fun e => outside (e ▸ inside)
        simp [Function.update, this])
    simp [witness] at this
  · intro r written saved
    have respects := all (witness u (fun x => decide (x = r)) (fun _ => false))
      (witness_summarizes u wf _ (by simpa using written) _ fun _ _ _ => rfl)
    have := respects.preserved (fun _ => true) r saved
    simp [witness] at this
  · intro yes r reg
    by_contra undefined
    have respects := all (witness u (fun _ => false) (fun _ => false))
      (witness_summarizes u wf _ (by simp) _ fun _ _ _ => rfl)
    have := respects.result yes (fun _ => false) (Function.update (fun _ => false) r true)
      (fun x inside => by
        have : x ≠ r := fun e => resultFree r reg (e ▸ inside)
        simp [Function.update, this]) r reg
    simp [witness, undefined] at this

end Silmaril.Proofs.Machine.Abi.Infer
