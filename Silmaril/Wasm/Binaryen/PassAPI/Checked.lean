module

public import Silmaril.Wasm.Binaryen.PassAPI.Pass

@[expose] public section

/-! # Pass API: checked passes (translation validation)

A `CheckedPass C` is an **untrusted** transformer (LLM-written, external, heuristic)
together with a **verified** checker: whenever `check x y = true` and `C.Inv x`, the
output `y` is a sound replacement satisfying the invariant. `Pass.checked` turns it into
a `Pass C` that falls back to the identity when the check fails. Only the checker needs
a proof; the transformer can be anything.

**Sequences.** `CheckedPass.seq c d` checks both steps and falls back to the *input* when
either fails, whereas `c.checked * d.checked` keeps the result of `c` when only `d`'s
check fails. They agree whenever both checks pass (`checked_seq_run_of_check`); when the first
fails, the checked sequence returns the input and the sequence of checked passes still
runs `d.checked` (`checked_seq_run_of_not_check₁`); they differ in general
(`checked_seq_ne_seq_checked`, on a two-program IR). The sequence of checked passes is
therefore the better-behaved composite; both are sound.

**Validation by normalisation** (`ofNormalizer`): with a verified pass `n` for a
symmetric contract, a decidable equality and a decidable invariant, `check x y :=
n.run x = n.run y ∧ Inv y` is a sound checker. The Binaryen IR has no `DecidableEq`
today (`Instr` derives only `Repr`), so the Binaryen example of this file is stated on a
small closed-arithmetic IR (`Toy`): constant folding validated by evaluating both sides.
-/

namespace Silmaril.Wasm.Binaryen.PassAPI

universe u

variable {X : Type u} {C : Contract X}

/-- **A checked pass**: an untrusted transformer and a verified checker. -/
structure CheckedPass (C : Contract X) where
  /-- Untrusted. -/
  transform : X → X
  /-- Verified. -/
  check : X → X → Bool
  check_sound : ∀ {x y}, check x y = true → C.Inv x → C.Rel x y ∧ C.Inv y

/-- **Checked passes are passes**: run the transformer, keep its result if it checks,
else return the input. -/
def Pass.checked (c : CheckedPass C) : Pass C where
  run x := if c.check x (c.transform x) then c.transform x else x
  inv_run {x} h := by
    by_cases hc : c.check x (c.transform x) = true
    · simp only [hc, ite_true]; exact (c.check_sound hc h).2
    · simp only [hc]; exact h
  sound {x} h := by
    by_cases hc : c.check x (c.transform x) = true
    · simp only [hc, ite_true]; exact (c.check_sound hc h).1
    · simp only [hc]; exact C.refl x

namespace CheckedPass

/-- Alias: `c.checked`. -/
abbrev checked (c : CheckedPass C) : Pass C := Pass.checked c

theorem checked_run (c : CheckedPass C) (x : X) :
    c.checked.run x = if c.check x (c.transform x) then c.transform x else x := rfl

theorem checked_run_of_check {c : CheckedPass C} {x : X}
    (h : c.check x (c.transform x) = true) : c.checked.run x = c.transform x := by
  simp [checked_run, h]

theorem checked_run_of_not_check {c : CheckedPass C} {x : X}
    (h : c.check x (c.transform x) = false) : c.checked.run x = x := by
  simp [checked_run, h]

/-- A verified pass is a checked pass whose checker recognises its own output. This needs
a decidable test `isRun x y` that implies `y = p.run x`. -/
def ofPass (p : Pass C) (isRun : X → X → Bool) (h : ∀ {x y}, isRun x y = true → y = p.run x) :
    CheckedPass C where
  transform := p.run
  check := isRun
  check_sound {x y} hc hx := by rw [h hc]; exact ⟨p.sound hx, p.inv_run hx⟩

/-- Sequencing checked passes: both transformers, both checks. -/
def seq (c d : CheckedPass C) : CheckedPass C where
  transform x := d.transform (c.transform x)
  check x z := c.check x (c.transform x) && d.check (c.transform x) z
  check_sound {x z} h hx := by
    simp only [Bool.and_eq_true] at h
    obtain ⟨r₁, i₁⟩ := c.check_sound h.1 hx
    obtain ⟨r₂, i₂⟩ := d.check_sound h.2 i₁
    exact ⟨C.trans r₁ r₂, i₂⟩

/-- When both checks pass, the checked sequence and the sequence of checked passes agree. -/
theorem checked_seq_run_of_check (c d : CheckedPass C) {x : X}
    (h₁ : c.check x (c.transform x) = true)
    (h₂ : d.check (c.transform x) (d.transform (c.transform x)) = true) :
    (c.seq d).checked.run x = (c.checked * d.checked).run x := by
  rw [Pass.mul_run, checked_run_of_check h₁, checked_run_of_check h₂, checked_run]
  simp [seq, h₁, h₂]

/-- When the first check fails, the checked sequence returns the input, while the
sequence of checked passes still runs `d.checked` on it. -/
theorem checked_seq_run_of_not_check₁ (c d : CheckedPass C) {x : X}
    (h₁ : c.check x (c.transform x) = false) :
    (c.seq d).checked.run x = x ∧ (c.checked * d.checked).run x = d.checked.run x := by
  refine ⟨?_, ?_⟩
  · rw [checked_run]; simp [seq, h₁]
  · rw [Pass.mul_run, checked_run_of_not_check h₁]

end CheckedPass

/-! ## A two-program counterexample -/

/-- The trivial contract on `Bool`: everything is a sound replacement. -/
def trivialContract : Contract Bool := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial,
  fun _ => True⟩

/-- Always produce `true`, always accept. -/
def cTrue : CheckedPass trivialContract := ⟨fun _ => true, fun _ _ => true, fun _ _ => ⟨trivial, trivial⟩⟩

/-- Do nothing, always reject. -/
def cReject : CheckedPass trivialContract :=
  ⟨fun b => b, fun _ _ => false, fun h _ => by simp at h⟩

/-- **The checked sequence is not the sequence of checked passes.** -/
theorem checked_seq_ne_seq_checked :
    (cTrue.seq cReject).checked ≠ cTrue.checked * cReject.checked := by
  intro h
  have := congrArg (fun p : Pass trivialContract => p.run false) h
  simp [CheckedPass.seq, cTrue, cReject, Pass.checked] at this

/-! ## Validation by normalisation -/

/-- **A checker from a verified normaliser.** For a contract whose relation is symmetric
on invariant-satisfying programs, accept `y` for `x` when they normalise to the same
program and `y` satisfies the invariant. -/
def ofNormalizer [DecidableEq X] [DecidablePred C.Inv] (n : Pass C)
    (hsymm : ∀ {x y}, C.Inv x → C.Rel x y → C.Rel y x) (transform : X → X) :
    CheckedPass C where
  transform := transform
  check x y := decide (n.run x = n.run y) && decide (C.Inv y)
  check_sound {x y} h hx := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨he, hy⟩ := h
    refine ⟨C.trans (n.sound hx) ?_, hy⟩
    rw [he]
    exact hsymm hy (n.sound hy)

/-! ## Toy IR: closed arithmetic, constant folding validated by evaluation -/

namespace Toy

/-- Closed arithmetic expressions. -/
inductive AExp where
  | lit (n : Nat)
  | add (a b : AExp)
  | mul (a b : AExp)
  deriving DecidableEq, Repr

/-- Evaluation (decidable semantics). -/
def AExp.eval : AExp → Nat
  | .lit n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- The contract: same value. -/
def contract : Contract AExp :=
  Contract.pullback (· = ·) (fun _ => rfl) (fun h₁ h₂ => h₁.trans h₂) AExp.eval (fun _ => True)

/-- An untrusted constant folder (it could be anything). -/
def cfold : AExp → AExp
  | .lit n => .lit n
  | .add a b => match cfold a, cfold b with
    | .lit x, .lit y => .lit (x + y)
    | a', b' => .add a' b'
  | .mul a b => match cfold a, cfold b with
    | .lit 0, _ => .lit 0
    | .lit x, .lit y => .lit (x * y)
    | a', b' => .mul a' b'

/-- **Constant folding as a checked pass**: the checker evaluates both sides. -/
def cfoldChecked : CheckedPass contract where
  transform := cfold
  check x y := x.eval == y.eval
  check_sound {_ _} h _ := ⟨(beq_iff_eq.mp h), trivial⟩

/-- The verified pass. -/
def cfoldPass : Pass contract := cfoldChecked.checked

/-- Soundness, by construction. -/
theorem cfoldPass_sound (e : AExp) : (cfoldPass.run e).eval = e.eval :=
  (show e.eval = (cfoldPass.run e).eval from cfoldPass.sound trivial).symm

end Toy

end Silmaril.Wasm.Binaryen.PassAPI
