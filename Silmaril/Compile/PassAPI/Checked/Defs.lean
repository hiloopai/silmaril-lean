module

public import Silmaril.Compile.PassAPI.Pass
import Silmaril.Proofs.Compile.PassAPI.Checked.Construction

@[expose] public section

/-! # Checked program transformations

A `CheckedPass C` combines an untrusted transformation with a checker whose
acceptances are proved sound. Whenever `check x y = true` and `C.Inv x`, the
candidate `y` is an acceptable replacement and satisfies the invariant.
`Pass.checked` retains that candidate when accepted and otherwise returns the
original input. No completeness or acceptance-rate guarantee is required.

The two sequencing operations have different failure behavior.
`CheckedPass.seq c d` checks both proposed steps and returns the original input
if either check fails. In contrast, `c.checked * d.checked` checks and falls back
at each step: it retains the first result if only the second check fails, and
still tries the second checked pass if the first check fails. They agree when
both checks pass; `checked_seq_ne_seq_checked` proves that they differ in general.
Both constructions are sound.

`ofNormalizer` constructs a checker for a symmetric contract by comparing the
outputs of a verified pass and checking the candidate's invariant. It requires
decidable equality and a decidable invariant. The closed arithmetic example in
`Toy` validates a proposed constant fold by evaluating both expressions.
-/

namespace Silmaril.Compile.PassAPI

universe u
variable {X : Type u} {C : Contract X}

/-- **A checked pass**: an untrusted transformer and a verified checker. -/
structure CheckedPass (C : Contract X) where
  /-- Untrusted. -/
  transform : X → X
  /-- Verified. -/
  check : X → X → Bool
  check_sound : ∀ {x y}, check x y = true → C.Inv x → C.Rel x y ∧ C.Inv y

/-- Run the transformer, keep its result if it checks, otherwise return the input. -/
def Pass.checked (c : CheckedPass C) : Pass C where
  run x := if c.check x (c.transform x) then c.transform x else x
  inv_run h := by exact (Proofs.Checked.checked_spec c.transform c.check c.check_sound h).1
  sound h := by exact (Proofs.Checked.checked_spec c.transform c.check c.check_sound h).2

namespace CheckedPass

/-- Alias: `c.checked`. -/
abbrev checked (c : CheckedPass C) : Pass C := Pass.checked c

/-- Recognize the output of a verified pass. Completeness is not required. -/
def ofPass (p : Pass C) (isRun : X → X → Bool)
    (h : ∀ {x y}, isRun x y = true → y = p.run x) : CheckedPass C where
  transform := p.run
  check := isRun
  check_sound hc hx := by rw [h hc]; exact ⟨p.sound hx, p.inv_run hx⟩

/-- Run both transformers; acceptance requires both checks. -/
def seq (c d : CheckedPass C) : CheckedPass C where
  transform x := d.transform (c.transform x)
  check x z := c.check x (c.transform x) && d.check (c.transform x) z
  check_sound h hx := by
    exact Proofs.Checked.seq_sound c.transform c.check d.check c.check_sound d.check_sound h hx

end CheckedPass

/-- Accept invariant-satisfying candidates with the same verified normal form.
The contract relation must be symmetric on invariant-satisfying inputs. -/
def ofNormalizer [DecidableEq X] [DecidablePred C.Inv] (n : Pass C)
    (hsymm : ∀ {x y}, C.Inv x → C.Rel x y → C.Rel y x) (transform : X → X) :
    CheckedPass C where
  transform := transform
  check x y := decide (n.run x = n.run y) && decide (C.Inv y)
  check_sound h hx := by exact Proofs.Checked.normalizer_sound n hsymm h hx

/-! Compatibility witnesses for the published sequencing counterexample. Its
argument is in `Silmaril.Proofs.Compile.PassAPI.Checked.Correctness`. -/

/-- The trivial contract on `Bool`: everything is a sound replacement. -/
def trivialContract : Contract Bool := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial,
  fun _ => True⟩

/-- Always produce `true`, always accept. -/
def cTrue : CheckedPass trivialContract :=
  ⟨fun _ => true, fun _ _ => true, fun _ _ => ⟨trivial, trivial⟩⟩

/-- Do nothing, always reject. -/
def cReject : CheckedPass trivialContract :=
  ⟨fun b => b, fun _ _ => false, fun h _ => by simp at h⟩

/-! ## Compatibility example

The original `Toy` declarations are retained here, including the inductive's
constructors and recursors. They are examples, not a compiler IR interface.
-/

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

end Toy

end Silmaril.Compile.PassAPI
