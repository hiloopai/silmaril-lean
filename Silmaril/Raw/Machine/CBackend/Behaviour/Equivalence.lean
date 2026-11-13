module

public import Silmaril.Machine.CBackend.Behaviour.Refinement.Defs
/-!
# Contracts and program equivalence 

A `Contract` says which pairs of initial states are compared (`pre`) and how
outcomes are compared (`obs`, indexed by the initial pair). The precondition is
relational from the start: the single-state precondition runs both programs
from the same state and cannot express sequential congruence, where the second
halves start from different but related states. `Contract.diag` recovers the
single-state form.

`Refinement mode c p q` is `Refines ⟨mode, .forbidden⟩ p q c.pre c.obs`: `p`
refines `q` under the contract, exhaustion not allowed. `Equiv m c p q` is
refinement in both directions, the second under the converse contract
`c.flip`, so `Equiv = ⊑ ∩ ⊒` for the same observation .

`EquivMode` offers `strict` and `partial` (partial correctness,
`trapOrDiverge`). `divergeToTrap` is deliberately not an equivalence mode:
mutual `divergeToTrap` refinement between deterministic programs is already
`strict` equivalence (`mutual_divergeToTrap_strict`), so `divergeToTrap` is
exposed only as the refinement preorder `Refinement .divergeToTrap`. Without
determinism the collapse fails; see `Examples.mutual_not_equiv`.

Observations are meant to be partial equivalences (`Obs.IsPER`): values outside
their domain, such as an architecturally undefined x86 flag, are never
observed, and equality of such a value with itself is not required.
`Equiv.symm` and `Equiv.trans` take exactly the symmetry and transitivity
premises they use rather than a global PER assumption. `X86.FlagValue.Admits`
expresses the same idea in the target-to-source direction (a defined value
admitted by a possibly undefined specification); this file does not depend on
the x86 model.

A stuck state has no behaviour (`Semantics.Beh`), so `Refinement mode c p q`
holds trivially when `p` gets stuck from every related state. `Equiv` is not
trivial in this way unless both sides are: the reverse refinement asks every
behaviour of `q` to be matched by one of `p`.

Not provided here: sequential or loop congruence, frame conditions, a
checker, or instances for particular machines (those are in
`X86.Equiv.Behaviour` and `RiscV.Equiv.Behaviour`).
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour

open Semantics

variable {S R T F : Type*}

/-- What is assumed of a pair of initial states and observed of a pair of
outcomes. -/
structure Contract (S R T F : Type*) where
  pre : S → S → Prop
  obs : S → S → Obs R R T T F F

namespace Contract

/-- The single-state form: both programs start from the same state
satisfying `pre`. -/
def diag (pre : S → Prop) (obs : S → Obs R R T T F F) : Contract S R T F :=
  ⟨fun s s' => s = s' ∧ pre s, fun s _ => obs s⟩

/-- The converse contract, for the reverse refinement. -/
def flip (c : Contract S R T F) : Contract S R T F :=
  ⟨fun s s' => c.pre s' s, fun s s' => (c.obs s' s).flip⟩

@[simp] theorem flip_flip (c : Contract S R T F) : c.flip.flip = c := by
  cases c; rfl

/-- The contract is its own converse on its precondition. -/
def Symmetric (c : Contract S R T F) : Prop :=
  (∀ s s', c.pre s s' → c.pre s' s) ∧ ∀ s s', c.pre s s' → (c.obs s' s).flip ≤ c.obs s s'

theorem diag_symmetric {pre : S → Prop} {obs : S → Obs R R T T F F}
    (h : ∀ s, pre s → (obs s).flip ≤ obs s) : (diag pre obs).Symmetric := by
  refine ⟨fun s s' ⟨e, hs⟩ => ⟨e.symm, e ▸ hs⟩, fun s s' ⟨e, hs⟩ => ?_⟩
  subst e
  exact h s hs

end Contract

/-- The equivalence modes. `divergeToTrap` is excluded on purpose. -/
inductive EquivMode where
  | strict
  | «partial»
  deriving DecidableEq, Repr

def EquivMode.toFailure : EquivMode → FailureMode
  | .strict => .strict
  | .«partial» => .trapOrDiverge

/-- `p` refines `q` under the contract, without the exhaustion relaxation. -/
def Refinement (mode : FailureMode) (c : Contract S R T F) (p q : Semantics S R T F) : Prop :=
  Refines ⟨mode, .forbidden⟩ p q c.pre c.obs

/-- Refinement in both directions, the reverse one under the converse contract. -/
def Equiv (m : EquivMode) (c : Contract S R T F) (p q : Semantics S R T F) : Prop :=
  Refinement m.toFailure c p q ∧ Refinement m.toFailure c.flip q p

namespace Refinement

variable {f f' : FailureMode} {c c₁ c₂ : Contract S R T F} {p q r : Semantics S R T F}

theorem mono (hf : f ≤ f') (h : Refinement f c p q) : Refinement f' c p q :=
  Refines.mono (show (⟨f, .forbidden⟩ : Mode) ≤ ⟨f', .forbidden⟩ from ⟨hf, le_rfl⟩)
    (fun _ _ h => h) (fun _ _ _ => le_rfl) h

/-- Composition of refinements under composable contracts. -/
theorem trans (h₁ : Refinement f c₁ p q) (h₂ : Refinement f c₂ q r)
    (hpre : ∀ a b, c.pre a b → ∃ m, c₁.pre a m ∧ c₂.pre m b)
    (hobs : ∀ a m b, c.pre a b → c₁.pre a m → c₂.pre m b →
      (c₁.obs a m).comp (c₂.obs m b) ≤ c.obs a b) :
    Refinement f c p r := by
  have h := Refines.trans h₁ h₂ hpre hobs
  rwa [sup_idem] at h

end Refinement

namespace Equiv

variable {m : EquivMode} {c c₁ c₂ : Contract S R T F} {p q r : Semantics S R T F}

theorem flip (h : Equiv m c p q) : Equiv m c.flip q p :=
  ⟨h.2, by rw [Contract.flip_flip]; exact h.1⟩

/-- Symmetry for a symmetric contract. -/
theorem symm (hc : c.Symmetric) (h : Equiv m c p q) : Equiv m c q p := by
  refine ⟨Refines.mono le_rfl (fun s s' hs => hc.1 s s' hs) (fun s s' hs => hc.2 s s' hs) h.2,
    Refines.mono le_rfl (fun s s' hs => hc.1 s' s hs) (fun s s' hs => ?_) h.1⟩
  have := Obs.flip_mono (hc.2 s' s hs)
  rwa [Obs.flip_flip] at this

/-- Transitivity for composable contracts: every precondition pair factors
through a middle state, and the composite observation is covered. For
`c₁ = c₂ = c` these are transitivity of `pre` (through some middle state) and
of `obs`. -/
theorem trans (h₁ : Equiv m c₁ p q) (h₂ : Equiv m c₂ q r)
    (hpre : ∀ a b, c.pre a b → ∃ x, c₁.pre a x ∧ c₂.pre x b)
    (hobs : ∀ a x b, c.pre a b → c₁.pre a x → c₂.pre x b →
      (c₁.obs a x).comp (c₂.obs x b) ≤ c.obs a b) :
    Equiv m c p r := by
  refine ⟨h₁.1.trans h₂.1 hpre hobs, h₂.2.trans h₁.2 (fun b a hab => ?_) ?_⟩
  · obtain ⟨x, h₁', h₂'⟩ := hpre a b hab
    exact ⟨x, h₂', h₁'⟩
  · intro b x a hab h₂' h₁'
    have := Obs.flip_mono (hobs a x b hab h₁' h₂')
    rwa [Obs.flip_comp] at this

/-- Reflexivity on a contract that only compares a state with itself and
observes reflexively there. -/
theorem refl_on (hpre : ∀ s s', c.pre s s' → s = s')
    (hobs : ∀ s, c.pre s s → (c.obs s s).IsRefl) : Equiv m c p p := by
  constructor
  · intro t s hts _ o ho
    obtain rfl := hpre t s hts
    exact ⟨o, ho, Outcome.Rel.refl (hobs t hts) _ o⟩
  · intro t s hts _ o ho
    obtain rfl := hpre s t hts
    exact ⟨o, ho, Outcome.Rel.refl (hobs _ hts).flip _ o⟩

theorem strict_partial (h : Equiv .strict c p q) : Equiv .«partial» c p q :=
  ⟨h.1.mono (FailureMode.strict_le _), h.2.mono (FailureMode.strict_le _)⟩

end Equiv

/-- Mutual `divergeToTrap` refinement of deterministic programs is `strict`
equivalence: a target trap may implement a source divergence, but then the
reverse refinement would have to implement that trap by a divergence, which
`divergeToTrap` forbids. Both determinism premises are used, one per
direction. The statement fails without them: `Examples.mutual_not_equiv` has
a nondeterministic `p` with behaviours `{trapped, diverges}` and a `q` with
behaviours `{diverges}`. -/
theorem mutual_divergeToTrap_strict {c : Contract S R T F} {p q : Semantics S R T F}
    (hp : p.Deterministic) (hq : q.Deterministic)
    (h₁ : Refinement .divergeToTrap c p q) (h₂ : Refinement .divergeToTrap c.flip q p) :
    Equiv .strict c p q := by
  constructor
  · intro t s hts hs o ho
    obtain ⟨o', ho', hr⟩ := h₁ t s hts hs o ho
    obtain ⟨o'', ho'', hr'⟩ := h₂ s t hts (h₁.safe hts hs) o' ho'
    rw [Beh.unique hp ho'' ho] at hr'
    exact ⟨o', ho', hr.strict_of_mutual hr'⟩
  · intro s t hst ht o ho
    obtain ⟨o', ho', hr⟩ := h₂ s t hst ht o ho
    obtain ⟨o'', ho'', hr'⟩ := h₁ t s hst (h₂.safe hst ht) o' ho'
    rw [Beh.unique hq ho'' ho] at hr'
    exact ⟨o', ho', hr.strict_of_mutual hr'⟩

end Silmaril.Machine.Behaviour
