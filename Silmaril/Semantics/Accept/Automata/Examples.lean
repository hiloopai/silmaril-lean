module

public import Silmaril.Semantics.Accept.Automata.Thms

/-! # Automata as acceptor presentations: worked examples and regression tests

The byte DFA `digitsDFA` for `[0-9]+` evaluated by `decide`/`rfl`, membership in `digitsLang`
derived from the checker, and two NFAs on which existential and universal acceptance of the
reachable-state runner differ. Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.AutomataExamples

open Silmaril.Accept Silmaril.Accept.Automata

/-! ## `[0-9]+` over bytes -/

example : digitsCheck [0x30] = true := by decide
example : digitsCheck [0x31, 0x32, 0x39] = true := by decide
example : digitsCheck [] = false := by decide
example : digitsCheck [0x2F] = false := by decide          -- '/' is just below '0'
example : digitsCheck [0x3A] = false := by decide          -- ':' is just above '9'
example : digitsCheck [0x31, 0x20, 0x32] = false := by decide
example : digitsCheck [0x41, 0x31] = false := by decide    -- a later digit does not revive `dead`

example : digitsDFA.eval [0x41, 0x31] = .dead := rfl
example : digitsDFA.eval [0x35] = .digits := rfl

/-- Membership in the specification, derived from one checker run. -/
example : [0x34, 0x32] ∈ digitsLang := (decides_digitsCheck _).mp (by decide)
example : [0x34, 0x2E] ∉ digitsLang := fun h => absurd ((decides_digitsCheck _).mpr h) (by decide)

/-- The same language through Mathlib's NFA and CSLib's acceptor. -/
example : digitsDFA.toNFA.accepts = digitsLang := by
  rw [DFA.toNFA_correct, accepts_digitsDFA]
example : Cslib.Automata.Acceptor.language (toCslibDA digitsDFA) = digitsLang :=
  accepts_digitsDFA
example : digitsLang.IsRegular := isRegular_digitsLang

/-! ## Existential and universal acceptance of an NFA differ -/

/-- Two start states that loop on every symbol; only `true` accepts. -/
def twoStarts : NFA Unit Bool := ⟨fun s _ => {s}, Set.univ, {true}⟩

/-- `[]` is accepted: the start state `true` accepts. -/
example : [] ∈ twoStarts.accepts := ⟨true, rfl, trivial⟩

/-- … but not universally: the start state `false` is also reachable on `[]`. -/
example : [] ∉ acceptsAll (nfaRun twoStarts) twoStarts.accept :=
  fun h => Bool.false_ne_true (h false trivial)

/-- An NFA with no start state accepts nothing, but universal acceptance is vacuous. -/
def noStart : NFA Unit Bool := ⟨fun s _ => {s}, ∅, {true}⟩

example : acceptsAll (nfaRun noStart) noStart.accept ≠ noStart.accepts :=
  acceptsAll_nfaRun_ne_accepts_of_start_eq_empty noStart rfl

end Silmaril.Accept.AutomataExamples
