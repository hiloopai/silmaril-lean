module

public import Silmaril.Semantics.Accept.Defs
public import Mathlib.Computability.EpsilonNFA
public import Cslib.Computability.Automata.DA.ToNA
public import Cslib.Computability.Automata.NA.ToDA

/-!
# State-machine presentations of acceptor sets

Finite automata are one way to *present* a language `Language α = Set (List α)`. This file
does not define automata: it reuses Mathlib's `DFA`, `NFA` and `εNFA`
(`Mathlib/Computability/{DFA,NFA,EpsilonNFA}.lean`) and CSLib's `DA.FinAcc` and `NA.FinAcc`
(`Cslib/Computability/Automata/…`), and connects them to the generic acceptor vocabulary of
`Silmaril.Semantics.Accept` (`Decides`, `acceptsSome`, `acceptsAll`, `detRun`).

## Checkers and runners

* `dfaChecker M`: the Bool checker `fun w => decide (M.eval w ∈ M.accept)` of a DFA with a
  decidable accept set. It `Decides M.accepts` (`Thms`).
* `dfaRun M`: the deterministic runner `detRun M.eval`. Existential and universal acceptance
  coincide on it, and both are `M.accepts`.
* `nfaRun M` / `εnfaRun M`: the runner `fun w => M.eval w` returning the *set* of states
  reachable on `w`. `M.accepts` is `acceptsSome` of this runner (existential acceptance);
  `acceptsAll` of the same runner is in general a *different* language (`Thms`, `Examples`).

## Presentations

For a target language `L`:

* `DFASound M L` / `NFASound M L`: the automaton accepts only words of `L`
  (`M.accepts ≤ L`, i.e. `⊆`).
* `DFAComplete M L` / `NFAComplete M L`: it accepts every word of `L` (`L ≤ M.accepts`).
* `DFAPresents M L` / `NFAPresents M L`: both (`M.accepts = L`).

These transport along Mathlib's conversions `DFA.toNFA`, `NFA.toDFA` and `εNFA.toNFA`.

## CSLib

* `toCslibDA M` / `ofCslibDA A`: a Mathlib `DFA α σ` and a CSLib `DA.FinAcc σ α` are the same
  data (transition function, start state, accept set), and the CSLib `Acceptor.language` agrees
  with `DFA.accepts`.
* `toCslibNA M`: a Mathlib `NFA α σ` as a CSLib `NA.FinAcc σ α` (transition relation
  `s' ∈ M.step s a`); its `Acceptor.language` is `NFA.accepts`.

## Bytes

Automata over `UInt8` present byte languages `Language UInt8`. The worked example is
`digitsDFA`, a three-state DFA for the ASCII decimal numerals `[0-9]+`, with the language
`digitsLang` it presents.
-/

@[expose] public section

namespace Silmaril.Accept.Automata

universe u v

variable {α : Type u} {σ : Type v}

/-! ## Checkers and runners -/

/-- The Bool checker of a DFA with a decidable accept set: run it and test the final state. -/
def dfaChecker (M : DFA α σ) [DecidablePred (· ∈ M.accept)] : List α → Bool :=
  fun w => decide (M.eval w ∈ M.accept)

/-- A DFA as a deterministic runner: the single outcome of `w` is the state `M.eval w`. -/
def dfaRun (M : DFA α σ) : List α → Set σ := detRun M.eval

/-- An NFA as a nondeterministic runner: the outcomes of `w` are the states reachable on `w`. -/
def nfaRun (M : NFA α σ) : List α → Set σ := fun w => M.eval w

/-- An ε-NFA as a nondeterministic runner (states reachable on `w`, closed under ε-moves). -/
def εnfaRun (M : εNFA α σ) : List α → Set σ := fun w => M.eval w

/-! ## Presentations of a target language -/

/-- A DFA is sound for `L`: everything it accepts lies in `L`. -/
def DFASound (M : DFA α σ) (L : Language α) : Prop := M.accepts ≤ L

/-- A DFA is complete for `L`: it accepts every word of `L`. -/
def DFAComplete (M : DFA α σ) (L : Language α) : Prop := L ≤ M.accepts

/-- A DFA presents `L`: it accepts exactly the words of `L`. -/
def DFAPresents (M : DFA α σ) (L : Language α) : Prop := M.accepts = L

/-- An NFA is sound for `L`: everything it accepts lies in `L`. -/
def NFASound (M : NFA α σ) (L : Language α) : Prop := M.accepts ≤ L

/-- An NFA is complete for `L`: it accepts every word of `L`. -/
def NFAComplete (M : NFA α σ) (L : Language α) : Prop := L ≤ M.accepts

/-- An NFA presents `L`: it accepts exactly the words of `L`. -/
def NFAPresents (M : NFA α σ) (L : Language α) : Prop := M.accepts = L

/-! ## CSLib automata -/

/-- A Mathlib DFA as a CSLib deterministic finite-word acceptor (same data). -/
def toCslibDA (M : DFA α σ) : Cslib.Automata.DA.FinAcc σ α :=
  ⟨⟨⟨M.step⟩, M.start⟩, M.accept⟩

/-- A CSLib deterministic finite-word acceptor as a Mathlib DFA (same data). -/
def ofCslibDA (A : Cslib.Automata.DA.FinAcc σ α) : DFA α σ :=
  ⟨A.tr, A.start, A.accept⟩

/-- A Mathlib NFA as a CSLib nondeterministic finite-word acceptor: `s →a s'` iff
`s' ∈ M.step s a`. -/
def toCslibNA (M : NFA α σ) : Cslib.Automata.NA.FinAcc σ α :=
  ⟨⟨⟨fun s a s' => s' ∈ M.step s a⟩, M.start⟩, M.accept⟩

/-! ## Bytes: ASCII decimal numerals -/

/-- `b` is an ASCII decimal digit `'0'`–`'9'` (`0x30`–`0x39`). -/
def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

/-- The ASCII decimal numerals `[0-9]+`: nonempty byte strings of digits. -/
def digitsLang : Language UInt8 := {w | w ≠ [] ∧ ∀ b ∈ w, isDigit b = true}

/-- States of `digitsDFA`: nothing read yet, at least one digit read, or a non-digit seen. -/
inductive DigitState
  | start
  | digits
  | dead
  deriving DecidableEq, Repr

instance : Fintype DigitState :=
  ⟨{.start, .digits, .dead}, fun s => by cases s <;> simp⟩

/-- The DFA of `[0-9]+` over bytes. A digit moves `start` or `digits` to `digits`; any other
byte, or any byte in `dead`, moves to `dead`. Only `digits` accepts. -/
def digitsDFA : DFA UInt8 DigitState where
  step
    | .dead, _ => .dead
    | _, b => if isDigit b then .digits else .dead
  start := .start
  accept := {s | s = .digits}

instance : DecidablePred (· ∈ digitsDFA.accept) :=
  inferInstanceAs (DecidablePred (· = DigitState.digits))

/-- The byte checker of `digitsDFA`. -/
def digitsCheck : List UInt8 → Bool := dfaChecker digitsDFA

end Silmaril.Accept.Automata
