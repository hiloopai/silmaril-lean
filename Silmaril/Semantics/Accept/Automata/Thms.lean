module

public import Silmaril.Semantics.Accept.Automata.Defs
public import Silmaril.Semantics.Accept.Thms
import Silmaril.Proofs.Semantics.Accept.Automata.Basic

/-!
# State-machine presentations of acceptor sets: laws

* checkers: `decides_dfaChecker` and the sound/complete/decides bridges
  `sound_dfaChecker_iff`, `complete_dfaChecker_iff`, `decides_dfaChecker_iff`;
* runners: on `dfaRun` existential and universal acceptance coincide with `DFA.accepts`
  (`acceptsSome_dfaRun`, `acceptsAll_dfaRun`); `NFA.accepts` and `εNFA.accepts` are existential
  acceptance of the reachable-state runner (`accepts_eq_acceptsSome_nfaRun`,
  `accepts_eq_acceptsSome_εnfaRun`); universal acceptance of that runner is a different language
  in general (`acceptsAll_nfaRun_ne_accepts_of_start_eq_empty`), agrees on DFA-shaped NFAs
  (`acceptsAll_nfaRun_toNFA`) and is contained in it when every word reaches some state
  (`acceptsAll_nfaRun_subset_accepts`);
* presentations: transport along `DFA.toNFA`, `NFA.toDFA`, `εNFA.toNFA`, and regularity of
  finite-state presentations;
* CSLib: `Acceptor.language` of `toCslibDA`/`toCslibNA` is `DFA.accepts`/`NFA.accepts`, also
  after CSLib's own `toNAFinAcc`/`toDAFinAcc` conversions;
* bytes: `digitsDFA` presents `digitsLang` and `digitsCheck` decides it.
-/

@[expose] public section

namespace Silmaril.Accept.Automata

open Silmaril.Accept Cslib.Automata

universe u v

variable {α : Type u} {σ : Type v}

/-! ## Checkers -/

section Checker

variable (M : DFA α σ) [DecidablePred (· ∈ M.accept)] {L : Language α}

@[simp] theorem dfaChecker_eq_true {w : List α} : dfaChecker M w = true ↔ w ∈ M.accepts :=
  decide_eq_true_iff

/-- The checker of a DFA decides the DFA's language. -/
theorem decides_dfaChecker : Decides (dfaChecker M) M.accepts := fun _ => dfaChecker_eq_true M

theorem ofBool_dfaChecker : ofBool (dfaChecker M) = M.accepts :=
  decides_iff_ofBool_eq.mp (decides_dfaChecker M)

theorem sound_dfaChecker_iff : Sound (dfaChecker M) L ↔ DFASound M L :=
  ⟨fun h w hw => h w ((dfaChecker_eq_true M).2 hw),
    fun h _ hw => h ((dfaChecker_eq_true M).1 hw)⟩

theorem complete_dfaChecker_iff : Complete (dfaChecker M) L ↔ DFAComplete M L :=
  ⟨fun h w hw => (dfaChecker_eq_true M).1 (h w hw),
    fun h _ hw => (dfaChecker_eq_true M).2 (h hw)⟩

theorem decides_dfaChecker_iff : Decides (dfaChecker M) L ↔ DFAPresents M L :=
  ⟨fun h => (ofBool_dfaChecker M).symm.trans (decides_iff_ofBool_eq.mp h),
    fun h => decides_iff_ofBool_eq.mpr ((ofBool_dfaChecker M).trans h)⟩

end Checker

/-! ## Runners -/

/-- On the deterministic runner of a DFA, existential acceptance is the DFA's language. -/
theorem acceptsSome_dfaRun (M : DFA α σ) : acceptsSome (dfaRun M) M.accept = M.accepts :=
  acceptsSome_detRun

/-- On the deterministic runner of a DFA, universal acceptance is the DFA's language too. -/
theorem acceptsAll_dfaRun (M : DFA α σ) : acceptsAll (dfaRun M) M.accept = M.accepts :=
  acceptsAll_detRun

theorem acceptsSome_dfaRun_eq_acceptsAll (M : DFA α σ) :
    acceptsSome (dfaRun M) M.accept = acceptsAll (dfaRun M) M.accept := by
  rw [acceptsSome_dfaRun, acceptsAll_dfaRun]

/-- NFA acceptance is existential: some state reachable on `w` accepts. -/
theorem accepts_eq_acceptsSome_nfaRun (M : NFA α σ) :
    M.accepts = acceptsSome (nfaRun M) M.accept :=
  Proofs.Semantics.Accept.Automata.accepts_eq_acceptsSome_nfaRun M

/-- ε-NFA acceptance is existential over the ε-closed reachable states. -/
theorem accepts_eq_acceptsSome_εnfaRun (M : εNFA α σ) :
    M.accepts = acceptsSome (εnfaRun M) M.accept :=
  Proofs.Semantics.Accept.Automata.accepts_eq_acceptsSome_εnfaRun M

/-- The NFA of a DFA has exactly one reachable state on every word. -/
theorem nfaRun_toNFA (M : DFA α σ) : nfaRun M.toNFA = dfaRun M :=
  Proofs.Semantics.Accept.Automata.nfaRun_toNFA M

/-- On DFA-shaped NFAs universal acceptance agrees with NFA acceptance. -/
theorem acceptsAll_nfaRun_toNFA (M : DFA α σ) :
    acceptsAll (nfaRun M.toNFA) M.toNFA.accept = M.toNFA.accepts := by
  rw [nfaRun_toNFA, DFA.toNFA_correct]; exact acceptsAll_dfaRun M

/-- If every word reaches some state, universal acceptance implies NFA acceptance. -/
theorem acceptsAll_nfaRun_subset_accepts (M : NFA α σ) (h : ∀ w, (M.eval w).Nonempty) :
    acceptsAll (nfaRun M) M.accept ⊆ M.accepts := by
  rw [accepts_eq_acceptsSome_nfaRun]; exact acceptsAll_subset_acceptsSome h

theorem nfaRun_of_start_eq_empty (M : NFA α σ) (h : M.start = ∅) (w : List α) :
    nfaRun M w = ∅ :=
  Proofs.Semantics.Accept.Automata.nfaRun_of_start_eq_empty M h w

/-- With no start state the NFA accepts nothing, while universal acceptance is vacuous: the two
quantifiers over the same runner give different languages. -/
theorem acceptsAll_nfaRun_ne_accepts_of_start_eq_empty (M : NFA α σ) (h : M.start = ∅) :
    acceptsAll (nfaRun M) M.accept ≠ M.accepts :=
  Proofs.Semantics.Accept.Automata.acceptsAll_nfaRun_ne_accepts_of_start_eq_empty M h

/-! ## Presentations -/

section Presents

variable {L : Language α}

theorem dfaPresents_iff (M : DFA α σ) : DFAPresents M L ↔ DFASound M L ∧ DFAComplete M L :=
  le_antisymm_iff

theorem nfaPresents_iff (M : NFA α σ) : NFAPresents M L ↔ NFASound M L ∧ NFAComplete M L :=
  le_antisymm_iff

@[simp] theorem nfaSound_toNFA (M : DFA α σ) : NFASound M.toNFA L ↔ DFASound M L := by
  rw [NFASound, DFA.toNFA_correct]; rfl

@[simp] theorem nfaComplete_toNFA (M : DFA α σ) : NFAComplete M.toNFA L ↔ DFAComplete M L := by
  rw [NFAComplete, DFA.toNFA_correct]; rfl

@[simp] theorem nfaPresents_toNFA (M : DFA α σ) : NFAPresents M.toNFA L ↔ DFAPresents M L := by
  rw [NFAPresents, DFA.toNFA_correct]; rfl

@[simp] theorem dfaSound_toDFA (M : NFA α σ) : DFASound M.toDFA L ↔ NFASound M L := by
  rw [DFASound, NFA.toDFA_correct]; rfl

@[simp] theorem dfaComplete_toDFA (M : NFA α σ) : DFAComplete M.toDFA L ↔ NFAComplete M L := by
  rw [DFAComplete, NFA.toDFA_correct]; rfl

@[simp] theorem dfaPresents_toDFA (M : NFA α σ) : DFAPresents M.toDFA L ↔ NFAPresents M L := by
  rw [DFAPresents, NFA.toDFA_correct]; rfl

theorem nfaSound_εNFA_toNFA (M : εNFA α σ) : NFASound M.toNFA L ↔ M.accepts ≤ L := by
  rw [NFASound, εNFA.toNFA_correct]

theorem nfaComplete_εNFA_toNFA (M : εNFA α σ) : NFAComplete M.toNFA L ↔ L ≤ M.accepts := by
  rw [NFAComplete, εNFA.toNFA_correct]

theorem nfaPresents_εNFA_toNFA (M : εNFA α σ) : NFAPresents M.toNFA L ↔ M.accepts = L := by
  rw [NFAPresents, εNFA.toNFA_correct]

/-- A finite-state DFA presentation makes the language regular (Mathlib's `IsRegular`). -/
theorem DFAPresents.isRegular {M : DFA α σ} [Fintype σ] (h : DFAPresents M L) : L.IsRegular :=
  Language.isRegular_iff.mpr ⟨σ, inferInstance, M, h⟩

/-- A finite-state NFA presentation makes the language regular (via the subset construction). -/
theorem NFAPresents.isRegular {M : NFA α σ} [Finite σ] (h : NFAPresents M L) : L.IsRegular :=
  have := Fintype.ofFinite σ
  ((dfaPresents_toDFA M).mpr h).isRegular

end Presents

/-! ## CSLib automata -/

/-- CSLib's language of the converted DFA is the Mathlib language. -/
@[simp] theorem language_toCslibDA (M : DFA α σ) :
    Acceptor.language (toCslibDA M) = M.accepts := rfl

@[simp] theorem accepts_ofCslibDA (A : DA.FinAcc σ α) :
    (ofCslibDA A).accepts = Acceptor.language A := rfl

@[simp] theorem ofCslibDA_toCslibDA (M : DFA α σ) : ofCslibDA (toCslibDA M) = M := rfl

@[simp] theorem toCslibDA_ofCslibDA (A : DA.FinAcc σ α) : toCslibDA (ofCslibDA A) = A := rfl

/-- CSLib's language of the converted NFA is the Mathlib language. -/
@[simp] theorem language_toCslibNA (M : NFA α σ) :
    Acceptor.language (toCslibNA M) = M.accepts :=
  Proofs.Semantics.Accept.Automata.language_toCslibNA M

/-- CSLib's DA-to-NA conversion agrees with Mathlib's `DFA.toNFA` on languages. -/
theorem language_toNAFinAcc_toCslibDA (M : DFA α σ) :
    Acceptor.language (toCslibDA M).toNAFinAcc = M.toNFA.accepts := by
  rw [DA.FinAcc.toNAFinAcc_language_eq, DFA.toNFA_correct]; rfl

/-- CSLib's subset construction agrees with Mathlib's `NFA.toDFA` on languages. -/
theorem language_toDAFinAcc_toCslibNA (M : NFA α σ) :
    Acceptor.language (toCslibNA M).toDAFinAcc = M.toDFA.accepts := by
  rw [NA.FinAcc.toDAFinAcc_language_eq, NFA.toDFA_correct, language_toCslibNA]

/-! ## Bytes: ASCII decimal numerals -/

theorem mem_digitsLang {w : List UInt8} :
    w ∈ digitsLang ↔ w ≠ [] ∧ ∀ b ∈ w, isDigit b = true := Iff.rfl

/-- `digitsDFA` accepts exactly the ASCII decimal numerals `[0-9]+` (sound and complete). -/
theorem accepts_digitsDFA : digitsDFA.accepts = digitsLang :=
  Proofs.Semantics.Accept.Automata.accepts_digitsDFA

theorem dfaPresents_digitsDFA : DFAPresents digitsDFA digitsLang := accepts_digitsDFA

/-- The byte checker accepts exactly `[0-9]+`. -/
theorem decides_digitsCheck : Decides digitsCheck digitsLang :=
  (decides_dfaChecker_iff digitsDFA).mpr dfaPresents_digitsDFA

theorem isRegular_digitsLang : digitsLang.IsRegular := dfaPresents_digitsDFA.isRegular

end Silmaril.Accept.Automata
