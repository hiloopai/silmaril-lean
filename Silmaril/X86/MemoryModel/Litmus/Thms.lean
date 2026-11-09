module

public import Silmaril.X86.MemoryModel.Litmus.Defs

/-!
# x86 litmus tests: generic facts about verdicts

PROVED (no `sorry`, no new axiom):

* `allowed_mono`: a witness reachable in a smaller set of final states is reachable in a
  larger one. With `Reach_SC ⊆ Reach_TSO ⊆ Reach_XL` this gives the per-test inclusions
  `SC ⊆ TSO ⊆ XL` for *allowed* verdicts;
* `forbidden_anti`: a witness forbidden in a larger set is forbidden in a smaller one (so a
  verdict proved for XL transfers to TSO and SC);
* `witness_forall`, `witness_exists`, `witness_notExists`: what `Test.witness` is.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

/-- Allowed is monotone in the set of reachable final states. -/
theorem allowed_mono {t : Test} {R R' : Final → Prop} (h : ∀ f, R f → R' f)
    (ha : t.Allowed R) : t.Allowed R' := by
  obtain ⟨f, hf, hw⟩ := ha
  exact ⟨f, h f hf, hw⟩

/-- Forbidden is antitone in the set of reachable final states. -/
theorem forbidden_anti {t : Test} {R R' : Final → Prop} (h : ∀ f, R f → R' f)
    (hb : Verdict.forbidden.Holds t R') : Verdict.forbidden.Holds t R :=
  fun ha => hb (allowed_mono h ha)

theorem witness_forall {t : Test} (h : t.quant = .forall_) : t.witness = .not t.cond := by
  simp [Test.witness, h]

theorem witness_exists {t : Test} (h : t.quant = .exists_) : t.witness = t.cond := by
  simp [Test.witness, h]

theorem witness_notExists {t : Test} (h : t.quant = .notExists) : t.witness = t.cond := by
  simp [Test.witness, h]

end Silmaril.X86.MemoryModel.Litmus
