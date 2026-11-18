module

public import Silmaril.Logic.Consequence.Arithmetic.Derivation.Defs
public import Silmaril.Logic.Consequence.Arithmetic.Thms
public import Silmaril.Logic.Consequence.Derivation.Thms
import Silmaril.Proofs.Logic.Consequence.Arithmetic.Derivation.Basic

/-!
# Peano and Robinson arithmetic as derivation systems: agreement, soundness, consistency

* `locallySound_derivable`: each rule instance is a step of `Derivation` (every label is checked
  against the existing natural deduction, never trusted).
* `locallySound_valid`: each rule instance is valid in ℕ.
* `tree_iff`: a judgment has a valid proof tree exactly when it has a `Derivation`;
  `treeDerives_pa : treeDerives .pa = paDerives` and `treeDerives_q : treeDerives .q = qDerives`.
* `treeDerives_soundFor`: the tree systems are sound for truth in ℕ, by local soundness, and
  `pa_tree_consistent` / `q_tree_consistent`: they do not derive `⊥` from no premises.
-/

@[expose] public section

namespace Silmaril.Consequence.Arithmetic.ND

open Silmaril.Logic.Arithmetic Silmaril.Proofs.Logic.Consequence.Arithmetic.Derivation

/-- **Every rule instance is a `Derivation` step.** -/
theorem locallySound_derivable (T : Theory) :
    (system T).LocallySound (fun (_ : Unit) (s : Seq) => s.Derivable T) :=
  fun _ r _ _ ⟨hs, hp, hc⟩ hps => hc ▸ rule_derivable r.2 hs (hp ▸ hps)

/-- **Every rule instance is valid in ℕ.** -/
theorem locallySound_valid (T : Theory) :
    (system T).LocallySound (fun (_ : Unit) (s : Seq) => s.Valid) :=
  fun _ r _ _ ⟨hs, hp, hc⟩ hps => hc ▸ rule_valid r.2 hs (hp ▸ hps)

/-- **Proof trees and `Derivation` agree**: a judgment has a valid tree from no assumptions
exactly when it has a derivation. -/
theorem tree_iff (T : Theory) (s : Seq) : (system T).derives [] s ↔ s.Derivable T :=
  ⟨fun h => DerivationSystem.derives_soundFor (locallySound_derivable T) [] s h ()
      (fun _ h => nomatch h),
   fun ⟨d⟩ => tree_of_derivation d⟩

/-- **Tree-checked PA is PA.** -/
theorem treeDerives_pa : treeDerives .pa = paDerives := by
  funext Γ φ; exact propext (tree_iff .pa ⟨0, Γ, φ⟩)

/-- **Tree-checked Q is Q.** -/
theorem treeDerives_q : treeDerives .q = qDerives := by
  funext Γ φ; exact propext (tree_iff .q ⟨0, Γ, φ⟩)

/-- **Soundness for truth in ℕ**, from local soundness. -/
theorem treeDerives_soundFor (T : Theory) : (treeDerives T).SoundFor standard :=
  fun Γ φ h _ hΓ =>
    DerivationSystem.derives_soundFor (locallySound_valid T) [] ⟨0, Γ, φ⟩ h ()
      (fun _ h => nomatch h) Fin.elim0 hΓ

/-- **Tree-checked PA does not derive `⊥`.** -/
theorem pa_tree_consistent : (treeDerives .pa).ConsistentWrt .bot [] :=
  consistentWrt_of_sound (treeDerives_soundFor .pa) () (by simp [standard, Satisfies])
    (by simp [standard, Formula.eval])

/-- **Tree-checked Q does not derive `⊥`.** -/
theorem q_tree_consistent : (treeDerives .q).ConsistentWrt .bot [] :=
  consistentWrt_of_sound (treeDerives_soundFor .q) () (by simp [standard, Satisfies])
    (by simp [standard, Formula.eval])

/-- **The checker decides PA proof trees**: a tree that checks derives its conclusion. -/
theorem derives_of_check (T : Theory) {t : (system T).Proof}
    (h : (system T).check [] t = true) : t.concl.Derivable T :=
  (tree_iff T _).1 (DerivationSystem.derives_of_check h)

end Silmaril.Consequence.Arithmetic.ND
