module

public import Silmaril.Logic.Consequence.FirstOrder.Derivation.Defs
public import Silmaril.Logic.Consequence.FirstOrder.Thms
public import Silmaril.Logic.Consequence.Derivation.Thms
import Silmaril.Proofs.Logic.Consequence.FirstOrder.Derivation

/-!
# First-order natural deduction: soundness and consistency

* `locallySound`: every rule instance preserves validity in every structure.
* `treeDerives_le_consequence`: checked proof trees derive only semantic consequences
  (`consequence Sg`, truth in every structure), and `treeDerives_soundFor`: they are sound for the
  interpretation in any one structure.
* `orderTheory_tree_consistent`: over `orderSig`, the order theory does not derive `¬⊤`, by the
  model ℕ.
-/

@[expose] public section

namespace Silmaril.Consequence.FirstOrder.ND

open Silmaril.Logic.Institution.Examples.UFOL

variable {Sg : Signature} [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)]

/-- **Every rule instance is valid in every structure.** -/
theorem locallySound :
    (system Sg).LocallySound (fun (M : Structure Sg) (s : Seq Sg) => s.ValidIn M) :=
  fun M r _ _ ⟨hs, hp, hc⟩ hps =>
    hc ▸ Proofs.Logic.Consequence.FirstOrder.Derivation.rule_valid M r.2 hs (hp ▸ hps)

/-- A checked tree's conclusion holds in every structure satisfying its hypotheses. -/
theorem treeDerives_holds {Γ : List (Sentence Sg)} {φ : Sentence Sg} (h : treeDerives Sg Γ φ)
    (M : Structure Sg) (hΓ : ∀ ψ ∈ Γ, Sentence.Holds M ψ) : Sentence.Holds M φ :=
  DerivationSystem.derives_soundFor locallySound [] ⟨0, Γ, φ⟩ h M (fun _ h => nomatch h)
    Fin.elim0 hΓ

/-- **Soundness for semantic consequence.** -/
theorem treeDerives_le_consequence : treeDerives Sg ≤ consequence Sg :=
  fun _ _ h M hΓ => treeDerives_holds h M hΓ

/-- **Soundness for truth in a structure.** -/
theorem treeDerives_soundFor (M : Structure Sg) : (treeDerives Sg).SoundFor (inStructure M) :=
  fun _ _ h _ hΓ => treeDerives_holds h M hΓ

/-- **The order theory is consistent for checked proof trees**: it does not derive `¬⊤`, since ℕ
satisfies it. -/
theorem orderTheory_tree_consistent : (treeDerives orderSig).ConsistentWrt falsity orderTheory :=
  consistentWrt_of_sound (treeDerives_soundFor natStructure) () natStructure_models
    (by simp [inStructure, Sentence.Holds, Formula.Holds, falsity])

end Silmaril.Consequence.FirstOrder.ND
