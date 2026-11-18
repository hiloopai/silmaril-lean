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
* `mapHom σ`, `treeDerives_map`: proofs translate along a signature morphism `σ` (a morphism of
  derivation systems), so derivability transports along the institution's sentence translation.
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

/-! ## Translation along signature morphisms -/

section Map

variable {Sg' : Signature} [∀ n, DecidableEq (Sg'.Op n)] [∀ n, DecidableEq (Sg'.Rel n)]

theorem Rule.map_side (σ : Sg ⟶ Sg') {k : ℕ} (r : Rule Sg k) (h : r.side = true) :
    (r.map σ).side = true :=
  Proofs.Logic.Consequence.FirstOrder.Derivation.rule_map_side σ r h

omit [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)]
  [∀ n, DecidableEq (Sg'.Op n)] [∀ n, DecidableEq (Sg'.Rel n)] in
theorem Rule.map_prems (σ : Sg ⟶ Sg') {k : ℕ} (r : Rule Sg k) :
    (r.map σ).prems = r.prems.map (Seq.map σ) :=
  Proofs.Logic.Consequence.FirstOrder.Derivation.rule_map_prems σ r

omit [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)]
  [∀ n, DecidableEq (Sg'.Op n)] [∀ n, DecidableEq (Sg'.Rel n)] in
theorem Rule.map_concl (σ : Sg ⟶ Sg') {k : ℕ} (r : Rule Sg k) : (r.map σ).concl = r.concl.map σ :=
  Proofs.Logic.Consequence.FirstOrder.Derivation.rule_map_concl σ r

/-- **Proofs translate along signature morphisms**: a morphism of derivation systems, mapping
judgments by `Formula.map σ` and each rule instance to the mapped instance. -/
def mapHom (σ : Sg ⟶ Sg') : DerivationSystem.Hom (system Sg) (system Sg') where
  f := Seq.map σ
  rule r := ⟨r.1, r.2.map σ⟩
  map_instance := fun r _ _ ⟨hs, hp, hc⟩ =>
    ⟨Rule.map_side σ r.2 hs, by rw [Rule.map_prems, hp], by rw [Rule.map_concl, hc]⟩

/-- **Derivability transports along signature morphisms**: the proof-level counterpart of the
institution's sentence translation (`Formula.map`). -/
theorem treeDerives_map (σ : Sg ⟶ Sg') {Γ : List (Sentence Sg)} {φ : Sentence Sg}
    (h : treeDerives Sg Γ φ) : treeDerives Sg' (Γ.map (Formula.map σ)) (φ.map σ) :=
  (mapHom σ).derives h

end Map

end Silmaril.Consequence.FirstOrder.ND
