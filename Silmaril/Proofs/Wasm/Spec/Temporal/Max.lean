module

public import Silmaril.Proofs.Wasm.Spec.Temporal.Basic

@[expose] public section

/-!
# Safety formulas in the readings of LTL: proofs

On good trace sets, `□ A` means the same in finite-trace LTL, in maximal-behaviour LTL and in the
action-invariant logic; over infinite limits it is implied (`ltlInf_of_act`).
-/

namespace Silmaril.Wasm.Spec

variable {Ty A R : Type} {X : Iface Ty}

/-- `□ A` in finite-trace LTL is the action invariant `A`. -/
theorem ltlFin_alw_atom_iff (T : Set (List (Event A R X))) (p : PosPred A R X) :
    (ltlFin Ty A R).Sat T (LTL.alw (LTL.atom p)) ↔ (act Ty A R).Sat T p :=
  forall₂_congr fun _ _ => LTL.holdsFin_alw_atom

/-- An action invariant holds on every infinite limit of a good set. -/
theorem ltlInf_of_act {T : Set (List (Event A R X))} {p : PosPred A R X}
    (h : (act Ty A R).Sat T p) : (ltlInf Ty A R).Sat T (LTL.alw (LTL.atom p)) := by
  intro w hw
  rw [LTL.holdsInf_alw_atom, ← everyPos_prefixList_iff]
  exact fun n => h _ (hw n)

/-- **On good sets, `□ A` over maximal behaviours is the action invariant `A`.** -/
theorem ltlMax_alw_atom_iff {T : Set (List (Event A R X))} (hG : Good T) (p : PosPred A R X) :
    (ltlMax Ty A R).Sat T (LTL.alw (LTL.atom p)) ↔ (act Ty A R).Sat T p := by
  constructor
  · rintro ⟨hinf, hfin⟩ t ht
    show EveryPos p t
    rcases exists_maximal_or_limit hG ht with ⟨u, htu, hu⟩ | ⟨w, hw, hwt⟩
    · have hpu : EveryPos p u := LTL.holdsFin_alw_atom.1 (hfin u hu)
      exact EveryPos.of_prefix hpu htu
    · have hpw : ∀ j, p (prefixList w j) (w j) := LTL.holdsInf_alw_atom.1 (hinf w hw)
      have hall : ∀ n, EveryPos p (prefixList w n) := everyPos_prefixList_iff.2 hpw
      rw [← hwt]
      exact hall t.length
  · intro h
    exact ⟨ltlInf_of_act h, fun t ht => LTL.holdsFin_alw_atom.2 (h t ht.1)⟩

end Silmaril.Wasm.Spec
