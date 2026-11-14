module

public import Silmaril.Process.Mt.Csl.Ro.Defs
import Silmaril.Proofs.Process.Mt.Csl.Adequacy

/-! # Read-only sharing keeps the decomposition sound: proofs

From a start agreeing with the read-only heap `RO` and decomposed for `roT U RO`, every run of `U`
is a run of `roT U RO` (`ro_reach`): by induction along the run, each configuration is
`roT U RO`-reachable, so `Csl.adequacy` makes it fault free for `roT U RO`, so the next step of
`U` keeps `RO` (a step that changes it is a fault of `roT U RO`) and is a step of `roT U RO`.
Promoted from erebor-lean's `Erebor.Proofs.Mt` (`Erebor/Proofs/Mt/Ro.lean`).
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Csl

open Silmaril.Process.Mt.Csl

variable {M A V : Type} {S : Store M A V} {U : TIsa S} {RO : Heap A V} {I : HProp A V}
  {Q : Nat → U.St → Heap A V → Prop}

theorem ro_star_snoc {α : Type} {r : α → α → Prop} {a b c : α} (h : Star r a b) (h' : r b c) :
    Star r a c := by
  induction h with
  | refl => exact .step h' .refl
  | step h1 _ ih => exact .step h1 (ih h')

/-- The runs of `roT U RO` keep agreeing with `RO`. -/
theorem ro_agrees {C C' : Cfg (roT U RO)} (r : Reach (roT U RO) C C') :
    S.Agrees RO C.mem → S.Agrees RO C'.mem := by
  induction r with
  | refl => exact id
  | step st _ ih =>
    intro h0
    apply ih
    cases st with
    | loc _ h => exact h.2.2
    | atom _ h => exact h.2.2
    | spawn _ _ h => exact h.2.2

/-- **Every run of `U` is a run of `roT U RO`** from a start agreeing with `RO` and decomposed for
`roT U RO`. -/
theorem ro_reach {C₀ C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (h0 : S.Agrees RO C₀.mem) (g : GInv (roT U RO) I Q (cfgRo RO C₀) hs hI)
    (r : Reach U C₀ C) : Reach (roT U RO) (cfgRo RO C₀) (cfgRo RO C) := by
  suffices key : ∀ B, Reach (roT U RO) (cfgRo RO C₀) (cfgRo RO B) → Reach U B C →
      Reach (roT U RO) (cfgRo RO C₀) (cfgRo RO C) from key C₀ .refl r
  clear r
  intro B hB rB
  induction rB with
  | refl => exact hB
  | @step B B' C st _ ih =>
    refine ih ?_
    have agB : S.Agrees RO B.mem := ro_agrees hB h0
    have nf : ¬ Fault (roT U RO) (cfgRo RO B) := (adequacy g hB).1
    refine ro_star_snoc hB ?_
    cases st with
    | @loc t s s' m' hs h =>
      by_cases hm : S.Agrees RO m'
      · exact Step.loc (U := roT U RO) hs ⟨agB, h, hm⟩
      · exact absurd ⟨t, s, hs, Or.inl ⟨agB, Or.inr (Or.inl ⟨s', m', h, hm⟩)⟩⟩ nf
    | @atom t s s' m' hs h =>
      by_cases hm : S.Agrees RO m'
      · exact Step.atom (U := roT U RO) hs ⟨agB, h, hm⟩
      · exact absurd ⟨t, s, hs, Or.inr ⟨agB, Or.inr ⟨s', m', h, hm⟩⟩⟩ nf
    | @spawn t u s s₁ s₂ m' hs hu h =>
      by_cases hm : S.Agrees RO m'
      · exact Step.spawn (U := roT U RO) hs hu ⟨agB, h, hm⟩
      · exact absurd ⟨t, s, hs, Or.inl ⟨agB, Or.inr (Or.inr ⟨u, s₁, s₂, m', h, hm⟩)⟩⟩ nf

/-- **Adequacy with read-only sharing.** -/
theorem ro_adequacy {C₀ C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (h0 : S.Agrees RO C₀.mem) (g : GInv (roT U RO) I Q (cfgRo RO C₀) hs hI)
    (r : Reach U C₀ C) :
    Good (roT U RO) I Q (cfgRo RO C) ∧ ¬ Fault U C ∧ S.Agrees RO C.mem := by
  have rr := ro_reach h0 g r
  have gd := adequacy g rr
  have ag : S.Agrees RO C.mem := ro_agrees rr h0
  refine ⟨gd, ?_, ag⟩
  rintro ⟨t, s, hs, hf | hf⟩
  · exact gd.1 ⟨t, s, hs, Or.inl ⟨ag, Or.inl hf⟩⟩
  · exact gd.1 ⟨t, s, hs, Or.inr ⟨ag, Or.inl hf⟩⟩

end Silmaril.Proofs.Process.Mt.Csl
