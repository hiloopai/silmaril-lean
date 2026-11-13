module

public import Silmaril.Compile.Category.Pass

@[expose] public section

/-!
# Round trips compose

A round trip `L ⇄ M` followed by a round trip `M ⇄ S` is a round trip `L ⇄ S`: lift through
`M`, lower back through `M`. Its composite convention is below the identity by the poset
enrichment (`Convention.comp_mono`):
`(up₁ ≫ up₂) ≫ (down₂ ≫ down₁) = up₁ ≫ (up₂ ≫ down₂) ≫ down₁ ≤ up₁ ≫ down₁ ≤ 𝟙 L`.
So an IR reached through a chain of round trips (Lir ⇄ RTL ⇄ RTL.SSA) conjugates its
optimizations to every language of the chain, with no proof beyond the parts.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

variable {L M S : Language.{u}}

namespace RoundTrip

/-- **Composition of round trips.** -/
def trans (T : RoundTrip L M) (U : RoundTrip M S) : RoundTrip L S where
  lift := T.lift ≫ₚ U.lift
  lower := U.lower ≫ₚ T.lower
  le_id := by
    calc (T.up ≫ U.up) ≫ U.down ≫ T.down = T.up ≫ (U.up ≫ U.down) ≫ T.down := by
          simp only [Category.assoc]
      _ ≤ T.up ≫ 𝟙 M ≫ T.down := Convention.comp_mono le_rfl (Convention.comp_mono U.le_id le_rfl)
      _ = T.up ≫ T.down := by rw [Category.id_comp]
      _ ≤ 𝟙 L := T.le_id

theorem trans_lift_run (T : RoundTrip L M) (U : RoundTrip M S) (p : L.Prog) :
    (T.trans U).lift.run p = (T.lift.run p).bind U.lift.run := rfl

theorem trans_lower_run (T : RoundTrip L M) (U : RoundTrip M S) (q : S.Prog) :
    (T.trans U).lower.run q = (U.lower.run q).bind T.lower.run := rfl

/-- Conjugating through a composite round trip is conjugating through the inner one, then the
outer one: the optimization on `S` seen from `M`, seen from `L`. -/
theorem trans_conj_run (T : RoundTrip L M) (U : RoundTrip M S) (E : EndoPass S) (p : L.Prog) :
    ((T.trans U).conj E).run p =
      (T.lift.run p).bind fun q => (U.conj E).run q |>.bind T.lower.run := by
  simp only [conj_run, trans_lift_run, trans_lower_run]
  cases T.lift.run p <;> simp
  rename_i q
  cases U.lift.run q <;> simp [trans_lower_run]

end RoundTrip

end Silmaril.Compile.Category
