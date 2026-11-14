module

public import Silmaril.Numeric.Libm.Catalogue.Defs
public import Silmaril.Numeric.Libm.Glibc.Thms

/-!
# Combined problems: profile order

`level_implies`: a stronger profile asks a stronger accuracy node of every
function. With `catalogue_monotone` (every catalogue entry is monotone in its
level), `ValidLibmDouble.mono` weakens a whole-libm problem along the profile
order `correctlyRounded → glibcMost → glibcAll → specialOnly` and
`correctlyRounded → faithful → specialOnly`.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm

theorem Accuracy.implies_refl : ∀ a : Accuracy, a.Implies a
  | .none => trivial
  | .ulps k => le_refl k
  | .glibc n => le_refl n
  | .correctlyRounded => trivial
  | .exact => trivial

/-- An entry whose validity is monotone in its accuracy level. -/
def Entry.Monotone (e : Entry) : Prop :=
  ∀ a b impl, a.Implies b → e.valid a impl → e.valid b impl

theorem Spec.entry_monotone {α τ : Type} [LibmFloat τ] (S : Spec α τ) : S.entry.Monotone :=
  fun _ _ _ hab h => Spec.valid_mono hab h

end Silmaril.Numeric.Libm

namespace Silmaril.Numeric.Libm.Double

theorem level_implies {p q : Profile} (h : p.Stronger q) (name : String) :
    (level p name).Implies (level q name) := by
  unfold level
  cases p <;> cases q <;> simp only [Profile.Stronger] at h <;> simp only [reduceCtorEq,
    ite_false, ite_true] <;> (try split_ifs) <;> first
    | trivial
    | exact Accuracy.implies_refl _
    | exact Glibc.mostPlatforms_implies_allPlatforms name
    | (show (1 / 2 : ℚ) ≤ 1; norm_num)

theorem frexpEntry_monotone : frexpEntry.Monotone := fun _ _ _ _ h => h
theorem modfEntry_monotone : modfEntry.Monotone := fun _ _ _ _ h => h

theorem catalogue_monotone : ∀ e ∈ catalogue, e.Monotone := by
  intro e he
  simp only [catalogue, batch1, batch2, batch2Unary, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  repeat' (rcases he with rfl | he)
  all_goals first
    | exact Spec.entry_monotone _
    | exact frexpEntry_monotone
    | exact modfEntry_monotone

/-- A whole-libm problem weakens along the profile order. -/
theorem ValidLibmDouble.mono {p q : Profile} (hpq : p.Stronger q) {impl : LibmImpl}
    (h : ValidLibmDouble p impl) : ValidLibmDouble q impl :=
  ValidLibm.mono (fun e he hv => catalogue_monotone e he _ _ _ (level_implies hpq e.name) hv) h

/-- A whole-libm problem is the conjunction of its per-function problems. -/
theorem validLibmDouble_iff (p : Profile) (impl : LibmImpl) :
    ValidLibmDouble p impl ↔ ∀ e ∈ catalogue, e.valid (level p e.name) (impl e) :=
  Iff.rfl

example : level .glibcMost "sin" = .glibc 1 := by decide
example : level .glibcAll "tgamma" = .glibc 9 := by decide
example : level .faithful "floor" = .exact := by decide
example : level .correctlyRounded "exp" = .correctlyRounded := by decide

end Silmaril.Numeric.Libm.Double
