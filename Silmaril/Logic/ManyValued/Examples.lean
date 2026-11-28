module

public import Silmaril.Logic.ManyValued.Thms

/-! # Checked truth tables and order examples -/

namespace Silmaril.Logic.ManyValued.Examples

private def table {α : Type} (values : List α) (op : α → α → α) : List (List α) :=
  values.map fun a => values.map (op a)

section K3

open K3

private def k3Values : List K3 := [tt, unknown, ff]

example : k3Values.map neg = [ff, unknown, tt] := by decide

example : table k3Values conj =
    [[tt, unknown, ff], [unknown, unknown, ff], [ff, ff, ff]] := by decide

example : table k3Values disj =
    [[tt, tt, tt], [tt, unknown, unknown], [tt, unknown, ff]] := by decide

example : table k3Values materialImp =
    [[tt, unknown, ff], [tt, unknown, unknown], [tt, tt, tt]] := by decide

example : table k3Values materialIff =
    [[tt, unknown, ff], [unknown, unknown, unknown], [ff, unknown, tt]] := by decide

-- Excluded middle at the K3 gap is undesignated.
example : (disj unknown (neg unknown)).isDesignated = false := rfl

example : (⟨ff⟩ ⊓ ⟨tt⟩ : K3.Information) = ⊥ := rfl

example : ¬ ∃ c : K3.Information, ⟨ff⟩ ≤ c ∧ ⟨tt⟩ ≤ c :=
  fun ⟨c, hc⟩ => K3.Information.known_no_common_upper_bound c hc

end K3

section FDE

open FDE

private def fdeValues : List FDE := [tt, both, neither, ff]

example : fdeValues.map neg = [ff, both, neither, tt] := by decide

example : table fdeValues conj =
    [[tt, both, neither, ff], [both, both, ff, ff],
     [neither, ff, neither, ff], [ff, ff, ff, ff]] := by decide

example : table fdeValues disj =
    [[tt, tt, tt, tt], [tt, both, tt, both],
     [tt, tt, neither, neither], [tt, both, neither, ff]] := by decide

-- The same two inputs have a different meet and join in the information lattice.
example : ff ⊓ tt = ff ∧ ff ⊔ tt = tt := by decide
example : (⟨ff⟩ ⊓ ⟨tt⟩ : FDE.Information) = ⊥ := rfl
example : (⟨ff⟩ ⊔ ⟨tt⟩ : FDE.Information) = ⊤ := rfl

example : neither.toOptionBool? = some none ∧ both.toOptionBool? = none := by decide

end FDE

-- Priest's LP uses the same three operation tables with a glut in the middle.
-- Its FDE restriction excludes the gap and inherits FDE designation.
private def lpValue : K3 → FDE
  | .ff => .ff
  | .unknown => .both
  | .tt => .tt

example (a : K3) : lpValue a.neg = (lpValue a).neg := by cases a <;> rfl
example (a b : K3) : lpValue (a ⊓ b) = lpValue a ⊓ lpValue b := by
  cases a <;> cases b <;> rfl
example (a b : K3) : lpValue (a ⊔ b) = lpValue a ⊔ lpValue b := by
  cases a <;> cases b <;> rfl
example (a : K3) : (lpValue a).isDesignated = true ↔ a ≠ .ff := by cases a <;> decide

end Silmaril.Logic.ManyValued.Examples
