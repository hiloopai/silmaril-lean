module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms

/-!
# Round 7, REH route 2: comparisons with an export-free operand need no injectivity

`Swap.cmpValues_eraseV` and `Swap.memValue_eraseV` move an equality, inequality or membership
test across `Swap.eraseV` under `QInj Q`, which is where the `StripInj` route needs `StripInj`.
The static check of `Round7.NxSites` asks instead that one operand be export-free (`nxB`). This
file proves that this suffices, with no hypothesis on a swap set:

* `nxB_eraseV`: erasing keeps every field name, so it keeps `nxB`;
* `eraseV_of_nxB`: `eraseV` fixes export-free values;
* `eraseV_eq_iff_of_nxB`: if `a` is export-free, `eraseV a = eraseV b ↔ a = b`;
* `cmpValues_eraseV_nx`, `memValue_eraseV_nx`: the two operators commute with erasure when one
  operand is export-free.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxSites

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

mutual
/-- **Erasing keeps `nxB`**: it changes the contents of `EXPORTS` fields, not field names. -/
theorem nxB_eraseV : ∀ v : Value, nxB (eraseV v) = nxB v
  | .bool _ => rfl
  | .num _ => rfl
  | .text _ => rfl
  | .tuple vs => by rw [eraseV_tuple, nxB_tuple, nxB_tuple, nxBs_eraseVs vs]
  | .case _ w => by rw [eraseV_case, nxB_case, nxB_case, nxB_eraseV w]
  | .struct gs => by rw [eraseV_struct, nxB_struct, nxB_struct, nxBf_eraseVf gs]
  | .list vs => by rw [eraseV_list, nxB_list, nxB_list, nxBs_eraseVs vs]
  | .opt none => rfl
  | .opt (some w) => by rw [eraseV_opt_some, nxB_opt_some, nxB_opt_some, nxB_eraseV w]

/-- `nxB_eraseV` on a list. -/
theorem nxBs_eraseVs : ∀ vs : List Value, nxBs (eraseVs vs) = nxBs vs
  | [] => rfl
  | v :: vs => by simp only [eraseVs, nxBs, nxB_eraseV v, nxBs_eraseVs vs]

/-- `nxB_eraseV` on record fields. -/
theorem nxBf_eraseVf : ∀ gs : List (IL.AtomS × Value), nxBf (eraseVf gs) = nxBf gs
  | [] => rfl
  | (a, v) :: gs => by
    rw [eraseVf_cons, nxBf_cons, nxBf_cons, nxBf_eraseVf gs]
    by_cases h : a = "EXPORTS"
    · subst h
      simp
    · simp only [h, ↓reduceIte, nxB_eraseV v]
end

mutual
/-- **`eraseV` fixes export-free values.** -/
theorem eraseV_of_nxB : ∀ v : Value, nxB v = true → eraseV v = v
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple vs, h => by rw [eraseV_tuple, eraseVs_of_nxBs vs h]
  | .case _ w, h => by rw [eraseV_case, eraseV_of_nxB w h]
  | .struct gs, h => by rw [eraseV_struct, eraseVf_of_nxBf gs h]
  | .list vs, h => by rw [eraseV_list, eraseVs_of_nxBs vs h]
  | .opt none, _ => rfl
  | .opt (some w), h => by rw [eraseV_opt_some, eraseV_of_nxB w h]

/-- `eraseV_of_nxB` on a list. -/
theorem eraseVs_of_nxBs : ∀ vs : List Value, nxBs vs = true → eraseVs vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [nxBs, Bool.and_eq_true] at h
    simp only [eraseVs, eraseV_of_nxB v h.1, eraseVs_of_nxBs vs h.2]

/-- `eraseV_of_nxB` on record fields. -/
theorem eraseVf_of_nxBf : ∀ gs : List (IL.AtomS × Value), nxBf gs = true → eraseVf gs = gs
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [nxBf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [eraseVf_cons, eraseV_of_nxB v h.1.1, eraseVf_of_nxBf gs h.2]
    simp only [h.1.2, ↓reduceIte]
end

/-- **An export-free operand makes erasure reflect equality.** -/
theorem eraseV_eq_iff_of_nxB {a b : Value} (ha : nxB a = true) :
    eraseV a = eraseV b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [eraseV_of_nxB a ha] at h
  have hb : nxB b = true := by rw [← nxB_eraseV b, ← h, ha]
  rw [eraseV_of_nxB b hb] at h
  exact h

/-- `eraseV_eq_iff_of_nxB` with the export-free operand on either side. -/
theorem eraseV_eq_iff_of_nx {a b : Value} (h : nxB a = true ∨ nxB b = true) :
    eraseV a = eraseV b ↔ a = b := by
  rcases h with h | h
  · exact eraseV_eq_iff_of_nxB h
  · rw [eq_comm, eraseV_eq_iff_of_nxB h, eq_comm]

/-- The boolean form of `eraseV_eq_iff_of_nx`. -/
theorem beq_eraseV_nx {a b : Value} (h : nxB a = true ∨ nxB b = true) :
    (eraseV a == eraseV b) = (a == b) := by
  by_cases hab : a = b
  · subst hab
    simp
  · have h' : eraseV a ≠ eraseV b := fun he => hab ((eraseV_eq_iff_of_nx h).1 he)
    simp [hab, h']

/-- **Comparisons with an export-free operand commute with erasure**, with no hypothesis on a
swap set (compare `Swap.cmpValues_eraseV`, which needs `QInj Q`). -/
theorem cmpValues_eraseV_nx {a b : Value} (h : nxB a = true ∨ nxB b = true) (op : IL.CmpOp) :
    cmpValues op (eraseV a) (eraseV b) = cmpValues op a b := by
  cases op with
  | eqOp => simp only [cmpValues, beq_eraseV_nx h]
  | neOp => simp only [cmpValues, beq_eraseV_nx h]
  | _ =>
    cases a with
    | num _ => cases b with
      | opt o => cases o <;> rfl
      | _ => rfl
    | opt o => cases o <;> rfl
    | _ => rfl

/-- Membership in a list commutes with erasure when the element or the list is export-free. -/
theorem contains_eraseV_nx {v : Value} {ws : List Value}
    (h : nxB v = true ∨ ∀ w ∈ ws, nxB w = true) :
    (ws.map eraseV).contains (eraseV v) = ws.contains v := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw : nxB v = true ∨ nxB w = true :=
      h.imp_right fun hw => hw w (List.mem_cons_self ..)
    have ht : nxB v = true ∨ ∀ x ∈ ws, nxB x = true :=
      h.imp_right fun hx x hm => hx x (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons, List.contains_cons]
    rw [ih ht, beq_eraseV_nx hw]

/-- **Membership tests with an export-free operand commute with erasure**, with no hypothesis
on a swap set (compare `Swap.memValue_eraseV`). -/
theorem memValue_eraseV_nx {a b : Value} (h : nxB a = true ∨ nxB b = true) :
    memValue (eraseV a) (eraseV b) = memValue a b := by
  cases b with
  | opt o =>
    cases o with
    | none => rfl
    | some w =>
      have hw : nxB a = true ∨ nxB w = true := by simpa using h
      simp only [eraseV_opt_some, memValue]
      rw [beq_eraseV_nx hw]
  | list ws =>
    have h' : nxB a = true ∨ ∀ w ∈ ws, nxB w = true :=
      h.imp id fun hb w hw => by
        rw [nxB_list, nxBs_eq_all, List.all_eq_true] at hb
        exact hb w hw
    simp only [eraseV_list', memValue, contains_eraseV_nx h']
  | _ => rfl

end Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
