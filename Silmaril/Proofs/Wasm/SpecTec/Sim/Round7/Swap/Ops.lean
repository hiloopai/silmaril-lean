module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Basic

/-!
# Round 7, the export swap: `eraseV` and the value operations

The value layer of an evaluator invariant for `Round7.Task.swapEquiv`. `eraseV` commutes with
every value operation of `Sem.evalExp` that does not name `EXPORTS`, and `AllIn Q` is kept by all
of them except a field update of a record that has an `EXPORTS` field (G9 §3.1: such an update
leaves the swap set, which is why the evaluator layer needs typed update roots).

* `field?_eraseV`, `setField_eraseV` (at an atom other than `EXPORTS`), `idx?_eraseV`,
  `setIdx_eraseV`, `slice?_eraseV`, `setSlice_eraseV`, `len?_eraseV`, `asNat?_eraseV`,
  `asBool?_eraseV`, `asNum?_eraseV`, `asText?_eraseV`;
* `beq_eraseV`: on `AllIn Q` values with `QInj Q`, equality reads alike before and after erasing
  (so `=`, `≠` and membership tests agree);
* `AllIn.field?`, `AllIn.idx?`, `AllIn.setIdx`, `AllIn.slice?`, `AllIn.setSlice`,
  `AllIn.setField` (the last only at a record without an `EXPORTS` field).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-! ## Commuting with the value operations -/

theorem find?_eraseVf {a : IL.AtomS} (ha : a ≠ "EXPORTS") :
    ∀ gs : List (IL.AtomS × Value),
      ((eraseVf gs).find? (·.1 = a)).map Prod.snd = ((gs.find? (·.1 = a)).map Prod.snd).map eraseV
  | [] => rfl
  | (b, v) :: gs => by
    by_cases hb : b = a
    · subst hb
      simp [eraseVf_cons, ha]
    · simp only [eraseVf_cons, List.find?_cons, hb, decide_false]
      exact find?_eraseVf ha gs

theorem field?_eraseV {a : IL.AtomS} (ha : a ≠ "EXPORTS") (v : Value) :
    (eraseV v).field? a = (v.field? a).map eraseV := by
  cases v with
  | struct gs => simp only [eraseV_struct, Value.field?_struct, find?_eraseVf ha]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem map_setField_eraseVf {a : IL.AtomS} (ha : a ≠ "EXPORTS") (w : Value) :
    ∀ gs : List (IL.AtomS × Value),
      (eraseVf gs).map (fun f => if f.1 = a then (f.1, eraseV w) else f) =
        eraseVf (gs.map fun f => if f.1 = a then (f.1, w) else f)
  | [] => rfl
  | (b, v) :: gs => by
    by_cases hb : b = a
    · subst hb
      simp [eraseVf_cons, ha, map_setField_eraseVf ha w gs]
    · simp [eraseVf_cons, hb, map_setField_eraseVf ha w gs]

theorem setField_eraseV {a : IL.AtomS} (ha : a ≠ "EXPORTS") (v w : Value) :
    (eraseV v).setField a (eraseV w) = (v.setField a w).map eraseV := by
  cases v with
  | struct gs => simp only [eraseV_struct, Value.setField_struct, map_setField_eraseVf ha,
      Option.map_some]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem idx?_eraseV (v : Value) (i : Nat) : (eraseV v).idx? i = (v.idx? i).map eraseV := by
  cases v with
  | list vs => simp [Value.idx?, eraseVs_eq_map]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem setIdx_eraseV (v w : Value) (i : Nat) :
    (eraseV v).setIdx i (eraseV w) = (v.setIdx i w).map eraseV := by
  cases v with
  | list vs =>
    simp only [eraseV_list', Value.setIdx, List.length_map]
    split <;> simp [List.map_set, eraseVs_eq_map]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem slice?_eraseV (v : Value) (i n : Nat) :
    (eraseV v).slice? i n = (v.slice? i n).map eraseV := by
  cases v with
  | list vs =>
    simp only [eraseV_list', Value.slice?, List.length_map]
    split <;> simp [List.map_drop, List.map_take, eraseVs_eq_map]
  | opt o => cases o <;> rfl
  | _ => rfl

set_option linter.unusedTactic false in
theorem setSlice_eraseV (v w : Value) (i n : Nat) :
    (eraseV v).setSlice i n (eraseV w) = (v.setSlice i n w).map eraseV := by
  cases v with
  | list vs =>
    cases w with
    | list ws =>
      simp only [eraseV_list', Value.setSlice, List.length_map]
      split <;> simp [List.map_drop, List.map_take, eraseVs_eq_map]
    | opt o => cases o <;> rfl
    | _ => rfl
  | opt o => cases o <;> cases w <;> (try rename_i o'; cases o') <;> rfl
  | _ => cases w <;> (try rename_i o'; cases o') <;> rfl

theorem len?_eraseV (v : Value) : (eraseV v).len? = v.len? := by
  cases v with
  | list vs => simp [Value.len?, eraseVs_eq_map]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asNat?_eraseV (v : Value) : (eraseV v).asNat? = v.asNat? := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asBool?_eraseV (v : Value) : (eraseV v).asBool? = v.asBool? := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asNum?_eraseV (v : Value) : (eraseV v).asNum? = v.asNum? := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asText?_eraseV (v : Value) : (eraseV v).asText? = v.asText? := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

/-! ## Equality -/

/-- **Equality tests agree** on `AllIn Q` values when `eraseV` is injective on `Q`. -/
theorem beq_eraseV {Q : Value → Prop} (hQ : QInj Q) {v₁ v₂ : Value} (h₁ : AllIn Q v₁)
    (h₂ : AllIn Q v₂) : (eraseV v₁ == eraseV v₂) = (v₁ == v₂) := by
  by_cases h : v₁ = v₂
  · subst h; simp
  · have h' : eraseV v₁ ≠ eraseV v₂ := fun he => h (eraseV_inj hQ h₁ h₂ he)
    simp [h, h']

/-- Membership in a list agrees on `AllIn Q` values. -/
theorem contains_eraseV {Q : Value → Prop} (hQ : QInj Q) {v : Value} {ws : List Value}
    (hv : AllIn Q v) (hw : ∀ w ∈ ws, AllIn Q w) :
    (ws.map eraseV).contains (eraseV v) = ws.contains v := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.contains_cons]
    rw [ih fun x hx => hw x (List.mem_cons_of_mem _ hx),
      beq_eraseV hQ hv (hw w (List.mem_cons_self ..))]

/-! ## Keeping `AllIn` -/

section Keep

variable {Q : Value → Prop}

theorem allInf_find? {a : IL.AtomS} : ∀ {gs : List (IL.AtomS × Value)}, AllInf Q gs →
    ∀ {u : Value}, (gs.find? (·.1 = a)).map Prod.snd = some u → AllIn Q u
  | [], _, _, h => by simp at h
  | (b, v) :: gs, h, u, hu => by
    by_cases hb : b = a
    · simp only [List.find?_cons, hb, decide_true, Option.map_some, Option.some.injEq] at hu
      exact hu ▸ h.1
    · simp only [List.find?_cons, hb, decide_false] at hu
      exact allInf_find? h.2 hu

theorem AllIn.field? {v u : Value} {a : IL.AtomS} (hv : AllIn Q v) (h : v.field? a = some u) :
    AllIn Q u := by
  cases v with
  | struct gs => exact allInf_find? hv.2 h
  | opt o => cases o <;> simp [Value.field?] at h
  | _ => simp [Value.field?] at h

theorem AllIn.idx? {v u : Value} {i : Nat} (hv : AllIn Q v) (h : v.idx? i = some u) :
    AllIn Q u := by
  cases v with
  | list vs =>
    simp only [Value.idx?] at h
    exact (allIns_iff Q vs).1 hv u (List.mem_of_getElem? h)
  | opt o => cases o <;> simp [Value.idx?] at h
  | _ => simp [Value.idx?] at h

theorem AllIn.setIdx {v w u : Value} {i : Nat} (hv : AllIn Q v) (hw : AllIn Q w)
    (h : v.setIdx i w = some u) : AllIn Q u := by
  cases v with
  | list vs =>
    simp only [Value.setIdx] at h
    split at h
    · cases h
      refine (allIns_iff Q _).2 fun x hx => ?_
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact (allIns_iff Q vs).1 hv x hx
      · exact hw
    · cases h
  | opt o => cases o <;> simp [Value.setIdx] at h
  | _ => simp [Value.setIdx] at h

theorem AllIn.slice? {v u : Value} {i n : Nat} (hv : AllIn Q v) (h : v.slice? i n = some u) :
    AllIn Q u := by
  cases v with
  | list vs =>
    simp only [Value.slice?] at h
    split at h
    · cases h
      exact (allIns_iff Q _).2 fun x hx =>
        (allIns_iff Q vs).1 hv x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    · cases h
  | opt o => cases o <;> simp [Value.slice?] at h
  | _ => simp [Value.slice?] at h

set_option linter.unusedTactic false in
theorem AllIn.setSlice {v w u : Value} {i n : Nat} (hv : AllIn Q v) (hw : AllIn Q w)
    (h : v.setSlice i n w = some u) : AllIn Q u := by
  cases v with
  | list vs =>
    cases w with
    | list ws =>
      simp only [Value.setSlice] at h
      split at h
      · cases h
        refine (allIns_iff Q _).2 fun x hx => ?_
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact (allIns_iff Q vs).1 hv x (List.mem_of_mem_take hx)
        · exact (allIns_iff Q ws).1 hw x hx
        · exact (allIns_iff Q vs).1 hv x (List.mem_of_mem_drop hx)
      · cases h
    | opt o => cases o <;> simp [Value.setSlice] at h
    | _ => simp [Value.setSlice] at h
  | opt o => cases o <;> cases w <;> (try rename_i o'; cases o') <;> simp [Value.setSlice] at h
  | _ => cases w <;> (try rename_i o'; cases o') <;> simp [Value.setSlice] at h

theorem allInf_map_set {a : IL.AtomS} {w : Value} (hw : AllIn Q w) :
    ∀ {gs : List (IL.AtomS × Value)}, AllInf Q gs →
      AllInf Q (gs.map fun f => if f.1 = a then (f.1, w) else f)
  | [], _ => trivial
  | (b, v) :: gs, h => by
    simp only [List.map_cons]
    by_cases hb : b = a
    · simp only [hb, ite_true]
      exact ⟨hw, allInf_map_set hw h.2⟩
    · simp only [hb, ite_false]
      exact ⟨h.1, allInf_map_set hw h.2⟩

theorem hasExp_map_set {a : IL.AtomS} {w : Value} :
    ∀ gs : List (IL.AtomS × Value),
      hasExp (gs.map fun f => if f.1 = a then (f.1, w) else f) = hasExp gs
  | [] => rfl
  | (b, v) :: gs => by
    simp only [List.map_cons]
    by_cases hb : b = a <;> simp [hb, hasExp_map_set gs]

/-- **A field update keeps `AllIn Q` when the updated record has no `EXPORTS` field.** At a
record with one, the result is a new `EXPORTS` record, which need not satisfy `Q`. -/
theorem AllIn.setField {gs : List (IL.AtomS × Value)} {w u : Value} {a : IL.AtomS}
    (hv : AllIn Q (.struct gs)) (hx : hasExp gs = false) (hw : AllIn Q w)
    (h : (Value.struct gs).setField a w = some u) : AllIn Q u := by
  simp only [Value.setField_struct, Option.some.injEq] at h
  subst h
  refine ⟨fun he => ?_, allInf_map_set hw hv.2⟩
  rw [hasExp_map_set, hx] at he
  cases he

end Keep

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
