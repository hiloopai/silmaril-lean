module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.Value

/-!
# Round 8 (copy of round 7 for `CODE` fields), the export swap: `eraseC` and the value operations

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

The value layer of an evaluator invariant for `Round7.Task.swapEquiv`. `eraseC` commutes with
every value operation of `Sem.evalExp` that does not name `CODE`, and `AllIn Q` is kept by all
of them except a field update of a record that has an `CODE` field (G9 §3.1: such an update
leaves the swap set, which is why the evaluator layer needs typed update roots).

* `field?_eraseC`, `setField_eraseC` (at an atom other than `CODE`), `idx?_eraseC`,
  `setIdx_eraseC`, `slice?_eraseC`, `setSlice_eraseC`, `len?_eraseC`, `asNat?_eraseC`,
  `asBool?_eraseC`, `asNum?_eraseC`, `asText?_eraseC`;
* `beq_eraseC`: on `AllIn Q` values with `QInj Q`, equality reads alike before and after erasing
  (so `=`, `≠` and membership tests agree);
* `AllIn.field?`, `AllIn.idx?`, `AllIn.setIdx`, `AllIn.slice?`, `AllIn.setSlice`,
  `AllIn.setField` (the last only at a record without an `CODE` field).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-! ## Commuting with the value operations -/

theorem find?_eraseCf {a : IL.AtomS} (ha : a ≠ "CODE") :
    ∀ gs : List (IL.AtomS × Value),
      ((eraseCf gs).find? (·.1 = a)).map Prod.snd = ((gs.find? (·.1 = a)).map Prod.snd).map eraseC
  | [] => rfl
  | (b, v) :: gs => by
    by_cases hb : b = a
    · subst hb
      simp [eraseCf_cons, ha]
    · simp only [eraseCf_cons, List.find?_cons, hb, decide_false]
      exact find?_eraseCf ha gs

theorem field?_eraseC {a : IL.AtomS} (ha : a ≠ "CODE") (v : Value) :
    (eraseC v).field? a = (v.field? a).map eraseC := by
  cases v with
  | struct gs => simp only [eraseC_struct, Value.field?_struct, find?_eraseCf ha]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem map_setField_eraseCf {a : IL.AtomS} (ha : a ≠ "CODE") (w : Value) :
    ∀ gs : List (IL.AtomS × Value),
      (eraseCf gs).map (fun f => if f.1 = a then (f.1, eraseC w) else f) =
        eraseCf (gs.map fun f => if f.1 = a then (f.1, w) else f)
  | [] => rfl
  | (b, v) :: gs => by
    by_cases hb : b = a
    · subst hb
      simp [eraseCf_cons, ha, map_setField_eraseCf ha w gs]
    · simp [eraseCf_cons, hb, map_setField_eraseCf ha w gs]

theorem setField_eraseC {a : IL.AtomS} (ha : a ≠ "CODE") (v w : Value) :
    (eraseC v).setField a (eraseC w) = (v.setField a w).map eraseC := by
  cases v with
  | struct gs => simp only [eraseC_struct, Value.setField_struct, map_setField_eraseCf ha,
      Option.map_some]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem idx?_eraseC (v : Value) (i : Nat) : (eraseC v).idx? i = (v.idx? i).map eraseC := by
  cases v with
  | list vs => simp [Value.idx?, eraseCs_eq_map]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem setIdx_eraseC (v w : Value) (i : Nat) :
    (eraseC v).setIdx i (eraseC w) = (v.setIdx i w).map eraseC := by
  cases v with
  | list vs =>
    simp only [eraseC_list', Value.setIdx, List.length_map]
    split <;> simp [List.map_set, eraseCs_eq_map]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem slice?_eraseC (v : Value) (i n : Nat) :
    (eraseC v).slice? i n = (v.slice? i n).map eraseC := by
  cases v with
  | list vs =>
    simp only [eraseC_list', Value.slice?, List.length_map]
    split <;> simp [List.map_drop, List.map_take, eraseCs_eq_map]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem setSlice_eraseC (v w : Value) (i n : Nat) :
    (eraseC v).setSlice i n (eraseC w) = (v.setSlice i n w).map eraseC := by
  cases v with
  | list vs =>
    cases w with
    | list ws =>
      simp only [eraseC_list', Value.setSlice, List.length_map]
      split <;> simp [List.map_drop, List.map_take, eraseCs_eq_map]
    | opt o => cases o <;> rfl
    | _ => rfl
  | opt o => cases o <;> cases w <;> (try rename_i o'; cases o') <;> rfl
  | _ => cases w <;> (try rename_i o'; cases o') <;> rfl

theorem len?_eraseC (v : Value) : (eraseC v).len? = v.len? := by
  cases v with
  | list vs => simp [Value.len?, eraseCs_eq_map]
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asNat?_eraseC (v : Value) : (eraseC v).asNat? = v.asNat? := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asBool?_eraseC (v : Value) : (eraseC v).asBool? = v.asBool? := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asNum?_eraseC (v : Value) : (eraseC v).asNum? = v.asNum? := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asText?_eraseC (v : Value) : (eraseC v).asText? = v.asText? := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

/-! ## Equality -/

/-- **Equality tests agree** on `AllIn Q` values when `eraseC` is injective on `Q`. -/
theorem beq_eraseC {Q : Value → Prop} (hQ : QInj Q) {v₁ v₂ : Value} (h₁ : AllIn Q v₁)
    (h₂ : AllIn Q v₂) : (eraseC v₁ == eraseC v₂) = (v₁ == v₂) := by
  by_cases h : v₁ = v₂
  · subst h; simp
  · have h' : eraseC v₁ ≠ eraseC v₂ := fun he => h (eraseC_inj hQ h₁ h₂ he)
    simp [h, h']

/-- Membership in a list agrees on `AllIn Q` values. -/
theorem contains_eraseC {Q : Value → Prop} (hQ : QInj Q) {v : Value} {ws : List Value}
    (hv : AllIn Q v) (hw : ∀ w ∈ ws, AllIn Q w) :
    (ws.map eraseC).contains (eraseC v) = ws.contains v := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.contains_cons]
    rw [ih fun x hx => hw x (List.mem_cons_of_mem _ hx),
      beq_eraseC hQ hv (hw w (List.mem_cons_self ..))]

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

theorem hasCode_map_set {a : IL.AtomS} {w : Value} :
    ∀ gs : List (IL.AtomS × Value),
      hasCode (gs.map fun f => if f.1 = a then (f.1, w) else f) = hasCode gs
  | [] => rfl
  | (b, v) :: gs => by
    simp only [List.map_cons]
    by_cases hb : b = a <;> simp [hb, hasCode_map_set gs]

/-- **A field update keeps `AllIn Q` when the updated record has no `CODE` field.** At a
record with one, the result is a new `CODE` record, which need not satisfy `Q`. -/
theorem AllIn.setField {gs : List (IL.AtomS × Value)} {w u : Value} {a : IL.AtomS}
    (hv : AllIn Q (.struct gs)) (hx : hasCode gs = false) (hw : AllIn Q w)
    (h : (Value.struct gs).setField a w = some u) : AllIn Q u := by
  simp only [Value.setField_struct, Option.some.injEq] at h
  subst h
  refine ⟨fun he => ?_, allInf_map_set hw hv.2⟩
  rw [hasCode_map_set, hx] at he
  cases he

end Keep

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
