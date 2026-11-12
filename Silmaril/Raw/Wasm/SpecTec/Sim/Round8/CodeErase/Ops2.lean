module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.Ops

/-!
# Round 8 (copy of round 7 for `CODE` fields), the export swap: the remaining value operations of the evaluator (round 2, pass 5)

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

`Swap/Ops.lean` covers the projections and updates. This file covers the other value operations
that `Sem.evalExp` applies, so that every value case of the planned evaluator invariant for
`Round8.CodeErase.Swap.Task.stepErase` (item 1 of the plan) is a lemma:

* destructors: `asTuple?_eraseC`, `asList?_eraseC`, `asOpt?_eraseC`, `asCase?_eraseC`;
* `cat?_eraseC` (`e₁ ++ e₂` and `=++`) and `AllIn.cat?`;
* the operators: `unValue_eraseC`, `binValues_eraseC`, `boolShort_eraseC` need no hypothesis
  (they read only booleans and numbers); `cmpValues_eraseC` and `memValue_eraseC` hold on
  `AllIn Q` values with `QInj Q` (`beq_eraseC`, `contains_eraseC`);
* record construction from syntax without an `CODE` atom: `eraseC_struct_of_noCode` and
  `allIn_struct_of_noCode`. A record built by `{A₁ e₁, …}` with no `Aᵢ = CODE` is erased
  fieldwise and is `AllIn Q` when its fields are.

Not here: record composition `Value.comp?` (used only by `Deftype_ok`, on validation contexts),
and the evaluator induction itself.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-! ## Destructors -/

theorem asTuple?_eraseC (v : Value) :
    (eraseC v).asTuple? = v.asTuple?.map (List.map eraseC) := by
  cases v with
  | opt o => cases o <;> rfl
  | tuple vs => simp [Value.asTuple?, eraseCs_eq_map]
  | _ => rfl

theorem asList?_eraseC (v : Value) :
    (eraseC v).asList? = v.asList?.map (List.map eraseC) := by
  cases v with
  | opt o => cases o <;> rfl
  | list vs => simp [Value.asList?, eraseCs_eq_map]
  | _ => rfl

theorem asOpt?_eraseC (v : Value) :
    (eraseC v).asOpt? = v.asOpt?.map (Option.map eraseC) := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asCase?_eraseC (v : Value) :
    (eraseC v).asCase? = v.asCase?.map fun p => (p.1, eraseC p.2) := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

/-! ## Concatenation -/

theorem cat?_eraseC (a b : Value) :
    Value.cat? (eraseC a) (eraseC b) = (Value.cat? a b).map eraseC := by
  rcases a with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;>
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;>
    simp [Value.cat?, eraseCs_eq_map]

/-- The three shapes of a concatenation. -/
theorem cat?_some {a b u : Value} (h : Value.cat? a b = some u) :
    (∃ xs ys, a = .list xs ∧ b = .list ys ∧ u = .list (xs ++ ys)) ∨
      (a = .opt none ∧ u = b) ∨ (b = .opt none ∧ u = a) := by
  rcases a with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;>
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;>
    simp [Value.cat?] at h ⊢ <;> simp [h]

section Keep

variable {Q : Value → Prop}

theorem AllIn.cat? {a b u : Value} (ha : AllIn Q a) (hb : AllIn Q b)
    (h : Value.cat? a b = some u) : AllIn Q u := by
  rcases cat?_some h with ⟨xs, ys, rfl, rfl, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · have hx : ∀ x ∈ xs, AllIn Q x := (allIns_iff Q xs).1 ha
    have hy : ∀ y ∈ ys, AllIn Q y := (allIns_iff Q ys).1 hb
    exact (allIns_iff Q _).2 fun x hm => (List.mem_append.1 hm).elim (hx x) (hy x)
  · exact hb
  · exact ha

end Keep

/-! ## Operators -/

/-- A value that `eraseC` fixes because it is a boolean or a number. -/
theorem eraseC_res_bool_num {r : Res Value}
    (h : ∀ v, r = .ok v → (∃ b, v = .bool b) ∨ ∃ n, v = .num n) :
    eraseC <$> r = r := by
  cases r with
  | error e => rfl
  | ok v =>
    rcases h v rfl with ⟨b, rfl⟩ | ⟨n, rfl⟩ <;> rfl

theorem unValue_eraseC (op : IL.UnOp) (v : Value) : unValue op (eraseC v) = unValue op v := by
  cases v with
  | opt o => cases o <;> cases op <;> rfl
  | _ => cases op <;> rfl

theorem binValues_eraseC (op : IL.BinOp) (a b : Value) :
    binValues op (eraseC a) (eraseC b) = binValues op a b := by
  cases a with
  | bool _ => cases b with
    | opt o => cases o <;> rfl
    | _ => rfl
  | num _ => cases b with
    | opt o => cases o <;> rfl
    | _ => rfl
  | opt o => cases o <;> rfl
  | _ => rfl

theorem boolShort_eraseC (op : IL.BinOp) (v : Value) :
    boolShort op (eraseC v) = boolShort op v := by
  cases v with
  | opt o => cases o <;> cases op <;> rfl
  | _ => cases op <;> rfl

theorem cmpValues_eraseC {Q : Value → Prop} (hQ : QInj Q) {a b : Value} (ha : AllIn Q a)
    (hb : AllIn Q b) (op : IL.CmpOp) :
    cmpValues op (eraseC a) (eraseC b) = cmpValues op a b := by
  cases op with
  | eqOp => simp only [cmpValues, beq_eraseC hQ ha hb]
  | neOp => simp only [cmpValues, beq_eraseC hQ ha hb]
  | _ =>
    cases a with
    | num _ => cases b with
      | opt o => cases o <;> rfl
      | _ => rfl
    | opt o => cases o <;> rfl
    | _ => rfl

theorem memValue_eraseC {Q : Value → Prop} (hQ : QInj Q) {a b : Value} (ha : AllIn Q a)
    (hb : AllIn Q b) : memValue (eraseC a) (eraseC b) = memValue a b := by
  cases b with
  | opt o =>
    cases o with
    | none => rfl
    | some w =>
      have hw : AllIn Q w := hb
      simp only [eraseC_opt_some, memValue, beq_eraseC hQ ha hw]
  | list ws =>
    have hws : ∀ w ∈ ws, AllIn Q w := (allIns_iff Q ws).1 hb
    simp only [eraseC_list', memValue, contains_eraseC hQ ha hws]
  | _ => rfl

/-! ## Records built from syntax -/

/-- No field of `gs` is named `CODE`. -/
def NoCodeF (gs : List (IL.AtomS × Value)) : Prop := ∀ p ∈ gs, p.1 ≠ "CODE"

theorem eraseCf_of_noCode : ∀ {gs : List (IL.AtomS × Value)}, NoCodeF gs →
    eraseCf gs = gs.map fun p => (p.1, eraseC p.2)
  | [], _ => rfl
  | (a, v) :: gs, h => by
    have ha : a ≠ "CODE" := h (a, v) (List.mem_cons_self ..)
    have ht : NoCodeF gs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [eraseCf_cons, ha, ite_false, List.map_cons, eraseCf_of_noCode ht]

/-- **A record without an `CODE` field is erased fieldwise.** -/
theorem eraseC_struct_of_noCode {gs : List (IL.AtomS × Value)} (h : NoCodeF gs) :
    eraseC (.struct gs) = .struct (gs.map fun p => (p.1, eraseC p.2)) := by
  rw [eraseC_struct, eraseCf_of_noCode h]

theorem hasCode_of_noCode : ∀ {gs : List (IL.AtomS × Value)}, NoCodeF gs → hasCode gs = false
  | [], _ => rfl
  | (a, v) :: gs, h => by
    have ha : a ≠ "CODE" := h (a, v) (List.mem_cons_self ..)
    have ht : NoCodeF gs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [hasCode_cons, hasCode_of_noCode ht, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
    exact ha

/-- **A record without an `CODE` field is `AllIn Q`** when its fields are. -/
theorem allIn_struct_of_noCode {Q : Value → Prop} {gs : List (IL.AtomS × Value)} (h : NoCodeF gs)
    (hf : ∀ p ∈ gs, AllIn Q p.2) : AllIn Q (.struct gs) := by
  refine ⟨fun he => absurd he (by rw [hasCode_of_noCode h]; decide), ?_⟩
  clear h
  induction gs with
  | nil => trivial
  | cons p gs ih =>
    obtain ⟨a, v⟩ := p
    exact ⟨hf (a, v) (List.mem_cons_self ..), ih fun q hq => hf q (List.mem_cons_of_mem _ hq)⟩

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
