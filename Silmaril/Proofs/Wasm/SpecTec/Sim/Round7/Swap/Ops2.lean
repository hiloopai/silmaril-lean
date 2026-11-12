module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Ops

/-!
# Round 7, the export swap: the remaining value operations of the evaluator (round 2, pass 5)

`Swap/Ops.lean` covers the projections and updates. This file covers the other value operations
that `Sem.evalExp` applies, so that every value case of the planned evaluator invariant for
`Round7.Swap.Task.stepErase` (item 1 of the plan) is a lemma:

* destructors: `asTuple?_eraseV`, `asList?_eraseV`, `asOpt?_eraseV`, `asCase?_eraseV`;
* `cat?_eraseV` (`e₁ ++ e₂` and `=++`) and `AllIn.cat?`;
* the operators: `unValue_eraseV`, `binValues_eraseV`, `boolShort_eraseV` need no hypothesis
  (they read only booleans and numbers); `cmpValues_eraseV` and `memValue_eraseV` hold on
  `AllIn Q` values with `QInj Q` (`beq_eraseV`, `contains_eraseV`);
* record construction from syntax without an `EXPORTS` atom: `eraseV_struct_of_noExp` and
  `allIn_struct_of_noExp`. A record built by `{A₁ e₁, …}` with no `Aᵢ = EXPORTS` is erased
  fieldwise and is `AllIn Q` when its fields are.

Not here: record composition `Value.comp?` (used only by `Deftype_ok`, on validation contexts),
and the evaluator induction itself.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-! ## Destructors -/

theorem asTuple?_eraseV (v : Value) :
    (eraseV v).asTuple? = v.asTuple?.map (List.map eraseV) := by
  cases v with
  | opt o => cases o <;> rfl
  | tuple vs => simp [Value.asTuple?, eraseVs_eq_map]
  | _ => rfl

theorem asList?_eraseV (v : Value) :
    (eraseV v).asList? = v.asList?.map (List.map eraseV) := by
  cases v with
  | opt o => cases o <;> rfl
  | list vs => simp [Value.asList?, eraseVs_eq_map]
  | _ => rfl

theorem asOpt?_eraseV (v : Value) :
    (eraseV v).asOpt? = v.asOpt?.map (Option.map eraseV) := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asCase?_eraseV (v : Value) :
    (eraseV v).asCase? = v.asCase?.map fun p => (p.1, eraseV p.2) := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

/-! ## Concatenation -/

theorem cat?_eraseV (a b : Value) :
    Value.cat? (eraseV a) (eraseV b) = (Value.cat? a b).map eraseV := by
  rcases a with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;>
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;>
    simp [Value.cat?, eraseVs_eq_map]

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

/-- A value that `eraseV` fixes because it is a boolean or a number. -/
theorem eraseV_res_bool_num {r : Res Value}
    (h : ∀ v, r = .ok v → (∃ b, v = .bool b) ∨ ∃ n, v = .num n) :
    eraseV <$> r = r := by
  cases r with
  | error e => rfl
  | ok v =>
    rcases h v rfl with ⟨b, rfl⟩ | ⟨n, rfl⟩ <;> rfl

theorem unValue_eraseV (op : IL.UnOp) (v : Value) : unValue op (eraseV v) = unValue op v := by
  cases v with
  | opt o => cases o <;> cases op <;> rfl
  | _ => cases op <;> rfl

theorem binValues_eraseV (op : IL.BinOp) (a b : Value) :
    binValues op (eraseV a) (eraseV b) = binValues op a b := by
  cases a with
  | bool _ => cases b with
    | opt o => cases o <;> rfl
    | _ => rfl
  | num _ => cases b with
    | opt o => cases o <;> rfl
    | _ => rfl
  | opt o => cases o <;> rfl
  | _ => rfl

theorem boolShort_eraseV (op : IL.BinOp) (v : Value) :
    boolShort op (eraseV v) = boolShort op v := by
  cases v with
  | opt o => cases o <;> cases op <;> rfl
  | _ => cases op <;> rfl

theorem cmpValues_eraseV {Q : Value → Prop} (hQ : QInj Q) {a b : Value} (ha : AllIn Q a)
    (hb : AllIn Q b) (op : IL.CmpOp) :
    cmpValues op (eraseV a) (eraseV b) = cmpValues op a b := by
  cases op with
  | eqOp => simp only [cmpValues, beq_eraseV hQ ha hb]
  | neOp => simp only [cmpValues, beq_eraseV hQ ha hb]
  | _ =>
    cases a with
    | num _ => cases b with
      | opt o => cases o <;> rfl
      | _ => rfl
    | opt o => cases o <;> rfl
    | _ => rfl

theorem memValue_eraseV {Q : Value → Prop} (hQ : QInj Q) {a b : Value} (ha : AllIn Q a)
    (hb : AllIn Q b) : memValue (eraseV a) (eraseV b) = memValue a b := by
  cases b with
  | opt o =>
    cases o with
    | none => rfl
    | some w =>
      have hw : AllIn Q w := hb
      simp only [eraseV_opt_some, memValue, beq_eraseV hQ ha hw]
  | list ws =>
    have hws : ∀ w ∈ ws, AllIn Q w := (allIns_iff Q ws).1 hb
    simp only [eraseV_list', memValue, contains_eraseV hQ ha hws]
  | _ => rfl

/-! ## Records built from syntax -/

/-- No field of `gs` is named `EXPORTS`. -/
def NoExpF (gs : List (IL.AtomS × Value)) : Prop := ∀ p ∈ gs, p.1 ≠ "EXPORTS"

theorem eraseVf_of_noExp : ∀ {gs : List (IL.AtomS × Value)}, NoExpF gs →
    eraseVf gs = gs.map fun p => (p.1, eraseV p.2)
  | [], _ => rfl
  | (a, v) :: gs, h => by
    have ha : a ≠ "EXPORTS" := h (a, v) (List.mem_cons_self ..)
    have ht : NoExpF gs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [eraseVf_cons, ha, ite_false, List.map_cons, eraseVf_of_noExp ht]

/-- **A record without an `EXPORTS` field is erased fieldwise.** -/
theorem eraseV_struct_of_noExp {gs : List (IL.AtomS × Value)} (h : NoExpF gs) :
    eraseV (.struct gs) = .struct (gs.map fun p => (p.1, eraseV p.2)) := by
  rw [eraseV_struct, eraseVf_of_noExp h]

theorem hasExp_of_noExp : ∀ {gs : List (IL.AtomS × Value)}, NoExpF gs → hasExp gs = false
  | [], _ => rfl
  | (a, v) :: gs, h => by
    have ha : a ≠ "EXPORTS" := h (a, v) (List.mem_cons_self ..)
    have ht : NoExpF gs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [hasExp_cons, hasExp_of_noExp ht, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
    exact ha

/-- **A record without an `EXPORTS` field is `AllIn Q`** when its fields are. -/
theorem allIn_struct_of_noExp {Q : Value → Prop} {gs : List (IL.AtomS × Value)} (h : NoExpF gs)
    (hf : ∀ p ∈ gs, AllIn Q p.2) : AllIn Q (.struct gs) := by
  refine ⟨fun he => absurd he (by rw [hasExp_of_noExp h]; decide), ?_⟩
  clear h
  induction gs with
  | nil => trivial
  | cons p gs ih =>
    obtain ⟨a, v⟩ := p
    exact ⟨hf (a, v) (List.mem_cons_self ..), ih fun q hq => hf q (List.mem_cons_of_mem _ hq)⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
