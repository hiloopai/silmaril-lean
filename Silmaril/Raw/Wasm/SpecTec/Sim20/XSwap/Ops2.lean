module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.Ops

/-!
# Round 8 (copy  for `EXPORTS` fields), the export swap: the remaining value operations of the evaluator

Round 9 copy 's `Round8.CodeErase` (itself a copy 's export erasure) for
`EXPORTS` fields with an arbitrary injective replacement `XTau.τ` (`swapX`); the prose below,
written for the earlier copies, speaks of erasure. Every value is in the swap set (`fun _ => True`).

`Swap/Ops.lean` covers the projections and updates. This file covers the other value operations
that `Sem.evalExp` applies, so that every value case of the planned evaluator invariant for
`XSwap.Swap.Task.stepErase` (item 1 of the plan) is a lemma:

* destructors: `asTuple?_eraseC`, `asList?_eraseC`, `asOpt?_eraseC`, `asCase?_eraseC`;
* `cat?_eraseC` (`e₁ ++ e₂` and `=++`) and `AllIn.cat?`;
* the operators: `unValue_eraseC`, `binValues_eraseC`, `boolShort_eraseC` need no hypothesis
  (they read only booleans and numbers); `cmpValues_eraseC` and `memValue_eraseC` hold on
  `AllIn Q` values with `QInj Q` (`beq_eraseC`, `contains_eraseC`);
* record construction from syntax without an `EXPORTS` atom: `swapX_struct_of_noCode` and
  `allIn_struct_of_noCode`. A record built by `{A₁ e₁, …}` with no `Aᵢ = CODE` is erased
  fieldwise and is `AllIn Q` when its fields are.

Not here: record composition `Value.comp?` (used only by `Deftype_ok`, on validation contexts),
and the evaluator induction itself.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-! ## Destructors -/

theorem asTuple?_eraseC (v : Value) :
    (swapX v).asTuple? = v.asTuple?.map (List.map swapX) := by
  cases v with
  | opt o => cases o <;> rfl
  | tuple vs => simp [Value.asTuple?, swapXs_eq_map]
  | _ => rfl

theorem asList?_eraseC (v : Value) :
    (swapX v).asList? = v.asList?.map (List.map swapX) := by
  cases v with
  | opt o => cases o <;> rfl
  | list vs => simp [Value.asList?, swapXs_eq_map]
  | _ => rfl

theorem asOpt?_eraseC (v : Value) :
    (swapX v).asOpt? = v.asOpt?.map (Option.map swapX) := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem asCase?_eraseC (v : Value) :
    (swapX v).asCase? = v.asCase?.map fun p => (p.1, swapX p.2) := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

/-! ## Concatenation -/

theorem cat?_eraseC (a b : Value) :
    Value.cat? (swapX a) (swapX b) = (Value.cat? a b).map swapX := by
  rcases a with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;>
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;>
    simp [Value.cat?, swapXs_eq_map]

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

/-- A value that `swapX` fixes because it is a boolean or a number. -/
theorem swapX_res_bool_num {r : Res Value}
    (h : ∀ v, r = .ok v → (∃ b, v = .bool b) ∨ ∃ n, v = .num n) :
    swapX <$> r = r := by
  cases r with
  | error e => rfl
  | ok v =>
    rcases h v rfl with ⟨b, rfl⟩ | ⟨n, rfl⟩ <;> rfl

theorem unValue_eraseC (op : IL.UnOp) (v : Value) : unValue op (swapX v) = unValue op v := by
  cases v with
  | opt o => cases o <;> cases op <;> rfl
  | _ => cases op <;> rfl

theorem binValues_eraseC (op : IL.BinOp) (a b : Value) :
    binValues op (swapX a) (swapX b) = binValues op a b := by
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
    boolShort op (swapX v) = boolShort op v := by
  cases v with
  | opt o => cases o <;> cases op <;> rfl
  | _ => cases op <;> rfl

theorem cmpValues_eraseC {Q : Value → Prop} (hQ : QInj Q) {a b : Value} (ha : AllIn Q a)
    (hb : AllIn Q b) (op : IL.CmpOp) :
    cmpValues op (swapX a) (swapX b) = cmpValues op a b := by
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
    (hb : AllIn Q b) : memValue (swapX a) (swapX b) = memValue a b := by
  cases b with
  | opt o =>
    cases o with
    | none => rfl
    | some w =>
      have hw : AllIn Q w := hb
      simp only [swapX_opt_some, memValue, beq_eraseC hQ ha hw]
  | list ws =>
    have hws : ∀ w ∈ ws, AllIn Q w := (allIns_iff Q ws).1 hb
    simp only [swapX_list', memValue, contains_eraseC hQ ha hws]
  | _ => rfl

/-! ## Records built from syntax -/

/-- No field of `gs` is named `EXPORTS`. -/
def NoExpF (gs : List (IL.AtomS × Value)) : Prop := ∀ p ∈ gs, p.1 ≠ "EXPORTS"

theorem swapXf_of_noCode : ∀ {gs : List (IL.AtomS × Value)}, NoExpF gs →
    swapXf gs = gs.map fun p => (p.1, swapX p.2)
  | [], _ => rfl
  | (a, v) :: gs, h => by
    have ha : a ≠ "EXPORTS" := h (a, v) (List.mem_cons_self ..)
    have ht : NoExpF gs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [swapXf_cons, ha, ite_false, List.map_cons, swapXf_of_noCode ht]

/-- **A record without an `EXPORTS` field is erased fieldwise.** -/
theorem swapX_struct_of_noCode {gs : List (IL.AtomS × Value)} (h : NoExpF gs) :
    swapX (.struct gs) = .struct (gs.map fun p => (p.1, swapX p.2)) := by
  rw [swapX_struct, swapXf_of_noCode h]

theorem hasExpX_of_noCode : ∀ {gs : List (IL.AtomS × Value)}, NoExpF gs → hasExpX gs = false
  | [], _ => rfl
  | (a, v) :: gs, h => by
    have ha : a ≠ "EXPORTS" := h (a, v) (List.mem_cons_self ..)
    have ht : NoExpF gs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [hasExpX_cons, hasExpX_of_noCode ht, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
    exact ha

/-- **A record without an `EXPORTS` field is `AllIn Q`** when its fields are. -/
theorem allIn_struct_of_noCode {Q : Value → Prop} {gs : List (IL.AtomS × Value)} (h : NoExpF gs)
    (hf : ∀ p ∈ gs, AllIn Q p.2) : AllIn Q (.struct gs) := by
  refine ⟨fun he => absurd he (by rw [hasExpX_of_noCode h]; decide), ?_⟩
  clear h
  induction gs with
  | nil => trivial
  | cons p gs ih =>
    obtain ⟨a, v⟩ := p
    exact ⟨hf (a, v) (List.mem_cons_self ..), ih fun q hq => hf q (List.mem_cons_of_mem _ hq)⟩

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
