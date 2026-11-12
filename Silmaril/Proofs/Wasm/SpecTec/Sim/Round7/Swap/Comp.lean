module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Ops2

/-!
# Round 7, the export swap: record composition `Value.comp?` (round 3, pass 1)

The last value operation of `Sem.evalExp` without an `eraseV` lemma (pass 5, `Swap/Ops2.lean`).

* `expLB v`: every record field of `v` named `EXPORTS` holds a list (at any depth). Module-instance
  images satisfy it; it is what makes composition of the two `EXPORTS` fields commute with
  erasing them (`[] ++ [] = []`, whereas `comp?` of a list with a non-list fails).
* `comp?_eraseV`: on `expLB` values, `Value.comp? (eraseV a) (eraseV b) = (Value.comp? a b).map
  eraseV`, and `compFields?_eraseVf` for the pointwise part.
* `expLB_of_nxB`, `nxB_comp?`, `AllIn.comp?_of_nxB`: values without `EXPORTS` records compose to
  such values, so the result is `AllIn Q` for every `Q`. The only reachable composition is in
  `Deftype_ok` (`Round7.Script.stepReach_comp`), on validation contexts, whose type declares no
  `EXPORTS` field.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-- `v` is a list. -/
def isListB : Value → Bool
  | .list _ => true
  | _ => false

mutual
/-- **Every `EXPORTS` field of `v` holds a list**, at any depth. -/
def expLB : Value → Bool
  | .bool _ => true
  | .num _ => true
  | .text _ => true
  | .tuple vs => expLBs vs
  | .case _ w => expLB w
  | .struct gs => expLBf gs
  | .list vs => expLBs vs
  | .opt none => true
  | .opt (some w) => expLB w

/-- `expLB` on a list of values. -/
def expLBs : List Value → Bool
  | [] => true
  | v :: vs => expLB v && expLBs vs

/-- `expLB` on the fields of a record. -/
def expLBf : List (IL.AtomS × Value) → Bool
  | [] => true
  | (a, v) :: gs => expLB v && (a != "EXPORTS" || isListB v) && expLBf gs
end

/-! ## Composition commutes with erasing -/

mutual
theorem comp?_eraseV : ∀ a b : Value, expLB a = true → expLB b = true →
    Value.comp? (eraseV a) (eraseV b) = (Value.comp? a b).map eraseV
  | .struct f₁, b, ha, hb => by
    cases b with
    | struct f₂ =>
      simp only [eraseV_struct, Value.comp?]
      rw [compFields?_eraseVf f₁ f₂ ha hb, Option.map_map, Option.map_map]
      rfl
    | opt o => cases o <;> rfl
    | _ => rfl
  | .list xs, b, _, _ => by
    cases b with
    | list ys => simp [Value.comp?, eraseVs_eq_map]
    | opt o => cases o <;> rfl
    | _ => rfl
  | .opt none, b, _, _ => by
    cases b with
    | opt o => cases o <;> simp [Value.comp?]
    | _ => rfl
  | .opt (some w), b, _, _ => by
    cases b with
    | opt o => cases o <;> simp [Value.comp?]
    | _ => rfl
  | .bool _, b, _, _ => by cases b <;> rfl
  | .num _, b, _, _ => by cases b <;> rfl
  | .text _, b, _, _ => by cases b <;> rfl
  | .tuple _, b, _, _ => by cases b <;> rfl
  | .case _ _, b, _, _ => by cases b <;> rfl

theorem compFields?_eraseVf : ∀ f₁ f₂ : List (IL.AtomS × Value), expLBf f₁ = true →
    expLBf f₂ = true →
    Value.compFields? (eraseVf f₁) (eraseVf f₂) = (Value.compFields? f₁ f₂).map eraseVf
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | (a₁, v₁) :: f₁, (a₂, v₂) :: f₂, ha, hb => by
    simp only [expLBf, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at ha hb
    obtain ⟨⟨ha₁, ha₂⟩, ha₃⟩ := ha
    obtain ⟨⟨hb₁, hb₂⟩, hb₃⟩ := hb
    simp only [eraseVf_cons, Value.compFields?]
    by_cases he : a₁ = a₂
    · subst he
      simp only [ite_true, compFields?_eraseVf f₁ f₂ ha₃ hb₃]
      by_cases hx : a₁ = "EXPORTS"
      · simp only [hx, ite_true, Value.comp?, List.append_nil, not_true_eq_false,
          false_or] at ha₂ hb₂ ⊢
        cases v₁ <;> simp [isListB] at ha₂
        cases v₂ <;> simp [isListB] at hb₂
        cases Value.compFields? f₁ f₂ <;> simp
      · simp only [hx, ite_false, comp?_eraseV v₁ v₂ ha₁ hb₁]
        cases Value.comp? v₁ v₂ <;> cases Value.compFields? f₁ f₂ <;> simp [hx]
    · simp [he]
end

/-! ## Composition without `EXPORTS` records -/

mutual
theorem expLB_of_nxB : ∀ v : Value, nxB v = true → expLB v = true
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple vs, h => expLBs_of_nxBs vs h
  | .case _ w, h => expLB_of_nxB w h
  | .struct gs, h => expLBf_of_nxBf gs h
  | .list vs, h => expLBs_of_nxBs vs h
  | .opt none, _ => rfl
  | .opt (some w), h => expLB_of_nxB w h

theorem expLBs_of_nxBs : ∀ vs : List Value, nxBs vs = true → expLBs vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [nxBs, Bool.and_eq_true] at h
    simp only [expLBs, expLB_of_nxB v h.1, expLBs_of_nxBs vs h.2, Bool.and_self]

theorem expLBf_of_nxBf : ∀ gs : List (IL.AtomS × Value), nxBf gs = true → expLBf gs = true
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [nxBf, Bool.and_eq_true] at h
    simp only [expLBf, expLB_of_nxB v h.1.1, expLBf_of_nxBf gs h.2, h.1.2, Bool.true_or,
      Bool.and_self]
end

mutual
theorem nxB_comp? : ∀ a b u : Value, nxB a = true → nxB b = true → Value.comp? a b = some u →
    nxB u = true
  | .struct f₁, b, u, ha, hb, h => by
    cases b with
    | struct f₂ =>
      simp only [Value.comp?, Option.map_eq_some_iff] at h
      obtain ⟨f, hf, rfl⟩ := h
      exact nxBf_compFields? f₁ f₂ f ha hb hf
    | opt o => cases o <;> simp [Value.comp?] at h
    | _ => simp [Value.comp?] at h
  | .list xs, b, u, ha, hb, h => by
    cases b with
    | list ys =>
      simp only [Value.comp?, Option.some.injEq] at h
      subst h
      simp only [nxB, nxBs_eq_all, List.all_append, Bool.and_eq_true] at ha hb ⊢
      exact ⟨ha, hb⟩
    | opt o => cases o <;> simp [Value.comp?] at h
    | _ => simp [Value.comp?] at h
  | .opt none, b, u, _, hb, h => by
    cases b with
    | opt o =>
      simp only [Value.comp?, Option.some.injEq] at h
      subst h
      exact hb
    | _ => simp [Value.comp?] at h
  | .opt (some w), b, u, ha, _, h => by
    cases b with
    | opt o =>
      cases o with
      | none =>
        simp only [Value.comp?, Option.some.injEq] at h
        subst h
        exact ha
      | some _ => simp [Value.comp?] at h
    | _ => simp [Value.comp?] at h
  | .bool _, b, _, _, _, h => by
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;> simp [Value.comp?] at h
  | .num _, b, _, _, _, h => by
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;> simp [Value.comp?] at h
  | .text _, b, _, _, _, h => by
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;> simp [Value.comp?] at h
  | .tuple _, b, _, _, _, h => by
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;> simp [Value.comp?] at h
  | .case _ _, b, _, _, _, h => by
    rcases b with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;> simp [Value.comp?] at h

theorem nxBf_compFields? : ∀ f₁ f₂ f : List (IL.AtomS × Value), nxBf f₁ = true →
    nxBf f₂ = true → Value.compFields? f₁ f₂ = some f → nxBf f = true
  | [], [], f, _, _, h => by
    simp only [Value.compFields?, Option.some.injEq] at h
    subst h
    rfl
  | [], _ :: _, _, _, _, h => by simp [Value.compFields?] at h
  | _ :: _, [], _, _, _, h => by simp [Value.compFields?] at h
  | (a₁, v₁) :: f₁, (a₂, v₂) :: f₂, f, ha, hb, h => by
    simp only [nxBf, Bool.and_eq_true] at ha hb
    simp only [Value.compFields?] at h
    split_ifs at h with he
    · subst he
      split at h
      · rename_i v g hv hg
        simp only [Option.some.injEq] at h
        subst h
        simp only [nxBf, Bool.and_eq_true]
        exact ⟨⟨nxB_comp? v₁ v₂ v ha.1.1 hb.1.1 hv, ha.1.2⟩,
          nxBf_compFields? f₁ f₂ g ha.2 hb.2 hg⟩
      · simp at h
end

/-- **Composition of values without `EXPORTS` records** is erased pointwise and is `AllIn Q`. -/
theorem AllIn.comp?_of_nxB {Q : Value → Prop} {a b u : Value} (ha : nxB a = true)
    (hb : nxB b = true) (h : Value.comp? a b = some u) :
    AllIn Q u ∧ Value.comp? (eraseV a) (eraseV b) = some (eraseV u) := by
  refine ⟨allIn_of_nxB Q u (nxB_comp? a b u ha hb h), ?_⟩
  rw [comp?_eraseV a b (expLB_of_nxB a ha) (expLB_of_nxB b hb), h]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
