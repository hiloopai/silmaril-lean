module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VBytes.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk1
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk3

/-!
# Round 7, memory SIMD: which bodies `simEnv B` finds are `GoodEvs`

The kernel facts of `Chunk0`–`Chunk3`, `Rules` and `Round7.VBytes`, read in `simEnv B` for every
`B`:

* `stepRelOnly_fixed`: among the items reachable from `Step`, only `Step` and `Step_read` refer
  to the relations `Step` or `Step_read`;
* `goodClauses`, `goodRules`: the clauses of a `GoodName` definition and the rules of a `GoodRel`
  relation are `GoodEvs`;
* `goodRule_pure`, `goodRule_read`, `goodRule_step`: every rule of `Step_pure`, every rule of
  `Step_read` other than 43, and every rule of `Step` other than 1–5 and 23 is `GoodEvs`
  (`GoodRule`). Rules 1–5 of `Step` refer to `Step_read` or `Step`, and rules 43 and 23 call
  `$vbytes_`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (Ev Item items evRefs evRule stepReach defsItems defsItems_append
  fixed_length_le stepReach_closed mem_evRefs defDefEv relDefEv findDef?_simEnv_item
  findRel?_simEnv_item findRel?_reach)

/-! ## The whole script -/

theorem stepRelOnly_append (a b : IL.Script) :
    stepRelOnly (a ++ b) = (stepRelOnly a && stepRelOnly b) := by
  simp [stepRelOnly, items, defsItems_append, List.all_append]

/-- `stepRelOnly` from chunks of `k` definitions. -/
theorem stepRelOnly_chunks (k : Nat) :
    ∀ (n : Nat) (s : IL.Script), s.length ≤ k * n →
      (∀ i < n, stepRelOnly ((s.drop (k * i)).take k) = true) → stepRelOnly s = true
  | 0, s, h, _ => by
    have hs : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (by simpa using h))
    rw [hs]
    rfl
  | n + 1, s, h, hc => by
    have h₀ : stepRelOnly (s.take k) = true := by simpa using hc 0 (Nat.succ_pos n)
    have hlen : (s.drop k).length ≤ k * n := by
      simp only [List.length_drop]
      rw [Nat.mul_succ] at h
      omega
    have hc' : ∀ i < n, stepRelOnly (((s.drop k).drop (k * i)).take k) = true := by
      intro i hi
      have hi' := hc (i + 1) (Nat.succ_lt_succ hi)
      rwa [Nat.mul_succ, Nat.add_comm, ← List.drop_drop] at hi'
    have h₁ : stepRelOnly (s.drop k) = true := stepRelOnly_chunks k n (s.drop k) hlen hc'
    rw [← List.take_append_drop k s, stepRelOnly_append, h₀, h₁]
    rfl

/-- **Among the reachable items, only `Step` and `Step_read` refer to `Step` or `Step_read`.** -/
theorem stepRelOnly_fixed : stepRelOnly Scripts.Wasm30.fixed = true := by
  refine stepRelOnly_chunks 250 4 _ (by simpa using fixed_length_le) fun i hi => ?_
  match i, hi with
  | 0, _ => simpa using stepRelOnly_chunk0
  | 1, _ => exact stepRelOnly_chunk1
  | 2, _ => exact stepRelOnly_chunk2
  | 3, _ => exact stepRelOnly_chunk3

/-- A reachable item other than `Step` and `Step_read` refers to neither. -/
theorem item_noStepRel {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) (hx : ¬ (it.1 = 0 ∧ (it.2.1 = "Step_read" ∨ it.2.1 = "Step")))
    {y : String} (hy : y = "Step" ∨ y = "Step_read") : (0, y) ∉ evRefs it.2.2 := by
  have hok : stepRelItemOk it = true := List.all_eq_true.mp stepRelOnly_fixed it h
  intro hmem
  have hany : (evRefs it.2.2).any stepRelRef = true :=
    List.any_eq_true.2 ⟨_, hmem, by rcases hy with rfl | rfl <;> decide⟩
  have hname : stepRelRef (it.1, it.2.1) = false := by
    obtain ⟨k, x, l⟩ := it
    simp only [stepRelRef, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq]
    exact ⟨fun h' => hx ⟨h'.1, Or.inr h'.2⟩, fun h' => hx ⟨h'.1, Or.inl h'.2⟩⟩
  simp [stepRelItemOk, hany, hname] at hok
  exact hok hR

/-- **A sublist of a reachable body with no reference to `$vbytes_`, `Step` or `Step_read` is
`GoodEvs`.** -/
theorem goodEvs_of {l L : List Ev} (hsub : ∀ e ∈ l, e ∈ L) (hR : ∀ r ∈ evRefs L, r ∈ stepReach)
    (hv : (1, "vbytes_") ∉ evRefs l) (hs : (0, "Step") ∉ evRefs l)
    (hr : (0, "Step_read") ∉ evRefs l) : GoodEvs l := by
  intro e he
  cases e with
  | ref k x =>
    have hL := hR _ (mem_evRefs (hsub _ he))
    have hl := mem_evRefs he
    rcases k with _ | _ | k
    · refine ⟨hL, fun hx => ?_, fun hx => ?_⟩
      · subst hx; exact hs hl
      · subst hx; exact hr hl
    · exact ⟨hL, fun hx => by subst hx; exact hv hl⟩
    · trivial
  | atom a => trivial
  | comp => trivial
  | upd r ats => trivial

/-- An item reachable from `Step`, other than `Step` and `Step_read`, is `GoodEvs`. -/
theorem goodEvs_of_item {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) (hx : ¬ (it.1 = 0 ∧ (it.2.1 = "Step_read" ∨ it.2.1 = "Step"))) :
    GoodEvs it.2.2 :=
  goodEvs_of (fun _ he => he) (stepReach_closed h hR) (VBytes.item_noVBytes h hx)
    (item_noStepRel h hR hx (Or.inl rfl)) (item_noStepRel h hR hx (Or.inr rfl))

@[simp] theorem goodEvs_append {l₁ l₂ : List Ev} : GoodEvs (l₁ ++ l₂) ↔ GoodEvs l₁ ∧ GoodEvs l₂ := by
  simp only [GoodEvs, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

@[simp] theorem goodEvs_flatMap {α : Type} {f : α → List Ev} {l : List α} :
    GoodEvs (l.flatMap f) ↔ ∀ x ∈ l, GoodEvs (f x) := by
  simp only [GoodEvs, List.mem_flatMap]
  exact ⟨fun h x hx e he => h e ⟨x, hx, he⟩, fun h e ⟨x, hx, he⟩ => h x hx e he⟩

/-- **The clauses `simEnv B` finds for a `GoodName` are `GoodEvs`.** -/
theorem goodClauses (B : Builtins) {x : IL.Id} (hx : GoodName x) {d : DefDef}
    (hd : (simEnv B).findDef? x = some d) : ∀ c ∈ d.2.2, GoodEvs (Round7.Script.evClause c) := by
  have := goodEvs_of_item (findDef?_simEnv_item hd) hx.1 (by simp)
  simp only [defDefEv, goodEvs_append, goodEvs_flatMap] at this
  exact this.2

/-- **The rules `simEnv B` finds for a `GoodRel` are `GoodEvs`.** -/
theorem goodRules (B : Builtins) {x : IL.Id} (hx : GoodRel x) {d : RelDef}
    (hd : (simEnv B).findRel? x = some d) : ∀ r ∈ d.2.2.2, GoodEvs (evRule r) := by
  have := goodEvs_of_item (findRel?_simEnv_item hd) hx.1
    (by simp only [not_and, not_or]; exact fun _ => ⟨hx.2.2, hx.2.1⟩)
  simp only [relDefEv, goodEvs_append, goodEvs_flatMap] at this
  exact this.2

/-! ## Single rules of `Step_pure`, `Step_read` and `Step` -/

/-- A rule outside `ruleUsersK k y rules` does not refer to `(k, y)`. -/
theorem not_mem_ruleUsersK {k : Nat} {y : String} {rules : List Rule} {i : Nat} {r : Rule}
    (hr : rules[i]? = some r) (hi : i ∉ ruleUsersK k y rules) : (k, y) ∉ evRefs (evRule r) := by
  intro hmem
  have hlt : i < rules.length := (List.getElem?_eq_some_iff.mp hr).1
  have hin : i ∈ ruleUsersK k y rules := by
    simp only [ruleUsersK, List.mem_filter, List.mem_range, hr, List.contains_eq_mem,
      decide_eq_true_eq]
    exact ⟨hlt, hmem⟩
  exact hi hin

/-- `ruleUsersK` of a relation `simEnv B` finds, from `relRulesUsersK`. -/
theorem ruleUsersK_of_rel {B : Builtins} {k : Nat} {y x : IL.Id} {v : RelDef} {l : List Nat}
    (h : (simEnv B).findRel? x = some v) (hl : relRulesUsersK k y x = some l) :
    ruleUsersK k y v.2.2.2 = l := by
  rw [VBytes.findRel?_simEnv_eq] at h
  simpa [relRulesUsersK, h] using hl

/-- A rule of a reachable relation with no reference to `$vbytes_`, `Step` or `Step_read` is
`GoodEvs`. -/
theorem goodEvs_rule {B : Builtins} {x : IL.Id} (hx : (0, x) ∈ stepReach) {v : RelDef} {i : Nat}
    {r : Rule} (h : (simEnv B).findRel? x = some v) (hr : v.2.2.2[i]? = some r)
    (hv : (1, "vbytes_") ∉ evRefs (evRule r)) (hs : (0, "Step") ∉ evRefs (evRule r))
    (hsr : (0, "Step_read") ∉ evRefs (evRule r)) : GoodEvs (evRule r) := by
  refine goodEvs_of (L := relDefEv v) (fun e he => ?_) (findRel?_reach hx h).1 hv hs hsr
  simp only [relDefEv, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨r, List.mem_of_getElem? hr, he⟩

theorem pure_mem_stepReach : (0, "Step_pure") ∈ stepReach := by decide +kernel
theorem read_mem_stepReach : (0, "Step_read") ∈ stepReach := by decide +kernel

/-- **Every rule of `Step_pure` is `GoodEvs`.** -/
theorem goodRule_pure (i : Nat) : GoodRule "Step_pure" i := by
  intro B v r h hr
  refine goodEvs_rule pure_mem_stepReach h hr (VBytes.pure_noVBytes h hr) ?_ ?_
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h pure_step]; simp)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h pure_read]; simp)

/-- **Every rule of `Step_read` other than 43 (`vload-num-val`) is `GoodEvs`.** -/
theorem goodRule_read {i : Nat} (hi : i ≠ 43) : GoodRule "Step_read" i := by
  intro B v r h hr
  refine goodEvs_rule read_mem_stepReach h hr ?_ ?_ ?_
  · exact VBytes.not_mem_ruleUsers hr
      (by rw [VBytes.ruleUsers_of_rel h VBytes.relRulesUsers_read]; simpa using hi)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h read_step]; simp)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h read_read]; simp)

/-- **Every rule of `Step` other than 1–5 and 23 (`vstore-val`) is `GoodEvs`.** -/
theorem goodRule_step {i : Nat} (hi : i ∉ [1, 2, 3, 4, 5, 23]) : GoodRule "Step" i := by
  intro B v r h hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  refine goodEvs_rule Round7.Script.step_mem_stepReach h hr ?_ ?_ ?_
  · exact VBytes.not_mem_ruleUsers hr
      (by rw [VBytes.ruleUsers_of_rel h VBytes.relRulesUsers_step]; simpa using hi.2.2.2.2.2)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h step_step]; simp; omega)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h step_read]; simpa using hi.1)

/-- `Step_read` off the memory SIMD rules: `GoodRule`. -/
theorem goodRule_read_ms {i : Nat} (hi : i ∉ MemSimd.msReadRules) : GoodRule "Step_read" i :=
  goodRule_read fun h => hi (by subst h; decide)

/-- The store-changing rules of `Step` off the memory SIMD rules: `GoodRule`. -/
theorem goodRule_step_ms {i : Nat} (h6 : 6 ≤ i) (hi : i ∉ MemSimd.stepMSRules) :
    GoodRule "Step" i :=
  goodRule_step fun h => by
    simp only [MemSimd.stepMSRules, List.mem_cons, List.not_mem_nil, or_false] at h hi
    omega

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
