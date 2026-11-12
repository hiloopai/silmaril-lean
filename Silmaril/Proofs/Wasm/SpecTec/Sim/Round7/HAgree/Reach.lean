module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.HostOnly

/-!
# Round 7, `BD`: which bodies `simEnv B` finds are `GoodEvs`

`Round7.VAgree`'s reachability facts with `$hostcall` also excluded. The kernel facts are reused:
`VAgree.stepRelOnly_fixed` (only `Step` and `Step_read` refer to `Step` or `Step_read`),
`Round7.VBytes` (only `Step_read` and `Step` refer to `$vbytes_`) and `HostOnly` (only `Step`
refers to `$hostcall`):

* `goodClauses`, `goodRules`: the clauses of a `GoodName` definition and the rules of a `GoodRel`
  relation are `GoodEvs`;
* `goodRule_pure`, `goodRule_read`, `goodRule_step`: every rule of `Step_pure`, every rule of
  `Step_read` other than 43, and every rule of `Step` other than 1–5, 8, 9 and 23 is `GoodEvs`
  (`GoodRule`). Rules 1–5 of `Step` refer to `Step_read` or `Step`, rules 43 and 23 call
  `$vbytes_`, and rules 8 and 9 call `$hostcall`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (Ev Item items evRefs evRule stepReach stepReach_closed mem_evRefs defDefEv
  relDefEv findDef?_simEnv_item findRel?_simEnv_item findRel?_reach)
open Round7.VAgree (GoodRel item_noStepRel not_mem_ruleUsersK ruleUsersK_of_rel pure_step pure_read
  read_step read_read step_step step_read pure_mem_stepReach read_mem_stepReach)

/-- **A sublist of a reachable body with no reference to `$vbytes_`, `$hostcall`, `Step` or
`Step_read` is `GoodEvs`.** -/
theorem goodEvs_of {l L : List Ev} (hsub : ∀ e ∈ l, e ∈ L) (hR : ∀ r ∈ evRefs L, r ∈ stepReach)
    (hv : (1, "vbytes_") ∉ evRefs l) (hh : (1, "hostcall") ∉ evRefs l)
    (hs : (0, "Step") ∉ evRefs l) (hr : (0, "Step_read") ∉ evRefs l) : GoodEvs l := by
  intro e he
  cases e with
  | ref k x =>
    have hL := hR _ (mem_evRefs (hsub _ he))
    have hl := mem_evRefs he
    rcases k with _ | _ | k
    · refine ⟨hL, fun hx => ?_, fun hx => ?_⟩
      · subst hx; exact hs hl
      · subst hx; exact hr hl
    · exact ⟨hL, fun hx => by subst hx; exact hv hl, fun hx => by subst hx; exact hh hl⟩
    · trivial
  | atom a => trivial
  | comp => trivial
  | upd r ats => trivial

/-- An item reachable from `Step`, other than `Step` and `Step_read`, is `GoodEvs`. -/
theorem goodEvs_of_item {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) (hx : ¬ (it.1 = 0 ∧ (it.2.1 = "Step_read" ∨ it.2.1 = "Step"))) :
    GoodEvs it.2.2 :=
  goodEvs_of (fun _ he => he) (stepReach_closed h hR) (VBytes.item_noVBytes h hx)
    (item_noHostcall h fun h' => hx ⟨h'.1, Or.inr h'.2⟩)
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

/-- A rule of a reachable relation with no reference to `$vbytes_`, `$hostcall`, `Step` or
`Step_read` is `GoodEvs`. -/
theorem goodEvs_rule {B : Builtins} {x : IL.Id} (hx : (0, x) ∈ stepReach) {v : RelDef} {i : Nat}
    {r : Rule} (h : (simEnv B).findRel? x = some v) (hr : v.2.2.2[i]? = some r)
    (hv : (1, "vbytes_") ∉ evRefs (evRule r)) (hh : (1, "hostcall") ∉ evRefs (evRule r))
    (hs : (0, "Step") ∉ evRefs (evRule r))
    (hsr : (0, "Step_read") ∉ evRefs (evRule r)) : GoodEvs (evRule r) := by
  refine goodEvs_of (L := relDefEv v) (fun e he => ?_) (findRel?_reach hx h).1 hv hh hs hsr
  simp only [relDefEv, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨r, List.mem_of_getElem? hr, he⟩

/-- **Every rule of `Step_pure` is `GoodEvs`.** -/
theorem goodRule_pure (i : Nat) : GoodRule "Step_pure" i := by
  intro B v r h hr
  refine goodEvs_rule pure_mem_stepReach h hr (VBytes.pure_noVBytes h hr) (pure_noHostcall h hr)
    ?_ ?_
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h pure_step]; simp)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h pure_read]; simp)

/-- **Every rule of `Step_read` other than 43 (`vload-num-val`) is `GoodEvs`.** -/
theorem goodRule_read {i : Nat} (hi : i ≠ 43) : GoodRule "Step_read" i := by
  intro B v r h hr
  refine goodEvs_rule read_mem_stepReach h hr ?_ (read_noHostcall h hr) ?_ ?_
  · exact VBytes.not_mem_ruleUsers hr
      (by rw [VBytes.ruleUsers_of_rel h VBytes.relRulesUsers_read]; simpa using hi)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h read_step]; simp)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h read_read]; simp)

/-- The rules of `Step` that are not `GoodRule`: the context rules, the host calls and
`vstore-val`. -/
def stepBad : List Nat := [1, 2, 3, 4, 5, 8, 9, 23]

/-- **Every rule of `Step` other than 1–5, 8, 9 and 23 is `GoodEvs`.** -/
theorem goodRule_step {i : Nat} (hi : i ∉ stepBad) : GoodRule "Step" i := by
  intro B v r h hr
  simp only [stepBad, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  refine goodEvs_rule Round7.Script.step_mem_stepReach h hr ?_
    (step_noHostcall h hr hi.2.2.2.2.2.1 hi.2.2.2.2.2.2.1) ?_ ?_
  · exact VBytes.not_mem_ruleUsers hr
      (by rw [VBytes.ruleUsers_of_rel h VBytes.relRulesUsers_step]; simpa using hi.2.2.2.2.2.2.2)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h step_step]; simp; omega)
  · exact not_mem_ruleUsersK hr (by rw [ruleUsersK_of_rel h step_read]; simpa using hi.1)

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
