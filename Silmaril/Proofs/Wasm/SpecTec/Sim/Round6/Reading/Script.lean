module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Transfer
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms
public import Silmaril.Wasm.SpecTec.Sim.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# Round 6: which rules of the pinned script the new reading changes

* `closed_pure`: `Step_pure` is closed (no rule has an empty-domain option iteration in its
  conclusion, and no rule consults a relation), so **every `Step_pure` fact transfers**:
  `firesB_pure_iff`, `sPureB_iff`.
* `closed_expand`: so is `Expand`.
* `plainOrTags_read`: every rule of `Step_read` is plain for `Expand`, except rules that name one
  of the four cast constructors (`castTags`: rules 2, 4, 65 and 67 consult `Ref_ok`). So at a
  left-hand side whose code names no cast constructor (`closedAt_read`), **every `Step_read`
  rule fires the same under both readings** (`firesB_read_iff`, `sReadB_iff`), including the
  `otherwise` rules.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open RefsGC (LhsIn ruleTags)

/-! ## The checks -/

/-- `plainRuleB` decides `PlainRule`. -/
theorem plainRule_of_plainRuleB {S : List IL.Id} {r : Rule} (h : plainRuleB S r = true) :
    PlainRule (· ∈ S) r := by
  obtain ⟨nm, qs, op, e, prems⟩ := r
  simp only [plainRuleB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    decide_eq_true_eq] at h
  exact h

/-- `closedB` decides `Closed`. -/
theorem closed_of_closedB {env : Env} {S : List IL.Id} (h : closedB env S = true) :
    Closed env (· ∈ S) := by
  intro x hx ps op t rules hrel r hr
  have hx' := List.all_eq_true.1 h x hx
  rw [hrel] at hx'
  exact plainRule_of_plainRuleB (List.all_eq_true.1 hx' r hr)

/-- `Closed` only looks relations up. -/
theorem closed_congr {env env' : Env} {S : IL.Id → Prop} (h : ∀ x, env'.findRel? x = env.findRel? x)
    (C : Closed env S) : Closed env' S :=
  fun x hx ps op t rules hrel => C x hx ps op t rules ((h x).symm.trans hrel)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step_pure` is closed in the pinned script. -/
theorem closedB_pure : closedB (envOfScript Specs.wasm30) ["Step_pure"] = true := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Expand` is closed in the pinned script. -/
theorem closedB_expand : closedB (envOfScript Specs.wasm30) ["Expand"] = true := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- Every rule of `Step_read` is plain for `Expand` or names a cast constructor. -/
theorem plainOrTagsB_read :
    plainOrTagsB ["Expand"] castTags (RefsGC.relRules (envOfScript Specs.wasm30) "Step_read") =
      true := by
  rfl

/-! ## `Step_pure` and `Expand` -/

/-- **`Step_pure` is closed** in every `simEnv B`. -/
theorem closed_pure (B : Builtins) : Closed (simEnv B) (· ∈ ["Step_pure"]) :=
  closed_congr (simEnv_findRel B) (closed_of_closedB closedB_pure)

/-- **`Expand` is closed** in every `simEnv B`. -/
theorem closed_expand (B : Builtins) : Closed (simEnv B) (· ∈ ["Expand"]) :=
  closed_congr (simEnv_findRel B) (closed_of_closedB closedB_expand)

/-- **Every rule of `Step_pure` fires the same under both readings.** -/
theorem firesB_pure_iff (B : Builtins) {i : Nat} {v : Value} :
    FiresB (simEnv B) "Step_pure" i v ↔ Fires (simEnv B) "Step_pure" i v :=
  firesB_iff_of_closed (closed_pure B) (List.mem_singleton_self _)

/-- **`Step_pure` is the same relation under both readings.** -/
theorem sPureB_iff (B : Builtins) {is js : List Value} :
    SPureB (simEnv B) is js ↔ SPure (simEnv B) is js :=
  dderivesB_otherwise_iff_of_closed (closed_pure B) (List.mem_singleton_self _)

/-! ## `Step_read` away from the casts -/

/-- A rule naming a constructor the left-hand side avoids cannot fire there, under either
reading. -/
theorem deadAt_of_tags {env : Env} {r : Rule} {S : List MixopS} {a : Value} (ha : LhsIn S a)
    (hn : hasOptNil (ruleConcl r) = false) {op : MixopS} (hop : op ∈ ruleTags r) (hS : op ∉ S) :
    DeadAt env r a := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  intro D els b hb
  rw [ruleBodyB_iff_of_not (show hasOptNil e = false from hn)] at hb
  exact RefsGC.not_ruleBody_of_tags ha hop hS hb

/-- **At a left-hand side naming no cast constructor, every rule of `Step_read` is plain for
`Expand` or dead.** -/
theorem closedAt_read (B : Builtins) {S : List MixopS} (hS : ∀ op ∈ castTags, op ∉ S) {a : Value}
    (ha : LhsIn S a) : ClosedAt (simEnv B) (· ∈ ["Expand"]) "Step_read" a := by
  intro ps op t rules hrel r hr
  have hrr : RefsGC.relRules (envOfScript Specs.wasm30) "Step_read" = rules := by
    simp only [RefsGC.relRules, ← simEnv_findRel B, hrel]
  have hc := List.all_eq_true.1 plainOrTagsB_read r (hrr ▸ hr)
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    decide_eq_true_eq] at hc
  rcases hc with hp | ⟨hn, op', hop, hK⟩
  · exact .inl (plainRule_of_plainRuleB hp)
  · exact .inr (deadAt_of_tags ha hn hop (hS op' hK))

/-- `Step_read` in every `simEnv B`. -/
theorem findRel_read (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step_read" = some ([], "%~>%", t, rules) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_simEnv B
    (Equiv.ExecRead.hasReadRules_wasm30).refTestTrue
  exact ⟨t, rules, hrel⟩

/-- **Away from the casts, every rule of `Step_read` fires the same under both readings**,
`otherwise` rules included. -/
theorem firesB_read_iff (B : Builtins) {S : List MixopS} (hS : ∀ op ∈ castTags, op ∉ S)
    {a b : Value} (ha : LhsIn S a) {i : Nat} :
    FiresB (simEnv B) "Step_read" i (.tuple [a, b]) ↔
      Fires (simEnv B) "Step_read" i (.tuple [a, b]) := by
  obtain ⟨t, rules, hrel⟩ := findRel_read B
  exact firesB_iff_at (closed_expand B) hrel (closedAt_read B hS ha)

/-- **Away from the casts, `Step_read` is the same relation under both readings.** -/
theorem sReadB_iff (B : Builtins) {S : List MixopS} (hS : ∀ op ∈ castTags, op ∉ S)
    {c : Value} {js : List Value} (ha : LhsIn S c) :
    SReadB (simEnv B) c js ↔ SRead (simEnv B) c js := by
  obtain ⟨t, rules, hrel⟩ := findRel_read B
  exact dderivesB_iff_at (closed_expand B) hrel (closedAt_read B hS ha)

/-! ## `Step` -/

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step_pure` and `Expand` together are closed in the pinned script. -/
theorem closedB_pureExpand :
    closedB (envOfScript Specs.wasm30) ["Step_pure", "Expand"] = true := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step`'s rules 0 (`pure`) and 6–35 (the rules that touch the store) are plain for
`Step_pure` and `Expand`, and none has an `otherwise` premise. -/
theorem stepPlainB :
    ((RefsGC.relRules (envOfScript Specs.wasm30) "Step").take 1 ++
      (RefsGC.relRules (envOfScript Specs.wasm30) "Step").drop 6).all
      (plainNoElseB ["Step_pure", "Expand"]) = true := by
  rfl

/-- `plainNoElseB` decides plainness and the absence of `otherwise`. -/
theorem of_plainNoElseB {S : List IL.Id} {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : plainNoElseB S (.ruleD nm qs op e prems) = true) :
    PlainRule (· ∈ S) (.ruleD nm qs op e prems) ∧ ∀ pr ∈ prems, noElsePr pr = true := by
  simp only [plainNoElseB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨plainRule_of_plainRuleB h.1, h.2⟩

/-- A rule of `Step` at index 0 or `≥ 6` is one `stepPlainB` checks. -/
theorem mem_stepChecked {rules : List Rule} {i : Nat} {r : Rule} (hr : rules[i]? = some r)
    (hi : i = 0 ∨ 6 ≤ i) : r ∈ rules.take 1 ++ rules.drop 6 := by
  rcases hi with rfl | hi
  · have h0 : (rules.take 1)[0]? = some r := by rw [List.getElem?_take]; simpa using hr
    exact List.mem_append_left _ (List.mem_of_getElem? h0)
  · have h6 : (rules.drop 6)[i - 6]? = some r := by
      rw [List.getElem?_drop, show 6 + (i - 6) = i by omega]
      exact hr
    exact List.mem_append_right _ (List.mem_of_getElem? h6)

/-- **Every rule of `Step` but `read` and the four context rules fires the same under both
readings.** Rules 1–5 consult `Step_read` or `Step`; they are lifted by `sstepB_read` and the
`sstepB_ctxt*` lemmas instead. -/
theorem firesB_step_iff (B : Builtins) {i : Nat} (hi : i = 0 ∨ 6 ≤ i) {v : Value} :
    FiresB (simEnv B) "Step" i v ↔ Fires (simEnv B) "Step" i v := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := (hasStepRules_simEnv B).pure
  have C : Closed (simEnv B) (· ∈ ["Step_pure", "Expand"]) :=
    closed_congr (simEnv_findRel B) (closed_of_closedB closedB_pureExpand)
  have hrr : RefsGC.relRules (envOfScript Specs.wasm30) "Step" = rules := by
    simp only [RefsGC.relRules, ← simEnv_findRel B, hrel]
  cases hr : rules[i]? with
  | none =>
    refine ⟨fun ⟨t', rules', r, hrel', hr', _⟩ => ?_, fun ⟨t', rules', r, hrel', hr', _⟩ => ?_⟩
    all_goals
      have he := Option.some.inj (hrel.symm.trans hrel')
      obtain rfl : rules = rules' := by
        simp only [Prod.mk.injEq, true_and] at he
        exact he.2
      exact absurd (hr.symm.trans hr') (by simp)
  | some r =>
    obtain ⟨nm, qs, op, e, prems⟩ := r
    have hc := List.all_eq_true.1 stepPlainB _ (hrr ▸ mem_stepChecked hr hi)
    obtain ⟨hp, hne⟩ := of_plainNoElseB hc
    exact firesB_iff_of_plain C hrel hr hp hne

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading
