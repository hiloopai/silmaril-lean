module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Read
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# Round 6: which `Step_read` rules can fire where

* `readCheck` (over the script): every rule of `Step_read` but the eight cast rules is plain for
  `Expand` and names a constructor that is neither a reference's nor a cast's (`pairTags`).
* `deadAt_castRule`: the eight cast rules cannot fire away from a cast pair.
* `closedAt_nonpair`: away from a cast pair, every rule is plain or dead.
* `fires_of_firesB_read`: every non-cast rule of `Step_read` that fires under the new reading
  fires under the old one, at every left-hand side.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round5.Read (readDoneK)
open Reading (FiresB DeadAt ClosedAt PlainRule)

variable {H : Type} {hn : H → String}

/-- One rule of `Step_read` passes the check: plain for `Expand`, naming a constructor outside
`pairTags`. -/
def ruleOk (r : Rule) : Bool :=
  Reading.plainRuleB ["Expand"] r && (RefsGC.ruleTags r).any (fun op => !decide (op ∈ pairTags))

/-- The cast rules' indices, as a test. -/
def isCastIdx (j : Nat) : Bool :=
  j == 2 || j == 3 || j == 4 || j == 5 || j == 65 || j == 66 || j == 67 || j == 68

/-- The check on `Step_read` from index `k` on: each rule is a cast rule or passes `ruleOk`. -/
def readCheckB : Nat → List Rule → Bool
  | _, [] => true
  | k, r :: rs => (isCastIdx k || ruleOk r) && readCheckB (k + 1) rs

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **The check holds of the pinned script.** -/
theorem readCheck :
    readCheckB 0 (RefsGC.relRules (envOfScript Specs.wasm30) "Step_read") = true := by
  rfl

/-- The check at one index. -/
theorem readCheckB_at : ∀ {k : Nat} {rules : List Rule}, readCheckB k rules = true →
    ∀ {j : Nat} {r : Rule}, rules[j]? = some r → isCastIdx (k + j) = true ∨ ruleOk r = true
  | _, [], _, _, _, hj => by simp at hj
  | k, r' :: rs, h, j, r, hj => by
    have h' : (isCastIdx k = true ∨ ruleOk r' = true) ∧ readCheckB (k + 1) rs = true := by
      simpa only [readCheckB, Bool.and_eq_true, Bool.or_eq_true] using h
    cases j with
    | zero =>
      obtain rfl : r' = r := by simpa using hj
      simpa using h'.1
    | succ j =>
      have e : k + (j + 1) = k + 1 + j := by omega
      rw [e]
      exact readCheckB_at h'.2 (by simpa using hj)

/-- `isCastIdx` is membership in `readDoneK`. -/
theorem isCastIdx_iff (j : Nat) : isCastIdx j = true ↔ j ∈ readDoneK := by
  simp only [isCastIdx, readDoneK, Bool.or_eq_true, beq_iff_eq, List.mem_cons, List.mem_nil_iff,
    or_false, or_assoc]

/-- A non-cast rule of `Step_read`: plain for `Expand`, without empty-domain options in its
conclusion, and naming a constructor outside `pairTags`. -/
theorem readCheck_at {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    {j : Nat} {r : Rule} (hj : rules[j]? = some r) (hk : j ∉ readDoneK) :
    PlainRule (· ∈ ["Expand"]) r ∧ Reading.hasOptNil (Reading.ruleConcl r) = false ∧
      ∃ op' ∈ RefsGC.ruleTags r, op' ∉ pairTags := by
  have hrr : RefsGC.relRules (envOfScript Specs.wasm30) "Step_read" = rules := by
    simp only [RefsGC.relRules, ← simEnv_findRel B, hrel]
  have hc := readCheckB_at (hrr ▸ readCheck) hj
  rw [Nat.zero_add, isCastIdx_iff] at hc
  have hc' : Reading.plainRuleB ["Expand"] r = true ∧
      ∃ op' ∈ RefsGC.ruleTags r, op' ∉ pairTags := by
    simpa [ruleOk] using hc.resolve_left hk
  have hp : PlainRule (· ∈ ["Expand"]) r := Reading.plainRule_of_plainRuleB hc'.1
  obtain ⟨nm, qs, op₀, e, prems⟩ := r
  exact ⟨hp, hp.1, hc'.2⟩

/-- A rule fact names the rule at its index. -/
theorem rule_eq_of_ruleAt {env : Env} {x : IL.Id} {op op' : MixopS} {k : Nat} {r₀ r : Rule}
    {ps : List Param} {t : Typ} {rules : List Rule} (h : HasRuleAt env x op k r₀)
    (hrel : env.findRel? x = some (ps, op', t, rules)) (hk : rules[k]? = some r) : r = r₀ := by
  obtain ⟨ps', t', rules', hrel', -, hk'⟩ := h
  have he := hrel.symm.trans hrel'
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨-, -, -, rfl⟩ := he
  exact Option.some.inj (hk.symm.trans hk')

/-- The rules of `Step_read` at the cast indices are the eight cast rules. -/
theorem castRule_cases {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    {j : Nat} {r : Rule} (hj : j ∈ readDoneK) (hjr : rules[j]? = some r) :
    r = brOnCastSucceedRule ∨ r = brOnCastFailRule ∨ r = brOnCastFailSucceedRule ∨
      r = brOnCastFailFailRule ∨ r = refTestTrueRule ∨ r = refTestFalseRule ∨
      r = refCastSucceedRule ∨ r = refCastFailRule := by
  have RR : HasReadRules (simEnv B) := State.hasReadRules_simEnv B
  simp only [readDoneK, List.mem_cons, List.mem_nil_iff, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [.inl (rule_eq_of_ruleAt RR.brOnCastSucceed hrel hjr),
    .inr (.inl (rule_eq_of_ruleAt RR.brOnCastFail hrel hjr)),
    .inr (.inr (.inl (rule_eq_of_ruleAt RR.brOnCastFailSucceed hrel hjr))),
    .inr (.inr (.inr (.inl (rule_eq_of_ruleAt RR.brOnCastFailFail hrel hjr)))),
    .inr (.inr (.inr (.inr (.inl (rule_eq_of_ruleAt RR.refTestTrue hrel hjr))))),
    .inr (.inr (.inr (.inr (.inr (.inl (rule_eq_of_ruleAt RR.refTestFalse hrel hjr)))))),
    .inr (.inr (.inr (.inr (.inr (.inr (.inl (rule_eq_of_ruleAt RR.refCastSucceed hrel hjr))))))),
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (rule_eq_of_ruleAt RR.refCastFail hrel hjr)))))))]

/-- A cast rule fires only at a cast pair, under either reading. -/
theorem pair_of_castBody {B : Builtins} {D : Interp} {els : Prop} {c : Config H} {b : Value}
    {r : Rule} (hr : r = brOnCastSucceedRule ∨ r = brOnCastFailRule ∨
      r = brOnCastFailSucceedRule ∨ r = brOnCastFailFailRule ∨ r = refTestTrueRule ∨
      r = refTestFalseRule ∨ r = refCastSucceedRule ∨ r = refCastFailRule)
    (hb : Reading.RuleBodyB (simEnv B) D els [] [] "%~>%" r (.tuple [configV hn c, b])) :
    CastPair c.code := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [pair_of_brOnCast (.inl rfl) (Reading.ruleBody_of_ruleBodyB (by rfl) hb),
    pair_of_brOnCast (.inr rfl) (Reading.ruleBody_of_ruleBodyB (by rfl) hb),
    pair_of_brOnCastFail (.inl rfl) (Reading.ruleBody_of_ruleBodyB (by rfl) hb),
    pair_of_brOnCastFail (.inr rfl) (Reading.ruleBody_of_ruleBodyB (by rfl) hb),
    pair_of_refTest (.inl rfl) (Reading.ruleBody_of_ruleBodyB (by rfl) hb),
    pair_of_refTest (.inr rfl) (Reading.ruleBody_of_ruleBodyB (by rfl) hb),
    pair_of_refCast (.inl rfl) (Reading.ruleBody_of_ruleBodyB (by rfl) hb),
    pair_of_refCast (.inr rfl) (Reading.ruleBody_of_ruleBodyB (by rfl) hb)]

/-- **The eight cast rules cannot fire away from a cast pair.** -/
theorem deadAt_castRule {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    {j : Nat} {r : Rule} (hj : j ∈ readDoneK) (hjr : rules[j]? = some r) {c : Config H}
    (hnp : ¬ CastPair c.code) : DeadAt (simEnv B) r (configV hn c) :=
  fun _ _ _ hb => hnp (pair_of_castBody (castRule_cases hrel hj hjr) hb)

/-- **Away from a cast pair, every rule of `Step_read` is plain for `Expand` or dead.** -/
theorem closedAt_nonpair {B : Builtins} {c : Config H} (hnp : ¬ CastPair c.code) :
    ClosedAt (simEnv B) (· ∈ ["Expand"]) "Step_read" (configV hn c) := by
  intro ps op t rules hrel r hr
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hr
  by_cases hk : j ∈ readDoneK
  · exact .inr (deadAt_castRule hrel hk hj hnp)
  · exact .inl (readCheck_at hrel hj hk).1

/-- **A non-cast rule of `Step_read` fires the same under both readings**, at every left-hand
side: at a cast pair it fires under neither, elsewhere every rule is plain or dead. -/
theorem fires_of_firesB_read {B : Builtins} {i : Nat} (hk : i ∉ readDoneK) {c : Config H}
    {w : Value} (hfi : FiresB (simEnv B) "Step_read" i (.tuple [configV hn c, w])) :
    Fires (simEnv B) "Step_read" i (.tuple [configV hn c, w]) := by
  by_cases hp : CastPair c.code
  · exfalso
    obtain ⟨t, rules, r, hrel, hr, hb⟩ := hfi
    obtain ⟨-, hno, op, hop, hS⟩ := readCheck_at hrel hr hk
    obtain ⟨s, f, code⟩ := c
    exact Reading.deadAt_of_tags (lhsIn_pair hp) hno hop hS _ _ _ hb
  · obtain ⟨t, rules, hrel⟩ := Reading.findRel_read B
    exact (Reading.firesB_iff_at (Reading.closed_expand B) hrel (closedAt_nonpair hp)).1 hfi

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
