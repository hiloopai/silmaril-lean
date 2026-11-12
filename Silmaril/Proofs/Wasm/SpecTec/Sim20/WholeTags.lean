module

public import Silmaril.Wasm.SpecTec.Sim20.Whole.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureRules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Otherwise
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Transfer

/-!
# The wasm-2.0 reduction relations: closedness, rule tags and the structural rules

* `closed_step20`: `Step`, `Step_pure` and `Step_read` of the wasm-2.0 script form a closed set
  (no rule conclusion has an empty-domain option iteration, and the premises consult only these
  three relations). So on all three the Round 6 backend reading is the declarative reading:
  `sstepB20_iff : SStepB (simEnv20 B) c c' ↔ SStep (simEnv20 B) c c'`, and likewise
  `sreadB20_iff`. This is the backend reading of the non-closed `Step` asked for in
  `docs/projects/spectec/README.md`: for 2.0 it is not a separate reading at all.
* `pureTags20`, `readTags20`, `stepTags20`: the instruction constructors that the left-hand side
  of each rule of the three relations forces (`RefsGC.ruleTags`), checked against the script by
  kernel `rfl` (`pureTags20_eq`, …).
* `not_dderives_of_table`: a relation does not derive anything at a left-hand side whose
  constructors avoid, rule by rule, a forced constructor, except at the rules listed as
  exceptions, which are refuted separately.
* `hasRuleAt_stepPure`, …: the provenance of the four structural rules of `Sim20.Whole.Defs`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (RuleBody DDerives otherwise SStep SRead dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (ruleTags relRules LhsIn checkAvoid checkAvoid_sound
  not_ruleBody_of_tags)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB SReadB closedB Closed closed_of_closedB
  closed_congr dderivesB_otherwise_iff_of_closed)

variable (B : Builtins)

set_option maxRecDepth 100000

/-! ## Closedness -/

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step`, `Step_pure` and `Step_read` are closed in the wasm-2.0 script. -/
theorem closedB_step20 :
    closedB (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed)
      ["Step", "Step_pure", "Step_read"] = true := by
  rfl

/-- The three reduction relations are closed in `simEnv20 B`. -/
theorem closed_step20 : Closed (simEnv20 B) (· ∈ ["Step", "Step_pure", "Step_read"]) :=
  closed_congr (fun _ => rfl) (closed_of_closedB closedB_step20)

/-- **On wasm-2.0's `Step` the backend reading is the declarative reading.** -/
theorem sstepB20_iff {c c' : Value} : SStepB (simEnv20 B) c c' ↔ SStep (simEnv20 B) c c' :=
  dderivesB_otherwise_iff_of_closed (closed_step20 B) (by simp)

/-- On wasm-2.0's `Step_read` the backend reading is the declarative reading. -/
theorem sreadB20_iff {c : Value} {js : List Value} :
    SReadB (simEnv20 B) c js ↔ SRead (simEnv20 B) c js :=
  dderivesB_otherwise_iff_of_closed (closed_step20 B) (by simp)

/-! ## Rule tags -/

/-- The forced constructors of the 56 rules of wasm-2.0 `Step_pure`, in order. -/
def pureTags20 : List (List MixopS) :=
  [["UNREACHABLE"], ["NOP"], ["DROP"], ["CONST", "SELECT"], ["CONST", "SELECT"],
   ["CONST", "IF%%ELSE%"], ["CONST", "IF%%ELSE%"], ["LABEL_%{%}%"], ["LABEL_%{%}%"],
   ["LABEL_%{%}%"], ["CONST", "BR_IF"], ["CONST", "BR_IF"], ["CONST", "BR_TABLE"],
   ["CONST", "BR_TABLE"], ["FRAME_%{%}%"], ["FRAME_%{%}%"], ["LABEL_%{%}%"], ["TRAP"],
   ["LABEL_%{%}%"], ["FRAME_%{%}%"], ["CONST", "UNOP"], ["CONST", "UNOP"],
   ["CONST", "CONST", "BINOP"], ["CONST", "CONST", "BINOP"], ["CONST", "TESTOP"],
   ["CONST", "CONST", "RELOP"], ["CONST", "CVTOP"], ["CONST", "CVTOP"], ["REF.IS_NULL"],
   ["REF.IS_NULL"], ["VCONST", "VVUNOP"], ["VCONST", "VCONST", "VVBINOP"],
   ["VCONST", "VCONST", "VCONST", "VVTERNOP"], ["VCONST", "VVTESTOP"], ["VCONST", "VUNOP"],
   ["VCONST", "VUNOP"], ["VCONST", "VCONST", "VBINOP"], ["VCONST", "VCONST", "VBINOP"],
   ["VCONST", "VTESTOP"], ["VCONST", "VTESTOP"], ["VCONST", "VCONST", "VRELOP"],
   ["VCONST", "CONST", "VSHIFTOP"], ["VCONST", "VBITMASK"], ["VCONST", "VCONST", "VSWIZZLE"],
   ["VCONST", "VCONST", "VSHUFFLE"], ["CONST", "VSPLAT"], ["VCONST", "VEXTRACT_LANE"],
   ["VCONST", "VEXTRACT_LANE"], ["VCONST", "CONST", "VREPLACE_LANE"], ["VCONST", "VEXTUNOP"],
   ["VCONST", "VCONST", "VEXTBINOP"], ["VCONST", "VCONST", "VNARROW"], ["VCONST", "VCVTOP"],
   ["VCONST", "VCVTOP"], ["VCONST", "VCVTOP"], ["LOCAL.TEE"]]

/-- The forced constructors of the 47 rules of wasm-2.0 `Step_read`, in order. -/
def readTags20 : List (List MixopS) :=
  [["BLOCK"], ["LOOP"], ["CALL"], ["CONST", "CALL_INDIRECT"], ["CONST", "CALL_INDIRECT"],
   ["CALL_ADDR"], ["REF.FUNC"], ["LOCAL.GET"], ["GLOBAL.GET"], ["CONST", "TABLE.GET"],
   ["CONST", "TABLE.GET"], ["TABLE.SIZE"], ["CONST", "CONST", "TABLE.FILL"],
   ["CONST", "CONST", "TABLE.FILL"], ["CONST", "CONST", "TABLE.FILL"],
   ["CONST", "CONST", "CONST", "TABLE.COPY"], ["CONST", "CONST", "CONST", "TABLE.COPY"],
   ["CONST", "CONST", "CONST", "TABLE.COPY"], ["CONST", "CONST", "CONST", "TABLE.COPY"],
   ["CONST", "CONST", "CONST", "TABLE.INIT"], ["CONST", "CONST", "CONST", "TABLE.INIT"],
   ["CONST", "CONST", "CONST", "TABLE.INIT"], ["CONST", "LOAD"], ["CONST", "LOAD"],
   ["CONST", "LOAD"], ["CONST", "LOAD"], ["CONST", "VLOAD"], ["CONST", "VLOAD"],
   ["CONST", "VLOAD"], ["CONST", "VLOAD"], ["CONST", "VLOAD"], ["CONST", "VLOAD"],
   ["CONST", "VLOAD"], ["CONST", "VLOAD"], ["CONST", "VCONST", "VLOAD_LANE"],
   ["CONST", "VCONST", "VLOAD_LANE"], ["MEMORY.SIZE"], ["CONST", "CONST", "MEMORY.FILL"],
   ["CONST", "CONST", "MEMORY.FILL"], ["CONST", "CONST", "MEMORY.FILL"],
   ["CONST", "CONST", "CONST", "MEMORY.COPY"], ["CONST", "CONST", "CONST", "MEMORY.COPY"],
   ["CONST", "CONST", "CONST", "MEMORY.COPY"], ["CONST", "CONST", "CONST", "MEMORY.COPY"],
   ["CONST", "CONST", "CONST", "MEMORY.INIT"], ["CONST", "CONST", "CONST", "MEMORY.INIT"],
   ["CONST", "CONST", "CONST", "MEMORY.INIT"]]

/-- The forced constructors of the 22 rules of wasm-2.0 `Step`, in order. `Step/pure` and
`Step/read` (rules 0 and 1) force none. -/
def stepTags20 : List (List MixopS) :=
  [[], [], ["LABEL_%{%}%"], ["FRAME_%{%}%"], ["LOCAL.SET"], ["GLOBAL.SET"],
   ["CONST", "TABLE.SET"], ["CONST", "TABLE.SET"], ["CONST", "TABLE.GROW"],
   ["CONST", "TABLE.GROW"], ["ELEM.DROP"], ["CONST", "CONST", "STORE"],
   ["CONST", "CONST", "STORE"], ["CONST", "CONST", "STORE"], ["CONST", "CONST", "STORE"],
   ["CONST", "VCONST", "VSTORE"], ["CONST", "VCONST", "VSTORE"],
   ["CONST", "VCONST", "VSTORE_LANE"], ["CONST", "VCONST", "VSTORE_LANE"],
   ["CONST", "MEMORY.GROW"], ["CONST", "MEMORY.GROW"], ["DATA.DROP"]]

/-- `relRules` only looks relations up. -/
theorem relRules_simEnv20 (x : IL.Id) :
    relRules (simEnv20 B) x = relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) x :=
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `pureTags20` is the tag table of wasm-2.0 `Step_pure`. -/
theorem pureTags20_eq :
    (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) "Step_pure").map ruleTags =
      pureTags20 := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `readTags20` is the tag table of wasm-2.0 `Step_read`. -/
theorem readTags20_eq :
    (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) "Step_read").map ruleTags =
      readTags20 := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `stepTags20` is the tag table of wasm-2.0 `Step`. -/
theorem stepTags20_eq :
    (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) "Step").map ruleTags =
      stepTags20 := by
  rfl

/-! ## Refuting a relation by its tag table -/

/-- **A relation derives nothing at a left-hand side that avoids its tags.** If the constructors of
`a` lie in `S`, and every rule of `x` outside `exc` forces a constructor outside `S` (by the tag
table `T`), while the rules in `exc` are refuted separately, then `x` derives nothing at `(a, b)`
under the declarative reading. -/
theorem not_dderives_of_table {env : Env} {x : IL.Id} {t : Typ} {rules : List Rule}
    (hrel : env.findRel? x = some ([], "%~>%", t, rules)) {T : List (List MixopS)}
    (hT : (relRules env x).map ruleTags = T) {S : List MixopS} {exc : List Nat} {a b : Value}
    (ha : LhsIn S a) (hc : checkAvoid T T.length exc S = true)
    (hexc : ∀ i ∈ exc, ∀ r, rules[i]? = some r →
      ¬ RuleBody env (DDerives env (otherwise env)) (otherwise env x [] i (.tuple [a, b])) [] []
        "%~>%" r (.tuple [a, b])) :
    ¬ DDerives env (otherwise env) x "%~>%" [] (.tuple [a, b]) := by
  rw [dderives_iff_fires hrel]
  rintro ⟨i, t', rules', r, hrel', hr, hb⟩
  rw [hrel] at hrel'
  obtain ⟨rfl, rfl⟩ : t = t' ∧ rules = rules' := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
    exact ⟨hrel'.2.2.1, hrel'.2.2.2⟩
  by_cases hx : i ∈ exc
  · exact hexc i hx r hr hb
  · have hT' : rules.map ruleTags = T := by simpa [relRules, hrel] using hT
    have hi : i < T.length := by
      rw [← hT', List.length_map]
      exact (List.getElem?_eq_some_iff.1 hr).1
    obtain ⟨op, hop, hS⟩ := checkAvoid_sound hc hi hx
    have htag : T[i]?.getD [] = ruleTags r := by
      rw [← hT', List.getElem?_map, hr]
      rfl
    rw [htag] at hop
    exact not_ruleBody_of_tags ha hop hS hb

/-! ## The structural rules of `Step`: provenance -/

theorem hasRuleAt_stepPure : HasRuleAt (simEnv20 B) "Step" "%~>%" 0 stepPureRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_stepRead : HasRuleAt (simEnv20 B) "Step" "%~>%" 1 stepReadRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_ctxtLabel : HasRuleAt (simEnv20 B) "Step" "%~>%" 2 ctxtLabelRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_ctxtFrame : HasRuleAt (simEnv20 B) "Step" "%~>%" 3 ctxtFrameRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_read` is a relation without parameters. -/
theorem findRel_read20 :
    ∃ t rules, (simEnv20 B).findRel? "Step_read" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
