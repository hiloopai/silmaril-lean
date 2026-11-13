module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30X.Defs
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The rule tables of `FwdB30X`, against the pinned script

`pureInfoT`, `readInfoT` and `stepInfoT` are `ruleInfo` on every rule of `Step_pure`,
`Step_read` and `Step` of the pinned wasm-3.0 script (kernel `rfl`), and so of `simEnv B` for
every `B` (`RefsGC.relRules_simEnv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (relRules relRules_simEnv)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `pureInfoT` is the table of `Step_pure`. -/
theorem pureInfoT_eq :
    (relRules (envOfScript Specs.wasm30) "Step_pure").map ruleInfo = pureInfoT := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `readInfoT` is the table of `Step_read`. -/
theorem readInfoT_eq :
    (relRules (envOfScript Specs.wasm30) "Step_read").map ruleInfo = readInfoT := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `stepInfoT` is the table of `Step`. -/
theorem stepInfoT_eq :
    (relRules (envOfScript Specs.wasm30) "Step").map ruleInfo = stepInfoT := by
  rfl

/-- The three tables in `simEnv B`. -/
theorem infoT_simEnv (B : Builtins) :
    (relRules (simEnv B) "Step_pure").map ruleInfo = pureInfoT ∧
      (relRules (simEnv B) "Step_read").map ruleInfo = readInfoT ∧
      (relRules (simEnv B) "Step").map ruleInfo = stepInfoT := by
  simp only [relRules_simEnv]
  exact ⟨pureInfoT_eq, readInfoT_eq, stepInfoT_eq⟩

/-! ## The checks on the instruction constructors -/

/-- The `nonV` tables. -/
theorem nvT_eq : pureInfoT.map nonV = pureNVT ∧ readInfoT.map nonV = readNVT ∧
    stepInfoT.map nonV = stepNVT := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem outside_cons_eq (t : MixopS) (row : List MixopS × Option Nat) :
    outside (t :: valTags) row = (nonV row).1.any (· != t) := by
  obtain ⟨l, n⟩ := row
  simp only [outside, nonV, List.any_filter]
  congr 1
  funext op
  simp only [List.contains_cons, Bool.not_or, bne]
  cases op == t <;> cases valTags.contains op <;> rfl

theorem outside_val_eq (row : List MixopS × Option Nat) :
    outside valTags row = !(nonV row).1.isEmpty := by
  obtain ⟨l, n⟩ := row
  simp only [outside, nonV]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, List.filter_cons]
    cases h : valTags.contains a
    · simp
    · simpa using ih

theorem chkProper_eq (k : Nat) (t : MixopS) (T : List (List MixopS × Option Nat)) :
    chkProper k t T = chkProperN k t (T.map nonV) := by
  simp only [chkProper, chkProperN, List.all_map]
  congr 1
  funext row
  simp only [Function.comp, outside_cons_eq, outside_val_eq]
  rfl

theorem chkFull_eq (k : Nat) (t : MixopS) (T : List (List MixopS × Option Nat)) :
    chkFull k t T = chkFullN k t (T.map nonV) := by
  simp only [chkFull, chkFullN, List.all_map]
  congr 1
  funext row
  simp only [Function.comp, outside_cons_eq]
  rfl

/-- `pureOk` is `pureOkN`. -/
theorem pureOk_eq (k : Nat) (t : MixopS) : pureOk k t = pureOkN k t := by
  simp only [pureOk, pureOkN, stepRestT, chkProper_eq, chkFull_eq, List.map_drop, nvT_eq]

/-- `readOk` is `readOkN`. -/
theorem readOk_eq (k : Nat) (t : MixopS) : readOk k t = readOkN k t := by
  simp only [readOk, readOkN, stepRestT, chkProper_eq, chkFull_eq, List.map_drop, nvT_eq]

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
