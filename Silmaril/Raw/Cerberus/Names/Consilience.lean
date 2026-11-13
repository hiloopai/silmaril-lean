module

public import Silmaril.Cerberus.Consilience.Equivalence.Defs

/-! # Cerberus correspondence index

Each row joins the Lem name in `Names` to a pinned external declaration. Evidence
records an actual equivalence when one is proved; tests, inspection and divergence
remain distinct statuses. The index covers only the three syntax types below.
-/

@[expose] public section

namespace Silmaril.Cerberus.Names.Consilience

open Silmaril.Cerberus.Consilience

/-- Status of this comparison, rather than of the whole Cerberus import. -/
inductive Status where
  | provedEquivalent
  | tested
  | inspected
  | divergent
  deriving DecidableEq, Repr

/-- Evidence for a comparison; a proof row carries the full equivalence. -/
inductive Evidence (generated hand : Type) where
  | provedEquivalent (equivalence : generated ≃ hand)
  | tested (report : String)
  | inspected (note : String)
  | divergent (note : String)

/-- The status justified by the row's evidence. -/
def Evidence.status {generated hand : Type} : Evidence generated hand → Status
  | .provedEquivalent _ => .provedEquivalent
  | .tested _ => .tested
  | .inspected _ => .inspected
  | .divergent _ => .divergent

/-- A comparison at separate source, backend and printer-patch pins. -/
structure Entry where
  lem : String
  hand : Lean.Name
  generated : Lean.Name
  source : String
  sourcePin : String
  backendPin : String
  printerPatchSha256 : String
  handType : Type
  generatedType : Type
  evidence : Evidence generatedType handType
  /-- Declaration containing the Equiv, or the full Evidence for another status. -/
  theoremName : Lean.Name

public meta section

open Lean Elab Term Meta

/-- Check declaration names against the types and evidence in an actual row. -/
def validateEntry (entry : Expr) : TermElabM Unit := do
  for (nameField, typeField, label) in [(``Entry.hand, ``Entry.handType, "hand"),
      (``Entry.generated, ``Entry.generatedType, "generated")] do
    let name : Name ← reduceEval (mkApp (mkConst nameField) entry)
    unless (← getEnv).contains name do
      throwError "consilience {label} declaration {privateToUserName name} does not exist"
    unless ← isDefEq (← mkConstWithFreshMVarLevels name) (mkApp (mkConst typeField) entry) do
      throwError "consilience {label} declaration {privateToUserName name} does not match its stored type"
  let name : Name ← reduceEval (mkApp (mkConst ``Entry.theoremName) entry)
  unless (← getEnv).contains name do
    throwError "consilience evidence declaration {privateToUserName name} does not exist"
  let evidence ← whnf (mkApp (mkConst ``Entry.evidence) entry)
  let expected := if evidence.isAppOf ``Evidence.provedEquivalent then
      evidence.getAppArgs.back!
    else evidence
  let declaration ← mkConstWithFreshMVarLevels name
  unless ← isDefEq (← inferType declaration) (← inferType expected) do
    throwError "consilience evidence declaration {privateToUserName name} has the wrong type"
  unless ← isDefEq declaration expected do
    throwError "consilience evidence declaration {privateToUserName name} does not match its stored evidence"

/-- Elaborate and validate every row before returning the kernel-checked list. -/
elab "consilience_entries%" rows:term : term => do
  let entries ← elabTermEnsuringType rows (mkApp (mkConst ``List [Level.one]) (mkConst ``Entry))
  synthesizeSyntheticMVarsNoPostponing
  let entries ← instantiateMVars entries
  let mut remaining ← whnf entries
  while remaining.isAppOf ``List.cons do
    let args := remaining.getAppArgs
    validateEntry args[1]!
    remaining ← whnf args[2]!
  unless remaining.isAppOf ``List.nil do
    throwError "consilience entries must reduce to a closed list"
  return entries

end

/-- One row for each type proved equivalent to the pinned Lem→Lean declaration. -/
def entries : List Entry := consilience_entries% [
  { lem := "IntegerType.integerBaseType", hand := ``IntegerBaseType,
    generated := ``Generated.LemLean.integerType.IntegerBaseType,
    source := "frontend/model/integerType.lem",
    sourcePin := Generated.sourcePin, backendPin := Generated.backendPin,
    printerPatchSha256 := Generated.printerPatchSha256,
    handType := IntegerBaseType,
    generatedType := Generated.LemLean.integerType.IntegerBaseType,
    evidence := .provedEquivalent integerBaseTypeEquiv,
    theoremName := ``integerBaseTypeEquiv },
  { lem := "Ctype.realFloatingType", hand := ``RealFloatingType,
    generated := ``Generated.LemLean.ctype.RealFloatingType,
    source := "frontend/model/ctype.lem",
    sourcePin := Generated.sourcePin, backendPin := Generated.backendPin,
    printerPatchSha256 := Generated.printerPatchSha256,
    handType := RealFloatingType,
    generatedType := Generated.LemLean.ctype.RealFloatingType,
    evidence := .provedEquivalent realFloatingTypeEquiv,
    theoremName := ``realFloatingTypeEquiv },
  { lem := "Core.binop", hand := ``Core.BinOp,
    generated := ``Generated.LemLean.core.Binop,
    source := "frontend/model/core.lem",
    sourcePin := Generated.sourcePin, backendPin := Generated.backendPin,
    printerPatchSha256 := Generated.printerPatchSha256,
    handType := Core.BinOp, generatedType := Generated.LemLean.core.Binop,
    evidence := .provedEquivalent binOpEquiv,
    theoremName := ``binOpEquiv }
]

/--
error: consilience hand declaration Silmaril.Cerberus.IntegerBaseType does not match its stored type
-/
#guard_msgs in
example : List Entry := consilience_entries% [
  { lem := "IntegerType.integerBaseType", hand := ``IntegerBaseType,
    generated := ``Generated.LemLean.integerType.IntegerBaseType,
    source := "frontend/model/integerType.lem",
    sourcePin := Generated.sourcePin, backendPin := Generated.backendPin,
    printerPatchSha256 := Generated.printerPatchSha256,
    handType := Nat, generatedType := Nat,
    evidence := .provedEquivalent (Equiv.refl Nat),
    theoremName := ``integerBaseTypeEquiv }]

/--
error: consilience generated declaration Silmaril.Cerberus.Consilience.Generated.LemLean.integerType.IntegerBaseType does not match its stored type
-/
#guard_msgs in
example : List Entry := consilience_entries% [
  { entries[0] with generatedType := Nat, evidence := .inspected "wrong type" }]

/--
error: consilience evidence declaration Silmaril.Cerberus.Consilience.binOpEquiv has the wrong type
-/
#guard_msgs in
example : List Entry := consilience_entries% [
  { entries[0] with theoremName := ``binOpEquiv }]

private def boolFlip : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

/-- error: consilience evidence declaration Silmaril.Cerberus.Names.Consilience.boolFlip does not match its stored evidence -/
#guard_msgs in
example : List Entry := consilience_entries% [
  { lem := "negative test", hand := ``Bool, generated := ``Bool,
    source := "test", sourcePin := "test", backendPin := "test",
    printerPatchSha256 := "test", handType := Bool, generatedType := Bool,
    evidence := .provedEquivalent (Equiv.refl Bool), theoremName := ``boolFlip }]

private def testedEvidence : Evidence
    Generated.LemLean.integerType.IntegerBaseType IntegerBaseType := .tested "report"

private def inspectedEvidence : Evidence
    Generated.LemLean.integerType.IntegerBaseType IntegerBaseType := .inspected "note"

private def divergentEvidence : Evidence
    Generated.LemLean.integerType.IntegerBaseType IntegerBaseType := .divergent "difference"

-- Every non-proof status accepts its named evidence and rejects stale evidence.
example : List Entry := consilience_entries% [
  { entries[0] with evidence := testedEvidence, theoremName := ``testedEvidence },
  { entries[0] with evidence := inspectedEvidence, theoremName := ``inspectedEvidence },
  { entries[0] with evidence := divergentEvidence, theoremName := ``divergentEvidence }]

/-- error: consilience evidence declaration Silmaril.Cerberus.Names.Consilience.testedEvidence does not match its stored evidence -/
#guard_msgs in
example : List Entry := consilience_entries% [
  { entries[0] with evidence := .tested "stale", theoremName := ``testedEvidence }]

/-- error: consilience evidence declaration Silmaril.Cerberus.Names.Consilience.inspectedEvidence does not match its stored evidence -/
#guard_msgs in
example : List Entry := consilience_entries% [
  { entries[0] with evidence := .inspected "stale", theoremName := ``inspectedEvidence }]

/-- error: consilience evidence declaration Silmaril.Cerberus.Names.Consilience.divergentEvidence does not match its stored evidence -/
#guard_msgs in
example : List Entry := consilience_entries% [
  { entries[0] with evidence := .divergent "stale", theoremName := ``divergentEvidence }]

/-- Every row names the hand-port declaration recorded in `Names`. -/
theorem entries_agree_with_names : ∀ entry ∈ entries,
    (Names.types.find? (·.cerberus == entry.lem)).map TypeName.silmaril = some entry.hand := by
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false]
  intro entry h
  rcases h with h | h | h <;> subst entry <;> rfl

/-- Every current row carries a proof, rather than a test or inspection claim. -/
theorem entries_proved_equivalent : ∀ entry ∈ entries,
    entry.evidence.status = .provedEquivalent := by
  decide +kernel

end Silmaril.Cerberus.Names.Consilience
