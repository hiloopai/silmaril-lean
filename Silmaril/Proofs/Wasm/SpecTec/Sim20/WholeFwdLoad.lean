module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCallAddr

/-!
# The unpacked loads forward (`Step_read` 22 and 23)

2.0's

  `z; (CONST I32 i) (LOAD nt ao) ~> TRAP`, if `i + ao.OFFSET + $size(nt)/8 > |$mem(z, 0).BYTES|`
  `z; (CONST I32 i) (LOAD nt ao) ~> (CONST nt c)`,
    if `$nbytes_(nt, c) = $mem(z, 0).BYTES[i + ao.OFFSET : $size(nt)/8]`

The value `c` is bound only by the second premise. Forward it is bound to the value V2 reads, and
the premise holds at builtins that answer `$nbytes_` as V2 does (`NBytes20`, so at `storeB`): the
slice of the encoded memory is the image of V2's `readBytes` (`Sim.Memory.slice?_bytesL`). No
inverse (`$inv_nbytes_`) is needed, because the rule does not compute `c`.

* `fires_loadNumTrap`, `fires_loadNumVal` (integer and float);
* `LoadFwd20`, `fwdBase20_load`, and **`Task.wholeStepFwd20D`** (proved): at `storeB`, the
  nested fragment `FwdStep20C` plus the four unpacked load steps is matched forward.

The packed loads (`load-pack-*`, `$ext` of `$ibytes_`) are not done here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The rules -/

/-- A `LOAD` of a number type without a pack, as V2 encodes it. -/
def LoadNumV (t : NumType) (ao : V2.MemArg) (li : V2.Instr) : Prop :=
  instrToV li = .case "LOAD" (.tuple [numTypeV t, .opt none, memargV ao])

theorem loadNumV_int (t : IntType) (ao : V2.MemArg) : LoadNumV (.int t) ao (.intLoad t none ao) :=
  rfl

theorem loadNumV_float (t : FloatType) (ao : V2.MemArg) : LoadNumV (.float t) ao (.floatLoad t ao) :=
  rfl

/-- `z; (CONST I32 i) (LOAD nt ao)`. -/
abbrev loadLhsE : Exp := .caseE "%;%" (.tupE [.varE "z", .listE [constIE,
  .caseE "LOAD" (.tupE [.varE "nt", .optE none, .varE "ao"])]])

/-- `$mem(z, 0).BYTES[i + ao.OFFSET : $size(nt)/8]`. -/
abbrev loadSliceE : Exp := .sliceE (.dotE mem0E "BYTES") (.binE .addOp (.numT .natT) iPay offE)
  (div8E sizeNtE)

/-- `Step_read/load-num-trap`, rule 22 (transcribed). -/
def loadNumTrapRule : Rule :=
  .ruleD "load-num-trap" [.expP "z" (.varT "state" []),
      .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "nt" (.varT "numtype" []),
      .expP "ao" (.varT "memarg" [])] "%~>%" (.tupE [loadLhsE, trapRhs])
    [.ifPr (.cmpE .gtOp (.numT .natT) (addrE (div8E sizeNtE)) memLenE)]

/-- `Step_read/load-num-val`, rule 23 (transcribed). -/
def loadNumValRule : Rule :=
  .ruleD "load-num-val" [.expP "z" (.varT "state" []),
      .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "nt" (.varT "numtype" []),
      .expP "ao" (.varT "memarg" []), .expP "c" (.varT "num_" [.expA (.varE "nt")])] "%~>%"
    (.tupE [loadLhsE, .listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c"])]])
    [.ifPr (.cmpE .eqOp .boolT (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")])
      loadSliceE)]

theorem hasRuleAt_loadNumTrap : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 22 loadNumTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_loadNumVal : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 23 loadNumValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The left-hand side, evaluated. -/
theorem evalExp_loadLhs {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32} {t : NumType}
    {ao : V2.MemArg} {li : V2.Instr} (hL : LoadNumV t ao li)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fnt : ρ.findVal? "nt" = some (numTypeV t)) (fa : ρ.findVal? "ao" = some (memargV ao)) :
    EvalExp (simEnv20 B) ρ loadLhsE (configV hn ⟨s, f, [constI32 i, .plain li]⟩) := by
  have h₂ : EvalExp (simEnv20 B) ρ (.caseE "LOAD" (.tupE [.varE "nt", .optE none, .varE "ao"]))
      (instrToV li) := by
    rw [hL]
    exact evalExp_case (Sim.evalExp_tup3 (evalExp_var fnt) (evalExp_optE_none_iff.2 rfl)
      (evalExp_var fa))
  exact evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constIE fi) (evalExps_cons h₂ evalExps_nil), rfl⟩))

/-- The memory of the frame, split. -/
theorem mem?_some {s : Store H} {f : Frame} {mi : MemInst}
    (h : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) :
    ∃ a, f.module.memAddr? memIdx0 = some a ∧ s.memInst? a = some mi := by
  cases ha : f.module.memAddr? memIdx0 with
  | none => simp [State.mem?, ha] at h
  | some a => exact ⟨a, rfl, by simpa [State.mem?, ha] using h⟩

/-! ## The rules fire -/

/-- **`Step_read/load-num-trap` fires forward** at the image of V2's `loadIntTrap` and
`loadFloatTrap`, at every builtins, from a typed state. -/
theorem fires_loadNumTrap {s : Store H} {f : Frame} {t : NumType} {ao : V2.MemArg}
    {li : V2.Instr} (hL : LoadNumV t ao li) {i : BitVec 32} {ad : MemAddr} {mi : MemInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
    Fires (simEnv20 B) "Step_read" 22 (.tuple [configV hn ⟨s, f, [constI32 i, .plain li]⟩,
      .list (adminsToV [.trap])]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("nt", numTypeV t), ("ao", memargV ao)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match loadNumTrapRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (Pure.typedV_numtype20 B t _ hρ)
        (QuantsOk.cons rfl (typedV_memarg20 ao _ hρ) QuantsOk.nil)))
  refine Pure.fires_of_ruleAt hasRuleAt_loadNumTrap σ hq
    (evalExp_tup2 (evalExp_loadLhs hL rfl rfl rfl rfl) evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl rfl rfl rfl (evalExp_sizeNt rfl rfl) (width_cases t) ha hm hlt)

/-- The slice of the frame's memory, at a read V2 makes. -/
theorem evalExp_loadSlice {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32} {t : NumType}
    {ao : V2.MemArg} {ad : MemAddr} {mi : MemInst} {r : Silmaril.Wasm.Execution.Memory.Bytes}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fnt : ρ.findVal? "nt" = some (numTypeV t)) (fa : ρ.findVal? "ao" = some (memargV ao))
    (hρ : ρ.findDef? "mem" = none) (hs : ρ.findDef? "size" = none)
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) =
      some r) :
    EvalExp (simEnv20 B) ρ loadSliceE (bytesV r) := by
  have hx : EvalExp (simEnv20 B) ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (idxV memIdx0) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)
  have hmem : EvalExp (simEnv20 B) ρ (.dotE mem0E "BYTES") (.list (Sim.Memory.bytesL mi.bytes)) := by
    rw [← bytesV_eq_bytesL]
    exact evalExp_dotE_iff.2 ⟨memInstV mi, evalExp_mem20 hρ (evalExp_var fz) hx
      (by simpa [ModuleInst.memAddr?] using ha) (by simpa [Store.memInst?] using hm), rfl⟩
  have hsl : (Value.list (Sim.Memory.bytesL mi.bytes)).slice? (effAddr i.toNat ao) (t.width / 8) =
      some (bytesV r) := by
    rw [Sim.Memory.slice?_bytesL, hb, bytesV_eq_bytesL]
    rfl
  exact evalExp_sliceE_iff.2 ⟨_, _, _, hmem, evalExp_addNat20 (evalExp_iPay fi) (evalExp_off fa),
    evalExp_div8 (evalExp_sizeNt hs fnt) (width_cases t), hsl⟩

/-- **`Step_read/load-num-val` fires forward** at the image of V2's `loadIntVal` and
`loadFloatVal`, at builtins answering `$nbytes_` as V2 does, from a typed state. -/
theorem fires_loadNumVal (hN : NBytes20 B) {s : Store H} {f : Frame} {t : NumType}
    {ao : V2.MemArg} {li : V2.Instr} (hL : LoadNumV t ao li) {i : BitVec 32} {ad : MemAddr}
    {mi : MemInst} {c : BitVec t.width} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) =
      some (nbytes t c)) :
    Fires (simEnv20 B) "Step_read" 23 (.tuple [configV hn ⟨s, f, [constI32 i, .plain li]⟩,
      .list (adminsToV [(Val.num ⟨t, c⟩).toAdmin])]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("nt", numTypeV t), ("ao", memargV ao), ("c", numV ⟨t, c⟩)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (numTypeV t) := rfl
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match loadNumValRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fnt (Pure.typedV_numtype20 B t _ hρ)
        (QuantsOk.cons rfl (typedV_memarg20 ao _ hρ)
          (QuantsOk.cons rfl (hasTyp_numAt20 t c (evalExp_var fnt)) QuantsOk.nil))))
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c"])])
      (.list (adminsToV [(Val.num ⟨t, c⟩).toAdmin])) := by
    show EvalExp _ _ _ (.list [adminToV (Val.num ⟨t, c⟩).toAdmin])
    rw [Pure.adminToV_num]
    exact evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fnt) (evalExp_var rfl)))
  have eN : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")]) (bytesV (nbytes t c)) :=
    evalExp_builtin20 ⟨_, _, rfl⟩ rfl (evalArgs_cons (evalExp_var fnt) (evalArgs_cons
      (evalExp_var rfl) evalArgs_nil)) (hN t c)
  refine Pure.fires_of_ruleAt hasRuleAt_loadNumVal σ hq
    (evalExp_tup2 (evalExp_loadLhs hL rfl rfl fnt rfl) hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue eN (evalExp_loadSlice rfl rfl fnt rfl rfl rfl ha hm hb))


/-! ## The fragment -/

/-- **V2's four unpacked load steps**, with V2's premises. -/
inductive LoadFwd20 : Config H → Config H → Prop where
  | intTrap {s : Store H} {f : Frame} {t : IntType} {ao : V2.MemArg} {i : BitVec 32}
      {mi : MemInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
      LoadFwd20 ⟨s, f, [constI32 i, .plain (.intLoad t none ao)]⟩ ⟨s, f, [.trap]⟩
  | intVal {s : Store H} {f : Frame} {t : IntType} {ao : V2.MemArg} {i : BitVec 32}
      {mi : MemInst} {c : BitVec t.width} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) =
        some (nbytes (.int t) c)) :
      LoadFwd20 ⟨s, f, [constI32 i, .plain (.intLoad t none ao)]⟩ ⟨s, f, [.plain (.intConst t c)]⟩
  | floatTrap {s : Store H} {f : Frame} {t : FloatType} {ao : V2.MemArg} {i : BitVec 32}
      {mi : MemInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
      LoadFwd20 ⟨s, f, [constI32 i, .plain (.floatLoad t ao)]⟩ ⟨s, f, [.trap]⟩
  | floatVal {s : Store H} {f : Frame} {t : FloatType} {ao : V2.MemArg} {i : BitVec 32}
      {mi : MemInst} {c : BitVec t.width} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) =
        some (fbytes t c)) :
      LoadFwd20 ⟨s, f, [constI32 i, .plain (.floatLoad t ao)]⟩
        ⟨s, f, [.plain (.floatConst t c)]⟩

theorem LoadFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : LoadFwd20 c c') : Step P host c c' := by
  cases h with
  | intTrap hm h => exact .read (.loadIntTrap hm h)
  | intVal hm hb => exact .read (.loadIntVal hm hb)
  | floatTrap hm h => exact .read (.loadFloatTrap hm h)
  | floatVal hm hb => exact .read (.loadFloatVal hm hb)

/-- **Subject reduction for the loads**: a trap or a value. -/
theorem typed20_succ_load20 {c c' : Config H} (hc : Typed20 (simEnv20 B) hn c)
    (h : LoadFwd20 c c') : Typed20 (simEnv20 B) hn c' := by
  obtain ⟨hz, -⟩ := typed20_iff.1 hc
  cases h with
  | intTrap _ _ | floatTrap _ _ => exact typed20_iff.2 ⟨hz, typedV_admins_trap20⟩
  | @intVal _ _ t _ _ _ c _ _ => exact typed20_iff.2 ⟨hz, typedV_admins_val20 (.num ⟨.int t, c⟩)⟩
  | @floatVal _ _ t _ _ _ c _ _ =>
    exact typed20_iff.2 ⟨hz, typedV_admins_val20 (.num ⟨.float t, c⟩)⟩

/-- **The unpacked loads are a base**, at builtins answering `$nbytes_`. -/
theorem fwdBase20_load {W : Store H → Prop} (hN : NBytes20 B) :
    FwdBase20 B hn W (LoadFwd20 (H := H)) where
  sr c c' hc h := typed20_succ_load20 hc h
  fwd c c' hc _ h := by
    have hc' := typed20_succ_load20 hc h
    have hz := typedV_state_of_typed20 hc
    cases h with
    | intTrap hm hlt =>
      obtain ⟨ad, ha, hm'⟩ := mem?_some hm
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_loadNumTrap (loadNumV_int _ _) hz ha hm' hlt)))
    | intVal hm hb =>
      obtain ⟨ad, ha, hm'⟩ := mem?_some hm
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_loadNumVal hN (loadNumV_int _ _) hz ha hm' hb)))
    | floatTrap hm hlt =>
      obtain ⟨ad, ha, hm'⟩ := mem?_some hm
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_loadNumTrap (loadNumV_float _ _) hz ha hm' hlt)))
    | floatVal hm hb =>
      obtain ⟨ad, ha, hm'⟩ := mem?_some hm
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_loadNumVal hN (loadNumV_float _ _) hz ha hm' hb)))

/-! ## The widened forward statement -/

/-- **The base at `storeB`, with the unpacked loads.** -/
inductive FwdStep20D (P : Profile) : Config H → Config H → Prop where
  | fwd {c c' : Config H} (h : FwdStep20C P c c') : FwdStep20D P c c'
  | load {c c' : Config H} (h : LoadFwd20 c c') : FwdStep20D P c c'

theorem FwdStep20D.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20D P c c') : Step P host c c' := by
  cases h with
  | fwd h => exact h.step
  | load h => exact h.step

/-- The widened base is a base at `storeB`. -/
theorem fwdBase20_fwdD (P : Profile) :
    FwdBase20 (storeB P) hn WholePages (FwdStep20D (H := H) P) where
  sr c c' hc h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdC P).sr c c' hc h
    | load h => exact (fwdBase20_load (W := WholePages) (nbytes20_storeB P)).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdC P).fwd c c' hc hw h
    | load h => exact (fwdBase20_load (nbytes20_storeB P)).fwd c c' hc hw h

/-- **The forward 2.0 half with the unpacked loads** (stated and proved): at `storeB`, every
step of `Nest20 (FwdStep20D P)` from a configuration with typed image and whole pages is a step of
the corrected script between the images, with a typed successor image. -/
def Task.wholeStepFwd20D : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Profile) (c c' : Config H),
    Typed20 (simEnv20 (storeB P)) hn c → WholePages c.store → Nest20 (FwdStep20D P) c c' →
    Typed20 (simEnv20 (storeB P)) hn c' ∧
      SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20D` is proved**, at every profile. -/
theorem wholeStepFwd20D : Task.wholeStepFwd20D :=
  fun _ _ P _ _ hc hw h => fwd_nest20 (fwdBase20_fwdD P) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
