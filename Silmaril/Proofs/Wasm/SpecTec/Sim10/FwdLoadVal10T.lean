module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdGrow10T

/-!
# The successful loads forward in `simEnv10T`

Round 4's `load-num-val` and `load-pack-val` leaves at `FwdAt10T` and `bytesB10`. The value
quantifier is typed in `simEnv10` (`hasTyp_valNum10`, `hasTyp_iN_of_uN10`) and grown.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress loadInt loadFloat)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst MemAddr)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV stateT evalExp_case evalExp_tup2
  evalExp_tup3 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one)
open Silmaril.Wasm.SpecTec.Sim20.Whole (constIE mem0E div8E iPay offE evalExp_addNat20 evalExp_div8
  evalExp_iPay evalExp_eqTrue width_cases)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}


/-- **`load-num-val` fires forward** at `bytesB10`, at a V1 read of the value `v`. -/
theorem fires10_loadNumValT {P : Profile} {s : Store H} {f : Frame} {c : BitVec 32}
    {ao : V1.MemArg} {a : MemAddr} {m : MemInst} {v : Execution.Runtime.Value} {code : List Admin}
    (hcode : adminsToV code = [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]),
      .case "LOAD" (.tuple [valTypeV v.type, .opt none, memargV ao])])
    (hz : TypedV (simEnv10T (bytesB10 P)) stateT (stateV hn s f))
    (hc : TypedV (simEnv10T (bytesB10 P)) valI32T (pctV c.toNat))
    (hm : frameMemory s f = some (a, m))
    (hb : Execution.Memory.readBytes m.data (effectiveAddress c ao) (v.type.width / 8) =
      some (Execution.Memory.encodeLE (v.type.width / 8) v.bits.toNat)) :
    Fires (simEnv10T (bytesB10 P)) "Step_read" 9
      (.tuple [configV hn ⟨s, f, code⟩, .list (adminsToV [value v])]) := by
  let σ := loadNumValScope (stateV hn s f) c ao v
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v.type) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV v) := rfl
  have hlhs : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE
      [.varE "z", .listE [constIE, .caseE "LOAD" (.tupE [.varE "t", .optE none, .varE "ao"])]]))
      (configV hn ⟨s, f, code⟩) := by
    rw [configV_eq_cfgV10, hcode]
    exact evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
      (evalExp_case (evalExp_tup3 (Sim.evalExp_var ft) (evalExp_optE_none_iff.2 rfl)
        (Sim.evalExp_var fa)))))
  have hrhs : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "t", .varE "c"])]) (.list (adminsToV [value v])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact evalExp_list1 (evalExp_case (evalExp_tup2 (Sim.evalExp_var ft) (Sim.evalExp_var fc)))
  have hprem : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "bytes_" [.expA (.varE "t"), .expA (.varE "c")])
        (loadSliceE10 sizeTE)) (.bool true) :=
    evalExp_eqTrue (evalExp_bytesCall10 rfl ft fc) (evalExp_loadSlice10 fz fi fa rfl
      (evalExp_size10 v.type rfl (Sim.evalExp_var ft)) (width_cases v.type) hm hb)
  exact fires_of_ruleAtT (hasRuleAt10_loadNumVal' _) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons ft (typedV_valtype10T v.type _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fa (typedV_memarg10T ao _ ⟨rfl, rfl, rfl⟩)
          (QuantsOk.cons fc (StoreAgree.hasTypT <| hasTyp_valNum10 v (Sim.evalExp_var ft)) QuantsOk.nil)))))
    (evalExp_tup2 hlhs hrhs) (prems_one (.ifPr hprem))

/-- **`load-pack-val` fires forward** at `bytesB10`, at a V1 read of the narrow value `x`. -/
theorem fires10_loadPackValT {P : Profile} {s : Store H} {f : Frame} {c : BitVec 32}
    {t : IntType} {sz : V1.PackSize} {sx : Signedness} {ao : V1.MemArg} {a : MemAddr}
    {m : MemInst} {x : BitVec sz.width}
    (hz : TypedV (simEnv10T (bytesB10 P)) stateT (stateV hn s f))
    (hc : TypedV (simEnv10T (bytesB10 P)) valI32T (pctV c.toNat))
    (hm : frameMemory s f = some (a, m))
    (hb : Execution.Memory.readBytes m.data (effectiveAddress c ao) (sz.width / 8) =
      some (Execution.Memory.encodeLE (sz.width / 8) x.toNat)) :
    Fires (simEnv10T (bytesB10 P)) "Step_read" 11 (.tuple [configV hn ⟨s, f, [value (.int .i32 c),
      .source (.intLoad t (some (sz, sx)) ao)]⟩,
      .list (adminsToV [value ⟨.int t, extPack10 t sx x⟩])]) := by
  let σ := loadPackValScope (stateV hn s f) c t sz sx ao x.toNat
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (valTypeV (.int t)) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fsx : (VarEnv.empty.bindVals σ).findVal? "sx" = some (Sim20.sxV sx) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) := rfl
  have hrhs : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [innE10, extendE10])])
      (.list (adminsToV [value ⟨.int t, extPack10 t sx x⟩])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (Sim.evalExp_var fInn))
      (evalExp_extend10 rfl rfl fInn fn fsx fc)))
  have hprem : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "ibytes_" [.expA (.varE "n"), .expA (.varE "c")])
        (loadSliceE10 (.varE "n"))) (.bool true) :=
    evalExp_eqTrue (evalExp_ibytesCall10 rfl fn fc) (evalExp_loadSlice10 fz fi fa rfl
      (Sim.evalExp_var fn) (packWidth10_cases sz) hm hb)
  exact fires_of_ruleAtT (hasRuleAt10_loadPackVal' _) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fInn (typedV_inn10T t _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fn (typedV_n10T _ _ ⟨rfl, rfl, rfl⟩)
          (QuantsOk.cons fsx (typedV_sx10T sx _ ⟨rfl, rfl, rfl⟩)
            (QuantsOk.cons fa (typedV_memarg10T ao _ ⟨rfl, rfl, rfl⟩)
              (QuantsOk.cons fc (StoreAgree.hasTypT <| hasTyp_iN_of_uN10 (Sim.evalExp_var fn) x.isLt)
                QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_loadPackLhs10 fz fi fInn fn fsx fa) hrhs) (prems_one (.ifPr hprem))

/-- **A successful integer load, forward**, at `bytesB10`: `load-num-val` or `load-pack-val`. -/
theorem fwdAt10T_intLoad_bytesB10 {P : Profile} (s : Store H) (f : Frame) (t : IntType)
    (packed : Option (V1.PackSize × Signedness)) (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr)
    (m : MemInst) (v : Execution.Runtime.Value) (hm : frameMemory s f = some (a, m))
    (hv : loadInt t packed m.data (effectiveAddress c arg) = some v) :
    FwdAt10T (bytesB10 P) hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩
      ⟨s, f, [value v]⟩ := by
  rcases packed with _ | ⟨sz, sx⟩
  · obtain ⟨b, rfl, hb⟩ := loadInt_none_some hv
    refine fwdAt10T_of_sread fun hz hcode => sread10T_of_fires (fires10_loadNumValT (v := ⟨.int t, b⟩)
      ?_ hz (typedV_head32_10T hcode) hm hb)
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  · obtain ⟨x, rfl, hb⟩ := loadPack_some hv
    exact fwdAt10T_of_sread fun hz hcode =>
      sread10T_of_fires (fires10_loadPackValT hz (typedV_head32_10T hcode) hm hb)

/-- **A successful float load, forward**, at `bytesB10`: `load-num-val`. -/
theorem fwdAt10T_floatLoad_bytesB10 {P : Profile} (s : Store H) (f : Frame) (t : FloatType)
    (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value)
    (hm : frameMemory s f = some (a, m)) (hv : loadFloat t m.data (effectiveAddress c arg) = some v) :
    FwdAt10T (bytesB10 P) hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩
      ⟨s, f, [value v]⟩ := by
  obtain ⟨b, rfl, hb⟩ := loadFloat_some hv
  refine fwdAt10T_of_sread fun hz hcode => sread10T_of_fires (fires10_loadNumValT (v := ⟨.float t, b⟩)
    ?_ hz (typedV_head32_10T hcode) hm hb)
  rw [adminsToV_map10, List.map_cons, adminToV_value]
  rfl


end Silmaril.Wasm.SpecTec.Sim10.Whole
