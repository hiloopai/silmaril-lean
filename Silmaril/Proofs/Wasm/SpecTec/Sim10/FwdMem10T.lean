module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdTable10T

/-!
# The load traps, `memory.size` and `memory.grow-fail` forward in `simEnv10T`

Round 3's leaves at `FwdAt10T`. The quantifiers other than the state are values, immediates and
memory arguments, typed in `simEnv10` and grown (`typedV10T`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress loadInt loadFloat setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst MemAddr)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV ValsOnly stateT evalExp_case evalExp_tup2
  evalExp_tup3 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one prems_nil)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memorySizeRule memGrowFailRule20 evalExp_constN
  evalExp_addNat20 evalExp_div8 evalExp_iPay evalExp_trapRhs cmpValues_gtOp_nat20 width_cases)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

theorem typedV_memarg10T (a : V1.MemArg) : TypedV (simEnv10T B) (.varT "memarg" []) (memargV a) :=
  typedV10T (typedV_memarg10 a)

theorem typedV_inn10T (t : IntType) :
    TypedV (simEnv10T B) (.varT "Inn" []) (valTypeV (.int t)) :=
  typedV10T (typedV_inn10 t)

theorem typedV_sx10T (s : Signedness) : TypedV (simEnv10T B) (.varT "sx" []) (Sim20.sxV s) :=
  typedV10T (typedV_sx10 s)

/-- The index of a `CONST I32 c; i` typed in `simEnv10T` is a `val_(I32)`. -/
theorem typedV_head32_10T {c : BitVec 32} {i : V1.Instr}
    (h : TypedV (simEnv10T B) adminsT (.list (adminsToV [value (.int .i32 c), .source i]))) :
    TypedV (simEnv10T B) valI32T (pctV c.toNat) :=
  typedV_valI32_of_const10T (by
    have h' := typedV_head10T h
    rwa [adminToV_value] at h')

/-- **`load-num-trap` fires forward** out of bounds, at a load of type `t` without packing. -/
theorem fires10_loadNumTrapT {s : Store H} {f : Frame} {c : BitVec 32} {t : V1.ValType}
    {ao : V1.MemArg} {a : MemAddr} {m : MemInst} {code : List Admin}
    (hcode : adminsToV code = [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]),
      .case "LOAD" (.tuple [valTypeV t, .opt none, memargV ao])])
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f))
    (hc : TypedV (simEnv10T B) valI32T (pctV c.toNat)) (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress c ao + t.width / 8) :
    Fires (simEnv10T B) "Step_read" 8
      (.tuple [configV hn ⟨s, f, code⟩, .list (adminsToV [.trap])]) := by
  let σ := loadNumScope (stateV hn s f) c t ao
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV t) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have hlhs : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z",
      .listE [Sim20.Whole.constIE, .caseE "LOAD" (.tupE [.varE "t", .optE none, .varE "ao"])]]))
      (configV hn ⟨s, f, code⟩) := by
    rw [configV_eq_cfgV10, hcode]
    exact evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
      (evalExp_case (evalExp_tup3 (Sim.evalExp_var ft) (evalExp_optE_none_iff.2 rfl)
        (Sim.evalExp_var fa)))))
  exact fires_of_ruleAtT (hasRuleAt10_loadNumTrap B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons ft (typedV_valtype10T t _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fa (typedV_memarg10T ao _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))
    (evalExp_tup2 hlhs evalExp_trapRhs)
    (prems_one (.ifPr (trapPrem10 fz fi fa rfl (evalExp_size10 t rfl (Sim.evalExp_var ft))
      (width_cases t) hm hlt)))

/-- **`load-pack-trap` fires forward** out of bounds. -/
theorem fires10_loadPackTrapT {s : Store H} {f : Frame} {c : BitVec 32} {t : IntType}
    {sz : V1.PackSize} {sx : Signedness} {ao : V1.MemArg} {a : MemAddr} {m : MemInst}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f))
    (hc : TypedV (simEnv10T B) valI32T (pctV c.toNat)) (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress c ao + sz.width / 8) :
    Fires (simEnv10T B) "Step_read" 10 (.tuple [configV hn ⟨s, f, [value (.int .i32 c),
      .source (.intLoad t (some (sz, sx)) ao)]⟩, .list (adminsToV [.trap])]) := by
  let σ := loadPackScope (stateV hn s f) c t sz sx ao
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (valTypeV (.int t)) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fsx : (VarEnv.empty.bindVals σ).findVal? "sx" = some (Sim20.sxV sx) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  exact fires_of_ruleAtT (hasRuleAt10_loadPackTrap B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fInn (typedV_inn10T t _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fn (typedV_n10T _ _ ⟨rfl, rfl, rfl⟩)
          (QuantsOk.cons fsx (typedV_sx10T sx _ ⟨rfl, rfl, rfl⟩)
            (QuantsOk.cons fa (typedV_memarg10T ao _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))))
    (evalExp_tup2 (evalExp_loadPackLhs10 fz fi fInn fn fsx fa) evalExp_trapRhs)
    (prems_one (.ifPr (trapPrem10 fz fi fa rfl (Sim.evalExp_var fn) (packWidth10_cases sz) hm
      hlt)))

/-- **`load` of an integer out of bounds, forward**: `load-num-trap` or `load-pack-trap`. -/
theorem fwdAt10T_intLoadTrap (s : Store H) (f : Frame) (t : IntType)
    (packed : Option (V1.PackSize × Signedness)) (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr)
    (m : MemInst) (hm : frameMemory s f = some (a, m))
    (hnone : loadInt t packed m.data (effectiveAddress c arg) = none) :
    FwdAt10T B hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩
      ⟨s, f, [.trap]⟩ := by
  have hlt := oob_of_loadInt_none hnone
  rcases packed with _ | ⟨sz, sx⟩
  · refine fwdAt10T_of_sread fun hz hcode => sread10T_of_fires (fires10_loadNumTrapT (t := .int t)
      ?_ hz (typedV_head32_10T hcode) hm hlt)
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  · exact fwdAt10T_of_sread fun hz hcode =>
      sread10T_of_fires (fires10_loadPackTrapT hz (typedV_head32_10T hcode) hm hlt)

/-- **`load` of a float out of bounds, forward**: `load-num-trap`. -/
theorem fwdAt10T_floatLoadTrap (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg)
    (c : BitVec 32) (a : MemAddr) (m : MemInst) (hm : frameMemory s f = some (a, m))
    (hnone : loadFloat t m.data (effectiveAddress c arg) = none) :
    FwdAt10T B hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10T_of_sread fun hz hcode => sread10T_of_fires (fires10_loadNumTrapT (t := .float t)
    ?_ hz (typedV_head32_10T hcode) hm (oob_of_loadFloat_none hnone))
  rw [adminsToV_map10, List.map_cons, adminToV_value]
  rfl

/-- **`memory.size` forward**, at a page-aligned memory of fewer than `2^32` pages. -/
theorem fwdAt10T_memorySize (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst)
    (hm : frameMemory s f = some (a, m)) (hal : MemAligned10 m) :
    FwdAt10T B hn ⟨s, f, [.source .memorySize]⟩
      ⟨s, f, [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩ := by
  refine fwdAt10T_of_sread fun hz _ => sread10T_of_fires (k := 12) ?_
  set k := Execution.Memory.size m.data with hk
  have hkm : k * 64 * 1024 = m.data.size := by
    have h₁ := Nat.div_add_mod m.data.size Execution.Memory.pageSize
    have h₂ : m.data.size % Execution.Memory.pageSize = 0 := hal.1
    simp only [Execution.Memory.size, Execution.Memory.pageSize] at hk h₁ h₂ ⊢
    omega
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN k))]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN k)) := rfl
  have hrhs := adminsToV_memorySize (m := m) hkm hal.2
  erw [hrhs]
  exact fires_of_ruleAtT (hasRuleAt10_memorySize B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fn (typedV_n10T _ _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (Sim.evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))))
      (evalExp_list1 (evalExp_constN fn)))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_pages10 fn rfl,
      evalExp_memLen10 rfl fz hm, cmpValues_eq_true_iff.2 (by rw [hkm])⟩)))

/-- **`memory.grow` failing, forward**: `Step/memory.grow-fail`, which has no premise. -/
theorem fwdAt10T_memGrowFail (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst) (c : BitVec 32)
    (hm : frameMemory s f = some (a, m)) :
    FwdAt10T B hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
      ⟨setMemory s a {m with data := m.data}, f, [value (.int .i32 (-1))]⟩ := by
  rw [setMemory_self (frameMemory_some hm).2]
  intro hz _ _ _
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN c.toNat))]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN c.toNat)) := rfl
  have hlhs : configV hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list [.case "CONST" (.tuple [caseNilV "I32",
        pctV c.toNat]), caseNilV "MEMORY.GROW"]]) := by
    rw [configV_eq_cfgV10, adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) Sim20.Whole.growFailRhs
      (configV hn ⟨s, f, [value ⟨.int .i32, -1⟩]⟩) :=
    evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup2
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_minusOne10 rfl) evalExps_nil,
        rfl⟩))))))
  refine sstepB10T_of_fires' (k := 12) ?_
  rw [hlhs]
  exact fires_of_ruleAtT (hasRuleAt10_memGrowFail B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fn (typedV_n10T _ _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (evalExp_case (evalExp_tupE_iff.2
        ⟨_, evalExps_cons (Sim.evalExp_var fn) evalExps_nil, rfl⟩))))
      Sim20.Pure.evalExp_caseNil))) he)
    prems_nil


end Silmaril.Wasm.SpecTec.Sim10.Whole
