module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnLoad

/-!
# The six scalar stores in `simEnv20T`, from a state typed there

`Step` 11–14 of the original script (rules 12–15 of `simEnv20T`), restated 's
`fires_storeNumTrap`, `fires_storePackTrap`, `fires_storePackVal`, `fires_storeNumVal` with
`firesT_step_of20`: the state typed in `simEnv20T`, the other quantifiers moved 's
typings (`quantsOkT_z`), the conclusion and premise evaluated 's lemmas in `simEnv20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.State (iterVar)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

/-- **`Step/store-num-trap` fires in `simEnv20T`** at the image of V2's `storeIntTrap` and
`storeFloatTrap`, at every builtins, from a state typed there. -/
theorem firesT_storeNumTrap {s : Store H} {f : Frame} {t : NumType} {x : BitVec t.width}
    {ao : V2.MemArg} {st : V2.Instr} (hS : StoreNumV t ao st) {i : BitVec 32} {ad : MemAddr}
    {mi : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
    Fires (simEnv20T B) "Step" 12 (.tuple [
      configV hn ⟨s, f, [constI32 i, (Val.num ⟨t, x⟩).toAdmin, .plain st]⟩,
      configV hn ⟨s, f, [.trap]⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("nt", numTypeV t), ("c", numV ⟨t, x⟩), ("ao", memargV ao)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (numTypeV t) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV ⟨t, x⟩) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      (match storeNumTrapRule with | .ruleD _ qs _ _ _ => qs) := quantsOkT_z (B := B) hρ fz hz (by decide)
      (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fnt (Pure.typedV_numtype20 B t _ hρ)
        (QuantsOk.cons fc (hasTyp_numAt20 t x (evalExp_var fnt))
          (QuantsOk.cons fa (typedV_memarg20 ao _ hρ) QuantsOk.nil))))
  refine firesT_step_of20 (D := fun _ _ _ _ => True) (els := True) (by decide) hasRuleAt_storeNumTrap rfl σ hq
    (evalExp_tup2 (evalExp_storeNumLhs hS fz fi fnt fc fa) (evalExp_zTrap fz)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl fz fi fa (evalExp_sizeNt rfl fnt) (width_cases t) ha hm hlt)

/-- **`Step/store-pack-trap` fires in `simEnv20T`** at the image of V2's `storePackTrap`, at every
builtins, from a state typed there. -/
theorem firesT_storePackTrap {s : Store H} {f : Frame} {t : IntType} {x : BitVec t.width}
    {sz : PackSize} {ao : V2.MemArg} {i : BitVec 32} {ad : MemAddr} {mi : MemInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
    Fires (simEnv20T B) "Step" 14 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.intConst t x), .plain (.intStore t (some sz) ao)]⟩,
      configV hn ⟨s, f, [.trap]⟩]) := by
  let σ := storePackScope (hn := hn) s f i t x sz ao
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (numTypeV (.int t)) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      (match storePackTrapRule with | .ruleD _ qs _ _ _ => qs) := quantsOkT_z (B := B) hρ fz hz (by decide)
      (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fInn (typedV_inn20 t _ hρ)
        (QuantsOk.cons fc (Pure.hasTyp_num_int20 x (evalExp_subE_iff.2 (evalExp_var fInn)))
          (QuantsOk.cons fn (typedV_n20 _ _ hρ)
            (QuantsOk.cons fa (typedV_memarg20 ao _ hρ) QuantsOk.nil)))))
  refine firesT_step_of20 (D := fun _ _ _ _ => True) (els := True) (by decide) hasRuleAt_storePackTrap rfl σ hq
    (evalExp_tup2 (evalExp_storePackLhs fz fi fInn fc fn fa) (evalExp_zTrap fz)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl fz fi fa (evalExp_var fn) (packWidth_cases sz) ha hm hlt)

/-- **`Step/store-pack-val` fires in `simEnv20T`** at the image of V2's `storePackVal`, at builtins
answering `$ibytes_` and the float primitives, from a state typed there. -/
theorem firesT_storePackVal {P : Profile} (hF : Sim.Floats.FloatB P B) (hL : LaneCalls20 B)
    {s : Store H} {f : Frame} {t : IntType} {x : BitVec t.width} {sz : PackSize}
    {ao : V2.MemArg} {i : BitVec 32} {ad : MemAddr} {mi mi' : MemInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
      (ibytes sz.width (x.setWidth sz.width)) = some mi') :
    Fires (simEnv20T B) "Step" 15 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.intConst t x), .plain (.intStore t (some sz) ao)]⟩,
      configV hn ⟨s.setMemInst ad mi', f, []⟩]) := by
  let w := ibytes sz.width (x.setWidth sz.width)
  let σ := storePackScope (hn := hn) s f i t x sz ao ++ [("b*", bytesV w)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (numTypeV (.int t)) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fb : (VarEnv.empty.bindVals σ).findVal? "b*" = some (bytesV w) := rfl
  have hsz : w.size = sz.width / 8 := ibytes_size _ _
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      (match storePackValRule with | .ruleD _ qs _ _ _ => qs) := quantsOkT_z (B := B) hρ fz hz (by decide)
      (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fInn (typedV_inn20 t _ hρ)
        (QuantsOk.cons fc (Pure.hasTyp_num_int20 x (evalExp_subE_iff.2 (evalExp_var fInn)))
          (QuantsOk.cons fn (typedV_n20 _ _ hρ) (QuantsOk.cons fa (typedV_memarg20 ao _ hρ)
            (QuantsOk.cons fb (typedV_bytes20 w _ hρ) QuantsOk.nil))))))
  have hb : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (iterVar "b" "b*") (bytesV w) :=
    Equiv.Execution.evalExp_iterPat (by decide) fb
  have hmems : f.module.mems[memIdx0.toNat]? = some ad := by
    simpa [ModuleInst.memAddr?] using ha
  have hmi : s.mems[ad]? = some mi := by simpa [Store.memInst?] using hm
  have hw' : mi.writeBytes? (i.toNat + ao.offset.val) w.size w = some mi' := by
    rw [hsz]; exact hw
  have hwm : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)])),
        .expA (.binE .addOp (.numT .natT) iPay offE), .expA (div8E (.varE "n")),
        .expA (iterVar "b" "b*")]) (stateV hn (s.setMemInst ad mi') f) :=
    evalExp_withMem20 (x := memIdx0) rfl (evalExp_var fz)
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil,
        rfl⟩))
      (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off fa))
      (by rw [hsz]; exact evalExp_div8 (evalExp_var fn) (packWidth_cases sz)) hb hmems hmi hw'
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E (.varE "n")), .expA (iterVar "b" "b*")], .listE []]))
      (configV hn ⟨s.setMemInst ad mi', f, []⟩) :=
    evalExp_case (evalExp_tup2 hwm (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))
  refine firesT_step_of20 (D := fun _ _ _ _ => True) (els := True) (by decide) hasRuleAt_storePackVal rfl σ hq
    (evalExp_tup2 (evalExp_storePackLhs fz fi fInn fc fn fa) hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue hb (evalExp_packBytes hF hL fInn fc fn rfl rfl rfl))

/-- **`Step/store-num-val` fires in `simEnv20T`** at the image of V2's `storeIntVal` and
`storeFloatVal`, at builtins answering `$nbytes_` as V2 does, from a state typed there. -/
theorem firesT_storeNumVal (hN : NBytes20 B) {s : Store H} {f : Frame} {t : NumType}
    {x : BitVec t.width} {ao : V2.MemArg} {st : V2.Instr} (hS : StoreNumV t ao st) {i : BitVec 32}
    {ad : MemAddr} {mi mi' : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (t.width / 8) (nbytes t x) = some mi') :
    Fires (simEnv20T B) "Step" 13 (.tuple [
      configV hn ⟨s, f, [constI32 i, (Val.num ⟨t, x⟩).toAdmin, .plain st]⟩,
      configV hn ⟨s.setMemInst ad mi', f, []⟩]) := by
  let w := nbytes t x
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("nt", numTypeV t), ("c", numV ⟨t, x⟩), ("ao", memargV ao), ("b*", bytesV w)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (numTypeV t) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV ⟨t, x⟩) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fb : (VarEnv.empty.bindVals σ).findVal? "b*" = some (bytesV w) := rfl
  have hsz : w.size = t.width / 8 := ibytes_size _ _
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      (match storeNumValRule with | .ruleD _ qs _ _ _ => qs) := quantsOkT_z (B := B) hρ fz hz (by decide)
      (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fnt (Pure.typedV_numtype20 B t _ hρ)
        (QuantsOk.cons fc (hasTyp_numAt20 t x (evalExp_var fnt))
          (QuantsOk.cons fa (typedV_memarg20 ao _ hρ)
            (QuantsOk.cons fb (typedV_bytes20 w _ hρ) QuantsOk.nil)))))
  have hb : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (iterVar "b" "b*") (bytesV w) :=
    Equiv.Execution.evalExp_iterPat (by decide) fb
  have hmems : f.module.mems[memIdx0.toNat]? = some ad := by
    simpa [ModuleInst.memAddr?] using ha
  have hmi : s.mems[ad]? = some mi := by simpa [Store.memInst?] using hm
  have hw' : mi.writeBytes? (i.toNat + ao.offset.val) w.size w = some mi' := by
    rw [hsz]; exact hw
  have hwm : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)])),
        .expA (.binE .addOp (.numT .natT) iPay offE), .expA (div8E sizeNtE),
        .expA (iterVar "b" "b*")]) (stateV hn (s.setMemInst ad mi') f) :=
    evalExp_withMem20 (x := memIdx0) rfl (evalExp_var fz)
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil,
        rfl⟩))
      (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off fa))
      (by rw [hsz]; exact evalExp_div8 (evalExp_sizeNt rfl fnt) (width_cases t)) hb hmems hmi hw'
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E sizeNtE), .expA (iterVar "b" "b*")], .listE []]))
      (configV hn ⟨s.setMemInst ad mi', f, []⟩) :=
    evalExp_case (evalExp_tup2 hwm (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))
  have eN : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")]) (bytesV w) :=
    evalExp_builtin20 ⟨_, _, rfl⟩ rfl (evalArgs_cons (evalExp_var fnt) (evalArgs_cons
      (evalExp_var fc) evalArgs_nil)) (hN t x)
  refine firesT_step_of20 (D := fun _ _ _ _ => True) (els := True) (by decide) hasRuleAt_storeNumVal rfl σ hq
    (evalExp_tup2 (evalExp_storeNumLhs hS fz fi fnt fc fa) hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue hb eN)

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
