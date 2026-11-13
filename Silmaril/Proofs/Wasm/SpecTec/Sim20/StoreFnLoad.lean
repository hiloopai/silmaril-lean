module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnRead

/-!
# The loads in `simEnv20T`, from a state typed there

`Step_read` 22 and 23 (unpacked loads, round 3) and 24 and 25 (packed loads, an earlier step),
fired by `firesT_read_of20`: the state typed in `simEnv20T`, the other quantifiers moved from
round 3's typings (`quantsOkT_z`), the conclusion and premise evaluated 's lemmas.
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
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (TypedV QuantsOk ValsOnly Fires stateT evalExp_tup2 evalExp_case
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (LoadNumV NBytes20 LaneCalls20 evalExp_loadLhs innE
  evalExp_trapRhs prem_of_trap evalExp_sizeNt width_cases typedV_memarg20 hasTyp_numAt20
  evalExp_builtin20 evalExp_eqTrue evalExp_loadSlice typedV_inn20 typedV_n20 hasTyp_iN_of_uN20
  packWidth_cases)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (loadPackScope evalExp_loadPackLhs evalExp_extend20
  evalExp_packSlice extPack20 extendE)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

/-- **`Step_read/load-num-trap` in `simEnv20T`.** -/
theorem firesT_loadNumTrap {s : Store H} {f : Frame} {t : NumType} {ao : V2.MemArg}
    {li : V2.Instr} (hL : LoadNumV t ao li) {i : BitVec 32} {ad : MemAddr} {mi : MemInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
    Fires (simEnv20T B) "Step_read" 22 (.tuple [configV hn ⟨s, f, [constI32 i, .plain li]⟩,
      .list (adminsToV [.trap])]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("nt", numTypeV t), ("ao", memargV ao)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  refine firesT_read_of20 Whole.hasRuleAt_loadNumTrap rfl σ
    (quantsOkT_z hρ rfl hz (by decide)
      (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
        (QuantsOk.cons rfl (Pure.typedV_numtype20 B t _ hρ)
          (QuantsOk.cons rfl (typedV_memarg20 ao _ hρ) QuantsOk.nil))))
    (evalExp_tup2 (evalExp_loadLhs hL rfl rfl rfl rfl) evalExp_trapRhs) ?_
    (D := fun _ _ _ _ => True) (els := True)
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl rfl rfl rfl (evalExp_sizeNt rfl rfl) (width_cases t) ha hm hlt)

/-- **`Step_read/load-num-val` in `simEnv20T`.** -/
theorem firesT_loadNumVal (hN : NBytes20 B) {s : Store H} {f : Frame} {t : NumType}
    {ao : V2.MemArg} {li : V2.Instr} (hL : LoadNumV t ao li) {i : BitVec 32} {ad : MemAddr}
    {mi : MemInst} {c : BitVec t.width} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) =
      some (nbytes t c)) :
    Fires (simEnv20T B) "Step_read" 23 (.tuple [configV hn ⟨s, f, [constI32 i, .plain li]⟩,
      .list (adminsToV [(Val.num ⟨t, c⟩).toAdmin])]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("nt", numTypeV t), ("ao", memargV ao), ("c", numV ⟨t, c⟩)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (numTypeV t) := rfl
  have hr : EvalExp (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c"])])
      (.list (adminsToV [(Val.num ⟨t, c⟩).toAdmin])) := by
    show EvalExp _ _ _ (.list [adminToV (Val.num ⟨t, c⟩).toAdmin])
    rw [Pure.adminToV_num]
    exact evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fnt) (evalExp_var rfl)))
  have eN : EvalExp (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")]) (bytesV (nbytes t c)) :=
    evalExp_builtin20 ⟨_, _, rfl⟩ rfl (evalArgs_cons (evalExp_var fnt) (evalArgs_cons
      (evalExp_var rfl) evalArgs_nil)) (hN t c)
  refine firesT_read_of20 Whole.hasRuleAt_loadNumVal rfl σ
    (quantsOkT_z hρ rfl hz (by decide)
      (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
        (QuantsOk.cons fnt (Pure.typedV_numtype20 B t _ hρ)
          (QuantsOk.cons rfl (typedV_memarg20 ao _ hρ)
            (QuantsOk.cons rfl (hasTyp_numAt20 t c (evalExp_var fnt)) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_loadLhs hL rfl rfl fnt rfl) hr) ?_
    (D := fun _ _ _ _ => True) (els := True)
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue eN (evalExp_loadSlice rfl rfl fnt rfl rfl rfl ha hm hb))

/-- **`Step_read/load-pack-trap` in `simEnv20T`.** -/
theorem firesT_loadPackTrap {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {ao : V2.MemArg} {i : BitVec 32} {ad : MemAddr} {mi : MemInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
    Fires (simEnv20T B) "Step_read" 24 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩,
      .list (adminsToV [.trap])]) := by
  let σ := loadPackScope (hn := hn) s f i t sz sx ao
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  refine firesT_read_of20 GoodMerge.hasRuleAt_loadPackTrap rfl σ
    (quantsOkT_z hρ rfl hz (by decide)
      (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
        (QuantsOk.cons rfl (typedV_inn20 t _ hρ) (QuantsOk.cons fn (typedV_n20 _ _ hρ)
          (QuantsOk.cons rfl (Pure.typedV_sx20 B sx _ hρ)
            (QuantsOk.cons rfl (typedV_memarg20 ao _ hρ) QuantsOk.nil))))))
    (evalExp_tup2 (evalExp_loadPackLhs rfl rfl rfl fn rfl rfl) evalExp_trapRhs) ?_
    (D := fun _ _ _ _ => True) (els := True)
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl rfl rfl rfl (evalExp_var fn) (packWidth_cases sz) ha hm hlt)

/-- **`Step_read/load-pack-val` in `simEnv20T`.** -/
theorem firesT_loadPackVal {P : Profile} (hF : Sim.Floats.FloatB P B) (hL : LaneCalls20 B)
    {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {sx : Signedness} {ao : V2.MemArg}
    {i : BitVec 32} {ad : MemAddr} {mi : MemInst} {c : BitVec sz.width}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (sz.width / 8) =
      some (ibytes sz.width c)) :
    Fires (simEnv20T B) "Step_read" 25 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩,
      .list (adminsToV [.plain (.intConst t (extPack20 t sx c))])]) := by
  let σ := loadPackScope (hn := hn) s f i t sz sx ao ++ [("c", pctV c.toNat)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (numTypeV (.int t)) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fsx : (VarEnv.empty.bindVals σ).findVal? "sx" = some (sxV sx) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have hr : EvalExp (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [innE, extendE])])
      (.list (adminsToV [.plain (.intConst t (extPack20 t sx c))])) :=
    evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fInn))
      (evalExp_extend20 hF rfl rfl fInn fn fsx fc)))
  have hi : EvalExp (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "ibytes_" [.expA (.varE "n"), .expA (.varE "c")]) (bytesV (ibytes sz.width c)) := by
    have h := evalExp_builtin20 (x := "ibytes_") ⟨_, _, rfl⟩ rfl
      (evalArgs_cons (evalExp_var fn) (evalArgs_cons (evalExp_var fc) evalArgs_nil))
      (hL.ibytes sz.width c.toNat)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  refine firesT_read_of20 GoodMerge.hasRuleAt_loadPackVal rfl σ
    (quantsOkT_z hρ fz hz (by decide)
      (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
        (QuantsOk.cons fInn (typedV_inn20 t _ hρ) (QuantsOk.cons fn (typedV_n20 _ _ hρ)
          (QuantsOk.cons fsx (Pure.typedV_sx20 B sx _ hρ)
            (QuantsOk.cons fa (typedV_memarg20 ao _ hρ)
              (QuantsOk.cons fc (hasTyp_iN_of_uN20 (evalExp_var fn) c.isLt) QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_loadPackLhs fz fi fInn fn fsx fa) hr) ?_
    (D := fun _ _ _ _ => True) (els := True)
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue hi (evalExp_packSlice fz fi fn fa rfl (packWidth_cases sz) ha hm hb))

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
