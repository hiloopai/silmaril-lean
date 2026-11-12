module

public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The packed loads forward (`Step_read` 24 and 25)

2.0's

  `z; (CONST I32 i) (LOAD Inn (n _ sx) ao) ~> TRAP`, if `i + ao.OFFSET + n/8 > |$mem(z, 0).BYTES|`
  `z; (CONST I32 i) (LOAD Inn (n _ sx) ao) ~> (CONST Inn $extend__(n, $size(Inn), sx, c))`,
    if `$ibytes_(n, c) = $mem(z, 0).BYTES[i + ao.OFFSET : n/8]`

Both rules are transcribed and found in `simEnv20` by `rfl` (`hasRuleAt_loadPackTrap`,
`hasRuleAt_loadPackVal`). As for the unpacked loads (`Whole.fires_loadNumVal`), the narrow value
`c` is bound only by the premise, and is bound forward to the bits V2 reads. The premise holds at
builtins answering `$ibytes_` as V2 does (`Whole.LaneCalls20`), and the result is V2's extension
at builtins answering the float primitives (`Sim.Floats.FloatB`, which gives `$extend__` by
`Sim.Floats.floatCall_extend`). `storeB P` has both.

* `fires_loadPackTrap` (every builtins), `fires_loadPackVal` (`FloatB` and `LaneCalls20`);
* `LoadPackFwd20`: V2's two packed load steps, with V2's premises;
* **`fwdBase20_loadPack`**: they are a base (`Whole.FwdBase20`): subject reduction and the step of
  `simEnv20S`, from a configuration typed in `simEnv20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.GoodMerge

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.Whole

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The rules -/

/-- The packing of a packed load, `n _ sx`. -/
abbrev packSxE : Exp :=
  .optE (some (.caseE "%_%" (.tupE [.caseE "%" (.tupE [.varE "n"]), .varE "sx"])))

/-- `z; (CONST I32 i) (LOAD Inn (n _ sx) ao)`. -/
abbrev loadPackLhsE : Exp := .caseE "%;%" (.tupE [.varE "z", .listE [constIE,
  .caseE "LOAD" (.tupE [innE, packSxE, .varE "ao"])]])

/-- `$extend__(n, $size(Inn), sx, c)`. -/
abbrev extendE : Exp :=
  .callE "extend__" [.expA (.varE "n"), .expA (.callE "size" [.expA (.subE (.varE "Inn")
    (.varT "Inn" []) (.varT "valtype" []))]), .expA (.varE "sx"), .expA (.varE "c")]

/-- `$mem(z, 0).BYTES[i + ao.OFFSET : n/8]`. -/
abbrev packSliceE : Exp :=
  .sliceE (.dotE mem0E "BYTES") (.binE .addOp (.numT .natT) iPay offE) (div8E (.varE "n"))

/-- `Step_read/load-pack-trap`, rule 24 (transcribed). -/
def loadPackTrapRule : Rule :=
  .ruleD "load-pack-trap" [.expP "z" (.varT "state" []),
      .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "Inn" (.varT "Inn" []),
      .expP "n" (.varT "n" []), .expP "sx" (.varT "sx" []), .expP "ao" (.varT "memarg" [])] "%~>%"
    (.tupE [loadPackLhsE, trapRhs])
    [.ifPr (.cmpE .gtOp (.numT .natT) (addrE (div8E (.varE "n"))) memLenE)]

/-- `Step_read/load-pack-val`, rule 25 (transcribed). -/
def loadPackValRule : Rule :=
  .ruleD "load-pack-val" [.expP "z" (.varT "state" []),
      .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "Inn" (.varT "Inn" []),
      .expP "n" (.varT "n" []), .expP "sx" (.varT "sx" []), .expP "ao" (.varT "memarg" []),
      .expP "c" (.varT "iN" [.expA (.varE "n")])] "%~>%"
    (.tupE [loadPackLhsE, .listE [.caseE "CONST" (.tupE [innE, extendE])]])
    [.ifPr (.cmpE .eqOp .boolT (.callE "ibytes_" [.expA (.varE "n"), .expA (.varE "c")])
      packSliceE)]

theorem hasRuleAt_loadPackTrap : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 24 loadPackTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_loadPackVal : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 25 loadPackValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- V2's extension of a packed load. -/
def extPack20 (t : IntType) (sx : Signedness) {N : Nat} (c : BitVec N) : BitVec t.width :=
  match sx with
  | .signed => c.signExtend t.width
  | .unsigned => c.setWidth t.width

/-! ## The pieces -/

/-- The left-hand side, evaluated. -/
theorem evalExp_loadPackLhs {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32} {t : IntType}
    {sz : PackSize} {sx : Signedness} {ao : V2.MemArg}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fInn : ρ.findVal? "Inn" = some (numTypeV (.int t)))
    (fn : ρ.findVal? "n" = some (.num (.natN sz.width))) (fsx : ρ.findVal? "sx" = some (sxV sx))
    (fa : ρ.findVal? "ao" = some (memargV ao)) :
    EvalExp (simEnv20 B) ρ loadPackLhsE
      (configV hn ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩) := by
  have hInn : EvalExp (simEnv20 B) ρ innE (numTypeV (.int t)) :=
    evalExp_subE_iff.2 (evalExp_var fInn)
  have hp : EvalExp (simEnv20 B) ρ packSxE (.opt (some (.case "%_%" (.tuple [szV sz, sxV sx])))) :=
    evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2
      ⟨_, evalExps_cons (evalExp_var fn) evalExps_nil, rfl⟩)) (evalExp_var fsx)), rfl⟩
  have h₂ : EvalExp (simEnv20 B) ρ (.caseE "LOAD" (.tupE [innE, packSxE, .varE "ao"]))
      (adminToV (.plain (.intLoad t (some (sz, sx)) ao))) :=
    evalExp_case (Sim.evalExp_tup3 hInn hp (evalExp_var fa))
  exact evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constIE fi) (evalExps_cons h₂ evalExps_nil), rfl⟩))

/-- The slice of the frame's memory at a width `w`, at a read V2 makes. -/
theorem evalExp_packSlice {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32}
    {ao : V2.MemArg} {w : Nat} {ad : MemAddr} {mi : MemInst}
    {r : Silmaril.Wasm.Execution.Memory.Bytes}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fn : ρ.findVal? "n" = some (.num (.natN w))) (fa : ρ.findVal? "ao" = some (memargV ao))
    (hρ : ρ.findDef? "mem" = none) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128)
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (w / 8) =
      some r) :
    EvalExp (simEnv20 B) ρ packSliceE (bytesV r) := by
  have hx : EvalExp (simEnv20 B) ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (idxV memIdx0) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)
  have hmem : EvalExp (simEnv20 B) ρ (.dotE mem0E "BYTES") (.list (Sim.Memory.bytesL mi.bytes)) := by
    rw [← bytesV_eq_bytesL]
    exact evalExp_dotE_iff.2 ⟨memInstV mi, evalExp_mem20 hρ (evalExp_var fz) hx
      (by simpa [ModuleInst.memAddr?] using ha) (by simpa [Store.memInst?] using hm), rfl⟩
  have hsl : (Value.list (Sim.Memory.bytesL mi.bytes)).slice? (effAddr i.toNat ao) (w / 8) =
      some (bytesV r) := by
    rw [Sim.Memory.slice?_bytesL, hb, bytesV_eq_bytesL]
    rfl
  exact evalExp_sliceE_iff.2 ⟨_, _, _, hmem, evalExp_addNat20 (evalExp_iPay fi) (evalExp_off fa),
    evalExp_div8 (evalExp_var fn) hw, hsl⟩

/-- **`$extend__(n, $size(Inn), sx, c)` is V2's extension**, at builtins answering the float
primitives. -/
theorem evalExp_extend20 {P : Profile} (hF : Sim.Floats.FloatB P B) {ρ : VarEnv} {t : IntType}
    {sz : PackSize} {sx : Signedness} {c : BitVec sz.width}
    (hρ₁ : ρ.findDef? "extend__" = none) (hρ₂ : ρ.findDef? "size" = none)
    (fInn : ρ.findVal? "Inn" = some (numTypeV (.int t)))
    (fn : ρ.findVal? "n" = some (.num (.natN sz.width))) (fsx : ρ.findVal? "sx" = some (sxV sx))
    (fc : ρ.findVal? "c" = some (pctV c.toNat)) :
    EvalExp (simEnv20 B) ρ extendE (pctV (extPack20 t sx c).toNat) := by
  have hs : EvalExp (simEnv20 B) ρ (.callE "size" [.expA (.subE (.varE "Inn") (.varT "Inn" [])
      (.varT "valtype" []))]) (.num (.natN t.width)) :=
    evalExp_callE_iff.2 (Pure.callDef_size20 (.int t) hρ₂
      (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var fInn)) evalArgs_nil))
  have hc : Sim.Floats.floatCall P "extend__" [.val (.num (.natN sz.width)),
      .val (.num (.natN t.width)), .val (sxV sx), .val (pctV c.toNat)] =
      some (pctV (extPack20 t sx c).toNat) := by
    rw [Pure.sxV_eq20]
    have h := Sim.Floats.floatCall_extend P sz.width t.width sx c
    cases sx <;> exact h
  exact evalExp_builtin20 (x := "extend__") ⟨_, _, rfl⟩ hρ₁
    (evalArgs_cons (evalExp_var fn) (evalArgs_cons hs (evalArgs_cons (evalExp_var fsx)
      (evalArgs_cons (evalExp_var fc) evalArgs_nil)))) (hF _ _ _ hc)

/-! ## The rules fire -/

/-- The scope of rule 24. -/
abbrev loadPackScope (s : Store H) (f : Frame) (i : BitVec 32) (t : IntType) (sz : PackSize)
    (sx : Signedness) (ao : V2.MemArg) : List (IL.Id × Value) :=
  [("z", stateV hn s f), ("i", pctV i.toNat), ("Inn", numTypeV (.int t)),
    ("n", .num (.natN sz.width)), ("sx", sxV sx), ("ao", memargV ao)]

/-- **`Step_read/load-pack-trap` fires forward** at the image of V2's `loadPackTrap`, at every
builtins, from a typed state. -/
theorem fires_loadPackTrap {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {ao : V2.MemArg} {i : BitVec 32} {ad : MemAddr} {mi : MemInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
    Fires (simEnv20 B) "Step_read" 24 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩,
      .list (adminsToV [.trap])]) := by
  let σ := loadPackScope (hn := hn) s f i t sz sx ao
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (numTypeV (.int t)) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fsx : (VarEnv.empty.bindVals σ).findVal? "sx" = some (sxV sx) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match loadPackTrapRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fInn (typedV_inn20 t _ hρ) (QuantsOk.cons fn (typedV_n20 _ _ hρ)
        (QuantsOk.cons fsx (Pure.typedV_sx20 B sx _ hρ)
          (QuantsOk.cons fa (typedV_memarg20 ao _ hρ) QuantsOk.nil)))))
  refine Pure.fires_of_ruleAt hasRuleAt_loadPackTrap σ hq
    (evalExp_tup2 (evalExp_loadPackLhs fz fi fInn fn fsx fa) evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl fz fi fa (evalExp_var fn) (packWidth_cases sz) ha hm hlt)

/-- **`Step_read/load-pack-val` fires forward** at the image of V2's `loadPackVal`, at builtins
answering `$ibytes_` and the float primitives as V2 does, from a typed state. -/
theorem fires_loadPackVal {P : Profile} (hF : Sim.Floats.FloatB P B) (hL : LaneCalls20 B)
    {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {sx : Signedness} {ao : V2.MemArg}
    {i : BitVec 32} {ad : MemAddr} {mi : MemInst} {c : BitVec sz.width}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (sz.width / 8) =
      some (ibytes sz.width c)) :
    Fires (simEnv20 B) "Step_read" 25 (.tuple [
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
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match loadPackValRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fInn (typedV_inn20 t _ hρ) (QuantsOk.cons fn (typedV_n20 _ _ hρ)
        (QuantsOk.cons fsx (Pure.typedV_sx20 B sx _ hρ)
          (QuantsOk.cons fa (typedV_memarg20 ao _ hρ)
            (QuantsOk.cons fc (hasTyp_iN_of_uN20 (evalExp_var fn) c.isLt) QuantsOk.nil))))))
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [innE, extendE])])
      (.list (adminsToV [.plain (.intConst t (extPack20 t sx c))])) :=
    evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fInn))
      (evalExp_extend20 hF rfl rfl fInn fn fsx fc)))
  have hi : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "ibytes_" [.expA (.varE "n"), .expA (.varE "c")]) (bytesV (ibytes sz.width c)) := by
    have h := evalExp_builtin20 (x := "ibytes_") ⟨_, _, rfl⟩ rfl
      (evalArgs_cons (evalExp_var fn) (evalArgs_cons (evalExp_var fc) evalArgs_nil))
      (hL.ibytes sz.width c.toNat)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  refine Pure.fires_of_ruleAt hasRuleAt_loadPackVal σ hq
    (evalExp_tup2 (evalExp_loadPackLhs fz fi fInn fn fsx fa) hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue hi (evalExp_packSlice fz fi fn fa rfl (packWidth_cases sz) ha hm hb))

/-! ## The fragment -/

/-- **V2's two packed load steps**, with V2's premises. -/
inductive LoadPackFwd20 : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {sx : Signedness}
      {ao : V2.MemArg} {i : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
      LoadPackFwd20 ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩ ⟨s, f, [.trap]⟩
  | val {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {sx : Signedness}
      {ao : V2.MemArg} {i : BitVec 32} {mi : MemInst} {c : BitVec sz.width}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (sz.width / 8) =
        some (ibytes sz.width c)) :
      LoadPackFwd20 ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩
        ⟨s, f, [.plain (.intConst t (extPack20 t sx c))]⟩

theorem LoadPackFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : LoadPackFwd20 c c') : Step P host c c' := by
  cases h with
  | trap hm h => exact .read (.loadPackTrap hm h)
  | @val _ _ _ _ sx _ _ _ _ hm hb => cases sx <;> exact .read (.loadPackVal hm hb)

/-- **Subject reduction for the packed loads**: a trap or a value. -/
theorem typed20_succ_loadPack {c c' : Config H} (hc : Typed20 (simEnv20 B) hn c)
    (h : LoadPackFwd20 c c') : Typed20 (simEnv20 B) hn c' := by
  obtain ⟨hz, -⟩ := typed20_iff.1 hc
  cases h with
  | trap _ _ => exact typed20_iff.2 ⟨hz, typedV_admins_trap20⟩
  | @val _ _ t _ sx _ _ _ c _ _ =>
    exact typed20_iff.2 ⟨hz, typedV_admins_val20 (.num ⟨.int t, extPack20 t sx c⟩)⟩

/-- **The packed loads are a base**, at builtins answering `$ibytes_` and the float primitives. -/
theorem fwdBase20_loadPack {P : Profile} {W : Store H → Prop} (hF : Sim.Floats.FloatB P B)
    (hL : LaneCalls20 B) : FwdBase20 B hn W (LoadPackFwd20 (H := H)) where
  sr c c' hc h := typed20_succ_loadPack hc h
  fwd c c' hc _ h := by
    have hc' := typed20_succ_loadPack hc h
    have hz := typedV_state_of_typed20 hc
    cases h with
    | trap hm hlt =>
      obtain ⟨ad, ha, hm'⟩ := mem?_some hm
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_loadPackTrap hz ha hm' hlt)))
    | val hm hb =>
      obtain ⟨ad, ha, hm'⟩ := mem?_some hm
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_loadPackVal hF hL hz ha hm' hb)))

/-- At `storeB`. -/
theorem fwdBase20_loadPack_storeB (P : Profile) {W : Store H → Prop} :
    FwdBase20 (storeB P) hn W (LoadPackFwd20 (H := H)) :=
  fwdBase20_loadPack (floatB_storeB P) (laneCalls20_storeB P)

end Silmaril.Wasm.SpecTec.Sim20.GoodMerge
