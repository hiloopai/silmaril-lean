module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVStoreLane

/-!
# The scalar store rules 11–14 forward at the top of the code, without an erratum

Pass 1 showed that a configuration whose code contains a V2 store has no typed image
(`not_typed20_storeStep`): the `STORE` case of `admininstr` iterates its premise over an unbound
`Inn?`. So the forward statements from typed images, which nest under the contexts, hold for the
store rules only vacuously. The restatement here does not type the code. The four rules quantify
only the parts of the instruction (`z`, `i`, `nt` or `Inn`, `c`, `n`, `ao`, `b*`), not the code
sequence, so at the top of the code each fires from the image of the V2 step as soon as the
**state** is typed:

* `fires_storeNumTrap` (rule 11, integer and float) and `fires_storePackTrap` (rule 13), at every
  builtins;
* `fires_storeNumVal` (rule 12, integer and float) at builtins answering `$nbytes_`
  (`NBytes20`), and `fires_storePackVal` (rule 14) at builtins answering `$ibytes_` and the
  float primitive `$wrap__`;
* `storeB P`: `laneB P` with `$nbytes_` answered; it keeps every earlier answer.
* **`Task.wholeStepStoreTop20`** (stated and proved): at `storeB`, each of V2's six scalar store
  steps at the top of the code, from a configuration whose state is typed, is a step of the
  corrected script between the images.

Below the top of the code the corrected script's structural rules quantify their code as
`admininstr*`, which a `STORE` never is, so nesting still needs the erratum binding `Inn`.
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
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.State (iterVar)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Left-hand sides -/

/-- A `STORE` of a number type without a pack size, as V2 encodes it. -/
def StoreNumV (t : NumType) (ao : V2.MemArg) (st : V2.Instr) : Prop :=
  instrToV st = .case "STORE" (.tuple [numTypeV t, .opt none, memargV ao])

theorem storeNumV_int (t : IntType) (ao : V2.MemArg) :
    StoreNumV (.int t) ao (.intStore t none ao) := rfl

theorem storeNumV_float (t : FloatType) (ao : V2.MemArg) :
    StoreNumV (.float t) ao (.floatStore t ao) := rfl

/-- The left-hand side `CONST I32 i; CONST nt c; STORE nt ε ao`, evaluated. -/
theorem evalExp_storeNumLhs {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32} {t : NumType}
    {x : BitVec t.width} {ao : V2.MemArg} {st : V2.Instr} (hS : StoreNumV t ao st)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fnt : ρ.findVal? "nt" = some (numTypeV t)) (fc : ρ.findVal? "c" = some (numV ⟨t, x⟩))
    (fa : ρ.findVal? "ao" = some (memargV ao)) :
    EvalExp (simEnv20 B) ρ (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "CONST" (.tupE [.varE "nt", .varE "c"]),
      .caseE "STORE" (.tupE [.varE "nt", .optE none, .varE "ao"])]]))
      (configV hn ⟨s, f, [constI32 i, (Val.num ⟨t, x⟩).toAdmin, .plain st]⟩) := by
  have h₂ : EvalExp (simEnv20 B) ρ (.caseE "CONST" (.tupE [.varE "nt", .varE "c"]))
      (adminToV (Val.num ⟨t, x⟩).toAdmin) := by
    rw [Pure.adminToV_num]
    exact evalExp_case (evalExp_tup2 (evalExp_var fnt) (evalExp_var fc))
  have h₃ : EvalExp (simEnv20 B) ρ (.caseE "STORE" (.tupE [.varE "nt", .optE none, .varE "ao"]))
      (adminToV (.plain st)) := by
    show EvalExp (simEnv20 B) ρ _ (instrToV st)
    rw [hS]
    exact evalExp_case (Sim.evalExp_tup3 (evalExp_var fnt) (evalExp_optE_none_iff.2 rfl)
      (evalExp_var fa))
  exact evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constIE fi) (evalExps_cons h₂ (evalExps_cons h₃ evalExps_nil)), rfl⟩))

/-- `c : num_(nt)`, in a scope binding `nt`. -/
theorem hasTyp_numAt20 {ρ : VarEnv} {e : Exp} (t : NumType) (x : BitVec t.width)
    (he : EvalExp (simEnv20 B) ρ e (numTypeV t)) :
    HasTyp (simEnv20 B) ρ (.varT "num_" [.expA e]) (numV ⟨t, x⟩) := by
  rcases t with t | t
  · exact Pure.hasTyp_num_int20 x he
  · exact Pure.hasTyp_num_float20 t x he

/-! ## Rule 11 -/

/-- **`Step/store-num-trap` fires forward** at the image of V2's `storeIntTrap` and
`storeFloatTrap`, at every builtins, from a typed state. -/
theorem fires_storeNumTrap {s : Store H} {f : Frame} {t : NumType} {x : BitVec t.width}
    {ao : V2.MemArg} {st : V2.Instr} (hS : StoreNumV t ao st) {i : BitVec 32} {ad : MemAddr}
    {mi : MemInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
    Fires (simEnv20 B) "Step" 11 (.tuple [
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
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match storeNumTrapRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fnt (Pure.typedV_numtype20 B t _ hρ)
        (QuantsOk.cons fc (hasTyp_numAt20 t x (evalExp_var fnt))
          (QuantsOk.cons fa (typedV_memarg20 ao _ hρ) QuantsOk.nil))))
  refine Pure.fires_of_ruleAt hasRuleAt_storeNumTrap σ hq
    (evalExp_tup2 (evalExp_storeNumLhs hS fz fi fnt fc fa) (evalExp_zTrap fz)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl fz fi fa (evalExp_sizeNt rfl fnt) (width_cases t) ha hm hlt)


/-! ## Rule 13 -/

/-- The left-hand side `CONST I32 i; CONST Inn c; STORE Inn (% n) ao`, evaluated. -/
theorem evalExp_storePackLhs {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32} {t : IntType}
    {x : BitVec t.width} {sz : PackSize} {ao : V2.MemArg}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fInn : ρ.findVal? "Inn" = some (numTypeV (.int t))) (fc : ρ.findVal? "c" = some (pctV x.toNat))
    (fn : ρ.findVal? "n" = some (.num (.natN sz.width))) (fa : ρ.findVal? "ao" = some (memargV ao)) :
    EvalExp (simEnv20 B) ρ (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "CONST" (.tupE [innE, .varE "c"]),
      .caseE "STORE" (.tupE [innE, .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"])]]))
      (configV hn ⟨s, f, [constI32 i, .plain (.intConst t x), .plain (.intStore t (some sz) ao)]⟩) := by
  have hInn : EvalExp (simEnv20 B) ρ innE (numTypeV (.int t)) := evalExp_subE_iff.2 (evalExp_var fInn)
  have h₂ : EvalExp (simEnv20 B) ρ (.caseE "CONST" (.tupE [innE, .varE "c"]))
      (adminToV (.plain (.intConst t x))) :=
    evalExp_case (evalExp_tup2 hInn (evalExp_var fc))
  have hsz : EvalExp (simEnv20 B) ρ (.optE (some (.caseE "%" (.tupE [.varE "n"]))))
      (.opt (some (szV sz))) :=
    evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var fn)
      evalExps_nil, rfl⟩), rfl⟩
  have h₃ : EvalExp (simEnv20 B) ρ
      (.caseE "STORE" (.tupE [innE, .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"]))
      (adminToV (.plain (.intStore t (some sz) ao))) :=
    evalExp_case (Sim.evalExp_tup3 hInn hsz (evalExp_var fa))
  exact evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constIE fi) (evalExps_cons h₂ (evalExps_cons h₃ evalExps_nil)), rfl⟩))

theorem findTyp_Inn20 : (simEnv20 B).findTyp? "Inn" = some ([], [.instD [] [] (.variantT
    [.mk "I32" (.tupT []) [] [], .mk "I64" (.tupT []) [] []])]) := rfl

/-- Every integer type is an `Inn`. -/
theorem typedV_inn20 (t : IntType) : TypedV (simEnv20 B) (.varT "Inn" []) (numTypeV (.int t)) := by
  cases t <;> exact Pure.typedV_closedCase20 findTyp_Inn20 rfl hasTyp_tupT_nil

/-- The scope of rules 13 and 14. -/
abbrev storePackScope (s : Store H) (f : Frame) (i : BitVec 32) (t : IntType) (x : BitVec t.width)
    (sz : PackSize) (ao : V2.MemArg) : List (IL.Id × Value) :=
  [("z", stateV hn s f), ("i", pctV i.toNat), ("Inn", numTypeV (.int t)), ("c", pctV x.toNat),
    ("n", .num (.natN sz.width)), ("ao", memargV ao)]

/-- **`Step/store-pack-trap` fires forward** at the image of V2's `storePackTrap`, at every
builtins, from a typed state. -/
theorem fires_storePackTrap {s : Store H} {f : Frame} {t : IntType} {x : BitVec t.width}
    {sz : PackSize} {ao : V2.MemArg} {i : BitVec 32} {ad : MemAddr} {mi : MemInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
    Fires (simEnv20 B) "Step" 13 (.tuple [
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
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match storePackTrapRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fInn (typedV_inn20 t _ hρ)
        (QuantsOk.cons fc (Pure.hasTyp_num_int20 x (evalExp_subE_iff.2 (evalExp_var fInn)))
          (QuantsOk.cons fn (typedV_n20 _ _ hρ)
            (QuantsOk.cons fa (typedV_memarg20 ao _ hρ) QuantsOk.nil)))))
  refine Pure.fires_of_ruleAt hasRuleAt_storePackTrap σ hq
    (evalExp_tup2 (evalExp_storePackLhs fz fi fInn fc fn fa) (evalExp_zTrap fz)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl fz fi fa (evalExp_var fn) (packWidth_cases sz) ha hm hlt)


/-! ## Rule 14 -/

/-- `$ibytes_(n, $wrap__($size(Inn), n, c))`. -/
abbrev packBytesE : Exp :=
  .callE "ibytes_" [.expA (.varE "n"), .expA (.callE "wrap__" [.expA (.callE "size"
    [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "valtype" []))]), .expA (.varE "n"),
    .expA (.varE "c")])]

/-- `Step/store-pack-val`, rule 14 of `Step` (verbatim). -/
def storePackValRule : Rule :=
  .ruleD "store-pack-val" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "Inn" (.varT "Inn" []),
    .expP "c" (.varT "num_" [.expA innE]), .expP "n" (.varT "n" []),
    .expP "ao" (.varT "memarg" []), .expP "b*" (.iterT (.varT "byte" []) .list)] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "CONST" (.tupE [innE, .varE "c"]),
      .caseE "STORE" (.tupE [innE, .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"])]]),
      .caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E (.varE "n")), .expA (iterVar "b" "b*")], .listE []])])
    [.ifPr (.cmpE .eqOp .boolT (iterVar "b" "b*") packBytesE)]

theorem hasRuleAt_storePackVal : HasRuleAt (simEnv20 B) "Step" "%~>%" 14 storePackValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The stored bytes of a pack store, as the rule computes them. -/
theorem evalExp_packBytes {P : Profile} (hF : Sim.Floats.FloatB P B) (hL : LaneCalls20 B)
    {ρ : VarEnv} {t : IntType} {x : BitVec t.width} {sz : PackSize}
    (fInn : ρ.findVal? "Inn" = some (numTypeV (.int t))) (fc : ρ.findVal? "c" = some (pctV x.toNat))
    (fn : ρ.findVal? "n" = some (.num (.natN sz.width))) (hρ : ρ.findDef? "size" = none)
    (hρw : ρ.findDef? "wrap__" = none) (hρi : ρ.findDef? "ibytes_" = none) :
    EvalExp (simEnv20 B) ρ packBytesE (bytesV (ibytes sz.width (x.setWidth sz.width))) := by
  have hs : EvalExp (simEnv20 B) ρ (.callE "size" [.expA (.subE (.varE "Inn") (.varT "Inn" [])
      (.varT "valtype" []))]) (.num (.natN t.width)) :=
    evalExp_callE_iff.2 (Pure.callDef_size20 (.int t) hρ
      (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var fInn)) evalArgs_nil))
  have hw : EvalExp (simEnv20 B) ρ (.callE "wrap__" [.expA (.callE "size"
      [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "valtype" []))]), .expA (.varE "n"),
      .expA (.varE "c")]) (pctV (x.setWidth sz.width).toNat) := by
    exact evalExp_builtin20 (x := "wrap__") ⟨_, _, rfl⟩ hρw
      (evalArgs_cons hs (evalArgs_cons (evalExp_var fn) (evalArgs_cons (evalExp_var fc)
        evalArgs_nil))) (hF _ _ _ (Sim.Floats.floatCall_wrap P t.width sz.width x))
  have h := evalExp_builtin20 (x := "ibytes_") ⟨_, _, rfl⟩ hρi
    (evalArgs_cons (evalExp_var fn) (evalArgs_cons hw evalArgs_nil)) (hL.ibytes _ _)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

/-- **`Step/store-pack-val` fires forward** at the image of V2's `storePackVal`, at builtins
answering `$ibytes_` and the float primitives, from a typed state. -/
theorem fires_storePackVal {P : Profile} (hF : Sim.Floats.FloatB P B) (hL : LaneCalls20 B)
    {s : Store H} {f : Frame} {t : IntType} {x : BitVec t.width} {sz : PackSize}
    {ao : V2.MemArg} {i : BitVec 32} {ad : MemAddr} {mi mi' : MemInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
      (ibytes sz.width (x.setWidth sz.width)) = some mi') :
    Fires (simEnv20 B) "Step" 14 (.tuple [
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
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match storePackValRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
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
  refine Pure.fires_of_ruleAt hasRuleAt_storePackVal σ hq
    (evalExp_tup2 (evalExp_storePackLhs fz fi fInn fc fn fa) hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue hb (evalExp_packBytes hF hL fInn fc fn rfl rfl rfl))


/-! ## Builtins answering `$nbytes_` -/

/-- `numV` is injective at each number type. -/
theorem numV20_inj {t : NumType} {a b : BitVec t.width} (h : numV ⟨t, a⟩ = numV ⟨t, b⟩) : a = b := by
  rcases t with t | t
  · exact BitVec.eq_of_toNat_eq (pctV_injective h)
  · exact Sim.Typing.floatV_injective t h

/-- **`B` answers `$nbytes_` as V2 does.** -/
def NBytes20 (B : Builtins) : Prop :=
  ∀ (t : NumType) (x : BitVec t.width),
    B.call "nbytes_" [.val (numTypeV t), .val (numV ⟨t, x⟩)] = some (bytesV (nbytes t x))

open Classical in
/-- `$nbytes_(nt, c)`. -/
noncomputable def nbytesCall20 (ws : List ArgV) : Option Value :=
  if h : ∃ p : (t : NumType) × BitVec t.width, ws = [.val (numTypeV p.1), .val (numV ⟨p.1, p.2⟩)]
  then some (bytesV (nbytes h.choose.1 h.choose.2)) else none

theorem nbytesCall20_eq (t : NumType) (x : BitVec t.width) :
    nbytesCall20 [.val (numTypeV t), .val (numV ⟨t, x⟩)] = some (bytesV (nbytes t x)) := by
  have h : ∃ p : (t : NumType) × BitVec t.width, [ArgV.val (numTypeV t), .val (numV ⟨t, x⟩)] =
      [.val (numTypeV p.1), .val (numV ⟨p.1, p.2⟩)] := ⟨⟨t, x⟩, rfl⟩
  rw [nbytesCall20, dite_eq_left_of_eq_true (eq_true h)]
  have hs := h.choose_spec
  generalize h.choose = p at hs ⊢
  obtain ⟨t', x'⟩ := p
  obtain ⟨e₁, t₁⟩ := List.cons.inj hs
  obtain ⟨e₂, -⟩ := List.cons.inj t₁
  obtain rfl := numTypeV_inj (ArgV.val.inj e₁).symm
  obtain rfl := numV20_inj (ArgV.val.inj e₂).symm
  rfl

/-- **`laneB P` with `$nbytes_` answered as V2 does.** -/
noncomputable def storeB (P : Profile) : Builtins :=
  ⟨fun x ws => if x = "nbytes_" then nbytesCall20 ws else (laneB P).call x ws⟩

theorem storeB_call_of_ne {P : Profile} {x : IL.Id} (h : x ≠ "nbytes_") (ws : List ArgV) :
    (storeB P).call x ws = (laneB P).call x ws := by
  simp [storeB, h]

theorem nbytes20_storeB (P : Profile) : NBytes20 (storeB P) := fun t x => by
  simp only [storeB, ↓reduceIte, nbytesCall20_eq]

theorem intB_storeB (P : Profile) : Sim.IntNumeric.IntB (storeB P) := by
  intro x ws v h
  by_cases hx : x = "nbytes_"
  · subst hx; simp [Sim.IntNumeric.intCall] at h
  rw [storeB_call_of_ne hx]
  exact intB_laneB P x ws v h

theorem floatB_storeB (P : Profile) : Sim.Floats.FloatB P (storeB P) := by
  intro x ws v h
  by_cases hx : x = "nbytes_"
  · subst hx; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  rw [storeB_call_of_ne hx]
  exact floatB_laneB P x ws v h

theorem growCalls20_storeB (P : Profile) : GrowCalls20 (storeB P) where
  table ti ti' n r h := by
    rw [storeB_call_of_ne (by decide)]
    exact (growCalls20_laneB P).table ti ti' n r h
  mem mi mi' n h := by
    rw [storeB_call_of_ne (by decide)]
    exact (growCalls20_laneB P).mem mi mi' n h

theorem vbytes20_storeB (P : Profile) : VBytes20 (storeB P) := fun c => by
  rw [storeB_call_of_ne (by decide)]
  exact vbytes20_laneB P c

theorem laneCalls20_storeB (P : Profile) : LaneCalls20 (storeB P) where
  lanes sz c := by
    rw [storeB_call_of_ne (by decide)]
    exact (laneCalls20_laneB P).lanes sz c
  ibytes N k := by
    rw [storeB_call_of_ne (by decide)]
    exact (laneCalls20_laneB P).ibytes N k


/-! ## Rule 12 -/

/-- `$size(nt <: valtype)`. -/
abbrev sizeNtE : Exp := .callE "size" [.expA (.subE (.varE "nt") (.varT "numtype" []) (.varT "valtype" []))]

/-- `Step/store-num-val`, rule 12 of `Step` (verbatim). -/
def storeNumValRule : Rule :=
  .ruleD "store-num-val" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "nt" (.varT "numtype" []),
    .expP "c" (.varT "num_" [.expA (.varE "nt")]), .expP "ao" (.varT "memarg" []),
    .expP "b*" (.iterT (.varT "byte" []) .list)] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "CONST" (.tupE [.varE "nt", .varE "c"]),
      .caseE "STORE" (.tupE [.varE "nt", .optE none, .varE "ao"])]]),
      .caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E sizeNtE), .expA (iterVar "b" "b*")], .listE []])])
    [.ifPr (.cmpE .eqOp .boolT (iterVar "b" "b*")
      (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")]))]

theorem hasRuleAt_storeNumVal : HasRuleAt (simEnv20 B) "Step" "%~>%" 12 storeNumValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- **`Step/store-num-val` fires forward** at the image of V2's `storeIntVal` and
`storeFloatVal`, at builtins answering `$nbytes_` as V2 does, from a typed state. -/
theorem fires_storeNumVal (hN : NBytes20 B) {s : Store H} {f : Frame} {t : NumType}
    {x : BitVec t.width} {ao : V2.MemArg} {st : V2.Instr} (hS : StoreNumV t ao st) {i : BitVec 32}
    {ad : MemAddr} {mi mi' : MemInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (t.width / 8) (nbytes t x) = some mi') :
    Fires (simEnv20 B) "Step" 12 (.tuple [
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
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match storeNumValRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
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
  refine Pure.fires_of_ruleAt hasRuleAt_storeNumVal σ hq
    (evalExp_tup2 (evalExp_storeNumLhs hS fz fi fnt fc fa) hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue hb eN)

end Silmaril.Wasm.SpecTec.Sim20.Whole
