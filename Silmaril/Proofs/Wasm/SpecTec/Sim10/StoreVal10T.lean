module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreTop10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLoadVal
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SubjRedStep
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVStoreVal

/-!
# The 1.0 successful stores in `simEnv10T`, forward at `bytesB10`

`Step` 8 (`store-num-val`) and 10 (`store-pack-val`) of the wasm-1.0 script write
`b* = $bytes_(t, c)` (or `$ibytes_(n, $wrap__($size(Inn), n, c))`) at `i + ao.OFFSET` with
`$with_mem`. At the builtins `bytesB10 P` (an earlier `fwdB10`), which answer `$bytes_` and
`$ibytes_` as V1 encodes values and keep `floatIntB`'s `$wrap__`, both fire in `simEnv10T` at
the image of V1's successful `intStore`/`floatStore`, from a state typed in `simEnv10T`:

* `evalExp_withMem10`: `$with_mem(z, 0, i, j, b*)` writes the bytes into the frame's memory, as
  V1's `Memory.writeBytes` does (`memInstV_write10`: the size, hence the `TYPE` field, is kept);
* `fires10T_storeNumVal` (rule 8, integer and float, no pack size) and `fires10T_storePackVal`
  (rule 10, a packed integer store);
* `storeInt_eq_write10`, `storeFloat_eq_write10`, `storeIntPack_eq_write10`: V1's `storeInt` and
  `storeFloat` are `writeBytes` of exactly those bytes.

The rules are transcribed verbatim (`storeNumValRule10`, `storePackValRule10`) and checked at their
index by `rfl`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress setMemory storeInt storeFloat)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV ValsOnly stateT evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathGet_idx pathSet_idx
  pathSet_dot pathSet_root evalExp_idxPayload HasClause1 idxPayload iterVar matchExp_iterVar)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (evalExp_of)
open Silmaril.Wasm.SpecTec.Sim20.Whole (div8E constIE offE iPay evalExp_div8 evalExp_addNat20
  evalExp_iPay width_cases withMemPats20 withMemBody20 pathSet_slice20 setSlice_bytesV20)
open Silmaril.Wasm.SpecTec.Sim10.Whole (innE10 sizeTE evalExp_off10 evalExp_size10 packWidth10_cases
  frameMemory_some bytesB10 storeV_setMem10)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## `$with_mem` at the 1.0 encoding -/

theorem hasClause_withMem10 : HasClause1 (simEnv10 B) "with_mem" withMemPats20 withMemBody20 :=
  ⟨_, _, _, rfl⟩

/-- A V1 memory instance with its bytes written: the slice of its bytes, and its record. -/
theorem memInstV_write10 {m : MemInst} {a : Nat} {w b : Execution.Memory.Bytes}
    (hw : Execution.Memory.writeBytes m.data a w = some b) :
    (bytesV m.data).setSlice a w.size (bytesV w) = some (bytesV b) ∧
      (memInstV m).setField "BYTES" (bytesV b) = some (memInstV {m with data := b}) := by
  refine ⟨?_, ?_⟩
  · have h := setSlice_bytesV20 m.data w a
    rw [hw] at h
    exact h
  have hs : Execution.Memory.size b = Execution.Memory.size m.data := by
    simp only [Execution.Memory.size, Execution.Memory.writeBytes_size _ _ _ _ hw]
  simp [memInstV, Value.setField, hs]

/-- **`$with_mem(z, 0, i, j, b*)`** at the 1.0 encoding: V1's `writeBytes` on the frame's
memory. -/
theorem evalExp_withMem10 {ρ : VarEnv} {ez ex ei ej eb : Exp} {s : Store H} {f : Frame}
    {a : Execution.Runtime.MemAddr} {i : Nat} {m : MemInst} {w b : Execution.Memory.Bytes}
    (hρ : ρ.findDef? "with_mem" = none) (hz : EvalExp (simEnv10 B) ρ ez (stateV hn s f))
    (hx : EvalExp (simEnv10 B) ρ ex (pctV 0)) (hi : EvalExp (simEnv10 B) ρ ei (.num (.natN i)))
    (hj : EvalExp (simEnv10 B) ρ ej (.num (.natN w.size)))
    (hb : EvalExp (simEnv10 B) ρ eb (bytesV w)) (hm : frameMemory s f = some (a, m))
    (hw : Execution.Memory.writeBytes m.data i w = some b) :
    EvalExp (simEnv10 B) ρ (.callE "with_mem" [.expA ez, .expA ex, .expA ei, .expA ej, .expA eb])
      (stateV hn (setMemory s a {m with data := b}) f) := by
  obtain ⟨ha, hs⟩ := frameMemory_some hm
  obtain ⟨hsl, hset⟩ := memInstV_write10 hw
  refine evalExp_call1 hasClause_withMem10 hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hi (evalArgs_cons hj
      (evalArgs_cons hb evalArgs_nil)))))
    (matchArgs_cons (matchArg_expA Sim20.State.matchExp_state) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
          (matchArg_expA (matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil))))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (Sim.evalExp_var rfl))
  have ha' : a.value < s.memories.length := (List.getElem?_eq_some_iff.1 hs).1
  have hidx : EvalExp (simEnv10 B) ((((((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f"
      (frameV f)).bindVal "x" (pctV 0)).bindVal "i" (.num (.natN i))).bindVal "j"
      (.num (.natN w.size))).bindVal "b*" (bytesV w))
      (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload) (.num (.natN a.value)) :=
    evalExp_idxE_iff.2 ⟨_, 0, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, Sim.evalExp_var rfl, rfl⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩
  have hg : PathGet (simEnv10 B) ((((((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f"
      (frameV f)).bindVal "x" (pctV 0)).bindVal "i" (.num (.natN i))).bindVal "j"
      (.num (.natN w.size))).bindVal "b*" (bytesV w)) (storeV hn s)
      (.idxP (.dotP .rootP "MEMS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload))
      (memInstV m) :=
    pathGet_idx (pathGet_dot pathGet_root rfl) hidx (by simp [Value.idx?, List.getElem?_map, hs])
  refine evalExp_updE_iff.2 ⟨storeV hn s, bytesV w, Sim.evalExp_var rfl,
    Equiv.Execution.evalExp_iterPat (by decide) rfl, ?_⟩
  refine pathSet_slice20 (pathGet_dot hg rfl) (Sim.evalExp_var rfl) (Sim.evalExp_var rfl) hsl ?_
  exact pathSet_dot hg hset (pathSet_idx (i := a.value) (pathGet_dot pathGet_root rfl) hidx
    (by simp [Value.setIdx, ha']) (pathSet_dot pathGet_root (storeV_setMem10 s a _) pathSet_root))

/-! ## V1's stores are `writeBytes` -/

theorem setWidth_toNat8 {n : Nat} (x : BitVec n) (hw : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) :
    (x.setWidth (8 * (n / 8))).toNat = x.toNat :=
  Whole.toNat_setWidth_le10 x (by omega)

/-- V1's `storeInt` without a pack size writes the value's little-endian bytes. -/
theorem storeInt_eq_write10 (t : IntType) (mem : Execution.Memory.Bytes) (start : Nat)
    (x : BitVec t.width) : storeInt t none mem start x = Execution.Memory.writeBytes mem start
      (Execution.Memory.encodeLE ((NumType.int t).width / 8) x.toNat) := by
  simp only [storeInt, Option.map_none, Option.getD_none, Execution.Memory.store]
  rw [setWidth_toNat8 x (width_cases (.int t))]
  rfl

/-- V1's `storeFloat` writes the value's little-endian bytes. -/
theorem storeFloat_eq_write10 (t : FloatType) (mem : Execution.Memory.Bytes) (start : Nat)
    (x : BitVec t.width) : storeFloat t mem start x = Execution.Memory.writeBytes mem start
      (Execution.Memory.encodeLE ((NumType.float t).width / 8) x.toNat) := by
  simp only [storeFloat, Execution.Memory.store]
  rw [setWidth_toNat8 x (width_cases (.float t))]
  rfl

/-- V1's packed `storeInt` writes the low `sz` bits' little-endian bytes. -/
theorem storeIntPack_eq_write10 (t : IntType) (sz : V1.PackSize) (mem : Execution.Memory.Bytes)
    (start : Nat) (x : BitVec t.width) : storeInt t (some sz) mem start x =
      Execution.Memory.writeBytes mem start
        (Execution.Memory.encodeLE (sz.width / 8) (x.setWidth sz.width).toNat) := by
  simp only [storeInt, Option.map_some, Option.getD_some, Execution.Memory.store]
  have h8 : 8 * (sz.width / 8) = sz.width := by
    rcases packWidth10_cases sz with h | h | h | h | h <;> rw [h]
  rw [h8]

/-! ## Rule 8 -/

/-- `Step/store-num-val` of 1.0, rule 8 of `Step` (verbatim). -/
def storeNumValRule10 : Rule :=
  .ruleD "store-num-val" [.expP "z" (.varT "state" []), .expP "i" Whole.valI32T',
    .expP "t" (.varT "valtype" []), .expP "c" (.varT "val_" [.expA (.varE "t")]),
    .expP "ao" (.varT "memarg" []), .expP "b*" (.iterT (.varT "byte" []) .list)] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "CONST" (.tupE [.varE "t", .varE "c"]),
      .caseE "STORE" (.tupE [.varE "t", .optE none, .varE "ao"])]]),
      .caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E sizeTE), .expA (iterVar "b" "b*")], .listE []])])
    [.ifPr (.cmpE .eqOp .boolT (iterVar "b" "b*")
      (.callE "bytes_" [.expA (.varE "t"), .expA (.varE "c")]))]

theorem hasRuleAt10_storeNumVal' : HasRuleAt (simEnv10 B) "Step" "%~>%" 8 storeNumValRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `%(0)`. -/
theorem evalExp_pct0' {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (pctV 0) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)

/-- **`Step/store-num-val` fires in `simEnv10T`** at `bytesB10`, at the image of V1's successful
`intStore` (no pack size) and `floatStore`, from a state typed in `simEnv10T`. -/
theorem fires10T_storeNumVal {P : Profile} {s : Store H} {f : Frame} {i : BitVec 32}
    {v : Execution.Runtime.Value} {ao : V1.MemArg} {st : V1.Instr} (hS : StoreNumV10 v ao st)
    {a : Execution.Runtime.MemAddr} {m : MemInst} {b : Execution.Memory.Bytes}
    (hz : TypedV (simEnv10T (bytesB10 P)) stateT (stateV hn s f))
    (hm : frameMemory s f = some (a, m))
    (hw : Execution.Memory.writeBytes m.data (effectiveAddress i ao)
      (Execution.Memory.encodeLE (v.type.width / 8) v.bits.toNat) = some b) :
    Fires (simEnv10T (bytesB10 P)) "Step" 8 (.tuple [
      configV hn ⟨s, f, [value ⟨.int .i32, i⟩, value v, .source st]⟩,
      configV hn ⟨setMemory s a {m with data := b}, f, []⟩]) := by
  let w := Execution.Memory.encodeLE (v.type.width / 8) v.bits.toNat
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("t", valTypeV v.type), ("c", numV v), ("ao", memargV ao), ("b*", bytesV w)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Sim20.Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v.type) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV v) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fb : (VarEnv.empty.bindVals σ).findVal? "b*" = some (bytesV w) := rfl
  have hS' := envSame10T (bytesB10 P)
  have hsz : w.size = v.type.width / 8 := Execution.Memory.encodeLE_size _ _
  have hq : QuantsOk (simEnv10T (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (match storeNumValRule10 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ)
      (QuantsOk.cons fi (hasTypT (Whole.hasTyp_valNum10 ⟨.int .i32, i⟩
        Sim20.Pure.evalExp_caseNil))
      (QuantsOk.cons ft (hasTypT (Whole.typedV_valtype10 v.type _ hρ))
      (QuantsOk.cons fc (hasTypT (Whole.hasTyp_valNum10 v (Sim.evalExp_var ft)))
      (QuantsOk.cons fa (hasTypT (Whole.typedV_memarg10 ao _ hρ))
      (QuantsOk.cons fb (hasTypT (Whole.typedV_bytes10 w _ hρ)) QuantsOk.nil)))))
  have hb : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) (iterVar "b" "b*")
      (bytesV w) :=
    Equiv.Execution.evalExp_iterPat (by decide) fb
  have hj : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) (div8E sizeTE)
      (.num (.natN w.size)) := by
    rw [hsz]
    exact evalExp_div8 (evalExp_size10 v.type rfl (Sim.evalExp_var ft)) (width_cases v.type)
  have hwm : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)])),
        .expA (.binE .addOp (.numT .natT) iPay offE), .expA (div8E sizeTE),
        .expA (iterVar "b" "b*")]) (stateV hn (setMemory s a {m with data := b}) f) :=
    evalExp_withMem10 rfl (Sim.evalExp_var fz) evalExp_pct0'
      (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off10 fa))
      hj hb hm hw
  have hr : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E sizeTE), .expA (iterVar "b" "b*")], .listE []]))
      (configV hn ⟨setMemory s a {m with data := b}, f, []⟩) :=
    evalExp_case (evalExp_tup2 hwm (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))
  refine Sim20.Pure.fires_of_ruleAt (hasRuleAtT hasRuleAt10_storeNumVal') σ hq
    (evalExp_of hS' (evalExp_tup2 (evalExp_storeNumLhs10 hS fz fi ft fc fa) hr)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_of hS' (Sim20.Whole.evalExp_eqTrue hb
    (Whole.evalExp_bytesCall10 rfl ft fc)))

/-! ## Rule 10 -/

/-- `$ibytes_(n, $wrap__($size(Inn), n, c))`. -/
abbrev packBytesE10 : Exp :=
  .callE "ibytes_" [.expA (.varE "n"), .expA (.callE "wrap__" [.expA (.callE "size"
    [.expA innE10]), .expA (.varE "n"), .expA (.varE "c")])]

/-- `Step/store-pack-val` of 1.0, rule 10 of `Step` (verbatim). -/
def storePackValRule10 : Rule :=
  .ruleD "store-pack-val" [.expP "z" (.varT "state" []), .expP "i" Whole.valI32T',
    .expP "Inn" (.varT "Inn" []), .expP "c" (.varT "val_" [.expA innE10]),
    .expP "n" (.varT "n" []), .expP "ao" (.varT "memarg" []),
    .expP "b*" (.iterT (.varT "byte" []) .list)] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "CONST" (.tupE [innE10, .varE "c"]),
      .caseE "STORE" (.tupE [innE10, .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"])]]),
      .caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E (.varE "n")), .expA (iterVar "b" "b*")], .listE []])])
    [.ifPr (.cmpE .eqOp .boolT (iterVar "b" "b*") packBytesE10)]

theorem hasRuleAt10_storePackVal' : HasRuleAt (simEnv10 B) "Step" "%~>%" 10 storePackValRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The stored bytes of a pack store at `bytesB10`. -/
theorem evalExp_packBytes10 {P : Profile} {ρ : VarEnv} {t : IntType} {x : BitVec t.width}
    {sz : V1.PackSize} (fInn : ρ.findVal? "Inn" = some (valTypeV (.int t)))
    (fc : ρ.findVal? "c" = some (pctV x.toNat)) (fn : ρ.findVal? "n" = some (.num (.natN sz.width)))
    (hρ : ρ.findDef? "size" = none) (hρw : ρ.findDef? "wrap__" = none)
    (hρi : ρ.findDef? "ibytes_" = none) :
    EvalExp (simEnv10 (bytesB10 P)) ρ packBytesE10
      (bytesV (Execution.Memory.encodeLE (sz.width / 8) (x.setWidth sz.width).toNat)) := by
  have hs : EvalExp (simEnv10 (bytesB10 P)) ρ (.callE "size" [.expA innE10])
      (.num (.natN t.width)) :=
    evalExp_size10 (.int t) hρ (evalExp_subE_iff.2 (Sim.evalExp_var fInn))
  have hw : EvalExp (simEnv10 (bytesB10 P)) ρ (.callE "wrap__" [.expA (.callE "size"
      [.expA innE10]), .expA (.varE "n"), .expA (.varE "c")])
      (pctV (x.setWidth sz.width).toNat) := by
    obtain ⟨ps, ty, hd⟩ : ∃ ps ty, (simEnv10 (bytesB10 P)).findDef? "wrap__" = some (ps, ty, []) :=
      ⟨_, _, rfl⟩
    exact evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil hρw hd
      (evalArgs_cons hs (evalArgs_cons (Sim.evalExp_var fn) (evalArgs_cons (Sim.evalExp_var fc)
        evalArgs_nil)))
      (by rw [simEnv10, Env.builtins_withBuiltins]
          exact Whole.floatB_bytesB10 P _ _ _ (Sim.Floats.floatCall_wrap P t.width sz.width x)))
  obtain ⟨ps, ty, hd⟩ := Whole.findDef_ibytes10 (B := bytesB10 P)
  exact evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil hρi hd
    (evalArgs_cons (Sim.evalExp_var fn) (evalArgs_cons hw evalArgs_nil))
    (by rw [simEnv10, Env.builtins_withBuiltins, Whole.bytesB10_ibytes, Whole.ibytesCall10_pct]
        rfl))

/-- **`Step/store-pack-val` fires in `simEnv10T`** at `bytesB10`, at the image of V1's successful
packed `intStore`, from a state typed in `simEnv10T`. -/
theorem fires10T_storePackVal {P : Profile} {s : Store H} {f : Frame} {i : BitVec 32}
    {t : IntType} {x : BitVec t.width} {sz : V1.PackSize} {ao : V1.MemArg}
    {a : Execution.Runtime.MemAddr} {m : MemInst} {b : Execution.Memory.Bytes}
    (hz : TypedV (simEnv10T (bytesB10 P)) stateT (stateV hn s f))
    (hm : frameMemory s f = some (a, m))
    (hw : Execution.Memory.writeBytes m.data (effectiveAddress i ao)
      (Execution.Memory.encodeLE (sz.width / 8) (x.setWidth sz.width).toNat) = some b) :
    Fires (simEnv10T (bytesB10 P)) "Step" 10 (.tuple [
      configV hn ⟨s, f, [value ⟨.int .i32, i⟩, value ⟨.int t, x⟩,
        .source (.intStore t (some sz) ao)]⟩,
      configV hn ⟨setMemory s a {m with data := b}, f, []⟩]) := by
  let w := Execution.Memory.encodeLE (sz.width / 8) (x.setWidth sz.width).toNat
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("Inn", valTypeV (.int t)), ("c", pctV x.toNat), ("n", .num (.natN sz.width)),
    ("ao", memargV ao), ("b*", bytesV w)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Sim20.Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (valTypeV (.int t)) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fb : (VarEnv.empty.bindVals σ).findVal? "b*" = some (bytesV w) := rfl
  have hS' := envSame10T (bytesB10 P)
  have hsz : w.size = sz.width / 8 := Execution.Memory.encodeLE_size _ _
  have hq : QuantsOk (simEnv10T (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (match storePackValRule10 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ)
      (QuantsOk.cons fi (hasTypT (Whole.hasTyp_valNum10 ⟨.int .i32, i⟩
        Sim20.Pure.evalExp_caseNil))
      (QuantsOk.cons fInn (hasTypT (Whole.typedV_inn10 t _ hρ))
      (QuantsOk.cons fc (hasTypT (Whole.hasTyp_valNum10 ⟨.int t, x⟩
        (evalExp_subE_iff.2 (Sim.evalExp_var fInn))))
      (QuantsOk.cons fn (hasTypT (Whole.typedV_n10 _ _ hρ))
      (QuantsOk.cons fa (hasTypT (Whole.typedV_memarg10 ao _ hρ))
      (QuantsOk.cons fb (hasTypT (Whole.typedV_bytes10 w _ hρ)) QuantsOk.nil))))))
  have hb : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) (iterVar "b" "b*")
      (bytesV w) :=
    Equiv.Execution.evalExp_iterPat (by decide) fb
  have hj : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) (div8E (.varE "n"))
      (.num (.natN w.size)) := by
    rw [hsz]
    exact evalExp_div8 (Sim.evalExp_var fn) (packWidth10_cases sz)
  have hwm : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)])),
        .expA (.binE .addOp (.numT .natT) iPay offE), .expA (div8E (.varE "n")),
        .expA (iterVar "b" "b*")]) (stateV hn (setMemory s a {m with data := b}) f) :=
    evalExp_withMem10 rfl (Sim.evalExp_var fz) evalExp_pct0'
      (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off10 fa))
      hj hb hm hw
  have hr : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E (.varE "n")), .expA (iterVar "b" "b*")], .listE []]))
      (configV hn ⟨setMemory s a {m with data := b}, f, []⟩) :=
    evalExp_case (evalExp_tup2 hwm (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))
  refine Sim20.Pure.fires_of_ruleAt (hasRuleAtT hasRuleAt10_storePackVal') σ hq
    (evalExp_of hS' (evalExp_tup2 (evalExp_storePackLhs10 fz fi fInn fc fn fa) hr)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_of hS' (Sim20.Whole.evalExp_eqTrue hb
    (evalExp_packBytes10 fInn fc fn rfl rfl rfl)))

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
