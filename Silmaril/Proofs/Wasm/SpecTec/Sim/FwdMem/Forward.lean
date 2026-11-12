module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.StoreRules
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms

/-!
# Every scalar load and store, Core → SpecTec

The `MemoryStep` constructors `loadIntVal`, `loadPackVal`, `loadFloatVal`, `storeIntVal`,
`storePackVal`, `storeFloatOob`, `storeFloatVal`, forward, at `simEnv B`, for every address type
(`i32` and `i64` memories), every width and every packing. Each has the type of its case of
`Forward.memory`, plus

* `BytesFuns (simEnv B)` (`$nbytes_`, `$ibytes_`; proved for `Prims.builtins`),
* `Floats.FloatB P B` for the packed cases (`$extend__`, `$wrap__`),
* the slice side condition `SliceTotal ∨ ea + k < |bytes|` for the `-val` cases: until upstream
  item U2 the evaluator's slices need the strict bound, so the access that ends at the last
  byte of memory is excluded (obstruction 2); with `SliceTotal` nothing is excluded.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)
open Memory (MemTyping memAt_of_mem?)
open Silmaril.SpecTec.Equiv.RuntimeBridge (memInstToValue)

/-! ## Widths and bits -/

theorem width8_int (t : IntType) : 8 * (t.width / 8) = t.width := by cases t <;> rfl
theorem width8_float (t : FloatType) : 8 * (t.width / 8) = t.width := by cases t <;> rfl
theorem width8_pack (sz : PackSize) : 8 * (sz.width / 8) = sz.width := by cases sz <;> rfl

theorem toNat_setWidth_of_le {n w : Nat} (x : BitVec n) (h : n ≤ w) :
    (x.setWidth w).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt
    (Nat.pow_le_pow_right (by decide) h))]

@[simp] theorem memInstV_BYTES' (m : MemInst) :
    (memInstToValue m).field? "BYTES" = some (.list (bytesV m.bytes)) := rfl

theorem memInstV_setBytes (m : MemInst) (b : ByteArray) :
    (memInstToValue m).setField "BYTES" (.list (bytesV b)) =
      some (memInstToValue { m with bytes := b }) := by
  simp [memInstToValue, Equiv.RuntimeBridge.bytesToValue, bytesV, Value.setField,
    Silmaril.SpecTec.Equiv.Execution.pctV, percentV, caseV]

theorem storeV_setMem {H : Type} (hn : H → String) (s : Store H) (a : Nat) (m : MemInst) :
    (storeV hn s).setField "MEMS" (.list ((s.mems.map memInstToValue).set a (memInstToValue m))) =
      some (storeV hn (s.setMem a m)) := by
  simp [storeV, Store.setMem, List.map_set]

/-- The slice side condition. -/
theorem sliceAt_of_or {mi : MemInst} {ea k : Nat} (hT : SliceTotal ∨ ea + k < mi.bytes.size)
    (hle : ea + k ≤ mi.bytes.size) : SliceAt (bytesV mi.bytes) ea k :=
  hT.elim (fun h => sliceAt_of_total h (by rw [bytesV_length]; exact hle))
    (fun h => sliceAt_of_lt (by rw [bytesV_length]; exact h))

/-- `$size(Inn <: numtype)`, in a term-only scope. -/
theorem evalExp_sizeInn {B : Builtins} {ρ : VarEnv} (hρ : ∀ y, ρ.findDef? y = none) {t : IntType}
    (h : ρ.findVal? "Inn" = some (Encode.toValue (NumType.int t))) :
    EvalExp (simEnv B) ρ
      (.callE "size" [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))])
      (natV t.width) := by
  have he : EvalExp (simEnv B) ρ (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))
      (Encode.toValue (Memory.intAddr t)) :=
    Memory.toValue_int t ▸ RefsGC.evalExp_sub_of (evalExp_var h)
  have hs := State.evalExp_size (State.growDefs_simEnv B) (hρ _) (Memory.intAddr t) he
  rwa [Memory.width_toAddr] at hs

set_option maxRecDepth 100000 in
theorem noClauses_extend (B : Builtins) : IntNumeric.NoClauses (simEnv B) "extend__" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_wrap (B : Builtins) : IntNumeric.NoClauses (simEnv B) "wrap__" := ⟨_, _, rfl⟩

section Forward

variable {H : Type} (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B)) (M : MemTyping (simEnv B)) (Bf : BytesFuns (simEnv B))
include T St M Bf

/-- A value load, at a numeral `v` whose `k`-byte encoding is the loaded slice. -/
theorem fwd_loadNum {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {v : NumVal} {p : Instr}
    (hp : instrToV p = .case "LOAD" (.tuple [Encode.toValue v.type, .opt none,
      idxV x.toNat, memargV arg]))
    (hm : s.mem? f x = some (ma, mi)) (hle : effAddr i.toNat arg + v.type.width / 8 ≤ mi.bytes.size)
    (hT : SliceTotal ∨ effAddr i.toNat arg + v.type.width / 8 < mi.bytes.size)
    (hc : leBytesV (v.type.width / 8) v.bits.toNat =
      ((bytesV mi.bytes).drop (effAddr i.toNat arg)).take (v.type.width / 8))
    {a' : Admin} (ha' : adminToV a' = .case "CONST" (.tuple [Encode.toValue v.type, numV v])) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain p]⟩ ⟨s, f, [a']⟩ := by
  refine Memory.fwd_of_sread' T (hasStepRules_simEnv B).read fun hc' => ?_
  have hs := sread_loadNumVal St M Bf (State.hasReadRules_simEnv B).loadNumVal
    (State.typedV_state T hc') x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES' mi)
    (sliceAt_of_or hT hle) hc
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  show SRead _ (cfgV _ [_, instrToV p]) [adminToV a']
  rw [hp, ha']
  exact hs

/-- `MemoryStep.loadIntVal`, forward. -/
theorem fwd_loadIntVal {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    {c : BitVec (8 * (t.width / 8))}
    (hT : SliceTotal ∨ effAddr i.toNat arg + t.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) =
      some c) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t none x arg)]⟩
      ⟨s, f, [.plain (.intConst t (c.setWidth t.width))]⟩ := by
  obtain ⟨hle, hb⟩ := load_bytesV hl
  refine fwd_loadNum B T St M Bf (v := ⟨.int t, c.setWidth t.width⟩) rfl hm hle hT ?_ rfl
  show leBytesV (t.width / 8) (c.setWidth t.width).toNat = _
  rw [toNat_setWidth_of_le c (by rw [width8_int]), hb]
  rfl

/-- `MemoryStep.loadFloatVal`, forward. -/
theorem fwd_loadFloatVal {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    {c : BitVec (8 * (t.width / 8))}
    (hT : SliceTotal ∨ effAddr i.toNat arg + t.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) =
      some c) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.floatLoad t x arg)]⟩
      ⟨s, f, [.plain (.floatConst t (c.setWidth t.width))]⟩ := by
  obtain ⟨hle, hb⟩ := load_bytesV hl
  refine fwd_loadNum B T St M Bf (v := ⟨.float t, c.setWidth t.width⟩) rfl hm hle hT ?_ rfl
  show leBytesV (t.width / 8) (c.setWidth t.width).toNat = _
  rw [toNat_setWidth_of_le c (by rw [width8_float]), hb]
  rfl

include T St M Bf in
/-- A packed load whose loaded `k` extends to `r`. -/
theorem fwd_loadPack {P : Silmaril.Wasm.Numerics.Profile} (hF : Floats.FloatB P B)
    {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width}
    {ma : Nat} {mi : MemInst} (y : BitVec sz.width) (r : BitVec t.width)
    (hr : r = match sx with | .signed => y.signExtend t.width | .unsigned => y.setWidth t.width)
    (hm : s.mem? f x = some (ma, mi)) (hle : effAddr i.toNat arg + sz.width / 8 ≤ mi.bytes.size)
    (hT : SliceTotal ∨ effAddr i.toNat arg + sz.width / 8 < mi.bytes.size)
    (hc : leBytesV (sz.width / 8) y.toNat =
      ((bytesV mi.bytes).drop (effAddr i.toNat arg)).take (sz.width / 8)) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩
      ⟨s, f, [.plain (.intConst t r)]⟩ := by
  refine Memory.fwd_of_sread' T (hasStepRules_simEnv B).read fun hc' => ?_
  have hs := sread_loadPackVal (r := pctV r.toNat) St M Bf
    (State.hasReadRules_simEnv B).loadPackVal (State.typedV_state T hc') x.value.isLt
    (memAt_of_mem? hn hm) (memInstV_BYTES' mi) y.isLt (sliceAt_of_or hT hle) hc
    (fun σ hd hN hI hS hC => by
      subst hr
      exact evalExp_callE_iff.2 (Floats.callDef_floatPrim hF (noClauses_extend B) (hd _)
        (evalArgs_cons (evalExp_var hN) (evalArgs_cons (evalExp_sizeInn hd hI)
          (evalArgs_cons (evalExp_var hS) (evalArgs_cons (evalExp_var hC) evalArgs_nil))))
        (Floats.floatCall_extend P sz.width t.width sx y)))
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `MemoryStep.loadPackVal`, forward. -/
theorem fwd_loadPackVal {P : Silmaril.Wasm.Numerics.Profile} (hF : Floats.FloatB P B)
    {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width}
    {ma : Nat} {mi : MemInst} {c : BitVec (8 * (sz.width / 8))}
    (hT : SliceTotal ∨ effAddr i.toNat arg + sz.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (sz.width / 8) =
      some c) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩
      ⟨s, f, [.plain (.intConst t (match sx with
        | .signed => c.signExtend t.width
        | .unsigned => c.setWidth t.width))]⟩ := by
  obtain ⟨hle, hb⟩ := load_bytesV hl
  cases sz
  · exact fwd_loadPack (sz := .i8) B T St M Bf hF c _ rfl hm hle hT hb
  · exact fwd_loadPack (sz := .i16) B T St M Bf hF c _ rfl hm hle hT hb
  · exact fwd_loadPack (sz := .i32) B T St M Bf hF c _ rfl hm hle hT hb
  · exact fwd_loadPack (sz := .i64) B T St M Bf hF c _ rfl hm hle hT hb

omit T St M Bf in
/-- The stored image, for a store writing `b`. -/
theorem fwd_storeAux {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {b : ByteArray} {k : Nat}
    {ws : List Value} (hm : s.mem? f x = some (ma, mi))
    (hb : bytesV b = (bytesV mi.bytes).take (effAddr i.toNat arg) ++ ws ++
      (bytesV mi.bytes).drop (effAddr i.toNat arg + k)) :
    (∃ M' Ls As, (storeV hn s).field? "MEMS" = some (.list Ls) ∧
      (frameV f).field? "MODULE" = some M' ∧ M'.field? "MEMS" = some (.list As) ∧
      As[x.toNat]? = some (.num (.natN ma)) ∧ Ls[ma]? = some (memInstToValue mi) ∧
      (memInstToValue mi).setField "BYTES" (.list ((bytesV mi.bytes).take (effAddr i.toNat arg) ++
        ws ++ (bytesV mi.bytes).drop (effAddr i.toNat arg + k))) =
        some (memInstToValue { mi with bytes := b }) ∧
      (storeV hn s).setField "MEMS" (.list (Ls.set ma (memInstToValue { mi with bytes := b }))) =
        some (storeV hn (s.setMem ma { mi with bytes := b }))) := by
  obtain ⟨hma, hmi⟩ := Memory.Store.mem?_eq_some hm
  exact ⟨_, _, _, State.storeV_MEMS hn s, State.frameV_MODULE f, State.moduleV_MEMS _,
    State.getElem?_map_natN hma, by simp [hmi], hb ▸ memInstV_setBytes mi b,
    storeV_setMem hn s ma _⟩

/-- A value store of a numeral `v`. -/
theorem fwd_storeNum {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {v : NumVal} {b : ByteArray}
    {p q : Instr} (hq : instrToV q = .case "CONST" (.tuple [Encode.toValue v.type, numV v]))
    (hp : instrToV p = .case "STORE" (.tuple [Encode.toValue v.type, .opt none,
      idxV x.toNat, memargV arg]))
    (hm : s.mem? f x = some (ma, mi)) (hle : effAddr i.toNat arg + v.type.width / 8 ≤ mi.bytes.size)
    (hT : SliceTotal ∨ effAddr i.toNat arg + v.type.width / 8 < mi.bytes.size)
    (hb : bytesV b = (bytesV mi.bytes).take (effAddr i.toNat arg) ++
      leBytesV (v.type.width / 8) v.bits.toNat ++
      (bytesV mi.bytes).drop (effAddr i.toNat arg + v.type.width / 8)) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain q, .plain p]⟩
      ⟨s.setMem ma { mi with bytes := b }, f, []⟩ := by
  intro hc _
  obtain ⟨M', Ls, As, hS, hM, hA, ha, hmi, hm', hS'⟩ := fwd_storeAux (hn := hn) hm hb
  have hs := sstep_storeNumVal St M Bf
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.storeNumVal |> hasRuleAt_simEnv B)
    (State.typedV_state T hc) x.value.isLt hS hM hA ha hmi
    (memInstV_BYTES' mi) (sliceAt_of_or hT hle) hm' hS'
  rw [State.configV_eq, State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  show SStep _ (cfgV _ [_, instrToV q, instrToV p]) _
  rw [hq, hp]
  exact hs

/-- `MemoryStep.storeIntVal`, forward. -/
theorem fwd_storeIntVal {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {mi : MemInst}
    {b : ByteArray} (hT : SliceTotal ∨ effAddr i.toNat arg + t.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hs : Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr i.toNat arg)
      (count := t.width / 8) (c.setWidth _) = some b) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intConst t c), .plain (.intStore t none x arg)]⟩
      ⟨s.setMem ma { mi with bytes := b }, f, []⟩ := by
  obtain ⟨hle, hb⟩ := store_bytesV hs
  refine fwd_storeNum B T St M Bf (v := ⟨.int t, c⟩) rfl rfl hm hle hT ?_
  show _ = _ ++ leBytesV (t.width / 8) c.toNat ++ _
  rw [hb, toNat_setWidth_of_le c (by rw [width8_int])]
  rfl

/-- `MemoryStep.storeFloatVal`, forward. -/
theorem fwd_storeFloatVal {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {mi : MemInst}
    {b : ByteArray} (hT : SliceTotal ∨ effAddr i.toNat arg + t.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hs : Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr i.toNat arg)
      (count := t.width / 8) (c.setWidth _) = some b) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a i, .plain (.floatConst t c), .plain (.floatStore t x arg)]⟩
      ⟨s.setMem ma { mi with bytes := b }, f, []⟩ := by
  obtain ⟨hle, hb⟩ := store_bytesV hs
  refine fwd_storeNum B T St M Bf (v := ⟨.float t, c⟩) rfl rfl hm hle hT ?_
  show _ = _ ++ leBytesV (t.width / 8) c.toNat ++ _
  rw [hb, toNat_setWidth_of_le c (by rw [width8_float])]
  rfl

/-- `MemoryStep.storePackVal`, forward. -/
theorem fwd_storePackVal {P : Silmaril.Wasm.Numerics.Profile} (hF : Floats.FloatB P B)
    {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {x : MemIdx}
    {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat}
    {mi : MemInst} {b : ByteArray}
    (hT : SliceTotal ∨ effAddr i.toNat arg + sz.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hs : Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr i.toNat arg)
      (count := sz.width / 8) (c.setWidth _) = some b) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a i, .plain (.intConst t c), .plain (.intStore t (some sz) x arg)]⟩
      ⟨s.setMem ma { mi with bytes := b }, f, []⟩ := by
  intro hc _
  obtain ⟨hle, hb⟩ := store_bytesV hs
  have hk : (c.setWidth (8 * (sz.width / 8))).toNat = (c.setWidth sz.width).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, width8_pack]
  rw [hk] at hb
  obtain ⟨M', Ls, As, hS, hM, hA, ha, hmi, hm', hS'⟩ := fwd_storeAux (hn := hn) hm hb
  have hst := sstep_storePackVal (k := (c.setWidth sz.width).toNat) St M Bf
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.storePackVal |> hasRuleAt_simEnv B)
    (State.typedV_state T hc) x.value.isLt hS hM hA ha hmi (memInstV_BYTES' mi)
    (sliceAt_of_or hT hle) hm' hS'
    (fun σ hd hN hI hC => evalExp_callE_iff.2 (Floats.callDef_floatPrim hF (noClauses_wrap B) (hd _)
      (evalArgs_cons (evalExp_sizeInn hd hI) (evalArgs_cons (evalExp_var hN)
        (evalArgs_cons (evalExp_var hC) evalArgs_nil)))
      (Floats.floatCall_wrap P t.width sz.width c)))
  rw [State.configV_eq, State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil]
  rw [State.adminToV_aconst, Memory.adminToV_intConst]
  exact hst

omit Bf in
/-- `MemoryStep.storeFloatOob`, forward. -/
theorem fwd_storeFloatOob {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a i, .plain (.floatConst t c), .plain (.floatStore t x arg)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro hc _
  have hs := sstep_storeNumOob (v := ⟨.float t, c⟩) St M
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.storeNumOob |> hasRuleAt_simEnv B)
    (State.typedV_state T hc) x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES' mi)
    (by rw [bytesV_length]; exact h)
  rw [State.configV_eq, State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

end Forward

end Silmaril.Wasm.SpecTec.Sim.FwdMem
