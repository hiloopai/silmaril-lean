module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.BackwardLane

/-!
# Round 7, memory SIMD: the out-of-bounds vector loads (`Step_read` 42, 44, 46, 48, 50), forward

Each out-of-bounds load rule traps when `i + ao.OFFSET + w/8` exceeds the memory's length, where
the access width `w` is read off the instruction:

| rule | instruction | `w` | Core |
| --- | --- | --- | --- |
| 42 `vload-num-oob` | `VLOAD V128 ε x ao` | `$vsize(V128) = 128` | `vecLoadOob`, `.full` |
| 44 `vload-pack-oob` | `VLOAD V128 (SHAPE K X M _ sx) x ao` | `K * M = 64` | `vecLoadOob`, `.extend…` |
| 46 `vload-splat-oob` | `VLOAD V128 (SPLAT N) x ao` | `N` | `vecLoadOob`, `.splat` |
| 48 `vload-zero-oob` | `VLOAD V128 (ZERO N) x ao` | `N ∈ {32, 64}` | `vecLoadOob`, `.zero…` |
| 50 `vload_lane-oob` | `VLOAD_LANE V128 N x ao j` | `N` | `vecLoadLaneOob` |

The loads are encoded by round 6's `instrToVM` (`instrToVM_vecLoad`, `instrToVM_vecLoadLane`).

* `fires_vloadOob`, `fires_vloadLaneOob`: the rules fire, for arbitrary typed state values.
* `fwd_vecLoadOob`, `fwd_vecLoadLaneOob`: **Core's `vecLoadOob`/`vecLoadLaneOob`, forward**, as
  `Step_read` steps in both readings (`SRead`, and round 6's `SReadB`, which agrees with it away
  from the cast constructors, `Round6.Reading.sReadB_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead (vloadNumOobRule vloadPackOobRule vloadSplatOobRule
  vloadZeroOobRule vloadLaneOobRule)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateTyping)
open Memory (MemAt MemTyping memAt_of_mem?)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-! ## The encoded loads -/

/-- The `VLOAD V128 op? x ao` instruction. -/
abbrev vloadV (o : Option Value) (n : Nat) (arg : MemArg) : Value :=
  .case "VLOAD" (.tuple [caseNilV "V128", .opt o, idxV n, memargV arg])

/-- The `VLOAD_LANE V128 N x ao j` instruction. -/
abbrev vloadLaneV (w n : Nat) (arg : MemArg) (j : Nat) : Value :=
  .case "VLOAD_LANE" (.tuple [caseNilV "V128", pctV w, idxV n, memargV arg, pctV j])

theorem instrToVM_vecLoad (op : VecLoadOp) (x : MemIdx) (arg : MemArg) :
    Round6.MemSimd.instrToVM (.vecLoad op x arg) =
      vloadV (Round6.MemSimd.vecLoadOpV op) x.toNat arg := rfl

theorem instrToVM_vecLoadLane (p : PackSize) (x : MemIdx) (arg : MemArg) (l : LaneIdx) :
    Round6.MemSimd.instrToVM (.vecLoadLane p x arg l) = vloadLaneV p.width x.toNat arg l.val :=
  rfl

/-! ## Typing the rules' quantifiers -/

set_option maxRecDepth 100000 in
theorem findTyp_K (B : Builtins) :
    (simEnv B).findTyp? "K" = some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

/-- A `Step_read` rule that fires is a `Step_read` step, in both readings, at a left-hand side
naming no cast constructor. -/
theorem sread_of_fires {B : Builtins} {k : Nat} {S : List MixopS}
    (hS : ∀ op ∈ Round6.Reading.castTags, op ∉ S) {a : Value} {js : List Value}
    (ha : RefsGC.LhsIn S a) (hf : Fires (simEnv B) "Step_read" k (.tuple [a, .list js])) :
    SRead (simEnv B) a js ∧ Round6.Reading.SReadB (simEnv B) a js := by
  obtain ⟨t, rules, hrel⟩ := Round6.Reading.findRel_read B
  have hr : SRead (simEnv B) a js := (dderives_iff_fires hrel).2 ⟨k, hf⟩
  exact ⟨hr, (Round6.Reading.sReadB_iff B hS ha).2 hr⟩

/-- The tags of a vector load's left-hand side. -/
def loadTags : List MixopS := ["CONST", "VCONST", "VLOAD", "VLOAD_LANE"]

theorem loadTags_noCast : ∀ op ∈ Round6.Reading.castTags, op ∉ loadTags := by decide

/-- `CONST at i; VLOAD …` names no cast constructor. -/
theorem lhsIn_vload (z : Value) (A : Value) (I : Nat) (o : Option Value) (n : Nat)
    (arg : MemArg) : RefsGC.LhsIn loadTags (cfgV z [aconstV A I, vloadV o n arg]) :=
  .inr ⟨z, _, rfl, fun x hx op w he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> cases he <;> decide⟩

/-- `CONST at i; VCONST V128 c; VLOAD_LANE …` names no cast constructor. -/
theorem lhsIn_vloadLane (z : Value) (A : Value) (I : Nat) (c : BitVec 128) (w n : Nat)
    (arg : MemArg) (j : Nat) :
    RefsGC.LhsIn loadTags (cfgV z [aconstV A I, vconstV c, vloadLaneV w n arg j]) :=
  .inr ⟨z, _, rfl, fun x hx op w he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> cases he <;> decide⟩

/-! ## The rules, for arbitrary state values -/

section Rules

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))

/-- The common premise of the out-of-bounds loads: `i + ao.OFFSET + w/8 > |$mem(z, x).BYTES|`. -/
theorem evalExp_oobPrem {σ : List (IL.Id × Value)} {ew : Exp} {S F m : Value} {bs : List Value}
    {I n k : Nat} {arg : MemArg}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV S F))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV n))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (hw : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) ew (.num (.natN k)))
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < I + arg.offset.val + k) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT) (.binE .addOp
      (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)) ew)
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")))
      (.bool true) :=
  RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat (Memory.evalExp_effAddr (evalExp_var fi)
    (evalExp_var fao)) hw)
    (Memory.evalExp_memBytesLen (State.stateDefs_simEnv B) (evalExp_var fz) (evalExp_var fx) hm
      hB) hoob

include St M in
/-- **`Step_read/vload-num-oob`** (rule 42). -/
theorem fires_vloadNumOob {S F m : Value} {bs : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {n : Nat} {arg : MemArg}
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs)) (hoob : bs.length < i.toNat + arg.offset.val + 16) :
    Fires (simEnv B) "Step_read" 42 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vloadV none n arg], .list [.case "TRAP" (.tuple [])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadNumOob σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (St.idx n hn _ hρ)
        (QuantsOk.cons rfl (M.memarg arg _ hρ) QuantsOk.nil)))))
    (by mem_eval_tac)
    (prems_one (.ifPr (evalExp_oobPrem rfl rfl rfl rfl evalExp_vsize8 hm hB hoob)))

include St M in
/-- **`Step_read/vload-pack-oob`** (rule 44), at `K X M` with `K * M = 64`. -/
theorem fires_vloadPackOob (sh : Shape) (k : Nat) (hk : k * sh.lanes = 64) (sx : Signedness)
    {S F m : Value} {bs : List Value} {a : AddrType} {i : BitVec a.intType.width} {n : Nat}
    {arg : MemArg} (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + 8) :
    Fires (simEnv B) "Step_read" 44 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vloadV (some (.case "SHAPE%X%_%" (.tuple [pctV k, pctV sh.lanes, Vec.sxV sx]))) n arg],
      .list [.case "TRAP" (.tuple [])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("K", .num (.natN k)), ("M", pctV sh.lanes), ("sx", Vec.sxV sx),
    ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hw : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cvtE (.binE .divOp (.numT .ratT)
      (.cvtE (.binE .mulOp (.numT .natT) (.varE "K") (.projE (.uncaseE (.varE "M") "%") 0))
        .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN 8)) :=
    Memory.evalExp_div8 (w := 64) (by decide)
      (hk ▸ RefsGC.evalExp_mulNat (evalExp_var rfl) (RefsGC.evalExp_unpct (evalExp_var rfl)))
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadPackOob σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_K B) _ _ hρ)
          (QuantsOk.cons rfl (Round5.SimdTy.typedV_M sh _ hρ)
            (QuantsOk.cons rfl (ConfigOk.typedV_sx sx _ hρ) (QuantsOk.cons rfl (St.idx n hn _ hρ)
              (QuantsOk.cons rfl (M.memarg arg _ hρ) QuantsOk.nil))))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (evalExp_oobPrem rfl rfl rfl rfl hw hm hB hoob)))

include St M in
/-- **`Step_read/vload-splat-oob`** (rule 46). -/
theorem fires_vloadSplatOob (p : PackSize) {S F m : Value} {bs : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {n : Nat} {arg : MemArg}
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + p.width / 8) :
    Fires (simEnv B) "Step_read" 46 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vloadV (some (.case "SPLAT" (szV p))) n arg], .list [.case "TRAP" (.tuple [])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("N", .num (.natN p.width)), ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hw8 : p.width = 8 ∨ p.width = 16 ∨ p.width = 32 ∨ p.width = 64 := by
    cases p <;> simp [PackSize.width]
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadSplatOob σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_N B) _ _ hρ)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            QuantsOk.nil))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (evalExp_oobPrem rfl rfl rfl rfl
      (Memory.evalExp_div8 hw8 (evalExp_var rfl)) hm hB hoob)))

include St M in
/-- **`Step_read/vload-zero-oob`** (rule 48), at `N ∈ {32, 64}`. -/
theorem fires_vloadZeroOob (N : Nat) (hN : N = 32 ∨ N = 64) {S F m : Value} {bs : List Value}
    {a : AddrType} {i : BitVec a.intType.width} {n : Nat} {arg : MemArg}
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + N / 8) :
    Fires (simEnv B) "Step_read" 48 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vloadV (some (.case "ZERO" (.tuple [pctV N]))) n arg],
      .list [.case "TRAP" (.tuple [])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("N", .num (.natN N)), ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadZeroOob σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_N B) _ _ hρ)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            QuantsOk.nil))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (evalExp_oobPrem rfl rfl rfl rfl
      (Memory.evalExp_div8 (by omega) (evalExp_var rfl)) hm hB hoob)))

include St M in
/-- **`Step_read/vload_lane-oob`** (rule 50). -/
theorem fires_vloadLaneOob (p : PackSize) (l : LaneIdx) (c : BitVec 128) {S F m : Value}
    {bs : List Value} {a : AddrType} {i : BitVec a.intType.width} {n : Nat} {arg : MemArg}
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + p.width / 8) :
    Fires (simEnv B) "Step_read" 50 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vconstV c, vloadLaneV p.width n arg l.val], .list [.case "TRAP" (.tuple [])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("c_1", pctV c.toNat), ("N", .num (.natN p.width)), ("x", idxV n),
    ("ao", memargV arg), ("j", pctV l.val)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hw8 : p.width = 8 ∨ p.width = 16 ∨ p.width = 32 ∨ p.width = 64 := by
    cases p <;> simp [PackSize.width]
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadLaneOob σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.hasTyp_vec c evalExp_v128)
          (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_N B) _ _ hρ)
            (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
              (QuantsOk.cons rfl (Round5.SimdTy.typedV_laneidx l _ hρ) QuantsOk.nil))))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (evalExp_oobPrem rfl rfl rfl rfl
      (Memory.evalExp_div8 hw8 (evalExp_var rfl)) hm hB hoob)))

end Rules

/-! ## Core's out-of-bounds vector loads, forward -/

section Core

variable {B : Builtins} {H : Type} {hn : H → String}

/-- The bound of an out-of-bounds load, on the encoded memory. -/
theorem oob_bytesL {mi : MemInst} {I k : Nat} {arg : MemArg}
    (h : mi.bytes.size < effAddr I arg + k) :
    (Memory.bytesL mi.bytes).length < I + arg.offset.val + k := by
  simpa [effAddr] using h

/-- The `Fires` half of `fwd_vecLoadOob`, by the load's shape. -/
theorem fires_vecLoadOob {s : Store H} {f : Frame} {op : VecLoadOp} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (h : mi.bytes.size < effAddr i.toNat arg + op.accessWidth / 8) :
    ∃ k, Fires (simEnv B) "Step_read" k (.tuple [cfgV (stateV hn s f)
      [aconstV (Encode.toValue a) i.toNat, vloadV (Round6.MemSimd.vecLoadOpV op) x.toNat arg],
      .list [.case "TRAP" (.tuple [])]]) := by
  have St := Typing.stateTyping_simEnv B
  have M := ConfigOk.memTyping_simEnv B
  have hmA := memAt_of_mem? hn hm
  have hl := oob_bytesL h
  cases op with
  | full => exact ⟨_, fires_vloadNumOob St M hz x.value.isLt hmA (Memory.memInstV_BYTES mi) hl⟩
  | extend8x8 sx => exact ⟨_, fires_vloadPackOob St M (.int .i16x8) 8 rfl sx hz x.value.isLt
      hmA (Memory.memInstV_BYTES mi) (by simpa [VecLoadOp.accessWidth] using hl)⟩
  | extend16x4 sx => exact ⟨_, fires_vloadPackOob St M (.int .i32x4) 16 rfl sx hz x.value.isLt
      hmA (Memory.memInstV_BYTES mi) (by simpa [VecLoadOp.accessWidth] using hl)⟩
  | extend32x2 sx => exact ⟨_, fires_vloadPackOob St M (.int .i64x2) 32 rfl sx hz x.value.isLt
      hmA (Memory.memInstV_BYTES mi) (by simpa [VecLoadOp.accessWidth] using hl)⟩
  | splat p => exact ⟨_, fires_vloadSplatOob St M p hz x.value.isLt hmA
      (Memory.memInstV_BYTES mi) hl⟩
  | zero32 => exact ⟨_, fires_vloadZeroOob St M 32 (.inl rfl) hz x.value.isLt hmA
      (Memory.memInstV_BYTES mi) hl⟩
  | zero64 => exact ⟨_, fires_vloadZeroOob St M 64 (.inr rfl) hz x.value.isLt hmA
      (Memory.memInstV_BYTES mi) hl⟩

/-- **`MemoryStep.vecLoadOob`, forward**: from a typed state image, the out-of-bounds vector load
(encoded by `instrToVM`) traps in `Step_read`, in both readings. -/
theorem fwd_vecLoadOob {s : Store H} {f : Frame} {op : VecLoadOp} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (h : mi.bytes.size < effAddr i.toNat arg + op.accessWidth / 8) :
    SRead (simEnv B) (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad op x arg)]) [adminToV .trap] ∧
      Round6.Reading.SReadB (simEnv B) (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad op x arg)]) [adminToV .trap] := by
  rw [State.adminToV_aconst, instrToVM_vecLoad]
  obtain ⟨k, hf⟩ := fires_vecLoadOob hz hm h
  exact sread_of_fires loadTags_noCast (lhsIn_vload _ _ _ _ _ _) hf

/-- **`MemoryStep.vecLoadLaneOob`, forward.** -/
theorem fwd_vecLoadLaneOob {s : Store H} {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg}
    {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width} {v : BitVec 128} {ma : Nat}
    {mi : MemInst} (hz : TypedV (simEnv B) stateT (stateV hn s f))
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
    SRead (simEnv B) (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec v),
        Round6.MemSimd.instrToVM (.vecLoadLane sz x arg j)]) [adminToV .trap] ∧
      Round6.Reading.SReadB (simEnv B) (cfgV (stateV hn s f) [adminToV (aconst a i),
        valV (.vec v), Round6.MemSimd.instrToVM (.vecLoadLane sz x arg j)]) [adminToV .trap] := by
  rw [State.adminToV_aconst, instrToVM_vecLoadLane]
  exact sread_of_fires loadTags_noCast (lhsIn_vloadLane _ _ _ _ _ _ _ _)
    (fires_vloadLaneOob (Typing.stateTyping_simEnv B) (ConfigOk.memTyping_simEnv B) sz j v hz
      x.value.isLt (memAt_of_mem? hn hm) (Memory.memInstV_BYTES mi) (oob_bytesL h))

end Core

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
