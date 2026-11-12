module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.VStore
public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Thms

/-!
# Round 7, memory SIMD: `Step/vstore_lane-val` (25), forward

`z; (CONST at i) (VCONST V128 c) (VSTORE_LANE V128 N x ao j) ~>
$with_mem(z, x, i + ao.OFFSET, N/8, b*); ε`, with three premises:

* `N = $jsize(Jnn)`;
* `M = 128 / N`, over the rationals;
* `b* = $ibytes_(N, $lanes_(Jnn X M, c)[j])`.

`Jnn` and `M` are quantified and bound only by these premises. The declarative reading picks
them as the lane type and the lane count of the integer shape whose lane width is `N`.

* `sstep_vstoreLaneVal`: the rule fires for arbitrary typed state values, given `$lanes_` and
  `$ibytes_` on the relevant images.
* `fwd_vecStoreLaneVal`: **Core's `MemoryStep.vecStoreLaneVal`, forward**, at
  `withVBytes (Prims.builtins P hn host)`, for an in-range lane index (`j < 128 / N`). This is the
  validation side condition. Core's step uses `getD j 0`, so out of range it stores lane `0`,
  while SpecTec's indexing is partial there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.ExecStepRules (vstoreLaneValRule)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateTyping)
open Memory (MemAt MemTyping memAt_of_mem?)
open FwdMem (leBytesV bytesV SliceAt)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-- Three premises. -/
theorem prems_three {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr₁ pr₂ pr₃ : Prem}
    (h₁ : DPrem env O els ρ pr₁) (h₂ : DPrem env O els ρ pr₂) (h₃ : DPrem env O els ρ pr₃) :
    ∀ p ∈ [pr₁, pr₂, pr₃], DPrem env O els ρ p := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h₁
  · exact prems_two h₂ h₃ p hp

set_option maxRecDepth 100000 in
theorem findDef_jsize (B : Builtins) : ∃ ps t, (simEnv B).findDef? "jsize" = some (ps, t,
    [.defD [.expP "Jnn" (.varT "Jnn" [])] [.expA (.varE "Jnn")]
      (.callE "lsize" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))]) []]) :=
  ⟨_, _, rfl⟩

/-- **`$jsize(Jnn)` is the lane width.** -/
theorem applies_jsize {B : Builtins} (s : IntShape) :
    Applies (simEnv B) "jsize" [.val (Vec.intLaneV s)] (natV s.laneWidth) := by
  obtain ⟨ps, ty, hd⟩ := findDef_jsize B
  exact ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_varE (by simp))) matchArgs_nil) premsHold_nil (Vec.evalExp_call rfl
      (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var (by simp))) evalArgs_nil)
      (Round5.Simd.applies_lsize s)))⟩

/-- The lane count of an integer shape, as the rule computes it: `128 / N` over `ℚ`. -/
theorem lanes_rat (s : IntShape) :
    ((128 : ℚ) / (s.laneWidth : ℚ)) = ((s.lanes : Nat) : ℚ) := by
  cases s <;> norm_num [IntShape.laneWidth, IntShape.lanes]

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))

include St M in
/-- **`Step/vstore_lane-val`** (rule 25), at the integer shape `s` whose lane width is `N`. -/
theorem fires_vstoreLaneVal (s : IntShape) {ls : List Value} {k : Nat}
    (h : HasRuleAt (simEnv B) "Step" "%~>%" 25 vstoreLaneValRule)
    {S F M' m m' S' : Value} {Ls As bs : List Value} {ma : Nat} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {n : Nat} {arg : MemArg} {l : LaneIdx}
    (hla : Applies (simEnv B) "lanes_" [.val (Vec.ishV s), .val (pctV c.toNat)] (.list ls))
    (hk : ls[l.val]? = some (pctV k))
    (hib : Applies (simEnv B) "ibytes_" [.val (.num (.natN s.laneWidth)), .val (pctV k)]
      (.list (leBytesV (s.laneWidth / 8) k)))
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hS : S.field? "MEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M')
    (hA : M'.field? "MEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN ma)))
    (hm : Ls[ma]? = some m) (hB : m.field? "BYTES" = some (.list bs))
    (hsl : SliceAt bs (i.toNat + arg.offset.val) (s.laneWidth / 8))
    (hm' : m.setField "BYTES" (.list (bs.take (i.toNat + arg.offset.val) ++
      leBytesV (s.laneWidth / 8) k ++ bs.drop (i.toNat + arg.offset.val + s.laneWidth / 8))) =
      some m')
    (hS' : S.setField "MEMS" (.list (Ls.set ma m')) = some S') :
    Fires (simEnv B) "Step" 25 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vconstV c, vstoreLaneV s.laneWidth n arg l.val], cfgV (stV S' F) []]) := by
  let ws := leBytesV (s.laneWidth / 8) k
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("c", pctV c.toNat), ("N", .num (.natN s.laneWidth)), ("x", idxV n),
    ("ao", memargV arg), ("j", pctV l.val), ("b*", .list ws), ("Jnn", Vec.intLaneV s),
    ("M", pctV s.lanes)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hw : s.laneWidth = 8 ∨ s.laneWidth = 16 ∨ s.laneWidth = 32 ∨ s.laneWidth = 64 := by
    cases s <;> simp [IntShape.laneWidth]
  have hbT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.iterT (.varT "byte" []) .list)
      (.list ws) := FwdMem.hasTyp_bytes hρ _
  -- `N = $jsize(Jnn)`
  have p₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "N") (.callE "jsize" [.expA (.varE "Jnn")])) (.bool true) :=
    RefsGC.evalExp_eq_true (evalExp_var rfl) (FwdMem.evalExp_call_applies
      (evalArgs_cons (evalExp_var rfl) evalArgs_nil) (applies_jsize s))
  -- `M = 128 / N`
  have eM : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.projE (.uncaseE (.varE "M") "%") 0) .natT .ratT) (.num (.ratN (s.lanes : ℚ))) :=
    evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_unpct (evalExp_var rfl), rfl, rfl⟩
  have e128 : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cvtE (.numE (.natN 128)) .natT .ratT)
      (.num (.ratN 128)) := evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_num', rfl, rfl⟩
  have eN : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cvtE (.varE "N") .natT .ratT)
      (.num (.ratN (s.laneWidth : ℚ))) := evalExp_cvtE_iff.2 ⟨_, _, evalExp_var rfl, rfl, rfl⟩
  have hN0 : (s.laneWidth : ℚ) ≠ 0 := by cases s <;> norm_num [IntShape.laneWidth]
  have eDiv : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.binE .divOp (.numT .ratT)
      (.cvtE (.numE (.natN 128)) .natT .ratT) (.cvtE (.varE "N") .natT .ratT))
      (.num (.ratN (s.lanes : ℚ))) :=
    evalExp_binE_iff.2 ⟨_, e128, .inr ⟨rfl, _, eN, by
      simp only [binValues, Num.bin, hN0, ↓reduceIte, lanes_rat]; rfl⟩⟩
  have p₂ := RefsGC.evalExp_eq_true (t := .boolT) eM eDiv
  -- `b* = $ibytes_(N, $lanes_(Jnn X M, c)[j])`
  have eSh : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%X%" (.tupE
      [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])) (Vec.ishV s) :=
    evalExp_case (evalExp_tup2 (RefsGC.evalExp_sub_of (evalExp_var rfl)) (evalExp_var rfl))
  have eLanes := FwdMem.evalExp_call_applies (σ := σ) (args := [.expA (.caseE "%X%" (.tupE
      [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])), .expA (.varE "c")])
    (evalArgs_cons eSh (evalArgs_cons (evalExp_var rfl) evalArgs_nil)) hla
  have eLane := RefsGC.evalExp_unpct (RefsGC.evalExp_idx eLanes
    (RefsGC.evalExp_unpct (evalExp_var (x := "j") rfl)) hk)
  have eArg : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "%" (.tupE [.projE (.uncaseE (.idxE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE
        [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])),
        .expA (.varE "c")]) (.projE (.uncaseE (.varE "j") "%") 0)) "%") 0])) (pctV k) :=
    evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons' eLane RefsGC.evalExps_nil'))
  have e₃ := FwdMem.evalExp_call_applies (σ := σ)
    (evalArgs_cons (evalExp_var (ρ := VarEnv.empty.bindVals σ) (x := "N") rfl)
      (evalArgs_cons eArg evalArgs_nil)) hib
  have p₃ := RefsGC.evalExp_eq_true (t := .boolT)
    (Equiv.Execution.evalExp_iterPat (x := "b") (y := "b*") (by decide) rfl) e₃
  have ewm := FwdMem.evalExp_withMem (ez := .varE "z") (ex := .varE "x")
    (eb := State.iterVar "b" "b*") (State.stateDefs_simEnv B) (FwdMem.withMemDef_simEnv B)
    (Memory.findDef_bindVals_empty σ _) (evalExp_var rfl) (evalExp_var rfl)
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
    (Memory.evalExp_div8 hw (evalExp_var (x := "N") rfl))
    (Equiv.Execution.evalExp_iterPat (by decide) rfl) hS hM hA ha hm hB (hsl.2 ws) hm' hS'
  exact fires_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.hasTyp_vec c evalExp_v128)
          (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_N B) _ _ hρ)
            (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
              (QuantsOk.cons rfl (Round5.SimdTy.typedV_laneidx l _ hρ)
                (QuantsOk.cons rfl hbT (QuantsOk.cons rfl (Round5.SimdTy.typedV_jnn s _ hρ)
                  (QuantsOk.cons rfl (Round5.SimdTy.typedV_M (.int s) _ hρ)
                    QuantsOk.nil)))))))))))
    (evalExp_tup2 (by mem_eval_tac) (evalExp_case (evalExp_tup2 ewm
      (RefsGC.evalExp_listE_of RefsGC.evalExps_nil'))))
    (prems_three (.ifPr p₁) (.ifPr p₂) (.ifPr p₃))

/-! ## Core's in-bounds lane store, forward -/

/-- The pack size of an integer shape's lanes. -/
def packOf : IntShape → PackSize
  | .i8x16 => .i8
  | .i16x8 => .i16
  | .i32x4 => .i32
  | .i64x2 => .i64

theorem packOf_width (s : IntShape) : (packOf s).width = s.laneWidth := by cases s <;> rfl

variable {H : Type} {hn : H → String}

/-- The lanes the concrete primitives give. -/
theorem applies_lanes_vb {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (s : IntShape) (c : BitVec 128) :
    Applies (simEnv (withVBytes (Prims.builtins P hn host))) "lanes_"
      [.val (Vec.ishV s), .val (pctV c.toNat)] (.list (Round5.Simd.lanesV (.int s) c)) :=
  Prims.applies_of_noClause (Round5.Simd.findDef_lanes _)
    (((show (withVBytes (Prims.builtins P hn host)).call "lanes_" _ =
        (Prims.builtins P hn host).call "lanes_" _ by simp [withVBytes]; rfl).trans
      (Round5.Simd.call_lanes P hn host _ _)).trans (Round5.Simd.lanesCall_eq (.int s) c))

/-- `$ibytes_` at the concrete primitives. -/
theorem applies_ibytes_vb {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (N k : Nat) :
    Applies (simEnv (withVBytes (Prims.builtins P hn host))) "ibytes_"
      [.val (.num (.natN N)), .val (pctV k)] (.list (leBytesV (N / 8) k)) :=
  Prims.applies_of_noClause (FwdMem.findDef_ibytes _)
    ((show (withVBytes (Prims.builtins P hn host)).call "ibytes_"
          [.val (.num (.natN N)), .val (pctV k)] =
        (Prims.builtins P hn host).call "ibytes_" [.val (.num (.natN N)), .val (pctV k)] by
          simp [withVBytes]).trans (by
      simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames,
        FwdMem.ibytesCall, Silmaril.SpecTec.Equiv.Execution.pctV]))

/-- **`MemoryStep.vecStoreLaneVal`, forward**, at an integer shape `s`, for an in-range lane. -/
theorem fwd_vecStoreLaneVal_shape {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (s : IntShape) {st : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {j : LaneIdx}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128} {ma : Nat} {mi : MemInst}
    {b : ByteArray} (hj : j.val < s.lanes)
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn st f))
    (hm : st.mem? f x = some (ma, mi))
    (hs : Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr i.toNat arg)
      (count := s.laneWidth / 8)
      (((Silmaril.Wasm.Numerics.lanes s.laneWidth s.lanes c).getD j.val 0).setWidth _) = some b) :
    SStep (simEnv (withVBytes (Prims.builtins P hn host)))
      (cfgV (stateV hn st f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane (packOf s) x arg j)])
      (cfgV (stateV hn (st.setMem ma { mi with bytes := b }) f) []) ∧
    (Round6.Int.backend).step (withVBytes (Prims.builtins P hn host))
      (cfgV (stateV hn st f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane (packOf s) x arg j)])
      (cfgV (stateV hn (st.setMem ma { mi with bytes := b }) f) []) := by
  obtain ⟨hle, hb⟩ := FwdMem.store_bytesV hs
  rw [FwdMem.toNat_setWidth_of_le _ (by cases s <;> decide)] at hb
  obtain ⟨M', Ls, As, hS, hM, hA, ha, hmi, hm', hS'⟩ := FwdMem.fwd_storeAux (hn := hn) hm hb
  rw [State.adminToV_aconst, instrToVM_vecStoreLane, packOf_width]
  exact both_of_fires (by decide) <| fires_vstoreLaneVal (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _) s
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreLaneVal |> hasRuleAt_simEnv _)
    (applies_lanes_vb s c) (Round5.Simd.getElem?_lanesV (.int s) c hj) (applies_ibytes_vb _ _)
    hz x.value.isLt hS hM hA ha hmi (FwdMem.memInstV_BYTES' mi)
    (FwdMem.sliceAt_of_or (.inl FwdMem.sliceTotal) hle) hm' hS'

/-- **`MemoryStep.vecStoreLaneVal`, forward**, in Core's own terms, for a lane index within the
lane count (`128 / N`). -/
theorem fwd_vecStoreLaneVal {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {st : Store H} {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg} {j : LaneIdx}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128} {ma : Nat} {mi : MemInst}
    {b : ByteArray} (hj : j.val < 128 / sz.width)
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn st f))
    (hm : st.mem? f x = some (ma, mi))
    (hs : Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr i.toNat arg)
      (count := sz.width / 8)
      (((Silmaril.Wasm.Numerics.lanes sz.width (128 / sz.width) c).getD j.val 0).setWidth _) =
      some b) :
    SStep (simEnv (withVBytes (Prims.builtins P hn host)))
      (cfgV (stateV hn st f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)])
      (cfgV (stateV hn (st.setMem ma { mi with bytes := b }) f) []) ∧
    (Round6.Int.backend).step (withVBytes (Prims.builtins P hn host))
      (cfgV (stateV hn st f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)])
      (cfgV (stateV hn (st.setMem ma { mi with bytes := b }) f) []) := by
  cases sz
  · exact fwd_vecStoreLaneVal_shape .i8x16 hj hz hm hs
  · exact fwd_vecStoreLaneVal_shape .i16x8 hj hz hm hs
  · exact fwd_vecStoreLaneVal_shape .i32x4 hj hz hm hs
  · exact fwd_vecStoreLaneVal_shape .i64x2 hj hz hm hs

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
