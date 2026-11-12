module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadSplat

/-!
# Round 7, memory SIMD: `v128.loadN_lane`, in bounds (`Step_read` 51), forward

`Step_read/vload_lane-val`: `z; (CONST at i) (VCONST V128 c_1) (VLOAD_LANE V128 N x ao j) ~>
(VCONST V128 c)` under four premises:

* `$ibytes_(N, k) = $mem(z, x).BYTES[i + ao.OFFSET : N/8]`;
* `N = $jsize(Jnn)`;
* `M = $vsize(V128) / N`, over the rationals;
* `c = $inv_lanes_(Jnn X M, $lanes_(Jnn X M, c_1)[[j] = k])`.

`Jnn` and `M` are quantified and bound only by the premises; the declarative reading picks the
integer shape whose lane width is `N`. Core's `vecLoadLaneVal` loads `N/8` bytes and replaces lane
`j` of `c_1` with them.

* `fires_vloadLaneVal`: the rule fires, for arbitrary typed state values, given `$ibytes_`,
  `$lanes_` and `$inv_lanes_` on the relevant images.
* `fwd_vecLoadLane_shape`: **Core's `vecLoadLaneVal`, forward**, at an integer shape and an
  in-range lane (the validation side condition: SpecTec's list update is partial, Core's
  `List.set` is not), as a `Step_read` step in both readings at `withVBytes (Prims.builtins …)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateTyping)
open Memory (MemAt MemTyping memAt_of_mem?)
open FwdMem (leBytesV bytesV SliceAt)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-- `$vsize(V128)`, read over the rationals. -/
theorem evalExp_vsizeRat {B : Builtins} {σ : List (IL.Id × Value)} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]) .natT .ratT) (.num (.ratN 128)) :=
  evalExp_cvtE_iff.2 ⟨_, _, FwdMem.evalExp_call_applies (evalArgs_cons evalExp_v128 evalArgs_nil)
    FwdSimdAgg.applies_vsize, rfl, rfl⟩

/-! ## The rule, for arbitrary state values -/

section Rule

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))

include St M in
/-- **`Step_read/vload_lane-val`** (rule 51), at the integer shape `s` whose lane width is `N`:
lane `l` of the lanes `ls` of `c₁` is replaced by the loaded word `k`, and `$inv_lanes_` of the
result is `r`. -/
theorem fires_vloadLaneVal (s : IntShape) {S F m : Value} {bs ls : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {n k r : Nat} {arg : MemArg} {l : LaneIdx} {c₁ : BitVec 128}
    (hk : k < 2 ^ s.laneWidth) (hr : r < 2 ^ 128) (hl : l.val < ls.length)
    (hib : Applies (simEnv B) "ibytes_" [.val (.num (.natN s.laneWidth)), .val (pctV k)]
      (.list (leBytesV (s.laneWidth / 8) k)))
    (hla : Applies (simEnv B) "lanes_" [.val (Vec.ishV s), .val (pctV c₁.toNat)] (.list ls))
    (hinv : Applies (simEnv B) "inv_lanes_"
      [.val (Vec.ishV s), .val (.list (ls.set l.val (pctV k)))] (pctV r))
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hsl : SliceAt bs (i.toNat + arg.offset.val) (s.laneWidth / 8))
    (hc : leBytesV (s.laneWidth / 8) k = (bs.drop (i.toNat + arg.offset.val)).take
      (s.laneWidth / 8)) :
    Fires (simEnv B) "Step_read" 51 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vconstV c₁, vloadLaneV s.laneWidth n arg l.val],
      .list [.case "VCONST" (.tuple [caseNilV "V128", pctV r])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("c_1", pctV c₁.toNat), ("N", .num (.natN s.laneWidth)),
    ("x", idxV n), ("ao", memargV arg), ("j", pctV l.val), ("c", pctV r), ("k", pctV k),
    ("Jnn", Vec.intLaneV s), ("M", pctV s.lanes)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hw : s.laneWidth = 8 ∨ s.laneWidth = 16 ∨ s.laneWidth = 32 ∨ s.laneWidth = 64 := by
    cases s <;> simp [IntShape.laneWidth]
  have hcT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ)
      (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV r) := by
    have h := Typing.hasTyp_vec (B := B) (ρ := VarEnv.empty.bindVals σ) (BitVec.ofNat 128 r)
      evalExp_v128
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr] at h
  -- `$ibytes_(N, k)` is the slice.
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "ibytes_" [.expA (.varE "N"), .expA (.varE "k")])
      (.list (leBytesV (s.laneWidth / 8) k)) :=
    FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl)
      evalArgs_nil)) hib
  have e₂ := FwdMem.evalExp_memSlice (σ := σ) (ez := .varE "z") (ex := .varE "x")
    (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl) hm hB
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
    (Memory.evalExp_div8 (e := .varE "N") hw (evalExp_var rfl)) hsl
  rw [← hc] at e₂
  -- `N = $jsize(Jnn)` and `M = $vsize(V128) / N`.
  obtain ⟨p₂, p₃⟩ := evalExp_jsizeM (B := B) s rfl rfl rfl (Memory.findDef_bindVals_empty σ _)
    evalExp_vsizeRat
  -- `c = $inv_lanes_(Jnn X M, $lanes_(Jnn X M, c_1)[[j] = k])`.
  have eSh : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%X%" (.tupE
      [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])) (Vec.ishV s) :=
    evalExp_case (evalExp_tup2 (RefsGC.evalExp_sub_of (evalExp_var rfl)) (evalExp_var rfl))
  have eLanes := FwdMem.evalExp_call_applies (σ := σ) (args := [.expA (.caseE "%X%" (.tupE
      [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])),
      .expA (.varE "c_1")])
    (evalArgs_cons eSh (evalArgs_cons (evalExp_var rfl) evalArgs_nil)) hla
  have eK : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "%" (.tupE [.projE (.uncaseE (.varE "k") "%") 0])) (pctV k) :=
    evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons'
      (RefsGC.evalExp_unpct (evalExp_var rfl)) RefsGC.evalExps_nil'))
  have hs : (Value.list ls).setIdx l.val (pctV k) = some (.list (ls.set l.val (pctV k))) := by
    simp [Value.setIdx, hl]
  have eUpd : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.updE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" [])
        (.varT "lanetype" []), .varE "M"])), .expA (.varE "c_1")])
        (.idxP .rootP (.projE (.uncaseE (.varE "j") "%") 0))
        (.caseE "%" (.tupE [.projE (.uncaseE (.varE "k") "%") 0])))
      (.list (ls.set l.val (pctV k))) :=
    evalExp_updE_iff.2 ⟨_, _, eLanes, eK,
      Vec.pathSet_idxRoot (RefsGC.evalExp_unpct (evalExp_var (x := "j") rfl)) hs⟩
  have e₄ := FwdMem.evalExp_call_applies (σ := σ)
    (evalArgs_cons eSh (evalArgs_cons eUpd evalArgs_nil)) hinv
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadLaneVal σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.hasTyp_vec c₁ evalExp_v128)
          (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_N B) _ _ hρ)
            (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
              (QuantsOk.cons rfl (Round5.SimdTy.typedV_laneidx l _ hρ)
                (QuantsOk.cons rfl hcT (QuantsOk.cons rfl (FwdMem.hasTyp_iN_var rfl hk)
                  (QuantsOk.cons rfl (Round5.SimdTy.typedV_jnn s _ hρ)
                    (QuantsOk.cons rfl (Round5.SimdTy.typedV_M (.int s) _ hρ)
                      QuantsOk.nil))))))))))))
    (by mem_eval_tac)
    (prems_four (.ifPr (RefsGC.evalExp_eq_true e₁ e₂)) (.ifPr p₂) (.ifPr p₃)
      (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) e₄)))

end Rule

/-! ## Core's lane load, forward -/

section Forward

variable {H : Type} {hn : H → String}

/-- **The lanes of Core's lane replacement**: lane `j` set to `x`, the others kept. -/
theorem lanesV_setLane (s : IntShape) (v : BitVec 128) (j : Nat)
    (x : BitVec (Shape.int s).laneWidth) :
    Round5.Simd.lanesV (.int s) (Shape.invLanes (.int s) ((Shape.lanesOf (.int s) v).set j x)) =
      (Round5.Simd.lanesV (.int s) v).set j (pctV x.toNat) := by
  simp only [Round5.Simd.lanesV]
  rw [Shape.lanesOf_invLanes _ _ (by simp), List.map_set]
  rfl

/-- **`MemoryStep.vecLoadLaneVal`, forward**, at the integer shape `s` and an in-range lane: from
a typed state image, the in-bounds lane load is a `Step_read` step to Core's result, in both
readings, at `withVBytes (Prims.builtins …)`. -/
theorem fwd_vecLoadLane_shape {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (s : IntShape) {st : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {j : LaneIdx}
    {a : AddrType} {i : BitVec a.intType.width} {v : BitVec 128} {ma : Nat} {mi : MemInst}
    {k : BitVec (8 * (s.laneWidth / 8))} (hj : j.val < s.lanes)
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn st f))
    (hm : st.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (s.laneWidth / 8) =
      some k) :
    let r := Shape.invLanes (.int s) ((Shape.lanesOf (.int s) v).set j.val
      (k.setWidth (Shape.int s).laneWidth))
    SRead (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), valV (.vec v),
          Round6.MemSimd.instrToVM (.vecLoadLane (packOf s) x arg j)])
      [adminToV (.plain (.vecConst r))] ∧
      Round6.Reading.SReadB (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), valV (.vec v),
          Round6.MemSimd.instrToVM (.vecLoadLane (packOf s) x arg j)])
        [adminToV (.plain (.vecConst r))] := by
  intro r
  obtain ⟨hle, hb⟩ := FwdMem.load_bytesV hl
  have hw : 8 * (s.laneWidth / 8) = s.laneWidth := by cases s <;> rfl
  have hk : k.toNat < 2 ^ s.laneWidth := lt_of_lt_of_eq k.isLt (by rw [hw])
  have hkw : (k.setWidth (Shape.int s).laneWidth).toNat = k.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hk
  have hlen : j.val < (Round5.Simd.lanesV (.int s) v).length := by
    simpa [Round5.Simd.lanesV, Shape.lanesOf, Shape.lanes] using hj
  have hinv : Applies (simEnv (withVBytes (Prims.builtins P hn host))) "inv_lanes_"
      [.val (Vec.ishV s), .val (.list ((Round5.Simd.lanesV (.int s) v).set j.val
        (pctV k.toNat)))] (pctV r.toNat) := by
    have h := applies_invLanes_vb (P := P) (hn := hn) (host := host) (.int s) r
    rwa [lanesV_setLane, hkw] at h
  have hv : adminToV (.plain (.vecConst r)) =
      .case "VCONST" (.tuple [caseNilV "V128", pctV r.toNat]) := rfl
  rw [State.adminToV_aconst, instrToVM_vecLoadLane, hv, packOf_width]
  exact sread_of_fires loadTags_noCast (lhsIn_vloadLane _ _ _ _ _ _ _ _)
    (fires_vloadLaneVal (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _) s hk r.isLt
      hlen (applies_ibytes_vb _ _) (applies_lanes_vb s v) hinv hz x.value.isLt
      (memAt_of_mem? hn hm) (FwdMem.memInstV_BYTES' mi)
      (FwdMem.sliceAt_of_or (.inl FwdMem.sliceTotal) hle) hb)

end Forward

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
