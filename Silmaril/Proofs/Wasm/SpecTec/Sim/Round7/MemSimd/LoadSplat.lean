module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadZero
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms

/-!
# Round 7, memory SIMD: `v128.loadN_splat`, in bounds (`Step_read` 47), forward

`Step_read/vload-splat-val`: `z; (CONST at i) (VLOAD V128 (SPLAT N) x ao) ~> (VCONST V128 c)`
under four premises:

* `$ibytes_(N, j) = $mem(z, x).BYTES[i + ao.OFFSET : N/8]`;
* `N = $jsize(Jnn)`;
* `M = 128 / N`, over the rationals;
* `c = $inv_lanes_(Jnn X M, j^M)` (the iteration `%(j.0)^M` has no domain).

`Jnn` and `M` are quantified and bound only by the premises; the declarative reading picks the
integer shape whose lane width is `N`. Core's `vecLoadVal` at `.splat sz` loads `sz.width / 8`
bytes and repeats the word in every lane (`vecLoadResult`).

* `lanesV_splat`: the lanes of Core's splat are the loaded word, `M` times.
* `fires_vloadSplatVal`: the rule fires, for arbitrary typed state values, given `$ibytes_` and
  `$inv_lanes_` on the relevant images.
* `fwd_vecLoadSplat`: **Core's `vecLoadVal` at `.splat sz`, forward**, as a `Step_read` step in
  both readings, at `withVBytes (Prims.builtins …)`.
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
open Silmaril.Wasm.Numerics (invLanes)
open State (aconstV idxV StateTyping)
open Memory (MemAt MemTyping memAt_of_mem?)
open FwdMem (leBytesV bytesV SliceAt)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-- Four premises. -/
theorem prems_four {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr₁ pr₂ pr₃ pr₄ : Prem}
    (h₁ : DPrem env O els ρ pr₁) (h₂ : DPrem env O els ρ pr₂) (h₃ : DPrem env O els ρ pr₃)
    (h₄ : DPrem env O els ρ pr₄) :
    ∀ p ∈ [pr₁, pr₂, pr₃, pr₄], DPrem env O els ρ p := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h₁
  · exact prems_three h₂ h₃ h₄ p hp

/-- The premises `N = $jsize(Jnn)` and `M = rhs / N` (over `ℚ`), at the integer shape `s` whose
lane width is `N`, for any `rhs` that evaluates to `128`. -/
theorem evalExp_jsizeM {B : Builtins} {ρ : VarEnv} (s : IntShape) {e128 : Exp}
    (fN : ρ.findVal? "N" = some (.num (.natN s.laneWidth)))
    (fJ : ρ.findVal? "Jnn" = some (Vec.intLaneV s)) (fM : ρ.findVal? "M" = some (pctV s.lanes))
    (hd : ρ.findDef? "jsize" = none)
    (h128 : EvalExp (simEnv B) ρ e128 (.num (.ratN 128))) :
    EvalExp (simEnv B) ρ
        (.cmpE .eqOp .boolT (.varE "N") (.callE "jsize" [.expA (.varE "Jnn")])) (.bool true) ∧
      EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.cvtE (.projE (.uncaseE (.varE "M") "%") 0)
        .natT .ratT) (.binE .divOp (.numT .ratT) e128 (.cvtE (.varE "N") .natT .ratT)))
        (.bool true) := by
  refine ⟨RefsGC.evalExp_eq_true (evalExp_var fN) (evalExp_callE_iff.2
    ((Silmaril.SpecTec.Equiv.ExecNumeric.applies_iff_callDef hd
      (evalArgs_cons (evalExp_var fJ) evalArgs_nil)).1 (applies_jsize s))), ?_⟩
  have eM : EvalExp (simEnv B) ρ (.cvtE (.projE (.uncaseE (.varE "M") "%") 0) .natT .ratT)
      (.num (.ratN (s.lanes : ℚ))) :=
    evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_unpct (evalExp_var fM), rfl, rfl⟩
  have eN : EvalExp (simEnv B) ρ (.cvtE (.varE "N") .natT .ratT)
      (.num (.ratN (s.laneWidth : ℚ))) := evalExp_cvtE_iff.2 ⟨_, _, evalExp_var fN, rfl, rfl⟩
  have hN0 : (s.laneWidth : ℚ) ≠ 0 := by cases s <;> norm_num [IntShape.laneWidth]
  have eDiv : EvalExp (simEnv B) ρ (.binE .divOp (.numT .ratT) e128
      (.cvtE (.varE "N") .natT .ratT)) (.num (.ratN (s.lanes : ℚ))) :=
    evalExp_binE_iff.2 ⟨_, h128, .inr ⟨rfl, _, eN, by
      simp only [binValues, Num.bin, hN0, ↓reduceIte, lanes_rat]; rfl⟩⟩
  exact RefsGC.evalExp_eq_true (t := .boolT) eM eDiv

/-! ## The rule, for arbitrary state values -/

section Rule

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))

include St M in
/-- **`Step_read/vload-splat-val`** (rule 47), at the integer shape `s` whose lane width is `N`:
the loaded word `k` is repeated in every lane, and `$inv_lanes_` gives `r`. -/
theorem fires_vloadSplatVal (s : IntShape) {S F m : Value} {bs : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {n k r : Nat} {arg : MemArg} (hk : k < 2 ^ s.laneWidth)
    (hr : r < 2 ^ 128)
    (hib : Applies (simEnv B) "ibytes_" [.val (.num (.natN s.laneWidth)), .val (pctV k)]
      (.list (leBytesV (s.laneWidth / 8) k)))
    (hinv : Applies (simEnv B) "inv_lanes_"
      [.val (Vec.ishV s), .val (.list (List.replicate s.lanes (pctV k)))] (pctV r))
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hsl : SliceAt bs (i.toNat + arg.offset.val) (s.laneWidth / 8))
    (hc : leBytesV (s.laneWidth / 8) k = (bs.drop (i.toNat + arg.offset.val)).take
      (s.laneWidth / 8)) :
    Fires (simEnv B) "Step_read" 47 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vloadV (some (.case "SPLAT" (pctV s.laneWidth))) n arg],
      .list [.case "VCONST" (.tuple [caseNilV "V128", pctV r])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("N", .num (.natN s.laneWidth)), ("x", idxV n), ("ao", memargV arg),
    ("c", pctV r), ("j", pctV k), ("Jnn", Vec.intLaneV s), ("M", pctV s.lanes)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hw : s.laneWidth = 8 ∨ s.laneWidth = 16 ∨ s.laneWidth = 32 ∨ s.laneWidth = 64 := by
    cases s <;> simp [IntShape.laneWidth]
  have hcT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ)
      (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV r) := by
    have h := Typing.hasTyp_vec (B := B) (ρ := VarEnv.empty.bindVals σ) (BitVec.ofNat 128 r)
      evalExp_v128
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr] at h
  -- `$ibytes_(N, j)` is the slice.
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "ibytes_" [.expA (.varE "N"), .expA (.varE "j")])
      (.list (leBytesV (s.laneWidth / 8) k)) :=
    FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl)
      evalArgs_nil)) hib
  have e₂ := FwdMem.evalExp_memSlice (σ := σ) (ez := .varE "z") (ex := .varE "x")
    (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl) hm hB
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
    (Memory.evalExp_div8 (e := .varE "N") hw (evalExp_var rfl)) hsl
  rw [← hc] at e₂
  -- `N = $jsize(Jnn)` and `M = 128 / N`.
  have e128 : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cvtE (.numE (.natN 128)) .natT .ratT)
      (.num (.ratN 128)) := evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_num', rfl, rfl⟩
  obtain ⟨p₂, p₃⟩ := evalExp_jsizeM (B := B) s rfl rfl rfl (Memory.findDef_bindVals_empty σ _)
    e128
  -- `c = $inv_lanes_(Jnn X M, j^M)`.
  have eSh : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%X%" (.tupE
      [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])) (Vec.ishV s) :=
    evalExp_case (evalExp_tup2 (RefsGC.evalExp_sub_of (evalExp_var rfl)) (evalExp_var rfl))
  have eJ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "%" (.tupE [.projE (.uncaseE (.varE "j") "%") 0])) (pctV k) :=
    evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons'
      (RefsGC.evalExp_unpct (evalExp_var rfl)) RefsGC.evalExps_nil'))
  have eRep := Vec.evalExp_iterListN_nodom (RefsGC.evalExp_unpct (evalExp_var (x := "M") rfl)) eJ
  have e₄ := FwdMem.evalExp_call_applies (σ := σ)
    (evalArgs_cons eSh (evalArgs_cons eRep evalArgs_nil)) hinv
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadSplatVal σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_N B) _ _ hρ)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            (QuantsOk.cons rfl hcT (QuantsOk.cons rfl (FwdMem.hasTyp_iN_var rfl hk)
              (QuantsOk.cons rfl (Round5.SimdTy.typedV_jnn s _ hρ)
                (QuantsOk.cons rfl (Round5.SimdTy.typedV_M (.int s) _ hρ) QuantsOk.nil))))))))))
    (by mem_eval_tac)
    (prems_four (.ifPr (RefsGC.evalExp_eq_true e₁ e₂)) (.ifPr p₂) (.ifPr p₃)
      (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) e₄)))

end Rule

/-! ## Core's splat, forward -/

section Forward

variable {H : Type} {hn : H → String}

/-- **The lanes of Core's splat** are the loaded word, once per lane. -/
theorem lanesV_splat (s : IntShape) (c : BitVec s.laneWidth) :
    Round5.Simd.lanesV (.int s) (invLanes s.laneWidth (List.replicate s.lanes c)) =
      List.replicate s.lanes (pctV c.toNat) := by
  have h : Shape.lanesOf (.int s) (invLanes s.laneWidth (List.replicate s.lanes c)) =
      List.replicate s.lanes c :=
    Silmaril.Wasm.Numerics.lanesW_invLanesW (Nat.le_of_eq s.size) _ (by simp)
  rw [Round5.Simd.lanesV, h]
  cases s <;> rfl

/-- `$inv_lanes_` at the concrete primitives, on the image of a lane list. -/
theorem applies_invLanes_vb {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (sh : Shape) (v : BitVec 128) :
    Applies (simEnv (withVBytes (Prims.builtins P hn host))) "inv_lanes_"
      [.val (Vec.shapeV sh), .val (.list (Round5.Simd.lanesV sh v))] (Vec.vecV v) :=
  Prims.applies_of_noClause (Round5.Simd.findDef_invLanes _)
    (((show (withVBytes (Prims.builtins P hn host)).call "inv_lanes_" _ =
        (Prims.builtins P hn host).call "inv_lanes_" _ by simp [withVBytes]).trans
      (Round5.Simd.call_invLanes P hn host _ _)).trans (Round5.Simd.invLanesCall_eq sh v))

/-- **`MemoryStep.vecLoadVal` at a splat, forward**, at the integer shape `s`: from a typed state
image, the in-bounds splat load is a `Step_read` step to Core's splat, in both readings. -/
theorem fwd_vecLoadSplat_shape {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (s : IntShape) {st : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {c : BitVec (8 * (s.laneWidth / 8))}
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn st f))
    (hm : st.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (s.laneWidth / 8) =
      some c) :
    let r := invLanes s.laneWidth (List.replicate s.lanes (c.setWidth s.laneWidth))
    SRead (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (.splat (packOf s)) x arg)])
      [adminToV (.plain (.vecConst r))] ∧
      Round6.Reading.SReadB (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (.splat (packOf s)) x arg)])
        [adminToV (.plain (.vecConst r))] := by
  intro r
  obtain ⟨hle, hb⟩ := FwdMem.load_bytesV hl
  have hw : 8 * (s.laneWidth / 8) = s.laneWidth := by cases s <;> rfl
  have hk : c.toNat < 2 ^ s.laneWidth := lt_of_lt_of_eq c.isLt (by rw [hw])
  have hcw : (c.setWidth s.laneWidth).toNat = c.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hk
  have hinv : Applies (simEnv (withVBytes (Prims.builtins P hn host))) "inv_lanes_"
      [.val (Vec.ishV s), .val (.list (List.replicate s.lanes (pctV c.toNat)))]
      (pctV r.toNat) := by
    have h := applies_invLanes_vb (P := P) (hn := hn) (host := host) (.int s) r
    rwa [lanesV_splat, hcw] at h
  have hv : adminToV (.plain (.vecConst r)) =
      .case "VCONST" (.tuple [caseNilV "V128", pctV r.toNat]) := rfl
  rw [State.adminToV_aconst, instrToVM_vecLoad, hv]
  have hop : Round6.MemSimd.vecLoadOpV (.splat (packOf s)) =
      some (.case "SPLAT" (pctV s.laneWidth)) := by cases s <;> rfl
  rw [hop]
  exact sread_of_fires loadTags_noCast (lhsIn_vload _ _ _ _ _ _)
    (fires_vloadSplatVal (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _) s hk r.isLt
      (applies_ibytes_vb _ _) hinv hz x.value.isLt (memAt_of_mem? hn hm)
      (FwdMem.memInstV_BYTES' mi) (FwdMem.sliceAt_of_or (.inl FwdMem.sliceTotal) hle) hb)

end Forward

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
