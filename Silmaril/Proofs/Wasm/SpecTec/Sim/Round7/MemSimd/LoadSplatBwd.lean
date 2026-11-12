module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.StepLift

/-!
# Round 7, memory SIMD: `v128.loadN_splat`, in bounds (`Step_read` 47), backward

`Jnn` and `M` are bound only by the premises of `Step_read/vload-splat-val`. Read back at
`withVBytes (Prims.builtins …)`:

* `$inv_lanes_` answers only at the image of a shape and of that shape's lanes of a 128-bit
  pattern (`invLanes_inv`); its lane list here is `%(j.0)` repeated, so the shape is an integer
  shape `s` (`laneV_pct`), `Jnn` is its lane type and `M` its lane count, and the pattern is
  Core's splat of `j` (`splatPrem_inv`, `eq_splat_of_lanesV`);
* `N = $jsize(Jnn)` makes the instruction's pack size `packOf s` (`packOf_of_jsize`);
* `$ibytes_(N, j)` is the slice, so `j` is Core's loaded word (`memSlice_load`).

* `bwd_vloadSplatVal`, `bwdB_vecLoadSplat`: if rule 47 fires at the image of a splat load, the
  result is the image of Core's splat, and Core's `vecLoadVal` steps there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (invLanes)
open State (aconstV idxV)
open FwdMem (leBytesV)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H} {F : Value}

/-- **`$inv_lanes_` at the concrete primitives, inverted**: a definite answer comes from the
image of a shape and of its lanes of a 128-bit pattern, and is that pattern. -/
theorem invLanes_inv {sv lv C : Value}
    (h : Applies (simEnv (withVBytes (Prims.builtins P hn host))) "inv_lanes_" [.val sv, .val lv]
      C) :
    ∃ sh v, sv = Vec.shapeV sh ∧ lv = .list (Round5.Simd.lanesV sh v) ∧ C = Vec.vecV v := by
  have hb := Round5.Simd.applies_noClause_iff (Round5.Simd.findDef_invLanes _) h
  have hb' : (withVBytes (Prims.builtins P hn host)).call "inv_lanes_" [.val sv, .val lv] =
      some C := hb
  rw [call_withVBytes_of_ne _ (by decide)] at hb'
  have hc : Round5.Simd.invLanesCall sv lv = some C :=
    (Round5.Simd.call_invLanes P hn host sv lv).symm.trans hb'
  unfold Round5.Simd.invLanesCall at hc
  split at hc
  · next hex =>
    obtain ⟨h₁, h₂⟩ := hex.choose_spec
    exact ⟨hex.choose.1, hex.choose.2, h₁, h₂, (Option.some.inj hc).symm⟩
  · exact absurd hc (by simp)

/-- A shape whose lanes of some pattern are a repeated `%`-numeral is an integer shape. -/
theorem int_of_lanesV_replicate {sh : Shape} {v : BitVec 128} {m k : Nat}
    (h : Round5.Simd.lanesV sh v = List.replicate m (pctV k)) : ∃ s : IntShape, sh = .int s := by
  have hlen : (Round5.Simd.lanesV sh v).length = sh.lanes := by
    simp [Round5.Simd.lanesV, Shape.lanesOf, Shape.lanes]
  have hpos : 0 < sh.lanes := by rcases sh with s | s <;> cases s <;> decide
  have hm : 0 < m := by rw [← List.length_replicate (n := m) (a := pctV k), ← h, hlen]; exact hpos
  have h0 := congrArg (·[0]?) h
  simp only [Round5.Simd.lanesV, List.getElem?_map] at h0
  rw [List.getElem?_replicate_of_lt hm] at h0
  obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.1 h0
  exact laneV_pct hx

/-- **The lanes of a pattern are a repeated word exactly at Core's splat of it.** -/
theorem eq_splat_of_lanesV {s : IntShape} {v : BitVec 128} {k : Nat} (hk : k < 2 ^ s.laneWidth)
    (h : Round5.Simd.lanesV (.int s) v = List.replicate s.lanes (pctV k)) :
    v = invLanes s.laneWidth (List.replicate s.lanes (BitVec.ofNat s.laneWidth k)) := by
  have hk' : (BitVec.ofNat s.laneWidth k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk
  apply Round5.Simd.lanesV_injective (.int s)
  rw [h, lanesV_splat, hk']

/-- **The splat premise `c = $inv_lanes_(Jnn X M, %(j.0)^M)`, inverted** at the concrete
primitives: `Jnn` is the lane type of an integer shape `s`, and the pattern's lanes are `j`. -/
theorem splatPrem_inv {σ : List (IL.Id × Value)} {k : Nat} {C : Value}
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV k))
    (h : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) (VarEnv.empty.bindVals σ)
      (.callE "inv_lanes_" [.expA (.caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" [])
        (.varT "lanetype" []), .varE "M"])), .expA (.iterE (.caseE "%" (.tupE
        [.projE (.uncaseE (.varE "j") "%") 0])) (.mk (.listN (.projE (.uncaseE (.varE "M") "%") 0)
        none) []))]) C) :
    ∃ (s : IntShape) (v : BitVec 128),
      (VarEnv.empty.bindVals σ).findVal? "Jnn" = some (Vec.intLaneV s) ∧
      Round5.Simd.lanesV (.int s) v = List.replicate s.lanes (pctV k) ∧ C = Vec.vecV v := by
  obtain ⟨v₁, v₂, e₁, e₂, hA⟩ := applies_of_call2 ⟨rfl, rfl, rfl⟩ h
  obtain ⟨sh, v, rfl, rfl, rfl⟩ := invLanes_inv hA
  obtain ⟨Jv, Mv, eJ, eM, hsh⟩ : ∃ Jv Mv, (VarEnv.empty.bindVals σ).findVal? "Jnn" = some Jv ∧
      (VarEnv.empty.bindVals σ).findVal? "M" = some Mv ∧
      Vec.shapeV sh = .case "%X%" (.tuple [Jv, Mv]) := by
    obtain ⟨u, hu, hv⟩ := evalExp_caseE_iff.1 e₁
    obtain ⟨Jv, Mv, rfl, hJ, hM⟩ := Vec.inv_tup2 hu
    exact ⟨Jv, Mv, evalExp_varE_iff.1 (evalExp_subE_iff.1 hJ), evalExp_varE_iff.1 hM, hv⟩
  have hJM : Vec.laneTypeV sh = Jv ∧ pctV sh.lanes = Mv := by
    simpa using (Vec.shapeV_eq sh).symm.trans hsh
  have hMv : Mv = pctV sh.lanes := hJM.2.symm
  have eRep : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) (VarEnv.empty.bindVals σ)
      (.iterE (.caseE "%" (.tupE [.projE (.uncaseE (.varE "j") "%") 0]))
        (.mk (.listN (.projE (.uncaseE (.varE "M") "%") 0) none) []))
      (.list (List.replicate sh.lanes (pctV k))) :=
    Vec.evalExp_iterListN_nodom (RefsGC.evalExp_unpct (evalExp_var (hMv ▸ eM)))
    (evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons'
      (RefsGC.evalExp_unpct (evalExp_var fj)) RefsGC.evalExps_nil')))
  have hl : Round5.Simd.lanesV sh v = List.replicate sh.lanes (pctV k) :=
    Value.list.inj (EvalExp.unique e₂ eRep)
  obtain ⟨s, rfl⟩ := int_of_lanesV_replicate hl
  have hJv : Jv = Vec.intLaneV s := hJM.1.symm
  exact ⟨s, v, hJv ▸ eJ, hl, rfl⟩

/-- Widening or narrowing is `ofNat` of the value. -/
theorem setWidth_eq_ofNat {n m : Nat} (c : BitVec n) : c.setWidth m = BitVec.ofNat m c.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- Core's splat of a loaded word, at the pack size of an integer shape. -/
theorem vecLoadResult_splat (s : IntShape) (c : BitVec (8 * ((packOf s).width / 8))) :
    vecLoadResult (.splat (packOf s)) c =
      invLanes s.laneWidth (List.replicate s.lanes (BitVec.ofNat s.laneWidth c.toNat)) := by
  cases s <;>
  · simp only [vecLoadResult, packOf, PackSize.width, IntShape.laneWidth, IntShape.lanes]
    congr 2
    exact setWidth_eq_ofNat c

/-- **The byte premise `$ibytes_(N, y) = $mem(z, x).BYTES[i + ao.OFFSET : N/8]`, inverted** at
the concrete primitives, for `y = %(kk)` with `kk < 2 ^ N`: Core's `N/8`-byte load reads `kk`. -/
theorem ibytesPrem_load {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : MemIdx}
    {I N kk : Nat} {arg : MemArg} {y : IL.Id}
    (hw8 : N = 8 ∨ N = 16 ∨ N = 32 ∨ N = 64)
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateVF F s f))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (fN : (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN N)))
    (fy : (VarEnv.empty.bindVals σ).findVal? y = some (pctV kk)) (hk : kk < 2 ^ N)
    (h : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "ibytes_" [.expA (.varE "N"), .expA (.varE y)])
        (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")
          (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
            (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
          (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "N") .natT .ratT)
            (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))) (.bool true)) :
    ∃ (ma : Nat) (mi : MemInst) (c : BitVec (8 * (N / 8))), s.mem? f x = some (ma, mi) ∧
      Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr I arg) (N / 8) = some c ∧
      c.toNat = kk := by
  obtain ⟨V, e₁, e₂⟩ := Bwd.eq_of_cmp h
  obtain ⟨vN, vJ, eN, eJ, hA⟩ := applies_of_call2 ⟨rfl, rfl, rfl⟩ e₁
  obtain ⟨k', hk', rfl⟩ := ibytes_inv_vb _ vJ V (EvalExp.unique eN (evalExp_var fN) ▸ hA)
  obtain rfl : kk = k' :=
    Round5.Read2.pctV_inj ((EvalExp.unique eJ (evalExp_var fy)).symm.trans hk')
  exact memSlice_load noAcc_vb fz fx fi fao
    (Memory.evalExp_div8 (e := .varE "N") hw8 (evalExp_var fN))
    (lt_of_lt_of_eq hk (by congr 1; omega)) e₂

/-- **`Step_read/vload-splat-val`, backward** (rule 47), at the concrete primitives with
`$vbytes_` answered: the memory resolves, Core's load succeeds at the instruction's width, and
the result is `VCONST` of Core's splat; the instruction's pack size is that of an integer
shape. -/
theorem bwd_vloadSplatVal {p : PackSize} {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {w : Value}
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 47
      (.tuple [cfgV (stateVF F s f) [aconstV (Encode.toValue a) i.toNat,
        vloadV (some (.case "SPLAT" (pctV p.width))) x.toNat arg], w])) :
    ∃ (sh : IntShape) (ma : Nat) (mi : MemInst) (c : BitVec (8 * (p.width / 8))),
      p = packOf sh ∧ s.mem? f x = some (ma, mi) ∧
      Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (p.width / 8) = some c ∧
      w = .list [.case "VCONST" (.tuple [caseNilV "V128", pctV (invLanes sh.laneWidth
        (List.replicate sh.lanes (BitVec.ofNat sh.laneWidth c.toNat))).toNat])] := by
  obtain ⟨σ, hq, fz, fx, fi, fao, ho, hr, hp⟩ :=
    fires_vload_inv (State.hasReadRules_simEnv _).vloadSplatVal hf
  have fN := optPct_N ho
  obtain ⟨J, fJ, hJ⟩ := hq "j" (.varT "iN" [.expA (.varE "N")]) (by simp)
  obtain ⟨k, rfl, hk⟩ := iN_inv_lt (evalExp_var fN) hJ
  have hw8 : p.width = 8 ∨ p.width = 16 ∨ p.width = 32 ∨ p.width = 64 := by
    cases p <;> simp [PackSize.width]
  obtain ⟨ma, mi, c, hm, hl, hcn⟩ := ibytesPrem_load hw8 fz fx fi fao fN fJ hk
    (RefsGC.premW_if (hp _ List.mem_cons_self))
  obtain ⟨C, eC, eInv⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))))
  obtain ⟨sh, v, fJnn, hl', rfl⟩ := splatPrem_inv fJ eInv
  have hpw : p = packOf sh := packOf_of_jsize ⟨rfl, rfl, rfl⟩ fN fJnn
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hk' : k < 2 ^ sh.laneWidth := by rw [← packOf_width sh, ← hpw]; exact hk
  have hv := eq_splat_of_lanesV hk' hl'
  refine ⟨sh, ma, mi, c, hpw, hm, hl, ?_⟩
  rw [rhs_vconst (evalExp_varE_iff.1 eC) hr, hcn, ← hv]

/-- **`v128.loadN_splat` in bounds at round 6's backend reading, backward**, at the concrete
primitives with `$vbytes_` answered: the result is the image of Core's splat, and Core's
`vecLoadVal` steps there. -/
theorem bwdB_vecLoadSplat {p : PackSize} {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {w : Value}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 47
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (.splat p) x arg)], w])) :
    ∃ v : BitVec 128, w = .list [adminToV (.plain (.vecConst v))] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad (.splat p) x arg)]⟩
        ⟨s, f, [.plain (.vecConst v)]⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f)
      [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (.splat p) x arg)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoad]; exact lhsIn_vload _ _ _ _ _ _
  have hf' := (Round6.Reading.firesB_read_iff _ loadTags_noCast ha).1 hf
  rw [State.adminToV_aconst, instrToVM_vecLoad] at hf'
  obtain ⟨sh, ma, mi, c, rfl, hm, hl, rfl⟩ := bwd_vloadSplatVal hf'
  refine ⟨vecLoadResult (.splat (packOf sh)) c, ?_, ?_⟩
  · rw [vecLoadResult_splat]; rfl
  · cases sh <;> exact .memory (.vecLoadVal hm hl)

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
