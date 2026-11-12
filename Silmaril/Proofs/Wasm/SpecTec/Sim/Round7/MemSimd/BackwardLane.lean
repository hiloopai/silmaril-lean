module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.BackwardVal
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.Agg

/-!
# Round 7, memory SIMD: the in-bounds lane store, backward (`Step` 25)

`Step/vstore_lane-val` binds the lane type `Jnn` and the lane count `M` only through its
premises, so a backward proof has to recover the shape:

* `b* = $ibytes_(N, $lanes_(Jnn X M, c)[j])`. At the concrete primitives `$lanes_` has no clause
  and is answered by round 5's `lanesCall`, which is defined only at the image of a shape
  (`lanes_inv`). The selected lane is unwrapped by `%`, so the shape is an integer shape
  (`laneV_pct`: a float lane is SpecTec's `fN`, a `POS`/`NEG` injection).
* `N = $jsize(Jnn)`. At the integer shape `s` this is `s.laneWidth` (`applies_jsize`), so the
  instruction's pack size is `packOf s`.

Then the written bytes are the `$ibytes_` encoding of Core's lane, and round 5's `$with_mem`
inversion (`withMem_store'`) gives Core's store and the written state.

* `bwd_vstoreLaneVal`: if rule 25 fires at the image of `v128.store*_lane` over a memory the
  frame resolves, at `withVBytes (Prims.builtins …)`, the result is the image of Core's store and
  Core's `vecStoreLaneVal` steps there.
* `bwdB_vstoreLaneVal`: the same at round 6's backend reading.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)
open FwdMem (leBytesV)

variable {H : Type} {hn : H → String}

/-- The lane-index operand `j` of a `VSTORE_LANE` element of a left-hand side. -/
theorem vstoreLane_fj {env : Env} {ρ : VarEnv} {w n : Nat} {arg : MemArg} {j : Nat}
    (h : EvalExp env ρ (.caseE "VSTORE_LANE" (.tupE [.caseE "V128" (.tupE []),
      .caseE "%" (.tupE [.varE "N"]), .varE "x", .varE "ao", .varE "j"])) (vstoreLaneV w n arg j)) :
    ρ.findVal? "j" = some (pctV j) := by
  have hx₂ := RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h))).2
  have hx₃ := RefsGC.evalExps_cons_inv hx₂.2
  exact evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hx₃.2).2).1

/-- A two-argument expression list, inverted. -/
theorem evalArgs_two_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {ws : List ArgV}
    (h : EvalArgs env ρ [.expA e₁, .expA e₂] ws) :
    ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ ws = [.val v₁, .val v₂] := by
  obtain ⟨v₁, ws₁, h₁, hws₁, rfl⟩ := Round5.BwdStep.evalArgs_cons_inv h
  obtain ⟨v₂, ws₂, h₂, hws₂, rfl⟩ := Round5.BwdStep.evalArgs_cons_inv hws₁
  obtain rfl := evalArgs_nil_iff.1 hws₂
  exact ⟨v₁, v₂, h₁, h₂, rfl⟩

/-- A call of a definition with two expression arguments, read as `Applies` at the arguments'
values (in a scope of values only). -/
theorem applies_of_call2 {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id} {e₁ e₂ : Exp}
    {v : Value} (h : EvalExp env ρ (.callE x [.expA e₁, .expA e₂]) v) :
    ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ Applies env x [.val v₁, .val v₂] v := by
  obtain ⟨ws, hws⟩ := Round5.BwdStep.args_of_call h
  obtain ⟨v₁, v₂, h₁, h₂, rfl⟩ := evalArgs_two_inv hws
  exact ⟨v₁, v₂, h₁, h₂, (applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _) hws).2
    (evalExp_callE_iff.1 h)⟩

/-- `$lanes_` at `withVBytes (Prims.builtins …)` is round 5's `lanesCall`. -/
theorem call_lanes_vb {P : Numerics.Profile} {host : HostSemantics H} (sv v : Value) :
    (simEnv (withVBytes (Prims.builtins P hn host))).builtins.call "lanes_" [.val sv, .val v] =
      Round5.Simd.lanesCall sv v :=
  (show (withVBytes (Prims.builtins P hn host)).call "lanes_" _ =
      (Prims.builtins P hn host).call "lanes_" _ by simp [withVBytes]).trans
    (Round5.Simd.call_lanes P hn host _ _)

/-- **`$lanes_` at the concrete primitives, inverted**: a definite answer at a 128-bit pattern
`c` comes from the image of a shape, and is the images of `c`'s lanes at that shape. -/
theorem lanes_inv {P : Numerics.Profile} {host : HostSemantics H} {sv L : Value} {c : BitVec 128}
    (h : Applies (simEnv (withVBytes (Prims.builtins P hn host))) "lanes_"
      [.val sv, .val (pctV c.toNat)] L) :
    ∃ sh, sv = Vec.shapeV sh ∧ L = .list (Round5.Simd.lanesV sh c) := by
  have hb := Round5.Simd.applies_noClause_iff (Round5.Simd.findDef_lanes _) h
  rw [call_lanes_vb] at hb
  unfold Round5.Simd.lanesCall at hb
  split at hb
  · next hex =>
    obtain ⟨h₁, h₂⟩ := hex.choose_spec
    have hc : c = hex.choose.2 := Round5.Simd.vecV_injective h₂
    exact ⟨hex.choose.1, h₁, by
      rw [← Option.some.inj hb]; exact congrArg _ (congrArg _ hc.symm)⟩
  · exact absurd hb (by simp)

/-- SpecTec's `fN` is a `POS` or `NEG` injection. -/
theorem floatV_case (t : FloatType) (b : BitVec t.width) :
    ∃ op m, floatV t b = .case op m ∧ op ≠ "%" := by
  unfold floatV
  split <;> exact ⟨_, _, rfl, by decide⟩

/-- **A lane that is a `%`-numeral is a lane of an integer shape.** -/
theorem laneV_pct {sh : Shape} {x : BitVec sh.laneWidth} {u : Value}
    (h : Round5.Simd.laneV sh x = .case "%" u) : ∃ s : IntShape, sh = .int s := by
  rcases sh with s | s
  · exact ⟨s, rfl⟩
  · exfalso
    cases s
    · obtain ⟨op, m, he, hne⟩ := floatV_case .f32 x
      simp only [Round5.Simd.laneV, he, Value.case.injEq] at h
      exact hne h.1
    · obtain ⟨op, m, he, hne⟩ := floatV_case .f64 x
      simp only [Round5.Simd.laneV, he, Value.case.injEq] at h
      exact hne h.1

/-- The `j`-th lane of `c` at an integer shape, as the `nat` SpecTec unwraps from it. -/
theorem lane_of_idx {s : IntShape} {c : BitVec 128} {l : Nat} {vs : List Value}
    (h : (Round5.Simd.lanesV (.int s) c)[l]? = some (.case "%" (.tuple vs))) :
    l < s.lanes ∧
      vs = [.num (.natN (((Shape.int s).lanesOf c).getD l 0).toNat)] := by
  have hl : l < (Round5.Simd.lanesV (.int s) c).length := by
    rcases Nat.lt_or_ge l (Round5.Simd.lanesV (.int s) c).length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at h; exact absurd h (by simp)
  have hl' : l < s.lanes := by
    simpa [Round5.Simd.lanesV, Shape.lanesOf, Shape.lanes] using hl
  rw [Round5.Simd.getElem?_lanesV (.int s) c (by simpa [Shape.lanes] using hl')] at h
  simp only [Round5.Simd.laneV, pctV, Option.some.injEq, Value.case.injEq,
    Value.tuple.injEq, true_and] at h
  exact ⟨hl', h.symm⟩

/-- The lane selector of rule 25's third premise. -/
abbrev laneSel : Exp :=
  .idxE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" [])
    (.varT "lanetype" []), .varE "M"])), .expA (.varE "c")]) (.projE (.uncaseE (.varE "j") "%") 0)

/-- `%(e.0)` around a `%`-injection, inverted. -/
theorem pctArg_inv {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ (.caseE "%" (.tupE [.projE (.uncaseE e "%") 0])) v) :
    ∃ ts u, EvalExp env ρ e (.case "%" (.tuple ts)) ∧ ts[0]? = some u ∧
      v = .case "%" (.tuple [u]) := by
  obtain ⟨w, hw, hv⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, hw'⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨u, us, hp, hus, hvs'⟩ := evalExps_cons_iff.1 hvs
  have hus' : us = [] := evalExps_nil_iff.1 hus
  obtain ⟨ts, hts, -, hti⟩ := evalExp_projE_iff.1 hp
  have hv' : v = .case "%" (.tuple [u]) := by rw [hv, hw', hvs', hus']
  exact ⟨ts, u, evalExp_uncaseE_iff.1 hts, hti, hv'⟩

/-- The `j`-th lane of the image of a shape is a `%`-numeral only at an integer shape, and is
then Core's lane. -/
theorem lanesV_idx_inv {sh : Shape} {c : BitVec 128} {l : Nat} {ts : List Value}
    (h : (Round5.Simd.lanesV sh c)[l]? = some (.case "%" (.tuple ts))) :
    ∃ s : IntShape, sh = .int s ∧ l < s.lanes ∧
      ts = [.num (.natN (((Shape.int s).lanesOf c).getD l 0).toNat)] := by
  have hy : ∃ y, Round5.Simd.laneV sh y = .case "%" (.tuple ts) := by
    simp only [Round5.Simd.lanesV, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨y, -, he⟩ := h
    exact ⟨y, he⟩
  obtain ⟨y, hy⟩ := hy
  obtain ⟨s, rfl⟩ := laneV_pct hy
  obtain ⟨hl, hts⟩ := lane_of_idx h
  exact ⟨s, rfl, hl, hts⟩

/-- **The lane selector `$lanes_(Jnn X M, c)[j]`, inverted** at the concrete primitives: `Jnn`
is the lane type of an integer shape `s`, `j` is in range, and the selected lane is Core's. -/
theorem laneSel_inv {P : Numerics.Profile} {host : HostSemantics H} {ρ : VarEnv}
    (hρ : ValsOnly ρ) {l : Nat} {c : BitVec 128} {ts : List Value}
    (fc : ρ.findVal? "c" = some (pctV c.toNat)) (fj : ρ.findVal? "j" = some (pctV l))
    (h : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) ρ laneSel
      (.case "%" (.tuple ts))) :
    ∃ s : IntShape, ρ.findVal? "Jnn" = some (Vec.intLaneV s) ∧ l < s.lanes ∧
      ts = [.num (.natN (((Shape.int s).lanesOf c).getD l 0).toNat)] := by
  obtain ⟨Lw, jj, eL, eJ, hLi⟩ := evalExp_idxE_iff.1 h
  have hjj : Value.num (.natN jj) = .num (.natN l) :=
    EvalExp.unique eJ (RefsGC.evalExp_unpct (evalExp_var fj))
  obtain ⟨sv, cv, eSh, ec, hAl⟩ := applies_of_call2 hρ eL
  have hcv : cv = pctV c.toNat := EvalExp.unique ec (evalExp_var fc)
  obtain ⟨sh, hsv, hLw⟩ := lanes_inv (hcv ▸ hAl)
  have hsel : (Round5.Simd.lanesV sh c)[l]? = some (.case "%" (.tuple ts)) := by
    simpa [hLw, show jj = l by simpa using hjj] using hLi
  obtain ⟨s, rfl, hl, hts⟩ := lanesV_idx_inv hsel
  have hJ : EvalExp _ ρ (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))
      (Vec.intLaneV s) := (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
        (RefsGC.case_inv (hsv ▸ eSh)))).1
  exact ⟨s, evalExp_varE_iff.1 (evalExp_subE_iff.1 hJ), hl, hts⟩

/-- The third premise of rule 25, `b* = $ibytes_(N, $lanes_(Jnn X M, c)[j])`, inverted at the
concrete primitives: the lanes are those of an integer shape `s`, `Jnn` is its lane type, and
`b*` is the `$ibytes_` encoding of lane `j` of `c`. -/
theorem ibytesLane_inv {P : Numerics.Profile} {host : HostSemantics H} {ρ : VarEnv}
    (hρ : ValsOnly ρ) {N l : Nat} {c : BitVec 128} {V : Value}
    (fN : ρ.findVal? "N" = some (.num (.natN N))) (fc : ρ.findVal? "c" = some (pctV c.toNat))
    (fj : ρ.findVal? "j" = some (pctV l))
    (h : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) ρ
      (.callE "ibytes_" [.expA (.varE "N"), .expA (.caseE "%" (.tupE [.projE (.uncaseE
        laneSel "%") 0]))]) V) :
    ∃ s : IntShape, ρ.findVal? "Jnn" = some (Vec.intLaneV s) ∧ l < s.lanes ∧
      V = .list (leBytesV (N / 8) (((Shape.int s).lanesOf c).getD l 0).toNat) := by
  obtain ⟨vN, vE, eN, eE, hA⟩ := applies_of_call2 hρ h
  have hvN : vN = .num (.natN N) := EvalExp.unique eN (evalExp_var fN)
  obtain ⟨ts, u, eSel, hu, hvE⟩ := pctArg_inv eE
  obtain ⟨s, fJ, hl, hts⟩ := laneSel_inv hρ fc fj eSel
  have hvE' : vE = pctV (((Shape.int s).lanesOf c).getD l 0).toNat := by
    rw [hts] at hu
    rw [hvE, ← Option.some.inj hu]; rfl
  exact ⟨s, fJ, hl, Applies.unique (hvN ▸ hvE' ▸ hA) (applies_ibytes_vb _ _)⟩

/-- **Rule 25's first premise, `N = $jsize(Jnn)`, fixes the pack size**: at the lane type of an
integer shape `s`, the instruction's pack size is `packOf s`. -/
theorem packOf_of_jsize {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {sz : PackSize}
    {s : IntShape} (fN : ρ.findVal? "N" = some (.num (.natN sz.width)))
    (fJ : ρ.findVal? "Jnn" = some (Vec.intLaneV s))
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.varE "N")
      (.callE "jsize" [.expA (.varE "Jnn")])) (.bool true)) :
    sz = packOf s := by
  obtain ⟨V, eN, eJs⟩ := Bwd.eq_of_cmp h
  have hV : V = .num (.natN sz.width) := EvalExp.unique eN (evalExp_var fN)
  have hJs : V = natV s.laneWidth := Applies.unique ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons (evalExp_var fJ)
      Equiv.evalArgs_nil)).2 (evalExp_callE_iff.1 eJs)) (applies_jsize s)
  have hw : sz.width = s.laneWidth := by simpa [natV, hV] using hJs
  cases sz <;> cases s <;> simp_all [PackSize.width, IntShape.laneWidth, packOf]

/-- A lane's bits, at the store width `8 * (N / 8)`, have the lane's value. -/
theorem toNat_lane_setWidth (s : IntShape) (c : BitVec 128) (l : Nat) :
    (((Numerics.lanes (packOf s).width (128 / (packOf s).width) c).getD l 0).setWidth
      (8 * ((packOf s).width / 8))).toNat = (((Shape.int s).lanesOf c).getD l 0).toNat := by
  rw [FwdMem.toNat_setWidth_of_le _ (by cases s <;> decide)]
  cases s <;> rfl

/-- **The left-hand side of rule 25, inverted**: the operands `i`, `c`, `N`, `x`, `ao`, `j`. -/
theorem vstoreLaneLhs_inv {env : Env} {ρ : VarEnv} {A : Value} {I w n : Nat} {arg : MemArg}
    {l : Nat} {c : BitVec 128}
    (h : EvalExps env ρ [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
        (.varT "numtype" []), .varE "i"]), .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []),
        .varE "c"]), .caseE "VSTORE_LANE" (.tupE [.caseE "V128" (.tupE []),
        .caseE "%" (.tupE [.varE "N"]), .varE "x", .varE "ao", .varE "j"])]
      [aconstV A I, vconstV c, vstoreLaneV w n arg l]) :
    ρ.findVal? "i" = some (idxV I) ∧ ρ.findVal? "c" = some (pctV c.toNat) ∧
      ρ.findVal? "N" = some (.num (.natN w)) ∧ ρ.findVal? "x" = some (idxV n) ∧
      ρ.findVal? "ao" = some (memargV arg) ∧ ρ.findVal? "j" = some (pctV l) := by
  have h₁ := RefsGC.evalExps_cons_inv h
  have h₂ := RefsGC.evalExps_cons_inv h₁.2
  have h₃ := (RefsGC.evalExps_cons_inv h₂.2).1
  obtain ⟨fN, fx, fao⟩ := vstoreLane_fvs h₃
  exact ⟨fi_of_aconst h₁.1, fc_of_vconst h₂.1, fN, fx, fao, vstoreLane_fj h₃⟩

/-- **`Step/vstore_lane-val`, backward**, at `withVBytes (Prims.builtins …)`: at a memory the
frame resolves, the result is the image of Core's store of lane `j`, and Core's
`vecStoreLaneVal` steps there. -/
theorem bwd_vstoreLaneVal {P : Numerics.Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg} {j : LaneIdx} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {ma : Nat} {mi : MemInst} {w : Value}
    (hm : s.mem? f x = some (ma, mi))
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 25
      (.tuple [cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)], w])) :
    ∃ s', w = cfgV (stateV hn s' f) [] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStoreLane sz x arg j)]⟩
        ⟨s', f, []⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecStoreLane] at hf
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreLaneVal |>
      hasRuleAt_simEnv _) hf
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨fi, fc, fN, fx, fao, fj⟩ := vstoreLaneLhs_inv hes
  obtain ⟨V, eb, ecall⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
  obtain ⟨sh, fJ, -, hV⟩ := ibytesLane_inv hρ fN fc fj ecall
  obtain rfl : sz = packOf sh :=
    packOf_of_jsize hρ fN fJ (RefsGC.premW_if (hp _ (List.mem_cons_self ..)))
  obtain ⟨W, hW, rfl⟩ := BwdPureStep.rhs_nil hr
  have hw8 : (packOf sh).width = 8 ∨ (packOf sh).width = 16 ∨ (packOf sh).width = 32 ∨
      (packOf sh).width = 64 := by cases sh <;> simp [packOf, PackSize.width]
  obtain ⟨b, hs, rfl⟩ := withMem_store' (k := (packOf sh).width / 8)
    (w := ((Numerics.lanes (packOf sh).width (128 / (packOf sh).width) c).getD j.val 0).setWidth
      (8 * ((packOf sh).width / 8)))
    call_withMem_vb fz fx fi fao hm (Memory.evalExp_div8 hw8 (evalExp_var fN))
    (by rw [toNat_lane_setWidth]; exact hV ▸ eb) hW
  exact ⟨_, rfl, .memory (.vecStoreLaneVal hm hs)⟩

/-- **`Step/vstore_lane-val` at round 6's backend reading, backward**, at the concrete
primitives. -/
theorem bwdB_vstoreLaneVal {P : Numerics.Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg} {j : LaneIdx} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {ma : Nat} {mi : MemInst} {w : Value}
    (hm : s.mem? f x = some (ma, mi))
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 25
      (.tuple [cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)], w])) :
    ∃ s', w = cfgV (stateV hn s' f) [] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStoreLane sz x arg j)]⟩
        ⟨s', f, []⟩ :=
  bwd_vstoreLaneVal hm ((Round6.Reading.firesB_step_iff _ (.inr (by decide))).1 hf)

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
