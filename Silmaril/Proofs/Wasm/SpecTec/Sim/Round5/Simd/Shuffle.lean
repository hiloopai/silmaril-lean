module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.UnboundRefute
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Fields

/-!
# Round 5, track simd (pass 3): `$vshufflop_` at the concrete builtins

`$vshufflop_`'s clause matches every argument list of the encoding (its lane-index pattern `i*`
binds the whole list, `matchExp_iterPat_fresh`) and calls `$ivshufflop_`, whose only clause binds
its lanes in an `if` premise and so definitely fails (`premsUndef_unbound`). Hence the call denotes
`vecOpCall`'s answer: the shuffle exactly on in-range lane indices.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {P : Profile} {hn : H → String} {host : HostSemantics H}

/-- A clause that matches, holds, and whose body definitely fails, makes the search fail. -/
theorem tryClausesUndef_body {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV} {ρ₀ ρ₁ : VarEnv}
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (hp : PremsHold env ρ₀ prems ρ₁)
    (hb : Prims.EvalExpUndef env ρ₁ e) : TryClausesUndef env (.defD q pats e prems :: cs) ws := by
  obtain ⟨n₁, h₁⟩ := hm
  obtain ⟨n₂, h₂⟩ := hp
  obtain ⟨n₃, h₃⟩ := hb
  refine ⟨max (max n₁ n₂) n₃ + 1, ?_⟩
  have e1 := matchArgs_ok_of_le (m := n₁) (n := max (max n₁ n₂) n₃) (by omega) h₁
  have e2 := premsHold_ok_of_le (m := n₂) (n := max (max n₁ n₂) n₃) (by omega) h₂
  have e3 := Prims.evalExp_undef_of_le (m := n₃) (n := max (max n₁ n₂) n₃) (by omega) h₃
  simp only [tryClauses, e1, Bind.bind, Except.bind, e2, Res.elimUndef, e3]

/-- The shape pattern `%(I8 X M)` of `$vshufflop_` matches `bshapeV`. -/
theorem matchExp_bshape {env : Env} :
    MatchExp env VarEnv.empty (.caseE "%" (.tupE [.caseE "%X%" (.tupE [.caseE "I8" (.tupE []),
      .varE "M"])])) Vec.bshapeV (VarEnv.empty.bindVal "M" (pctV 16)) :=
  show MatchExp _ _ _ (.case "%" (.tuple [.case "%X%" (.tuple [.case "I8" (.tuple []), pctV 16])]))
    _ from
  matchExp_caseE (matchExp_tupE_one (matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2
    ⟨_, rfl, Equiv.Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl, matchExp_caseE matchExp_tupE_nil,
      Equiv.Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl, matchExp_varE (by simp),
        Equiv.Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩)))

/-- `I8 X M`, evaluated where `M` is `16`. -/
theorem evalExp_i8Shape {env : Env} {ρ : VarEnv} (hM : ρ.findVal? "M" = some (pctV 16)) :
    EvalExp env ρ (.caseE "%X%" (.tupE [.caseE "I8" (.tupE []), .varE "M"])) (Vec.ishV .i8x16) :=
  ⟨20, by
    simp [evalExp, evalExps, hM, Res.ofOption, Bind.bind, Except.bind, Functor.map, Except.map,
      pure, Except.pure, Vec.ishV, Vec.intLaneV, caseNilV, pctV, IntShape.lanes]⟩

/-- **Every clause of `$ivshufflop_` definitely fails.** -/
theorem undef_ivshufflop (B : Builtins) (L : List Value) (a b : V128) :
    TryClausesUndef (simEnv B) (clausesOf Original.d530)
      [.val (Vec.ishV .i8x16), .val (.list L), .val (Vec.vecV a), .val (Vec.vecV b)] :=
  IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_jnnPat (by simp) (by simp)))
      (matchArgs_cons (matchArg_expA (Equiv.Execution.matchExp_iterPat_fresh (by simp) (by decide)
        (by simp) L))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
          (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))))
    (premsUndef_unbound (by simp)) IntNumeric.tryClausesUndef_nil

/-- **Every clause of `$vshufflop_` definitely fails** at `encShuffle`. -/
theorem undef_Shuffle (idx : List LaneIdx) (a b : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d543)
      (encShuffle (idx, a, b)) := by
  let L := idx.map Vec.laneIdxV
  let ρ := (((VarEnv.empty.bindVal "M" (pctV 16)).bindVal "i*" (.list L)).bindVal "v_1"
    (Vec.vecV a)).bindVal "v_2" (Vec.vecV b)
  have hm : MatchArgs (simEnv (BI P hn host)) VarEnv.empty
      [.expA (.caseE "%" (.tupE [.caseE "%X%" (.tupE [.caseE "I8" (.tupE []), .varE "M"])])),
        .expA (iterPat "i" "i*"), .expA (.varE "v_1"), .expA (.varE "v_2")]
      (encShuffle (idx, a, b)) ρ :=
    matchArgs_cons (matchArg_expA matchExp_bshape)
      (matchArgs_cons (matchArg_expA (Equiv.Execution.matchExp_iterPat_fresh (by simp) (by decide)
        (by simp) L))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
          (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))
  have hargs : EvalArgs (simEnv (BI P hn host)) ρ
      [.expA (.caseE "%X%" (.tupE [.caseE "I8" (.tupE []), .varE "M"])),
        .expA (iterPat "i" "i*"), .expA (.varE "v_1"), .expA (.varE "v_2")]
      [.val (Vec.ishV .i8x16), .val (.list L), .val (Vec.vecV a), .val (Vec.vecV b)] :=
    Equiv.evalArgs_cons (evalExp_i8Shape (by simp [ρ]))
      (Equiv.evalArgs_cons (Equiv.Execution.evalExp_iterPat (by decide) (by simp [ρ]))
        (Equiv.evalArgs_cons (evalExp_var (by simp [ρ]))
          (Equiv.evalArgs_cons (evalExp_var (by simp [ρ])) Equiv.evalArgs_nil)))
  exact tryClausesUndef_body hm (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (Prims.evalExpUndef_call (by simp [ρ]) hargs (findDef_Ivshufflop _)
      (undef_ivshufflop _ L a b) (call_Ivshufflop P hn host _))

/-- **`VecAgreeOps.shuffle`** at the concrete builtins. -/
theorem f_shuffle (idx : List LaneIdx) (a b : V128) (c : Value) :
    Applies (simEnv (BI P hn host)) "vshufflop_"
      [.val Vec.bshapeV, .val (.list (idx.map Vec.laneIdxV)), .val (Vec.vecV a), .val (Vec.vecV b)]
      c ↔ (∀ j ∈ idx, j.val < 32) ∧ c = Vec.vecV (vecShuffle idx a b) := by
  show Applies _ _ (encShuffle (idx, a, b)) c ↔ _
  rw [applies_iff_of_undef' (findDef_Vshufflop _) ⟨_, _, _, _, rfl⟩ (undef_Shuffle idx a b),
    call_vecOp _ (by simp)]
  simp only [vecOpCall, decodeArgs_enc encShuffle_injective, Option.bind_some]
  split
  · next h => exact ⟨fun hc => ⟨h, (Option.some.inj hc).symm⟩, fun ⟨_, hc⟩ => by rw [hc]⟩
  · next h => simp [h]

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
