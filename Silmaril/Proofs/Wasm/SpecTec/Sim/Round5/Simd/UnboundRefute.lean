module
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Undef
public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Defs

/-!
# Round 5, track simd (pass 3): without a fallback, the lane-wise operators denote nothing

`$vnarrowop__`'s only clause binds `c_1*` in an `if` premise, which the IL evaluator only tests:
the premise mentions an unbound variable and definitely fails (`vnarrowop_undef`, for every `B`).
So wherever `B` does not answer `$vnarrowop__` itself, no call denotes anything, and the `narrow`
field of `VecAgreeOps` is false (`not_narrow_of`, `not_vecAgreeOps_of_narrow`). `Prims.builtins`
was such a `B` until pass 3, which added `vecOpCall`; the same holds of every lane-wise operator
(`Undef*.lean`).
-/

@[expose] public section
namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-- The pattern `Jnn X M` of the lane-wise operators' clauses. -/
abbrev jnnPat (x m : IL.Id) : Exp :=
  .caseE "%X%" (.tupE [.subE (.varE x) (.varT "Jnn" []) (.varT "lanetype" []), .varE m])

/-- A premise `c* = rhs` whose list variable `cs` only it could bind. -/
abbrev unboundPrem (c cs : IL.Id) (rhs : Exp) : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.iterE (.varE c) (.mk .list [.mk c (.varE cs)])) rhs)

set_option maxRecDepth 100000 in
/-- `$vnarrowop__` has one clause, whose first premise is `c_1* = $lanes_(…)`. -/
theorem findDef_vnarrowop (B : Builtins) : ∃ ps t qs rhs rest,
    (simEnv B).findDef? "vnarrowop__" = some (ps, t, [.defD qs [.expA (jnnPat "Jnn_1" "M_1"),
      .expA (jnnPat "Jnn_2" "M_2"), .expA (.varE "sx"), .expA (.varE "v_1"), .expA (.varE "v_2")]
      (.varE "v") (unboundPrem "c_1" "c_1*" rhs :: rest)]) :=
  ⟨_, _, _, _, _, rfl⟩

/-- **An `if` premise over an unbound list variable definitely fails.** -/
theorem premsUndef_unbound {env : Env} {ρ : VarEnv} {c cs : IL.Id} {rhs : Exp} {rest : List Prem}
    (h : ρ.findVal? cs = none) : PremsUndef env ρ (unboundPrem c cs rhs :: rest) :=
  ⟨8, by
    simp [premsHold, premHolds, evalExp, evalIterE, evalDoms, domVar, domSrc, h, Bind.bind,
      Except.bind]⟩

/-- `Jnn X M` matches a shape image. -/
theorem matchExp_jnnPat {env : Env} {ρ : VarEnv} {x m : IL.Id} {l mv : Value}
    (hx : ρ.findVal? x = none) (hm : (ρ.bindVal x l).findVal? m = none) :
    MatchExp env ρ (jnnPat x m) (.case "%X%" (.tuple [l, mv])) ((ρ.bindVal x l).bindVal m mv) :=
  ⟨6, by
    simp [matchExp, matchExps, hx, hm, Res.assert, Res.ofOption, Bind.bind, Except.bind,
      Value.asTuple?, Value.asCase?]⟩

/-- The arguments of `$vnarrowop__` match its clause's patterns. -/
theorem matchArgs_vnarrowop {env : Env} (s t : IntShape) (sxv a b : Value) :
    MatchArgs env VarEnv.empty [.expA (jnnPat "Jnn_1" "M_1"), .expA (jnnPat "Jnn_2" "M_2"),
      .expA (.varE "sx"), .expA (.varE "v_1"), .expA (.varE "v_2")]
      [.val (Vec.ishV s), .val (Vec.ishV t), .val sxv, .val a, .val b]
      (((((((VarEnv.empty.bindVal "Jnn_1" (Vec.intLaneV s)).bindVal "M_1" (pctV s.lanes)).bindVal
        "Jnn_2" (Vec.intLaneV t)).bindVal "M_2" (pctV t.lanes)).bindVal "sx" sxv).bindVal
        "v_1" a).bindVal "v_2" b) :=
  matchArgs_cons (matchArg_expA (matchExp_jnnPat (by simp) (by simp)))
    (matchArgs_cons (matchArg_expA (matchExp_jnnPat (by simp) (by simp)))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
          (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))))

/-- **Every clause of `$vnarrowop__` definitely fails**: its premise `c_1* = $lanes_(…)` mentions
`c_1*`, which only an `if` premise could bind. -/
theorem vnarrowop_undef (B : Builtins) (s t : IntShape) (sxv a b : Value) :
    ∃ ps ty cs, (simEnv B).findDef? "vnarrowop__" = some (ps, ty, cs) ∧
      Equiv.ExecNumeric.TryClausesUndef (simEnv B) cs
        [.val (Vec.ishV s), .val (Vec.ishV t), .val sxv, .val a, .val b] := by
  obtain ⟨ps, ty, qs, rhs, rest, hd⟩ := findDef_vnarrowop B
  exact ⟨ps, ty, _, hd, IntNumeric.tryClausesUndef_skip_prem (matchArgs_vnarrowop s t sxv a b)
    (premsUndef_unbound (by simp)) IntNumeric.tryClausesUndef_nil⟩

/-- **`VecAgreeOps.narrow` fails where `B` does not answer `$vnarrowop__`**, as `Prims.builtins`
did before pass 3. -/
theorem not_narrow_of {B : Builtins} (hB : ∀ ws, B.call "vnarrowop__" ws = none) :
    ¬ ∀ s t sx a b c, Applies (simEnv B) "vnarrowop__"
      [.val (Vec.ishV s), .val (Vec.ishV t), .val (Vec.sxV sx), .val (Vec.vecV a),
        .val (Vec.vecV b)] c ↔ ∃ r, VecNarrowRel s t sx a b r ∧ c = Vec.vecV r := by
  intro h
  obtain ⟨ps, ty, cs, hd, hu⟩ := vnarrowop_undef B .i16x8 .i8x16 (Vec.sxV .signed) (Vec.vecV 0)
    (Vec.vecV 0)
  have ha := (h .i16x8 .i8x16 .signed 0 0 _).2 ⟨_, rfl, rfl⟩
  have := (applies_iff_of_undef hd hu).1 ha
  rw [show (simEnv B).builtins = B from rfl, hB] at this
  exact absurd this (by simp)

/-- **`VecAgreeOps` is false where `B` does not answer `$vnarrowop__`.** -/
theorem not_vecAgreeOps_of_narrow {B : Builtins} (hB : ∀ ws, B.call "vnarrowop__" ws = none)
    (P : Profile) : ¬ VecAgreeOps (simEnv B) P := fun O => not_narrow_of hB O.narrow

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
