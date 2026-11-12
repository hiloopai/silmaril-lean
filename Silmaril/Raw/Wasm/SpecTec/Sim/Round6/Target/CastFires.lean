module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Cast

/-!
# Round 6: the cast rules fire only on cast redexes

The left-hand-side half of track read's cast lemmas (`Round5.Read.bwdK_*`, in
`Silmaril/Raw/Wasm/SpecTec/Sim/Round5/Read/Cast.lean`), without `Round5.Fwd.RefOkB`: when one of
the eight cast rules of `Step_read` (2–5, 65–68) fires on the image of a configuration, its code
is `[ref r, cast]`, so it is a `CastRedex`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Target

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)
open Round5.Read (cast_inv brCast_inv head_refTest head_refCast)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- `ref.test-true` (65). -/
theorem castRedex_of_65 {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_read" 65 (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body RR.refTestTrue hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.TEST" RT]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨-, -, r, a, rfl, -, ha⟩ := cast_inv hR hcw
  obtain ⟨rt, rfl⟩ := head_refTest (Typing.adminToV_case ha).symm
  exact castRedex_refTest

/-- `ref.test-false` (66). -/
theorem castRedex_of_66 {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_read" 66 (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body RR.refTestFalse hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.TEST" RT]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨-, -, r, a, rfl, -, ha⟩ := cast_inv hR hcw
  obtain ⟨rt, rfl⟩ := head_refTest (Typing.adminToV_case ha).symm
  exact castRedex_refTest

/-- `ref.cast-succeed` (67). -/
theorem castRedex_of_67 {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_read" 67 (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body RR.refCastSucceed hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.CAST" RT]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨-, -, r, a, rfl, -, ha⟩ := cast_inv hR hcw
  obtain ⟨rt, rfl⟩ := head_refCast (Typing.adminToV_case ha).symm
  exact castRedex_refCast

/-- `ref.cast-fail` (68). -/
theorem castRedex_of_68 {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_read" 68 (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body RR.refCastFail hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.CAST" RT]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨-, -, r, a, rfl, -, ha⟩ := cast_inv hR hcw
  obtain ⟨rt, rfl⟩ := head_refCast (Typing.adminToV_case ha).symm
  exact castRedex_refCast

/-- `br_on_cast-succeed` (2). -/
theorem castRedex_of_2 {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_read" 2 (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body RR.brOnCastSucceed hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST" (.tuple [L, RT₁, RT₂])]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨-, -, r, l, rt₁, rt₂, rfl, -⟩ := brCast_inv hR (.inl rfl) hcw
  exact castRedex_brOnCast

/-- `br_on_cast-fail` (3). -/
theorem castRedex_of_3 {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_read" 3 (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body RR.brOnCastFail hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST" (.tuple [L, RT₁, RT₂])]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨-, -, r, l, rt₁, rt₂, rfl, -⟩ := brCast_inv hR (.inl rfl) hcw
  exact castRedex_brOnCast

/-- `br_on_cast_fail-succeed` (4). -/
theorem castRedex_of_4 {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_read" 4 (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body RR.brOnCastFailSucceed hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST_FAIL" (.tuple [L, RT₁, RT₂])]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨-, -, r, l, rt₁, rt₂, rfl, -⟩ := brCast_inv hR (.inr rfl) hcw
  exact castRedex_brOnCastFail

/-- `br_on_cast_fail-fail` (5). -/
theorem castRedex_of_5 {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_read" 5 (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body RR.brOnCastFailFail hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST_FAIL" (.tuple [L, RT₁, RT₂])]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨-, -, r, l, rt₁, rt₂, rfl, -⟩ := brCast_inv hR (.inr rfl) hcw
  exact castRedex_brOnCastFail

/-- **The cast rules of `Step_read` fire only on cast redexes.** -/
theorem castRedex_of_fires_readK {i : Nat} (hi : i ∈ Round5.Read.readDoneK) {c : Config H}
    {w : Value} (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  simp only [Round5.Read.readDoneK, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [castRedex_of_2 hf, castRedex_of_3 hf, castRedex_of_4 hf, castRedex_of_5 hf,
    castRedex_of_65 hf, castRedex_of_66 hf, castRedex_of_67 hf, castRedex_of_68 hf]

end Silmaril.Wasm.SpecTec.Sim.Round6.Target
