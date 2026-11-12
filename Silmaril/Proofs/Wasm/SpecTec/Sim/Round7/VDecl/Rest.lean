module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.Fires

/-!
# Round 7, memory SIMD: `OpenRMRest.rest` at `BM` is the same obligation at `BI`

`OpenRMRest.rest` is `BackwardUpToDRestS NoCastVM (simEnv BM) hn P host`, with
`BM = withVBytes (Prims.builtins P hn host)` and `BI = Prims.builtins P hn host`. Its three fields
read `TypedD` and `Fires` of `Step_pure` (every rule), `Step_read` (rules outside 42–51, so not
43) and `Step` (rules from 6 on, outside 22–25, so not 23). All three move across `withVBytes`
(`typedD_iff`, `fires_*_iff`), so the obligation is the same at the two builtins
(`backwardUpToDRestS_withVBytes_iff`), for every predicate `V`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.VAgree (AgreeOff agreeOff_symm agreeOff_withVBytes)
open Round7.MemSimd (BackwardUpToDRestS TypedD msReadRules stepMSRules)

variable {B₁ B₂ : Builtins} {H : Type}

/-- `TypedD` reads alike at builtins that agree off `$vbytes_`. -/
theorem typedD_iff (hB : AgreeOff B₁ B₂) (hn : H → String) (c : Config H) :
    TypedD (simEnv B₁) hn c ↔ TypedD (simEnv B₂) hn c :=
  hasTyp_iff hB Round7.VAgree.defsOk_empty typsG_empty rg_config

theorem ne43_of_not_ms {i : Nat} (hi : i ∉ msReadRules) : i ≠ 43 := by
  intro h
  exact hi (by rw [h]; decide)

theorem not_ctx_of_not_ms {i : Nat} (h6 : 6 ≤ i) (hi : i ∉ stepMSRules) :
    i ∉ [1, 2, 3, 4, 5, 23] := by
  intro hm
  have h23 : i ≠ 23 := fun h => hi (by rw [h]; decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  omega

/-- **The obligations off memory SIMD move from `B₂` to `B₁`.** -/
theorem backwardUpToDRestS_agree (hB : AgreeOff B₁ B₂) {V : Config H → Prop} {hn : H → String}
    {P : Profile} {host : HostSemantics H}
    (h : BackwardUpToDRestS V (simEnv B₂) hn P host) : BackwardUpToDRestS V (simEnv B₁) hn P host where
  pure i s f is w hV hT hF :=
    h.pure i s f is w hV ((typedD_iff hB hn _).1 hT) ((fires_pure_iff hB i _).1 hF)
  read i hi c w hV hT hF :=
    h.read i hi c w hV ((typedD_iff hB hn c).1 hT) ((fires_read_iff hB (ne43_of_not_ms hi) _).1 hF)
  step i h6 hi c w hV hT hF :=
    h.step i h6 hi c w hV ((typedD_iff hB hn c).1 hT)
      ((fires_step_iff hB (not_ctx_of_not_ms h6 hi) _).1 hF)

/-- **`OpenRMRest.rest` at `withVBytes B` is the same obligation at `B`**, for every predicate
`V`. At `B = Prims.builtins P hn host` and `V = NoCastVM`, the left side is `OpenRMRest.rest`
(stated at `BM`) and the right side is the obligation at round 6's builtins `BI`. -/
theorem backwardUpToDRestS_withVBytes_iff (B : Builtins) (V : Config H → Prop) (hn : H → String)
    (P : Profile) (host : HostSemantics H) :
    BackwardUpToDRestS V (simEnv (MemSimd.withVBytes B)) hn P host ↔
      BackwardUpToDRestS V (simEnv B) hn P host :=
  ⟨backwardUpToDRestS_agree (agreeOff_symm (agreeOff_withVBytes B)),
    backwardUpToDRestS_agree (agreeOff_withVBytes B)⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
