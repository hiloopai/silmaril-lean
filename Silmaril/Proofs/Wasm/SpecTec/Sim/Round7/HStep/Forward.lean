module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.HStep.Step
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# Round 7, `BD`: the whole step between `BD`, `BM` and `BI`, and a piece of `forward` at `BD`

* `sstep_bd_bm_iff`, `sstep_bd_bi_iff`: on sources whose image has no memory SIMD atom and no
  `CALL_REF` (`VInv.NoAtoms hAtoms`), SpecTec's whole step reads alike at `BD` and `BM`, and at
  `BD` and round 6's `BI` (`sstep_iff_h` with `HAgree.agreeOff_bd_bm`, `agreeOff_bd_bi`).
* `forwardD_noMS`: **`RMD.OpenRMRestD.forward` at memory-SIMD-free sources whose image has no
  `CALL_REF`**, when no Core successor has memory SIMD code and the host is `HostOk`. Round 6's
  forward simulation at `BI` (`Round6.Target.forwardR'`) gives a step between `configV` images;
  they are `configVD` images, and the step moves to `BD`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HStep

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (NoMemSimd)
open Round6.Target (CastRedex)
open Round7.MemSimd (BoundedSelM configVD)
open Round7.HostD (BD)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The whole step reads alike at `BD` and `BM`** on sources without memory SIMD atoms and
`CALL_REF`. -/
theorem sstep_bd_bm_iff {c c' : Value} (hc : VInv.NoAtoms hAtoms c) :
    SStep (simEnv (BD P hn host)) c c' ↔ SStep (simEnv (Round7.MemSimd.BM P hn host)) c c' :=
  sstep_iff_h (HAgree.agreeOff_bd_bm P hn host) ⟨c, c', rfl, hc⟩

/-- **The whole step reads alike at `BD` and round 6's `BI`** on the same sources. -/
theorem sstep_bd_bi_iff {c c' : Value} (hc : VInv.NoAtoms hAtoms c) :
    SStep (simEnv (BD P hn host)) c c' ↔ SStep (simEnv (Prims.builtins P hn host)) c c' :=
  sstep_iff_h (HAgree.agreeOff_bd_bi P hn host) ⟨c, c', rfl, hc⟩

/-- **`forward` at `BD` at memory-SIMD-free sources whose image has no `CALL_REF`.** -/
theorem forwardD_noMS (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts) (hb : BoundedSelM c)
    (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelM c₁) (hx : ¬ CastRedex c.code)
    (hm : NoMemSimd c) (hms : ∀ c₁, Step P host c c₁ → NoMemSimd c₁)
    (hA : VInv.NoAtoms hAtoms (configV hn c)) (hs : Step P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d') := by
  obtain ⟨c'', hs'', hu, hF⟩ := Round6.Target.forwardR' hinj hf hs
    (Round7.MemSimd.bounded_of_boundedM hb.1.1 hm) hx
  have hT := VInv.typed_of_typedD hm
    (Round7.MemSimd.typedD_of_configOk_selM (Prims.builtins P hn host) hn hc hb)
  have hc'' := (Step.preservation hh hc hs'').1
  have hT'' := VInv.typed_of_typedD (hms _ hs'')
    (Round7.MemSimd.typedD_of_configOk_selM (Prims.builtins P hn host) hn hc''
      (hsucc _ hs''))
  obtain ⟨d', hd', -, hst⟩ := hF hT hT''
  refine ⟨c'', hs'', hu, d', hd', ?_⟩
  rw [Round7.MemSimd.configVD_eq_of_noMemSimd hn hm,
    Round7.MemSimd.configVD_eq_of_noMemSimd hn (VInv.noMemSimd_of_configEq hd' (hms _ hs''))]
  exact (sstep_bd_bi_iff hA).2 hst

end Silmaril.Wasm.SpecTec.Sim.Round7.HStep
