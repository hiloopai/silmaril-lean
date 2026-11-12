module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.SubElim
public import Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Agree.Thms

/-!
# Round 6: the target from the introduction half of `AgreeTy`

* `agreeTy_of_intro`: on the concrete builtins, `RefOkV.AgreeTy` is its introduction half
  `AgreeTyIntro` together with the proved `okElim_BI` and `subElim_BI`;
* `openR_backend_of_intro`, `wholeStepValidR_backend_of_intro`, `runsR_backend_of_intro`: so
  `Target.OpenR Int.backend`, `Round6.Task.wholeStepValidR Int.backend` and its multi-step
  corollary follow from `AgreeTyIntro` alone (pass 3's `Int.*_backend_of_agreeTy`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)
open Round5.Target (BoundedReachSel)
open Target (DetSteps RSteps)

variable {H : Type} {hn : H → String} {host : HostSemantics H}

/-- **`AgreeTy` on the concrete builtins is its introduction half**: the elimination fields are
`okElim_BI` and `subElim_BI`. -/
theorem agreeTy_of_intro {prof : Silmaril.Wasm.Numerics.Profile}
    (A : AgreeTyIntro (simEnv (Prims.builtins prof hn host))) :
    RefOkV.AgreeTy (simEnv (Prims.builtins prof hn host)) :=
  ⟨A.okIntro, A.subIntro, okElim_BI, subElim_BI⟩

/-- `Target.OpenR Int.backend` from `AgreeTyIntro`. -/
theorem openR_backend_of_intro {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (A : AgreeTyIntro (simEnv (BI (Profile.spec nd r) hn host))) :
    Target.OpenR Int.backend hn (Profile.spec nd r) host :=
  Int.openR_backend_of_agreeTy hinj hf hh (agreeTy_of_intro A)

/-- **`Round6.Task.wholeStepValidR Int.backend` from `AgreeTyIntro`** at every injective
encoding, finite `HostOk` host and spec profile. -/
theorem wholeStepValidR_backend_of_intro
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          AgreeTyIntro (simEnv (BI (Profile.spec nd r) hn host))) :
    Round6.Task.wholeStepValidR Int.backend :=
  Int.wholeStepValidR_backend_of_agreeTy fun H hn hinj host hf hh nd r =>
    agreeTy_of_intro (h H hn hinj host hf hh nd r)

/-- **The multi-step corollary at the backend reading, from `AgreeTyIntro`.** -/
theorem runsR_backend_of_intro {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (A : AgreeTyIntro (simEnv (BI (Profile.spec nd r) hn host))) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps Int.backend (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ →
      RSteps Int.backend (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  Int.runsR_backend_of_agreeTy hinj hf hh (agreeTy_of_intro A)

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
