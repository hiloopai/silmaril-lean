module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Generic
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Thms

/-!
# Round 6: the cast leaf at the backend reading, from `RefOkBB`

* `castsBwd`: `Target.Casts.bwd` at the backend reading. The witness `d` of a valid `BoundedSel`
  configuration `c` is typed and `ReadValidS`, so `backwardB` turns its `SStepB` step into a Core
  step of `d` up to `ConfigEq`; Core respects `ConfigEq` (`Bwd.step_respects`), so `c` takes the
  matching step; the successor's witness is typed when the successor is (`succTypedB`).
* `casts_backend_of_refOkBB`: `Target.Casts Int.backend`, from `RefOkBB`, for an injective
  encoding, a finite `HostOk` host and a profile in which growth may both succeed and fail;
  `casts_backend_spec_of_refOkBB` at `Profile.spec nd r`.
* `backwardR_backend_of_refOkBB`: the backward half of `Round6.Task.wholeStepValidR Int.backend`
  at every configuration (cast redex or not), from `RefOkBB` alone.
* `wholeStepValidR_backend_of_refOkBB`: the whole target at the backend reading from `RefOkBB`
  and the forward transfer lemma `TransferFwd` (`Target.Transfer.fwd`) alone.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel)
open Round4Int (BI)
open Round5.Target (BoundedSel typed_of_configOk_sel)
open Reading (RefOkBB SStepB)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The backward half of the cast leaf at the backend reading, from `CastRefOk`** at
`ReadValidS c ∧ W c`, for `W` closed under the context decompositions and holding at the
witness (round 6, track casts-v). It does not use the cast redex. -/
theorem castsBwdG (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    {W : Config H → Prop} (CW : Target.CtxClosedVals W)
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn (fun c => Round5.Read.ReadValidS c ∧ W c))
    (c d : Config H) (ts : List CValType) (w : Value)
    (hc : ConfigOk c ts) (hb : BoundedSel c) (hd : SimRel (BI P hn host) hn c d) (hw : W d)
    (hs : SStepB (simEnv (BI P hn host)) (configV hn d) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧
      (Typed (simEnv (BI P hn host)) hn c' → Typed (simEnv (BI P hn host)) hn d') ∧
      w = configV hn d' ∧ Step P host c c' := by
  have hv₀ : Round5.Read.ReadValidS c := Round5.Read.readValidS_of_bounded hc hb.1.1
  have hv : Round5.Read.ReadValidS d := Round5.Int2.readValidS_of_configEq hd.1 hv₀
    (Round5.Multi.witnessBnd _ hn c d hv₀.bnd hd.1 hd.2)
  obtain ⟨c₂, d₂, h₁, rfl, hst⟩ := backwardG hinj hf hPs hPf CW K d w hv hw hd.2 hs
  obtain ⟨c', hst', h₂⟩ := Bwd.step_respects hst c (Round4.configEq_symm hd.1)
  have he : Bwd.ConfigEq c' d₂ := Round5.Multi.configEq_trans (Round4.configEq_symm h₂) h₁
  exact ⟨c', d₂, he, fun htc' => succTypedB _ hn d d₂ c' hd.2 hs he htc', rfl, hst'⟩

/-- **The backward half of the cast leaf at the backend reading**, from `RefOkBB`. It does not
use the cast redex: it holds at every witness of a valid `BoundedSel` configuration. -/
theorem castsBwd (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (KB : RefOkBB (simEnv (BI P hn host))) (c d : Config H) (ts : List CValType) (w : Value)
    (hc : ConfigOk c ts) (hb : BoundedSel c) (hd : SimRel (BI P hn host) hn c d)
    (hs : SStepB (simEnv (BI P hn host)) (configV hn d) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧
      (Typed (simEnv (BI P hn host)) hn c' → Typed (simEnv (BI P hn host)) hn d') ∧
      w = configV hn d' ∧ Step P host c c' :=
  castsBwdG hinj hf hPs hPf true_closed (Reading.castRefOk_bnd KB fun _ h => h.1.frame) c d ts w
    hc hb hd trivial hs

/-- **The cast leaf of the round-6 target at the backend reading, from `RefOkBB`**: both halves
of `Target.Casts Int.backend`, for an injective encoding, a finite `HostOk` host and a profile in
which growth may both succeed and fail. -/
theorem casts_backend_of_refOkBB (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (KB : RefOkBB (simEnv (BI P hn host))) :
    Target.Casts Int.backend (BI P hn host) hn P host where
  fwd c d c' ts hc hb hsucc hd hx hs := castsFwd hh KB c d c' ts hc hb hsucc hd hx hs
  bwd c d ts w hc hb hd _ hs := castsBwd hinj hf hPs hPf KB c d ts w hc hb hd hs

/-- `casts_backend_of_refOkBB` at the spec profile. -/
theorem casts_backend_spec_of_refOkBB {nd : Bool} {r : RelaxedChoice}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (KB : RefOkBB (simEnv (BI (Profile.spec nd r) hn host))) :
    Target.Casts Int.backend (BI (Profile.spec nd r) hn host) hn (Profile.spec nd r) host :=
  casts_backend_of_refOkBB hinj hf hh (Round5.BwdStep.growMaySucceed_spec nd r)
    (Round4.growMayFail_spec nd r) KB

/-- **The backward half of `Round6.Task.wholeStepValidR Int.backend`, from `RefOkBB`**, at one
injective encoding, finite host and spec profile, with `B := Prims.builtins`: every step of the
backend reading from the image of a valid `BoundedSel` configuration is the image of a Core step,
up to `ConfigEq`. Neither the transfer lemma nor a cast redex is needed. -/
theorem backwardR_backend_of_refOkBB {nd : Bool} {r : RelaxedChoice}
    (hinj : Function.Injective hn) (hf : HostFinite host)
    (KB : RefOkBB (simEnv (BI (Profile.spec nd r) hn host))) (c : Config H)
    (ts : List CValType) (w : Value) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hs : Int.backend.step (BI (Profile.spec nd r) hn host) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c' :=
  backwardB hinj hf (Round5.BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r) KB c
    w (Round5.Read.readValidS_of_bounded hc hb.1.1) (typed_of_configOk_sel _ hn hc hb) hs

/-- The forward transfer lemma alone (`Target.Transfer.fwd`) at the backend reading: away from
cast redexes, declarative steps from the image of a witness are backend steps. -/
def TransferFwd (B : Builtins) (hn : H → String) : Prop :=
  ∀ (c d : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → BoundedSel c →
    SimRel B hn c d → ¬ Target.CastRedex d.code → SStep (simEnv B) (configV hn d) w →
      SStepB (simEnv B) (configV hn d) w

/-- **The forward half of `Round6.Task.wholeStepValidR Int.backend`, from `RefOkBB` and the
forward transfer lemma** (`Target.fwdR_of_open` with the cast leaf `casts_backend_of_refOkBB`). -/
theorem fwdR_backend_of_refOkBB (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (KB : RefOkBB (simEnv (BI P hn host)))
    (TF : TransferFwd (BI P hn host) hn) (c c' : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hb : BoundedSel c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁)
    (hs : Step P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ Int.backend.step (BI P hn host) (configV hn c) (configV hn d') := by
  have htc := typed_of_configOk_sel (BI P hn host) hn hc hb
  have hr : SimRel (BI P hn host) hn c c := ⟨Bwd.ConfigEq.refl c, htc⟩
  by_cases hx : Target.CastRedex c.code
  · obtain ⟨d', hd', hst⟩ := castsFwd hh KB c c c' ts hc hb hsucc hr hx hs
    exact ⟨c', hs, fun _ => rfl, d', hd'.1, hst⟩
  · obtain ⟨c'', hs'', hu, hfu⟩ := Target.forwardR' hinj hf hs hb.1.1 hx
    have htc'' := typed_of_configOk_sel (BI P hn host) hn (Step.preservation hh hc hs'').1
      (hsucc c'' hs'')
    obtain ⟨d', hd', -, hst⟩ := hfu htc htc''
    exact ⟨c'', hs'', hu, d', hd', TF c c ts _ hc hb hr hx hst⟩

/-- **`Round6.Task.wholeStepValidR Int.backend` from `RefOkBB` and the forward transfer lemma
alone**: the backward transfer lemma (`Target.Transfer.bwd`) is not needed, since
`backwardB` covers every step of the backend reading. -/
theorem wholeStepValidR_backend_of_refOkBB
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          RefOkBB (simEnv (BI (Profile.spec nd r) hn host)) ∧
            TransferFwd (BI (Profile.spec nd r) hn host) hn) :
    Round6.Task.wholeStepValidR Int.backend := fun H hn hinj host hfin hok nd r =>
  have K := h H hn hinj host hfin hok nd r
  ⟨_, fun c c' ts hc hb hsucc hs => fwdR_backend_of_refOkBB hinj hfin hok K.1 K.2 c c' ts hc hb
      hsucc hs,
    fun c ts w hc hb hs => backwardR_backend_of_refOkBB hinj hfin K.1 c ts w hc hb hs⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
