module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Backward

/-!
# Round 6: `Task.wholeStepValidR` from the transfer lemma and the cast leaf

* `fwdR_of_open`, `bwdR_of_open`, `oneStepR_of_open`: the two halves of the target at one
  encoding, host and profile, from `OpenR` (the transfer lemma `Transfer` and the cast leaf
  `Casts`). Away from cast redexes, the forward half is `forwardR'` (proved, up to Core's choice)
  carried through `Transfer.fwd`, and the backward half is `Transfer.bwd` followed by
  `backwardNC` (proved). At cast redexes both halves are `Casts`.
* `wholeStepValidR_of_open`: `Task.wholeStepValidR Rd` from `OpenR Rd` at every injective
  encoding, finite `HostOk` host and `Profile.spec nd r`.
* `transfer_declarative`: round 5's reading satisfies the transfer lemma, trivially; so the
  transfer lemma alone does not determine a reading, and `Casts` is where the readings differ.
* `wholeStepValidR_declarative_of_sel`: at round 5's reading, the new target asks no more than
  `Round5.Task.wholeStepValidSel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Target

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)
open Round5.Target (BoundedSel typed_of_configOk_sel)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The forward half of the target, from `OpenR`**, for an injective encoding and a finite
`HostOk` host. -/
theorem fwdR_of_open {Rd : Reading} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (O : OpenR Rd hn P host) (c c' : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hb : BoundedSel c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁)
    (hs : Step P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ Rd.step (BI P hn host) (configV hn c) (configV hn d') := by
  have htc := typed_of_configOk_sel (BI P hn host) hn hc hb
  have hr : Round4.SimRel (BI P hn host) hn c c := ⟨Bwd.ConfigEq.refl c, htc⟩
  by_cases hx : CastRedex c.code
  · obtain ⟨d', hd', hst⟩ := O.casts.fwd c c c' ts hc hb hsucc hr hx hs
    exact ⟨c', hs, fun _ => rfl, d', hd'.1, hst⟩
  · obtain ⟨c'', hs'', hu, hfu⟩ := forwardR' hinj hf hs hb.1.1 hx
    have htc'' := typed_of_configOk_sel (BI P hn host) hn (Step.preservation hh hc hs'').1
      (hsucc c'' hs'')
    obtain ⟨d', hd', -, hst⟩ := hfu htc htc''
    exact ⟨c'', hs'', hu, d', hd', O.transfer.fwd c c ts _ hc hb hr hx hst⟩

/-- **The backward half of the target, from `OpenR`**, for an injective encoding, a finite host
and a profile in which growth may both succeed and fail. -/
theorem bwdR_of_open {Rd : Reading} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (O : OpenR Rd hn P host) (c : Config H) (ts : List CValType) (w : Value)
    (hc : ConfigOk c ts) (hb : BoundedSel c) (hs : Rd.step (BI P hn host) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' := by
  have htc := typed_of_configOk_sel (BI P hn host) hn hc hb
  have hr : Round4.SimRel (BI P hn host) hn c c := ⟨Bwd.ConfigEq.refl c, htc⟩
  by_cases hx : CastRedex c.code
  · obtain ⟨c', d', he, -, hw, hst⟩ := O.casts.bwd c c ts w hc hb hr hx hs
    exact ⟨c', d', he, hw, hst⟩
  · exact backwardNC hinj hf hPs hPf c w ⟨Round5.Read.readValidS_of_bounded hc hb.1.1, hx⟩ htc
      (O.transfer.bwd c c ts w hc hb hr hx hs)

/-- **`Task.wholeStepValidR Rd` from the transfer lemma and the cast leaf**, at every injective
encoding, finite `HostOk` host and `Profile.spec nd r`, with `B := Prims.builtins`. -/
theorem wholeStepValidR_of_open (Rd : Reading)
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenR Rd hn (Profile.spec nd r) host) :
    Round6.Task.wholeStepValidR Rd := fun H hn hinj host hfin hok nd r =>
  have O := h H hn hinj host hfin hok nd r
  ⟨_, fun c c' ts hc hb hsucc hs => fwdR_of_open hinj hfin hok O c c' ts hc hb hsucc hs,
    fun c ts w hc hb hs => bwdR_of_open hinj hfin (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) O c ts w hc hb hs⟩

/-- **Round 5's reading satisfies the transfer lemma**, trivially. -/
theorem transfer_declarative (B : Builtins) (hn : H → String) : Transfer declarative B hn :=
  ⟨fun _ _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ _ _ h => h⟩

/-- **At round 5's reading the new target asks no more than `Round5.Task.wholeStepValidSel`**
(vacuously if, as argued, that target is false). -/
theorem wholeStepValidR_declarative_of_sel (h : Round5.Task.wholeStepValidSel) :
    Round6.Task.wholeStepValidR declarative := fun H hn hinj host hfin hok nd r => by
  obtain ⟨B, hF, hB⟩ := h H hn hinj host hfin hok nd r
  exact ⟨B, fun c c' ts hc hb hsucc hs => ⟨c', hs, fun _ => rfl,
    hF c c' ts hc hb (hsucc c' hs) hs⟩, hB⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Target
