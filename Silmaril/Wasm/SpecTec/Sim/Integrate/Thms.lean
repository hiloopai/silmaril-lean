module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Integrate.Concrete
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Integrate.NonVacuous

/-!
# SpecTec ↔ Core 3.0, round 2 integration: what is proved

Neither frozen goal (`Task.wholeStep`, `Bwd.Task.wholeStepUpTo`) is proved. What the round-2
tracks prove is assembled here for **one concrete `B`**, `Prims.builtins (Profile.spec nd r) hn
host`, with every remaining hypothesis an explicit, named bundle:

* `forward_concrete` (Core → SpecTec): on the widened fragment `Integrate.Covered` (no SIMD
  operator but `v128.const` and the bitwise ones, no load or store, no `array.new_elem`,
  `array.new_data`, `array.init_data`, no `return_call_ref`; unpacked aggregate types; `StoreOk` store bounds), under `Residue` (typing
  of the runtime type syntax, results and function instances; `RefOkBridge`, `$inst_reftype`)
  and `Extra` (the memory and aggregates tracks' interfaces). `CtrlCall.default` is proved
  (`ctrlCallDefault_simEnv`), as is the converse of `$hostcall` (`hostInv_concrete`).
* `backward_concrete` (SpecTec → Core, up to call annotations, `Bwd.ConfigEq`): for every typed
  configuration, under `Residue` and `BwdOpen` (exception-field typing and the backward rules
  without a lemma, `RemainingW`).
* `wholeStepUpTo_of_concrete`: `Bwd.Task.wholeStepUpTo` follows from those bundles together with
  the forward direction outside the fragment, for every host. Its premises are not all true as
  stated: outside `StoreOk` and at the load boundary (obstruction 2) the forward direction fails
  (memory and aggregates tracks; see `docs/projects/spectec/README.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Integrate

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-- **Core → SpecTec for the concrete `B`, on the widened fragment.** -/
theorem forward_concrete {H : Type} {hn : H → String} {host : HostSemantics H}
    (hf : HostFinite host) (hr : Prims.HostRespects hn host) (nd : Bool) (r : RelaxedChoice)
    (O : Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn)
    (X : Extra (simEnv (Prims.builtins (Profile.spec nd r) hn host)))
    (c c' : Config H) (hcov : Covered c)
    (hc : Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c)
    (hc' : Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c')
    (h : Step (Profile.spec nd r) host c c') :
    SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c) (configV hn c') :=
  forward_wide (assumptions_concrete hf hr O) X (Prims.floatB_builtins hn host)
    (FwdSimdAgg.vvB_builtins hn host) h hcov hc hc'

/-- **SpecTec → Core for the concrete `B`, up to call annotations**, for every typed
configuration. -/
theorem backward_concrete {H : Type} {hn : H → String} {host : HostSemantics H}
    (hf : HostFinite host) (hr : Prims.HostRespects hn host) (nd : Bool) (r : RelaxedChoice)
    (O : Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn)
    (Bo : BwdOpen (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r) host)
    (c : Config H) (w : Value)
    (hc : Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c)
    (hs : SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c' :=
  Bwd.simEnv_backward_upTo _ (bwdHyps_concrete hf hr O Bo) (Typing.typingFacts_simEnv _ hn)
    (remaining_of_w (Prims.intB_builtins hn host) (Prims.floatB_builtins hn host)
      (BwdPureStep.bwdB_builtins hn host) (BwdRead.noAcc_builtins _ hn host) Bo.remaining)
    c w hc hs

/-- **`Bwd.Task.wholeStepUpTo`, reduced to the open bundles for the concrete `B`**: for every
injectively named finite host and every `nd`, `r`, a host respecting the encoding, `Residue`,
`Extra`, `BwdOpen`, and the forward direction (up to `ConfigEq`) from configurations outside the
fragment `Covered`. -/
theorem wholeStepUpTo_of_concrete
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Prims.HostRespects hn host ∧
        Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn ∧
        Extra (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
        BwdOpen (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r) host ∧
        (∀ c c' : Config H, ¬ Covered c →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c' →
          Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧
            SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c)
              (configV hn d'))) :
    Bwd.Task.wholeStepUpTo := by
  intro H hn hinj host hfin nd r
  obtain ⟨hr, O, X, Bo, hrest⟩ := h H hn hinj host hfin nd r
  refine ⟨Prims.builtins (Profile.spec nd r) hn host, fun c c' hc hc' hs => ?_,
    fun c w hc hs => backward_concrete hfin hr nd r O Bo c w hc hs⟩
  by_cases hcov : Covered c
  · exact ⟨c', Bwd.ConfigEq.refl _, forward_concrete hfin hr nd r O X c c' hcov hc hc' hs⟩
  · exact hrest c c' hcov hc hc' hs

/-- **`Task.wholeStepBounded` (the round-2 target), reduced to the open bundles for the concrete
`B`**: as `wholeStepUpTo_of_concrete`, but the forward direction outside the fragment is only
needed from stores satisfying `StoreOk`. -/
theorem wholeStepBounded_of_concrete
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Prims.HostRespects hn host ∧
        Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn ∧
        Extra (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
        BwdOpen (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r) host ∧
        (∀ c c' : Config H, ¬ Covered c → StoreOk c.store →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c' →
          Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧
            SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c)
              (configV hn d'))) :
    Task.wholeStepBounded := by
  intro H hn hinj host hfin nd r
  obtain ⟨hr, O, X, Bo, hrest⟩ := h H hn hinj host hfin nd r
  refine ⟨Prims.builtins (Profile.spec nd r) hn host, fun c c' hst hc hc' hs => ?_,
    fun c w hc hs => backward_concrete hfin hr nd r O Bo c w hc hs⟩
  by_cases hcov : Covered c
  · exact ⟨c', Bwd.ConfigEq.refl _, forward_concrete hfin hr nd r O X c c' hcov hc hc' hs⟩
  · exact hrest c c' hcov hst hc hc' hs

end Silmaril.Wasm.SpecTec.Sim.Integrate

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.forward_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.forward_concrete

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.backward_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.backward_concrete

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.wholeStepUpTo_of_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.wholeStepUpTo_of_concrete

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.forward_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.forward_wide

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.assumptions_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.assumptions_concrete

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.bwdHyps_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.bwdHyps_concrete

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.ctrlCallDefault_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.ctrlCallDefault_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.hostInv_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.hostInv_concrete

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.wholeStepBounded_of_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Integrate.wholeStepBounded_of_concrete

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.Task.wholeStepBounded_of_upTo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Integrate.Task.wholeStepBounded_of_upTo

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.fragment_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.fragment_inhabited

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.remaining_of_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.remaining_of_w

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.callInv_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.callInv_concrete

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Integrate.blockInv_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Integrate.blockInv_concrete
