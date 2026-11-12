module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.UpTo

/-!
# The concrete `B`

* `bytesFuns_builtins`: `Prims.builtins` answers `$nbytes_`/`$ibytes_` by Core's little-endian
  encoding (`Prims.call`'s `FwdMem.nbytesCall`/`ibytesCall` entries), so `BytesFuns` holds.
* `sliceTotal`: with upstream item U2 applied, `SliceTotal` holds, so the
  fragment includes every scalar load and store (`Covered3 true`).
* `forward3_concrete`: `forward_upTo` for `Prims.builtins (Profile.spec nd r) hn host`, from
  `Integrate.Residue` and `Integrate.Extra` (round 2's bundles, unchanged), on `Covered3 true`.
* `wholeStepBounded_of_concrete3`: round 2's `Integrate.wholeStepBounded_of_concrete` with the
  forward premise needed only outside the wider fragment `Covered3 true`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics
open Integrate (Residue Extra BwdOpen StoreOk)

variable {H : Type}

set_option maxRecDepth 100000 in
theorem findDef_nbytes (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "nbytes_" = some (ps, t, []) := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_ibytes (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "ibytes_" = some (ps, t, []) := ⟨_, _, rfl⟩

/-- **`BytesFuns` for the concrete `B`.** -/
theorem bytesFuns_builtins (prof : Profile) (hn : H → String) (host : HostSemantics H) :
    BytesFuns (simEnv (Prims.builtins prof hn host)) where
  nbytes v := by
    obtain ⟨t, b⟩ := v
    have h : (Prims.builtins prof hn host).call "nbytes_"
        [.val (Encode.toValue t), .val (numV ⟨t, b⟩)] =
        some (.list (leBytesV (t.width / 8) b.toNat)) := by
      rw [Typing.toValue_numType]
      simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames,
        nbytesCall, Floats.decNumType_numTypeV, Floats.decNum_numV]
    exact Prims.applies_of_noClause (findDef_nbytes _) h
  ibytes N k := by
    have h : (Prims.builtins prof hn host).call "ibytes_"
        [.val (.num (.natN N)), .val (Silmaril.SpecTec.Equiv.Execution.pctV k)] =
        some (.list (leBytesV (N / 8) k)) := by
      simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames,
        ibytesCall, Silmaril.SpecTec.Equiv.Execution.pctV]
    exact Prims.applies_of_noClause (findDef_ibytes _) h

/-- **Slices are total up to the end of the list**, now that the ported evaluator uses the bound
`i + n ≤ |vs|` (upstream item U2, applied by its proof). -/
theorem sliceTotal : SliceTotal :=
  ⟨fun vs i n h => by simp [Value.slice?, h],
    fun vs ws i n h => by simp [Value.setSlice, h]⟩

/-- **Core → SpecTec for the concrete `B`, on the round-3 fragment, up to call annotations.** -/
theorem forward3_concrete {hn : H → String} {host : HostSemantics H}
    (hf : HostFinite host) (hr : Prims.HostRespects hn host) (nd : Bool) (r : RelaxedChoice)
    (O : Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn)
    (X : Extra (simEnv (Prims.builtins (Profile.spec nd r) hn host)))
    (c c' : Config H) (hcov : Covered3 true c)
    (hc : Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c)
    (hc' : Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c')
    (h : Step (Profile.spec nd r) host c c') :
    ∃ d', Bwd.ConfigEq c' d' ∧
      SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c) (configV hn d') := by
  obtain ⟨d', he, -, hs⟩ := forward_upTo (Integrate.assumptions_concrete hf hr O) X
    (Prims.floatB_builtins hn host) (bytesFuns_builtins _ hn host)
    (FwdSimdAgg.vvB_builtins hn host) (fun _ => sliceTotal) h hcov hc hc'
  exact ⟨d', he, hs⟩

/-- **`Integrate.Task.wholeStepBounded`, reduced to the open bundles for the concrete `B`, on the
round-3 fragment**: as `Integrate.wholeStepBounded_of_concrete`, with the forward direction
needed only outside `Covered3 true`. -/
theorem wholeStepBounded_of_concrete3
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Prims.HostRespects hn host ∧
        Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn ∧
        Extra (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
        BwdOpen (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r) host ∧
        (∀ c c' : Config H, ¬ Covered3 true c → StoreOk c.store →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c' →
          Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧
            SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c)
              (configV hn d'))) :
    Integrate.Task.wholeStepBounded := by
  intro H hn hinj host hfin nd r
  obtain ⟨hr, O, X, Bo, hrest⟩ := h H hn hinj host hfin nd r
  refine ⟨Prims.builtins (Profile.spec nd r) hn host, fun c c' hst hc hc' hs => ?_,
    fun c w hc hs => Integrate.backward_concrete hfin hr nd r O Bo c w hc hs⟩
  by_cases hcov : Covered3 true c
  · exact forward3_concrete hfin hr nd r O X c c' hcov hc hc' hs
  · exact hrest c c' hcov hst hc hc' hs

end Silmaril.Wasm.SpecTec.Sim.FwdMem
