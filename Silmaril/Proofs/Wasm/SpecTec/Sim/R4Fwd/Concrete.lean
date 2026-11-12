module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.Assembly

/-!
# The forward conjunct for the concrete `B`, with no coverage restriction

`forward_concrete4`: `forward_all` at `B := Prims.builtins (Profile.spec nd r) hn host`, with the
float primitives, the byte primitives and the bitwise vector primitives discharged (`floatB_builtins`,
`bytesFuns_builtins`, `vvB_builtins`) and `Whole.Assumptions` built from round 2's `Residue`
(`Integrate.assumptions_concrete`). What it still takes: `Residue`, `Extra` (round 2's bundles,
unchanged) and `Open4`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics
open Integrate (Residue Extra)

variable {H : Type}

/-- **`Prims.builtins` answers `$zbytes_`** by `ZBytes.zbytesCall`. -/
theorem zB_builtins {prof : Numerics.Profile} (hn : H → String) (host : HostSemantics H) :
    ZBytes.ZB (Prims.builtins prof hn host) := by
  intro zt c v h
  show Prims.call prof hn host "zbytes_" [.val zt, .val c] = some v
  simp [Prims.call, Floats.floatCall, Floats.floatNames, IntNumeric.intCall, h]

/-- **`ExpandInv` for `Prims.builtins`**: `Prims.expand_of_dderives`. -/
theorem expandInv_builtins {prof : Numerics.Profile} (hn : H → String)
    (host : HostSemantics H) : ExpandInv (simEnv (Prims.builtins prof hn host)) :=
  fun _ _ _ h => Prims.expand_of_dderives h

/-- **The forward conjunct for the concrete `B`, on every configuration with a bounded store**, up
to call annotations, from `Residue`, `Extra` and the per-class obligations `Open4`. -/
theorem forward_concrete4 {hn : H → String} {host : HostSemantics H}
    (hf : HostFinite host) (hr : Prims.HostRespects hn host) (nd : Bool) (r : RelaxedChoice)
    (O : Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn)
    (X : Extra (simEnv (Prims.builtins (Profile.spec nd r) hn host)))
    (O4 : Open4 (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r)) :
    Forward (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r) host
      fun _ => True := by
  intro c c' _ hst hc hc' h
  obtain ⟨d', he, -, hs⟩ := forward_all (Integrate.assumptions_concrete hf hr O) X
    (Prims.floatB_builtins hn host) (FwdMem.bytesFuns_builtins _ hn host)
    (FwdSimdAgg.vvB_builtins hn host) (zB_builtins hn host) (expandInv_builtins hn host) O4 h hst
    hc hc'
  exact ⟨d', he, hs⟩

/-- The same, for every validity predicate `V` on the source configuration (what a restated
target with Core validity needs). -/
theorem forward_concrete4_valid {hn : H → String} {host : HostSemantics H}
    (hf : HostFinite host) (hr : Prims.HostRespects hn host) (nd : Bool) (r : RelaxedChoice)
    (O : Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn)
    (X : Extra (simEnv (Prims.builtins (Profile.spec nd r) hn host)))
    (O4 : Open4 (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r))
    (V : Config H → Prop) :
    Forward (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r) host V :=
  (forward_concrete4 hf hr nd r O X O4).mono fun _ _ => trivial

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
