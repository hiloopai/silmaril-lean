module

public import Silmaril.Wasi.Versions.FwdT.Defs
public import Silmaril.Wasi.Versions.Stateful.Thms

@[expose] public section

/-!
# Forwarding with translated answers: theorems

PROVED (standard axioms):

* **`fwdT_inv`**: a simulation `FwdSim` is an invariant (`WpInv`) of the forwarder.
* **`fwdT_model`**: over every host of the import theory, the forwarder is a model of the
  export theory.
-/

namespace Silmaril.Wasi.Versions

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.Net (gated)

/-- **A simulation is an invariant of the forwarder.** -/
theorem fwdT_inv {ST SG : Type} {X I : Set FnName} {tgt : FnName → FnName}
    {hto : ∀ f ∈ X, tgt f ∈ I} {tr : FnName → Option (List Val) → Option (List Val)}
    {iT : ST} {nT : ST → WEv → ST} {okT : ST → WEv → Bool}
    {iG : SG} {nG : SG → WEv → SG} {okG : SG → WEv → Bool} {R : ST → SG → Prop}
    (hS : FwdSim X tgt tr iT nT okT iG nG okG R) :
    WpInv (fwdT X I tgt hto tr) () (gated iT nT okT) (gated iG nG okG) (fun _ qT qG => R qT qG) where
  init := hS.init
  call := by
    intro _ qT qG q hR r qT' hT
    have hT' : (if okT qT (.imp (tgt q.1.1) q.2 r) then some (nT qT (.imp (tgt q.1.1) q.2 r))
        else none) = some qT' := hT
    have hok : okT qT (.imp (tgt q.1.1) q.2 r) = true := by
      by_contra hn
      simp [hn] at hT'
    have hq : qT' = nT qT (.imp (tgt q.1.1) q.2 r) := by simpa [hok, eq_comm] using hT'
    have hs := hS.step qT qG q.1.1 q.2 r q.1.2 hR hok
    refine ⟨nG qG (.imp q.1.1 q.2 (tr q.1.1 r)), ?_, hq ▸ hs.2⟩
    show (if okG qG (.imp q.1.1 q.2 (tr q.1.1 r)) then some _ else none) = some _
    simp only [hs.1, ↓reduceIte]

/-- **The translating forwarder is a model of the export theory over every host of the import
theory.** -/
theorem fwdT_model {ST SG : Type} {X I : Set FnName} {tgt : FnName → FnName}
    {hto : ∀ f ∈ X, tgt f ∈ I} {tr : FnName → Option (List Val) → Option (List Val)}
    {iT : ST} {nT : ST → WEv → ST} {okT : ST → WEv → Bool}
    {iG : SG} {nG : SG → WEv → SG} {okG : SG → WEv → Bool} {R : ST → SG → Prop}
    (hS : FwdSim X tgt tr iT nT okT iG nG okG R) {Y : Sig.{0}} {η : Host Y I}
    (hη : (hostSat (gated iT nT okT).Accepts).holds η) :
    (hostSat (gated iG nG okG).Accepts).holds (link η (ofSBody (fwdT X I tgt hto tr) ())) :=
  link_model (ag_of_wpInv (fwdT_inv hS)) hη

end Silmaril.Wasi.Versions
