module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XFam
public import Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Thms

/-!
# Existence of `Step_pure`/`Step_read` facts at `Wasm30.builtins`, by inversion

What is known of the choice-made primitives `Wasm30.builtins` is round 6's whole-step theorem:
on `DomDet`, Core's successor is a `Step` observation of `stepModel builtins` up to `CfgRel`
(`FwdX30Fin.stepObs_builtins`). At a checked flat redex that `Step` fact can only come from
`Step/pure` (`Step/read`) at the whole redex, whatever the primitives (`spure_of_sstep_flat`,
`sread_of_sstep_flat`). Reading the fact backwards gives the `Step_pure` (`Step_read`) fact,
with no law of the primitives used.

* `pureFlat_builtins`, `readFlat_builtins`: the inversion at `builtins`, for a Core step.
* `pureX_builtins`: **every `FwdX30.PureHeadX` redex** has a `Step_pure` fact of
  `stepModel builtins`, to Core's successor up to `CfgRel` (`FwdB30.pureG_builtins` on
  `PureG`, the inversion on the rest).
* `readR_builtins`: the same for `Step_read` at `FwdB30.ReadG` and `ReadB` redexes.
* `pureX_two_sided`, `readR_two_sided`: with `FwdX30Fin`'s uniqueness, at these redexes the
  `Step_pure` (`Step_read`) facts of `stepModel builtins` to typed code exist and are all
  Core's successor up to `CfgRel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdX30 (PureHeadX)
open Silmaril.Wasm.SpecTec.Institution.FwdB30 (PureG ReadG)

variable {H : Type}

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- `CfgRel` is reflexive on images. -/
theorem cfgRel_refl (c : Config H) : SpecTec.CfgRel hn (configV hn c) (configV hn c) :=
  ⟨c, c, Bwd.ConfigEq.refl c, rfl, rfl⟩

/-- **Inversion at `builtins`, `Step_pure`**: on `DomDet`, at a checked flat redex, a Core step
has a `Step_pure` fact of `stepModel builtins` to its successor up to `CfgRel`. -/
theorem pureFlat_builtins {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') {k : Nat} {t : IL.MixopS} (hfl : FlatA k t c.code)
    (hok : pureOk k t = true) :
    ∃ js, (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js]) ∧
      SpecTec.CfgRel hn (configV hn c') (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨⟨w, hw, hrel⟩, -⟩ := FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hs
  have hw' : SStep EB (configV hn c) w :=
    (Round6.Transfer.sstepB_iff_of_not_castRedex _ hn hfl.2 w).1 hw
  rw [Bwd.configV_eq] at hw'
  obtain ⟨js, rfl, hp⟩ := spure_of_sstep_flat (tables_simEnv _) hfl.1 hok hw'
  exact ⟨js, (Round6.Reading.sPureB_iff _).2 hp, hrel⟩

/-- **Inversion at `builtins`, `Step_read`**: on `DomDet`, at a checked flat redex, a Core step
has a `Step_read` fact of `stepModel builtins` to its successor up to `CfgRel`. -/
theorem readFlat_builtins {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') {k : Nat} {t : IL.MixopS} (hfl : FlatA k t c.code)
    (hok : readOk k t = true) :
    ∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn c') (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨⟨w, hw, hrel⟩, -⟩ := FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hs
  have hw' : SStep EB (configV hn c) w :=
    (Round6.Transfer.sstepB_iff_of_not_castRedex _ hn hfl.2 w).1 hw
  rw [Bwd.configV_eq] at hw'
  obtain ⟨js, rfl, hp⟩ := sread_of_sstep_flat (tables_simEnv _) hfl.1 hok hw'
  rw [← Bwd.configV_eq] at hp
  exact ⟨js, (Round6.Transfer.sReadB_iff_noCast hfl.2).2 hp, hrel⟩

/-- **Every `PureHeadX` redex has its `Step_pure` fact at `builtins`**, to Core's successor up
to `CfgRel`. -/
theorem pureX_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hp : PureHeadX (Profile.spec nd r) c.code is') :
    ∃ js, (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact hp.step
  rcases pureHeadX_cases hp with hg | ⟨k, t, hm, hfl⟩
  · exact ⟨_, (FwdB30.pureG_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hg).1,
      cfgRel_refl _⟩
  · exact pureFlat_builtins hc hs hfl (pureCombos_ok hm)

/-- **Every `ReadG` or `ReadB` redex has its `Step_read` fact at `builtins`**, to Core's
successor up to `CfgRel`. -/
theorem readR_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadG c is' ∨ ReadB (Profile.spec nd r) c is') :
    ∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  rcases hr with hg | hb
  · exact ⟨_, (FwdB30.readG_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hg).1,
      cfgRel_refl _⟩
  · obtain ⟨k, t, hm, hfl⟩ := readB_flat hb
    exact readFlat_builtins hc hb.toX.step hfl (readCombos_ok hm)

/-- **`Step_pure` at `builtins` is two-sided at every `PureHeadX` redex**: on `DomDet`, there
is a `Step_pure` fact of `stepModel builtins` to Core's successor up to `CfgRel`, and every
`Step_pure` fact from the code to typed code is that successor up to `CfgRel`. -/
theorem pureX_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin}
    (hp : PureHeadX (Profile.spec nd r) c.code is') :
    (∃ js, (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js)) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact hp.step
  exact ⟨pureX_builtins hc hp, fun _ hjs hq => FwdX30Fin.pureFact_unique_builtins hc hs hjs hq⟩

/-- **`Step_read` at `builtins` is two-sided at every `ReadG` and `ReadB` redex**: on
`DomDet`, there is a `Step_read` fact of `stepModel builtins` to Core's successor up to
`CfgRel`, and every `Step_read` fact from `c` to typed code is that successor up to `CfgRel`. -/
theorem readR_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin}
    (hr : ReadG c is' ∨ ReadB (Profile.spec nd r) c is') :
    (∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js)) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    rcases hr with hg | hb
    · exact (hg.toX (P := Profile.spec nd r)).step
    · exact hb.toX.step
  exact ⟨readR_builtins hc hr, fun _ hjs hq => FwdX30Fin.readFact_unique_builtins hc hs hjs hq⟩

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
