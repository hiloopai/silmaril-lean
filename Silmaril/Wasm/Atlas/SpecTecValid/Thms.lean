module

public import Silmaril.Wasm.Atlas.SpecTec.Thms
public import Silmaril.Wasm.Atlas.SpecTecValid.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Thms

/-!
# The step charts on valid configurations: transitions

The SpecTec transition `Atlas.SpecTec.toSpec` wired to :

* `SpecTecValid.fwdOn_of_oneStep`, `bwdOn_of_oneStep`: the round-4 one-step simulation
  (`Round4.OneStep`) gives both conjuncts on `Dom`.
* `SpecTecValid.toSpecValid`: the Core ↔ SpecTec transition on `Dom`, equal on `CfgRel`-respecting
  sentences, from `Round4.OneStep`.
* `SpecTecValid.sat_iff_of_parts`: the same from `Round4Int.Parts` (every field open).
* `SpecTecValid.sat_iff_of_wholeStepValid`: from the frozen target itself, at its own `B`.

All three are **conditional**: `Round4.Task.wholeStepValid` and `Round4Int.Parts` are not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecValid

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec

variable {P : Profile} {H : Type} {host : HostSemantics H} {hn : H → String} {B : Builtins}

/-- The round-4 forward conjunct is `FwdOn` on `Dom`. -/
theorem fwdOn_of_oneStep (h : Sim.Round4.OneStep B hn P host) :
    SpecTec.FwdOn (Sim.simEnv B) P host hn (Dom P host) :=
  fun c ⟨⟨⟨ts, hc⟩, hb⟩, hsucc⟩ c' hs => h.1 c c' ts hc hb (hsucc c' hs) hs

/-- The round-4 backward conjunct is `BwdOn` on `Dom`. -/
theorem bwdOn_of_oneStep (h : Sim.Round4.OneStep B hn P host) :
    SpecTec.BwdOn (Sim.simEnv B) P host hn (Dom P host) :=
  fun c ⟨⟨⟨ts, hc⟩, hb⟩, _⟩ w hs => h.2 c ts w hc hb hs

/-- **Conditional: Core ↔ SpecTec on valid configurations**, from the round-4 one-step
simulation. -/
noncomputable def toSpecValid (h : Sim.Round4.OneStep B hn P host) :
    Transition (SpecTec.coreChart P host hn (Dom P host)) (SpecTec.specChart (Sim.simEnv B)) :=
  SpecTec.toSpec (fwdOn_of_oneStep h) (bwdOn_of_oneStep h)

/-- A `CfgRel`-respecting step sentence holds of a valid `c` in Core iff it holds of its image in
SpecTec, given the round-4 one-step simulation. -/
theorem sat_iff_of_oneStep (h : Sim.Round4.OneStep B hn P host) {c : Config H}
    (hc : Dom P host c) {s : BSen Unit Value} (hs : s.Respects (SpecTec.CfgRel hn)) :
    (SpecTec.coreChart P host hn (Dom P host)).Sat c s ↔
      (SpecTec.specChart (Sim.simEnv B)).Sat (Sim.configV hn c) s :=
  SpecTec.sat_iff_of_sim (fwdOn_of_oneStep h) (bwdOn_of_oneStep h) hc hs

/-- The same, from the integration's `Parts` (concrete `B := Prims.builtins`). -/
theorem sat_iff_of_parts (Pa : Sim.Round4Int.Parts hn P host) {c : Config H}
    (hc : Dom P host c) {s : BSen Unit Value} (hs : s.Respects (SpecTec.CfgRel hn)) :
    (SpecTec.coreChart P host hn (Dom P host)).Sat c s ↔
      (SpecTec.specChart (Sim.simEnv (Sim.Round4Int.BI P hn host))).Sat (Sim.configV hn c) s :=
  sat_iff_of_oneStep (Sim.Round4Int.oneStep_of_parts Pa) hc hs

/-- **From the frozen round-4 target**: for each injective encoding, finite host and
`Profile.spec nd r`, some `B` makes the valid step chart agree with SpecTec's. -/
theorem sat_iff_of_wholeStepValid (h : Sim.Round4.Task.wholeStepValid) (hn : H → String)
    (hinj : Function.Injective hn) (host : HostSemantics H) (hfin : Sim.HostFinite host)
    (nd : Bool) (r : RelaxedChoice) :
    ∃ B : Builtins, ∀ (c : Config H), Dom (Profile.spec nd r) host c →
      ∀ s : BSen Unit Value, s.Respects (SpecTec.CfgRel hn) →
        ((SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host)).Sat c s ↔
          (SpecTec.specChart (Sim.simEnv B)).Sat (Sim.configV hn c) s) := by
  obtain ⟨B, hB⟩ := h H hn hinj host hfin nd r
  exact ⟨B, fun _ hc _ hs => sat_iff_of_oneStep hB hc hs⟩

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Atlas.SpecTecValid.sat_iff_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_of_parts

/-- info: 'Silmaril.Wasm.Atlas.SpecTecValid.sat_iff_of_wholeStepValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_of_wholeStepValid

end Silmaril.Wasm.Atlas.SpecTecValid
