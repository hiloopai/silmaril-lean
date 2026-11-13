module

public import Silmaril.Wasm.Game.LinkStart.Defs
public import Silmaril.Wasm.Game.Start.Thms
public import Silmaril.Games.Category.Defs
import Silmaril.Proofs.Wasm.Game.LinkStart.Main
import Silmaril.Proofs.Wasm.Game.LinkStart.Link

/-!
# Static links with start functions: theorems

For an **arbitrary** profile `P` and a link with start functions
(`StartSetup`), its game-semantic link `S.linkInst P` (the provider's
strategy with its start phase below the consumer's instantiable system,
`Silmaril.Games.DStrategy.link`) instantiates the provider, and runs its start
function, **before** the consumer:

## M3 with start functions

The *linked module* with its start sequence is `S.linkedInstStrategy P`: the
closed linked instance whose instantiation runs `S.linkedStarts` (the
provider's start function, then the consumer's, at the same addresses in the
linked store) by `ScalarInstance.instSysSeq`.

* `StartSetup.link_is_composition_inst` (**every profile** `P`): its finite
  plays are those of the game-semantic link,
  `(S.linkedInstStrategy P).forget = (S.linkInst P).forget`; in categorical
  form (`link_is_composition_inst_comp`) the composite, in `Silmaril.Games`, of the
  provider's instantiable strategy with the strategy of the consumer's link
  system. This covers export calls after instantiation (the stores left by the
  start functions persist), failures of either start function, and consumer
  start functions that call the provider.
* `StartSetup.linkInst_instReady_iff`: hence the link is ready exactly when the
  linked module's start sequence returns under the empty host (no restriction
  on the consumer's start function), and
  `linkedInst_instReady_iff_core` for the linked module itself.

The hypotheses are those of `Linking.Setup` (the linker fragment of
`Recipe.Assembly`, scalar interfaces `S.Scalar`) and of `StartSetup` (start
functions of type `[] → []` that are functions of their modules,
`provStartFunc`/`consStartFunc`). `link?` itself rejects start functions, so
the linked module's start sequence is the start-free linked module together
with `S.linkedStarts` (the wasm-merge ordering of an earlier development; in the
linker fragment consumer initialisation evaluates only constant expressions).

## Not shown

Equality of the divergence-observing strategies is not shown here; it is
`link_is_composition_inst_div` in `Silmaril.Wasm.Game.LinkStartDiv`. The Core
side of a start phase is the invocation of the start function at the store
returned by `instantiateOnce?`; the spec's `Config.withStart` run is not
related here.

Proofs: `Silmaril.Proofs.Wasm.Game.LinkStart.*` (new), using the start-function
splitting of `Silmaril.Proofs.Wasm.Game.Linking.Split.Start` and the M3 equations at
reached stores of `Silmaril.Proofs.Wasm.Game.Linking.StartShared`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Games.Inst Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable {I : ScalarInstance} {P : Profile} {s : Store Nat} {start : Option Nat}

/-- Instantiation succeeds without import calls exactly when the start phase may return under
the empty host. -/
theorem closed_instReady_iff :
    (I.instStrategy P s start).InstReady ↔
      ∃ s', StartsTo P (Det.noHost : HostSemantics Nat) s start s' :=
  Silmaril.Proofs.Wasm.Game.LinkStart.instReady_iff

/-- Instantiation fails with `b` without import calls exactly when the start phase may trap or
throw `b` under the empty host. -/
theorem closed_instFails_iff {b : Behaviour Val} :
    (I.instStrategy P s start).InstFails b ↔
      ∃ (c' : Config Nat) (r : Result),
        Steps P (Det.noHost : HostSemantics Nat) (startConfig s start) c' ∧
        c'.code = r.toAdmin ∧ (r = .trap ∨ ∃ x, r = .throw x) ∧ b = r.toBehaviour :=
  Silmaril.Proofs.Wasm.Game.LinkStart.instFails_iff

/-- Instantiation diverges without import calls exactly when the start phase may diverge under
the empty host. -/
theorem closed_instDiverges_iff :
    (I.instStrategy P s start).InstDiverges ↔
      Diverges P (Det.noHost : HostSemantics Nat) (startConfig s start) :=
  Silmaril.Proofs.Wasm.Game.LinkStart.instDiverges_iff

end ScalarInstance

namespace Linking.StartSetup

variable (S : StartSetup) {P : Profile}

/-- **A failing provider start function makes the link fail alike** (every profile). -/
theorem linkInst_instFails {b : Behaviour Val}
    (h : ∃ (c' : Config Nat) (r : Result),
      Steps P (Det.noHost : HostSemantics Nat) (startConfig S.sp S.provStart) c' ∧
      c'.code = r.toAdmin ∧ (r = .trap ∨ ∃ x, r = .throw x) ∧ b = r.toBehaviour) :
    (S.linkInst P).InstFails b :=
  Silmaril.Proofs.Wasm.Game.LinkStart.StartSetup.linkInst_instFails S h

/-- **A diverging provider start function makes the link diverge** (every profile). -/
theorem linkInst_instDiverges
    (h : Diverges P (Det.noHost : HostSemantics Nat) (startConfig S.sp S.provStart)) :
    (S.linkInst P).InstDiverges :=
  Silmaril.Proofs.Wasm.Game.LinkStart.StartSetup.linkInst_instDiverges S h

/-- **The link is ready when the provider's start function, then the consumer's, may return**
(the consumer's start function making no import call; every profile). -/
theorem linkInst_instReady {sp' sc' : Store Nat}
    (hp : StartsTo P (Det.noHost : HostSemantics Nat) S.sp S.provStart sp')
    (hc : StartsTo P (Det.noHost : HostSemantics Nat) S.scs S.consStart sc') :
    (S.linkInst P).InstReady :=
  Silmaril.Proofs.Wasm.Game.LinkStart.StartSetup.linkInst_instReady S hp hc

/-- **The link is ready only if the provider's start function may return** (every profile):
the provider is instantiated, and its start function run, before the consumer. -/
theorem linkInst_instReady_imp (h : (S.linkInst P).InstReady) :
    ∃ sp', StartsTo P (Det.noHost : HostSemantics Nat) S.sp S.provStart sp' :=
  Silmaril.Proofs.Wasm.Game.LinkStart.StartSetup.linkInst_instReady_imp S h

/-- Without start functions the link is ready. -/
theorem noStart_linkInst_instReady (S : Setup) : (S.noStart.linkInst P).InstReady :=
  linkInst_instReady S.noStart (startsTo_none.2 rfl) (startsTo_none.2 rfl)

variable (P) in
/-- **M3 with start functions (static linking is composition), every profile.** The finite
plays of the instantiable strategy of the linked module, whose instantiation runs the
provider's start function and then the consumer's, are those of the link of the instantiable
provider and consumer (the provider instantiated, and its start function run, first; its store
persisting into the consumer's start function and all export calls). -/
theorem link_is_composition_inst (hS : S.Scalar) :
    (S.linkedInstStrategy P).forget = (S.linkInst P).forget :=
  Silmaril.Proofs.Wasm.Game.LinkStart.StartSetup.linkedInst_forget hS

variable (P) in
/-- **M3 with start functions, categorical form**: the linked module's instantiable strategy
(finite plays) is the composite of the provider's instantiable strategy and the strategy of the
consumer's link system. -/
theorem link_is_composition_inst_comp (hS : S.Scalar) :
    ((S.linkedInstStrategy P).forget :
        ifaceSig [] ⟶ (ifaceSig S.exportTypes).withInst (Behaviour Val)) =
      CategoryTheory.CategoryStruct.comp (obj := Sig) (X := ifaceSig [])
        (Y := (ifaceSig S.stubTypes).withInst (Behaviour Val))
        (Z := (ifaceSig S.exportTypes).withInst (Behaviour Val))
        (S.providerI.instStrategy P S.sp S.provStart).forget
        (Strategy.ofLTS (S.consumerI.instSys P S.scs S.consStart).consumerLTS) :=
  S.link_is_composition_inst P hS

/-- The linked module is ready exactly when its start sequence returns under the empty host. -/
theorem linkedInst_instReady_iff_core :
    (S.linkedInstStrategy P).InstReady ↔
      ∃ l₁ l₂, StartsTo P (Det.noHost : HostSemantics Nat) S.sl S.provStart l₁ ∧
        StartsTo P (Det.noHost : HostSemantics Nat) l₁ S.consStart l₂ :=
  Silmaril.Proofs.Wasm.Game.LinkStart.StartSetup.linked_instReady_iff

/-- **The link is ready exactly when the linked module's start sequence returns** (every
profile; the consumer's start function may call the provider). -/
theorem linkInst_instReady_iff (hS : S.Scalar) :
    (S.linkInst P).InstReady ↔
      ∃ l₁ l₂, StartsTo P (Det.noHost : HostSemantics Nat) S.sl S.provStart l₁ ∧
        StartsTo P (Det.noHost : HostSemantics Nat) l₁ S.consStart l₂ := by
  have h : (S.linkInst P).InstReady ↔ (S.linkedInstStrategy P).InstReady := by
    show _ ∈ (S.linkInst P).forget ↔ _ ∈ (S.linkedInstStrategy P).forget
    rw [S.link_is_composition_inst P hS]
  exact h.trans S.linkedInst_instReady_iff_core

end Linking.StartSetup

end Silmaril.Wasm.Game
