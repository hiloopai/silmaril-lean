module

public import Silmaril.Wasm.Game.Linking.Thms
public import Silmaril.Wasm.Game.DivAdequacy.Thms
import Silmaril.Proofs.Wasm.Game.Linking.DivMain
import Silmaril.Proofs.Wasm.Game.Linking.SpecSetup

/-!
# Static linking is composition, divergence observed

For an **arbitrary** silmaril profile `P` (no determinism is used), in the fragment of
silmaril-lean's linker (`Linking.Setup`, `Recipe.Assembly`) with scalar interfaces
(`Setup.Scalar`):

* `Linking.Setup.link_is_composition_div`: the divergence-observing strategy of the linked
  module is the composite (`DStrategy.comp`, hidden infinite chatter creating divergence) of
  the divergence-observing strategies of the provider and the consumer: plays, **divergences
  and infinite plays** agree. This strengthens `link_is_composition_profile` (its `forget`,
  `link_is_composition_div_forget`).
* `Linking.Setup.linked_dstrategy_eq_shared`, `Linking.Setup.shared_dstrategy_eq_comp`: the two
  steps, (A) linked = shared (lock-step bisimulation along the linker relation) and (B) shared =
  the composite system of provider and consumer (divergence-sensitive simulations in both
  directions: the synchronisations of the import interface take no shared step and decrease a
  measure; a trapping provider makes the shared configuration doomed, whose steps decrease the
  size of the code, `Choice.trapped_step_lt`).
* `Linking.Setup.instantiate_spec`: when the provider and the consumer have no globals, all the
  stores of the setup are the specification's instantiations (`Instantiate P host`, no segment
  code, no start function), so the linking theorems are about the spec's `$instantiate`.

Proofs: `Silmaril.Proofs.Wasm.Game.Linking.{DivShared,DivMain,SpecSetup}`,
`Silmaril.Proofs.Wasm.Game.Linking.Split.{DivSup,DivSub}`,
`Silmaril.Proofs.Wasm.Game.Machine.Doomed`. New.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Linking.Setup

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Link.GC

variable (S : Setup)

/-- **Static linking is composition, divergence observed, every profile.** -/
theorem link_is_composition_div (hS : S.Scalar) (P : Profile) :
    S.linkedI.dstrategy P S.sl =
      (S.providerI.dstrategy P S.sp).comp (S.consumerI.dstrategy P S.scs) :=
  Silmaril.Proofs.Wasm.Game.Linking.link_is_composition_div hS P

/-- The finite plays of `link_is_composition_div`. -/
theorem link_is_composition_div_forget (hS : S.Scalar) (P : Profile) :
    (S.linkedI.dstrategy P S.sl).forget =
      ((S.providerI.dstrategy P S.sp).comp (S.consumerI.dstrategy P S.scs)).forget :=
  congrArg DStrategy.forget (S.link_is_composition_div hS P)

/-- **(A), divergence observed**: the linked module and the shared world. -/
theorem linked_dstrategy_eq_shared (hS : S.Scalar) (P : Profile) :
    S.linkedI.dstrategy P S.sl = S.sharedI.dstrategy P S.sc :=
  Silmaril.Proofs.Wasm.Game.Linking.DivShared.linked_dstrategy_eq_shared hS P

/-- **(B), divergence observed**: the shared world and the composite system of the provider and
the consumer. -/
theorem shared_dstrategy_eq_comp (hS : S.Scalar) (P : Profile) :
    S.sharedI.dstrategy P S.sc =
      DStrategy.ofLTS ((S.providerI.dlts P S.sp).comp (S.consumerI.dlts P S.scs)) :=
  Silmaril.Proofs.Wasm.Game.Linking.Split.shared_eq_comp hS P

/-- **The stores of a global-free linking setup are the specification's instantiations**, for
every profile and host. -/
theorem instantiate_spec (hg : S.provider.globals = [] ∧ S.consumer.globals = [])
    (P : Profile) (host : HostSemantics Nat) :
    Instantiate P host S.base S.provider (Preparation.imports []) ⟨S.sp, S.fp, []⟩ ∧
    Instantiate P host S.sp S.consumer
      (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
      ⟨S.sc, S.fc, []⟩ ∧
    Instantiate P host (stubOut S.base.funcs.length S.stubs S.sp) S.consumer
      (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
      ⟨S.scs, S.fcs, []⟩ ∧
    Instantiate P host S.base S.linked (Preparation.imports []) ⟨S.sl, S.fl, []⟩ :=
  Silmaril.Proofs.Wasm.Game.Linking.Setup.instantiate_spec S hg P host

end Silmaril.Wasm.Game.Linking.Setup
