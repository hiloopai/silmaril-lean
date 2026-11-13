module

public import Silmaril.Proofs.Wasm.Logic.Open.Strategy

/-!
# Open Wasm modules: soundness, linking and closing

For an open module `M` whose imports are host-function stubs, with stub `h`
standing for the environment's function at address `bind h`
(`Silmaril.Wasm.Logic.Open.Defs`):

* `FSpecAt.stub` (`Silmaril.Proofs.Wasm.Logic.Open.Stub`): under the most general
  environment `specHost bind Γi`, a stub meets its import specification, so
  import calls are proved with `Hoare.Safe.call`; `ModuleSat.of_step` proves a
  module by Löb induction (mutual recursion among its functions);
* `modStrat_sound` (`Silmaril.Proofs.Wasm.Logic.Open.Strategy`): **the game link**.
  `ModuleSat P M bind Γi Γe` implies that the strategy `modStrat P M bind` of the
  module's reduction semantics refines `agStrat (ctxSpec Γi) (ctxSpec Γe)`;
* `link_refines`: two linked modules (`Strategy.comp`) refine the
  assume/guarantee strategy of the outer import and export specifications;
* `ModuleSat.valid_host`: closing a module with a concrete environment that is
  sound and live for the imports gives valid exports in the closed world
  `Step P host`, and `ModuleSat.invoke_vals` gives every run of `$invoke`.

Partial correctness, for every profile. See `Silmaril.Wasm.Logic.Open.Defs` for the
model's limits (shared store, imports are stubs only, no re-entrancy during an
import call, linking by `bind` rather than by silmaril-lean's instantiation).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Open

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {M : OMod H} {bind : H → Nat} {Γi Γe : Ctx H}

/-- **Soundness of a closed module.** Under a concrete environment sound and live
for the imports, every run of `$invoke` of an export that returns values meets
the export's postcondition. -/
theorem ModuleSat.invoke_vals (hm : ModuleSat P M bind Γi Γe) {host : HostSemantics H}
    (hsound : ∀ h s args o, host h s args o → specHost bind Γi h s args o)
    (hlive : ∀ h s args S, Γi (bind h) = some S → S.pre s args → ∃ o, host h s args o)
    {a : Nat} {S : FSpec H} (hS : Γe a = some S) {s s' : Store H} {f' : Frame}
    {args res : List Val} (hpre : S.pre s args)
    (hs : Steps P host (invoke s a args) ⟨s', f', vals res⟩) : S.post s args s' (.normal res) :=
  FSpecValid.invoke_vals (fun n => hm.valid_host hsound hlive n a S hS) hpre hs

end Silmaril.Wasm.Logic.Open
