module

public import Silmaril.Wasm.Det.Game.Instance.Thms
public import Silmaril.Wasm.Game.Linking.Thms
public import Silmaril.Wasm.Det.NoMem.Thms
public import Silmaril.Wasm.Det.Stateless.Thms

/-!
# Static linking preserves determinism and statelessness modulo traps

For a static link of silmaril-lean's GC linker in the scalar fragment
(`Silmaril.Wasm.Game.Linking.Setup`, `Setup.Scalar`), the strategy of the linked module is the
composite of the provider's and the consumer's strategies
(`Setup.link_is_composition_profile`, every profile). Composition preserves determinism and
statelessness modulo traps when the consumer is trap-strict (`DetMod.comp`,
`StatelessMod.comp`), and every instance strategy is strict (`strict_strategy`). So:

* `linked_detMod`: if the provider (exporting the stubs, store `sp`) and the consumer (with
  host stubs, store `scs`) are `DetModule`, the linked module's strategy is deterministic
  modulo traps, at every profile;
* `linked_statelessMod`: the same for `StatelessModule` and statelessness;
* `linked_detMod_of_storeB`, `linked_statelessMod_of_good`: the hypotheses discharged by the
  executable checks of the subsets `Silmaril.Wasm.Det.NoMem` (no memory, no floats) and
  `Silmaril.Wasm.Det.Stateless`.

For the linked **store** `S.sl`, the converse after earlier activations
(`obsModule_of_detMod`, `obsStateless_of_statelessMod`) gives the observable part of
`DetModule`/`StatelessModule` (`linked_obsModule`, `linked_obsStateless`): output agreement of
export invocations of the linked module at every call state reached by trap-free activations
(resp. any activations). Stores are not compared and call states after traps are not
constrained: the game hides the store, and `DetMod → DetModule` fails as stated (see
`Silmaril.Wasm.Det.Game.Instance.Thms`).

New proofs (no source file).
-/

public section

namespace Silmaril.Wasm.Det.Link

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
open Silmaril.Wasm.Numerics (Profile)

variable (S : Setup) {P : Profile}

/-- The linked strategy is the composite of the strategies of the parts. -/
theorem linked_eq_comp (hS : S.Scalar) (P : Profile) :
    S.linkedI.σ P = (S.providerI.σ P).comp (S.consumerI.σ P) :=
  S.link_is_composition_profile hS P

/-- **Static linking preserves determinism modulo traps** (every profile). -/
theorem linked_detMod (hS : S.Scalar) (hp : DetModule P (entry S.providerI) S.sp)
    (hc : DetModule P (entry S.consumerI) S.scs) :
    DetMod (wasmTraps S.exportTypes) (S.linkedI.σ P) := by
  rw [linked_eq_comp S hS P]
  exact (detMod_strategy hp hS.provider.export_type).comp
    (detMod_strategy hc hS.consumer.export_type) (strict_strategy (I := S.consumerI) S.scs)

/-- **Static linking preserves statelessness modulo traps** (every profile). -/
theorem linked_statelessMod (hS : S.Scalar) (hp : StatelessModule P (entry S.providerI) S.sp)
    (hc : StatelessModule P (entry S.consumerI) S.scs) :
    StatelessMod (wasmTraps S.exportTypes) (S.linkedI.σ P) := by
  rw [linked_eq_comp S hS P]
  exact (statelessMod_strategy hp hS.provider.export_type).comp
    (statelessMod_strategy hc hS.consumer.export_type) (strict_strategy (I := S.consumerI) S.scs)

/-- **Linking two modules of the no-memory, no-float subset** gives a deterministic linked
strategy (every profile; the checks are executable). -/
theorem linked_detMod_of_storeB (hS : S.Scalar) (hp : NoMem.storeB S.sp = true)
    (hc : NoMem.storeB S.scs = true) : DetMod (wasmTraps S.exportTypes) (S.linkedI.σ P) :=
  linked_detMod S hS (NoMem.detModule_of_storeB hp) (NoMem.detModule_of_storeB hc)

/-- **Linking two modules of the stateless subset** gives a stateless linked strategy (every
profile). -/
theorem linked_statelessMod_of_good (hS : S.Scalar) {A₁ R₁ A₂ R₂ : Nat → Bool}
    (hp : Stateless.GoodFuns A₁ R₁ (fun _ => false) S.sp.funcs)
    (hpE : ∀ a fi, entry S.providerI a → S.sp.funcs[a]? = some fi → A₁ a = true)
    (hc : Stateless.GoodFuns A₂ R₂ (fun _ => false) S.scs.funcs)
    (hcE : ∀ a fi, entry S.consumerI a → S.scs.funcs[a]? = some fi → A₂ a = true) :
    StatelessMod (wasmTraps S.exportTypes) (S.linkedI.σ P) :=
  linked_statelessMod S hS (Stateless.statelessModule_of_good hp hpE)
    (Stateless.statelessModule_of_good hc hcE)

/-- **Static linking gives an observably deterministic linked store** (every profile): at every
call state of the linked module reached by trap-free activations, export invocations agree on
their visible outputs against the same typed trace. -/
theorem linked_obsModule (hS : S.Scalar) (hp : DetModule P (entry S.providerI) S.sp)
    (hc : DetModule P (entry S.consumerI) S.scs) : ObsModule P S.linkedI S.sl :=
  obsModule_of_detMod (linked_detMod S hS hp hc)

/-- **Static linking gives an observably stateless linked store** (every profile). -/
theorem linked_obsStateless (hS : S.Scalar) (hp : StatelessModule P (entry S.providerI) S.sp)
    (hc : StatelessModule P (entry S.consumerI) S.scs) : ObsStateless P S.linkedI S.sl :=
  obsStateless_of_statelessMod (linked_statelessMod S hS hp hc)

end Silmaril.Wasm.Det.Link
