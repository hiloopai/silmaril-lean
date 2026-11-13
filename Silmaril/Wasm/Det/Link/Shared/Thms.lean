module

public import Silmaril.Wasm.Det.Link.Store.Thms
public import Silmaril.Wasm.Det.Shared.Thms
public import Silmaril.Wasm.Game.ULink.Runs.Thms
public import Silmaril.Wasm.Det.Link.Shared.Defs
public import Silmaril.Wasm.Det.Stateless.Thms
import Silmaril.Proofs.Wasm.Det.Link.Shared
import Silmaril.Proofs.Wasm.Det.Shared.Weak

/-!
# Determinism of the linked store from the parts (step B, store-writing route)

For a static link `S : Linking.Setup` in the scalar fragment (`S.Scalar`), at **every**
profile, `DetModule` (outputs **and stores**, at every call state, including call states after
trapped calls) of the shared store `S.sc`, hence (step A, `linked_detModule_of_shared`) of the
linked store `S.sl`, from determinism of the two parts:

* the **consumer with stubs** is deterministic against every host that keeps the functions
  (`DetModuleS P KeepFuncs`), at every store with the functions of its own store `S.scs`;
* the **provider**'s invocations of its exports are deterministic (`DetCfg`, or `DetModuleS`
  against `KeepFuncs`) at every store with the functions of the shared store `S.sc`.

Both hypotheses quantify over **all** stores with the given functions, not over reachable ones:
the consumer sees the provider's effects as store writes by its host (the provider runs in the
shared store), and the provider runs in the shared store, which the consumer has written. They
have the shape of `detModuleS_of_closB` (memory-free subset, direct mode), whence
`linked_detModule_of_closB`.

The proof reads a run of the shared world as a consumer run in the stubbed store (`S.scs` is
the stubbed shared store) whose stub calls are answered by provider runs in the real store
(`Silmaril.Wasm.Game.ULink.linked_oruns`), and compares two such runs at the first difference of
their traces. No renaming of heap addresses is needed (both parts see the one shared store).
`DetModule` of the parts at their own reachable stores (`S.sp`, `S.scs`) is **not** enough for
this route; that is the renaming route of `docs/projects/wasm-wasi.md` (not done).

**Statelessness** (`linked_statelessModule_of_parts`): the same route, with both parts
`StatelessModuleW` (`Silmaril.Wasm.Det.Link.Shared.Defs`): output agreement between two call
states against hosts keeping the functions whose returned stores may differ between the two runs
(the provider writes the shared store differently from different call states). Subset code of
`Silmaril.Wasm.Det.Stateless` reading no global satisfies it (`statelessModuleW_of_good`), whence
`linked_statelessModule_of_good`.

Proofs: `Silmaril.Proofs.Wasm.Det.Link.Shared`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.Link

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm.Det.Shared Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} (S : Setup)

/-- **Step B, per invocation**: every export invocation in every store with the shared functions
is deterministic modulo traps (outputs and stores). -/
theorem shared_detCall_of_parts (hS : S.Scalar)
    (hp : ∀ s, s.funcs = S.sc.funcs → ∀ a, entry S.providerI a → ∀ vs, DetCfg P (invoke s a vs))
    (hc : DetModuleS P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI))
    {s : Store Nat} (hs : s.funcs = S.sc.funcs) {a : Nat} (ha : entry S.sharedI a)
    (vs : List Val) : DetCfg P (invoke s a vs) :=
  Silmaril.Proofs.Wasm.Det.Link.Shared.shared_detCall S hS hp hc hs ha vs

/-- **Step B**: `DetModule` of the shared store from the parts. -/
theorem shared_detModule_of_parts (hS : S.Scalar)
    (hp : ∀ s, s.funcs = S.sc.funcs → ∀ a, entry S.providerI a → ∀ vs, DetCfg P (invoke s a vs))
    (hc : DetModuleS P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI)) :
    DetModule P (entry S.sharedI) S.sc :=
  Silmaril.Proofs.Wasm.Det.Link.Shared.shared_detModule_of_parts S hS hp hc

/-- The provider hypothesis from `DetModuleS` against hosts keeping the functions. -/
theorem provider_detCfg_of_detModuleS
    (hp : DetModuleS P KeepFuncs (fun s => s.funcs = S.sc.funcs) (entry S.providerI)) :
    ∀ s, s.funcs = S.sc.funcs → ∀ a, entry S.providerI a → ∀ vs, DetCfg P (invoke s a vs) :=
  fun s hs a ha vs => DetCfgS.detCfg (A := KeepFuncs) (fun _ => rfl) (hp s hs a ha vs)

/-- **Determinism of the linked store from the parts** (steps A and B), every profile. -/
theorem linked_detModule_of_parts (hS : S.Scalar)
    (hp : DetModuleS P KeepFuncs (fun s => s.funcs = S.sc.funcs) (entry S.providerI))
    (hc : DetModuleS P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI)) :
    DetModule P (entry S.linkedI) S.sl :=
  linked_detModule_of_shared S hS
    (shared_detModule_of_parts S hS (provider_detCfg_of_detModuleS S hp) hc)

/-- **The memory-free subset, direct mode**: if the provider's exports pass `closB` in the shared
store and the consumer's exports pass `closB` in the consumer store, the linked store is
deterministic. -/
theorem linked_detModule_of_closB (hS : S.Scalar) {Lp Lc : List Nat}
    (hpB : Silmaril.Wasm.Det.NoMem.closB S.sc Lp = true) (hpE : ∀ a, entry S.providerI a → a ∈ Lp)
    (hcB : Silmaril.Wasm.Det.NoMem.closB S.scs Lc = true) (hcE : ∀ a, entry S.consumerI a → a ∈ Lc) :
    DetModule P (entry S.linkedI) S.sl :=
  linked_detModule_of_parts S hS
    (fun s hs a ha => detModuleS_of_closB (P := P) hpB s hs a (hpE a ha))
    (fun s hs a ha => detModuleS_of_closB (P := P) hcB s hs a (hcE a ha))

/-! ### Statelessness -/

/-- **Subset code reading no global is stateless against hosts whose returned stores differ**,
over the stores with the functions of `s₀`. -/
theorem statelessModuleW_of_good {A W : Nat → Bool} {Entry : Nat → Prop} {s₀ : Store Nat}
    (hm : Silmaril.Wasm.Det.Stateless.GoodFuns A (fun _ => false) W s₀.funcs)
    (hE : ∀ a, Entry a → A a = true) :
    StatelessModuleW P KeepFuncs (fun s => s.funcs = s₀.funcs) Entry :=
  Silmaril.Proofs.Wasm.Det.Shared.Weak.statelessModuleW_of_good hm hE

/-- **Step B, statelessness, per invocation**: export invocations on the same arguments in any two
stores with the shared functions agree on non-trapping outputs. -/
theorem shared_obsAgree_of_parts (hS : S.Scalar)
    (hp : StatelessModuleW P KeepFuncs (fun s => s.funcs = S.sc.funcs) (entry S.providerI))
    (hc : StatelessModuleW P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI))
    {s₁ s₂ : Store Nat} (hs₁ : s₁.funcs = S.sc.funcs) (hs₂ : s₂.funcs = S.sc.funcs) {a : Nat}
    (ha : entry S.sharedI a) (vs : List Val) : ObsAgree P (invoke s₁ a vs) (invoke s₂ a vs) :=
  Silmaril.Proofs.Wasm.Det.Link.Shared.shared_obsAgree S hS hp hc hs₁ hs₂ ha vs

/-- **Step B, statelessness**: `StatelessModule` of the shared store from the parts. -/
theorem shared_statelessModule_of_parts (hS : S.Scalar)
    (hp : StatelessModuleW P KeepFuncs (fun s => s.funcs = S.sc.funcs) (entry S.providerI))
    (hc : StatelessModuleW P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI)) :
    StatelessModule P (entry S.sharedI) S.sc :=
  Silmaril.Proofs.Wasm.Det.Link.Shared.shared_statelessModule_of_parts S hS hp hc

/-- **Statelessness of the linked store from the parts** (steps A and B), every profile. -/
theorem linked_statelessModule_of_parts (hS : S.Scalar)
    (hp : StatelessModuleW P KeepFuncs (fun s => s.funcs = S.sc.funcs) (entry S.providerI))
    (hc : StatelessModuleW P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI)) :
    StatelessModule P (entry S.linkedI) S.sl :=
  linked_statelessModule_of_shared S hS (shared_statelessModule_of_parts S hS hp hc)

/-- **The stateless subset, reading no global**: if the provider's exports are subset code in
the shared store and the consumer's exports are subset code in the consumer store, the linked
store is stateless. -/
theorem linked_statelessModule_of_good (hS : S.Scalar) {Ap Wp Ac Wc : Nat → Bool}
    (hpG : Silmaril.Wasm.Det.Stateless.GoodFuns Ap (fun _ => false) Wp S.sc.funcs)
    (hpE : ∀ a, entry S.providerI a → Ap a = true)
    (hcG : Silmaril.Wasm.Det.Stateless.GoodFuns Ac (fun _ => false) Wc S.scs.funcs)
    (hcE : ∀ a, entry S.consumerI a → Ac a = true) :
    StatelessModule P (entry S.linkedI) S.sl :=
  linked_statelessModule_of_parts S hS (statelessModuleW_of_good hpG hpE)
    (statelessModuleW_of_good hcG hcE)

end Silmaril.Wasm.Det.Link
