module

public import Silmaril.Wasm.Det.Shared.Stateless.Defs
public import Silmaril.Wasm.Det.Shared.Thms
public import Silmaril.Wasm.Det.Stateless.Thms
import Silmaril.Proofs.Wasm.Det.Shared.Stateless

/-!
# Statelessness under store-writing hosts: theorems

Every statement holds at an arbitrary profile `P`.

* `DetCfgS.obsAgreeS`: determinism under store-writing hosts gives output agreement of a
  configuration with itself.
* `StatelessFnS.anti`, `StatelessModuleS.anti`: fewer call states.
* The stateless subset of `Silmaril.Wasm.Det.Stateless` (no memory, no floats, globals read in `R`
  and written in `W`): `closedS_sl` (its invariant is closed under answers in every store
  keeping the function instances), `detCfgS_sl`, and
  * `obsAgreeS_of_agree`: subset code from the same frame and code in two stores agreeing on the
    functions and the globals of `R` has the same non-trapping outputs against the same answers
    and returned stores;
  * `statelessFnS_of_good`, `statelessModuleS_of_good`, `statelessFnS_of_check`: subset functions
    (modules) are stateless under every host keeping the function instances, over the stores
    agreeing with `s₀` on the functions and on the globals they read. With no global read, that
    is every store holding the functions.

**Relation to the store-free notion.** `ObsAgreeS` compares runs that resume every answer in
the **same** returned store, whereas `Silmaril.Wasm.Det.Core.ObsAgree` resumes each run in its own
store. So neither notion implies the other in general: code reading a global only after an import
call agrees under `ObsAgreeS` (both runs read the returned store) but may disagree under
`ObsAgree`. Neither direction is formalised.

Proofs: `Silmaril.Proofs.Wasm.Det.Shared.Stateless`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.Shared

open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Stateless Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {A : Store Nat → Store Nat → Prop}

theorem DetCfgS.obsAgreeS {c : Config Nat} (h : DetCfgS P A c) : ObsAgreeS P A c c :=
  Silmaril.Proofs.Wasm.Det.Shared.Stateless.DetCfgS.obsAgreeS h

theorem StatelessFnS.anti {S S' : Store Nat → Prop} {a : Nat} (hS : ∀ s, S' s → S s)
    (h : StatelessFnS P A S a) : StatelessFnS P A S' a :=
  fun s₁ s₂ vs h₁ h₂ => h s₁ s₂ vs (hS _ h₁) (hS _ h₂)

theorem StatelessModuleS.anti {S S' : Store Nat → Prop} {Entry : Nat → Prop}
    (hS : ∀ s, S' s → S s) (h : StatelessModuleS P A S Entry) : StatelessModuleS P A S' Entry :=
  fun a ha => (h a ha).anti hS

variable {Ar R W : Nat → Bool}

theorem closedS_sl (P : Profile) : ClosedS P KeepFuncs (Inv Ar R W) :=
  Silmaril.Proofs.Wasm.Det.Shared.Stateless.closedS_sl P

/-- **Stateless-subset code is deterministic against every host keeping the functions.** -/
theorem detCfgS_sl {c : Config Nat} (hc : Inv Ar R W c) : DetCfgS P KeepFuncs c :=
  Silmaril.Proofs.Wasm.Det.Shared.Stateless.detCfgS_sl hc

/-- **Statelessness for agreeing stores, under store-writing hosts.** -/
theorem obsAgreeS_of_agree {c₁ c₂ : Config Nat} (hc : Inv Ar R W c₁)
    (hag : Agree R c₁.store c₂.store) (hf : c₁.frame = c₂.frame) (hcode : c₁.code = c₂.code) :
    ObsAgreeS P KeepFuncs c₁ c₂ :=
  Silmaril.Proofs.Wasm.Det.Shared.Stateless.obsAgreeS_of_agree hc hag hf hcode

/-- **Subset functions are stateless under every host keeping the functions**, over the stores
agreeing with `s₀` on the functions and the globals of `R`. -/
theorem statelessFnS_of_good {s₀ : Store Nat} {a : Nat} (hg : GoodFuns Ar R W s₀.funcs)
    (ha : Ar a = true) : StatelessFnS P KeepFuncs (fun s => Agree R s s₀) a :=
  Silmaril.Proofs.Wasm.Det.Shared.Stateless.statelessFnS_of_good hg ha

/-- **A module of subset functions is stateless under every host keeping the functions.** -/
theorem statelessModuleS_of_good {Entry : Nat → Prop} {s₀ : Store Nat}
    (hm : GoodFuns Ar R W s₀.funcs) (hE : ∀ a, Entry a → Ar a = true) :
    StatelessModuleS P KeepFuncs (fun s => Agree R s s₀) Entry :=
  Silmaril.Proofs.Wasm.Det.Shared.Stateless.statelessModuleS_of_good hm hE

/-- **The stateless check gives statelessness under store-writing hosts.** -/
theorem statelessFnS_of_check {s : Store Nat} {a : Nat} (h : statelessCheck s a = true) :
    StatelessFnS P KeepFuncs (fun t => Agree (readsOf s (closure s [a])).contains t s) a :=
  Silmaril.Proofs.Wasm.Det.Shared.Stateless.statelessFnS_of_check h

end Silmaril.Wasm.Det.Shared
