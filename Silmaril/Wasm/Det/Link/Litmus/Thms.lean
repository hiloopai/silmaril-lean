module

public import Silmaril.Wasm.Det.Link.Litmus.Defs
public import Silmaril.Wasm.Det.Link.Thms
public import Silmaril.Wasm.Det.Link.Shared.Thms
import Silmaril.Proofs.Wasm.Det.Link.Litmus

/-!
# A concrete static link is deterministic and stateless (litmus)

The provider `linkP` (exporting `seven`) and the consumer `linkC` (exporting `eight`, which
calls `seven` and adds one) of `Silmaril.Wasm.Det.Link.Litmus` are linked by silmaril-lean's GC
linker. Kernel evaluation of `link?`, `instantiateOnce?` and the typing of the stub and export
functions builds a `Setup` in the scalar fragment through
`Silmaril.Wasm.Game.Linking.exists_scalar_setup`, with the computed stores `linkSp`, `linkScs` and
`linkSl` (`link_setup`). On it, at every profile:

* `link_litmus_detMod`: both parts pass the executable no-memory check `NoMem.storeB`, so the
  linked strategy is deterministic modulo traps (`linked_detMod_of_storeB`), and the linked
  store is observably deterministic (`linked_obsModule`);
* `link_litmus_statelessMod`: both parts pass `Stateless.moduleStatelessCheck`, so the linked
  strategy is stateless modulo traps (`linked_statelessMod`) and the linked store observably
  stateless (`linked_obsStateless`);
* `link_litmus_detModule`: the linked store itself also passes both checks, so the linked
  module is `DetModule` and `StatelessModule` directly (by the subset theorems, not by
  transfer).

**Determinism and statelessness from the parts (step B).** The setup also pins the shared store
to `linkSc` (`link_setup_sc`). Both parts pass the direct-mode check `NoMem.closB` on both
function addresses `linkAddrs` (the provider in the shared store, the consumer in the consumer
store with stubs) and the stateless check `Stateless.checkSet` reading no global, so the
hypotheses of `linked_detModule_of_closB` and `linked_statelessModule_of_good` are discharged by
kernel evaluation:

* `link_litmus_detModule_of_closB`: `DetModule` of the linked store from the parts;
* `link_litmus_statelessModule_of_good`: `StatelessModule` of the linked store from the parts.

Proofs: `Silmaril.Proofs.Wasm.Det.Link.Litmus`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.Link.Litmus

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm.Det.Link
open Silmaril.Wasm.Numerics (Profile)

/-- **The concrete link is a setup of the scalar fragment** with the computed stores. -/
theorem link_setup : ∃ S : Setup, S.namespaceName = "p" ∧ S.provider = linkP ∧
    S.consumer = linkC ∧ S.linked = linkL ∧ S.sp = linkSp ∧ S.scs = linkScs ∧ S.sl = linkSl ∧
    S.stubTypes = [i32Fn] ∧ S.exportTypes = [i32Fn, i32Fn] ∧ S.Scalar :=
  Silmaril.Proofs.Wasm.Det.Link.Litmus.exists_setup

/-- **Litmus: linking two deterministic modules gives a deterministic linked strategy and an
observably deterministic linked store** (every profile). -/
theorem link_litmus_detMod : ∃ S : Setup, S.provider = linkP ∧ S.consumer = linkC ∧
    S.sl = linkSl ∧ S.Scalar ∧ ∀ P : Profile,
      DetMod (wasmTraps S.exportTypes) (S.linkedI.σ P) ∧ ObsModule P S.linkedI S.sl := by
  obtain ⟨S, -, hp, hc, -, hsp, hscs, hsl, -, -, hS⟩ := link_setup
  have h₁ : NoMem.storeB S.sp = true := hsp ▸ Silmaril.Proofs.Wasm.Det.Link.Litmus.storeB_sp
  have h₂ : NoMem.storeB S.scs = true := hscs ▸ Silmaril.Proofs.Wasm.Det.Link.Litmus.storeB_scs
  exact ⟨S, hp, hc, hsl, hS, fun P => ⟨linked_detMod_of_storeB S hS h₁ h₂,
    linked_obsModule S hS (NoMem.detModule_of_storeB h₁) (NoMem.detModule_of_storeB h₂)⟩⟩

/-- **Litmus: linking two stateless modules gives a stateless linked strategy and an observably
stateless linked store** (every profile). -/
theorem link_litmus_statelessMod : ∃ S : Setup, S.provider = linkP ∧ S.consumer = linkC ∧
    S.sl = linkSl ∧ S.Scalar ∧ ∀ P : Profile,
      StatelessMod (wasmTraps S.exportTypes) (S.linkedI.σ P) ∧
        ObsStateless P S.linkedI S.sl := by
  obtain ⟨S, -, hp, hc, -, hsp, hscs, hsl, -, -, hS⟩ := link_setup
  have h₁ : Stateless.moduleStatelessCheck S.sp = true :=
    hsp ▸ Silmaril.Proofs.Wasm.Det.Link.Litmus.stateless_sp
  have h₂ : Stateless.moduleStatelessCheck S.scs = true :=
    hscs ▸ Silmaril.Proofs.Wasm.Det.Link.Litmus.stateless_scs
  exact ⟨S, hp, hc, hsl, hS, fun P =>
    ⟨linked_statelessMod S hS (Stateless.statelessModule_of_check h₁)
      (Stateless.statelessModule_of_check h₂),
    linked_obsStateless S hS (Stateless.statelessModule_of_check h₁)
      (Stateless.statelessModule_of_check h₂)⟩⟩

/-- The linked store of the litmus is `DetModule` and `StatelessModule` for every entry set
(every profile), by the subset checks on the linked store itself. -/
theorem link_litmus_detModule (P : Profile) (Entry : Nat → Prop) :
    DetModule P Entry linkSl ∧ StatelessModule P Entry linkSl :=
  ⟨NoMem.detModule_of_storeB Silmaril.Proofs.Wasm.Det.Link.Litmus.storeB_sl,
    Stateless.statelessModule_of_check Silmaril.Proofs.Wasm.Det.Link.Litmus.stateless_sl⟩

/-- **The concrete link is a setup of the scalar fragment with its shared store pinned**, the
export addresses of both parts lying in `linkAddrs`. -/
theorem link_setup_sc : ∃ S : Setup, S.provider = linkP ∧ S.consumer = linkC ∧
    S.sc = linkSc ∧ S.scs = linkScs ∧ S.sl = linkSl ∧ S.Scalar ∧
    (∀ a, entry S.providerI a → a ∈ linkAddrs) ∧ (∀ a, entry S.consumerI a → a ∈ linkAddrs) :=
  Silmaril.Proofs.Wasm.Det.Link.Litmus.exists_setup_sc

/-- **Litmus for step B, determinism**: `linked_detModule_of_closB` on the concrete link, its
`closB` and entry hypotheses discharged by kernel evaluation (every profile). -/
theorem link_litmus_detModule_of_closB : ∃ S : Setup, S.provider = linkP ∧ S.consumer = linkC ∧
    S.sl = linkSl ∧ S.Scalar ∧ ∀ P : Profile, DetModule P (entry S.linkedI) S.sl := by
  obtain ⟨S, hp, hc, hsc, hscs, hsl, hS, hpE, hcE⟩ := link_setup_sc
  have hpB : NoMem.closB S.sc linkAddrs = true :=
    hsc ▸ Silmaril.Proofs.Wasm.Det.Link.Litmus.closB_sc
  have hcB : NoMem.closB S.scs linkAddrs = true :=
    hscs ▸ Silmaril.Proofs.Wasm.Det.Link.Litmus.closB_scs
  exact ⟨S, hp, hc, hsl, hS, fun P => linked_detModule_of_closB (P := P) S hS hpB hpE hcB hcE⟩

/-- **Litmus for step B, statelessness**: `linked_statelessModule_of_good` on the concrete link,
its `GoodFuns` and entry hypotheses discharged by kernel evaluation (every profile). -/
theorem link_litmus_statelessModule_of_good : ∃ S : Setup, S.provider = linkP ∧
    S.consumer = linkC ∧ S.sl = linkSl ∧ S.Scalar ∧
      ∀ P : Profile, StatelessModule P (entry S.linkedI) S.sl := by
  obtain ⟨S, hp, hc, hsc, hscs, hsl, hS, hpE, hcE⟩ := link_setup_sc
  have hpG := Stateless.checkSet_sound (hsc ▸ Silmaril.Proofs.Wasm.Det.Link.Litmus.checkSet_sc)
  have hcG := Stateless.checkSet_sound (hscs ▸ Silmaril.Proofs.Wasm.Det.Link.Litmus.checkSet_scs)
  exact ⟨S, hp, hc, hsl, hS, fun P => linked_statelessModule_of_good (P := P) S hS hpG
    (fun a ha => List.contains_iff_mem.2 (hpE a ha)) hcG
    (fun a ha => List.contains_iff_mem.2 (hcE a ha))⟩

end Silmaril.Wasm.Det.Link.Litmus
