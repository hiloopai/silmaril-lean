module

public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkInst
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSound

/-!
# Soundness of the litmus `dblFwdL`

The doubler `dblS` answering `fwdS`'s import `g` satisfies the conditions of `linked2_sound`
(`dblFwdL_wireTy`, `dblFwdL_namesOk`, `dblFwdL_wireNodup`, `dblFwdL_splitOk` and the facts of
both litmus components); `dblFwd_sound` is the instance.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Proofs.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Numerics (Profile)

/-- **Soundness of the litmus `dblFwdL`** (every profile, component choice profile and host
functions): every behaviour of instantiating `dblFwdL.toRef` and calling `f` on `x` is matched by
the linked IR. -/
theorem dblFwd_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) (x : BitVec 32) :
    ∀ b ∈ exportBehaviours prof (linkHost impl) h₀ dblFwdL.toRef [] "f" [toRefVal (.u32 x)],
      Linked2.IRObs P dblFwdL ⟨0, by decide⟩ [.u32 x] b :=
  linked2_sound P prof dblFwdL dblS_good dblS_inst fwdS_good fwdS_inst fwdS_arity
    fwdS_floatFree dblFwdL_wireTy dblFwdL_namesOk dblFwdL_wireNodup dblFwdL_splitOk impl h₀
    ⟨0, by decide⟩ [.u32 x] rfl

end Silmaril.Proofs.Wasm.Component.Reference
