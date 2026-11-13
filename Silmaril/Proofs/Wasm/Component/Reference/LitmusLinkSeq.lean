module

public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkInst
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq

/-!
# Sequences of calls of the litmus `dblFwdL`

`dblFwd_sound_seq`: the instance of `linked2_sound_seq` for calls `f(xᵢ)` followed by `f(x)` on
one instance of the doubler answering `fwdS`'s import (the conditions as for `dblFwd_sound`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Proofs.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Numerics (Profile)

/-- **Sequences of calls of the litmus `dblFwdL`** (every profile, component choice profile and
host functions): every behaviour of instantiating `dblFwdL.toRef`, calling `f` on each of `xs`
(each resolving), then on `x`, is matched by the linked IR. -/
theorem dblFwd_sound_seq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) (xs : List (BitVec 32))
    (x : BitVec 32) (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHost impl) h₀ dblFwdL.toRef
      (xs.map fun a => ("f", [toRefVal (.u32 a)])) "f" [toRefVal (.u32 x)]) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Linked2.seqMoves dblFwdL (xs.map fun a => (⟨0, by decide⟩, [.u32 a])) wss ∈
        dblFwdL.toComp.den (impSem P) ∧
      Linked2.SeqIRObs P dblFwdL (xs.map fun a => (⟨0, by decide⟩, [.u32 a])) wss
        ⟨0, by decide⟩ [.u32 x] p.2 := by
  have ht : SimpleI.TypedCalls dblFwdL.imp (xs.map fun a => (⟨0, by decide⟩, [.u32 a])) := by
    intro q hq
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
    rfl
  have hcalls : (xs.map fun a => ((⟨0, by decide⟩ : Fin dblFwdL.imp.exports.length),
        [Silmaril.Wasm.Component.Val.u32 a])).map
      (fun q : Fin dblFwdL.imp.exports.length × List Silmaril.Wasm.Component.Val =>
        (dblFwdL.imp.exports[q.1].name, q.2.map toRefVal)) =
      xs.map fun a => ("f", [toRefVal (.u32 a)]) := by
    rw [List.map_map]
    rfl
  exact linked2_sound_seq P prof dblFwdL dblS_good dblS_inst fwdS_good fwdS_inst fwdS_arity
    fwdS_floatFree dblFwdL_wireTy dblFwdL_namesOk dblFwdL_wireNodup dblFwdL_splitOk impl h₀ _
    ⟨0, by decide⟩ [.u32 x] ht rfl p (hcalls ▸ hp)

end Silmaril.Proofs.Wasm.Component.Reference
