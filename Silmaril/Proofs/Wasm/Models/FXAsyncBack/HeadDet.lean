module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.Inv
public import Silmaril.Raw.Wasm.Models.FXAsyncBack.HeadCtl

/-!
# Core head steps of plain instructions are deterministic

Silmaril's `Head.det_fam` (deterministic profile) compares two head steps of the same
non-control instruction; `Head.det_ctl` gives only joinability, because of the context rules on
labels, frames and handlers. For a **plain** instruction no context rule applies, so the two
head steps are equal (the control case, a case analysis closed by automation, is
`Silmaril.Raw.Wasm.Models.FXAsyncBack.head_plain_ctl`):

* **`head_plain_det`**: two head steps of `.plain i` in the deterministic profile, whose
  arguments are suffixes of each other, take the same arguments and reach the same configuration.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf Fam famOf_of_shape singleton_hp last_hp
  p_nil_of_len Expand.det)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type}

/-- **Head steps of a plain instruction are deterministic** (deterministic profile). -/
theorem head_plain_det {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {args₁ args₂ p : List Val} {i : Instr} {c₁ c₂ : Config H}
    (h₁ : Head (Profile.deterministic o) s f args₁ (.plain i) c₁)
    (h₂ : Head (Profile.deterministic o) s f args₂ (.plain i) c₂) (hp : args₁ = p ++ args₂) :
    p = [] ∧ c₁ = c₂ := by
  by_cases hk : famOf (.plain i) = .control
  · exact Silmaril.Raw.Wasm.Models.FXAsyncBack.head_plain_ctl hk h₁ h₂ hp
  · exact Silmaril.Wasm.SingleThreaded.Det.Head.det_fam hk h₁ h₂ hp

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
