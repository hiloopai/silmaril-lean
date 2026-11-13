module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Step
public import Silmaril.Wasm.SingleThreaded.Thread

/-!
# Forced runs

`DetTo P c d`: every configuration on the run from `c` to `d` other than `d` has exactly one
host-free successor (any profile `P`), is not at a host-call redex and is not a result. The
segment-initialisation prefix of `$instantiate` is such a run (`Silmaril.Proofs.Wasm.Game.
SpecGlobals.SegRun`), so strategies that start from `c` and from `d` agree
(`Silmaril.Proofs.Wasm.Game.SpecGlobals.DetStrat`).

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- A forced host-free run from `c` to `d`. -/
inductive DetTo (P : Profile) : Config Nat → Config Nat → Prop where
  | refl (c : Config Nat) : DetTo P c c
  | step {c c' d : Config Nat} (h : Step P noHost c c')
      (uniq : ∀ e, Step P noHost c e → e = c')
      (nocall : decompose? c.store c.code = none)
      (nores : ∀ r : Result, c.code ≠ r.toAdmin)
      (rest : DetTo P c' d) : DetTo P c d

theorem DetTo.trans {P : Profile} {c d e : Config Nat} (h₁ : DetTo P c d) (h₂ : DetTo P d e) :
    DetTo P c e := by
  induction h₁ with
  | refl => exact h₂
  | step h uniq nocall nores _ ih => exact .step h uniq nocall nores (ih h₂)

end Silmaril.Proofs.Wasm.Game.SpecGlobals
