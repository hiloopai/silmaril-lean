module

public import Silmaril.Wasm.Binaryen.InlReverseMatch

@[expose] public section

/-! # Smaller active-body obligations for reverse inlining

Generic, caller and relocated-callee runtime modes can all contain nested
activations. Their reverse proof therefore recurses together on the actual
target code. The forward simulation's auxiliary `top` mode is handled inside
the caller's complete source activation, where exiting it makes real source
progress; it is not an independent positive-progress reverse obligation.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Numerics SingleThreaded

structure ReverseIH (p : Prm) (P : Profile) (H : Type) (limit : Nat) : Prop where
  generic : ∀ {original target next : Config H}, sizeOf target.code < limit →
    ContextTyped original → MR p .gen original target → SR p original.store target.store →
    Step P Det.noHost target next → ReverseProgress p P .gen original target next
  caller : ∀ {original target next : Config H}, sizeOf target.code < limit →
    ContextTyped original → MR p .g original target → SR p original.store target.store →
    Step P Det.noHost target next → ReverseProgress p P .g original target next
  callee : ∀ {d : Nat} {L : List (Option Val)} {original target next : Config H},
    sizeOf target.code < limit → ContextTyped original → MR p (.i d L) original target →
    SR p original.store target.store → Step P Det.noHost target next →
    ReverseProgress p P (.i d L) original target next

theorem ReverseIH.mono {p : Prm} {P : Profile} {H : Type} {limit smaller : Nat}
    (hypothesis : ReverseIH p P H limit) (bound : smaller ≤ limit) :
    ReverseIH p P H smaller where
  generic size typed runtime stores step :=
    hypothesis.generic (by omega) typed runtime stores step
  caller size typed runtime stores step :=
    hypothesis.caller (by omega) typed runtime stores step
  callee size typed runtime stores step :=
    hypothesis.callee (by omega) typed runtime stores step

end Silmaril.Wasm.Binaryen.InlR
