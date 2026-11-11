module

public import Silmaril.Proofs.Wasm.Auto.Equiv.Typed

/-!
# Equivalence of straight-line segments: reflexivity, symmetry, transitivity, bodies

`SegEquiv.refl`, `symm`, `trans` (and the same for `OutEquiv`), `SegEquiv.out`, and
`SegEquiv.body`: equivalent function bodies have the same weakest precondition for every
postcondition. Stated in `Silmaril.Wasm.Auto.Equiv.Thms`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Wp Corr)

variable {lt st : List IntType} {a b c : List Instr}

theorem SegEquiv.refl (lt st : List IntType) (a : List Instr) : SegEquiv lt st a a :=
  fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl

theorem SegEquiv.symm (h : SegEquiv lt st a b) : SegEquiv lt st b a :=
  fun m P _ host s f ρ us rest Q => (h m P host s f ρ us rest Q).symm

theorem SegEquiv.trans (h₁ : SegEquiv lt st a b) (h₂ : SegEquiv lt st b c) : SegEquiv lt st a c :=
  fun m P _ host s f ρ us rest Q =>
    (h₁ m P host s f ρ us rest Q).trans (h₂ m P host s f ρ us rest Q)

theorem OutEquiv.refl (lt st : List IntType) (a : List Instr) : OutEquiv lt st a a :=
  fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl

theorem OutEquiv.symm (h : OutEquiv lt st a b) : OutEquiv lt st b a :=
  fun m P _ host s f ρ us Q hQ => (h m P host s f ρ us Q hQ).symm

theorem OutEquiv.trans (h₁ : OutEquiv lt st a b) (h₂ : OutEquiv lt st b c) : OutEquiv lt st a c :=
  fun m P _ host s f ρ us Q hQ =>
    (h₁ m P host s f ρ us Q hQ).trans (h₂ m P host s f ρ us Q hQ)

/-- `SegEquiv` implies `OutEquiv`. -/
theorem SegEquiv.out (h : SegEquiv lt st a b) : OutEquiv lt st a b :=
  fun m P _ host s f ρ us Q _ => h m P host s f ρ us [] Q

/-- **Function bodies.** Equivalent straight-line bodies (locals typed `lt`, empty
initial stack) have the same every-run weakest precondition for every postcondition. -/
theorem SegEquiv.body (h : SegEquiv lt [] a b) (m : Corr) (P : Profile) {H : Type}
    (host : HostSemantics H) (s : Store H) (f : Frame) (ρ : Env)
    (Q : Silmaril.Wasm.Logic.Core.Post H) :
    Wp m P host s (frameAt f ρ (initState lt [])) (expression a) Q ↔
      Wp m P host s (frameAt f ρ (initState lt [])) (expression b) Q := by
  simpa [codeAt, stackAt, initState] using h m P host s f ρ [] [] Q

end Silmaril.Proofs.Wasm.Auto.Equiv