module

public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Logic.Total.Defs

/-!
# Total correctness from the verification-condition generator: definitions

* `cutQ C Q`: the postcondition of a code segment followed by a **cut**: falling through must
  establish the cut predicate `C` on the store, the frame and the stack; every other outcome
  (a branch, a `return`, a trap) must satisfy `Q`. Long functions are verified segment by segment
  (`Silmaril.Wasm.Logic.VC.twp_cut`), with `wpc` on each segment.
* `fnPost n R`: what a function body may end with, in every run: falling through with `n`
  results, `return` (the top `n` values are the results) or a trap. `Silmaril.Wasm.Logic.Exec.bodyPost`
  is its no-`return` case (`fnPost_of_bodyPost`, `bodyPost_iff_fnPost`); the angelic
  `Silmaril.Wasm.Logic.Core.funcPost` (with tail calls) is a third, unrelated form.
* `VCSpecs.TValid`: every specification of a spec context is **totally** correct
  (`Silmaril.Wasm.Logic.Hoare.TFSpecAt`), for calls under total correctness.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type}

/-- Falling through establishes `C`; every other outcome satisfies `Q`. -/
def cutQ (C : Store H → Frame → List Val → Prop) (Q : Post H) : Post H := fun s f o =>
  match o with
  | .normal vs => C s f vs
  | o => Q s f o

/-- A function body of result arity `n` returns (by falling through or by `return`) results
satisfying `R`, or traps with `R s .trap`. -/
def fnPost (n : Nat) (R : Store H → Outcome → Prop) : Post H := fun s _ o =>
  match o with
  | .normal res => res.length = n ∧ R s (.normal res)
  | .ret vs => n ≤ vs.length ∧ R s (.normal (vs.drop (vs.length - n)))
  | .trap => R s .trap
  | _ => False

/-- Every specification of the spec context is totally correct. -/
def VCSpecs.TValid (Γ : VCSpecs H) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) : Prop :=
  ∀ a n S, Γ.specs a = some (n, S) → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a S ∧
    ∀ s args, S.pre s args → (s.funcs[a]?).isSome

end Silmaril.Wasm.Logic.VC
