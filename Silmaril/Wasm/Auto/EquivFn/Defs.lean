module

public import Silmaril.Wasm.Logic.Total.Defs
public import Silmaril.Wasm.Logic.Instr.Defs
public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Behaviour.Basic

/-!
# Function-level equivalence: definitions

The checkers of `Silmaril.Wasm.Auto.Equiv` (straight-line, extended, in context) relate function **bodies** at
the top level of a configuration (`SegEquiv`, `OutEquivX`, `CEquiv`). A call runs the body inside
`FRAME_n{F} (LABEL_n{} body)`, and the converse of the frame rule is false in general (a body
that reaches `REF.NULL; RETURN_CALL_REF` is stuck at the top level but traps inside a frame, see
`docs/projects/wasm-binaryen-tooling.md`). This module states the function-level notions for bodies whose
every run ends at one known outcome:

* `Pin s' o'`: the postcondition "the store is `s'` and the outcome is `o'`";
* `Pinned P host s F b s' o'`: every run of `b` from `s, F` terminates, and it ends with outcome
  `o'` in store `s'` (total correctness with the pinning postcondition). The straight-line
  executor of `Silmaril.Wasm.Auto.Equiv` pins every body it runs (`pinned_of_xsexec`), and pinning
  is transferred by `OutEquivX` (`Pinned.of_outEquivX`);
* `Fits n o`: the outcome falls through with `n` values or traps;
* `FrameOut n f us Q s' o'`: what a caller in frame `f`, with the values `us` below the frame,
  sees of a body that ended with `o'` in store `s'` (exactly `n` results, or a trap);
* `CallEquivAt P host s a₁ a₂ args`: calling `a₁` or `a₂` on `args` in store `s` has the same
  every-run weakest precondition (both readings) in every caller context: every frame, values
  below the arguments, `CALL_REF` form and postcondition;
* `xOutcome c mem A`: the store and outcome of a symbolic run of `Silmaril.Wasm.Auto.Equiv` in the
  typed context `c`; `outBeh o`: the behaviour of a call whose body ended with `o`;
* `pinSpec s₀ args₀ s' o'`: the function specification of one pinned call (precondition: the
  store is `s₀` and the arguments are `args₀`; postcondition: the store `s'` and outcome `o'`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivFn

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type}

/-- The store is `s'` and the outcome `o'`. -/
def Pin (s' : Store H) (o' : Outcome) : Post H := fun s _ o => s = s' ∧ o = o'

/-- **A pinned configuration**: every run terminates, with outcome `o'` in store `s'`. -/
def Pinned (P : Profile) (host : HostSemantics H) (s : Store H) (F : Frame) (b : List Admin)
    (s' : Store H) (o' : Outcome) : Prop :=
  TWP P host s F b (Pin s' o')

/-- The outcome falls through with `n` values, or traps (the outcomes of a function body of `n`
results that does not branch out of its label, return, throw or tail-call). -/
def Fits (n : Nat) : Outcome → Prop
  | .normal res => res.length = n
  | .trap => True
  | _ => False

/-- What the caller sees of a body that ended with `o'` in store `s'`: `n` results returned on top
of `us`, or a trap. -/
def FrameOut (n : Nat) (f : Frame) (us : List Val) (Q : Post H) (s' : Store H) : Outcome → Prop
  | .normal res => res.length = n ∧ Q s' f (.normal (us ++ res))
  | .trap => Q s' f .trap
  | _ => False

/-- **Call-level equivalence** of the function addresses `a₁` and `a₂` of the store `s` on the
arguments `args`: the same every-run weakest precondition, in both readings, from every caller
frame, values below the arguments, `CALL_REF` form and postcondition. -/
def CallEquivAt (P : Profile) (host : HostSemantics H) (s : Store H) (a₁ a₂ : Nat)
    (args : List Val) : Prop :=
  ∀ (m : Corr) (f : Frame) (vs₀ : List Val) (c : Admin) (Q : Post H), c.IsCallRef →
    (Wp m P host s f (vals vs₀ ++ vals args ++ [.ref (.func a₁), c]) Q ↔
      Wp m P host s f (vals vs₀ ++ vals args ++ [.ref (.func a₂), c]) Q)

/-- The specification of one pinned call: from store `s₀` on the arguments `args₀`, the call ends
in store `s'` with the callee outcome `o'`. -/
def pinSpec (s₀ : Store H) (args₀ : List Val) (s' : Store H) (o' : Outcome) : FSpec H where
  pre := fun s args => s = s₀ ∧ args = args₀
  post := fun _ _ s o => s = s' ∧ o = o'

/-- The behaviour of a call whose callee ended with `o` (`normal` or `trap`). -/
def outBeh : Outcome → Behaviour Val
  | .normal vs => .returns vs
  | .trap => .traps
  | _ => .diverges

open Silmaril.Wasm.Auto.Equiv (XCtx XState firstFail) in
/-- The store and outcome in which the symbolic run `A` ends in the context `c`: a trap at the
first failing guard, or the final stack. -/
def xOutcome (c : XCtx H) (mem : Bool) (A : XState) : Store H × Outcome :=
  match firstFail c.ρ c.mi.bytes A.guards with
  | some T => (c.storeOf mem T, .trap)
  | none => (c.storeOf mem A, .normal (c.stackOf A).reverse)

end Silmaril.Wasm.Auto.EquivFn
