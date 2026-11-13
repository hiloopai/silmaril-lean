module

public import Silmaril.Wasm.Wasmi.Observed.Defs

/-!
# Code without rounding operators

The wasmi 0.40.0 model (`Silmaril.Wasm.Wasmi.Observed.Step`) differs from Core 3.0 only at the
rounding operators `ceil`, `floor`, `trunc`, `nearest` (`IsRound`). This module names the code
and the points on which it cannot differ:

* `rfI`, `rfIs`: an instruction, or a sequence, has no rounding operator, also inside the bodies
  of `block`, `loop`, `if` and `try_table`;
* `rfA`, `rfAs`: the same for runtime code, also inside the continuations and bodies of
  `LABEL`, and the bodies of `HANDLER` and `FRAME`;
* `rfF`, `StoreFree`: every Wasm function instance of the store has a body without rounding
  operators (host functions are not inspected);
* `Free c`: a configuration whose code and store are both free of rounding operators;
* `HostKeeps host`: every store a host call returns is `StoreFree` when the store it was given
  is (a host that does not install Wasm code with rounding operators).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.RoundFree

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Wasmi.Observed

variable {H : Type}

mutual
/-- The instruction has no rounding operator, also inside its structured bodies. -/
def rfI : Instr → Bool
  | .floatUnOp _ op => !IsRound op
  | .block _ b => rfIs b
  | .loop _ b => rfIs b
  | .tryTable _ _ b => rfIs b
  | .if_ _ b₁ b₂ => rfIs b₁ && rfIs b₂
  | _ => true

/-- No instruction of the sequence has a rounding operator. -/
def rfIs : List Instr → Bool
  | [] => true
  | i :: is => rfI i && rfIs is
end

mutual
/-- The administrative instruction has no rounding operator, also inside labels (continuation
and body), handlers and frames. -/
def rfA : Admin → Bool
  | .plain i => rfI i
  | .label _ cont b => rfIs cont && rfAs b
  | .handler _ _ b => rfAs b
  | .frame _ _ b => rfAs b
  | _ => true

/-- No administrative instruction of the code has a rounding operator. -/
def rfAs : List Admin → Bool
  | [] => true
  | a :: as => rfA a && rfAs as
end

/-- A function instance whose code, if it is Wasm code, has no rounding operator. -/
def rfF (fi : FuncInst H) : Bool :=
  match fi.code with
  | .wasm f => rfIs f.body
  | .host _ => true

/-- **A store without rounding operators**: every function instance satisfies `rfF`. -/
def StoreFree (s : Store H) : Prop := ∀ fi ∈ s.funcs, rfF fi = true

/-- **A configuration without rounding operators**: its code and its store. -/
def Free (c : Config H) : Prop := rfAs c.code = true ∧ StoreFree c.store

/-- **A host that keeps stores free of rounding operators.** -/
def HostKeeps (host : HostSemantics H) : Prop :=
  ∀ h s vs s' r, host h s vs (.returned s' r) → StoreFree s → StoreFree s'

end Silmaril.Wasm.Wasmi.RoundFree
