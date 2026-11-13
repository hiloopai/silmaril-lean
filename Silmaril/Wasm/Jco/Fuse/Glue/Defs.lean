module

public import Silmaril.Wasm.Component.Wiring.Defs

/-!
# Glue code: the code of generated adaptor modules

The jco-style toolchain wraps a core module `M` together with a generated
*adaptor* module whose functions take canonical-ABI calls and delegate to `M`.
Adaptor code is stateless straight-line code over flat core values; `Code` is
that language:

* `Code.ret`: return the current values;
* `Code.trap`: trap;
* `Code.pick ix k`: keep the values at the positions `ix` (in that order;
  an index out of range traps) and continue with `k`;
* `Code.call j k`: call import `j` with the current values; continue with `k`
  on its flat results (a trap, or a non-flat answer, traps).

`Code.run c xs : Prog sigU (Option Payload)` is its meaning on the values
`xs`, and `glueH code : Handler sigU sigU` is the handler of a list of
function bodies: function `i` on flat arguments runs `code[i]`, anything else
traps.

A `Glue` module is a list of function bodies with its core import and export
interfaces; `Glue.handler g : Handler (sigN g.imports.length) (sigN g.exports.length)`
is its semantics (calls beyond its imports trap, as do calls of functions it
does not export).

**Inlining.** `Code.seq c k` runs `c` and continues with `k` on its results;
`Code.inline lib c` replaces every call `call j` of `c` by the body `lib[j]`
(a missing body traps). This is how two glue modules are fused into one:
`Glue.inline g₁ g₂` is the module whose functions are those of `g₂` with the
calls of `g₁`'s functions inlined; it imports what `g₁` imports. Its
correctness, `glueH (inlineAll g₁ g₂) = (glueH g₁).comp (glueH g₂)`, is in
the theorem module.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Fuse

open Silmaril.Games
open Silmaril.Wasm.Component

/-- Stateless straight-line glue code over flat core values. -/
inductive Code where
  /-- Return the current values. -/
  | ret
  /-- Trap. -/
  | trap
  /-- Keep the values at the positions `ix` (in that order) and continue. -/
  | pick (ix : List Nat) (k : Code)
  /-- Call import `j` with the current values and continue on its results. -/
  | call (j : Nat) (k : Code)
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Continue with `k` on a flat answer; trap otherwise. -/
def cont (k : List Flat → Prog sigU (Option Payload)) : Option Payload →
    Prog sigU (Option Payload)
  | some (.flat ys) => k ys
  | _ => .pure none

/-- Select the values at the positions `ix`. -/
def pickVals (ix : List Nat) (xs : List Flat) : Option (List Flat) :=
  ix.mapM fun i => xs[i]?

namespace Code

/-- The meaning of glue code on the current values. -/
def run : Code → List Flat → Prog sigU (Option Payload)
  | .ret, xs => .pure (some (.flat xs))
  | .trap, _ => .pure none
  | .pick ix k, xs =>
    match pickVals ix xs with
    | some ys => k.run ys
    | none => .pure none
  | .call j k, xs => .call (j, .flat xs) (cont k.run)

/-- Run `c`, then `k` on its results (`ret` of `c` becomes `k`). -/
def seq : Code → Code → Code
  | .ret, k => k
  | .trap, _ => .trap
  | .pick ix c, k => .pick ix (c.seq k)
  | .call j c, k => .call j (c.seq k)

/-- Inline the bodies `lib` for the calls of `c` (a missing body traps). -/
def inline (lib : List Code) : Code → Code
  | .ret => .ret
  | .trap => .trap
  | .pick ix c => .pick ix (c.inline lib)
  | .call j c => (lib[j]?.getD .trap).seq (c.inline lib)

/-- The delegation body: call import `j` with the arguments, return its
results. -/
abbrev delegate (j : Nat) : Code := .call j .ret

end Code

/-- The handler of a list of function bodies: function `i` on flat arguments
runs `code[i]`; anything else traps. -/
def glueH (code : List Code) : Handler sigU sigU := fun q =>
  match code[q.1]?, q.2 with
  | some c, .flat xs => c.run xs
  | _, _ => .pure none

/-- A glue (adaptor) core module: core import and export interfaces and one
body per export. -/
structure Glue where
  /-- The core functions it imports. -/
  imports : CoreIface
  /-- The core functions it exports. -/
  exports : CoreIface
  /-- One body per export. -/
  code : List Code
  deriving Repr, Inhabited, BEq

namespace Glue

/-- The semantics of a glue module at its interface sizes. -/
def handler (g : Glue) : Handler (sigN g.imports.length) (sigN g.exports.length) :=
  (widenH g.imports.length).comp ((glueH g.code).comp (narrowH g.exports.length))

/-- **Fusion of glue modules**: the functions of `g₂`, with the calls of the
functions of `g₁` (its imports) inlined. The result imports what `g₁`
imports. -/
def inline (g₁ g₂ : Glue) : Glue where
  imports := g₁.imports
  exports := g₂.exports
  code := g₂.code.map (Code.inline g₁.code)

end Glue

end Silmaril.Wasm.Jco.Fuse
