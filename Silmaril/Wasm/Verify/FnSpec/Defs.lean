module

public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Logic.Words.Defs
public import Silmaril.Wasm.Examples.Common.Defs

/-!
# Function specifications checked by `wasm_vc`

A small, uniform way to state and prove what a Wasm function computes, for **every** input: the
caller writes a `FnSpec`, the tactic `wasm_vc` (`Silmaril.Wasm.Verify.FnSpec.Thms`) proves
`S.vc fn` for the function `fn` of a quoted (`wat3!`) or decoded (`.wasm`) module, and
`FnSpec.sound` turns that into a valid every-run specification of the function at every
profile and for every host relation.

* `FnSpec α`: the arguments `args x` for each input `x : α` (for example
  `fun (p, x) => [.i32 p, .i32 x]`), a precondition and a postcondition on the module instance,
  the store and the results, and loop invariants (`Silmaril.Wasm.Logic.VC.Invs`, one per loop in
  pre-order; `True` by default);
* `FnSpec.vc S fn`: the verification condition, computed by the verified generator
  `Silmaril.Wasm.Logic.VC.wpc` (straight-line code, integer loads and stores, `select`, `block`,
  `if`, `loop`, `br`, `br_if`, `return`): every exit of the body is a normal return of
  `nresults` values meeting the postcondition (no trap);
* two shapes cover most small functions:
  - `FnSpec.pure args post`: the store is unchanged and the results meet `post x res`;
  - `FnSpec.mem args post`: memory `0` of the instance holds bytes `B` (`MemAt`); afterwards it
    holds `write x B` (default: `B`, a read-only function), the rest of the store is unchanged,
    and the results meet `post x B res`. Read words with `Silmaril.Wasm.Logic.Words.wd B a`, write
    them with `wr B a v`;
* `FnSpec.fspec S fi a x`: the specification of the call of the function instance `fi` at
  address `a` on the input `x` (`Silmaril.Wasm.Logic.Hoare.FSpec`);
* `Verified m i S`: function `i` of the module `m` meets `S` (`∃ fn, m.funcs[i]? = some fn ∧
  S.vc fn`), the statement form for a project value of format `wasm`/`wat`.

These are partial-correctness statements with safety (every run that ends returns normally and
meets the postcondition; no run gets stuck or traps), as `Silmaril.Wasm.Logic.Hoare`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.VC (wpc Invs)
open Silmaril.Wasm.Logic.Hoare (FSpec)
open Silmaril.Wasm.Logic.Words (MemAt)

/-- **A function specification**, indexed by the inputs `x : α`. -/
structure FnSpec (α : Type) where
  /-- The arguments of the call on input `x`. -/
  args : α → List Val
  /-- The number of results. -/
  nresults : Nat := 1
  /-- The precondition, on the input, the module instance and the store. -/
  pre : α → ModuleInst → Store Nat → Prop
  /-- The postcondition, on the input, the instance, the store before, the results and the
  store after. -/
  post : α → ModuleInst → Store Nat → List Val → Store Nat → Prop
  /-- The loop invariants (`Invs`: loop number, store, frame, loop parameters), given the input,
  the instance and the initial store. -/
  inv : α → ModuleInst → Store Nat → Invs Nat := fun _ _ _ _ _ _ _ => True

/-- **The verification condition** of `fn` for `S`: for every input, instance and store meeting
the precondition, the generator's condition holds for the body in the callee's initial frame,
with every exit a normal return of `nresults` values meeting the postcondition. -/
def FnSpec.vc {α : Type} (S : FnSpec α) (fn : Func) : Prop :=
  ∀ x mi s, S.pre x mi s →
    wpc (S.inv x mi s) 0 fn.body
      (Silmaril.Wasm.Examples.Common.bodyPost S.nresults fun s' o =>
        ∃ res, o = .normal res ∧ S.post x mi s res s')
      s (Frame.forCall mi (S.args x) fn.locals) []

/-- A function that leaves the store unchanged and whose results meet `post x res`. -/
def FnSpec.pure {α : Type} (args : α → List Val) (post : α → List Val → Prop)
    (pre : α → Prop := fun _ => True) (nresults : Nat := 1)
    (inv : α → ModuleInst → Store Nat → Invs Nat := fun _ _ _ _ _ _ _ => True) : FnSpec α where
  args := args
  nresults := nresults
  pre x _ _ := pre x
  post x _ s res s' := s' = s ∧ post x res
  inv := inv

/-- A function over memory `0`: from bytes `B` meeting `pre x B`, it leaves memory `0` holding
`write x B` (and the rest of the store unchanged) and its results meet `post x B res`. -/
def FnSpec.mem {α : Type} (args : α → List Val) (post : α → ByteArray → List Val → Prop)
    (pre : α → ByteArray → Prop := fun _ _ => True)
    (write : α → ByteArray → ByteArray := fun _ B => B) (nresults : Nat := 1)
    (inv : α → ModuleInst → Store Nat → Invs Nat := fun _ _ _ _ _ _ _ => True) : FnSpec α where
  args := args
  nresults := nresults
  pre x mi s := ∃ ma mt B, MemAt s mi ma mt B ∧ pre x B
  post x mi s res s' := ∀ ma mt B, MemAt s mi ma mt B →
    s' = s.setMem ma ⟨mt, write x B⟩ ∧ post x B res
  inv := inv

/-- The specification of the call of the function instance `fi` at address `a` on input `x`. -/
def FnSpec.fspec {α : Type} (S : FnSpec α) (fi : FuncInst Nat) (a : Nat) (x : α) : FSpec Nat where
  pre s args := s.funcs[a]? = some fi ∧ args = S.args x ∧ S.pre x fi.module s
  post s _ s' o := ∃ res, o = .normal res ∧ S.post x fi.module s res s'

/-- **Function `i` of the module `m` meets `S`.** -/
def Verified {α : Type} (m : Module) (i : Nat) (S : FnSpec α) : Prop :=
  ∃ fn, m.funcs[i]? = some fn ∧ S.vc fn

end Silmaril.Wasm.Verify
