module

public import Silmaril.Project.WasmP3Rust.CoreLayer.Defs
public import Silmaril.Project.WasmP3Rust.DenX.Defs
public import Mathlib.Data.Nat.Find

/-!
# The core layer with a re-entrant `realloc`: a faithful `CoreExecX`

`DenX.den Ks` lowers the `list<string>` answer of `get-arguments` as the Canonical ABI does,
calling `realloc` in the component's core instance while the core thread that called the
lowered import is suspended. It abstracts that call as `CoreExecX.alloc`. `CoreLayer.coreKs`
(silmaril's Core 3.0 interpreter on the component's core layer) has no `alloc`: its
configurations hold one thread. This module adds the faithful one.

## `realloc` (`reallocOf`)

The `realloc` option of the sync `canon lower` of `get-arguments` (the core function `k` with
`DenX.isGetArgs`): a core function index of the component.

## The re-entrant call (`allocFuel`, `allocExact`)

`allocFuel L ra n x size align`: a **second thread** `Thread.invokeFlat a [0, 0, align, size]`
on the store of `x` (the function at `ra` in the core function space, address `a`), run by the
same interpreter step (`internalC (stepI neverFail)`) until it returns one value `p`, within `n`
steps; the result is the new store with the suspended thread of `x` unchanged, and `p`. A
callout of the second thread (realloc calling an import), a trap, or no return within `n`
steps is `none`.

`allocExact L ra x size align` is `allocFuel` with the least sufficient fuel when some fuel
suffices, and `none` otherwise (classical; the interpreter is deterministic, so all sufficient
fuels agree: `CoreLayerX.Thms.allocExact_of_fuel`). This is the Canonical ABI's
`realloc(0, 0, align, size)` call, with a diverging `realloc` read as a trap (the CLI specs
of the bridge allow a failing run; a real host would hang instead).

## The core semantics (`coreKsX`)

`execX L ra = { exec L with alloc := allocExact L ra }`, and `coreKsX c` is it on `layer c`
with `reallocOf c` (a layer with no entry and a failing `alloc` otherwise). `execXFuel L ra n`
uses `allocFuel` with fuel `n`, for testing (`tools/cli-core-trace`).

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.CoreLayerX

open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.CoreLayer
open Silmaril.Project.WasmP3Rust.DenX (CoreExecX isGetArgs)
open Silmaril.Wasm.Component.BinaryP3 (Ast)
open Silmaril.Wasm.SingleThreaded (Thread)

/-- **The `realloc` of the lowering of `get-arguments`**: a core function index. -/
def reallocOf (c : Ast) : Option Nat :=
  let S := spaces c
  (List.range S.coreFns.length).findSome? fun k =>
    if isGetArgs S k then
      match S.coreFns[k]? with
      | some (.canon (.lower _ os)) => os.findSome? fun
        | .realloc i => some i
        | _ => none
      | _ => none
    else none

/-- Run the thread `t` on the store `s` until it returns one value, within `n` steps. -/
def runTo (s : St) (t : Thread) : Nat → Option (St × Nat)
  | 0 => none
  | n + 1 =>
    match Silmaril.Wasm.Component.Engine.Core3.statusE oracle s t with
    | .returned (.values [v]) => some (s, ofVal v)
    | .running =>
      match Silmaril.Wasm.SingleThreaded.internalC
          (Silmaril.Wasm.SingleThreaded.Exec.stepI oracle) (s, t) with
      | some (s', t') => runTo s' t' n
      | none => none
    | _ => none

/-- **`realloc(0, 0, align, size)` as a re-entrant call**, within `n` steps: a second thread on
the store; the suspended thread of `x` is kept. -/
def allocFuel (L : Layer) (ra n : Nat) (x : Conf) (size align : Nat) : Option (Conf × Nat) :=
  match L.funcs.getD ra .none with
  | .addr (.func a) =>
    (args? x.store a [0, 0, align, size]).bind fun vs =>
      (runTo x.store (Thread.invokeFlat a vs) n).map fun r => (⟨r.1, x.thread⟩, r.2)
  | _ => none

open Classical in
/-- **The re-entrant `realloc` call**, without a step bound: `allocFuel` with the least fuel
that suffices, `none` when none does. -/
noncomputable def allocExact (L : Layer) (ra : Nat) (x : Conf) (size align : Nat) :
    Option (Conf × Nat) :=
  if h : ∃ n, (allocFuel L ra n x size align).isSome then
    allocFuel L ra (Nat.find h) x size align
  else none

/-- The core layer with the re-entrant `realloc` `ra`. -/
noncomputable def execX (L : Layer) (ra : Nat) : CoreExecX :=
  { exec L with alloc := allocExact L ra }

/-- The same with a step bound on `realloc` (computable; for tests). -/
def execXFuel (L : Layer) (ra n : Nat) : CoreExecX :=
  { exec L with alloc := allocFuel L ra n }

/-- A core layer with no entry and no `alloc`. -/
def noCoreX : CoreExecX := { noCore with alloc := fun _ _ _ => none }

/-- **The faithful core semantics of components**, with the re-entrant `realloc`. -/
noncomputable def coreKsX (c : Ast) : CoreExecX :=
  match layer c, reallocOf c with
  | some L, some ra => execX L ra
  | _, _ => noCoreX

end Silmaril.Project.WasmP3Rust.CoreLayerX

end
