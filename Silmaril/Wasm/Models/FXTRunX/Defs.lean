module

public import Silmaril.Wasm.Models.FXTRun.Defs

/-!
# The `StepFXT` interpreter with traps

`Silmaril.Wasm.Models.FXTRun.tstep` stops at a trap, and at a `resume` of a consumed continuation,
so `checkT` checks only runs that finish with no values. This module adds, next to it and
without changing it, the trap steps of `StepFX'`:

* `resume` of a consumed continuation traps (`resumeUsed`);
* a trap after values or before code becomes the whole code (`trapSeq`), and a label, frame or
  handler whose body is a trap is a trap (`trapLabel`, `trapFrame`, `trapHandler`), looking
  through labels, frames and handlers for the first non-value (`xstep`, fuel `d`).

`stepX` takes a `tstep` step when there is one and a trap step otherwise; `runX` iterates it,
and `checkTrapX` tests that a run ends with the code `trap` and a given log
(`Silmaril.Wasm.Models.FXTRunX.Thms`: soundness, and the behaviour `ObsT.ret log traps`).

A Silmaril addition (Follow-up 5 workflow, track fx).
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXTRunX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXTRun

/-- Is the code exactly `trap`? -/
def isTrap : List AdminFX → Bool
  | [.core .trap] => true
  | _ => false

/-- The last value is a consumed continuation: the values before it. -/
def usedCont (K : List (Option ContFX)) (vs : List FVal) : Option (List FVal) :=
  match lastCont vs with
  | some (u, k) =>
    match K[k]? with
    | some none => some u
    | _ => none
  | none => none

/-- A recursive trap stepper (continuation store fixed). -/
abbrev XStepper := Frame → List AdminFX → Option (List AdminFX)

/-- **A trap step at the head** `vs; e; rest`. -/
def trapHead (rec : XStepper) (f : Frame) (K : List (Option ContFX)) (vs : List FVal)
    (rest : List AdminFX) : AdminFX → Option (List AdminFX)
  | .core .trap => if vs.isEmpty && rest.isEmpty then none else some [.core .trap]
  | .fx (.resume _ _) => (usedCont K vs).map fun u => fvals u ++ [.core .trap] ++ rest
  | .label n k body =>
    if isTrap body then some (fvals vs ++ [.core .trap] ++ rest)
    else (rec f body).map fun b => fvals vs ++ [.label n k b] ++ rest
  | .frame n fi body =>
    if isTrap body then some (fvals vs ++ [.core .trap] ++ rest)
    else (rec fi body).map fun b => fvals vs ++ [.frame n fi b] ++ rest
  | .handler hs body =>
    if isTrap body then some (fvals vs ++ [.core .trap] ++ rest)
    else (rec f body).map fun b => fvals vs ++ [.handler hs b] ++ rest
  | _ => none

/-- **One trap step**, looking at most `d` levels deep. -/
def xstep (K : List (Option ContFX)) : Nat → XStepper
  | 0, _, _ => none
  | d + 1, f, code =>
    match splitV code with
    | (_, []) => none
    | (vs, e :: rest) => trapHead (xstep K d) f K vs rest e

variable {H : Type} (tar : Nat → Nat) (fx : H → Option FuncFX) (intr : H → Option Intr)

/-- One step: a `tstep` step, or else a trap step. -/
def stepX (d : Nat) (c : ConfigT H) : Option (ConfigT H) :=
  match stepC tar fx intr d c with
  | some c' => some c'
  | none =>
    (xstep c.cfg.conts d c.cfg.frame c.cfg.code).map fun code =>
      ⟨⟨c.cfg.store, c.cfg.conts, c.cfg.frame, code⟩, c.tbl⟩

/-- Run at most `n` steps (stopping when no step applies). -/
def runX (d : Nat) : Nat → ConfigT H → ConfigT H
  | 0, c => c
  | n + 1, c =>
    match stepX tar fx intr d c with
    | some c' => runX d n c'
    | none => c

/-- The run of `n` steps ends with the code `trap` and the log `log`. -/
def checkTrapX (d n : Nat) (c : ConfigT H) (log : List Val) : Bool :=
  let e := runX tar fx intr d n c
  isTrap e.cfg.code && decide (e.tbl.log = log)

end Silmaril.Wasm.Models.FXTRunX
