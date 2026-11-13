module

public import Silmaril.Wasm.Component.Streams.Proc.Defs

/-!
# Running the pipeline: schedulers

Executable drivers for the pipeline of `Silmaril.Wasm.Component.Streams.Proc`: `stepBy` performs one
step of the chosen component (the consumer with a chosen read size), `runChoices` follows a list
of choices, and `runRandom` picks, at every step, a component and a read size from a
pseudo-random sequence (a 64-bit linear congruential generator), skipping components that cannot
step, until no component can step. `Silmaril.Wasm.Component.Streams.Run.Thms` proves that every run
is a sequence of pipeline steps (`Steps`), so the theorems of `Proc.Thms` apply to the systems the
drivers reach; `tools/wasm-streams` runs them on byte streams.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Run

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async
open Silmaril.Wasm.Component.Streams.Proc

variable {σ : Type}

/-- Which component steps. -/
inductive Choice where
  | prod
  | trans
  /-- The consumer, reading up to `n` items. -/
  | cons (n : Nat)

/-- One step of the chosen component. -/
def stepBy (T : Tr σ Val Val) (N : Nat) : Choice → Sys σ → Option (Sys σ)
  | .prod, s => (pStep s.st s.p).map fun q => { s with st := q.1, p := q.2 }
  | .trans, s => (tStep T N s.st s.t).map fun q => { s with st := q.1, t := q.2 }
  | .cons n, s =>
    if 0 < n then (cStep n s.st s.c).map fun q => { s with st := q.1, c := q.2 } else none

/-- The initial system: the setup store, the producer about to write `cs`. -/
def start (T : Tr σ Val Val) (cs : List (List Val)) : Option (Sys σ) :=
  (runOps Store.empty setupOps).map fun st => { st, p := .send cs, t := .rd T.init, c := .recv [] }

/-- The first choice of the list that can step, with the system after it. -/
def firstStep (T : Tr σ Val Val) (N : Nat) (s : Sys σ) : List Choice → Option (Sys σ)
  | [] => none
  | ch :: chs =>
    match stepBy T N ch s with
    | some s' => some s'
    | none => firstStep T N s chs

/-- The next value of the generator. -/
def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- The choices in the order tried at a step with random value `r`. -/
def order (r maxRead : Nat) : List Choice :=
  let c := Choice.cons (1 + (r / 7) % maxRead)
  match r % 3 with
  | 0 => [.prod, .trans, c]
  | 1 => [.trans, c, .prod]
  | _ => [c, .prod, .trans]

/-- **A random run**: at most `fuel` steps; the final system and the number of steps. -/
def runRandom (T : Tr σ Val Val) (N maxRead : Nat) : Nat → Nat → Sys σ → Sys σ × Nat
  | 0, _, s => (s, 0)
  | fuel + 1, seed, s =>
    match firstStep T N s (order seed maxRead) with
    | some s' => let r := runRandom T N maxRead fuel (lcg seed) s'; (r.1, r.2 + 1)
    | none => (s, 0)

/-- All three components have finished; the consumer's items. -/
def finished (s : Sys σ) : Option (List Val) :=
  match s.p, s.t, s.c with
  | .fin, .fin, .fin acc => some acc
  | _, _, _ => none

end Silmaril.Wasm.Component.Streams.Run
