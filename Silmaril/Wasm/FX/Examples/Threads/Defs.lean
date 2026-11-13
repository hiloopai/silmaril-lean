module

public import Silmaril.Wasm.Models.FXL.Defs

/-!
# The explainer's lightweight threads as `StepFXL` programs

The WasmFX explainer (pinned in docs/projects/wasm-wasi.md) has two lightweight-thread examples, written here
instruction by instruction in the machine of `Silmaril.Wasm.Models.FXL`. Folded WAT is flattened
(`(call $f (x))` is `x; call $f`), `(call $log …)` is `log`, the queue imports are `qEmpty`,
`enq`, `deq`, and `ref.func f; cont.new` is `contNew f`. Label indices are de Bruijn, counted
from the instruction that uses them, as in Wasm.

**Static threads** (`staticP`, tag `0` = `$yield` with no payload):

* `0`, `1`, `2`: `$thread1..3` (`log 10; suspend $yield; log 11; suspend $yield; log 12`, and
  20…, 30…);
* `3`: `$scheduler.run`: `loop $l (if queue-empty return) (block $on_yield (result (ref $cont))
  (resume (on $yield $on_yield) (dequeue)) (br $l)) enqueue; br $l`;
* `4`: the exported `run`: enqueue `cont.new` of each thread, `log -1`, run the scheduler,
  `log -2`.

**Dynamic threads** (`dynP`, tag `0` = `$yield`, tag `1` = `$fork` with one continuation):

* `0`: `$main` (`log 0; suspend $fork (cont.new $thread1); log 1; … ; log 3`);
* `1`, `2`, `3`: the threads;
* `4` … `8`: the schedulers `sync`, `kt`, `tk`, `ykt`, `ytk` (parameter `$nextk`, local `0`);
  they share the loop of `sched`, and differ in the code after `$on_fork` and `$on_yield`;
* `9`: the exported `run`: `log -1`, `sync (cont.new $main)`, `log -2`, `kt …`, … , `log -6`;
* `10` … `14`: one scheduler alone on `cont.new $main` (not in the explainer, which runs the
  five in sequence; used to state each scheduler's trace).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.Threads

open Silmaril.Wasm.Models.FXL

/-- A function without parameters, locals or results. -/
def proc (body : List I) : Fn := ⟨0, 0, 0, body⟩

/-- `log a; suspend $yield; log b; suspend $yield; log c` (tag `0` = `$yield`). -/
def thread (a b c : Int) : Fn :=
  proc [.const a, .log, .suspend 0, .const b, .log, .suspend 0, .const c, .log]

/-! ## Static threads -/

/-- `$scheduler.run`. -/
def staticRun : Fn :=
  proc [.loop [.qEmpty, .if_ [.ret] [],
    .block 1 [.deq, .resume [(0, 0)], .br 1],
    .enq, .br 0]]

/-- The static example. -/
def staticP : Prog :=
  [thread 10 11 12, thread 20 21 22, thread 30 31 32, staticRun,
   proc [.contNew 0, .enq, .contNew 1, .enq, .contNew 2, .enq,
     .const (-1), .log, .call 3, .const (-2), .log]]

/-- Tag payload arities of the static example: `$yield` has none. -/
def staticAr : Nat → Nat := fun _ => 0

/-- The output of the static example, as documented. -/
def staticLog : List Int := [-1, 10, 20, 30, 11, 21, 31, 12, 22, 32, -2]

/-! ## Dynamic threads -/

/-- `$main`: fork the three threads (tag `1` = `$fork`). -/
def dynMain : Fn :=
  proc [.const 0, .log, .contNew 1, .suspend 1, .const 1, .log, .contNew 2, .suspend 1,
    .const 2, .log, .contNew 3, .suspend 1, .const 3, .log]

/-- A scheduler with parameter `$nextk`: the loop shared by all five, with the code `onFork`
after the block `$on_fork` (stack: new thread, current thread on top) and `onYield` after the
block `$on_yield` (stack: current thread). Clauses: `$yield` to `$on_yield` (label `1` at the
`resume`), `$fork` to `$on_fork` (label `0`). -/
def sched (onFork onYield : List I) : Fn :=
  ⟨1, 0, 0, [.loop ([.localGet 0, .refIsNull, .if_ [.ret] [],
    .block 1 ([.block 2 [.localGet 0, .resume [(0, 1), (1, 0)], .deq, .localSet 0, .br 2]] ++
      onFork)] ++ onYield)]⟩

/-- `$on_yield` of the asynchronous schedulers: enqueue the current thread, dequeue the next. -/
def yieldAsync : List I := [.enq, .deq, .localSet 0, .br 0]

/-- `sync`: forking enqueues the new thread, yielding carries on. -/
def syncF : Fn := sched [.localSet 0, .enq, .br 1] [.localSet 0, .br 0]

/-- `kt`: no yield on fork, continuation first. -/
def ktF : Fn := sched [.localSet 0, .enq, .br 1] yieldAsync

/-- `tk`: no yield on fork, new thread first. -/
def tkF : Fn := sched [.enq, .localSet 0, .br 1] yieldAsync

/-- `ykt`: yield on fork, continuation first. -/
def yktF : Fn := sched [.enq, .enq, .deq, .localSet 0, .br 1] yieldAsync

/-- `ytk`: yield on fork, new thread first. -/
def ytkF : Fn := sched [.localSet 0, .enq, .localGet 0, .enq, .deq, .localSet 0, .br 1] yieldAsync

/-- `cont.new $main` passed to scheduler `s`. -/
def runOne (s : Nat) : List I := [.contNew 0, .call s]

/-- The dynamic example. -/
def dynP : Prog :=
  [dynMain, thread 10 11 12, thread 20 21 22, thread 30 31 32,
   syncF, ktF, tkF, yktF, ytkF,
   proc ([.const (-1), .log] ++ runOne 4 ++ [.const (-2), .log] ++ runOne 5 ++
     [.const (-3), .log] ++ runOne 6 ++ [.const (-4), .log] ++ runOne 7 ++
     [.const (-5), .log] ++ runOne 8 ++ [.const (-6), .log]),
   proc (runOne 4), proc (runOne 5), proc (runOne 6), proc (runOne 7), proc (runOne 8)]

/-- Tag payload arities of the dynamic example: `$yield` none, `$fork` one continuation. -/
def dynAr : Nat → Nat
  | 1 => 1
  | _ => 0

/-- The output of `sync` alone (as documented for the synchronous scheduler). -/
def syncLog : List Int := [0, 1, 2, 3, 10, 11, 12, 20, 21, 22, 30, 31, 32]

/-- The output of `kt` alone (the block between `-2` and `-3` of the documented output). -/
def ktLog : List Int := [0, 1, 2, 3, 10, 20, 30, 11, 21, 31, 12, 22, 32]

/-- The output of `tk` alone (between `-3` and `-4`). -/
def tkLog : List Int := [0, 10, 1, 20, 11, 2, 30, 21, 12, 3, 31, 22, 32]

/-- The output of `ykt` alone (between `-4` and `-5`). -/
def yktLog : List Int := [0, 1, 10, 2, 20, 11, 3, 30, 21, 12, 31, 22, 32]

/-- The output of `ytk` alone (between `-5` and `-6`). -/
def ytkLog : List Int := [0, 10, 1, 11, 20, 2, 12, 21, 30, 3, 22, 31, 32]

/-- The documented output of the dynamic example's `run`. -/
def dynLog : List Int :=
  [-1] ++ syncLog ++ [-2] ++ ktLog ++ [-3] ++ tkLog ++ [-4] ++ yktLog ++ [-5] ++ ytkLog ++ [-6]

end Silmaril.Wasm.FX.Examples.Threads
