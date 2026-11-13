module

public import Silmaril.Wasi.Versions.P2.Io.Defs
public import Silmaril.Wasi.Versions.WitImport.Pick.Defs
public import Silmaril.Wasi.Versions.WitImport.RSlices.Defs

@[expose] public section

/-!
# WASI 0.2: `wasi:cli`, `wasi:clocks`, a `wasi:filesystem` slice, and the command world

Checked against the vendored WIT `specs/wasi/v0.2.9/{cli,clocks,filesystem}/*.wit`
(WebAssembly/WASI `v0.2.9`). Stable (`@since`) functions only; `@unstable` ones
(`exit-with-code`, `wasi:clocks/timezone`) are left out.

## Functions

* `wasi:cli`: `environment.{get-environment, get-arguments, initial-cwd}`, `exit.exit`,
  `stdin.get-stdin`, `stdout.get-stdout` (#856's `getStdout`), `stderr.get-stderr`,
  `terminal-{stdin,stdout,stderr}.get-terminal-*`; the export `run.run` (#856's `cliRun`).
* `wasi:clocks`: `monotonic-clock.{now (#856's clockNow), resolution, subscribe-instant,
  subscribe-duration}`, `wall-clock.{now, resolution}`.
* `wasi:filesystem`: #856's slice (`preopens.get-directories`, `descriptor.{open-at, write,
  read}`, `[resource-drop]descriptor`) and `descriptor.{read-via-stream, write-via-stream,
  append-via-stream, get-type}`. As in #856, `open-at` is applied to `(self, path)`; the WIT
  signature also has `path-flags`, `open-flags` and `flags`, which this slice does not model
  (only answers are constrained, so the theory does not depend on the argument layout).

`p2Imports` is the union with `ioImports`; `p2Command = ⟨p2Imports, {run}⟩` is the slice of
`wasi:cli/command@0.2.9` modelled here (sockets, random and http are not part of this slice).

## The theory `p2Th r`

`p2Th r = ioTh r ⊗ clockTh ⊗ pointwise p2Ok ⊗ fsTyped` (`Protocol.prod`):

* the `wasi:io` theory in the reading `r` (`Silmaril.Wasi.Versions.P2.Io`);
* #856's monotonic-clock theory `clockTh` (monotonic `now`);
* `p2Ok`: the WIT result types of the `wasi:cli`, `wasi:clocks` and new `wasi:filesystem`
  functions (`cliOk`, for the functions `ioOp` classifies as `other`), `wall-clock` datetimes
  with `nanoseconds < 10^9`, and **`exit` never returns** (its only admissible answer is a trap:
  the host ends the run);
* #856's filesystem typing theory `fsTyped`.

`option<T>` is the variant with cases `none` (`0`) and `some` (`1`).

## Switched to the WIT import

`cliOk` is **defined from the resolved WIT** (`WitImport.p2P`, read from the vendored files):
for the twelve functions of `WitImport.cli2X` it looks up the function's interface and
signature in the imported table and checks the answer with `WitImport.resOkR`; for the others
(`exit`, the wall clock, the `*-via-stream` functions, `get-type`, `drop`), whose checks the WIT
does not express or that are not exact, it is the hand-written `cliOkH`. The hand-written check
`cliOkH` and the theory built on it (`p2OkH`, `p2ThH`) stay as related variants:
`P2.cliOk_eq_hand`, `p2Ok_eq_hand`, `p2Th_eq_hand` (in `Silmaril.Wasi.Versions.WitImport.RCli2`)
prove them equal. Proofs that need the cases rewrite with `cliOk_eq_hand`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Function names -/

/-- `wasi:cli/environment.get-environment`. -/
def getEnv : FnName := ⟨"wasi:cli/environment", "get-environment"⟩
/-- `wasi:cli/environment.get-arguments`. -/
def getArgs : FnName := ⟨"wasi:cli/environment", "get-arguments"⟩
/-- `wasi:cli/environment.initial-cwd`. -/
def initialCwd : FnName := ⟨"wasi:cli/environment", "initial-cwd"⟩
/-- `wasi:cli/exit.exit`. -/
def cliExit : FnName := ⟨"wasi:cli/exit", "exit"⟩
/-- `wasi:cli/stdin.get-stdin`. -/
def getStdin : FnName := ⟨"wasi:cli/stdin", "get-stdin"⟩
/-- `wasi:cli/stderr.get-stderr`. -/
def getStderr : FnName := ⟨"wasi:cli/stderr", "get-stderr"⟩
/-- `wasi:cli/terminal-stdin.get-terminal-stdin`. -/
def getTermStdin : FnName := ⟨"wasi:cli/terminal-stdin", "get-terminal-stdin"⟩
/-- `wasi:cli/terminal-stdout.get-terminal-stdout`. -/
def getTermStdout : FnName := ⟨"wasi:cli/terminal-stdout", "get-terminal-stdout"⟩
/-- `wasi:cli/terminal-stderr.get-terminal-stderr`. -/
def getTermStderr : FnName := ⟨"wasi:cli/terminal-stderr", "get-terminal-stderr"⟩

/-- `wasi:clocks/monotonic-clock.resolution`. -/
def monoRes : FnName := ⟨"wasi:clocks/monotonic-clock", "resolution"⟩
/-- `wasi:clocks/monotonic-clock.subscribe-instant`. -/
def monoSubInstant : FnName := ⟨"wasi:clocks/monotonic-clock", "subscribe-instant"⟩
/-- `wasi:clocks/monotonic-clock.subscribe-duration`. -/
def monoSubDuration : FnName := ⟨"wasi:clocks/monotonic-clock", "subscribe-duration"⟩
/-- `wasi:clocks/wall-clock.now`. -/
def wallNow : FnName := ⟨"wasi:clocks/wall-clock", "now"⟩
/-- `wasi:clocks/wall-clock.resolution`. -/
def wallRes : FnName := ⟨"wasi:clocks/wall-clock", "resolution"⟩

/-- `wasi:filesystem/types.[method]descriptor.read-via-stream`. -/
def fdReadStream : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.read-via-stream"⟩
/-- `wasi:filesystem/types.[method]descriptor.write-via-stream`. -/
def fdWriteStream : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.write-via-stream"⟩
/-- `wasi:filesystem/types.[method]descriptor.append-via-stream`. -/
def fdAppendStream : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.append-via-stream"⟩
/-- `wasi:filesystem/types.[method]descriptor.get-type`. -/
def fdGetType : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.get-type"⟩

/-- The `wasi:cli` imports of this slice, **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `cliImports_eq`. -/
def cliImports : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.cli2T) WitImport.cliKeys}

/-- **The imported functions of `cliImports` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem cliImports_eq : cliImports = {getEnv, getArgs, initialCwd, cliExit, getStdin, getStdout, getStderr, getTermStdin, getTermStdout, getTermStderr} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.cli2T) WitImport.cliKeys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.cli2T) WitImport.cliKeys).Perm [getEnv, getArgs, initialCwd, cliExit, getStdin, getStdout, getStderr, getTermStdin, getTermStdout, getTermStderr] by decide +kernel).mem_iff]
  simp

/-- The `wasi:clocks` imports (all of `wasi:clocks` 0.2), **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `clockImports_eq`. -/
def clockImports : Set FnName := {f | f ∈ WitImport.names WitImport.clocks2T}

/-- **The imported functions of `clockImports` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem clockImports_eq : clockImports = {clockNow, monoRes, monoSubInstant, monoSubDuration, wallNow, wallRes} := by
  ext f
  show f ∈ WitImport.names WitImport.clocks2T ↔ _
  rw [(show (WitImport.names WitImport.clocks2T).Perm [clockNow, monoRes, monoSubInstant, monoSubDuration, wallNow, wallRes] by decide +kernel).mem_iff]
  simp

/-- The `wasi:filesystem` imports of this slice, **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `fsImports_eq`. -/
def fsImports : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.fs2T ++ WitImport.fs2D) WitImport.fsKeys}

/-- **The imported functions of `fsImports` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem fsImports_eq : fsImports = {getDirs, openAt, fdWrite, fdRead, fdDrop, fdReadStream, fdWriteStream, fdAppendStream, fdGetType} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.fs2T ++ WitImport.fs2D) WitImport.fsKeys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.fs2T ++ WitImport.fs2D) WitImport.fsKeys).Perm [getDirs, openAt, fdWrite, fdRead, fdDrop, fdReadStream, fdWriteStream, fdAppendStream, fdGetType] by decide +kernel).mem_iff]
  simp

/-- The imports of the WASI 0.2 command slice. -/
def p2Imports : Set FnName := ioImports ∪ cliImports ∪ clockImports ∪ fsImports

/-- **The WASI 0.2 command world** (this slice of `wasi:cli/command@0.2.9`). -/
def p2Command : World := ⟨p2Imports, {cliRun}⟩

/-! ## Typing -/

/-- A WIT `string`: a record of characters. -/
def strOk : Val → Bool
  | .record cs => cs.all fun | .char _ => true | _ => false
  | _ => false

/-- A `tuple<string, string>`. -/
def envEntryOk : Val → Bool
  | .record [k, v] => strOk k && strOk v
  | _ => false

/-- An `option<string>`. -/
def optStrOk : Val → Bool
  | .variant 0 none => true
  | .variant 1 (some s) => strOk s
  | _ => false

/-- An `option<own<_>>`. -/
def optHandleOk : Val → Bool
  | .variant 0 none => true
  | .variant 1 (some (.u32 _)) => true
  | _ => false

/-- A `datetime` (`nanoseconds < 10^9`). -/
def datetimeOk : Val → Bool
  | .record [.u64 _, .u32 ns] => decide (ns.toNat < 1000000000)
  | _ => false

/-- `result<own<_>, error-code>`. -/
def handleResOk : Option (List Val) → Bool
  | some [.variant 0 (some (.u32 _))] => true
  | some [.variant 1 (some _)] => true
  | _ => false

/-- **The admissible answers of the `wasi:cli`, `wasi:clocks` and new `wasi:filesystem`
functions, as written by hand** (`cliOk_eq_hand`: equal to `cliOk`). `exit` does not return: its
only admissible answer is the trap `none` (the host ends the run). -/
def cliOkH (f : FnName) (r : Option (List Val)) : Bool :=
  if f = cliExit then r.isNone
  else if f = getEnv then (match r with | some [.record es] => es.all envEntryOk | _ => false)
  else if f = getArgs then (match r with | some [.record ss] => ss.all strOk | _ => false)
  else if f = initialCwd then (match r with | some [v] => optStrOk v | _ => false)
  else if f = getStdin ∨ f = getStdout ∨ f = getStderr ∨ f = monoSubInstant ∨
      f = monoSubDuration then (match r with | some [.u32 _] => true | _ => false)
  else if f = getTermStdin ∨ f = getTermStdout ∨ f = getTermStderr then
    (match r with | some [v] => optHandleOk v | _ => false)
  else if f = monoRes then (match r with | some [.u64 _] => true | _ => false)
  else if f = wallNow ∨ f = wallRes then (match r with | some [v] => datetimeOk v | _ => false)
  else if f = fdReadStream ∨ f = fdWriteStream ∨ f = fdAppendStream then handleResOk r
  else if f = fdGetType then
    (match r with | some [.variant 0 (some (.variant _ none))] => true
                  | some [.variant 1 (some _)] => true | _ => false)
  else if f = streamDrop then (match r with | some [] => true | _ => false)
  else true

/-! ## The check from the WIT import -/

end Silmaril.Wasi.Versions.P2

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi.Versions

/-- The `cliOk` functions whose WIT result has no named type (moved here from
`WitImport.Cli2`). -/
def cli2E : List FnName :=
  [P2.getEnv, P2.getArgs, P2.initialCwd, P2.getStdin, Silmaril.Wasi.getStdout, P2.getStderr,
   P2.getTermStdin, P2.getTermStdout, P2.getTermStderr, P2.monoSubInstant, P2.monoSubDuration]

/-- The functions of `cli2E` and `monotonic-clock.resolution`: the `cliOk` functions whose
hand-written check is exactly the resolved WIT result check (`cliOkH_eqR`; moved here from
`WitImport.RCli2`). -/
def cli2X : List FnName := P2.monoRes :: cli2E

end Silmaril.Wasi.Versions.WitImport

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- **The admissible answers of the `wasi:cli`, `wasi:clocks` and new `wasi:filesystem`
functions, from the WIT import.** For the functions of `WitImport.cli2X`, the interface and the
signature are looked up in the resolved imported table `WitImport.p2P` and the answer is checked
with the resolved WIT typing `WitImport.resOkR`; the other functions (and, unreachably, a
function missing from the table) use the hand-written `cliOkH`. `cliOk_eq_hand`: this is
`cliOkH`. -/
def cliOk (f : FnName) (r : Option (List Val)) : Bool :=
  if f ∈ WitImport.cli2X then
    match WitImport.p2P.1.lookup f with
    | some (i, s) => WitImport.resOkR WitImport.p2P.2 i s r
    | none => cliOkH f r
  else cliOkH f r

/-- The answers of the functions `wasi:io` does not classify must satisfy `cliOk`. -/
def p2Ok : WEv → Bool
  | .imp f _ r => if ioOp f = .other then cliOk f r else true
  | _ => true

/-- `p2Ok` with the hand-written `cliOkH` (`p2Ok_eq_hand`: equal to `p2Ok`). -/
def p2OkH : WEv → Bool
  | .imp f _ r => if ioOp f = .other then cliOkH f r else true
  | _ => true

/-! ## The theory -/

/-- The state of the WASI 0.2 theory. -/
abbrev P2St : Type := IoSt × Option (BitVec 64) × Unit × Unit

/-- **The WASI 0.2 theory** of this slice, in the reading `r`. -/
def p2Th (r : Reading) : Protocol P2St WEv :=
  (ioTh r).prod (clockTh.prod ((pointwise p2Ok).prod fsTyped))

/-- The WASI 0.2 theory with the hand-written `cliOkH` (`p2Th_eq_hand`: equal to `p2Th`). -/
def p2ThH (r : Reading) : Protocol P2St WEv :=
  (ioTh r).prod (clockTh.prod ((pointwise p2OkH).prod fsTyped))

end Silmaril.Wasi.Versions.P2
