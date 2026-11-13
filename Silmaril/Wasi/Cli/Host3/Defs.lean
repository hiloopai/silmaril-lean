module

public import Silmaril.Wasi.Cli.View3.Defs
public import Silmaril.Wasi.Cli.Host2.Defs

/-!
# The WASI 0.3 host of `Command.mainWith`

`api3 : Api I3` (`Silmaril.Wasi.Cli.Main`) for the WASI 0.3 CLI world `p3CliWorld`:

* `args`, `env`: `wasi:cli/environment@0.3.2.get-arguments()`, `get-environment()`, read as in
  WASI 0.2 (`strsOf`, `envOf`);
* `put ch b` (`put3`), the canonical ABI's way of writing a byte string synchronously:
  `stream.new()` (a readable end `r` and a writable end `w`), `write-via-stream(r)` of
  `wasi:cli/stdout` or `wasi:cli/stderr`, `stream.write(w, b)`; if it reports `COMPLETED` with
  all of `b`, `stream.drop-writable(w)` and `true`; if it reports `BLOCKED`,
  `waitable-set.new()`, `waitable.join(w, set)`, `waitable-set.wait(set)` and the same check
  on the `STREAM_WRITE` event (code `3`, index `w`); anything else is `false` (a short or
  dropped write, an ill-formed answer). The future of `write-via-stream` is not awaited.
* `finish k`: return `ok` from `run` when `k` is `0` as an exit status, otherwise
  `wasi:cli/exit.exit-with-code(k)` (and `error` if the host returns from it). Exit codes are
  exact.

The theory is `cliTh3 i` (`get-arguments`, `get-environment`, `get-directories`); the view is
`p3CliView`.

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host3

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult)
open Silmaril.Wasi.Versions.P3 (natOf copyOf cStreamNew cStreamWrite cStreamDropW cWsNew cJoin cWait
  stdoutWrite3 canonFns p3World)
open Silmaril.Wasi.Cli.Host2 (u32Of toWasm)

/-- The imports of the WASI 0.3 CLI world. -/
abbrev I3 : Set FnName := p3CliWorld.imports

theorem canon_mem {f : FnName} (h : f ∈ canonFns) : f ∈ I3 := Or.inl (Or.inr h)
theorem extra_mem {f : FnName}
    (h : f ∈ ({W3.getArgs, W3.getEnv, exit3, W3.exitCode, W3.stderrWrite, W3.writeVia} :
      Set FnName)) : f ∈ I3 := Or.inr h

theorem new_mem : cStreamNew ∈ I3 := canon_mem (by simp [canonFns])
theorem write_mem : cStreamWrite ∈ I3 := canon_mem (by simp [canonFns])
theorem dropW_mem : cStreamDropW ∈ I3 := canon_mem (by simp [canonFns])
theorem wsNew_mem : cWsNew ∈ I3 := canon_mem (by simp [canonFns])
theorem join_mem : cJoin ∈ I3 := canon_mem (by simp [canonFns])
theorem wait_mem : cWait ∈ I3 := canon_mem (by simp [canonFns])
theorem stdout_mem : stdoutWrite3 ∈ I3 :=
  Or.inl (Or.inl (by rw [Versions.P3.wasiFns3_eq]; exact Or.inl rfl))
theorem args_mem : W3.getArgs ∈ I3 := extra_mem (by simp)
theorem env_mem : W3.getEnv ∈ I3 := extra_mem (by simp)
theorem exitCode_mem : W3.exitCode ∈ I3 := extra_mem (by simp)
theorem stderr_mem : W3.stderrWrite ∈ I3 := extra_mem (by simp)

/-- The `write-via-stream` of a channel. -/
def outFn : Channel → FnName
  | .stdout => stdoutWrite3
  | .stderr => W3.stderrWrite

theorem outFn_mem : (ch : Channel) → outFn ch ∈ I3
  | .stdout => stdout_mem
  | .stderr => stderr_mem

/-- A `stream.new` answer: the readable and the writable end. -/
def pairOf : Option (List Val) → Option (BitVec 32 × BitVec 32)
  | some [.u32 r, .u32 w] => some (r, w)
  | _ => none

/-- A `waitable-set.wait` answer reporting that the write on `w` completed with `len` items. -/
def waitOk (n : Option (List Val)) (w : BitVec 32) (len : Nat) : Bool :=
  match n with
  | some [cv, iv, pv] => decide (natOf cv = some 3 ∧ natOf iv = some w.toNat ∧
      (natOf pv >>= copyOf) = some (some (.completed, len)))
  | _ => false

/-- Drop the writable end, and succeed. -/
def dropW (w : BitVec 32) : WProg I3 Bool :=
  (callI cStreamDropW dropW_mem [.u32 w]).bind fun _ => .pure true

/-- After the `waitable-set.wait` of a blocked write. -/
def afterWait (w : BitVec 32) (len : Nat) (n : Option (List Val)) : WProg I3 Bool :=
  if waitOk n w len then dropW w else .pure false

/-- Wait for a blocked write. -/
def waitWrite (w : BitVec 32) (len : Nat) : WProg I3 Bool :=
  (callI cWsNew wsNew_mem []).bind fun n =>
    match u32Of n with
    | some ws => (callI cJoin join_mem [.u32 w, .u32 ws]).bind fun _ =>
        (callI cWait wait_mem [.u32 ws]).bind (afterWait w len)
    | none => .pure false

/-- After `stream.write(w, b)` of `len` bytes. -/
def afterWrite (w : BitVec 32) (len : Nat) (n : Option (List Val)) : WProg I3 Bool :=
  match copyAns n with
  | some (some (.completed, k)) => if k = len then dropW w else .pure false
  | some none => waitWrite w len
  | _ => .pure false

/-- **Write bytes on a channel** (WASI 0.3). -/
def put3 (ch : Channel) (b : Bytes) : WProg I3 Bool :=
  (callI cStreamNew new_mem []).bind fun n =>
    match pairOf n with
    | some (r, w) => (callI (outFn ch) (outFn_mem ch) [.u32 r]).bind fun _ =>
        (callI cStreamWrite write_mem [.u32 w, bytesV (toWasm b)]).bind
          (afterWrite w (toWasm b).length)
    | none => .pure false

/-- **End the run with an exit code** (WASI 0.3): `ok`, or `exit-with-code`. -/
def finish3 (k : UInt32) : BProg I3 :=
  if k.toUInt8 = 0 then .pure (some [okV none])
  else (callI W3.exitCode exitCode_mem [.u8 k.toUInt8.toBitVec]).bind fun _ =>
    .pure (some [errV none])

/-- **The WASI 0.3 host.** -/
def api3 : Api I3 where
  args := (callI W3.getArgs args_mem []).bind fun r => .pure (strsOf r)
  env := (callI W3.getEnv env_mem []).bind fun r => .pure ((envOf r).getD [])
  put := put3
  finish := finish3

/-- **A `wasi:cli/command` 0.3 component behind the grammar `c`.** -/
def command3 (c : Command) (run : Matches → CliM I3 UInt32) : p3CliWorld.Model :=
  ofBody (api3.body c run)

end Silmaril.Wasi.Cli.Host3

end
