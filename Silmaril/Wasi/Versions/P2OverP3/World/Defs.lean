module

public import Silmaril.Wasi.Versions.P2.World.Defs
public import Silmaril.Wasi.Versions.P3.Defs

@[expose] public section

/-!
# WASI 0.2 over 0.3: the worlds

The component of relation (c) (`Silmaril.Wasi.Versions.P2OverP3.Comp`) **imports** WASI 0.3 with
the Component Model async built-ins and **exports** the WASI 0.2 interfaces `wasi:io`,
`wasi:cli` and `wasi:clocks` of the slice `Silmaril.Wasi.Versions.P2`.

## Imports: `imp3`

`imp3 = p3World.imports ∪ extra3`: the WASI 0.3 slice of `Silmaril.Wasi.Versions.P3` (with its
`$root` `canon` built-ins `stream.new/read/write/drop-*`, `future.read/drop-readable`,
`waitable-set.new`, `waitable.join`, `waitable-set.wait`) and the further WASI 0.3 functions
the 0.2 `cli`/`clocks` exports need. Checked against `vendor/wasi/0.3.2` (WASI tag
`v0.3.2`, commit `bdadbbb8`):

| Lean | WIT (`@0.3.2`) |
| --- | --- |
| `getEnv3` | `wasi:cli/environment` `get-environment: func() -> list<tuple<string, string>>` (`cli/wit/environment.wit`) |
| `getArgs3` | `wasi:cli/environment` `get-arguments: func() -> list<string>` |
| `cwd3` | `wasi:cli/environment` `get-initial-cwd: func() -> option<string>` |
| `exit3` | `wasi:cli/exit` `exit: func(status: result)` (`cli/wit/exit.wit`) |
| `stderrWrite3` | `wasi:cli/stderr` `write-via-stream: func(data: stream<u8>) -> future<result<_, error-code>>` (`cli/wit/stdio.wit`) |
| `termStdin3`, `termStdout3`, `termStderr3` | `wasi:cli/terminal-{stdin,stdout,stderr}` `get-terminal-*: func() -> option<terminal-*>` (`cli/wit/terminal.wit`) |
| `monoRes3` | `wasi:clocks/monotonic-clock` `get-resolution: func() -> duration` (`clocks/wit/monotonic-clock.wit`) |
| `sysNow3` | `wasi:clocks/system-clock` `now: func() -> instant`, `record instant { seconds: s64, nanoseconds: u32 }` (`clocks/wit/system-clock.wit`) |
| `sysRes3` | `wasi:clocks/system-clock` `get-resolution: func() -> duration` (`duration = u64`, `clocks/wit/types.wit`) |

WASI 0.3 renamed `wall-clock` to `system-clock` and its `datetime` to `instant` (with `s64`
seconds), and `resolution` to `get-resolution`; the 0.2 `wall-clock` exports convert.

## Exports: `exp2`

`exp2 = ioImports ∪ cliImports ∪ clockImports`: the WASI 0.2 functions of `wasi:io`, `wasi:cli`
and `wasi:clocks` in `Silmaril.Wasi.Versions.P2` (vendored WIT `v0.2.9`). The filesystem slice is
not exported.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2

/-! ## Further WASI 0.3 functions -/

/-- `wasi:cli/environment@0.3.2.get-environment`. -/
def getEnv3 : FnName := ⟨"wasi:cli/environment@0.3.2", "get-environment"⟩
/-- `wasi:cli/environment@0.3.2.get-arguments`. -/
def getArgs3 : FnName := ⟨"wasi:cli/environment@0.3.2", "get-arguments"⟩
/-- `wasi:cli/environment@0.3.2.get-initial-cwd`. -/
def cwd3 : FnName := ⟨"wasi:cli/environment@0.3.2", "get-initial-cwd"⟩
/-- `wasi:cli/exit@0.3.2.exit`. -/
def exit3 : FnName := ⟨"wasi:cli/exit@0.3.2", "exit"⟩
/-- `wasi:cli/stderr@0.3.2.write-via-stream`. -/
def stderrWrite3 : FnName := ⟨"wasi:cli/stderr@0.3.2", "write-via-stream"⟩
/-- `wasi:cli/terminal-stdin@0.3.2.get-terminal-stdin`. -/
def termStdin3 : FnName := ⟨"wasi:cli/terminal-stdin@0.3.2", "get-terminal-stdin"⟩
/-- `wasi:cli/terminal-stdout@0.3.2.get-terminal-stdout`. -/
def termStdout3 : FnName := ⟨"wasi:cli/terminal-stdout@0.3.2", "get-terminal-stdout"⟩
/-- `wasi:cli/terminal-stderr@0.3.2.get-terminal-stderr`. -/
def termStderr3 : FnName := ⟨"wasi:cli/terminal-stderr@0.3.2", "get-terminal-stderr"⟩
/-- `wasi:clocks/monotonic-clock@0.3.2.get-resolution`. -/
def monoRes3 : FnName := ⟨"wasi:clocks/monotonic-clock@0.3.2", "get-resolution"⟩
/-- `wasi:clocks/system-clock@0.3.2.now`. -/
def sysNow3 : FnName := ⟨"wasi:clocks/system-clock@0.3.2", "now"⟩
/-- `wasi:clocks/system-clock@0.3.2.get-resolution`. -/
def sysRes3 : FnName := ⟨"wasi:clocks/system-clock@0.3.2", "get-resolution"⟩

/-- The further WASI 0.3 imports. -/
def extra3 : Set FnName :=
  {getEnv3, getArgs3, cwd3, exit3, stderrWrite3, termStdin3, termStdout3, termStderr3, monoRes3,
   sysNow3, sysRes3}

/-- **The imports**: the WASI 0.3 slice with its `canon` built-ins, and `extra3`. -/
def imp3 : Set FnName := p3World.imports ∪ extra3

/-- **The exports**: WASI 0.2 `wasi:io`, `wasi:cli` and `wasi:clocks`. -/
def exp2 : Set FnName := ioImports ∪ cliImports ∪ clockImports

/-- **The world of the component**: import WASI 0.3, export WASI 0.2 io, cli and clocks. -/
def p2OverP3World : World := ⟨imp3, exp2⟩

/-! ## The WASI 0.3 theory -/

/-- **The WASI 0.3 theory of the slice**: typing, the clock theory and the loose stdout theory
of `Silmaril.Wasi.Versions.P3`. -/
def p3Th : Silmaril.Wasm.Resource.Protocol (Unit × ClockSt × OutSt) WEv :=
  typed3.prod (clockTh3.prod stdoutTh3)

/-! ## Membership -/

theorem mem_wasi3 {f : FnName} (h : f ∈ wasiFns3) : f ∈ imp3 := Or.inl (Or.inl h)
theorem mem_canon {f : FnName} (h : f ∈ canonFns) : f ∈ imp3 := Or.inl (Or.inr h)
theorem mem_extra {f : FnName} (h : f ∈ extra3) : f ∈ imp3 := Or.inr h

/-- An import call. -/
abbrev IOp : Type := (nsig imp3).Op

/-- A program of the component over its imports. -/
abbrev Pg (A : Type) : Type := Prog (nsig imp3) A

/-! ## The import calls used -/

/-- `stream.new()`. -/
def opStreamNew : IOp := (⟨cStreamNew, mem_canon (by simp [canonFns])⟩, [])
/-- `stream.write(w, bytes)`. -/
def opStreamWrite (w : Val) (bs : List (BitVec 8)) : IOp :=
  (⟨cStreamWrite, mem_canon (by simp [canonFns])⟩, [w, bytesV bs])
/-- `stream.read(r, n)`. -/
def opStreamRead (r : Val) (n : Nat) : IOp :=
  (⟨cStreamRead, mem_canon (by simp [canonFns])⟩, [r, natV n])
/-- `stream.drop-readable(r)`. -/
def opDropR (r : Val) : IOp := (⟨cStreamDropR, mem_canon (by simp [canonFns])⟩, [r])
/-- `stream.drop-writable(w)`. -/
def opDropW (w : Val) : IOp := (⟨cStreamDropW, mem_canon (by simp [canonFns])⟩, [w])
/-- `future.drop-readable(f)`. -/
def opFutDropR (f : Val) : IOp := (⟨cFutureDropR, mem_canon (by simp [canonFns])⟩, [f])
/-- `waitable-set.new()`. -/
def opWsNew : IOp := (⟨cWsNew, mem_canon (by simp [canonFns])⟩, [])
/-- `waitable.join(w, s)`. -/
def opJoin (w s : Val) : IOp := (⟨cJoin, mem_canon (by simp [canonFns])⟩, [w, s])
/-- `waitable-set.wait(s)`. -/
def opWait (s : Val) : IOp := (⟨cWait, mem_canon (by simp [canonFns])⟩, [s])

/-- `wasi:cli/stdout.write-via-stream(r)`. -/
def opStdout (r : Val) : IOp := (⟨stdoutWrite3, mem_wasi3 (by simp [wasiFns3_eq])⟩, [r])
/-- `wasi:cli/stderr.write-via-stream(r)`. -/
def opStderr (r : Val) : IOp := (⟨stderrWrite3, mem_extra (by simp [extra3])⟩, [r])
/-- `wasi:cli/stdin.read-via-stream()`. -/
def opStdin : IOp := (⟨stdinRead3, mem_wasi3 (by simp [wasiFns3_eq])⟩, [])
/-- `monotonic-clock.now()`. -/
def opNow : IOp := (⟨now3, mem_wasi3 (by simp [wasiFns3_eq])⟩, [])
/-- `monotonic-clock.wait-for(d)` (an `async func`, sync-lowered). -/
def opWaitFor (d : Nat) : IOp := (⟨waitFor3, mem_wasi3 (by simp [wasiFns3_eq])⟩, [.u64 (BitVec.ofNat 64 d)])
/-- A further WASI 0.3 function without arguments. -/
def opExtra (f : FnName) (h : f ∈ extra3) (a : List Val) : IOp := (⟨f, mem_extra h⟩, a)

end Silmaril.Wasi.Versions.P2OverP3
