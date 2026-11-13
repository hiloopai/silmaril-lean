module

public import Silmaril.Wasi.Cli.Main.Defs

/-!
# The WASI 0.2 host of `Command.mainWith`

`api2 : Api p2Command.imports` (`Silmaril.Wasi.Cli.Main`) for the WASI 0.2 command slice
`Versions.P2.p2Command`:

* `args`: `wasi:cli/environment.get-arguments()`, read with `strsOf` (`none` when the answer is
  not a `list<string>`);
* `env`: `get-environment()`, read with `envOf` (empty when ill-formed);
* `put ch b`: `get-stdout()` or `get-stderr()`; if the answer is a handle `h`, the bytes in
  chunks of at most 4096 (`chunk4096`; WASI 0.2: "a write of up to 4096 bytes") by
  `[method]output-stream.blocking-write-and-flush(h, chunk)`, stopping with `false` at the first
  answer that is not `ok`; `false` when the answer is not a handle;
* `finish k`: return `ok` from `run` when `k` is `0` as an exit status (`k.toUInt8 = 0`),
  `error` otherwise. WASI 0.2 has no stable `exit-with-code`, so every failure exits `1`
  (`exit01`).

The theory is the bridge's `cliTh2 i` (`get-arguments`, `get-environment`, `get-directories`
and stdin pinned to `i`); nothing is assumed about `get-stdout`, `get-stderr` or the writes,
whose every answer the program handles. The view is `p2View`.

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host2

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.P2 (p2Command p2Imports cliImports cliImports_eq ioImports ioImports_eq)

/-- The imports of the WASI 0.2 command slice. -/
abbrev I2 : Set FnName := p2Command.imports

theorem getArgs_mem : Versions.P2.getArgs ∈ I2 := by simp [I2, p2Command, p2Imports, cliImports_eq]
theorem getEnv_mem : Versions.P2.getEnv ∈ I2 := by simp [I2, p2Command, p2Imports, cliImports_eq]
theorem getStdout_mem : getStdout ∈ I2 := by simp [I2, p2Command, p2Imports, cliImports_eq]
theorem getStderr_mem : Versions.P2.getStderr ∈ I2 := by
  simp [I2, p2Command, p2Imports, cliImports_eq]
theorem bwf_mem : streamWrite ∈ I2 := by simp [I2, p2Command, p2Imports, ioImports_eq]

/-- The function returning the stream of a channel. -/
def stdFn : Channel → FnName
  | .stdout => getStdout
  | .stderr => Versions.P2.getStderr

theorem stdFn_mem : (ch : Channel) → stdFn ch ∈ I2
  | .stdout => getStdout_mem
  | .stderr => getStderr_mem

/-- A `u32` answer. -/
def u32Of : Option (List Val) → Option (BitVec 32)
  | some [.u32 h] => some h
  | _ => none

/-- The answer `ok` of a `result<_, stream-error>`. -/
def okUnit : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | _ => false

/-- The model's bytes as WASI's. -/
def toWasm (b : Bytes) : List (BitVec 8) := b.map UInt8.toBitVec

/-- Chunks of at most 4096 items. -/
def chunk4096 {α : Type} : List α → List (List α)
  | [] => []
  | a :: l => (a :: l).take 4096 :: chunk4096 ((a :: l).drop 4096)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Write the chunks on the stream `h`, stopping at the first failed write. -/
def writeAll (h : BitVec 32) : List (List (BitVec 8)) → WProg I2 Bool
  | [] => .pure true
  | c :: cs => (callI streamWrite bwf_mem [.u32 h, bytesV c]).bind fun r =>
    if okUnit r then writeAll h cs else .pure false

/-- **The WASI 0.2 host.** -/
def api2 : Api I2 where
  args := (callI Versions.P2.getArgs getArgs_mem []).bind fun r => .pure (strsOf r)
  env := (callI Versions.P2.getEnv getEnv_mem []).bind fun r => .pure ((envOf r).getD [])
  put ch b := (callI (stdFn ch) (stdFn_mem ch) []).bind fun r =>
    match u32Of r with
    | some h => writeAll h (chunk4096 (toWasm b))
    | none => .pure false
  finish k := .pure (some [if k.toUInt8 = 0 then okV none else errV none])

/-- **A `wasi:cli/command` 0.2 component behind the grammar `c`.** -/
def command2 (c : Command) (run : Matches → CliM I2 UInt32) : p2Command.Model :=
  ofBody (api2.body c run)

/-- The WASI 0.2 reading of a specification: exit codes as `0`/`1`, allowing failure. -/
def spec2 (S : Spec) : Spec := Spec.orFail (exit01 S)

end Silmaril.Wasi.Cli.Host2

end
