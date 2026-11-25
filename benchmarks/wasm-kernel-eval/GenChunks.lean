module

import Silmaril.Wasm.KernelEval.Examples
meta import Silmaril.Wasm.KernelEval.Examples

/-! Print a piecewise certificate for `fillSort n`: checkpoints found by compiled evaluation
(untrusted), each chunk then checked by the kernel. Usage:
`lake env lean --run benchmarks/wasm-kernel-eval/GenChunks.lean N CHUNK` -/
open Silmaril.Wasm.KernelEval Examples

def runN (n : Nat) (c : Config NatMem) : Config NatMem :=
  match run n c with | .running c' => c' | _ => c

public def main (args : List String) : IO Unit := do
  let [size, chunk] := args | throw (IO.userError "usage: GenChunks.lean N CHUNK")
  let some (n + 1) := size.toNat? | throw (IO.userError "N must be positive")
  let n := n + 1
  if n > 65536 / 4 then
    throw (IO.userError "N exceeds the number of i32 cells in one memory page")
  let some (k + 1) := chunk.toNat? | throw (IO.userError "CHUNK must be positive")
  let chunkSize := k + 1
  let c0 := Config.init fillSort (fillSortLocals n) (NatMem.zeros 65536)
  let rec count (fuel : Nat) (c : Config NatMem) (acc : Nat) : Option Nat := match fuel with
    | 0 => none
    | f + 1 => match step c with
      | .running c' => count f c' (acc + 1)
      | .done .. => some (acc + 1)
      | .trap | .stuck => none
  let some total := count 10000000 c0 0
    | throw (IO.userError "fillSort did not return within the benchmark step limit")
  let chunks := (total - 1) / chunkSize
  IO.println "module\n\npublic import Silmaril.Wasm.KernelEval.Thms"
  IO.println "public import Silmaril.Wasm.KernelEval.Examples"
  IO.println "public import Silmaril.Wasi.Versions.WitImport.KRfl.Defs"
  IO.println "open Silmaril.Wasm.KernelEval Examples"
  IO.println "set_option Elab.async false\nset_option maxRecDepth 100000"
  IO.println "set_option profiler true\nset_option profiler.threshold 0"
  IO.println s!"def c0 : Config NatMem := Config.init fillSort (fillSortLocals {n}) (NatMem.zeros 65536)"
  let mut c := c0
  for i in [0:chunks] do
    c := runN chunkSize c
    IO.println s!"def c{i+1} : Config NatMem := {(repr c).pretty 1000000}"
    IO.println s!"theorem h{i} : run {chunkSize} c{i} = .running c{i+1} := by kernel_rfl"
  let rest := total - chunks * chunkSize
  IO.println s!"theorem hlast : (match (run {rest} c{chunks}).top? with | some w => w == {n+1} | none => false) = true := by decide +kernel"
