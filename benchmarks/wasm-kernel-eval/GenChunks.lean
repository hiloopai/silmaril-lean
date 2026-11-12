import Silmaril.Wasm.KernelEval.Examples
/-! Print a piecewise certificate for `fillSort n`: checkpoints found by compiled evaluation
(untrusted), each chunk then checked by the kernel. Usage:
`lake env lean --run benchmarks/wasm-kernel-eval/GenChunks.lean N CHUNK` -/
open Silmaril.Wasm.KernelEval Examples

def runN (n : Nat) (c : Config NatMem) : Config NatMem :=
  match run n c with | .running c' => c' | _ => c

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!; let k := args[1]!.toNat!
  let c0 := Config.init fillSort (fillSortLocals n) (NatMem.zeros 65536)
  -- total steps
  let rec count (fuel : Nat) (c : Config NatMem) (acc : Nat) : Nat := match fuel with
    | 0 => acc
    | f + 1 => match step c with | .running c' => count f c' (acc + 1) | _ => acc + 1
  let total := count 10000000 c0 0
  let chunks := total / k
  IO.println "import Silmaril.Wasm.KernelEval.Thms\nimport Silmaril.Wasm.KernelEval.Examples"
  IO.println "import Lean"
  let rfl ← IO.FS.readFile "benchmarks/wasm-kernel-eval/KernelRfl.lean"
  IO.println (rfl.replace "import Lean\n" "")
  IO.println "open Silmaril.Wasm.KernelEval Examples\nset_option maxRecDepth 100000"
  IO.println "set_option profiler true\nset_option profiler.threshold 0"
  IO.println s!"def c0 : Config NatMem := Config.init fillSort (fillSortLocals {n}) (NatMem.zeros 65536)"
  let mut c := c0
  for i in [0:chunks] do
    c := runN k c
    IO.println s!"def c{i+1} : Config NatMem := {(repr c).pretty 1000000}"
    IO.println s!"theorem h{i} : run {k} c{i} = .running c{i+1} := by kernel_rfl"
  let rest := total - chunks * k + 1
  IO.println s!"theorem hlast : (match (run {rest} c{chunks}).top? with | some w => w == {n+1} | none => false) = true := by decide +kernel"
