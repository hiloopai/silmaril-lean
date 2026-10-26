import Silmaril.Numeric.Ieee754.Std.Bridge

/-!
Differential check of `Silmaril.Numeric.Ieee754.Std` against `Numeric.Float`
profiles and Lean core's `Float.Model` on the operands of TestFloat vector files.

Usage: `lake env lean --run scripts/ieee754/BridgeCheck.lean MANIFEST`

The manifest is the one written by `scripts/ieee754/testfloat-check.sh`. Lines for
`sf8086SSE`/`x86SSE` compare `Profile.x86SSE` (with the x86 hardware FMA rule)
with `Isa.x86SSE`, and, under round to nearest even, Lean core's model with
`Isa.x86SSE`; lines for `riscv` compare `Profile.riscvFD` with `Isa.riscv`.
Functions a bridge does not cover are skipped.
-/

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.Std TestFloat Bridge
open Silmaril.Numeric.Float

def runOne (line : String) : IO Bool := do
  let [isaName, fn, modeName, exactName, _prec, tinName, file] := (line.splitOn " ").filter (· ≠ "")
    | return true
  if tinName != "after" then return true
  let some mode := mode? modeName | return true
  let exact := exactName == "exact"
  let (p, rule, I) := if isaName == "riscv" then (Profile.riscvFD, riscvFmaNaNRule, Isa.riscv)
    else (Profile.x86SSE {}, x86HardwareFmaNaNRule, Isa.x86SSE)
  if isaName == "x87" || isaName == "x87hw" then return true
  let lines := (← IO.FS.readFile file).splitOn "\n" |>.filter (fun l => !l.all Char.isWhitespace)
  let mut n := 0
  let mut bad : List String := []
  let mut nc := 0
  let mut badc : List String := []
  for l in lines do
    match agreeProfile p rule I fn mode exact l with
    | some true => n := n + 1
    | some false => n := n + 1; bad := l :: bad
    | none => pure ()
    if mode == .nearestTiesToEven && isaName != "riscv" then
      match agreeCore fn l with
      | some true => nc := nc + 1
      | some false => nc := nc + 1; badc := l :: badc
      | none => pure ()
  if n > 0 then
    IO.println s!"profile {isaName} {fn} {modeName} {exactName}: compared {n} disagreed {bad.length}"
    for l in bad.reverse.take 3 do IO.println s!"  DIFF {l}"
  if nc > 0 then
    IO.println s!"core {fn} {modeName}: compared {nc} disagreed {badc.length}"
    for l in badc.reverse.take 3 do IO.println s!"  DIFF {l}"
  (← IO.getStdout).flush
  return bad.isEmpty && badc.isEmpty

def main (args : List String) : IO UInt32 := do
  let [manifest] := args | IO.eprintln "usage: MANIFEST"; return 2
  let lines := (← IO.FS.readFile manifest).splitOn "\n" |>.filter (fun l => !l.all Char.isWhitespace)
  let mut ok := true
  for l in lines do
    ok := (← runOne l) && ok
  return if ok then 0 else 1
