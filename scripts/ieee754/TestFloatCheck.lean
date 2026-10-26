import Silmaril.Numeric.Ieee754.Std.TestFloat

/-!
Check files of Berkeley TestFloat 3e vectors against `Silmaril.Numeric.Ieee754.Std`.

Usage: `lake env lean --run scripts/ieee754/TestFloatCheck.lean MANIFEST`

Each manifest line is `ISA FUNCTION MODE EXACT PRECISION TININESS FILE`, where ISA
is `x86SSE` (hardware), `sf8086SSE` (SoftFloat's 8086-SSE), `riscv`, `x87` or `x87hw`
(x87 with the hardware reading of unnormals, pseudo-infinities and pseudo-NaNs), MODE a `testfloat_gen` rounding option
(`-rnear_even`, ...), EXACT `exact` or `notexact`, PRECISION `80`, `64` or `32`
(extF80 rounding precision) and TININESS `after` or `before`. For each line it
prints `checked N failed M` and up to five failing vectors; it exits nonzero if
any vector fails or a vector file is empty. `scripts/ieee754/testfloat-check.sh` generates the vectors
and the manifest.
-/

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.Std TestFloat

def runOne (line : String) : IO Bool := do
  let [isaName, fn, modeName, exactName, prec, tinName, file] := (line.splitOn " ").filter (· ≠ "")
    | IO.eprintln s!"bad manifest line: {line}"; return false
  let some isa := isa? isaName | IO.eprintln s!"unknown ISA {isaName}"; return false
  let some mode := mode? modeName | IO.eprintln s!"unknown mode {modeName}"; return false
  let precision := match prec with | "32" => 24 | "64" => 53 | _ => 64
  let tin : TininessDetection := if tinName == "before" then .beforeRounding else .afterRounding
  let reading : X87Reading := if isaName == "x87hw" then .hardware else .softfloat
  let c : Config :=
    { isa := { isa with tin }, fn, mode, exact := exactName == "exact", precision, reading }
  let text ← IO.FS.readFile file
  let (n, bad) := checkAll c text
  IO.println s!"{isaName} {fn} {modeName} {exactName} {prec} {tinName}: checked {n} failed {bad.length}"
  for l in bad.reverse.take 5 do IO.println s!"  FAIL {l}"
  if n == 0 then IO.println s!"  EMPTY {file}"
  (← IO.getStdout).flush
  return bad.isEmpty && n > 0

def main (args : List String) : IO UInt32 := do
  let [manifest] := args | IO.eprintln "usage: MANIFEST"; return 2
  let lines := (← IO.FS.readFile manifest).splitOn "\n" |>.filter (fun l => !l.all Char.isWhitespace)
  let mut ok := true
  for l in lines do
    ok := (← runOne l) && ok
  return if ok then 0 else 1
