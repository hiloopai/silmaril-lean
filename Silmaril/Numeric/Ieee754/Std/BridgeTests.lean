module

public import Silmaril.Numeric.Ieee754.Std.Bridge
public import Silmaril.Numeric.Ieee754.Std.Vectors
public meta import Silmaril.Numeric.Ieee754.Std.Bridge
public meta import Silmaril.Numeric.Ieee754.Std.Vectors

/-!
# Build-time differential checks of the bridges

On the operands of the vector samples of `Std.Vectors` (the expected results are
ignored), `Std` is compared with the older implementations, bit for bit and flag
for flag (`Bridge.agreeProfile`), and under round to nearest, ties to even, with
Lean core's `Float32.Model`/`Float.Model` through the `F32`/`F64` wrappers
(`Bridge.agreeCore`; NaN results only need to be NaNs there):

* x86 lines (`sf8086SSE`, `x86SSE`): `Numeric.Float.Profile.x86SSE` with the x86
  hardware FMA rule against `Isa.x86SSE`;
* RISC-V lines: `Profile.riscvFD` with `riscvFmaNaNRule` against `Isa.riscv`.

`#guard` evaluates with the compiler. The full level-1 runs are made by
`scripts/ieee754/BridgeCheck.lean`.
-/

namespace Silmaril.Numeric.Ieee754.Std.BridgeTests

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.Std TestFloat Bridge
open Silmaril.Numeric.Float

/-- The bridge disagreements on a vector text, and the number of lines compared. -/
def bridgeBlocks (text : String) : List String × ℕ := Id.run do
  let mut bad : List String := []
  let mut n := 0
  let mut cfg : Option (String × String × RoundingMode × Bool) := none
  for line in text.splitOn "\n" do
    if line.all Char.isWhitespace then continue
    if line.startsWith "#" then
      let w := ((line.drop 1).toString.splitOn " ").filter (· ≠ "")
      cfg := match w with
        | [isaName, fn, modeName, exactName, _, "after"] => do
          let mode ← mode? modeName
          pure (isaName, fn, mode, exactName == "exact")
        | _ => none
      continue
    let some (isaName, fn, mode, exact) := cfg | continue
    if isaName == "x87" || isaName == "x87hw" then continue
    let (p, rule, I) := if isaName == "riscv" then (Profile.riscvFD, riscvFmaNaNRule, Isa.riscv)
      else (Profile.x86SSE {}, x86HardwareFmaNaNRule, Isa.x86SSE)
    match agreeProfile p rule I fn mode exact line with
    | some false => bad := s!"profile {isaName} {fn}: {line}" :: bad; n := n + 1
    | some true => n := n + 1
    | none => pure ()
    if mode == .nearestTiesToEven && isaName != "riscv" then
      match agreeCore fn line with
      | some false => bad := s!"core {fn}: {line}" :: bad; n := n + 1
      | some true => n := n + 1
      | none => pure ()
  return (bad, n)

#guard (bridgeBlocks Vectors.softfloat8086SSE).1 == []
#guard (bridgeBlocks Vectors.softfloatRiscv).1 == []
#guard (bridgeBlocks Vectors.hardwareX86).1 == []
-- the checks are not vacuous
#guard 1000 ≤ (bridgeBlocks Vectors.softfloat8086SSE).2
#guard 1000 ≤ (bridgeBlocks Vectors.softfloatRiscv).2

end Silmaril.Numeric.Ieee754.Std.BridgeTests
