module

import Silmaril.Logic.DigitalSimulation.Thms

/-!
Kernel-checked scalar table regressions and an example of reading a resolved bus.
The rows are ordered as in the published tables cited in
`docs/projects/ieee-digital-simulation.md`.
-/

namespace Silmaril.Logic.DigitalSimulation

private def verilogValues : List VerilogBit := [.zero, .one, .x, .z]

private def verilogChar : VerilogBit → Char
  | .zero => '0' | .one => '1' | .x => 'X' | .z => 'Z'

private def vhdlValues : List StdULogic := [.u, .x, .zero, .one, .z, .w, .l, .h, .dash]

private def vhdlChar : StdULogic → Char
  | .u => 'U' | .x => 'X' | .zero => '0' | .one => '1' | .z => 'Z'
  | .w => 'W' | .l => 'L' | .h => 'H' | .dash => '-'

private def rows {α : Type} (values : List α) (encode : α → Char) (op : α → α → α) :
    List String :=
  values.map fun a => String.ofList (values.map fun b => encode (op a b))

example : String.ofList (verilogValues.map (verilogChar ∘ VerilogBit.not)) = "10XX" := by decide
example : rows verilogValues verilogChar VerilogBit.and = ["0000", "01XX", "0XXX", "0XXX"] := by
  decide
example : rows verilogValues verilogChar VerilogBit.or = ["01XX", "1111", "X1XX", "X1XX"] := by
  decide
example : rows verilogValues verilogChar VerilogBit.xor = ["01XX", "10XX", "XXXX", "XXXX"] := by
  decide
example :
    rows verilogValues verilogChar VerilogBit.resolvePair = ["0XX0", "X1X1", "XXXX", "01XZ"] := by
  decide

example : String.ofList (vhdlValues.map (vhdlChar ∘ StdULogic.not)) = "UX10XX10X" := by decide
example :
    rows vhdlValues vhdlChar StdULogic.and =
      ["UU0UUU0UU", "UX0XXX0XX", "000000000", "UX01XX01X", "UX0XXX0XX",
       "UX0XXX0XX", "000000000", "UX01XX01X", "UX0XXX0XX"] := by decide
example :
    rows vhdlValues vhdlChar StdULogic.or =
      ["UUU1UUU1U", "UXX1XXX1X", "UX01XX01X", "111111111", "UXX1XXX1X",
       "UXX1XXX1X", "UX01XX01X", "111111111", "UXX1XXX1X"] := by decide
example :
    rows vhdlValues vhdlChar StdULogic.xor =
      ["UUUUUUUUU", "UXXXXXXXX", "UX01XX01X", "UX10XX10X", "UXXXXXXXX",
       "UXXXXXXXX", "UX01XX01X", "UX10XX10X", "UXXXXXXXX"] := by decide
example :
    rows vhdlValues vhdlChar StdULogic.resolvePair =
      ["UUUUUUUUU", "UXXXXXXXX", "UX0X0000X", "UXX11111X", "UX01ZWLHX",
       "UX01WWWWX", "UX01LWLWX", "UX01HWWHX", "UXXXXXXXX"] := by decide

example : VerilogBit.resolve [] = .z := by decide
example : VerilogBit.resolve [.z, .zero, .one] = .x := by decide
example : StdULogic.resolve [] = .z := by decide
example : vhdlValues.map (fun a => StdULogic.resolve [a]) = vhdlValues := by decide
example :
    rows vhdlValues vhdlChar (fun a b => StdULogic.resolve [a, b]) =
      rows vhdlValues vhdlChar StdULogic.resolvePair := by decide
example : StdULogic.resolve [.z, .l, .h] = .w := by decide
example : StdULogic.resolve [.dash, .z] = .x := by decide

-- A pull-up shares the bus with an output. Resolve the drivers before applying
-- the receiver's enable and observing a Boolean level.
private def readPulledBus (driver enable : StdULogic) : Option Bool :=
  ((StdULogic.resolve [driver, .h]).and enable).toBool?

example : readPulledBus .z .one = some true := by decide
example : readPulledBus .zero .one = some false := by decide
example : readPulledBus .dash .one = none := by decide
example : readPulledBus .dash .zero = some false := by decide
example : VerilogBit.resolve ([StdULogic.zero, .h].map StdULogic.toVerilog) = .x := by decide

-- Observation loses high impedance, which is significant during resolution.
example : VerilogBit.toBool? .z = VerilogBit.toBool? .x := by decide
example : (VerilogBit.resolvePair .z .one).toBool? ≠ (VerilogBit.resolvePair .x .one).toBool? := by
  decide
-- The projection forgets weak strength even when followed by its section.
example : StdULogic.toVerilog .h = StdULogic.toVerilog .one := by decide
example : (StdULogic.toVerilog .h).toStdULogic ≠ .h := by decide

end Silmaril.Logic.DigitalSimulation
