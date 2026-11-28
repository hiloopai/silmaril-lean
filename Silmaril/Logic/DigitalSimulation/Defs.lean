module

/-!
# IEEE scalar digital simulation

The Verilog operations use the scalar bitwise tables of IEEE 1800-2017
and the equal-strength case of ordinary wire/tri net resolution.
The VHDL operations use the IEEE 1076-2019 `STD_LOGIC_1164` package.
See `docs/projects/ieee-digital-simulation.md` for the source tables and scope.
-/

namespace Silmaril.Logic.DigitalSimulation

/-- Verilog/SystemVerilog's four scalar values. `x` is unknown and `z` is high impedance. -/
public inductive VerilogBit where
  | zero | one | x | z
  deriving DecidableEq, Repr

/-- VHDL's `STD_ULOGIC` in declaration order. `u` is uninitialized, `x` is forcing
unknown, `z` is high impedance, `w` is weak unknown, `l` and `h` are weak zero and one,
and `dash` is don't-care. `zero` and `one` are forcing values. -/
public inductive StdULogic where
  | u | x | zero | one | z | w | l | h | dash
  deriving DecidableEq, Repr

@[expose] public section

namespace VerilogBit

/-- Scalar bitwise complement (`~`). -/
def not : VerilogBit → VerilogBit
  | .zero => .one
  | .one => .zero
  | .x | .z => .x

/-- Scalar bitwise AND (`&`). -/
def and : VerilogBit → VerilogBit → VerilogBit
  | .zero, _ | _, .zero => .zero
  | .one, .one => .one
  | _, _ => .x

/-- Scalar bitwise OR (`|`). -/
def or : VerilogBit → VerilogBit → VerilogBit
  | .one, _ | _, .one => .one
  | .zero, .zero => .zero
  | _, _ => .x

/-- Scalar bitwise XOR (`^`). -/
def xor : VerilogBit → VerilogBit → VerilogBit
  | .zero, .zero | .one, .one => .zero
  | .zero, .one | .one, .zero => .one
  | _, _ => .x

/-- Pair resolution on an ordinary wire/tri with a shared drive strength.
High impedance contributes no drive. -/
def resolvePair : VerilogBit → VerilogBit → VerilogBit
  | .z, b => b
  | a, .z => a
  | .zero, .zero => .zero
  | .one, .one => .one
  | _, _ => .x

/-- Resolve the drivers on an ordinary scalar wire/tri with a shared drive strength.
An undriven net resolves to high impedance. -/
def resolve (drivers : List VerilogBit) : VerilogBit :=
  drivers.foldl resolvePair .z

/-- Embed a known bit. -/
def ofBool : Bool → VerilogBit
  | false => .zero
  | true => .one

/-- Observe the known bit, if any. Both `x` and `z` are unobserved. -/
def toBool? : VerilogBit → Option Bool
  | .zero => some false
  | .one => some true
  | .x | .z => none

/-- Use `x` for an absent observation. -/
def ofOptionBool : Option Bool → VerilogBit
  | some b => ofBool b
  | none => .x

/-- Embed a four-state value in the forcing/high-impedance fragment of `STD_ULOGIC`. -/
def toStdULogic : VerilogBit → StdULogic
  | .zero => .zero
  | .one => .one
  | .x => .x
  | .z => .z

end VerilogBit

namespace StdULogic

/-- IEEE `not_table`. The result lies in the `UX01` subset. -/
def not : StdULogic → StdULogic
  | .u => .u
  | .zero | .l => .one
  | .one | .h => .zero
  | _ => .x

/-- IEEE `and_table`. A known low input controls the result, including weak low. -/
def and : StdULogic → StdULogic → StdULogic
  | .zero, _ | .l, _ | _, .zero | _, .l => .zero
  | .u, _ | _, .u => .u
  | .one, .one | .one, .h | .h, .one | .h, .h => .one
  | _, _ => .x

/-- IEEE `or_table`. A known high input controls the result, including weak high. -/
def or : StdULogic → StdULogic → StdULogic
  | .one, _ | .h, _ | _, .one | _, .h => .one
  | .u, _ | _, .u => .u
  | .zero, .zero | .zero, .l | .l, .zero | .l, .l => .zero
  | _, _ => .x

/-- IEEE `xor_table`. An uninitialized input propagates even against `x`. -/
def xor : StdULogic → StdULogic → StdULogic
  | .u, _ | _, .u => .u
  | .zero, .zero | .zero, .l | .l, .zero | .l, .l
  | .one, .one | .one, .h | .h, .one | .h, .h => .zero
  | .zero, .one | .zero, .h | .l, .one | .l, .h
  | .one, .zero | .one, .l | .h, .zero | .h, .l => .one
  | _, _ => .x

/-- IEEE `resolution_table`. Clause order follows resolution precedence. In particular,
a don't-care driver becomes `x` against `z`, while `u` dominates every value. -/
def resolvePair : StdULogic → StdULogic → StdULogic
  | .u, _ | _, .u => .u
  | .dash, _ | _, .dash | .x, _ | _, .x => .x
  | .z, b => b
  | a, .z => a
  | .zero, .one | .one, .zero => .x
  | .zero, _ | _, .zero => .zero
  | .one, _ | _, .one => .one
  | .l, .l => .l
  | .h, .h => .h
  | _, _ => .w

/-- IEEE `resolved`, in array traversal order. A single driver is returned unchanged,
including `dash`. The table fold starts at `z`, which also handles the empty list. -/
def resolve : List StdULogic → StdULogic
  | [driver] => driver
  | drivers => drivers.foldl resolvePair .z

/-- Observe low and high even at weak strength. All other values are unobserved. -/
def toBool? : StdULogic → Option Bool
  | .zero | .l => some false
  | .one | .h => some true
  | _ => none

/-- Embed a known bit at forcing strength. -/
def ofBool (b : Bool) : StdULogic :=
  (VerilogBit.ofBool b).toStdULogic

/-- Use forcing unknown for an absent observation. -/
def ofOptionBool (b : Option Bool) : StdULogic :=
  (VerilogBit.ofOptionBool b).toStdULogic

/-- Project to four states, forgetting drive strength and the reasons for an unknown
value. The projection retains high impedance. -/
def toVerilog : StdULogic → VerilogBit
  | .zero | .l => .zero
  | .one | .h => .one
  | .z => .z
  | .u | .x | .w | .dash => .x

end StdULogic

end
end Silmaril.Logic.DigitalSimulation
