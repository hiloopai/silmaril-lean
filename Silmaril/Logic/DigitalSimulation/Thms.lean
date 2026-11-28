module

public import Silmaril.Logic.DigitalSimulation.Defs
import Silmaril.Proofs.Logic.DigitalSimulation.Resolution

public section

namespace Silmaril.Logic.DigitalSimulation

namespace VerilogBit

theorem toBool?_ofOptionBool (value : Option Bool) : (ofOptionBool value).toBool? = value := by
  cases value with
  | none => rfl
  | some b => cases b <;> rfl

theorem ofBool_not (a : Bool) : ofBool (!a) = (ofBool a).not := by cases a <;> rfl

theorem ofBool_and (a b : Bool) : ofBool (a && b) = (ofBool a).and (ofBool b) := by
  cases a <;> cases b <;> rfl

theorem ofBool_or (a b : Bool) : ofBool (a || b) = (ofBool a).or (ofBool b) := by
  cases a <;> cases b <;> rfl

theorem ofBool_xor (a b : Bool) : ofBool (Bool.xor a b) = (ofBool a).xor (ofBool b) := by
  cases a <;> cases b <;> rfl

theorem toStdULogic_toVerilog (a : VerilogBit) : a.toStdULogic.toVerilog = a := by
  cases a <;> rfl

theorem toStdULogic_not (a : VerilogBit) : a.not.toStdULogic = a.toStdULogic.not := by
  cases a <;> rfl

theorem toStdULogic_and (a b : VerilogBit) :
    (a.and b).toStdULogic = a.toStdULogic.and b.toStdULogic := by
  cases a <;> cases b <;> rfl

theorem toStdULogic_or (a b : VerilogBit) :
    (a.or b).toStdULogic = a.toStdULogic.or b.toStdULogic := by
  cases a <;> cases b <;> rfl

theorem toStdULogic_xor (a b : VerilogBit) :
    (a.xor b).toStdULogic = a.toStdULogic.xor b.toStdULogic := by
  cases a <;> cases b <;> rfl

theorem toStdULogic_resolvePair (a b : VerilogBit) :
    (a.resolvePair b).toStdULogic = a.toStdULogic.resolvePair b.toStdULogic :=
  Proofs.toStdULogic_resolvePair a b

theorem toStdULogic_resolve (drivers : List VerilogBit) :
    (resolve drivers).toStdULogic = StdULogic.resolve (drivers.map toStdULogic) :=
  Proofs.toStdULogic_resolve drivers

theorem resolvePair_comm (a b : VerilogBit) : a.resolvePair b = b.resolvePair a := by
  cases a <;> cases b <;> rfl

theorem resolvePair_assoc (a b c : VerilogBit) :
    (a.resolvePair b).resolvePair c = a.resolvePair (b.resolvePair c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem resolvePair_idem (a : VerilogBit) : a.resolvePair a = a := by cases a <;> rfl

@[simp] theorem resolve_nil : resolve [] = .z := rfl

@[simp] theorem resolve_singleton (a : VerilogBit) : resolve [a] = a := rfl

/-- Scalar gates normalize high impedance, violating a lattice meet's idempotence law. -/
theorem and_z_z_ne_z : and .z .z ≠ .z := by decide

end VerilogBit

namespace StdULogic

theorem toVerilog_not (a : StdULogic) : a.not.toVerilog = a.toVerilog.not := by
  cases a <;> rfl

theorem toVerilog_and (a b : StdULogic) : (a.and b).toVerilog = a.toVerilog.and b.toVerilog := by
  cases a <;> cases b <;> rfl

theorem toVerilog_or (a b : StdULogic) : (a.or b).toVerilog = a.toVerilog.or b.toVerilog := by
  cases a <;> cases b <;> rfl

theorem toVerilog_xor (a b : StdULogic) : (a.xor b).toVerilog = a.toVerilog.xor b.toVerilog := by
  cases a <;> cases b <;> rfl

theorem toBool?_eq_toVerilog (a : StdULogic) : a.toBool? = a.toVerilog.toBool? := by
  cases a <;> rfl

theorem toBool?_ofOptionBool (value : Option Bool) : (ofOptionBool value).toBool? = value := by
  cases value with
  | none => rfl
  | some b => cases b <;> rfl

theorem ofBool_not (a : Bool) : ofBool (!a) = (ofBool a).not := by cases a <;> rfl

theorem ofBool_and (a b : Bool) : ofBool (a && b) = (ofBool a).and (ofBool b) := by
  cases a <;> cases b <;> rfl

theorem ofBool_or (a b : Bool) : ofBool (a || b) = (ofBool a).or (ofBool b) := by
  cases a <;> cases b <;> rfl

theorem ofBool_xor (a b : Bool) : ofBool (Bool.xor a b) = (ofBool a).xor (ofBool b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem resolve_nil : resolve [] = .z := rfl

@[simp] theorem resolve_singleton (a : StdULogic) : resolve [a] = a := rfl

theorem resolve_two (a b : StdULogic) : resolve [a, b] = a.resolvePair b := by
  cases a <;> cases b <;> rfl

/-- A forcing zero can override weak high. After dropping strength, the drivers conflict. -/
theorem toVerilog_resolvePair_zero_h_ne :
    (resolvePair .zero .h).toVerilog ≠
      VerilogBit.resolvePair (toVerilog .zero) (toVerilog .h) := by decide

/-- The same strength loss matters when projecting a list of drivers before resolution. -/
theorem toVerilog_resolve_zero_h_ne :
    (resolve [.zero, .h]).toVerilog ≠ VerilogBit.resolve ([.zero, .h].map toVerilog) := by decide

/-- Scalar gates normalize high impedance, violating a lattice meet's idempotence law. -/
theorem and_z_z_ne_z : and .z .z ≠ .z := by decide

/-- Pair resolution violates idempotence on don't-care. -/
theorem resolvePair_dash_dash_ne_dash : resolvePair .dash .dash ≠ .dash := by decide

end StdULogic
end Silmaril.Logic.DigitalSimulation
