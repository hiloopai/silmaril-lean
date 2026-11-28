module

public import Silmaril.Logic.DigitalSimulation.Defs

namespace Silmaril.Logic.DigitalSimulation.Proofs

public theorem toStdULogic_resolvePair (a b : VerilogBit) :
    (a.resolvePair b).toStdULogic = a.toStdULogic.resolvePair b.toStdULogic := by
  cases a <;> cases b <;> rfl

private theorem toStdULogic_foldl (a : VerilogBit) (drivers : List VerilogBit) :
    (drivers.foldl VerilogBit.resolvePair a).toStdULogic =
      (drivers.map VerilogBit.toStdULogic).foldl StdULogic.resolvePair a.toStdULogic := by
  induction drivers generalizing a with
  | nil => rfl
  | cons driver drivers ih =>
    simp only [List.map_cons, List.foldl_cons, ← toStdULogic_resolvePair, ih]

public theorem toStdULogic_resolve (drivers : List VerilogBit) :
    (VerilogBit.resolve drivers).toStdULogic =
      StdULogic.resolve (drivers.map VerilogBit.toStdULogic) := by
  cases drivers with
  | nil => rfl
  | cons driver rest =>
    cases rest with
    | nil => cases driver <;> rfl
    | cons next rest => exact toStdULogic_foldl .z (driver :: next :: rest)

end Silmaril.Logic.DigitalSimulation.Proofs
