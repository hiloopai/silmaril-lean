module

public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.C6.Defs
@[expose] public section

/-!
# The Ail → Mir validator for C6

`checkC6` is `checkC5` (`Validator.lean`) with `C6.run` (`C6.lean`: compound literals,
statement expressions, members of structure values) as the source: it accepts a program when
`C6.run` and ccomp's Mir linked with its C library (`ccompMirRt`) both end with the same
observation. Compound-literal objects and statement-expression locals are internal to both
sides; only the observation (output and exit) is compared, so a program that prints the
address of a compound literal is accepted only when ccomp's and C6's agree. `C6.beh_of_done`
supplies the local semantic lemma to the generic soundness proof `checkRunWith_sound`; target
`ccomp_rt_tv_sound_c6` (`TargetsC6.lean`).
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Compile.Category

/-- The fuel `checkC6` runs C6 with (`csem run`'s). -/
def tvC6Fuel : Nat := 100000000

/-- `checkC6` with explicit fuels: C6 and ccomp's Mir linked with its C library both end,
with the same observation. -/
def checkC6With (lirFuel c6Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkRunWith ccompMirRt C6.run lirFuel c6Fuel p

/-- The Ail → Mir validator for C6, with ccomp's C library: run and compare. -/
def checkC6 (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool := checkC6With tvLirFuel tvC6Fuel p

/-- Acceptance at any fuels gives ccomp's Mir linked with its C library, valid at `cAM`
for C6 and with a behaviour. -/
theorem checkC6With_sound {lirFuel c6Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkC6With lirFuel c6Fuel p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C6.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkRunWith_sound (run := C6.run) (front := ccompMirRt) (lirFuel := lirFuel) (fuel := c6Fuel)
    C6.beh_of_done h

theorem checkC6_sound {p : Silmaril.Cerberus.Ail.TypedProgram} (h : checkC6 p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C6.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkC6With_sound h

/-- Why `checkC6With` rejects a program (`csem why6`; `none` when it accepts). -/
def checkC6Why (lirFuel c6Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkRunWhy ccompMirRt ccompUnitsRt C6.run "c6" lirFuel c6Fuel p

end Silmaril.Compile.C.Sem
