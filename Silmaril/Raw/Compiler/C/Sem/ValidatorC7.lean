module

public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.C7.Defs
@[expose] public section

/-!
# The Ail → Mir validator for C7

`checkC7` is `checkC6` (`ValidatorC6.lean`) with `C7.run` (`C7.lean`: stdio streams on the
standard output and error, floating `printf` conversions, `va_list` arguments of the printf
family) as the source: it accepts a program when `C7.run` and ccomp's Mir linked with its C
library (`ccompMirRt`) both end with the same observation. The printf family, the stream
functions and the decimal formatting of floating values are C code of ccomp's C library, compiled
and linked with the program, so they are inside what is validated: a program is accepted only
when that code prints exactly what C7's formatter does. A completed run of `C7.run` is a
behaviour of C7 by the definition of `C7.beh`, the local lemma the generic soundness proof
`checkRunWith_sound` needs; target `ccomp_rt_tv_sound_c7` (`TargetsC7.lean`).
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Compile.Category

/-- The fuel `checkC7` runs C7 with (`csem run`'s). -/
def tvC7Fuel : Nat := 100000000

/-- `checkC7` with explicit fuels: C7 and ccomp's Mir linked with its C library both end,
with the same observation. -/
def checkC7With (lirFuel c7Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkRunWith ccompMirRt C7.run lirFuel c7Fuel p

/-- The Ail → Mir validator for C7, with ccomp's C library: run and compare. -/
def checkC7 (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool := checkC7With tvLirFuel tvC7Fuel p

/-- Acceptance at any fuels gives ccomp's Mir linked with its C library, valid at `cAM`
for C7 and with a behaviour. -/
theorem checkC7With_sound {lirFuel c7Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkC7With lirFuel c7Fuel p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C7.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkRunWith_sound (run := C7.run) (front := ccompMirRt) (lirFuel := lirFuel) (fuel := c7Fuel)
    (fun h => Or.inl ⟨_, h⟩) h

theorem checkC7_sound {p : Silmaril.Cerberus.Ail.TypedProgram} (h : checkC7 p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C7.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkC7With_sound h

/-- Why `checkC7With` rejects a program (`csem why7`; `none` when it accepts). -/
def checkC7Why (lirFuel c7Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkRunWhy ccompMirRt ccompUnitsRt C7.run "c7" lirFuel c7Fuel p

end Silmaril.Compile.C.Sem
