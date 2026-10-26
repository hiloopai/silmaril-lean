module

/-!
# Functional register files

Registers and their values are parameters. Architectural policies such as the
RISC-V hardwired zero register or x86 overlapping register views belong to the
architecture-specific read/write operations built on top of this storage.
-/

@[expose] public section

namespace Silmaril.Machine

universe u v

/-- Total register storage, independent of an instruction set or word width. -/
abbrev RegisterFile (Register : Type u) (Value : Type v) := Register → Value

namespace RegisterFile

variable {Register : Type u} {Value : Type v} [DecidableEq Register]

/-- Update one register, retaining the values of all other registers. -/
def write (registers : RegisterFile Register Value) (dest : Register) (value : Value) :
    RegisterFile Register Value := fun reg => if reg = dest then value else registers reg

@[simp] theorem write_same (registers : RegisterFile Register Value) (dest : Register)
    (value : Value) : write registers dest value dest = value := by
  simp [write]

@[simp] theorem write_other (registers : RegisterFile Register Value) (dest reg : Register)
    (value : Value) (h : reg ≠ dest) : write registers dest value reg = registers reg := by
  simp [write, h]

@[simp] theorem write_current (registers : RegisterFile Register Value) (dest : Register) :
    write registers dest (registers dest) = registers := by
  funext reg
  by_cases h : reg = dest <;> simp [write, h]

@[simp] theorem write_shadow (registers : RegisterFile Register Value) (dest : Register)
    (first second : Value) :
    write (write registers dest first) dest second = write registers dest second := by
  funext reg
  by_cases h : reg = dest <;> simp [write, h]

/-- Writes to distinct registers commute. -/
theorem write_commute (registers : RegisterFile Register Value) (first second : Register)
    (firstValue secondValue : Value) (h : first ≠ second) :
    write (write registers first firstValue) second secondValue =
      write (write registers second secondValue) first firstValue := by
  funext reg
  by_cases hfirst : reg = first
  · subst reg
    simp [write, h]
  · by_cases hsecond : reg = second <;> simp [write, hfirst, hsecond, Ne.symm h]

end RegisterFile
end Silmaril.Machine
