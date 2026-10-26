module

public import Silmaril.Process.LPS.Syscall

/-!
# LPS in Lean: syscall-table arms and dispatch

Translation of LPS `Sys/Dispatch.v` (upstream commit `f1006fe8`). A table is a list of
arms keyed by syscall number. The LPS table (`specTable`) uses the asm-generic (riscv64)
numbers; a native x86-64 table uses `arch/x86/entry/syscalls/syscall_64.tbl` numbers. Each
family module (`Silmaril.Process.LPS.Sys.*`) exports its translated arms as `SpecArm` lists
so that the tables are assembled without the family modules depending on one another.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- Whether an arm's specification has been translated. -/
inductive ArmStatus where
  | translated
  | pending
  deriving DecidableEq, Repr

/-- LPS `Sys/Dispatch.v:34` `SpecArm`, with the Linux name and the translation status. -/
structure SpecArm where
  no : Nat
  name : String
  status : ArmStatus
  spec : Sys SyscallEffect

/-- LPS `Sys/Dispatch.v:41` `lookup_arm`. -/
def lookupArm : List SpecArm → Nat → Option SpecArm
  | [], _ => none
  | a :: r, n => if a.no = n then some a else lookupArm r n

/-- LPS `Sys/Dispatch.v:53` `dispatch`: an unknown number is `unmodeled`. -/
def dispatch (t : List SpecArm) : Sys SyscallEffect := fun i m o =>
  match lookupArm t i.sysno.toNat with
  | some a => a.spec i m o
  | none => Sys.unmodeled i m o

/-- LPS `Sys/Dispatch.v:61` `arm_numbers`. -/
def armNumbers (t : List SpecArm) : List Nat := t.map (·.no)

/-- A translated arm. As in LPS (`mkSpecArm n (fun i => spec (in_arg i 0) … i)`), the
specification may read its arguments from the input. -/
def arm (no : Nat) (name : String) (spec : SyscallInput → Sys SyscallEffect) : SpecArm :=
  ⟨no, name, .translated, fun i => spec i i⟩

/-- An arm of the LPS table whose specification is not translated yet: `unmodeled`. -/
def pendingArm (no : Nat) (name : String) : SpecArm := ⟨no, name, .pending, Sys.unmodeled⟩

end Silmaril.Process.LPS
