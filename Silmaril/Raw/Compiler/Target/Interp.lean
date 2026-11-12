module

public import Silmaril.Compiler.Mir.Interp.Defs
public import Silmaril.Compiler.Target.Runtime.Defs
/-! # Running a linked program in the reference interpreter

`Target.interp` runs a linked program (`Mir.Linked`, with the runtime unit first) in
`Mir.Interp` from `__ccomp_start`, over the memory the startup code builds (`memSize`
bytes, the image at `dataBase`, the first page inaccessible), and reads back what the
process of `tools/ccomp/runtime/crt0-x86_64.S` would show: the output buffer as
stdout, and the exit status (`main`'s result, the status of `exit`) or the signal
(`SIGABRT` after `abort`, `SIGILL` for another trap or a too deep recursion, `SIGSEGV`
on the NULL page). A stuck run (undefined behaviour in Lir) has no process
counterpart: it is reported with its reason and place. `ccomp --interp` is this function; comparing it with the
x86-64 executable is a differential test of the backend and the startup code, and its
stuck reasons localise miscompilations in the front end (`docs/projects/cerberus.md`).

## Intended theorem

For a link `l` whose run returns or traps, the stdout and the exit status of the
process built from `Target.compile .x86_64 l` by the startup code are those of
`interp l` (from `X86.Backend.compile_refines`, `Lir.Alloc.spill_refines` and the
loader statement of `Silmaril.Compile.Target.Backends`).
-/

@[expose] public section

namespace Silmaril.Compile.Target

open Silmaril.Machine
open Silmaril.Compile.Mir

/-- How the process ends. -/
inductive Exit where
  | status (code : Nat)
  | signal (sig : Nat)
  /-- Undefined behaviour of the Lir program. -/
  | stuck (why : String)
  | outOfFuel
  deriving Repr, Inhabited

/-- What the process shows: its standard output and its end. -/
structure Observation where
  stdout : ByteArray
  exit : Exit
  /-- Where a fault, a stack exhaustion or the end of the fuel happened. -/
  note : Option String := none

/-- The output buffer of a final memory (`flush` of the startup code). -/
def outputOf (ctl : Nat) (m : Interp.Mem) : ByteArray :=
  let word (i : Nat) := (m.readLE (ctl + 8 * i) 8).toNat
  m.slice (word 6) (min (word 3) (word 7))

/-- The observation of an interpreter outcome, given the address of the control block. -/
def observe (names : Array String) (ctl : Nat) (o : Interp.Outcome) : Observation :=
  let m := o.mem
  let exit : Exit := match o with
    | .returned vs _ => .status ((vs.headD 0).toNat % 256)
    | .trapped _ => match (m.readLE (ctl + 40) 8).toNat with
      | 1 => .status ((m.readLE (ctl + 32) 4).toNat % 256)
      | 2 => .signal 6
      | _ => .signal 4
    | .fault .. => .signal 11
    | .exhausted .. => .signal 4
    | .stuck why pt _ => .stuck s!"{why} at {pt.describe names}"
    | .outOfFuel _ _ => .outOfFuel
  let note := match o with
    | .fault a pt _ => some s!"access to address {a} in the NULL page at {pt.describe names}"
    | .exhausted pt _ => some s!"machine stack exhausted at {pt.describe names}"
    | .outOfFuel pt _ => some s!"out of fuel at {pt.describe names}"
    | _ => none
  ⟨outputOf ctl m, exit, note⟩

/-- Run a linked program from `__ccomp_start` for at most `fuel` steps. -/
def interp (l : Linked) (fuel : Nat) : Except String (Observation × Interp.Outcome) := do
  let some entry := l.funcs[startSymbol]? | throw s!"no {startSymbol}"
  let some ctl := l.data[ctlSymbol]? | throw s!"no {ctlSymbol}"
  let code := Interp.load l.prog
  let m ← Interp.start code entry [] (Interp.Mem.ofImage memSize l.dataBase l.image)
  let o := Interp.run code { guard := dataBase } fuel m
  return (observe (Interp.funcNames l) ctl o, o)

end Silmaril.Compile.Target
