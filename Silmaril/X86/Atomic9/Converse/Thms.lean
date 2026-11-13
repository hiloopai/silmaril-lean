module

public import Silmaril.X86.Atomic9.Thms
public import Silmaril.X86.MemEvent.Defs
import Silmaril.Proofs.X86.Atomic9.Converse

/-!
# `Atomic9`: the converse of the listing law

PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Atomic9/Converse.lean`).

* `exec_of_step_base`, `exec_of_step_new`: if the program counter of a loaded image is at a
  listed `Ext` base form (`.open9 (.ext8 (.base b))`) or a listed atomic form (`.new j`) of
  length `l`, and `Atomic9.step` succeeds, then the executor of that form returned `.ok` with
  the step's core and memory. The listing law `step_of_listed` is the other direction; together
  they say a listed form steps exactly when it executes.

* `fetch_of_listed_base`, `fetch_of_listed_new`: at such a listed form,
  `MemEvent.atomic9Fetch` (the fetch of the TSO pool's `atomic9Ev`) returns the form and its
  length.

Not covered: the `Ext8` and `Ext9` new forms (`.open9 (.ext8 (.new _))`, `.open9 (.new _)`),
which no current front end accepts.
-/

@[expose] public section

namespace Silmaril.X86.Atomic9

open Silmaril.X86 (MState Word Byte)
open Silmaril.X86.Ext (Loaded)

/-- **A listed base form that steps executed**: its executor returned the step's result. -/
theorem exec_of_step_base {m m' : MState} {base : Word} {code : List Byte} {o l : Nat}
    {b : Silmaril.X86.Ext.Instr} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (.open9 (.ext8 (.base b)), l))
    (hs : step m = some m') :
    exec (.open9 (.ext8 (.base b))) m.core m.memory l = .ok m'.core m'.memory :=
  Silmaril.Proofs.X86.Atomic9.exec_of_step_base hl hrip hfit hdec hs

/-- **A listed atomic form that steps executed**: its executor returned the step's result. -/
theorem exec_of_step_new {m m' : MState} {base : Word} {code : List Byte} {o l : Nat}
    {j : New} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (.new j, l))
    (hs : step m = some m') : exec (.new j) m.core m.memory l = .ok m'.core m'.memory :=
  Silmaril.Proofs.X86.Atomic9.exec_of_step_new hl hrip hfit hdec hs

/-- **The fetch of a listed base form**. -/
theorem fetch_of_listed_base {mem : Silmaril.Process.Memory} {base pc : Word} {code : List Byte}
    {o l : Nat} {b : Silmaril.X86.Ext.Instr} (hl : Loaded mem base code)
    (hrip : pc = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (.open9 (.ext8 (.base b)), l)) :
    MemEvent.atomic9Fetch mem pc.toNat = some (.open9 (.ext8 (.base b)), l) :=
  Silmaril.Proofs.X86.Atomic9.fetch_of_listed_base hl hrip hfit hdec

/-- **The fetch of a listed atomic form**. -/
theorem fetch_of_listed_new {mem : Silmaril.Process.Memory} {base pc : Word} {code : List Byte}
    {o l : Nat} {j : New} (hl : Loaded mem base code) (hrip : pc = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : decode ((code.drop o).take l) = some (.new j, l)) :
    MemEvent.atomic9Fetch mem pc.toNat = some (.new j, l) :=
  Silmaril.Proofs.X86.Atomic9.fetch_of_listed_new hl hrip hfit hdec

end Silmaril.X86.Atomic9
