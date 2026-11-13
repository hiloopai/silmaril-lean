module

public import Silmaril.X86.Str9X.Defs
public import Silmaril.X86.Features.Ext.X87.Checks

/-!
# Checker for the x87 vectors on the tower

`checkLine` runs one vector of the x87 lane (`scripts/x86-features/gen_x87_vectors.py`, the
format of `Features.Fpu.Checks`) through **one `Str9X.step`**: the instruction bytes at
`0x1000` in an executable region, the 128-byte operand buffer at `0x10000` (`rdi`), RAX, the
six arithmetic flags and the x87 state of the vector, DF clear. So the whole decoder chain of
`Str9D` must reject the bytes, `fetchFpu` must fetch them, and `execFpu` must give the
processor's result. Where the lane's checker expects a retirement, the step must retire with
the processor's control, status and tag words, ST registers, memory operand, RAX and flags,
and RIP past the instruction; where the processor raised #MF, or the lane leaves the form
`unmodeled`, the tower has no step.
-/

@[expose] public section

namespace Silmaril.X86.Str9X.Checks

open Silmaril.X86 (Byte Word Reg State)
open Silmaril.Process (Memory)
open Silmaril.X86.Features (X87 Result)
open Silmaril.X86.Features.Fpu.Checks (memBase ripBase encBytes flagsOf x87Of agrees runLine)

/-- The code (read, execute) and the operand buffer (read, write). -/
def memoryOf (code : List Byte) (memlen mem : Nat) : Memory :=
  let data := (List.range 128).map fun i => if i < memlen then BitVec.ofNat 8 (mem >>> (8 * i)) else 0
  ⟨[⟨ripBase.toNat, code.length, ⟨true, false, true⟩⟩, ⟨memBase, 128, ⟨true, true, false⟩⟩],
    Memory.install (Memory.install ∅ ripBase.toNat code) memBase data⟩

/-- The input state: RDI addresses the buffer, RAX and RFLAGS as given, DF clear. -/
def stateOf (code : List Byte) (x : X87) (rax fl memlen mem : Nat) : XState :=
  let core : State :=
    { regs := fun r => if r = .rdi then BitVec.ofNat 64 memBase
        else if r = .rax then BitVec.ofNat 64 rax else 0
      rip := ripBase, flags := flagsOf fl }
  ⟨⟨⟨⟨⟨⟨core, memoryOf code memlen mem⟩, fun _ => 0⟩, fun _ => 0, true⟩, fun _ => 0⟩, false⟩, x⟩

/-- **One vector through `Str9X.step`.** -/
def checkLine (fields : List Nat) : Bool :=
  match fields with
  | enc :: cw :: sw :: tw :: rest =>
    match rest.drop 8 with
    | memlen :: mem :: rax :: fl :: _ =>
      let code := encBytes enc
      let x := stateOf code (x87Of cw sw tw (rest.take 8)) rax fl memlen mem
      match runLine fields with
      | some (.retired _ _, n, _, out, true) =>
        match step x with
        | some y => y.core.rip == ripBase + BitVec.ofNat 64 n && agrees (toF y) y.memory memlen out
        | none => false
      | some (.fault (.x87Exception _), _, _, _, false) => (step x).isNone
      | some (.unmodeled, _, _, _, _) => (step x).isNone
      | _ => false
    | _ => false
  | _ => false

end Silmaril.X86.Str9X.Checks
