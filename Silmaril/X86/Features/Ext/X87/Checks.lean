module

public import Silmaril.X86.Features.Ext.X87.Extension
public import Silmaril.X86.Features.Checks

/-!
# Checker for the x87 differential vectors

`checkLine` runs one vector of `scripts/x86-features/gen_x87_vectors.py`: it
decodes the instruction bytes with `Fpu.byteDecoder`, builds the extended state
and memory the native harness started from, executes `Fpu.ext.exec`, and
compares the x87 control, status and tag words, ST(0)–ST(7), the memory
operand, RAX and the six arithmetic flags with what the processor produced.
An #MF on hardware must be `Fault.x87Exception` in the model. A vector on which
the model is `unmodeled` is accepted (the model makes no claim) and counted by
`unmodeledLine`.
-/

@[expose] public section

namespace Silmaril.X86.Features.Fpu.Checks

open Silmaril.X86 (Byte Word)
open Silmaril.Process (Memory Region)
open Silmaril.X86.Features (State X87 Result hexFields)

/-- The address of the memory operand buffer (`rdi`). -/
def memBase : Nat := 0x10000

/-- The code address. -/
def ripBase : Word := 0x1000

/-- The bytes of an encoding written as a big-endian hexadecimal number. -/
def encBytes (enc : Nat) : List Byte :=
  let n := (bitlen enc + 7) / 8
  (List.range n).reverse.map fun i => BitVec.ofNat 8 (enc >>> (8 * i))

/-- The six arithmetic flags of an RFLAGS image. -/
def flagsOf (fl : Nat) : X86.Flags :=
  let b := fun i => some (fl >>> i % 2 == 1)
  ⟨b 0, b 2, b 4, b 6, b 7, b 11⟩

def flagsMatch (f : X86.Flags) (fl : Nat) : Bool :=
  f.carry == some (fl % 2 == 1) && f.parity == some (fl >>> 2 % 2 == 1) &&
    f.adjust == some (fl >>> 4 % 2 == 1) && f.zero == some (fl >>> 6 % 2 == 1) &&
    f.sign == some (fl >>> 7 % 2 == 1) && f.overflow == some (fl >>> 11 % 2 == 1)

/-- The x87 state with physical registers `regs` (R0..R7). -/
def x87Of (cw sw tw : Nat) (regs : List Nat) : X87 :=
  ⟨fun p => BitVec.ofNat 80 (regs.getD p.val 0), BitVec.ofNat 16 sw, BitVec.ofNat 16 cw,
    BitVec.ofNat 16 tw⟩

/-- The input state: RDI addresses the buffer, RAX and RFLAGS as given. -/
def stateOf (x : X87) (rax fl : Nat) : State :=
  let core : X86.State :=
    { regs := fun r => if r = .rdi then BitVec.ofNat 64 memBase
        else if r = .rax then BitVec.ofNat 64 rax else 0
      rip := ripBase, flags := flagsOf fl }
  { State.ofCore core with x87 := x }

/-- A 128-byte read-write buffer holding the memory operand. -/
def memoryOf (memlen mem : Nat) : Memory :=
  ⟨[⟨memBase, 128, ⟨true, true, false⟩⟩],
    Memory.install ∅ memBase ((List.range 128).map fun i =>
      if i < memlen then BitVec.ofNat 8 (mem >>> (8 * i)) else 0)⟩

/-! ## Vector lines

A line is `enc cw sw tw r0..r7 memlen mem rax rflags ok` followed, when `ok =
1`, by `cw' sw' tw' r0'..r7' mem' rax' rflags'`, in hexadecimal, with registers
in physical order (R0..R7). An output field `.` repeats the input field. -/

/-- The input field an output field defaults to. -/
def outSource (k : Nat) : Nat := if k < 11 then k + 1 else k + 2

/-- The fields of a line, with `.` resolved. -/
def lineFields (line : String) : Option (List Nat) :=
  let words := (line.splitOn " ").filter (!·.isEmpty)
  if words.isEmpty then none
  else
    let ins := words.take 17
    let outs := words.drop 17
    match ins.mapM Features.hexNat? with
    | none => none
    | some inv =>
      let outv := (List.range outs.length).zip outs |>.mapM fun (k, w) =>
        if w == "." then some (inv.getD (outSource k) 0) else Features.hexNat? w
      outv.map (inv ++ ·)

/-- The resolved lines of a vector text. -/
def vectorLines (text : String) : List (List Nat) :=
  (text.splitOn "\n").filterMap lineFields

/-- Compare a model result with the hardware outputs. -/
def agrees (t : State) (m : Memory) (memlen : Nat) (out : List Nat) : Bool :=
  match out with
  | cw :: sw :: tw :: rest =>
    let regs := rest.take 8
    match rest.drop 8 with
    | [mem, rax, fl] =>
      let x := t.x87
      x.control.toNat == cw && x.status.toNat == sw && x.tag.toNat == tw &&
        (List.range 8).all (fun p => (x.regs ⟨p % 8, Nat.mod_lt _ (by decide)⟩).toNat == regs.getD p 0) &&
        (m.readBytes memBase memlen).map ofLe == some mem &&
        (t.core.read .rax).toNat == rax && flagsMatch t.core.flags fl
    | _ => false
  | _ => false

/-- Run the model on a vector line. -/
def runLine (fields : List Nat) : Option (Result × Nat × Nat × List Nat × Bool) :=
  match fields with
  | enc :: cw :: sw :: tw :: rest =>
    let regs := rest.take 8
    match rest.drop 8 with
    | memlen :: mem :: rax :: fl :: ok :: out =>
      let bytes := encBytes enc
      match decode bytes with
      | some (i, n) =>
        if n != bytes.length then none
        else
          let s := stateOf (x87Of cw sw tw regs) rax fl
          some (exec i n s (memoryOf memlen mem), n, memlen, out, ok == 1)
      | none => none
    | _ => none
  | _ => none

/-- One vector: the model agrees with the hardware, or is `unmodeled`. -/
def checkLine (fields : List Nat) : Bool :=
  match runLine fields with
  | some (.retired t m, n, memlen, out, true) =>
    t.rip == ripBase + BitVec.ofNat 64 n && agrees t m memlen out
  | some (.fault (.x87Exception _), _, _, _, false) => true
  | some (.unmodeled, _, _, _, _) => true
  | _ => false

/-- The model is `unmodeled` on the vector. -/
def unmodeledLine (fields : List Nat) : Bool :=
  match runLine fields with
  | some (.unmodeled, _, _, _, _) => true
  | _ => false

end Silmaril.X86.Features.Fpu.Checks
