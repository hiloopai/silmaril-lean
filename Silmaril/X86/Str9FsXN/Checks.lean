module

public import Silmaril.X86.Str9FsXN.Defs

/-!
# Checker for the `Narrow9` hardware vectors

`checkLine` runs one vector of `scripts/x86-narrow/gen_narrow_vectors.py`: it builds the
state the native harness started from (the instruction at `0x1000` in an executable region,
a 32-byte read-write buffer at `0x10000`, the fifteen registers other than `rsp`, the six
arithmetic flags), takes **one `Str9FsXN.step`** (so fetch, the whole decoder chain and
the `Narrow9` semantics are exercised), and compares RIP, every register but `rsp`, every
flag the model defines, and the buffer with what the processor produced. A flag the model
leaves undefined (`none`) is not compared. The processor never faulted, so a step that
does not retire fails the check.
-/

@[expose] public section

namespace Silmaril.X86.Str9FsXN.Checks

open Silmaril.X86 (Byte Word Reg State Flags MState)
open Silmaril.X86.Sse9 (XState)
open Silmaril.Process (Memory)

/-- The code address. -/
def ripBase : Nat := 0x1000

/-- The buffer address. -/
def memBase : Nat := 0x10000

/-- The buffer length. -/
def memLen : Nat := 32

/-- A hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

/-- A hexadecimal number. -/
def hexNat? (s : String) : Option Nat :=
  if s.isEmpty then none else s.toList.foldlM (fun acc c => (hexDigit? c).map (16 * acc + ·)) 0

/-- Pairs of hexadecimal digits as bytes. -/
def hexBytes? : List Char → Option (List Byte)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigit? a
    let y ← hexDigit? b
    let t ← hexBytes? rest
    pure (BitVec.ofNat 8 (16 * x + y) :: t)
  | _ => none

/-- The registers in hardware order. -/
def regs : List Reg := [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The six arithmetic flags of an RFLAGS image. -/
def flagsOf (fl : Nat) : Flags :=
  let b := fun i => some (fl >>> i % 2 == 1)
  ⟨b 0, b 2, b 4, b 6, b 7, b 11⟩

/-- Every flag the model defines has the hardware value. -/
def flagsMatch (f : Flags) (fl : Nat) : Bool :=
  let ok := fun (o : Option Bool) (i : Nat) => o.all (· == (fl >>> i % 2 == 1))
  ok f.carry 0 && ok f.parity 2 && ok f.adjust 4 && ok f.zero 6 && ok f.sign 7 && ok f.overflow 11

/-- The memory: the code (read, execute) and the buffer (read, write). -/
def memoryOf (code : List Byte) (buf : Nat) : Memory :=
  let data := (List.range memLen).map fun i => BitVec.ofNat 8 (buf >>> (8 * i))
  ⟨[⟨ripBase, code.length, ⟨true, false, true⟩⟩, ⟨memBase, memLen, ⟨true, true, false⟩⟩],
    Memory.install (Memory.install ∅ ripBase code) memBase data⟩

/-- The input state. -/
def stateOf (code : List Byte) (rv : List Nat) (fl buf : Nat) : XState :=
  let core : State :=
    { regs := fun r => BitVec.ofNat 64 (rv.getD (regs.idxOf r) 0)
      rip := BitVec.ofNat 64 ripBase, flags := flagsOf fl }
  ⟨⟨core, memoryOf code buf⟩, fun _ => 0⟩

/-- A vector line: the code bytes and the 36 numbers that follow. -/
def lineFields (line : String) : Option (List Byte × List Nat) :=
  match (line.splitOn " ").filter (!·.isEmpty) with
  | [] => none
  | enc :: rest => do
    let code ← hexBytes? enc.toList
    let nums ← rest.mapM hexNat?
    if nums.length = 36 then some (code, nums) else none

/-- The lines of a vector text. -/
def vectorLines (text : String) : List (List Byte × List Nat) :=
  (text.splitOn "\n").filterMap lineFields

/-- **One vector**: one `Str9FsXN.step` retires with the processor's result. -/
def checkLine (v : List Byte × List Nat) : Bool :=
  let (code, nums) := v
  let rv := nums.take 16
  let fl := nums.getD 16 0
  let buf := nums.getD 17 0
  let out := nums.drop 18
  let rv' := out.take 16
  let fl' := out.getD 16 0
  let buf' := out.getD 17 0
  match step (stateOf code rv fl buf) with
  | none => false
  | some y =>
    let c := y.m.core
    c.rip.toNat == ripBase + code.length &&
      (List.range 16).all (fun k => k == 4 || (c.read (regs.getD k .rax)).toNat == rv'.getD k 0) &&
      flagsMatch c.flags fl' &&
      (y.m.memory.readBytes memBase memLen).map Silmaril.X86.Ext.leValue == some buf'

end Silmaril.X86.Str9FsXN.Checks
