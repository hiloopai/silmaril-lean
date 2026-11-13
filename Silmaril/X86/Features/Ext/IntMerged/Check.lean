module

public import Silmaril.X86.Features.Ext.IntExt.Extension
public import Silmaril.X86.Features.Ext.BaseInt.Extension
public import Silmaril.X86.Features.Checks

/-!
# Checking an integer extension against native execution

`check e row` runs one vector of `scripts/x86-features/gen_int_vectors.py`
through the extension `e`: it decodes the code bytes with `e`'s decoder, runs
`e.exec` on the input registers, flags and data words, and compares with the
hardware's result.

The state: the sixteen registers (RSP is the harness's RSP when the instruction
started), RIP `0x1000` (no case is RIP-relative), the six status flags all
known. The memory: the 64-byte data area at `0x10000800`, readable and
writable, and the sixteen bytes around RSP for PUSH.

The comparison: every register, every flag the model defines (`some`; an
undefined flag matches anything), the data words, RIP advanced by the length,
and the pushed word when RSP moved. `Verdict.unmodeled` means the model makes
no claim (chaos), which matches any hardware result.
-/

@[expose] public section

namespace Silmaril.X86.Features.IntMerged

open Silmaril.X86 (Reg Word Byte Flags)
open Silmaril.Process (Memory Region)

/-- The outcome of checking one vector. -/
inductive Verdict where
  | pass
  | unmodeled
  /-- The decoder rejects the bytes, or consumes a different length. -/
  | undecoded
  /-- The model faults or computes a different result. -/
  | mismatch
  deriving DecidableEq, Repr

def Verdict.ok : Verdict → Bool
  | .pass | .unmodeled => true
  | _ => false

def regList : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def dataBase : Nat := 0x10000800

/-- `len` bytes, most significant first, of `code`. -/
def codeBytes (len code : Nat) : List Byte :=
  (List.range len).map fun j => BitVec.ofNat 8 (code / 256 ^ (len - 1 - j))

def leBytes (v k : Nat) : List Byte := (List.range k).map fun j => BitVec.ofNat 8 (v / 256 ^ j)

def flagsOf (f : Nat) : Flags :=
  ⟨some (f.testBit 0), some (f.testBit 2), some (f.testBit 4), some (f.testBit 6),
    some (f.testBit 7), some (f.testBit 11)⟩

def initState (regs : List Nat) (rflags : Nat) : State :=
  State.ofCore
    { regs := fun r => BitVec.ofNat 64 (regs.getD (regList.idxOf r) 0), rip := 0x1000,
      flags := flagsOf rflags }

def rw : Silmaril.Process.Permissions := ⟨true, true, false⟩

def initMemory (data : List Nat) (rsp : Nat) : Memory :=
  ⟨[⟨dataBase, 64, rw⟩, ⟨rsp - 8, 16, rw⟩],
    Memory.install (Memory.install ∅ (rsp - 8) (List.replicate 16 0)) dataBase
      (data.flatMap (leBytes · 8))⟩

def flagOk (model : Option Bool) (hw : Bool) : Bool :=
  match model with
  | some b => b == hw
  | none => true

def flagsOk (f : Flags) (hw : Nat) : Bool :=
  flagOk f.carry (hw.testBit 0) && flagOk f.parity (hw.testBit 2) &&
    flagOk f.adjust (hw.testBit 4) && flagOk f.zero (hw.testBit 6) &&
    flagOk f.sign (hw.testBit 7) && flagOk f.overflow (hw.testBit 11)

/-- Compare a retired state with the hardware's registers, flags, data words and
pushed word. -/
def agrees (len rsp : Nat) (t : State) (m : Memory) (outRegs : List Nat) (outFlags : Nat)
    (outData : List Nat) (pushed : Nat) : Bool :=
  (regList.zipIdx.all fun (r, i) => (t.core.read r).toNat == outRegs.getD i 0) &&
    flagsOk t.core.flags outFlags &&
    ((List.range 8).all fun j =>
      (Ext.loadN m (BitVec.ofNat 64 (dataBase + 8 * j)) 8).map BitVec.toNat == some (outData.getD j 0)) &&
    t.rip.toNat == 0x1000 + len &&
    (t.core.read .rsp == BitVec.ofNat 64 rsp ||
      (Ext.loadN m (t.core.read .rsp) 8).map BitVec.toNat == some pushed)

/-- Check one vector row (`lanes len code regs[16] rflags data[8] outRegs[16]
outFlags outData[8] pushed`) through `e`. -/
def check (e : Extension) (row : List Nat) : Verdict :=
  match row with
  | _ :: len :: code :: rest =>
    let regs := rest.take 16
    let rflags := rest.getD 16 0
    let data := (rest.drop 17).take 8
    let outRegs := (rest.drop 25).take 16
    let outFlags := rest.getD 41 0
    let outData := (rest.drop 42).take 8
    let pushed := rest.getD 50 0
    let rsp := regs.getD 4 0
    match e.decoder.decode (codeBytes len code) with
    | some (x, n) =>
      if n != len then .undecoded
      else
        match e.exec x n (initState regs rflags) (initMemory data rsp) with
        | .retired t m => if agrees len rsp t m outRegs outFlags outData pushed then .pass else .mismatch
        | .fault _ => .mismatch
        | .unmodeled => .unmodeled
    | none => .undecoded
  | _ => .undecoded

end Silmaril.X86.Features.IntMerged
