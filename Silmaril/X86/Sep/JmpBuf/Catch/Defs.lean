module

public import Silmaril.X86.Sep.JmpBuf.Defs
public import Silmaril.X86.Stack

/-!
# A worked example: `catch → throw2 → throw1 → longjmp`

A hand-assembled three-function program at base `e` (122 bytes):

| offset | function | code |
| --- | --- | --- |
| 0 | `catch` | `call setjmp; test %eax,%eax; jne 1f; call throw2; ret; 1: mov $-1,%eax; ret` |
| 21 | `throw2` | `call throw1; ret` |
| 27 | `throw1` | `mov $0,%esi; call longjmp; ret` |
| 38 | `setjmp` | `setjmpBytes` |
| 81 | `longjmp` | `longjmpBytes` |

`catch` is entered with `rdi = jb` (an owned `jmp_buf`). `throw1` calls `longjmp(jb, 0)`, two
frames below `catch`, so `setjmp` returns a second time with `1` and `catch` returns `-1`
(`eax = 0xffffffff`).

* `catchPre e s r jb c0 … c5`: the code, `catch` entered at `e` with return address `r` at `s`
  and 24 bytes of stack below it, `rdi = jb` an owned `jmp_buf`, the callee-saved registers
  `c0 … c5`.
* `catchPost s r c0 … c5`: returned to `r` with `rsp = s + 8`, `eax = -1` and the callee-saved
  registers, the rest garbage.
* `m0`: a concrete state (one region mapping every address read/write/execute) with the 122
  bytes at `0x400000`, the return address `RA = 0x777777` at `rsp = 0x7000`, `rdi = 0x6000`
  and the callee-saved registers `11 … 16`.

The theorems are in `Sep/JmpBuf/Catch/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.JmpBuf.CatchTest

open Silmaril.X86 (State MState Word Byte Reg Insn)
open Silmaril.Process (Memory Region)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.JmpBuf

/-! ## Code -/

def t1Mov : List Byte := [0xbe, 0x00, 0x00, 0x00, 0x00]
def cTest : List Byte := [0x85, 0xc0]
def cJne : List Byte := [0x75, 0x06]
def cMov : List Byte := [0xb8, 0xff, 0xff, 0xff, 0xff]

/-! ## Pre- and postcondition -/

/-- The precondition of the test: the code, `catch` entered at `e` with return address `r`
at `s` and 24 bytes of stack below, `rdi = jb` an owned `jmp_buf`. -/
def catchPre (e s r jb c0 c1 c2 c3 c4 c5 : Word) : SProp :=
  (codePt e.toNat (Insn.encode (.call 0x21#32)) ∗ codePt (e + BitVec.ofNat 64 5).toNat cTest ∗
        codePt (e + BitVec.ofNat 64 7).toNat cJne ∗ codePt (e + BitVec.ofNat 64 9).toNat (Insn.encode (.call 0x07#32)) ∗
        codePt (e + BitVec.ofNat 64 15).toNat cMov ∗ codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗
        codePt (e + BitVec.ofNat 64 21).toNat (Insn.encode (.call 0x01#32)) ∗ codePt (e + BitVec.ofNat 64 27).toNat t1Mov ∗
        codePt (e + BitVec.ofNat 64 32).toNat (Insn.encode (.call 0x2c#32)) ∗
        codePt (e + BitVec.ofNat 64 38).toNat setjmpBytes ∗ codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes) ∗
    ripPt e ∗ regPt .rsp s ∗ wordPt s.toNat r ∗ blockAny (s.toNat - 8) 8 ∗
    blockAny (s.toNat - 16) 8 ∗ blockAny (s.toNat - 24) 8 ∗ regPt .rdi jb ∗
    regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] ∗ regAny .rax ∗ regAny .rsi ∗
    regsAny [.rcx, .rdx, .r8, .r9, .r10, .r11] ∗ flagsAny ∗ jbAny jb.toNat

/-- `catch`'s result: returned to `r` with `eax = -1` and the callee-saved registers. -/
def catchPost (s r c0 c1 c2 c3 c4 c5 : Word) : SProp :=
  (ripPt r ∗ regPt .rsp (s + 8#64) ∗ regPt .rax 0xFFFFFFFF#64 ∗
    regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5]) ∗ strue

/-! ## A concrete state -/

/-- The 122 bytes of the catch test, the never-executed `ret`s at offsets 14, 26 and 37
included. -/
def catchBytes : List Byte :=
  Insn.encode (.call 0x21#32) ++ cTest ++ cJne ++ Insn.encode (.call 0x07#32) ++
    Insn.encode .ret ++ cMov ++ Insn.encode .ret ++ Insn.encode (.call 0x01#32) ++
    Insn.encode .ret ++ t1Mov ++ Insn.encode (.call 0x2c#32) ++ Insn.encode .ret ++
    setjmpBytes ++ longjmpBytes

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩

/-- The return address of `catch`'s caller. -/
def RA : Word := 0x777777

def mem0 : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ 0x7000 (encodeWords [RA])) 0x400000 catchBytes⟩

/-- `rip = 0x400000`, `rsp = 0x7000`, `rdi = 0x6000`, `rbx rbp r12 … r15 = 11 … 16`. -/
def core0 : State :=
  ⟨fun r => match r with
    | .rdi => 0x6000 | .rsp => 0x7000 | .rbx => 11 | .rbp => 12 | .r12 => 13 | .r13 => 14
    | .r14 => 15 | .r15 => 16 | _ => 0,
    0x400000, ⟨none, none, none, none, none, none⟩, 0⟩

def m0 : MState := ⟨core0, mem0⟩

end Silmaril.X86.Sep.JmpBuf.CatchTest
