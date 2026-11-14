module

public import Silmaril.Process.Mt.X86.Defs
public meta import Silmaril.Process.Mt.X86.Defs
public meta import Silmaril.Process.Mt.Prim.Defs
public meta import Silmaril.X86.Basic

/-!
# Exhaustive schedules of the multithreaded x86 process model (differential testing)

Small two-thread x86-64 programs (raw bytes, position independent: every address comes in a
register), explored over **every schedule** with the executable SC scheduler `Mt.X86.exec1`
(each of its runs is an `MtProc X sc Prim.table (Base.none Unit)` run, `Mt.X86.run_sound`).
`#guard` checks the set of final observations (compiled evaluation, as in `Examples`), to
compare with the same bytes run natively (`tools/litmus-hw/mtproc_hw.c`;
`docs/mt-validation.md` has the comparison).

| program | observation | every schedule of the model (SC) | hardware (i7-8700) |
|---|---|---|---|
| SB | `[r1, r2, status]` | `{[0,1,0], [1,0,0], [1,1,0]}` (924 schedules) | also `r1 = r2 = 0` |
| MP | `[flag, data, status]` | `{[0,0,0], [0,1,0], [1,1,0]}` | the same set |
| INC2 | `[x, status]` | `{[1,0], [2,0]}` | the same set |
| LOCKINC2 | `[x, status]` | `{[2,0]}` | the same set |

SB is racy: its weak outcome is outside every SC run, and the model's `tso` memory system
reaches it only through buffered plain steps, which need the instructions' access lists
(`Task.x86Acc`); `mtX` emits none today.

Thread `t` runs at `0x1000 + 0x100 t` with `rdi`, `rsi`, `rdx` set as below; data at `0x3000`.
-/

namespace Silmaril.Proofs.Process.Mt.Explore

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory Region)
open Silmaril.Process.Mt
open Silmaril.Process.Mt.X86

def regs (vs : List (Reg × Word)) : Silmaril.Machine.RegisterFile Reg Word :=
  fun r => ((vs.find? (·.1 == r)).map (·.2)).getD 0

def core (rip : Nat) (vs : List (Reg × Word)) : Core :=
  ⟨{ regs := regs vs, rip := BitVec.ofNat 64 rip, flags := ⟨none, none, none, none, none, none⟩ },
    fun _ => 0⟩

def mem (code : List (Nat × List Byte)) : Memory :=
  let rx : Silmaril.Process.Permissions := ⟨true, false, true⟩
  let rw : Silmaril.Process.Permissions := ⟨true, true, false⟩
  let zeros := (List.range 0x40).map fun _ => (0 : Byte)
  ⟨[⟨0x1000, 0x1000, rx⟩, ⟨0x3000, 0x1000, rw⟩, ⟨0x5000, 0x3000, rw⟩],
    code.foldl (fun b c => Memory.install b c.1 c.2) (Memory.install ∅ 0x3000 zeros)⟩

def cfg (ths : List (Nat × Core)) (m : Memory) : XCfg Unit :=
  ⟨fun t => (ths.find? (·.1 == t)).map fun p => { st := .run p.2 }, m, {}, (), false, none⟩

def word (C : XCfg Unit) (a : Nat) : Nat := (Prim.rd C.ms a 8).getD 999

/-- The final configurations of every schedule (at most `fuel` steps deep). -/
partial def finals (C : XCfg Unit) (tids : List Nat) (fuel : Nat) : List (XCfg Unit) :=
  if fuel = 0 then [] else
  match tids.filterMap (fun t => exec1 ({} : Env Unit) tids C t) with
  | [] => [C]
  | succ => succ.flatMap fun p => finals p.1 p.2 (fuel - 1)

/-- Distinct observations. -/
def observe (C₀ : XCfg Unit) (tids : List Nat) (obs : XCfg Unit → List Nat) : List (List Nat) :=
  ((finals C₀ tids 64).map obs).foldl (fun acc o => if acc.contains o then acc else acc ++ [o]) []

/-- `exit(0)`: `mov rax, 60; xor rdi, rdi; syscall`. -/
def exit0 : List Byte := [0x48, 0xC7, 0xC0, 0x3C, 0x00, 0x00, 0x00, 0x48, 0x31, 0xFF, 0x0F, 0x05]

/-- **SB**: `mov qword [rdi], 1; mov rax, [rsi]; mov [rdx], rax; exit(0)`. Thread 1:
`rdi = x`, `rsi = y`, `rdx = r1`; thread 2: `rdi = y`, `rsi = x`, `rdx = r2`. -/
def sbCode : List Byte :=
  [0x48, 0xC7, 0x07, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x06, 0x48, 0x89, 0x02] ++ exit0

def sb : XCfg Unit :=
  cfg [(1, core 0x1100 [(.rsp, 0x5ff8), (.rdi, 0x3000), (.rsi, 0x3008), (.rdx, 0x3010)]),
       (2, core 0x1200 [(.rsp, 0x6ff8), (.rdi, 0x3008), (.rsi, 0x3000), (.rdx, 0x3018)])]
    (mem [(0x1100, sbCode), (0x1200, sbCode)])

/-- **MP**, writer: `mov qword [rdi], 1; mov qword [rsi], 1; exit(0)` (`rdi = data`,
`rsi = flag`); reader: `mov rax, [rsi]; mov rcx, [rdi]; mov [rdx], rax; mov [rdx+8], rcx;
exit(0)`. -/
def mpW : List Byte :=
  [0x48, 0xC7, 0x07, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x06, 0x01, 0x00, 0x00, 0x00] ++ exit0
def mpR : List Byte :=
  [0x48, 0x8B, 0x06, 0x48, 0x8B, 0x0F, 0x48, 0x89, 0x02, 0x48, 0x89, 0x4A, 0x08] ++ exit0

def mp : XCfg Unit :=
  cfg [(1, core 0x1100 [(.rsp, 0x5ff8), (.rdi, 0x3000), (.rsi, 0x3008)]),
       (2, core 0x1200 [(.rsp, 0x6ff8), (.rdi, 0x3000), (.rsi, 0x3008), (.rdx, 0x3010)])]
    (mem [(0x1100, mpW), (0x1200, mpR)])

/-- **INC2**: `mov rax, [rdi]; add rax, 1; mov [rdi], rax; exit(0)` in both threads. -/
def incCode : List Byte := [0x48, 0x8B, 0x07, 0x48, 0x83, 0xC0, 0x01, 0x48, 0x89, 0x07] ++ exit0

def inc2 : XCfg Unit :=
  cfg [(1, core 0x1100 [(.rsp, 0x5ff8), (.rdi, 0x3000)]),
       (2, core 0x1200 [(.rsp, 0x6ff8), (.rdi, 0x3000)])]
    (mem [(0x1100, incCode), (0x1200, incCode)])

/-- **LOCKINC2**: `lock add qword [rdi], 1; exit(0)` in both threads. -/
def lockIncCode : List Byte := [0xF0, 0x48, 0x83, 0x07, 0x01] ++ exit0

def lockInc2 : XCfg Unit :=
  cfg [(1, core 0x1100 [(.rsp, 0x5ff8), (.rdi, 0x3000)]),
       (2, core 0x1200 [(.rsp, 0x6ff8), (.rdi, 0x3000)])]
    (mem [(0x1100, lockIncCode), (0x1200, lockIncCode)])

/-- The same elements. -/
def sameSet (a b : List (List Nat)) : Bool := a.all b.contains && b.all a.contains

-- observations: `[r1, r2, status]`, `[flag, data, status]`, `[x, status]`
#guard sameSet (observe sb [1, 2] fun C => [word C 0x3010, word C 0x3018, C.status.getD 999])
  [[0, 1, 0], [1, 0, 0], [1, 1, 0]]
#guard (finals sb [1, 2] 64).length == 924
#guard sameSet (observe mp [1, 2] fun C => [word C 0x3010, word C 0x3018, C.status.getD 999])
  [[0, 0, 0], [0, 1, 0], [1, 1, 0]]
#guard sameSet (observe inc2 [1, 2] fun C => [word C 0x3000, C.status.getD 999]) [[1, 0], [2, 0]]
#guard sameSet (observe lockInc2 [1, 2] fun C => [word C 0x3000, C.status.getD 999]) [[2, 0]]

end Silmaril.Proofs.Process.Mt.Explore
