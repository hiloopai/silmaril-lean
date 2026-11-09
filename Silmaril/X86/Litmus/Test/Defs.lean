module

public import Silmaril.X86.Litmus.Extract.Defs

/-!
# A minimal litmus test format

This is the structure hand-built tests use, and that a generated corpus can target. A test is
a
herd-style x86 litmus test whose threads are **machine-code bytes**:

* shared locations (`Loc`) live at absolute addresses in one read-write data page
  `[dataBase, dataBase + dataSize)`, with an initial value and a size in bytes;
* thread `k`'s code lives at `codeBase k = 0x400000 + 0x1000 * k` in a read-execute
  page; its initial registers are listed (`initRegs`; others are zero, flags undefined);
* the final condition is herd's `exists` clause: a conjunction of `Atom`s;
* `herd` is the expected x86-TSO verdict (herd7's `x86tso.cat`), with `source` the
  provenance (a herdtools7 catalogue path and commit, or `hand-written`).

`Test.thread k` turns thread `k` into an extraction `Thread`, and `Test.extractAll` extracts
every thread over the test's value domain.
-/

@[expose] public section

namespace Silmaril.X86.Litmus

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.Process (Region)

/-- A shared location. -/
structure Loc where
  name : String
  addr : Nat
  size : Nat
  init : Nat
  deriving DecidableEq, Repr

/-- One thread: its code bytes and initial registers. -/
structure TThread where
  code : List Byte
  initRegs : List (Reg × Word)
  deriving DecidableEq, Repr

/-- An atom of a final condition: a thread's final register value, or a location's final
value. -/
inductive Atom where
  | reg (thread : Nat) (r : Reg) (v : Nat)
  | loc (name : String) (v : Nat)
  deriving DecidableEq, Repr

/-- A verdict on the final condition. -/
inductive Verdict where
  | allowed
  | forbidden
  deriving DecidableEq, Repr

/-- A litmus test. -/
structure Test where
  name : String
  locs : List Loc
  threads : List TThread
  /-- The value domain every read ranges over. -/
  domain : List Nat
  /-- The maximum number of instructions per thread. -/
  fuel : Nat
  /-- herd's `exists` clause, as a conjunction. -/
  cond : List Atom
  /-- The expected x86-TSO verdict of `cond`, if known. -/
  herd : Option Verdict
  /-- Provenance: a catalogue path and commit, or `hand-written`. -/
  source : String
  deriving Repr

/-- The data page. -/
def dataBase : Nat := 0x10000

/-- The size of the data page. -/
def dataSize : Nat := 0x1000

/-- The code address of thread `k`. -/
def codeBase (k : Nat) : Word := BitVec.ofNat 64 (0x400000 + 0x1000 * k)

/-- The mapping list of a test with `n` threads: the data page (read-write) and one code page
per thread (read-execute). -/
def testRegions (n : Nat) : List Region :=
  ⟨dataBase, dataSize, ⟨true, true, false⟩⟩ :: ⟨0x400000, 0x1000 * n, ⟨true, false, true⟩⟩ :: []

/-- Thread `k` of a test, as an extraction thread. -/
def Test.thread (T : Test) (k : Nat) : Option Thread :=
  T.threads[k]?.map fun th =>
    ⟨codeBase k, th.code, testRegions T.threads.length, initCore (codeBase k) th.initRegs⟩

/-- Every thread's candidate traces, in thread order. -/
def Test.extractAll (T : Test) : Option (List (List Trace)) :=
  (List.range T.threads.length).mapM fun k =>
    (T.thread k).bind fun t => extract t T.domain T.fuel

/-- The registers a condition observes on thread `k`. -/
def Test.observed (T : Test) (k : Nat) : List Reg :=
  T.cond.filterMap fun
    | .reg j r _ => if j = k then some r else none
    | .loc .. => none

/-- The compact views of every thread's traces, with the observed registers. -/
def Test.views (T : Test) : Option (List (List View)) :=
  T.extractAll.map fun trss =>
    (List.range trss.length).zip trss |>.map fun (k, trs) => trs.map (Trace.view (T.observed k))

/-- **Extraction succeeds on every thread of the test, and every extracted trace replays** on
`Atomic9.step` (`Replay`). -/
def Test.Sound (T : Test) : Prop :=
  ∀ k < T.threads.length, ∃ t trs, T.thread k = some t ∧ extract t T.domain T.fuel = some trs ∧
    ∀ tr ∈ trs, Replay t t.init tr.steps tr.final

/-- Every thread extracts, and every step of every trace is `Thread.placed` (checked by
`decide`). -/
def Test.placed (T : Test) : Bool :=
  (List.range T.threads.length).all fun k =>
    match T.thread k with
    | none => false
    | some t =>
      match extract t T.domain T.fuel with
      | some trs => t.allPlaced trs
      | none => false

/-- **The replay hypotheses of the test are satisfiable**: at every step of every extracted
trace, some memory has the thread's regions and code and answers the step's reads. -/
def Test.NonVacuous (T : Test) : Prop :=
  ∀ k < T.threads.length, ∃ t trs, T.thread k = some t ∧ extract t T.domain T.fuel = some trs ∧
    ∀ tr ∈ trs, ∀ r ∈ tr.steps, ∃ m : Silmaril.Process.Memory, m.regions = t.regions ∧
      Silmaril.X86.Ext.Loaded m t.base t.code ∧ Answers m r.acts

/-! ## Hand-built tests

`x` is at `0x10000` and `y` at `0x10040` (different cache lines), both 4 bytes, initially 0.
The bytes were assembled with GNU as 2.42 (`.intel_syntax noprefix`) and checked with
`objdump -d`. -/

namespace Hand

/-- `x`, `y`. -/
def xy : List Loc := [⟨"x", 0x10000, 4, 0⟩, ⟨"y", 0x10040, 4, 0⟩]

/-- `mov dword ptr [0x10000], 1` -/
def stX1 : List Byte := [0xC7, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00]
/-- `mov dword ptr [0x10040], 1` -/
def stY1 : List Byte := [0xC7, 0x04, 0x25, 0x40, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00]
/-- `mov eax, dword ptr [0x10000]` -/
def ldEaxX : List Byte := [0x8B, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00]
/-- `mov eax, dword ptr [0x10040]` -/
def ldEaxY : List Byte := [0x8B, 0x04, 0x25, 0x40, 0x00, 0x01, 0x00]
/-- `mov ebx, dword ptr [0x10000]` -/
def ldEbxX : List Byte := [0x8B, 0x1C, 0x25, 0x00, 0x00, 0x01, 0x00]
/-- `mfence` -/
def mfence : List Byte := [0x0F, 0xAE, 0xF0]
/-- `mov eax, 1` -/
def movEax1 : List Byte := [0xB8, 0x01, 0x00, 0x00, 0x00]
/-- `lock xadd dword ptr [0x10000], eax` -/
def lockXaddX : List Byte := [0xF0, 0x0F, 0xC1, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00]

/-- **SB** (store buffering): `P0: x = 1; r0 = y`, `P1: y = 1; r1 = x`;
`exists 0:rax=0 /\ 1:rax=0`. Allowed by x86-TSO. -/
def sb : Test where
  name := "SB"
  locs := xy
  threads := [⟨stX1 ++ ldEaxY, []⟩, ⟨stY1 ++ ldEaxX, []⟩]
  domain := [0, 1]
  fuel := 4
  cond := [.reg 0 .rax 0, .reg 1 .rax 0]
  herd := some .allowed
  source := "hand-written (shape of herdtools7 x86 SB)"

/-- **SB+mfences**: SB with `mfence` between the store and the load in both threads.
Forbidden by x86-TSO. -/
def sbMfences : Test where
  name := "SB+mfences"
  locs := xy
  threads := [⟨stX1 ++ mfence ++ ldEaxY, []⟩, ⟨stY1 ++ mfence ++ ldEaxX, []⟩]
  domain := [0, 1]
  fuel := 4
  cond := [.reg 0 .rax 0, .reg 1 .rax 0]
  herd := some .forbidden
  source := "hand-written (shape of herdtools7 x86 SB+mfences)"

/-- **MP** (message passing): `P0: x = 1; y = 1`, `P1: r0 = y; r1 = x`;
`exists 1:rax=1 /\ 1:rbx=0`. Forbidden by x86-TSO. -/
def mp : Test where
  name := "MP"
  locs := xy
  threads := [⟨stX1 ++ stY1, []⟩, ⟨ldEaxY ++ ldEbxX, []⟩]
  domain := [0, 1]
  fuel := 4
  cond := [.reg 1 .rax 1, .reg 1 .rbx 0]
  herd := some .forbidden
  source := "hand-written (shape of herdtools7 x86 MP)"

/-- **XADD2**: both threads `r = 1; lock xadd [x], r` (an atomic fetch-and-add); `exists
0:rax=0 /\ 1:rax=0 /\ x=1` (a lost update). Forbidden by x86-TSO (RMW atomicity). -/
def xadd2 : Test where
  name := "XADD2"
  locs := [⟨"x", 0x10000, 4, 0⟩]
  threads := [⟨movEax1 ++ lockXaddX, []⟩, ⟨movEax1 ++ lockXaddX, []⟩]
  domain := [0, 1, 2]
  fuel := 4
  cond := [.reg 0 .rax 0, .reg 1 .rax 0, .loc "x" 1]
  herd := some .forbidden
  source := "hand-written"

/-- The absolute memory operand `[disp32]` (SIB, no base, no index). -/
def absMem (d : BitVec 32) : Silmaril.X86.Ext.Mem := ⟨.none, none, d, by simp⟩

/-! Compact expected actions (4-byte accesses). -/

/-- A plain 4-byte store of `v` at `a`. -/
def st (a v : Nat) : Brief := ⟨.store, a, 4, false, 0, v⟩
/-- A plain 4-byte load at `a` returning `v`. -/
def ld (a v : Nat) : Brief := ⟨.load, a, 4, false, v, 0⟩
/-- A locked 4-byte read-modify-write at `a` reading `r` and writing `w`. -/
def lrmw (a r w : Nat) : Brief := ⟨.rmw, a, 4, true, r, w⟩
/-- `mfence`. -/
def mf : Brief := ⟨.fence .mfence, 0, 0, false, 0, 0⟩

/-! ### Byte mutations

Variants of the hand tests with one byte-level change, to check that the extracted events
follow the bytes. -/

/-- XADD2 with the `lock` prefix (`0xF0`) dropped in thread 0. -/
def xadd2NoLock : Test :=
  { xadd2 with threads := [⟨movEax1 ++ lockXaddX.drop 1, []⟩, ⟨movEax1 ++ lockXaddX, []⟩] }

/-- SB+mfences with both `mfence`s dropped: the bytes of SB. -/
def sbMfencesNoFence : Test :=
  { sbMfences with threads := [⟨stX1 ++ ldEaxY, []⟩, ⟨stY1 ++ ldEaxX, []⟩] }

/-- SB with the immediate of thread 0's store changed from 1 to 2. -/
def sbImm2 : Test :=
  { sb with threads := [⟨stX1.set 7 2 ++ ldEaxY, []⟩, ⟨stY1 ++ ldEaxX, []⟩] }

/-- One thread loading from the unmapped address `0x20000`
(`mov eax, dword ptr [0x20000]`). -/
def unmappedLoad : Test :=
  { sb with threads := [⟨[0x8B, 0x04, 0x25, 0x00, 0x00, 0x02, 0x00], []⟩] }

/-- One thread with an unsupported memory form, `add dword ptr [0x10000], eax`. -/
def addMem : Test :=
  { sb with threads := [⟨[0x01, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00], []⟩] }

end Hand

end Silmaril.X86.Litmus
