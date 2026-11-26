module

public import Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Run
public import Silmaril.X86.MemoryModel.Litmus.Corpus.Defs

/-!
# The TSO pool over SB's bytes reaches the store-buffering outcome

`sb_pool_allowed`: the byte-granular TSO pool running the bytes of the corpus
test `SB` on `Atomic9.step` (`TsoFinal`) reaches the final state with `0:rax = 0` and
`1:rax = 0`, the outcome SC forbids. The run: thread 0 buffers its store to `x`, then loads `y`
from memory (`0`); thread 1 buffers its store to `y`, then loads `x` from memory (`0`); both
buffers flush.

This is the allowed direction of gap 1 on one test, and it checks two things about the proved
`Bridge.Task.tsoRunCir`: the machine over the bytes is genuinely weak (it is not an SC machine),
and `TsoFinal` of a two-thread corpus test is not empty, so the `*_pool_forbidden` verdicts are
not vacuous for lack of runs.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Sb

open Silmaril.X86 (State Byte Word)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemoryModel.Litmus (Test Final)
open Silmaril.X86.Pool (TPool TsoStep TsoFlush TsoReach overlay atomic9Ev storeEntries readSpan)
open Silmaril.X86.Concurrency.Bridge

/-- The test. -/
abbrev sb : Test := Silmaril.X86.MemoryModel.Litmus.Corpus.«SB»

def code0 : List Byte := [0xc7, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00,
  0x8b, 0x04, 0x25, 0x40, 0x00, 0x01, 0x00]

def code1 : List Byte := [0xc7, 0x04, 0x25, 0x40, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00,
  0x8b, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00]

def th0 : Silmaril.X86.MemoryModel.Litmus.Thread := sb.threads[0]
def th1 : Silmaril.X86.MemoryModel.Litmus.Thread := sb.threads[1]

theorem th0_code : th0.code = code0 := by decide +kernel
theorem th1_code : th1.code = code1 := by decide +kernel

def codePage0 : List Byte := code0 ++ List.replicate 4078 0
def codePage1 : List Byte := code1 ++ List.replicate 4078 0
def dataPage : List Byte := List.replicate 4096 0

theorem codePage0_len : codePage0.length = 4096 := by
  rw [codePage0, List.length_append, List.length_replicate]; rfl
theorem codePage1_len : codePage1.length = 4096 := by
  rw [codePage1, List.length_append, List.length_replicate]; rfl
theorem dataPage_len : dataPage.length = 4096 := List.length_replicate

/-- A two-thread test memory: zeros on the data page, each thread's code on its page. -/
def mem : Memory := ⟨Silmaril.X86.Litmus.testRegions 2,
  Memory.install (Memory.install (Memory.install ∅ 0x400000 codePage0) 0x401000 codePage1)
    0x10000 dataPage⟩

theorem get_data (i : Nat) (hi : i < 4096) : mem.bytes.get? (0x10000 + i) = some 0 := by
  show (Memory.install _ 0x10000 dataPage).get? _ = _
  rw [Memory.install_get _ _ _ _ (by rw [dataPage_len]; exact hi)]
  simp only [dataPage, List.getElem_replicate]

theorem get_code1 (i : Nat) (hi : i < 4096) :
    mem.bytes.get? (0x401000 + i) = some (codePage1[i]'(by rw [codePage1_len]; exact hi)) := by
  show (Memory.install _ 0x10000 dataPage).get? _ = _
  rw [Memory.install_outside _ _ _ _ (.inr (by rw [dataPage_len]; omega)),
    Memory.install_get _ _ _ _ (by rw [codePage1_len]; exact hi)]

theorem get_code0 (i : Nat) (hi : i < 4096) :
    mem.bytes.get? (0x400000 + i) = some (codePage0[i]'(by rw [codePage0_len]; exact hi)) := by
  show (Memory.install _ 0x10000 dataPage).get? _ = _
  rw [Memory.install_outside _ _ _ _ (.inr (by rw [dataPage_len]; omega)),
    Memory.install_outside _ _ _ _ (.inl (by omega)),
    Memory.install_get _ _ _ _ (by rw [codePage0_len]; exact hi)]

theorem backed : Backed mem := by
  intro a ha
  simp only [Memory.permits, mem] at ha
  simp [Silmaril.X86.Litmus.testRegions, Silmaril.Process.Region.Contains,
    Silmaril.X86.Litmus.dataBase, Silmaril.X86.Litmus.dataSize,
    Silmaril.Process.Permissions.allows] at ha
  rcases ha with ha | ha
  · have := of_decide_eq_true ha
    have := get_data (a - 0x10000) (by omega)
    rw [show 0x10000 + (a - 0x10000) = a by omega] at this
    rw [this]; rfl
  · have := of_decide_eq_true ha
    by_cases h0 : a < 0x401000
    · have := get_code0 (a - 0x400000) (by omega)
      rw [show 0x400000 + (a - 0x400000) = a by omega] at this
      rw [this]; rfl
    · have := get_code1 (a - 0x401000) (by omega)
      rw [show 0x401000 + (a - 0x401000) = a by omega] at this
      rw [this]; rfl

theorem rb_code0 (n i : Nat) (h : i + n ≤ 4096) :
    Memory.readBacking mem.bytes (0x400000 + i) n = some ((codePage0.drop i).take n) := by
  induction n generalizing i with
  | zero => simp [Memory.readBacking]
  | succ n ih =>
    simp only [Memory.readBacking, get_code0 i (by omega), Option.bind_eq_bind, Option.bind_some]
    rw [show 0x400000 + i + 1 = 0x400000 + (i + 1) by omega, ih (i + 1) (by omega)]
    rw [List.drop_eq_getElem_cons (i := i) (by rw [codePage0_len]; omega)]
    rfl

theorem rb_code1 (n i : Nat) (h : i + n ≤ 4096) :
    Memory.readBacking mem.bytes (0x401000 + i) n = some ((codePage1.drop i).take n) := by
  induction n generalizing i with
  | zero => simp [Memory.readBacking]
  | succ n ih =>
    simp only [Memory.readBacking, get_code1 i (by omega), Option.bind_eq_bind, Option.bind_some]
    rw [show 0x401000 + i + 1 = 0x401000 + (i + 1) by omega, ih (i + 1) (by omega)]
    rw [List.drop_eq_getElem_cons (i := i) (by rw [codePage1_len]; omega)]
    rfl

theorem rb_data (n i : Nat) (h : i + n ≤ 4096) :
    Memory.readBacking mem.bytes (0x10000 + i) n = some (List.replicate n 0) := by
  induction n generalizing i with
  | zero => simp [Memory.readBacking]
  | succ n ih =>
    simp only [Memory.readBacking, get_data i (by omega), Option.bind_eq_bind, Option.bind_some]
    rw [show 0x10000 + i + 1 = 0x10000 + (i + 1) by omega, ih (i + 1) (by omega)]
    rfl

/-- The extraction thread of thread `k`. -/
def xt (k : Nat) (th : Silmaril.X86.MemoryModel.Litmus.Thread) : Silmaril.X86.Litmus.Thread :=
  sb.xthread k th

theorem loaded0 : Loaded mem (xt 0 th0).base (xt 0 th0).code := by
  simp only [Loaded, Memory.fetchBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  rw [show (xt 0 th0).code = code0 from th0_code,
    show ((xt 0 th0).base).toNat = 0x400000 + 0 by decide +kernel]
  exact rb_code0 18 0 (by omega)

theorem loaded1 : Loaded mem (xt 1 th1).base (xt 1 th1).code := by
  simp only [Loaded, Memory.fetchBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  rw [show (xt 1 th1).code = code1 from th1_code,
    show ((xt 1 th1).base).toNat = 0x401000 + 0 by decide +kernel]
  exact rb_code1 18 0 (by omega)

/-! ## The views -/

/-- Memory with `[1, 0, 0, 0]` installed at `a`, on the data page. -/
def put (a : Nat) : Memory := { mem with bytes := Memory.install mem.bytes a [1, 0, 0, 0] }

theorem put_x : overlay mem [(0x10000, [1, 0, 0, 0])] = put 0x10000 := rfl
theorem put_y : overlay mem [(0x10040, [1, 0, 0, 0])] = put 0x10040 := rfl

/-- The data page is readable and writable. -/
theorem perm_data {m : Memory} (hm : m.regions = Silmaril.X86.Litmus.testRegions 2) {b : Nat}
    (h : 0x10000 ≤ b ∧ b < 0x11000) {acc : Silmaril.Process.Access}
    (hacc : acc = .write ∨ acc = .read) : m.permits acc b = true := by
  simp only [Memory.permits, hm]
  simp [Silmaril.X86.Litmus.testRegions, Silmaril.Process.Region.Contains,
      Silmaril.X86.Litmus.dataBase, Silmaril.X86.Litmus.dataSize,
      Silmaril.Process.Permissions.allows]
  left
  refine ⟨decide_eq_true ⟨h.1, h.2⟩, ?_⟩
  rcases hacc with rfl | rfl <;> rfl

theorem loaded_put {a : Nat} (ha : 0x10000 ≤ a ∧ a + 4 ≤ 0x11000) {k : Nat}
    {th : Silmaril.X86.MemoryModel.Litmus.Thread} (hl : Loaded mem (xt k th).base (xt k th).code) :
    Loaded (put a) (xt k th).base (xt k th).code := by
  refine Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.loaded_congr hl rfl fun b hb => ?_
  apply Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.install_outside'
  have hw := Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.wx (m := mem) (N := 2) rfl (a := b)
  by_contra hc
  simp only [List.length_cons, List.length_nil] at hc
  rw [hw (perm_data rfl (by omega) (.inl rfl))] at hb
  cases hb

theorem read_put_zero {a b : Nat} (hb : 0x10000 ≤ b ∧ b + 4 ≤ 0x11000)
    (hd : b + 4 ≤ a ∨ a + 4 ≤ b) : (put a).readBytes b 4 = some [0, 0, 0, 0] := by
  simp only [Memory.readBytes, Memory.readWith]
  have hc : (put a).checkSpan .read b 4 = true := by
    rw [Memory.checkSpan_iff]
    refine ⟨by simp [Silmaril.Process.addressLimit]; omega,
      by simp [Silmaril.Process.addressLimit]; omega,
      fun j hj => perm_data rfl (by omega) (.inr rfl)⟩
  rw [hc]
  simp only [↓reduceIte]
  show Memory.readBacking (Memory.install mem.bytes a [1, 0, 0, 0]) b 4 = _
  rw [Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.readBacking_congr (b := mem.bytes) 4 b
    fun j hj => Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.install_outside' _ _ _ _
      (by simp only [List.length_cons, List.length_nil]; omega)]
  rw [show b = 0x10000 + (b - 0x10000) by omega, rb_data 4 _ (by omega)]
  rfl

theorem readSpan_put (a : Nat) : readSpan (put a) a 4 = [1, 0, 0, 0] := by
  have h (i : Nat) (hi : i < 4) := Memory.install_get mem.bytes a [1, 0, 0, 0] i hi
  simp only [Std.ExtHashMap.get?_eq_getElem?] at h
  simp only [readSpan, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, put, Std.ExtHashMap.get?_eq_getElem?, List.cons_append]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]
  rfl

/-! ## The four instructions -/

def dX : Silmaril.X86.Ext.Mem := { base := .none, index := none, disp := 0x10000#32, rip_no_index := by decide }
def dY : Silmaril.X86.Ext.Mem := { base := .none, index := none, disp := 0x10040#32, rip_no_index := by decide }

/-- `mov dword [x], 1` and `mov dword [y], 1`. -/
def stX : Atomic9.Instr := .open9 (.ext8 (.base (.movI .d (.mem dX) 1#32)))
def stY : Atomic9.Instr := .open9 (.ext8 (.base (.movI .d (.mem dY) 1#32)))
/-- `mov eax, dword [y]` and `mov eax, dword [x]`. -/
def ldY : Atomic9.Instr := .open9 (.ext8 (.base (.load .d .rax dY)))
def ldX : Atomic9.Instr := .open9 (.ext8 (.base (.load .d .rax dX)))

def i0 : State := (xt 0 th0).init
def i1 : State := (xt 1 th1).init

/-- After the store. -/
def a0 : State := { i0 with rip := i0.rip + BitVec.ofNat 64 11 }
def a1 : State := { i1 with rip := i1.rip + BitVec.ofNat 64 11 }

/-- After the load of `0`. -/
def b0 : State :=
  { Silmaril.X86.Ext.Sz.write .d a0 .rax
      ((BitVec.ofNat 64 (Silmaril.X86.Ext.leValue [0, 0, 0, 0])).setWidth
        Silmaril.X86.Ext.Sz.d.bits) with rip := a0.rip + BitVec.ofNat 64 7 }
def b1 : State :=
  { Silmaril.X86.Ext.Sz.write .d a1 .rax
      ((BitVec.ofNat 64 (Silmaril.X86.Ext.leValue [0, 0, 0, 0])).setWidth
        Silmaril.X86.Ext.Sz.d.bits) with rip := a1.rip + BitVec.ofNat 64 7 }

theorem writeBytes_put (a : Nat) (ha : 0x10000 ≤ a ∧ a + 4 ≤ 0x11000) :
    mem.writeBytes a [1, 0, 0, 0] = some (put a) := by
  have hc : mem.checkSpan .write a 4 = true := by
    rw [Memory.checkSpan_iff]
    refine ⟨by simp [Silmaril.Process.addressLimit]; omega,
      by simp [Silmaril.Process.addressLimit]; omega,
      fun j hj => perm_data rfl (by omega) (.inl rfl)⟩
  have hl : [(1 : Byte), 0, 0, 0].length = 4 := rfl
  simp only [Memory.writeBytes, hl, hc, ↓reduceIte]
  rfl

theorem leBytes_one :
    Silmaril.X86.Ext.leBytes (((1#32).signExtend Silmaril.X86.Ext.Sz.d.bits).setWidth 64) 4 =
      [1, 0, 0, 0] := by decide +kernel

theorem exec_stX : Atomic9.exec stX i0 mem 11 = .ok a0 (put 0x10000) := by
  simp only [stX, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.storeN]
  rw [show (Silmaril.X86.Ext.Mem.addr dX i0 (i0.rip + BitVec.ofNat 64 11)).toNat = 0x10000 by
      decide +kernel,
    show Silmaril.X86.Ext.Sz.d.bytes = 4 from rfl, leBytes_one, writeBytes_put _ (by omega)]
  rfl

theorem exec_stY : Atomic9.exec stY i1 mem 11 = .ok a1 (put 0x10040) := by
  simp only [stY, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.storeN]
  rw [show (Silmaril.X86.Ext.Mem.addr dY i1 (i1.rip + BitVec.ofNat 64 11)).toNat = 0x10040 by
      decide +kernel,
    show Silmaril.X86.Ext.Sz.d.bytes = 4 from rfl, leBytes_one, writeBytes_put _ (by omega)]
  rfl

theorem exec_ldY : Atomic9.exec ldY a0 (put 0x10000) 7 = .ok b0 (put 0x10000) := by
  simp only [ldY, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.loadN]
  rw [show (Silmaril.X86.Ext.Mem.addr dY a0 (a0.rip + BitVec.ofNat 64 7)).toNat = 0x10040 by
      decide +kernel,
    show Silmaril.X86.Ext.Sz.d.bytes = 4 from rfl, read_put_zero (by omega) (by omega)]
  rfl

theorem exec_ldX : Atomic9.exec ldX a1 (put 0x10040) 7 = .ok b1 (put 0x10040) := by
  simp only [ldX, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.loadN]
  rw [show (Silmaril.X86.Ext.Mem.addr dX a1 (a1.rip + BitVec.ofNat 64 7)).toNat = 0x10000 by
      decide +kernel,
    show Silmaril.X86.Ext.Sz.d.bytes = 4 from rfl, read_put_zero (by omega) (by omega)]
  rfl

theorem fetch_stX : MemEvent.atomic9Fetch mem i0.rip.toNat = some (stX, 11) :=
  Atomic9.fetch_of_listed_base (o := 0) loaded0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem fetch_stY : MemEvent.atomic9Fetch mem i1.rip.toNat = some (stY, 11) :=
  Atomic9.fetch_of_listed_base (o := 0) loaded1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem fetch_ldY : MemEvent.atomic9Fetch (put 0x10000) a0.rip.toNat = some (ldY, 7) :=
  Atomic9.fetch_of_listed_base (o := 11) (loaded_put (by omega) loaded0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem fetch_ldX : MemEvent.atomic9Fetch (put 0x10040) a1.rip.toNat = some (ldX, 7) :=
  Atomic9.fetch_of_listed_base (o := 11) (loaded_put (by omega) loaded1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem acc_stX : MemEvent.atomic9Accesses stX i0 11 = [⟨.store, 0x10000, 4, false⟩] := by
  decide +kernel
theorem acc_stY : MemEvent.atomic9Accesses stY i1 11 = [⟨.store, 0x10040, 4, false⟩] := by
  decide +kernel
theorem acc_ldY : MemEvent.atomic9Accesses ldY a0 7 = [⟨.load, 0x10040, 4, false⟩] := by
  decide +kernel
theorem acc_ldX : MemEvent.atomic9Accesses ldX a1 7 = [⟨.load, 0x10000, 4, false⟩] := by
  decide +kernel

theorem entries_st (a : Nat) :
    storeEntries [⟨.store, a, 4, false⟩] (put a) = [(a, [1, 0, 0, 0])] := by
  simp [storeEntries, MemEvent.Kind.writes, readSpan_put]

theorem entries_ld (a : Nat) (m : Memory) : storeEntries [⟨.load, a, 4, false⟩] m = [] := by
  simp [storeEntries, MemEvent.Kind.writes]

/-! ## The run -/

def p0 : TPool Nat := testPool sb mem
def p1 : TPool Nat := { p0 with
  threads := Function.update p0.threads 0 (some a0),
  buffer := Function.update p0.buffer 0 [(0x10000, [1, 0, 0, 0])] }
def p2 : TPool Nat := { p1 with threads := Function.update p1.threads 0 (some b0) }
def p3 : TPool Nat := { p2 with
  threads := Function.update p2.threads 1 (some a1),
  buffer := Function.update p2.buffer 1 [(0x10040, [1, 0, 0, 0])] }
def p4 : TPool Nat := { p3 with threads := Function.update p3.threads 1 (some b1) }
def p5 : TPool Nat := { p4 with
  memory := { p4.memory with bytes := Memory.install p4.memory.bytes 0x10000 [1, 0, 0, 0] },
  buffer := Function.update p4.buffer 0 [] }
def p6 : TPool Nat := { p5 with
  memory := { p5.memory with bytes := Memory.install p5.memory.bytes 0x10040 [1, 0, 0, 0] },
  buffer := Function.update p5.buffer 1 [] }

theorem hnf0 (s : State) (h : s.rip ≠ (sb.xthread 0 th0).endRip) : ¬ TestFin sb 0 s :=
  fun hf => h (hf th0 rfl)
theorem hnf1 (s : State) (h : s.rip ≠ (sb.xthread 1 th1).endRip) : ¬ TestFin sb 1 s :=
  fun hf => h (hf th1 rfl)

theorem step1 : TsoStep atomic9Ev (TestFin sb) p0 0 p1 := by
  have h := @TsoStep.buffered Nat _ atomic9Ev (TestFin sb) p0 0 i0 a0 stX 11 (put 0x10000) rfl
    (hnf0 _ (by decide +kernel)) fetch_stX (by decide +kernel)
    exec_stX
  rw [show atomic9Ev.accesses stX i0 11 = _ from acc_stX, entries_st] at h
  exact h

theorem view1 : overlay p1.memory (p1.buffer 0) = put 0x10000 := by
  simp only [p1, p0, testPool, Function.update_self]; rfl

theorem step2 : TsoStep atomic9Ev (TestFin sb) p1 0 p2 := by
  have h := @TsoStep.buffered Nat _ atomic9Ev (TestFin sb) p1 0 a0 b0 ldY 7 (put 0x10000)
    (by simp [p1]) (hnf0 _ (by decide +kernel)) (by rw [view1]; exact fetch_ldY)
    (by decide +kernel) (by rw [view1]; exact exec_ldY)
  rw [show atomic9Ev.accesses ldY a0 7 = _ from acc_ldY, entries_ld, List.append_nil,
    Function.update_eq_self] at h
  exact h

theorem view3 : overlay p2.memory (p2.buffer 1) = mem := by
  simp only [p2, p1, p0, testPool, ne_eq, one_ne_zero, not_false_eq_true,
    Function.update_of_ne]; rfl

theorem step3 : TsoStep atomic9Ev (TestFin sb) p2 1 p3 := by
  have h := @TsoStep.buffered Nat _ atomic9Ev (TestFin sb) p2 1 i1 a1 stY 11 (put 0x10040)
    (by simp [p2, p1, p0, testPool]; exact ⟨th1, rfl, rfl⟩) (hnf1 _ (by decide +kernel))
    (by rw [view3]; exact fetch_stY) (by decide +kernel)
    (by rw [view3]; exact exec_stY)
  rw [show atomic9Ev.accesses stY i1 11 = _ from acc_stY, entries_st] at h
  have hb : p2.buffer 1 = [] := by simp [p2, p1, p0, testPool]
  rw [hb, List.nil_append] at h
  exact h

theorem view4 : overlay p3.memory (p3.buffer 1) = put 0x10040 := by
  simp only [p3, p2, p1, p0, testPool, Function.update_self]; rfl

theorem step4 : TsoStep atomic9Ev (TestFin sb) p3 1 p4 := by
  have h := @TsoStep.buffered Nat _ atomic9Ev (TestFin sb) p3 1 a1 b1 ldX 7 (put 0x10040)
    (by simp [p3]) (hnf1 _ (by decide +kernel)) (by rw [view4]; exact fetch_ldX)
    (by decide +kernel) (by rw [view4]; exact exec_ldX)
  rw [show atomic9Ev.accesses ldX a1 7 = _ from acc_ldX, entries_ld, List.append_nil,
    Function.update_eq_self] at h
  exact h

theorem flush5 : TsoFlush p4 p5 :=
  TsoFlush.head (t := 0) (rest := []) (by simp [p4, p3, p2, p1])

theorem flush6 : TsoFlush p5 p6 :=
  TsoFlush.head (t := 1) (rest := []) (by simp [p5, p4, p3])

theorem reach : TsoReach atomic9Ev (TestFin sb) p0 p6 :=
  .tail (.tail (.tail (.tail (.tail (.single (.inl ⟨0, step1⟩)) (.inl ⟨0, step2⟩))
    (.inl ⟨1, step3⟩)) (.inl ⟨1, step4⟩)) (.inr flush5)) (.inr flush6)

theorem testMem : TestMem sb mem := by
  refine ⟨rfl, ?_, ?_, backed⟩
  · intro k th h
    match k, h with
    | 0, h =>
      simp only [sb, Silmaril.X86.MemoryModel.Litmus.Corpus.«SB», List.getElem?_cons_zero,
        Option.some.injEq] at h
      subst h
      exact loaded0
    | 1, h =>
      simp only [sb, Silmaril.X86.MemoryModel.Litmus.Corpus.«SB», List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact loaded1
    | k + 2, h => simp [sb, Silmaril.X86.MemoryModel.Litmus.Corpus.«SB»] at h
  · intro a b h
    simp only [Test.initMem, Silmaril.X86.MemoryModel.Litmus.initByte] at h
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    have hm := List.mem_of_find?_eq_some hl
    have hp := List.find?_some hl
    simp only [sb, Silmaril.X86.MemoryModel.Litmus.Corpus.«SB», List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl <;> simp at hp <;>
      rw [show a = 0x10000 + (a - 0x10000) by omega, get_data _ (by omega)] <;> simp

theorem drained : Pool.Drained p6 := by
  intro t
  by_cases h1 : t = 1
  · subst h1; simp [p6]
  · by_cases h0 : t = 0
    · subst h0; simp [p6, p5]
    · simp [p6, p5, p4, p3, p2, p1, p0, testPool, h0, h1]

theorem fin : ∀ k s, p6.threads k = some s → TestFin sb k s := by
  intro k s h th hth
  match k, h, hth with
  | 0, h, hth =>
    simp [p6, p5, p4, p3, p2, p1] at h
    subst h
    simp only [sb, Silmaril.X86.MemoryModel.Litmus.Corpus.«SB», List.getElem?_cons_zero,
      Option.some.injEq] at hth
    subst hth
    decide +kernel
  | 1, h, hth =>
    simp [p6, p5, p4, p3] at h
    subst h
    simp only [sb, Silmaril.X86.MemoryModel.Litmus.Corpus.«SB», List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at hth
    subst hth
    decide +kernel
  | k + 2, _, hth => simp [sb, Silmaril.X86.MemoryModel.Litmus.Corpus.«SB»] at hth

theorem witness : sb.witness.eval (poolFinal p6) = true := by
  have h0 : p6.threads 0 = some b0 := by simp [p6, p5, p4, p3, p2, p1]
  have h1 : p6.threads 1 = some b1 := by simp [p6, p5, p4, p3]
  simp only [Test.witness, sb, Silmaril.X86.MemoryModel.Litmus.Corpus.«SB», Silmaril.X86.MemoryModel.Litmus.Cond.eval,
    Silmaril.X86.MemoryModel.Litmus.Atom.eval, poolFinal, h0, h1, Option.map_some, Option.getD_some]
  decide +kernel

/-- **The TSO pool over SB's bytes reaches the store-buffering outcome** `0:rax = 0 ∧ 1:rax = 0`
(forbidden under SC). -/
theorem sb_pool_allowed : Silmaril.X86.MemoryModel.Litmus.Verdict.allowed.Holds sb (TsoFinal sb) :=
  ⟨poolFinal p6, ⟨mem, p6, testMem, reach, drained, fin, rfl⟩, witness⟩

end Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Sb
