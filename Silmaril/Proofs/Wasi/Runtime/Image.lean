module

public import Silmaril.Proofs.Wasi.Runtime.Loop
public import Silmaril.Machine.X86.Open.Thms

/-!
# Proofs: the concrete x86 runtime of `hello` meets `HelloLoop`

The program `helloCode` with memory `helloMem` (`Silmaril.Wasi.Runtime`) on the open machine
`Open.step`. Every step is one `Open.step_of_listed` (the listing law) with a `decide`d
decoding of the instruction's bytes, and `simp` on `Ext.exec`.

* `helloMem_loaded`, `view_data0`, `view_data1`: the code is fetchable at `codeBase`, and `hi`
  is readable at `dataBase`.
* `step_at`: one step of the program at offset `o`.
* `movEsi_step`, `movEdx_step`, `movEax1_step`, `movEdi1_step`, `add_step`, `sub_step`,
  `jne_back`, `jne_out`, `movEax60_step`, `movEdi0_step`: the nine instructions, on `RegsAt`.
* `resume_regs`: after a `write` answer, the state LPS resumes with is at offset `22` with
  `rax = |ds|` (the other registers of `RegsAt` and the memory unchanged).
* `loop_back`, `loop_out`: from offset `22` to the next `syscall` (bytes left) or to the exit
  sequence (none left).
* **`helloLoopImg`**: the program is a `HelloLoop Open.step segs ch e` for every segment list and
  every LPS model whose descriptor `1` is the live channel `ch`.
* **`helloLoop_exists`**: `Task.helloLoop_exists`. **`initModel_stdout`**: LPS's initial model
  binds descriptor `1` to channel `1`.
* **`helloImg_psafe`**: on every native machine agreeing with `Open.step`, an LPS configuration
  holding `helloStart`, with a model whose descriptor `1` is a live channel `ch`, is process-safe
  for "a prefix of `hi` on `ch`, then `exit 0`".

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Runtime

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (State MState Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Wasi.Os
open Silmaril.Wasi.Examples (hiBytes)

/-! ## Memory -/

theorem codeBase_toNat : codeBase.toNat = 0x401000 := rfl

/-- The code is fetchable at `codeBase`. -/
theorem helloMem_loaded : Loaded helloMem codeBase helloCode := by
  unfold Loaded Memory.fetchBytes
  refine Memory.readWith_eq _ _ _ _ (by decide) ?_
  intro i hi
  exact Memory.install_get _ _ _ _ hi

theorem helloMem_data (i : Nat) (hi : i < 2) :
    helloMem.bytes[0x402000 + i]? = some (hiBytes[i]'(by simp [hiBytes]; omega)) := by
  have h1 := Memory.install_outside (Memory.install ∅ 0x402000 hiBytes) 0x401000 helloCode
    (0x402000 + i) (.inr (by simp [helloCode]; omega))
  have h2 := Memory.install_get ∅ 0x402000 hiBytes i (by simp [hiBytes]; omega)
  simp only [Std.ExtHashMap.get?_eq_getElem?] at h1 h2
  exact h1.trans h2

theorem view_data0 : viewByte helloMem .read dataBase = some 0x68 := by
  have h := helloMem_data 0 (by omega)
  simp only [viewByte, show helloMem.permits .read dataBase.toNat = true by decide, ↓reduceIte]
  exact h

theorem view_data1 : viewByte helloMem .read (dataBase + 1#64) = some 0x69 := by
  have h := helloMem_data 1 (by omega)
  simp only [viewByte, show helloMem.permits .read (dataBase + 1#64).toNat = true by decide,
    ↓reduceIte]
  exact h

/-! ## Steps -/

theorem open_decode {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {l : Nat}
    (h : Silmaril.X86.Ext.decode bytes = some (i, l)) :
    Silmaril.Machine.X86.Open.decode bytes = some (.base i, l) := by
  simp [Silmaril.Machine.X86.Open.decode, Silmaril.X86.Ext8.decode_of_ext h]

/-- **One step of the program** at offset `o`. -/
theorem step_at {m : MState} {o l : Nat} {i : Silmaril.X86.Ext.Instr} {c : State} {mem : Memory}
    (hm : m.memory = helloMem) (hrip : m.core.rip = codeBase + BitVec.ofNat 64 o)
    (hfit : o + l ≤ helloCode.length)
    (hdec : Silmaril.X86.Ext.decode ((helloCode.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Ext.exec i m.core m.memory l = .ok c mem) :
    Silmaril.Machine.X86.Open.step m = some ⟨c, mem⟩ :=
  Silmaril.Machine.X86.Open.step_of_listed (hm ▸ helloMem_loaded) hrip hfit (open_decode hdec)
    (by simp [Silmaril.X86.Ext8.exec]; exact hx)

variable {m : MState} {a d s x : Word}

theorem movEsi_step (h : RegsAt 0 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 5 a d dataBase x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 0) (l := 5) (i := .movI32 .rsi 0x402000#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, ha, hd, hx, Silmaril.X86.Ext.Sz.write, codeBase, dataBase]

theorem movEdx_step (h : RegsAt 5 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 10 a d s 2#64 m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 5) (l := 5) (i := .movI32 .rdx 2#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, ha, hd, hs, Silmaril.X86.Ext.Sz.write, codeBase]

theorem movEax1_step (h : RegsAt 10 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 15 1#64 d s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 10) (l := 5) (i := .movI32 .rax 1#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, hx, hd, hs, Silmaril.X86.Ext.Sz.write, codeBase]

theorem movEdi1_step (h : RegsAt 15 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 20 a 1#64 s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 15) (l := 5) (i := .movI32 .rdi 1#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, hx, ha, hs, Silmaril.X86.Ext.Sz.write, codeBase]

theorem add_step (h : RegsAt 22 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 25 a d (s + a) x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 22) (l := 3) (i := .alu .q .add (.reg .rsi) .rax) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hrip, hx, ha, hd, hs, codeBase, Silmaril.X86.Ext.AluOp.resultN]
  rfl

theorem sub_step (h : RegsAt 25 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 28 a d s (x - a) m' ∧
      m'.core.flags.zero = some (x - a == 0#64) := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 25) (l := 3) (i := .alu .q .sub (.reg .rdx) .rax) hm hrip (by decide)
    (by decide) rfl, ⟨hm, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp [hrip, hx, ha, hd, hs, codeBase, Silmaril.X86.Ext.AluOp.resultN,
      Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN]
  all_goals rfl

theorem jne_back (h : RegsAt 28 a d s x m) (hz : m.core.flags.zero = some false) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 10 a d s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 28) (l := 2) (i := .jcc8 .ne 0xec#8) hm hrip (by decide)
    (by decide) (by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Cond.eval, hz,
      Silmaril.X86.Ext.kNot]; exact ⟨rfl, rfl⟩), ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hrip, hx, ha, hd, hs, codeBase]

theorem jne_out (h : RegsAt 28 a d s x m) (hz : m.core.flags.zero = some true) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 30 a d s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 28) (l := 2) (i := .jcc8 .ne 0xec#8) hm hrip (by decide)
    (by decide) (by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Cond.eval, hz,
      Silmaril.X86.Ext.kNot]; exact ⟨rfl, rfl⟩), ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hrip, hx, ha, hd, hs, codeBase]

theorem movEax60_step (h : RegsAt 30 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 35 60#64 d s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 30) (l := 5) (i := .movI32 .rax 60#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, hx, hd, hs, Silmaril.X86.Ext.Sz.write, codeBase]

theorem movEdi0_step (h : RegsAt 35 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAt 40 a 0#64 s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at (o := 35) (l := 5) (i := .movI32 .rdi 0#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, hx, ha, hs, Silmaril.X86.Ext.Sz.write, codeBase]

/-! ## The `syscall`s -/

theorem regsAt_trap (h : RegsAt 20 a d s x m) : AtSyscall m := by
  obtain ⟨hm, hrip, -, -, -, -⟩ := h
  have hf := helloMem_loaded.fetchBytes_sub (offset := 20) (len := 2) (by omega) (by decide)
  unfold AtSyscall
  rw [hm, hrip]
  exact hf

theorem regsAt_exit (h : RegsAt 40 60#64 0#64 s x m) : ExitOk m := by
  obtain ⟨hm, hrip, ha, hd, -, -⟩ := h
  have hf := helloMem_loaded.fetchBytes_sub (offset := 40) (len := 2) (by omega) (by decide)
  refine ⟨?_, by rw [ha]; rfl, by rw [hd]; rfl⟩
  unfold AtSyscall
  rw [hm, hrip]
  exact hf

/-- **After a `write` answer**, LPS resumes at offset `22` with `rax = |ds|`. -/
theorem resume_regs {segs : List Segment} {k : X86FlagChoices.Choice} {ds : List Byte}
    (h : RegsAt 20 a d s x m) :
    RegsAt 22 (lenWord ds) d s x (resume (trapAt m k) (writeEff segs m k ds)) := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [resume, x86AdvancePastSvc, x86ApplyEffectNative, trapAt, trapped,
    X86FlagChoices.completeState, writeEff, applyMemoryEffect, mkEffect,
    SyscallEffect.withCopyins, hm, hrip, codeBase]
  all_goals split <;> simp [hd, hs, hx]

/-! ## The request at the `write` syscall -/

theorem reqAt_sysno {segs : List Segment} {k : X86FlagChoices.Choice} :
    (reqAt segs m k).sysno = m.core.read .rax := rfl

theorem reqAt_arg0 {segs : List Segment} {k : X86FlagChoices.Choice} :
    (reqAt segs m k).arg 0 = m.core.read .rdi := rfl

theorem reqAt_arg1 {segs : List Segment} {k : X86FlagChoices.Choice} :
    (reqAt segs m k).arg 1 = m.core.read .rsi := rfl

theorem reqAt_arg2 {segs : List Segment} {k : X86FlagChoices.Choice} :
    (reqAt segs m k).arg 2 = m.core.read .rdx := rfl

theorem reqAt_mem {segs : List Segment} {k : X86FlagChoices.Choice} :
    (reqAt segs m k).mem = viewByte m.memory .read := rfl

/-- The source of the `write` at offset `j` of `hi`. -/
theorem hello_writeSource (j : Nat) (hj : j < 2) :
    writeSource (viewByte helloMem .read) (dataBase + BitVec.ofNat 64 j) (BitVec.ofNat 64 (2 - j)) =
      hiBytes.drop j := by
  have e2 : (zw (rwCountClamp 2#64)).toNat = 2 := by decide
  have e1 : (zw (rwCountClamp 1#64)).toNat = 1 := by decide
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · simp only [writeSource, readableBytes, Nat.sub_zero, BitVec.add_zero]
    rw [show BitVec.ofNat 64 2 = 2#64 from rfl, e2]
    simp [readableBytesAux, view_data0, view_data1, hiBytes]
  · simp only [writeSource, readableBytes]
    rw [show BitVec.ofNat 64 (2 - 1) = 1#64 from rfl, e1]
    simp [readableBytesAux, view_data1, hiBytes]

theorem hello_source {segs : List Segment} {bs : List Byte} (h : helloInv bs m)
    (k : X86FlagChoices.Choice) :
    writeSource (reqAt segs m k).mem ((reqAt segs m k).arg 1) ((reqAt segs m k).arg 2) = bs := by
  obtain ⟨j, hj, rfl, hm, -, -, -, hs, hx⟩ := h
  rw [reqAt_mem, reqAt_arg1, reqAt_arg2, hm, hs, hx]
  exact hello_writeSource j hj

theorem hello_nonempty {bs : List Byte} (h : helloInv bs m) : bs ≠ [] := by
  obtain ⟨j, hj, rfl, -⟩ := h
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [hiBytes]

theorem hello_chan {segs : List Segment} {e : Silmaril.Process.LPS.Model} {ch : Word}
    (hfd : fdLookup e.fds 1 = some (.channel ch)) {bs : List Byte} (h : helloInv bs m)
    (k : X86FlagChoices.Choice) :
    fdLookup e.fds (fd32 ((reqAt segs m k).arg 0)) = some (.channel ch) := by
  obtain ⟨j, -, -, -, -, -, hd, -, -⟩ := h
  rw [reqAt_arg0, hd]
  exact hfd

/-- **`writeArm` handles the loop's `syscall`.** -/
theorem hello_handles {segs : List Segment} {e : Silmaril.Process.LPS.Model} {ch : Word}
    (hfd : fdLookup e.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) {bs : List Byte}
    (h : helloInv bs m) (k : X86FlagChoices.Choice) : (writeArm segs).Handles (trapAt m k) e := by
  have hsrc := hello_source (segs := segs) h k
  have hne := hello_nonempty h
  have hc := hello_chan (segs := segs) hfd h k
  obtain ⟨j, hj, -, -, -, ha, -, hs, hx⟩ := h
  refine ⟨by rw [reqAt_sysno, ha]; rfl, ch, hc, hch, ?_, ?_, ?_⟩
  · rw [reqAt_arg1, reqAt_arg2, hs, hx]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> decide
  · rw [reqAt_arg2, hx]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> decide
  · rw [hsrc]
    exact hne

/-! ## Runs between the `syscall`s -/

theorem safe_step {c : MState → Option MState} {Q : MState → Prop} {m m' : MState}
    (h : c m = some m') (h' : ∀ n, SafeN c Q n m') : ∀ n, SafeN c Q n m
  | 0 => trivial
  | n + 1 => .inr ⟨m', h, h' n⟩

theorem safe_now {c : MState → Option MState} {Q : MState → Prop} {m : MState} (h : Q m) :
    ∀ n, SafeN c Q n m
  | 0 => trivial
  | _ + 1 => .inl h

/-- **Bytes left**: from offset `22` back to the `write` syscall. -/
theorem loop_back {s' x' : Word} (h : RegsAt 22 a 1#64 s x m) (hs : s + a = s') (hx : x - a = x')
    (hne : x' ≠ 0#64) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step (RegsAt 20 1#64 1#64 s' x') n m := by
  obtain ⟨m1, h1, r1⟩ := add_step h
  obtain ⟨m2, h2, r2, z2⟩ := sub_step r1
  have hz : m2.core.flags.zero = some false := by
    rw [z2, hx]
    simp [hne]
  obtain ⟨m3, h3, r3⟩ := jne_back r2 hz
  obtain ⟨m4, h4, r4⟩ := movEax1_step r3
  obtain ⟨m5, h5, r5⟩ := movEdi1_step r4
  rw [hs, hx] at r5
  exact safe_step h1 (safe_step h2 (safe_step h3 (safe_step h4 (safe_step h5 (safe_now r5)))))

/-- **No bytes left**: from offset `22` to the exit sequence. -/
theorem loop_out (h : RegsAt 22 a 1#64 s x m) (hx : x - a = 0#64) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step helloFin n m := by
  obtain ⟨m1, h1, r1⟩ := add_step h
  obtain ⟨m2, h2, r2, z2⟩ := sub_step r1
  have hz : m2.core.flags.zero = some true := by
    rw [z2, hx]
    rfl
  obtain ⟨m3, h3, r3⟩ := jne_out r2 hz
  exact safe_step h1 (safe_step h2 (safe_step h3 (safe_now ⟨_, _, _, _, r3⟩)))

/-- The three short writes: `l` bytes written at offset `j` of `hi`. -/
theorem hello_after {j l : Nat} (hjl : (j = 0 ∧ l = 1) ∨ (j = 0 ∧ l = 2) ∨ (j = 1 ∧ l = 1))
    (hR : RegsAt 22 (BitVec.ofNat 64 l) 1#64 (dataBase + BitVec.ofNat 64 j)
      (BitVec.ofNat 64 (2 - j)) m) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step (fun m' => if (hiBytes.drop j).drop l = [] then
      helloFin m' else helloInv ((hiBytes.drop j).drop l) m') n m := by
  rcases hjl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : (hiBytes.drop 0).drop 1 = [0x69] := rfl
    simp only [e, reduceCtorEq, ↓reduceIte]
    exact fun n => Silmaril.Machine.X86.Safe.safeN_post (fun m' hm' => ⟨1, by omega, rfl, hm'⟩)
      (loop_back hR (by decide) (by decide) (by decide) n)
  · have e : (hiBytes.drop 0).drop 2 = [] := rfl
    simp only [e, ↓reduceIte]
    exact loop_out hR (by decide)
  · have e : (hiBytes.drop 1).drop 1 = [] := rfl
    simp only [e, ↓reduceIte]
    exact loop_out hR (by decide)

/-- **After a short write of `ds`**, the loop runs to the rest, or to the exit sequence. -/
theorem hello_next {segs : List Segment} {bs : List Byte} (h : helloInv bs m)
    (k : X86FlagChoices.Choice) (ds : List Byte) (h1 : 1 ≤ ds.length) (hp : ds <+: bs) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step
      (fun m' => if bs.drop ds.length = [] then helloFin m' else helloInv (bs.drop ds.length) m')
      n (resume (trapAt m k) (writeEff segs m k ds)) := by
  obtain ⟨j, hj, hbs, hr⟩ := h
  have hR : RegsAt 22 (lenWord ds) 1#64 (dataBase + BitVec.ofNat 64 j) (BitVec.ofNat 64 (2 - j))
      (resume (trapAt m k) (writeEff segs m k ds)) := resume_regs hr
  have hlen : lenWord ds = BitVec.ofNat 64 ds.length := by simp [lenWord, zw]
  have hle : ds.length ≤ 2 - j := by
    have hl : ds.length ≤ (hiBytes.drop j).length := hbs ▸ hp.length_le
    simpa only [List.length_drop, hiBytes, List.length_cons, List.length_nil] using hl
  have hjl : (j = 0 ∧ ds.length = 1) ∨ (j = 0 ∧ ds.length = 2) ∨ (j = 1 ∧ ds.length = 1) := by
    omega
  exact hbs ▸ hello_after hjl (hlen ▸ hR)

/-- From the launch state to the `write` of `hi`. -/
theorem hello_toWrite : ∀ n, SafeN Silmaril.Machine.X86.Open.step (helloInv hiBytes) n helloStart := by
  have r0 : RegsAt 0 0#64 0#64 0#64 0#64 helloStart := ⟨rfl, by decide, rfl, rfl, rfl, rfl⟩
  obtain ⟨m1, h1, r1⟩ := movEsi_step r0
  obtain ⟨m2, h2, r2⟩ := movEdx_step r1
  obtain ⟨m3, h3, r3⟩ := movEax1_step r2
  obtain ⟨m4, h4, r4⟩ := movEdi1_step r3
  have hi : helloInv hiBytes m4 :=
    ⟨0, by omega, rfl, by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using r4⟩
  exact safe_step h1 (safe_step h2 (safe_step h3 (safe_step h4 (safe_now hi))))

/-- From the exit sequence to `exit(0)`. -/
theorem hello_toExit (h : helloFin m) : ∀ n, SafeN Silmaril.Machine.X86.Open.step ExitOk n m := by
  obtain ⟨a, d, s, x, r0⟩ := h
  obtain ⟨m1, h1, r1⟩ := movEax60_step r0
  obtain ⟨m2, h2, r2⟩ := movEdi0_step r1
  exact safe_step h1 (safe_step h2 (safe_now (regsAt_exit r2)))

/-! ## The runtime -/

/-- **The program is a runtime of `hello`** on the open machine, for every LPS model whose
descriptor `1` is the live channel `ch`. -/
def helloLoopImg (segs : List Segment) {e : Silmaril.Process.LPS.Model} {ch : Word}
    (hfd : fdLookup e.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    HelloLoop Silmaril.Machine.X86.Open.step segs ch e where
  Inv := helloInv
  Fin := helloFin
  nonempty _ _ h := hello_nonempty h
  trap _ _ h := by
    obtain ⟨_, _, _, hr⟩ := h
    exact regsAt_trap hr
  handles _ _ h k := hello_handles hfd hch h k
  chan _ _ h k := hello_chan hfd h k
  source _ _ h k := hello_source h k
  next _ _ h k ds h1 hp := hello_next h k ds h1 hp
  start := helloStart
  toWrite := hello_toWrite
  toExit _ h := hello_toExit h

/-- **`Task.helloLoop_exists` holds.** -/
theorem helloLoop_exists : Task.helloLoop_exists := fun _ _ hfd hch =>
  ⟨Silmaril.Machine.X86.Open.step, [], fun h => h, ⟨helloLoopImg [] hfd hch⟩⟩

/-- **LPS's initial model binds descriptor `1` to channel `1`.** -/
theorem initModel_stdout (reserved : List (Word × Word)) (brk0 mbase sp : Word) (lim : Int)
    (inp : ProcInput) :
    fdLookup (initModel reserved brk0 mbase sp lim inp).fds 1 = some (.channel 1) := rfl

/-- **The concrete runtime is process-safe for LPS**: on every native machine agreeing with
`Open.step`, an LPS configuration aligned with `helloStart`, whose model binds descriptor `1` to
a live channel `ch`, produces only a prefix of `hi` on `ch`, then `exit 0`. -/
theorem helloImg_psafe {oracle : Oracle} {nstep : NStep} {refused : RefusalFilter}
    {segs : List Segment} {ch : Word} (hM : Agrees nstep Silmaril.Machine.X86.Open.step)
    {cfg : Config (flagMachine oracle nstep)} (al : AlignedF cfg helloStart)
    (hfd : fdLookup cfg.model.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    PSafeF segs refused (helloAllowed ch cfg.model.fs) cfg :=
  helloLoop_psafe hM (helloLoopImg segs hfd hch) al rfl

/-- **The concrete runtime on the bridge's release machine** (`x86WithFlagOracle8`, every flag
oracle), with the trace read as the OS image of `hello`'s WASI run against `stdoutImpl`. -/
theorem helloImg_psafe8 {oracle : Oracle} {refused : RefusalFilter} {segs : List Segment}
    {ch : Word} {cfg : Config (machine oracle)} (al : Aligned cfg helloStart)
    (hfd : fdLookup cfg.model.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    PSafe segs refused
      (fun tr => tr <+: osTrace ch (Silmaril.Wasi.wtrace helloRun) ++ [.exitEv 0 cfg.model.fs]) cfg := by
  rw [helloRun_os]
  exact (Silmaril.Proofs.Machine.Process.LpsBridge.psafeF_iff).1
    (helloImg_psafe Silmaril.Proofs.Machine.Process.LpsBridge.agrees_open8
      (Silmaril.Proofs.Machine.Process.LpsBridge.alignedF_iff.2 al) hfd hch)

end Silmaril.Wasi.Runtime