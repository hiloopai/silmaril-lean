module

public import Silmaril.Wasi.Runtime.Launch.Defs
public import Silmaril.Wasi.Runtime.Thms
public import Silmaril.Machine.X86.Open.Thms

/-!
# Proofs: `helloCode` is a runtime of `hello` in every memory that holds it

The proofs of `Silmaril.Proofs.Wasi.Runtime.Image` (`RegsAt`, `helloInv`, `helloFin`, on
`helloMem`), restated over any memory `M` with `HelloMem M` (`RegsAtM`, `helloInvM`,
`helloFinM`): the same listing-law steps, with `HelloMem.loaded` for the fetches and
`HelloMem.data0`/`data1` for the `write` source.

* **`hello_toWrite`**: from *any* state at `codeBase` with memory `M` (whatever its other
  registers, so in particular a launch state with `rsp` set) to the `write` of `hi`.
* **`helloLoopAt`**: such a state starts a `HelloLoop Open.step segs ch e`, for every LPS model
  whose descriptor `1` is the live channel `ch`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Runtime.Launch

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (State MState Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Wasi.Os
open Silmaril.Wasi.Runtime (codeBase dataBase helloCode open_decode safe_step safe_now reqAt_sysno
  reqAt_arg0 reqAt_arg1 reqAt_arg2 reqAt_mem ExitOk HelloLoop)
open Silmaril.Wasi.Examples (hiBytes)

variable {M : Memory}

/-! ## Steps -/

theorem step_at (hM : HelloMem M) {m : MState} {o l : Nat} {i : Silmaril.X86.Ext.Instr} {c : State}
    {mem : Memory}
    (hm : m.memory = M) (hrip : m.core.rip = codeBase + BitVec.ofNat 64 o)
    (hfit : o + l ≤ helloCode.length)
    (hdec : Silmaril.X86.Ext.decode ((helloCode.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Ext.exec i m.core m.memory l = .ok c mem) :
    Silmaril.Machine.X86.Open.step m = some ⟨c, mem⟩ :=
  Silmaril.Machine.X86.Open.step_of_listed (hm ▸ hM.loaded) hrip hfit (open_decode hdec)
    (by simp [Silmaril.X86.Ext8.exec]; exact hx)

variable {m : MState} {a d s x : Word}

theorem movEsi_step (hM : HelloMem M) (h : RegsAtM M 0 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 5 a d dataBase x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 0) (l := 5) (i := .movI32 .rsi 0x402000#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, ha, hd, hx, Silmaril.X86.Ext.Sz.write, codeBase, dataBase]

theorem movEdx_step (hM : HelloMem M) (h : RegsAtM M 5 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 10 a d s 2#64 m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 5) (l := 5) (i := .movI32 .rdx 2#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, ha, hd, hs, Silmaril.X86.Ext.Sz.write, codeBase]

theorem movEax1_step (hM : HelloMem M) (h : RegsAtM M 10 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 15 1#64 d s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 10) (l := 5) (i := .movI32 .rax 1#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, hx, hd, hs, Silmaril.X86.Ext.Sz.write, codeBase]

theorem movEdi1_step (hM : HelloMem M) (h : RegsAtM M 15 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 20 a 1#64 s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 15) (l := 5) (i := .movI32 .rdi 1#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, hx, ha, hs, Silmaril.X86.Ext.Sz.write, codeBase]

theorem add_step (hM : HelloMem M) (h : RegsAtM M 22 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 25 a d (s + a) x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 22) (l := 3) (i := .alu .q .add (.reg .rsi) .rax) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hrip, hx, ha, hd, hs, codeBase, Silmaril.X86.Ext.AluOp.resultN]
  rfl

theorem sub_step (hM : HelloMem M) (h : RegsAtM M 25 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 28 a d s (x - a) m' ∧
      m'.core.flags.zero = some (x - a == 0#64) := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 25) (l := 3) (i := .alu .q .sub (.reg .rdx) .rax) hm hrip (by decide)
    (by decide) rfl, ⟨hm, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp [hrip, hx, ha, hd, hs, codeBase, Silmaril.X86.Ext.AluOp.resultN,
      Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN]
  all_goals rfl

theorem jne_back (hM : HelloMem M) (h : RegsAtM M 28 a d s x m)
    (hz : m.core.flags.zero = some false) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 10 a d s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 28) (l := 2) (i := .jcc8 .ne 0xec#8) hm hrip (by decide)
    (by decide) (by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Cond.eval, hz,
      Silmaril.X86.Ext.kNot]; exact ⟨rfl, rfl⟩), ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hrip, hx, ha, hd, hs, codeBase]

theorem jne_out (hM : HelloMem M) (h : RegsAtM M 28 a d s x m)
    (hz : m.core.flags.zero = some true) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 30 a d s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 28) (l := 2) (i := .jcc8 .ne 0xec#8) hm hrip (by decide)
    (by decide) (by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Cond.eval, hz,
      Silmaril.X86.Ext.kNot]; exact ⟨rfl, rfl⟩), ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hrip, hx, ha, hd, hs, codeBase]

theorem movEax60_step (hM : HelloMem M) (h : RegsAtM M 30 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 35 60#64 d s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 30) (l := 5) (i := .movI32 .rax 60#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, hx, hd, hs, Silmaril.X86.Ext.Sz.write, codeBase]

theorem movEdi0_step (hM : HelloMem M) (h : RegsAtM M 35 a d s x m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ RegsAtM M 40 a 0#64 s x m' := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨_, step_at hM (o := 35) (l := 5) (i := .movI32 .rdi 0#32) hm hrip (by decide)
    (by decide) rfl, ?_⟩
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hrip, hx, ha, hs, Silmaril.X86.Ext.Sz.write, codeBase]

/-! ## The `syscall`s -/

theorem regsAt_trap (hM : HelloMem M) (h : RegsAtM M 20 a d s x m) : AtSyscall m := by
  obtain ⟨hm, hrip, -, -, -, -⟩ := h
  have hf := hM.loaded.fetchBytes_sub (offset := 20) (len := 2) (by omega) (by decide)
  unfold AtSyscall
  rw [hm, hrip]
  exact hf

theorem regsAt_exit (hM : HelloMem M) (h : RegsAtM M 40 60#64 0#64 s x m) : ExitOk m := by
  obtain ⟨hm, hrip, ha, hd, -, -⟩ := h
  have hf := hM.loaded.fetchBytes_sub (offset := 40) (len := 2) (by omega) (by decide)
  refine ⟨?_, by rw [ha]; rfl, by rw [hd]; rfl⟩
  unfold AtSyscall
  rw [hm, hrip]
  exact hf

/-- **After a `write` answer**, LPS resumes at offset `22` with `rax = |ds|`. -/
theorem resume_regs {segs : List Segment} {k : X86FlagChoices.Choice} {ds : List Byte}
    (h : RegsAtM M 20 a d s x m) :
    RegsAtM M 22 (lenWord ds) d s x (resume (trapAt m k) (writeEff segs m k ds)) := by
  obtain ⟨hm, hrip, ha, hd, hs, hx⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [resume, x86AdvancePastSvc, x86ApplyEffectNative, trapAt, trapped,
    X86FlagChoices.completeState, writeEff, applyMemoryEffect, mkEffect,
    SyscallEffect.withCopyins, hm, hrip, codeBase]
  all_goals split <;> simp [hd, hs, hx]

/-- The source of the `write` at offset `j` of `hi`. -/
theorem hello_writeSource (hM : HelloMem M) (j : Nat) (hj : j < 2) :
    writeSource (viewByte M .read) (dataBase + BitVec.ofNat 64 j) (BitVec.ofNat 64 (2 - j)) =
      hiBytes.drop j := by
  have e2 : (zw (rwCountClamp 2#64)).toNat = 2 := by decide
  have e1 : (zw (rwCountClamp 1#64)).toNat = 1 := by decide
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · simp only [writeSource, readableBytes, Nat.sub_zero, BitVec.add_zero]
    rw [show BitVec.ofNat 64 2 = 2#64 from rfl, e2]
    simp [readableBytesAux, hM.data0, hM.data1, hiBytes]
  · simp only [writeSource, readableBytes]
    rw [show BitVec.ofNat 64 (2 - 1) = 1#64 from rfl, e1]
    simp [readableBytesAux, hM.data1, hiBytes]

theorem hello_source (hM : HelloMem M) {segs : List Segment} {bs : List Byte} (h : helloInvM M bs m)
    (k : X86FlagChoices.Choice) :
    writeSource (reqAt segs m k).mem ((reqAt segs m k).arg 1) ((reqAt segs m k).arg 2) = bs := by
  obtain ⟨j, hj, rfl, hm, -, -, -, hs, hx⟩ := h
  rw [reqAt_mem, reqAt_arg1, reqAt_arg2, hm, hs, hx]
  exact hello_writeSource hM j hj

theorem hello_nonempty {bs : List Byte} (h : helloInvM M bs m) : bs ≠ [] := by
  obtain ⟨j, hj, rfl, -⟩ := h
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [hiBytes]

theorem hello_chan {segs : List Segment} {e : Silmaril.Process.LPS.Model} {ch : Word}
    (hfd : fdLookup e.fds 1 = some (.channel ch)) {bs : List Byte} (h : helloInvM M bs m)
    (k : X86FlagChoices.Choice) :
    fdLookup e.fds (fd32 ((reqAt segs m k).arg 0)) = some (.channel ch) := by
  obtain ⟨j, -, -, -, -, -, hd, -, -⟩ := h
  rw [reqAt_arg0, hd]
  exact hfd

/-- **`writeArm` handles the loop's `syscall`.** -/
theorem hello_handles (hM : HelloMem M) {segs : List Segment} {e : Silmaril.Process.LPS.Model}
    {ch : Word}
    (hfd : fdLookup e.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) {bs : List Byte}
    (h : helloInvM M bs m) (k : X86FlagChoices.Choice) :
    (writeArm segs).Handles (trapAt m k) e := by
  have hsrc := hello_source hM (segs := segs) h k
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


/-- **Bytes left**: from offset `22` back to the `write` syscall. -/
theorem loop_back (hM : HelloMem M) {s' x' : Word} (h : RegsAtM M 22 a 1#64 s x m)
    (hs : s + a = s') (hx : x - a = x')
    (hne : x' ≠ 0#64) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step (RegsAtM M 20 1#64 1#64 s' x') n m := by
  obtain ⟨m1, h1, r1⟩ := add_step hM h
  obtain ⟨m2, h2, r2, z2⟩ := sub_step hM r1
  have hz : m2.core.flags.zero = some false := by
    rw [z2, hx]
    simp [hne]
  obtain ⟨m3, h3, r3⟩ := jne_back hM r2 hz
  obtain ⟨m4, h4, r4⟩ := movEax1_step hM r3
  obtain ⟨m5, h5, r5⟩ := movEdi1_step hM r4
  rw [hs, hx] at r5
  exact safe_step h1 (safe_step h2 (safe_step h3 (safe_step h4 (safe_step h5 (safe_now r5)))))

/-- **No bytes left**: from offset `22` to the exit sequence. -/
theorem loop_out (hM : HelloMem M) (h : RegsAtM M 22 a 1#64 s x m) (hx : x - a = 0#64) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step (helloFinM M) n m := by
  obtain ⟨m1, h1, r1⟩ := add_step hM h
  obtain ⟨m2, h2, r2, z2⟩ := sub_step hM r1
  have hz : m2.core.flags.zero = some true := by
    rw [z2, hx]
    rfl
  obtain ⟨m3, h3, r3⟩ := jne_out hM r2 hz
  exact safe_step h1 (safe_step h2 (safe_step h3 (safe_now ⟨_, _, _, _, r3⟩)))

/-- The three short writes: `l` bytes written at offset `j` of `hi`. -/
theorem hello_after (hM : HelloMem M) {j l : Nat}
    (hjl : (j = 0 ∧ l = 1) ∨ (j = 0 ∧ l = 2) ∨ (j = 1 ∧ l = 1))
    (hR : RegsAtM M 22 (BitVec.ofNat 64 l) 1#64 (dataBase + BitVec.ofNat 64 j)
      (BitVec.ofNat 64 (2 - j)) m) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step (fun m' => if (hiBytes.drop j).drop l = [] then
      helloFinM M m' else helloInvM M ((hiBytes.drop j).drop l) m') n m := by
  rcases hjl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : (hiBytes.drop 0).drop 1 = [0x69] := rfl
    simp only [e, reduceCtorEq, ↓reduceIte]
    exact fun n => Silmaril.Machine.X86.Safe.safeN_post (fun m' hm' => ⟨1, by omega, rfl, hm'⟩)
      (loop_back hM hR (by decide) (by decide) (by decide) n)
  · have e : (hiBytes.drop 0).drop 2 = [] := rfl
    simp only [e, ↓reduceIte]
    exact loop_out hM hR (by decide)
  · have e : (hiBytes.drop 1).drop 1 = [] := rfl
    simp only [e, ↓reduceIte]
    exact loop_out hM hR (by decide)

/-- **After a short write of `ds`**, the loop runs to the rest, or to the exit sequence. -/
theorem hello_next (hM : HelloMem M) {segs : List Segment} {bs : List Byte} (h : helloInvM M bs m)
    (k : X86FlagChoices.Choice) (ds : List Byte) (h1 : 1 ≤ ds.length) (hp : ds <+: bs) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step
      (fun m' => if bs.drop ds.length = [] then helloFinM M m'
        else helloInvM M (bs.drop ds.length) m')
      n (resume (trapAt m k) (writeEff segs m k ds)) := by
  obtain ⟨j, hj, hbs, hr⟩ := h
  have hR : RegsAtM M 22 (lenWord ds) 1#64 (dataBase + BitVec.ofNat 64 j) (BitVec.ofNat 64 (2 - j))
      (resume (trapAt m k) (writeEff segs m k ds)) := resume_regs hr
  have hlen : lenWord ds = BitVec.ofNat 64 ds.length := by simp [lenWord, zw]
  have hle : ds.length ≤ 2 - j := by
    have hl : ds.length ≤ (hiBytes.drop j).length := hbs ▸ hp.length_le
    simpa only [List.length_drop, hiBytes, List.length_cons, List.length_nil] using hl
  have hjl : (j = 0 ∧ ds.length = 1) ∨ (j = 0 ∧ ds.length = 2) ∨ (j = 1 ∧ ds.length = 1) := by
    omega
  exact hbs ▸ hello_after hM hjl (hlen ▸ hR)

/-- From any state at offset `0` in memory `M` to the `write` of `hi`. -/
theorem hello_toWrite (hM : HelloMem M) {m0 : MState} (hm : m0.memory = M)
    (hrip : m0.core.rip = codeBase) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step (helloInvM M hiBytes) n m0 := by
  have r0 : RegsAtM M 0 (m0.core.read .rax) (m0.core.read .rdi) (m0.core.read .rsi)
      (m0.core.read .rdx) m0 := ⟨hm, by rw [hrip]; decide, rfl, rfl, rfl, rfl⟩
  obtain ⟨m1, h1, r1⟩ := movEsi_step hM r0
  obtain ⟨m2, h2, r2⟩ := movEdx_step hM r1
  obtain ⟨m3, h3, r3⟩ := movEax1_step hM r2
  obtain ⟨m4, h4, r4⟩ := movEdi1_step hM r3
  have hi : helloInvM M hiBytes m4 :=
    ⟨0, by omega, rfl, by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using r4⟩
  exact safe_step h1 (safe_step h2 (safe_step h3 (safe_step h4 (safe_now hi))))

/-- From the exit sequence to `exit(0)`. -/
theorem hello_toExit (hM : HelloMem M) (h : helloFinM M m) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step ExitOk n m := by
  obtain ⟨a, d, s, x, r0⟩ := h
  obtain ⟨m1, h1, r1⟩ := movEax60_step hM r0
  obtain ⟨m2, h2, r2⟩ := movEdi0_step hM r1
  exact safe_step h1 (safe_step h2 (safe_now (regsAt_exit hM r2)))

/-! ## The runtime -/

/-- **The program is a runtime of `hello`** from every state `m0` at `codeBase` whose memory
holds it, for every LPS model whose descriptor `1` is the live channel `ch`. -/
def helloLoopAt (segs : List Segment) (hM : HelloMem M) {m0 : MState} (hm : m0.memory = M)
    (hrip : m0.core.rip = codeBase) {e : Silmaril.Process.LPS.Model} {ch : Word}
    (hfd : fdLookup e.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    HelloLoop Silmaril.Machine.X86.Open.step segs ch e where
  Inv := helloInvM M
  Fin := helloFinM M
  nonempty _ _ h := hello_nonempty h
  trap _ _ h := by
    obtain ⟨_, _, _, hr⟩ := h
    exact regsAt_trap hM hr
  handles _ _ h k := hello_handles hM hfd hch h k
  chan _ _ h k := hello_chan hfd h k
  source _ _ h k := hello_source hM h k
  next _ _ h k ds h1 hp := hello_next hM h k ds h1 hp
  start := m0
  toWrite := hello_toWrite hM hm hrip
  toExit _ h := hello_toExit hM h

end Silmaril.Wasi.Runtime.Launch
