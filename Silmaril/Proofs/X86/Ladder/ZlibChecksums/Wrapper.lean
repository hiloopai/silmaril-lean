module

public import Silmaril.X86.BlockCert.Ext8.Instr.Thms
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Open9.Thms

/-!
# Tail-call wrappers `mov %edx,%edx; jmp f`

zlib's `crc32` and `adler32` are `uInt` wrappers of `crc32_z`/`adler32_z`: gcc -O2 compiles each
to `mov %edx,%edx; jmp rel32` (zero-extend the length, tail-call). `wrap_total`: a wrapper is
totally correct for any spec `W` that, after the two instructions, is the callee's spec `S`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86 Silmaril.X86.BlockCert8

/-- The wrapper's listing. -/
def wrapL (rel : BitVec 32) : List LI :=
  [(.base (.mov .d (.reg .rdx) .rdx), 2), (.base (.jmp rel), 5)]

/-- The state after the wrapper's two instructions. -/
def after (rel : BitVec 32) (m : MState) : MState :=
  ⟨{ m.core.write .rdx ((m.core.read .rdx).setWidth 32 |>.setWidth 64) with
      rip := m.core.rip + 7#64 + rel.signExtend 64 }, m.memory⟩

theorem run_wrap (rel : BitVec 32) (m : MState) : run8 (wrapL rel) m = some (after rel m) := by
  simp [wrapL, run8, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, after,
    BitVec.add_assoc]

theorem after_read (rel : BitVec 32) (m : MState) {r : Reg} (h : r ≠ .rdx) :
    (after rel m).core.read r = m.core.read r := by
  show (m.core.write .rdx _).read r = _
  exact Silmaril.X86.State.read_write_other _ _ _ _ h

theorem after_retOf (rel : BitVec 32) (m : MState) :
    FnContract.retOf (after rel m).core (after rel m).memory = FnContract.retOf m.core m.memory := by
  simp only [FnContract.retOf, after_read rel m (r := .rsp) (by decide)]; rfl

/-- **Tail-call wrappers.** -/
theorem wrap_total {code : List Byte} {rel : BitVec 32}
    (hl : listing8 code 0 (wrapL rel) = true) (S W : FnContract.Spec MState)
    (hS : S.Total Open.isa)
    (hW : ∀ m, W.entry m → Loaded m.memory m.core.rip code ∧ S.entry (after rel m))
    (hfp : ∀ m a, W.entry m → S.footprint (after rel m) a → W.footprint m a)
    (hpost : ∀ m t, W.entry m → S.post (after rel m) t → W.post m t) :
    W.Total Open.isa := by
  intro m hlive hab he
  obtain ⟨hlo, hse⟩ := hW m he
  have hr := (run8_open (base := m.core.rip) (o := 0) hl hlo (by simp) (run_wrap rel m)).1
  have hab' : FnContract.AbiEntry (after rel m).core (after rel m).memory := by
    refine ⟨?_, ?_⟩
    · rw [after_read rel m (by decide)]; exact hab.aligned
    · rw [after_read rel m (by decide), after_retOf]; exact hab.returnAddress
  obtain ⟨t, hrt, res⟩ := hS (after rel m) trivial hab' hse
  refine ⟨t, hr.trans hrt, rfl, ⟨?_, ?_, ?_⟩, ?_, hpost m t he res.post⟩
  · rw [res.abi.pc, after_retOf]
  · rw [res.abi.stack, after_read rel m (by decide)]
  · intro r hr'
    rw [res.abi.calleeSaved r hr', after_read rel m]
    simp [Silmaril.X86.sysv64_calleeSaved] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact res.frame.mono (fun a ha => hfp m a he ha)

/-- **Tail-call wrappers** on the open machine over `Ext9` (the callee may use `Ext9` forms;
the wrapper's two instructions are `Ext` forms, run on `Open` and transported). -/
theorem wrap_total9 {code : List Byte} {rel : BitVec 32}
    (hl : listing8 code 0 (wrapL rel) = true) (S W : FnContract.Spec MState)
    (hS : S.Total Open9.isa)
    (hW : ∀ m, W.entry m → Loaded m.memory m.core.rip code ∧ S.entry (after rel m))
    (hfp : ∀ m a, W.entry m → S.footprint (after rel m) a → W.footprint m a)
    (hpost : ∀ m t, W.entry m → S.post (after rel m) t → W.post m t) :
    W.Total Open9.isa := by
  intro m hlive hab he
  obtain ⟨hlo, hse⟩ := hW m he
  have hr := (run8_open (base := m.core.rip) (o := 0) hl hlo (by simp) (run_wrap rel m)).1
  have hab' : FnContract.AbiEntry (after rel m).core (after rel m).memory := by
    refine ⟨?_, ?_⟩
    · rw [after_read rel m (by decide)]; exact hab.aligned
    · rw [after_read rel m (by decide), after_retOf]; exact hab.returnAddress
  obtain ⟨t, hrt, res⟩ := hS (after rel m) trivial hab' hse
  refine ⟨t, (Open9.reaches_of_open hr).trans hrt, rfl, ⟨?_, ?_, ?_⟩, ?_, hpost m t he res.post⟩
  · rw [res.abi.pc, after_retOf]
  · rw [res.abi.stack, after_read rel m (by decide)]
  · intro r hr'
    rw [res.abi.calleeSaved r hr', after_read rel m]
    simp [Silmaril.X86.sysv64_calleeSaved] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact res.frame.mono (fun a ha => hfp m a he ha)

end Silmaril.Proofs.X86.Ladder.ZlibChecksums
