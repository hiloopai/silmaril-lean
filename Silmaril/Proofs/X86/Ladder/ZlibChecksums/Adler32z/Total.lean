module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Next
public import Silmaril.X86.SegVC.Mono

/-!
# `adler32_z`: assembling the segment VCs into a total contract on `Open9`

`SegVC.sound` over `Open9.isa` (listing `adlerListing`, cut points `cuts c`, stops `stops c`,
budget `200`) gives a run from the entry to one of the four `ret`s with `Q`; one more
`Open9` step executes the `ret`. `total_of` takes the segment VCs as hypotheses (`VcA`, `VcB`,
`VcC`, `VcD`, `VcE`, `VcP`), so this file is independent of how (and whether) each is proved.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.SegVC (wpN)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums

/-- The segment VC of a cut point at offset `o` with invariant `I` and pointer register `r`. -/
def VcAt (o : Nat) (I : Ctx → MState → Prop) (r : Reg) (K : Nat) : Prop :=
  ∀ (c : Ctx) (s : MState), Loaded s.memory c.base adler32zCode →
    s.core.rip = c.base + BitVec.ofNat 64 o → I c s →
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base (some (meas c r s)) K o s

def VcA (K : Nat) : Prop := VcAt 128 InvA .r8 K
def VcB (K : Nat) : Prop := VcAt 517 InvB .rcx K
def VcC (K : Nat) : Prop := VcAt 739 InvC .rcx K
def VcD (K : Nat) : Prop := VcAt 992 InvD .r8 K

/-- The segment VC after the prologue (`0x20`). -/
def VcP (K : Nat) : Prop :=
  ∀ (c : Ctx) (s : MState), Loaded s.memory c.base adler32zCode →
    s.core.rip = c.base + BitVec.ofNat 64 32 → InvP c s →
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base (some (c.n + 1)) K 32 s

/-- The segment VC of the entry. -/
def VcE (K : Nat) : Prop :=
  ∀ (c : Ctx), c.Pre → Loaded c.m0.memory c.base adler32zCode →
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base none K 0 c.m0

theorem VcAt.mono {o : Nat} {I : Ctx → MState → Prop} {r : Reg} {K K' : Nat} (h : VcAt o I r K)
    (hK : K ≤ K') : VcAt o I r K' :=
  fun c s hl hrip hI => Silmaril.X86.SegVC.wpN_mono hK (h c s hl hrip hI)

/-- The `ret` at a stop. -/
theorem ret_at {o : Nat} (ho : o = 502 ∨ o = 628 ∨ o = 690 ∨ o = 1122) :
    List.lookup (β := Ext9.Instr × Nat) o adlerListing = some (.ext8 (.base .ret), 1) := by
  rcases ho with rfl | rfl | rfl | rfl <;> rfl

/-- The return step: from a stop with `Q`, one `Open9` step reaches the System V exit. -/
theorem ret_step {c : Ctx} {o : Nat} {t : MState} (ho : o = 502 ∨ o = 628 ∨ o = 690 ∨ o = 1122)
    (hq : Q c t) (hrip : t.core.rip = c.base + BitVec.ofNat 64 o)
    (hl : Loaded t.memory c.base adler32zCode) :
    ∃ t', Open9.step t = some t' ∧ (adler32zContract c.base).Result Open9.isa c.m0 t' := by
  have hP := hq.pre
  obtain ⟨hdec, hfit⟩ := Silmaril.X86.SegVC.valid_entry (I := Open9.isa) adlerListing_valid
    (ret_at ho)
  have hrd : t.memory.readBytes (t.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [FnContract.retOf c.m0.core c.m0.memory]) := by
    rw [hq.sp, hq.mem.readBytes_eq (by have := hP.room; simp only [Ctx.lo, Ctx.r0] at *; omega)]
    exact hP.abi.returnAddress
  have hpop := Silmaril.X86.popWord_of_readBytes hrd
  refine ⟨_, Open9.step_of_listed hl hrip hfit hdec (by
    show Silmaril.X86.Ext.exec .ret t.core t.memory 1 = _
    simp only [Silmaril.X86.Ext.exec, hpop]; rfl), ?_⟩
  refine ⟨rfl, ⟨rfl, ?_, ?_⟩, ?_, ?_⟩
  · show (t.core.write .rsp (t.core.read .rsp + 8#64)).read .rsp = _
    rw [Silmaril.X86.State.read_write_same, hq.sp]; rfl
  · intro r hr
    show (t.core.write .rsp (t.core.read .rsp + 8#64)).read r = _
    simp [Silmaril.X86.sysv64_calleeSaved] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [Silmaril.X86.State.read_write_other _ _ _ _ (by decide)]
    exacts [hq.rbx, hq.rbp, hq.r12, hq.r13, hq.r14, hq.r15]
  · show c.m0.memory.WritesWithin t.memory _
    refine hq.mem.mono fun a ha => ?_
    simp only [Ctx.area, Ctx.lo, Ctx.r0] at ha
    show adlerFrame c.m0 a
    have := hP.room
    simp only [adlerFrame, Ctx.r0] at this ⊢; omega
  · show t.core.read .rax = _
    rw [hq.rax]; rfl

theorem stops_lookup {c : Ctx} {o : Nat} {q : MState → Prop} (hq : (stops c).lookup o = some q) :
    (o = 502 ∨ o = 628 ∨ o = 690 ∨ o = 1122) ∧ q = Q c := by
  unfold stops at hq
  simp only [List.lookup_cons, List.lookup_nil] at hq
  by_cases h1 : o = 502
  · subst h1; simp only [Nat.reduceBEq, Option.some.injEq] at hq; exact ⟨by omega, hq.symm⟩
  by_cases h2 : o = 628
  · subst h2; simp only [Nat.reduceBEq, Option.some.injEq] at hq; exact ⟨by omega, hq.symm⟩
  by_cases h3 : o = 690
  · subst h3; simp only [Nat.reduceBEq, Option.some.injEq] at hq; exact ⟨by omega, hq.symm⟩
  by_cases h4 : o = 1122
  · subst h4; simp only [Nat.reduceBEq, Option.some.injEq] at hq; exact ⟨by omega, hq.symm⟩
  have e1 : (o == 502) = false := by simpa using h1
  have e2 : (o == 628) = false := by simpa using h2
  have e3 : (o == 690) = false := by simpa using h3
  have e4 : (o == 1122) = false := by simpa using h4
  simp only [e1, e2, e3, e4, reduceCtorEq] at hq

/-- The segment VC of the cut point `o` for one call context `c`. -/
def VcAtC (c : Ctx) (o : Nat) (I : Ctx → MState → Prop) (r : Reg) (K : Nat) : Prop :=
  ∀ (s : MState), Loaded s.memory c.base adler32zCode →
    s.core.rip = c.base + BitVec.ofNat 64 o → I c s →
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base (some (meas c r s)) K o s

/-- **One call of `adler32_z` on `Open9`**, given the segment VCs, the two loop VCs only for this
call's context. -/
theorem run_of {KA KB KC KD KE KP : Nat} {entry : Word} {m0 : MState}
    (hA : VcAtC ⟨entry, m0⟩ 128 InvA .r8 KA) (hB : VcB KB)
    (hC : VcAtC ⟨entry, m0⟩ 739 InvC .rcx KC) (hD : VcD KD)
    (hE : VcE KE) (hPr : VcP KP) (hab : FnContract.AbiEntry m0.core m0.memory)
    (he : (adler32zContract entry).entry m0) :
    ∃ t, Silmaril.Machine.Execution.Reaches Open9.isa.step m0 t ∧
      (adler32zContract entry).Result Open9.isa m0 t := by
  let c : Ctx := ⟨entry, m0⟩
  have hP : c.Pre := pre_of hab he
  let K := KA + KB + KC + KD + KE + KP
  have hvc : Silmaril.X86.SegVC.vc Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] []
      entry 0 (fun s => s = m0) K := by
    refine ⟨fun s _ hl hrip hpre => ?_, fun oc hoc s _ hl hrip hinv => ?_⟩
    · subst hpre
      exact Silmaril.X86.SegVC.wpN_mono (by omega) (hE c hP hl)
    · simp only [cuts, List.mem_cons, List.not_mem_nil, or_false] at hoc
      rcases hoc with rfl | rfl | rfl | rfl | rfl
      · exact Silmaril.X86.SegVC.wpN_mono (by omega) (hPr c s hl hrip hinv)
      · exact Silmaril.X86.SegVC.wpN_mono (by omega) (hA s hl hrip hinv)
      · exact (VcAt.mono hB (by omega)) c s hl hrip hinv
      · exact Silmaril.X86.SegVC.wpN_mono (by omega) (hC s hl hrip hinv)
      · exact (VcAt.mono hD (by omega)) c s hl hrip hinv
  obtain ⟨o, q, t, hq, hqt, hr, hrip, hl, _⟩ :=
    Silmaril.X86.SegVC.sound adlerListing_valid hvc m0 trivial hP.loaded
      (by simpa using hP.rip) rfl
  have ho := stops_lookup hq
  obtain ⟨ho, rfl⟩ := ho
  obtain ⟨t', hs, hres⟩ := ret_step (c := c) ho hqt hrip hl
  exact ⟨t', hr.trans ⟨1, by simp [Silmaril.Machine.Execution.run, hs]⟩, hres⟩

/-- **`adler32_z` is totally correct on `Open9`, given its segment VCs.** -/
theorem total_of {KA KB KC KD KE KP : Nat} (hA : VcA KA) (hB : VcB KB) (hC : VcC KC) (hD : VcD KD)
    (hE : VcE KE) (hPr : VcP KP) (entry : Word) : (adler32zContract entry).Total Open9.isa :=
  fun _ _ hab he => run_of (fun s => hA _ s) hB (fun s => hC _ s) hD hE hPr hab he

/-- Below `16` bytes no state satisfies the loop invariants `InvA` (`0x80`) or `InvC` (`0x2e3`),
so their VCs hold vacuously for such a call. -/
theorem vcA_short {c : Ctx} (h : c.n < 16) (K : Nat) : VcAtC c 128 InvA .r8 K := by
  rintro s - - ⟨-, k, j, hk, -⟩
  simp only [NMAX] at hk; omega

theorem vcC_short {c : Ctx} (h : c.n < 16) (K : Nat) : VcAtC c 739 InvC .rcx K := by
  rintro s - - ⟨-, k, t, hk, -⟩
  omega

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
