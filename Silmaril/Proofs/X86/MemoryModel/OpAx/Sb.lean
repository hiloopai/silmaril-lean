module

public import Silmaril.X86.MemoryModel.OpAx.Defs
public import Silmaril.Proofs.X86.MemoryModel.OpAx.Paired
public import Silmaril.Proofs.X86.MemoryModel.OpAx.Counter

/-!
# Store buffering: the general theorem is not an SC theorem

A non-vacuity check for `run_explains_paired`. Program `sbP` (SB): thread 0 stores `1` at 0
and loads 1, thread 1 stores `1` at 1 and loads 0. Its hypotheses hold (`sb_threadsOk`,
`sb_cells`), the machine reaches the weak outcome (both loads return `0`, `sb_run`), so the
general theorem yields an x86-TSO candidate for it (`sb_explained`), while no SC candidate
explains it (`sb_not_sc`: `W0 →po R0 →fr W1 →po R1 →fr W0`).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.OpAx.Proofs

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.OpAx
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush Byte Mem readView enqueue xembed
  writeMem)
open Silmaril.X86.MemoryModel.Litmus (ACfg AStep)
open Relation

/-- SB: `st [0] 1; ld [1]` against `st [1] 1; ld [0]`, both loads returning `0`. -/
def sbP : List (List (XEvent Nat)) :=
  [[.store 0 0 [1], .load 0 1 [0]], [.store 1 1 [1], .load 1 0 [0]]]

def sbV0 : Ev := { tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] }
def sbR0 : Ev := { tid := 0, pos := 2, act := .read, addr := 1, size := 1 }
def sbV1 : Ev := { tid := 1, pos := 0, act := .write, addr := 1, size := 1, data := [1] }
def sbR1 : Ev := { tid := 1, pos := 2, act := .read, addr := 0, size := 1 }

theorem sb_units : progUnits sbP = [(sbV0, []), (sbR0, [0]), (sbV1, []), (sbR1, [0])] := by
  decide

theorem sb_threadsOk : ThreadsOk sbP := by
  intro i es h ev hev
  match i, h with
  | 0, h =>
    simp only [sbP, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp at hev; rcases hev with rfl | rfl <;> rfl
  | 1, h =>
    simp only [sbP, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp at hev; rcases hev with rfl | rfl <;> rfl
  | n + 2, h => simp [sbP] at h

theorem sb_cells : ThreadCells sbP := by
  intro i es h ev₁ hev₁ ev₂ hev₂ p hp q hq ⟨y, h1, h2, h3, h4⟩
  match i, h with
  | 0, h =>
    simp only [sbP, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp at hev₁ hev₂
    rcases hev₁ with rfl | rfl <;> rcases hev₂ with rfl | rfl <;>
      simp [footOf] at hp hq <;> subst hp hq <;> simp at h1 h2 h3 h4 ⊢ <;> omega
  | 1, h =>
    simp only [sbP, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp at hev₁ hev₂
    rcases hev₁ with rfl | rfl <;> rcases hev₂ with rfl | rfl <;>
      simp [footOf] at hp hq <;> subst hp hq <;> simp at h1 h2 h3 h4 ⊢ <;> omega
  | n + 2, h => simp [sbP] at h

/-- The states of the run: both stores buffered, both loads from memory, then both flushes. -/
def sb0 : XState Nat := xembed Tso.Litmus.zeroMem
def sb1 : XState Nat := enqueue sb0 0 0 [1]
def sb2 : XState Nat := enqueue sb1 1 1 [1]
def sb3 : XState Nat := ⟨writeMem sb2.memory 0 [1], Function.update sb2.buffer 0 []⟩
def sb4 : XState Nat := ⟨writeMem sb3.memory 1 [1], Function.update sb3.buffer 1 []⟩

theorem sb_run : Run sbP Tso.Litmus.zeroMem sb4 := by
  refine ⟨?_, fun t => ?_⟩
  · have s1 : AStep ⟨sbP, sb0⟩ ⟨[[.load 0 1 [0]], [.store 1 1 [1], .load 1 0 [0]]], sb1⟩ :=
      AStep.ev sbP sb0 sb1 0 (.store 0 0 [1]) [.load 0 1 [0]] rfl (XStep.store _ _ _ _)
    have s2 : AStep ⟨[[.load 0 1 [0]], [.store 1 1 [1], .load 1 0 [0]]], sb1⟩
        ⟨[[.load 0 1 [0]], [.load 1 0 [0]]], sb2⟩ :=
      AStep.ev _ sb1 sb2 1 (.store 1 1 [1]) [.load 1 0 [0]] rfl (XStep.store _ _ _ _)
    have s3 : AStep ⟨[[.load 0 1 [0]], [.load 1 0 [0]]], sb2⟩ ⟨[[], [.load 1 0 [0]]], sb2⟩ :=
      AStep.ev _ sb2 sb2 0 (.load 0 1 [0]) [] rfl (XStep.load _ _ _ _ (by decide))
    have s4 : AStep ⟨[[], [.load 1 0 [0]]], sb2⟩ ⟨[[], []], sb2⟩ :=
      AStep.ev _ sb2 sb2 1 (.load 1 0 [0]) [] rfl (XStep.load _ _ _ _ (by decide))
    have s5 : AStep ⟨[[], []], sb2⟩ ⟨[[], []], sb3⟩ :=
      AStep.flush _ sb2 sb3 (XFlush.head sb2 0 0 [1] [] (by decide))
    have s6 : AStep ⟨[[], []], sb3⟩ ⟨[[], []], sb4⟩ :=
      AStep.flush _ sb3 sb4 (XFlush.head sb3 1 1 [1] [] (by decide))
    exact ((((((ReflTransGen.refl.tail s1).tail s2).tail s3).tail s4).tail s5).tail s6)
  · simp only [sb4, sb3, sb2, sb1, sb0, enqueue, xembed, Function.update]
    split <;> simp_all

/-- The general theorem applies to SB's weak outcome. -/
theorem sb_explained :
    ∃ x, Explains Exec.Tso sbP Tso.Litmus.zeroMem sb4 x ∧ RmwPaired x :=
  run_explains_paired sb_threadsOk sb_cells sb_run

/-- No SC candidate explains SB's weak outcome. -/
theorem sb_not_sc (x : Exec) : ¬ Explains Exec.Sc sbP Tso.Litmus.zeroMem sb4 x := by
  rintro ⟨us, hperm, hevs, hsc, hreads, hrfW, -, -, -⟩
  rw [sb_units] at hperm
  have hfst : (us.map Prod.fst).Perm [sbV0, sbR0, sbV1, sbR1] := by
    have := hperm.map Prod.fst; simpa using this
  have hlenU : x.n = (us.map Prod.fst).length := by simp [Exec.n, hevs]
  have hevN : ∀ w (hw : w < (us.map Prod.fst).length), x.evN w = (us.map Prod.fst)[w] := by
    intro w hw
    simp only [Exec.evN, hevs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw,
      Option.getD_some]
  have hcases : ∀ w < x.n, x.evN w = sbV0 ∨ x.evN w = sbR0 ∨ x.evN w = sbV1 ∨ x.evN w = sbR1 := by
    intro w hw
    rw [hlenU] at hw
    rw [hevN w hw]
    have := hfst.mem_iff.mp (List.getElem_mem hw)
    simpa using this
  -- locate the four units
  have find : ∀ e, e ∈ [sbV0, sbR0, sbV1, sbR1] → ∃ i, ∃ h : i < x.n, x.evN i = e := by
    intro e he
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp (hfst.mem_iff.mpr he)
    exact ⟨i, by rw [hlenU]; exact hi, by rw [hevN i hi]; exact hget⟩
  obtain ⟨a, ha, hEa⟩ := find sbV0 (by simp)
  obtain ⟨b, hb, hEb⟩ := find sbR0 (by simp)
  obtain ⟨c, hc, hEc⟩ := find sbV1 (by simp)
  obtain ⟨d, hd, hEd⟩ := find sbR1 (by simp)
  -- what a read returns
  have readOf : ∀ r < x.n, (x.evN r).isR = true → x.readBytes (fun y => (Tso.Litmus.zeroMem y).getD 0) r = [0] := by
    intro r hr hR
    rw [hreads r hr hR]
    have hr' : r < us.length := by simpa [hlenU] using hr
    have hfe : (us[r]).1 = x.evN r := by
      rw [hevN r (by simpa using hr')]; simp
    have hmem : us[r] ∈ us := List.getElem_mem hr'
    have hall := hperm.mem_iff.mp hmem
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
    generalize us[r] = p at hfe hall ⊢
    obtain ⟨e, bs⟩ := p
    simp only at hfe ⊢
    subst hfe
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hall
    rcases hall with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [h1] at hR; simp [sbV0, Ev.isR] at hR
    · exact h2
    · rw [h1] at hR; simp [sbV1, Ev.isR] at hR
    · exact h2
  -- a read returning 0 takes it from the initial state
  have rfNone : ∀ r < x.n, (x.evN r).isR = true → ∀ y, (x.evN r).bytes = [y] → x.rf r y = none := by
    intro r hr hR y hy
    have h0 := readOf r hr hR
    simp only [Exec.readBytes, hy, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h0
    cases h : x.rf r y with
    | none => rfl
    | some w =>
      obtain ⟨hwn, hwW, hwc⟩ := hrfW _ _ _ h
      simp only [Exec.readByte, h] at h0
      rcases hcases w hwn with h' | h' | h' | h' <;> rw [h'] at hwW hwc h0
      · obtain rfl : y = 0 := by
          simp only [sbV0, Ev.covers] at hwc
          have h1 := of_decide_eq_true (Bool.and_eq_true_iff.mp hwc).1
          have h2 := of_decide_eq_true (Bool.and_eq_true_iff.mp hwc).2
          omega
        simp [sbV0, Ev.byte] at h0
      · simp [sbR0, Ev.isW] at hwW
      · obtain rfl : y = 1 := by
          simp only [sbV1, Ev.covers] at hwc
          have h1 := of_decide_eq_true (Bool.and_eq_true_iff.mp hwc).1
          have h2 := of_decide_eq_true (Bool.and_eq_true_iff.mp hwc).2
          omega
        simp [sbV1, Ev.byte] at h0
      · simp [sbR1, Ev.isW] at hwW
  have hrb : x.rf b 1 = none := rfNone b hb (by rw [hEb]; rfl) 1 (by rw [hEb]; decide)
  have hrd : x.rf d 0 = none := rfNone d hd (by rw [hEd]; rfl) 0 (by rw [hEd]; decide)
  -- the cycle
  have e1 : x.scRel ⟨a, ha⟩ ⟨b, hb⟩ = true := by
    simp only [Exec.scRel, BRel.union_iff]; left
    simp [Exec.po, ev_eq, hEa, hEb, sbV0, sbR0]
  have e2 : x.scRel ⟨b, hb⟩ ⟨c, hc⟩ = true := by
    simp only [Exec.scRel, BRel.union_iff]; right
    refine BRel.seq_of_left x.sm_refl ?_
    simp only [Exec.com, BRel.union_iff]; right; right
    simp only [Exec.frR, ev_eq, hEb, hEc]
    simp [sbV1, sbR0, Ev.isW, Ev.isR, Ev.bytes, Ev.covers, hrb]
  have e3 : x.scRel ⟨c, hc⟩ ⟨d, hd⟩ = true := by
    simp only [Exec.scRel, BRel.union_iff]; left
    simp [Exec.po, ev_eq, hEc, hEd, sbV1, sbR1]
  have e4 : x.scRel ⟨d, hd⟩ ⟨a, ha⟩ = true := by
    simp only [Exec.scRel, BRel.union_iff]; right
    refine BRel.seq_of_left x.sm_refl ?_
    simp only [Exec.com, BRel.union_iff]; right; right
    simp only [Exec.frR, ev_eq, hEd, hEa]
    simp [sbV0, sbR1, Ev.isW, Ev.isR, Ev.bytes, Ev.covers, hrd]
  exact hsc.2 _ ((((TransGen.single (r := x.scRel.Holds) e1).tail e2).tail e3).tail e4)

end Silmaril.X86.MemoryModel.OpAx.Proofs
