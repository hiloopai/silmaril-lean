module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.MkHyp

/-!
# Localisation: the fragment replays sequentially

`frag_replay`: in a candidate whose units are `A ++ F ++ C` with `F` the
fragment's units (on the cells, which nothing else touches), consistent under XL, the fragment's
actions replay sequentially from the initial memory, to the final bytes of the restricted
candidate (the `oneSem_iff` on `Surg.rexec`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace actUnits threadUnits accUnits units rmwPairs)

theorem trOf_acts' (as : List XAct) : (trOf as).acts = as := by
  simp [trOf, Silmaril.X86.Litmus.Trace.acts]

/-- One thread of cell actions does not tear. -/
theorem units_one {cs : List (Nat × Nat)} (hcs : CellsOk cs) (as : List XAct)
    (h : ∀ a ∈ as, (∃ f, a.ev.kind = .fence f) ∨ (a.ev.addr, a.ev.size) ∈ cs) :
    units [trOf as] = threadUnits 0 0 as := by
  have hacc : accUnits [trOf as] = threadUnits 0 0 as := by
    simp [accUnits, trOf_acts']
  have hC : ∀ v ∈ threadUnits 0 0 as, UC cs v :=
    threadUnits_all 0 _ fun a ha p => actUnits_UC (h a ha) 0 p
  rw [units_eq', hacc]
  exact flatMap_sp_self _ fun v hv => tear_C hcs (fun w hw => .inr (hC w hw)) (hC v hv)

theorem relab_rt (i p1 : Nat) (as : List XAct) (k : Nat) (h1 : k < (threadUnits 0 0 as).length)
    (h : k < (threadUnits i p1 as).length) :
    (threadUnits 0 0 as)[k] = ({ ((threadUnits i p1 as)[k]).1 with tid := 0, pos := k },
      ((threadUnits i p1 as)[k]).2) := by
  have e : (threadUnits i p1 as)[k] = rt i p1 ((threadUnits 0 0 as)[k]) := by
    have := threadUnits_rt i p1 as
    simp only [List.getElem_of_eq this, List.getElem_map]
  rw [e]
  obtain ⟨ht, hp⟩ := threadUnits_pos 0 0 as k h1
  generalize (threadUnits 0 0 as)[k] = u at ht hp ⊢
  obtain ⟨⟨tid, pos, act, addr, size, aa, as', lk, ann, data⟩, d⟩ := u
  simp only at ht hp
  subst ht hp
  simp [rt]

theorem tame_of_UC {cs : List (Nat × Nat)} (hcs : CellsOk cs) {F : List (Ev × List Byte)}
    (hF : ∀ u ∈ F, UC cs u) : ∀ u ∈ F, u.1.isM = true → u.1.singleCopy = true ∧
      ∀ v ∈ F, v.1.isM = true → u.1.accOverlap v.1 = true →
        u.1.accAddr = v.1.accAddr ∧ u.1.accSize = v.1.accSize := by
  intro u hu hM
  obtain ⟨h1, h2, h3⟩ := hF u hu hM
  refine ⟨?_, fun v hv hvM hov => ?_⟩
  · obtain ⟨hs, ha⟩ := hcs.1 _ h3
    simp only [Ev.singleCopy, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ← h1, ← h2]
    simp only at hs ha
    exact ⟨by omega, ha⟩
  · obtain ⟨g1, g2, g3⟩ := hF v hv hvM
    rcases hcs.2 _ h3 _ g3 with h | h | h
    · simp only [Prod.mk.injEq] at h
      rw [← h1, ← h2, ← g1, ← g2]; exact h
    · simp only [Ev.accOverlap, Bool.and_eq_true, decide_eq_true_eq] at hov
      simp only at h; omega
    · simp only [Ev.accOverlap, Bool.and_eq_true, decide_eq_true_eq] at hov
      simp only at h; omega

/-- The restriction's hypotheses for the fragment's actions. -/
theorem rhyp_frag {S : Surg} {cs : List (Nat × Nat)} (hcs : CellsOk cs) (a2 : List XAct)
    (hF : S.F = threadUnits S.i S.p1 a2)
    (hc : ∀ a ∈ a2, (∃ f, a.ev.kind = .fence f) ∨ (a.ev.addr, a.ev.size) ∈ cs) :
    S.RHyp (units [trOf a2]) := by
  have hF1 := units_one hcs a2 hc
  have hUC : ∀ u ∈ S.F, UC cs u := by
    rw [hF]; exact threadUnits_all _ _ fun a ha p => actUnits_UC (hc a ha) _ p
  exact {
    len := by rw [hF1, hF, length_threadUnits S.i S.p1]
    relab := fun k h1 h => by
      rw [List.getElem_of_eq hF1]
      have h1' : k < (threadUnits 0 0 a2).length := by rwa [hF1] at h1
      have h' : k < (threadUnits S.i S.p1 a2).length := by rwa [hF] at h
      rw [relab_rt S.i S.p1 a2 k h1' h']
      simp only [List.getElem_of_eq hF]
    posF := fun k h => by
      have h' : k < (threadUnits S.i S.p1 a2).length := by rwa [hF] at h
      simp only [List.getElem_of_eq hF]
      exact threadUnits_pos S.i S.p1 a2 k h'
    tameF := tame_of_UC hcs hUC }

/-- **The fragment replays from the initial memory.** -/
theorem frag_replay {S : Surg} {x : Exec} {m0 : Mem} {cs : List (Nat × Nat)} (hcs : CellsOk cs)
    (H : S.Hyp (fun y => (m0 y).getD 0)) (hx : x.evs = S.old.map Prod.fst) (hwf : x.Wf = true)
    (hrmw : x.rmw = rmwPairs x.evs)
    (hro : ∀ r < x.n, (x.evN r).isR = true →
      x.readBytes (fun y => (m0 y).getD 0) r = (S.old.map Prod.snd).getD r [])
    (hxl : x.Xl) (a2 : List XAct) (hF : S.F = threadUnits S.i S.p1 a2)
    (hc : ∀ a ∈ a2, (∃ f, a.ev.kind = .fence f) ∨ (a.ev.addr, a.ev.size) ∈ cs)
    (hok : ∀ a ∈ a2, ActOk a) :
    actsReplay m0 a2 = some (finalMem m0 (S.rexec (units [trOf a2]) x)) := by
  have R := rhyp_frag hcs a2 hF hc
  refine (oneSem_iff sc_le_xl (MLe.refl _) m0 a2 hok _).mp ⟨S.rexec (units [trOf a2]) x, rfl, rfl,
    Surg.wf_r H R hx hwf hrmw, Surg.readsOk_r H R hx hwf hrmw hro, Surg.xl_r H R hx hwf hrmw hxl, rfl⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
