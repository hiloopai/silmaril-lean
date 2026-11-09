module

public import Silmaril.X86.MemoryModel.Xl.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms

/-!
# x86-TSO implies XL, and XL is x86-TSO on tame executions: proofs

* `tso_xl`: every x86-TSO-consistent candidate is XL-consistent. Every XL coherence or
  global-order edge is a TSO path; no-thin-air follows from TSO's uniproc (internal `rf` goes
  forward in `po`) and `acyclic_po_union` (a `po ∪ rfe` cycle alternates `rfe` with `po` edges
  from a read to a write, which are `ppo`).
* `tso_of_xl_of_tame`: on executions whose memory units are all write-back and not tearable,
  every TSO edge is an XL path.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Axiomatic.Proofs.Xl

open Silmaril.X86.MemoryModel.Axiomatic
open Relation

variable (x : Exec)

theorem smT_sm {a b : Fin x.n} (h : x.smT a b = true) : x.sm a b = true := by
  simp only [Exec.smT, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with rfl | h
  · exact x.sm_refl a
  · exact h.1

theorem smT_refl (a : Fin x.n) : x.smT a a = true := by simp [Exec.smT]

theorem rfR_kinds {a b : Fin x.n} (h : x.rfR a b = true) :
    (x.ev a).isW = true ∧ (x.ev b).isR = true := by
  simp only [Exec.rfR, Bool.and_eq_true] at h
  exact h.1

theorem not_R_and_W (e : Ev) (hr : e.isR = true) (hw : e.isW = true) : False := by
  simp only [Ev.isR, Ev.isW, beq_iff_eq] at hr hw
  rw [hr] at hw
  cases hw

/-- Under TSO uniproc, a reads-from edge is external or goes forward in program order. -/
theorem rf_po_or_rfe (hu : BRel.Acyclic x.uniproc) {a b : Fin x.n} (h : x.rfR a b = true) :
    x.po a b = true ∨ x.rfe a b = true := by
  have hcom : x.uniproc a b = true := by
    simp only [Exec.uniproc, BRel.union_iff]
    exact .inr (BRel.seq_of_left x.sm_refl (by simp [Exec.com, BRel.union_iff, h]))
  by_cases he : x.ext a b = true
  · exact .inr (BRel.inter_iff.mpr ⟨h, he⟩)
  · have htid : (x.ev a).tid = (x.ev b).tid := by simpa [Exec.ext] using he
    rcases Nat.lt_trichotomy (x.ev a).pos (x.ev b).pos with hlt | heq | hgt
    · exact .inl (by simp [Exec.po, htid, hlt])
    · exfalso
      apply hu a
      refine .single ?_
      simp only [BRel.Holds, Exec.uniproc, BRel.union_iff]
      refine .inr ?_
      simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
      exact ⟨b, List.mem_finRange b, by simp [Exec.com, BRel.union_iff, h],
        by simp [Exec.sm, htid, heq]⟩
    · exfalso
      have hk := (rfR_kinds x) h
      have hloc : x.loc b a = true := by
        simp only [Exec.rfR, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
        obtain ⟨-, y, hy, -, hc⟩ := h
        simp only [Exec.loc, Bool.and_eq_true, List.any_eq_true, Ev.isM, Bool.or_eq_true]
        exact ⟨⟨.inl hk.2, .inr hk.1⟩, y, hy, hc⟩
      have hpo : x.poLoc b a = true :=
        BRel.inter_iff.mpr ⟨by simp [Exec.po, htid, hgt], hloc⟩
      apply hu b
      exact .tail (.single (BRel.union_iff.mpr (.inl hpo))) hcom

theorem rfe_ghb {a b : Fin x.n} (h : x.rfe a b = true) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  exact .inr (.inr (.inr (BRel.seq_of_left x.sm_refl (BRel.union_iff.mpr (.inl h)))))

theorem ppo_ghb {a b : Fin x.n} (h : x.ppo a b = true) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  exact .inr (.inr (.inl h))

/-- x86-TSO implies no-thin-air. -/
theorem thinAir_of_tso (h : x.Tso) : BRel.Acyclic x.thinAir := by
  have hpr : BRel.Acyclic (x.po.union x.rfe) := by
    refine BRel.acyclic_po_union x.po x.rfe x.ghb (fun a => (x.ev a).isR) (fun a => (x.ev a).isW)
      (fun _ _ _ => x.po_trans) x.po_irrefl
      (fun a b hab => (rfR_kinds x) (BRel.inter_iff.mp hab).1)
      (fun a hr hw => not_R_and_W _ hr hw) (fun _ _ => (rfe_ghb x)) ?_ h.2.2
    intro a b hr hw hpo
    apply (ppo_ghb x)
    simp [Exec.ppo, hpo, hr, hw, Ev.isM]
  refine BRel.acyclic_mono ?_ hpr
  intro a b hab
  refine .single ?_
  simp only [BRel.Holds, Exec.thinAir, BRel.union_iff] at hab ⊢
  rcases hab with hab | hab
  · exact .inl hab
  · exact (rf_po_or_rfe x) h.2.1 hab

/-- A program-order edge between memory units with a locked end is a TSO `ghb` edge. -/
theorem locked_ghb {a b : Fin x.n} (hpo : x.po a b = true) (ha : (x.ev a).isM = true)
    (hb : (x.ev b).isM = true) (hl : (x.ev a).isA = true ∨ (x.ev b).isA = true) :
    x.ghb a b = true := by
  simp only [Ev.isM, Bool.or_eq_true] at ha hb
  rcases ha with ha | ha
  · exact (ppo_ghb x) (by simp [Exec.ppo, hpo, ha, Ev.isM, hb])
  · rcases hb with hb | hb
    · simp only [Exec.ghb, BRel.union_iff]
      refine .inr (.inl ?_)
      simp only [Exec.implied, hpo, ha, hb, Bool.and_self, Bool.true_and, Bool.or_eq_true]
      exact hl
    · exact (ppo_ghb x) (by simp [Exec.ppo, hpo, ha, hb])

theorem isA_isM {e : Ev} (h : e.isA = true) : e.isM = true := by
  simp only [Ev.isA, Bool.and_eq_true] at h
  exact h.2

theorem ghbXl_tso {a b : Fin x.n} (h : x.ghbXl a b = true) : TransGen x.ghb.Holds a b := by
  simp only [Exec.ghbXl, BRel.union_iff] at h
  rcases h with h | h | h | h | h
  · refine .single ?_
    simp only [BRel.Holds, Exec.ghb, BRel.union_iff]
    exact .inl h
  · simp only [Exec.ppoXl, Bool.and_eq_true] at h
    exact .single ((ppo_ghb x) h.1.1)
  · simp only [Exec.lockXl, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h
    obtain ⟨⟨⟨ha, hb⟩, hpo⟩, hl⟩ := h
    rcases hl with (hl | hl) | ⟨l, _, ⟨hlA, hal⟩, hlb⟩
    · exact .single ((locked_ghb x) hpo ha hb (.inl hl))
    · exact .single ((locked_ghb x) hpo ha hb (.inr hl))
    · exact .tail (.single ((locked_ghb x) hal ha (isA_isM hlA) (.inr hlA)))
        ((locked_ghb x) hlb (isA_isM hlA) hb (.inl hlA))
  · simp only [Exec.sfenceXl, Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hf⟩ := h
    exact .single ((ppo_ghb x) (by simp [Exec.ppo, x.fencerel_po hf, ha, hb]))
  · refine .single ?_
    simp only [BRel.Holds, Exec.ghb, BRel.union_iff]
    exact .inr (.inr (.inr (BRel.seq_mono (fun _ _ h => h) (fun _ _ => (smT_sm x)) h)))

theorem uniprocXl_tso {a b : Fin x.n} (h : x.uniprocXl a b = true) :
    TransGen x.uniproc.Holds a b := by
  refine .single ?_
  simp only [BRel.Holds, Exec.uniprocXl, Exec.uniproc, BRel.union_iff] at h ⊢
  rcases h with h | h
  · exact .inl h
  · exact .inr (BRel.seq_mono (fun _ _ h => h) (fun _ _ => (smT_sm x)) h)

/-- x86-TSO implies XL, for every candidate execution. -/
theorem tso_xl (h : x.Tso) : x.Xl :=
  ⟨h.1, BRel.acyclic_mono (fun _ _ => (uniprocXl_tso x)) h.2.1, (thinAir_of_tso x) h,
    BRel.acyclic_mono (fun _ _ => (ghbXl_tso x)) h.2.2⟩

/-! ## Tame executions -/

theorem sm_smT (ht : x.Tame) {a b : Fin x.n} (h : x.sm a b = true) : x.smT a b = true := by
  simp [Exec.smT, h, (ht a).2]

theorem ghb_xl (ht : x.Tame) {a b : Fin x.n} (h : x.ghb a b = true) :
    TransGen x.ghbXl.Holds a b := by
  refine .single ?_
  simp only [BRel.Holds, Exec.ghb, Exec.ghbXl, BRel.union_iff] at h ⊢
  rcases h with h | h | h | h
  · exact .inl h
  · refine .inr (.inr (.inl ?_))
    simp only [Exec.implied, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hpo, ha⟩, hb⟩, hl⟩ := h
    simp [Exec.lockXl, hpo, Ev.isM, ha, hb, hl]
  · refine .inr (.inl ?_)
    simp [Exec.ppoXl, h, (ht a).1, (ht b).1]
  · exact .inr (.inr (.inr (.inr (BRel.seq_mono (fun _ _ h => h) (fun _ _ => (sm_smT x) ht) h))))

theorem uniproc_xl (ht : x.Tame) {a b : Fin x.n} (h : x.uniproc a b = true) :
    TransGen x.uniprocXl.Holds a b := by
  refine .single ?_
  simp only [BRel.Holds, Exec.uniprocXl, Exec.uniproc, BRel.union_iff] at h ⊢
  rcases h with h | h
  · exact .inl h
  · exact .inr (BRel.seq_mono (fun _ _ h => h) (fun _ _ => (sm_smT x) ht) h)

/-- On tame executions XL implies x86-TSO. -/
theorem tso_of_xl_of_tame (ht : x.Tame) (h : x.Xl) : x.Tso :=
  ⟨h.1, BRel.acyclic_mono (fun _ _ => (uniproc_xl x) ht) h.2.1,
    BRel.acyclic_mono (fun _ _ => (ghb_xl x) ht) h.2.2.2⟩

end Silmaril.X86.MemoryModel.Axiomatic.Proofs.Xl
