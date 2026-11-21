module

public import Silmaril.X86.Concurrency.Cir.Tv.Sys.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms

/-!
# Bounded trace-inclusion translation validation: proofs

`tvOk` is the inclusion itself, so refinement is the
`axReach_pick` with every register "clobbered" (the conditions observe memory only), and the
verdicts come from `axJudge_spec`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvSys

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus

theorem mapM_id_spec {α : Type} :
    ∀ {l : List (Option α)} {L : List α}, l.mapM id = some L → L.length = l.length
  | [], L, h => by simp at h; subst h; simp
  | x :: l, L, h => by
    rw [List.mapM_cons] at h
    simp only [id, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, -, L', hl, rfl⟩ := h
    simp [mapM_id_spec hl]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> simp [allRegs]

theorem ctraces_length (c : FTest) : c.ctraces.length = c.prog.threads.length := by
  unfold FTest.ctraces; split <;> simp [Prog.traces, Prog.btraces]

theorem eval_memOnly {cond : Cond} (h : memOnly cond = true) {f f' : Final}
    (hm : f'.mem = f.mem) {w : Cond} (hw : w.atoms = cond.atoms) : w.eval f' = w.eval f := by
  apply Silmaril.X86.Concurrency.Cir.Tv.cond_eval_congr
  intro a ha
  rw [hw] at ha
  have := List.all_eq_true.mp h a ha
  cases a with
  | mem ad sz v => simp [Atom.eval, hm]
  | reg => simp at this

theorem refines {c : FTest} (h : c.tvOk = true) {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop}
    {f : Final} (hf : c.XBehav M f) :
    ∃ f', c.CBehav M f' ∧ f'.mem = f.mem ∧ c.test.witness.eval f' = c.test.witness.eval f := by
  obtain ⟨T, hT, hf⟩ := hf
  simp only [FTest.tvOk, Bool.and_eq_true, beq_iff_eq, hT] at h
  obtain ⟨⟨⟨hmem, -⟩, hlen⟩, hincl⟩ := h
  have hTl : T.length = c.threads.length := by
    simpa using mapM_id_spec hT
  have hUl := ctraces_length c
  obtain ⟨f', hf', hm, -⟩ := Silmaril.X86.Concurrency.Cir.Tv.axReach_pick (t := c.test)
    (U := c.ctraces) (Ks := List.replicate T.length allRegs) (by omega)
    (fun k h₁ h₂ a ha => by
      have hz : (T[k], c.ctraces[k]) ∈ T.zip c.ctraces := by
        rw [List.mem_iff_getElem]
        exact ⟨k, by simp; omega, by simp⟩
      have hi := List.all_eq_true.mp hincl _ hz
      simp only [inclB, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hi
      obtain ⟨b, hb, he⟩ := hi a ha
      refine ⟨b, hb, ?_, ?_⟩
      · rw [← Silmaril.X86.Concurrency.Cir.Tv.threadUnits_normActs, he]
      · intro r hr
        exact absurd (by simp [List.getD_eq_getElem?_getD, h₁, mem_allRegs]) hr) hf
  exact ⟨f', hf', hm, eval_memOnly hmem hm (witness_atoms c.test)⟩

theorem realizes {c : FTest} (h : c.coverOk = true) {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop}
    {f : Final} (hf : c.CBehav M f) :
    ∃ f', c.XBehav M f' ∧ f'.mem = f.mem ∧ c.test.witness.eval f' = c.test.witness.eval f := by
  unfold FTest.coverOk at h
  split at h
  swap
  · simp at h
  rename_i T hT
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hmem, hlen⟩, hcov⟩ := h
  have hTl : T.length = c.threads.length := by
    simpa using mapM_id_spec hT
  have hUl := ctraces_length c
  obtain ⟨f', hf', hm, -⟩ := Silmaril.X86.Concurrency.Cir.Tv.axReach_pick (t := c.test)
    (T := c.ctraces) (U := T) (Ks := List.replicate c.ctraces.length allRegs) (by omega)
    (fun k h₁ h₂ b hb => by
      have hz : (T[k], c.ctraces[k]) ∈ T.zip c.ctraces := by
        rw [List.mem_iff_getElem]
        exact ⟨k, by simp; omega, by simp⟩
      have hi := List.all_eq_true.mp hcov _ hz
      simp only [coverB, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hi
      obtain ⟨a, ha, he⟩ := hi b hb
      refine ⟨a, ha, ?_, ?_⟩
      · rw [← he, Silmaril.X86.Concurrency.Cir.Tv.threadUnits_normActs]
      · intro r hr
        exact absurd (by simp [List.getD_eq_getElem?_getD, h₁, mem_allRegs]) hr) hf
  exact ⟨f', ⟨T, hT, hf'⟩, hm, eval_memOnly hmem hm (witness_atoms c.test)⟩

theorem cir_of_check {c : FTest} (h : c.cirCheck = true) :
    (∀ M : Model, (c.verdict M).Holds c.test (c.CBehav M.Holds)) ∧
      ∃ f, c.CBehav Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f := by
  unfold FTest.cirCheck at h
  split at h
  swap
  · cases h
  rename_i js hjs
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hsc, htso⟩, hxl⟩, hne⟩ := h
  have hv : ∀ M : Model, c.verdict M = c.test.verdictOf (outsBy js M.sel) := by
    intro M; cases M
    · exact hsc
    · exact htso
    · exact hxl
  refine ⟨fun M => ?_, ?_⟩
  · rw [hv M]
    exact verdictOf_holds fun o => axJudge_spec hjs M o
  · obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (by simpa using hne)
    obtain ⟨f, hf, _⟩ := (axJudge_spec hjs Model.sc o).mp ho
    exact ⟨f, hf⟩

theorem transfer_of_allOk {c : FTest} (h : c.allOk = true) : c.Transfer := by
  simp only [FTest.allOk, Bool.and_eq_true] at h
  obtain ⟨htv, hc⟩ := h
  obtain ⟨hcir, hsc⟩ := cir_of_check hc
  refine ⟨fun M f hf => refines htv hf, hcir, hsc, ?_⟩
  intro M hM
  have := hcir M
  rw [hM] at this
  rintro ⟨f, hf, hw⟩
  obtain ⟨f', hb, -, he⟩ := refines htv hf
  exact this ⟨f', hb, he ▸ hw⟩

theorem axReach_locs {t t' : Test} (h : t.locs = t'.locs) {T : List (List XTrace)}
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} :
    AxReach t T M f ↔ AxReach t' T M f := by
  have hi : t.initMem = t'.initMem := by simp [Test.initMem, h]
  have hb : t.initB = t'.initB := by funext y; simp [Test.initB, hi]
  unfold AxReach ReadsOk finalAx
  rw [hi, hb]

theorem cbehav_iff {c : FTest} (h : c.tvOk = true) {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop}
    {f : Final} :
    c.CBehav M f ↔ if c.blk then BBehavIn c.prog c.dom M f else BehavIn c.prog c.dom M f := by
  simp only [FTest.tvOk, Bool.and_eq_true, beq_iff_eq] at h
  have hl : c.test.locs = c.prog.memTest.locs := h.1.1.2.symm
  unfold FTest.CBehav FTest.ctraces BBehavIn BehavIn
  split <;> exact axReach_locs hl

theorem forall2_mem_mono {α : Type} {trs : List α} {T U : List (List α)}
    (h : List.Forall₂ (· ∈ ·) trs T) (hl : T.length = U.length)
    (hs : ∀ k (h1 : k < T.length) (h2 : k < U.length), ∀ a ∈ T[k], a ∈ U[k]) :
    List.Forall₂ (· ∈ ·) trs U := by
  induction h generalizing U with
  | nil => cases U with
    | nil => exact .nil
    | cons _ _ => simp at hl
  | cons hab _ ih =>
    cases U with
    | nil => simp at hl
    | cons u U =>
      refine .cons (hs 0 (by simp) (by simp) _ hab) (ih (by simpa using hl) fun k h1 h2 =>
        hs (k + 1) (by simpa using h1) (by simpa using h2))

theorem witness_sc {c : FTest} {ks : List Nat} (h : c.witnessOk ks = true) :
    c.test.Allowed (c.CBehav Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc) := by
  unfold FTest.witnessOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hl, h⟩ := h
  split at h
  swap
  · cases h
  rename_i js hjs
  have hv : c.test.verdictOf (outsBy js Model.sc.sel) = .allowed := by simpa using h
  have := verdictOf_holds (R := AxReach c.test (c.pickT ks) Model.sc.Holds)
    fun o => axJudge_spec hjs Model.sc o
  rw [hv] at this
  obtain ⟨f, ⟨trs, h2, rest⟩, hw⟩ := this
  refine ⟨f, ⟨trs, forall2_mem_mono h2 (by simp [FTest.pickT, hl]) ?_, rest⟩, hw⟩
  intro k h1 h2 a ha
  simp only [FTest.pickT, List.getElem_map, List.getElem_zip] at ha
  simp only [Option.mem_toList] at ha
  exact List.mem_of_getElem? ha

theorem readsOkB_iff {t : Test} {x : Silmaril.X86.MemoryModel.Axiomatic.Exec} {exps : List (List Byte)} :
    readsOkB t x exps = true ↔ ReadsOk t x exps := by
  simp only [readsOkB, ReadsOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq]
  constructor
  · intro h r hr hR
    rcases h r hr with h | h
    · rw [hR] at h; cases h
    · exact h
  · intro h r hr
    cases hR : (x.evN r).isR
    · exact Or.inl rfl
    · exact Or.inr (h r hr hR)

theorem pick_forall2 {α : Type} :
    ∀ (L : List (List α)) (ks : List Nat),
      ((L.zip ks).filterMap fun p => p.1[p.2]?).length = L.length →
      List.Forall₂ (· ∈ ·) ((L.zip ks).filterMap fun p => p.1[p.2]?) L
  | [], _, _ => by simp
  | l :: L, [], h => by simp at h
  | l :: L, k :: ks, h => by
    have hle : ((L.zip ks).filterMap fun p => p.1[p.2]?).length ≤ L.length :=
      (List.length_filterMap_le _ _).trans (by simp)
    simp only [List.zip_cons_cons, List.filterMap_cons] at h ⊢
    cases hk : l[k]? with
    | none => rw [hk] at h; simp at h; omega
    | some a =>
      rw [hk] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      exact .cons (List.mem_of_getElem? hk) (pick_forall2 L ks h)

theorem sched_sc {c : FTest} {ks sch : List Nat} (h : c.schedOk ks sch = true) :
    c.test.Allowed (c.CBehav Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc) := by
  unfold FTest.schedOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hl, hwf⟩, hro⟩, hsc⟩, hw⟩ := h
  exact ⟨_, ⟨c.pickTr ks, pick_forall2 _ _ hl, _, rfl, rfl, hwf, readsOkB_iff.mp hro, hsc, rfl⟩, hw⟩

end Silmaril.Proofs.X86.Concurrency.Cir.TvSys
