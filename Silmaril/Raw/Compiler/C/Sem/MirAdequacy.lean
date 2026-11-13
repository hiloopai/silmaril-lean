module

public import Silmaril.Compiler.C.Sem.TargetsFit.Defs
public import Silmaril.Compiler.Mir.InterpRun.Defs
@[expose] public section

/-! # Mir interpreter adequacy for images that fit -/

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine

private theorem linked_run_rel (cfg : Config) (n : Nat) (us : Array Unit) (o : Outcome)
    (fit : ∀ l, link cfg.layout us = .ok l →
      ∀ i < l.image.size, l.dataBase + i < cfg.memSize)
    (hrun : Mir.run cfg n us = .ok o) :
    ∃ (l : Linked) (m : Machine), link cfg.layout us = .ok l ∧
      l.prog.start 0 [] (Mir.initMem cfg l) = some m.toLir ∧
      RunRel o (Lir.run l.prog n m.toLir) := by
  unfold Mir.run at hrun
  cases hl : link cfg.layout us with
  | error e =>
    rw [hl] at hrun
    change Except.error e.message = Except.ok o at hrun
    cases hrun
  | ok l =>
    cases hs : start (load l.prog) 0 [] (initMem cfg l) with
    | error e => simp [hl, hs] at hrun
    | ok m =>
      simp [hl, hs] at hrun
      have hfit := fit l hl
      obtain ⟨hstart, hstack, hfr⟩ := start_toLir l.prog 0 [] (initMem cfg l) m hs
      have hmem := start_mem (load l.prog) 0 [] (initMem cfg l) m hs
      have hm : m.WellFormed l.prog := by
        refine ⟨hfr, ?_, ?_, ?_⟩
        · rw [hmem]
          exact Mem.ofImage_wellFormed _ _ _ hfit
        · rw [hmem]
          have he := Mem.ofImage_extents cfg.memSize l.dataBase l.image hfit
          simpa only [initMem, he.1] using he.2
        · simp [hstack]
      have hr := run_rel l.prog ⟨0,n+1⟩ rfl n m hm
      rw [hrun] at hr
      refine ⟨l,m,rfl,?_,hr⟩
      rw [Mem.ofImage_toLir cfg l hfit] at hstart
      simpa [Machine.toLir, hstack] using hstart

end Silmaril.Compile.Mir.Interp

namespace Silmaril.Compile.Targets.Proofs

open Silmaril.Machine

theorem mir_run_returned_fit : Targets.mir_run_returned_fit := by
  intro cfg n us vs mem hfit hrun
  obtain ⟨l,m,hl,hs,hr⟩ := Mir.Interp.linked_run_rel cfg n us (.returned vs mem) hfit hrun
  change Lir.run l.prog n m.toLir = .returned (vs.map UInt64.toBitVec) mem.toLir at hr
  rw [Mir.beh_eq_link cfg us l hl]
  change (.returned (vs.map UInt64.toBitVec,mem.toLir) : Mir.LirOutcome) ∈
    match l.prog.start 0 [] (Mir.initMem cfg l) with
    | some s => Mir.ubClose {o | (Lir.sem l.prog).Beh s o}
    | none => ∅
  rw [hs]
  exact Or.inl (Lir.beh_iff_behaves.mpr (Lir.run_returned hr))


theorem mir_run_trapped_fit : Targets.mir_run_trapped_fit := by
  intro cfg n us mem hfit hrun
  obtain ⟨l,m,hl,hs,hr⟩ := Mir.Interp.linked_run_rel cfg n us (.trapped mem) hfit hrun
  change Lir.run l.prog n m.toLir = .trapped mem.toLir at hr
  rw [Mir.beh_eq_link cfg us l hl]
  change (.trapped mem.toLir : Mir.LirOutcome) ∈
    match l.prog.start 0 [] (Mir.initMem cfg l) with
    | some s => Mir.ubClose {o | (Lir.sem l.prog).Beh s o}
    | none => ∅
  rw [hs]
  exact Or.inl (Lir.beh_iff_behaves.mpr (Lir.run_trapped hr))


end Silmaril.Compile.Targets.Proofs
