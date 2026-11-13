module

public import Silmaril.Compiler.C.Sem.Targets.Defs
public import Silmaril.Compiler.C.Sem.MirStuckChecks.Defs
public import Silmaril.Compiler.Mir.InterpRun.Defs
public import Silmaril.Compiler.Mir.InterpMemBounded.Defs
public import Silmaril.Compiler.Mir.MemoryAgreement.Defs
@[expose] public section

/-! # Unrestricted adequacy of stuck Mir runs -/

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine

private theorem initMem_agrees (cfg : Config) (l : Linked) :
    (initMem cfg l).toLir.Agrees (Mir.initMem cfg l) := by
  have hinv := Mem.ofImage_invariants_any cfg.memSize l.dataBase l.image
  refine ⟨hinv.2.1, ?_⟩
  intro b hb
  have hb' : b < cfg.memSize := by
    simpa only [Mem.toLir, initMem, hinv.2.1] using hb
  change BitVec.ofNat 8 ((Mem.ofImage cfg.memSize l.dataBase l.image).getByte b).toNat =
    if l.dataBase ≤ b ∧ b < l.dataBase+l.image.size then
      BitVec.ofNat 8 (l.image.get! (b-l.dataBase)).toNat else 0
  rw [Mem.getByte_ofImage_any]
  by_cases h : l.dataBase ≤ b ∧ b < l.dataBase+l.image.size
  · rw [ite_eq_left ⟨h.1,h.2,hb'⟩, ite_eq_left h]
    have hi : b-l.dataBase < l.image.size := by omega
    have he : l.image[b-l.dataBase]! = l.image.get! (b-l.dataBase) := by
      rcases him : l.image with ⟨xs⟩
      rw [him] at hi
      rw [getElem!_pos (ByteArray.mk xs) (b-l.dataBase) hi]
      change xs[b-l.dataBase] = xs[b-l.dataBase]!
      exact (getElem!_pos xs _ hi).symm
    rw [he]
  · rw [ite_eq_right (show ¬ (l.dataBase ≤ b ∧ b < l.dataBase+l.image.size ∧ b < cfg.memSize)
        from fun hc => h ⟨hc.1,hc.2.1⟩), ite_eq_right h]
    rfl

private theorem start_replace_memory (p : Lir.Prog Nat) (f : Nat) (args : List Lir.Word)
    (mem mem' : Lir.Memory) (s : Lir.State Nat) (hs : p.start f args mem = some s) :
    p.start f args mem' = some {s with mem := mem'} := by
  unfold Lir.Prog.start at hs ⊢
  cases he : p.enter f args with
  | none => simp [he] at hs
  | some v =>
    rcases v with ⟨pt,fr⟩
    simp only [he, Option.map_some, Option.some.injEq] at hs
    cases hs
    rfl

end Silmaril.Compile.Mir.Interp

namespace Silmaril.Compile.Targets.Proofs

open Silmaril.Machine
open Mir.Interp

theorem mir_run_stuck : Targets.mir_run_stuck := by
  intro cfg n us why pt mem hrun
  unfold Mir.run at hrun
  cases hl : Mir.link cfg.layout us with
  | error e =>
    rw [hl] at hrun
    change Except.error e.message = Except.ok (Outcome.stuck why pt mem) at hrun
    cases hrun
  | ok l =>
    cases hs : start (load l.prog) 0 [] (initMem cfg l) with
    | error e => simp [hl, hs] at hrun
    | ok m =>
      simp [hl, hs] at hrun
      have hinv := Mem.ofImage_invariants_any cfg.memSize l.dataBase l.image
      obtain ⟨hstart,hstack,hfr⟩ := start_toLir l.prog 0 [] (initMem cfg l) m hs
      have hmem := start_mem (load l.prog) 0 [] (initMem cfg l) m hs
      have hm : m.WellFormed l.prog := by
        refine ⟨hfr, ?_, ?_, ?_⟩
        · rw [hmem]; exact hinv.1
        · rw [hmem]; simpa only [initMem,hinv.2.1] using hinv.2.2
        · simp [hstack]
      have hr := run_rel l.prog ⟨0,n+1⟩ rfl n m hm
      rw [hrun] at hr
      change Lir.run l.prog n m.toLir = .stuck at hr
      have hs' : l.prog.start 0 [] (initMem cfg l).toLir = some m.toLir := by
        simpa [Machine.toLir, hstack] using hstart
      let s : Lir.State Nat := {m.toLir with mem := Mir.initMem cfg l}
      have hsactual : l.prog.start 0 [] (Mir.initMem cfg l) = some s :=
        start_replace_memory l.prog 0 [] _ _ m.toLir hs'
      have hagree : m.toLir.Agrees s := by
        refine ⟨rfl,rfl,rfl,?_⟩
        change m.mem.toLir.Agrees (Mir.initMem cfg l)
        rw [hmem]
        exact initMem_agrees cfg l
      have hractual := Lir.run_stuck_of_agrees l.prog n m.toLir s hagree hr
      have hu : (Lir.sem l.prog).Beh s (.undefined : Mir.LirOutcome) :=
        (Lir.beh_iff_behaves (b := .stuck)).mpr
          (Lir.run_final hractual (by intro x h; cases h))
      rw [Mir.beh_eq_link cfg us l hl]
      change (match l.prog.start 0 [] (Mir.initMem cfg l) with
        | some s => Mir.ubClose {o | (Lir.sem l.prog).Beh s o}
        | none => ∅) = Set.univ
      rw [hsactual]
      exact Mir.ubClose_of_undefined hu

end Silmaril.Compile.Targets.Proofs
