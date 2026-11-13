module

public import Silmaril.Compiler.Target.RenameLiveness.Defs
public import Silmaril.Compiler.Target.RenameInfos.Defs
/-! # Completeness of the renamer checker

`checkCert k p` accepts every program whose functions' entry labels name blocks
(`checkCert_total`), so by `checkCert_sound` every numbering of `renumber` has a liveness
certificate on those programs (`renumber_certified_wf`).

For a function whose liveness converges, with `m` its intervals (`infos`) and `σ` the
numbering `assign k m` gives:

* the header check holds because the last pass of `liveness` changed nothing
  (`liveness_fix`): the registers live at a block's header lie in `gen ∪ (out \ kill)`
  (`liveFrom_genKill`), which lies in the block's `liveIn`;
* a register live after an instruction is live at the block's header or defined at or
  before the instruction, and it is used after the instruction, by the terminator or live
  out of the block (`liveFrom_drop_earlier`, `liveFrom_drop_later`); so its interval
  contains the instruction's write position, like the intervals of the registers the
  instruction defines (`infos_cover`), and `assign` separates them (`assign_sep`);
* the register parameters are all placed at the write position of the entry header,
  which exists when the entry label names a block.
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine Silmaril.Machine.Lir

/-- A register live after the first `j` instructions of a block is used by one of the
others or live before the terminator. -/
theorem liveFrom_drop_later {out : List Nat} :
    ∀ {is : List (Instr Nat)} {j v : Nat}, v ∈ liveFrom out (is.drop j) →
      (∃ j' : Nat, ∃ h : j' < is.length, j ≤ j' ∧ v ∈ instrUses is[j']) ∨ v ∈ out
  | [], _, _, h => .inr (by simpa [liveFrom] using h)
  | i :: is, 0, v, h => by
    rcases mem_liveStep.mp h with hu | ⟨ha, -, -⟩
    · exact .inl ⟨0, by simp, le_refl _, hu⟩
    · rcases liveFrom_drop_later (j := 0) (by simpa using ha) with ⟨j', hj', -, hu⟩ | ho
      · exact .inl ⟨j' + 1, by simp; omega, by omega, by simpa using hu⟩
      · exact .inr ho
  | i :: is, j + 1, v, h => by
    rw [List.drop_succ_cons] at h
    rcases liveFrom_drop_later h with ⟨j', hj', hle, hu⟩ | ho
    · exact .inl ⟨j' + 1, by simp; omega, by omega, by simpa using hu⟩
    · exact .inr ho

/-- A register live after the first `j` instructions of a block is live at its header or
defined by one of them. -/
theorem liveFrom_drop_earlier {out : List Nat} :
    ∀ {is : List (Instr Nat)} {j v : Nat}, v ∈ liveFrom out (is.drop j) →
      v ∈ liveFrom out is ∨ ∃ j' : Nat, ∃ h : j' < is.length, j' < j ∧ v ∈ instrDefs is[j']
  | _, 0, _, h => .inl (by simpa using h)
  | [], _ + 1, _, h => .inl (by simpa [liveFrom] using h)
  | i :: is, j + 1, v, h => by
    rw [List.drop_succ_cons] at h
    rcases liveFrom_drop_earlier h with h' | ⟨j', hj', hlt, hd⟩
    · by_cases hd : v ∈ instrDefs i
      · exact .inr ⟨0, by simp, by omega, by simpa using hd⟩
      · refine .inl (mem_liveStep.mpr ?_)
        by_cases hu : v ∈ instrUses i
        · exact .inl hu
        · exact .inr ⟨h', hd, hu⟩
    · exact .inr ⟨j' + 1, by simp; omega, by omega, by simpa using hd⟩

/-- An interval that contains two positions contains every position between them. -/
theorem Covers.between {m : Std.HashMap Nat Info} {v a b q : Nat} (ha : Covers m v a)
    (hb : Covers m v b) (h₁ : a ≤ q) (h₂ : q ≤ b) : Covers m v q := by
  obtain ⟨i, hi, hs, -⟩ := ha
  obtain ⟨i', hi', -, he⟩ := hb
  rw [hi, Option.some.injEq] at hi'
  subst hi'
  exact ⟨i, hi, by omega, by omega⟩

/-- The converse of `checkRun_fst`. -/
theorem checkRun_fst_of {σ : Nat → Nat} {out : List Nat} :
    ∀ {is : List (Instr Nat)},
      (∀ j (h : j < is.length), interfOk σ is[j] (liveFrom out (is.drop (j + 1))) = true) →
      (checkRun σ out is).1 = true
  | [], _ => rfl
  | i :: is, h => by
    simp only [checkRun, Bool.and_eq_true]
    refine ⟨checkRun_fst_of fun j hj => ?_, ?_⟩
    · have := h (j + 1) (by simp; omega)
      rwa [List.getElem_cons_succ, List.drop_succ_cons] at this
    · rw [checkRun_snd]
      have := h 0 (by simp)
      rwa [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at this

/-- **Completeness of the checker** on one function whose entry label names a block. -/
theorem checkFunc_total (k : Nat) (fn : Func Nat) (hentry : fn.entry < fn.blocks.length) :
    checkFunc k fn = true := by
  cases hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
  | none => rw [checkFunc, hl]
  | some r =>
    obtain ⟨LI, LO⟩ := r
    rw [checkFunc, hl]
    obtain ⟨hLI, hLO, hfix⟩ := liveness_fix hl
    simp only [List.size_toArray] at hLI hLO
    have sep : ∀ {u w q : Nat}, u ≠ w → Covers (infos fn fn.blocks.toArray LI LO) u q →
        Covers (infos fn fn.blocks.toArray LI LO) w q →
        (assign k (infos fn fn.blocks.toArray LI LO)).getD u u ≠
          (assign k (infos fn fn.blocks.toArray LI LO)).getD w w :=
      assign_sep k _ fun _ _ h => infos_wf fn _ LI LO h
    simp only [Bool.and_eq_true, List.all_eq_true]
    constructor
    · -- the parameters all cover the write position of the entry header
      have cov := (infos_cover fn fn.blocks.toArray LI LO fn.entry (by simpa using hentry)).2.1 rfl
      simp only [paramsOk, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      intro v hv w hw
      by_cases hvw : v = w
      · exact .inr hvw
      · exact .inl (sep hvw (cov v hv) (cov w hw))
    · rintro ⟨b, l⟩ hmem
      have hb := List.mem_zipIdx_iff_getElem?.mp hmem
      dsimp only at hb
      obtain ⟨hl', rfl⟩ := List.getElem?_eq_some_iff.mp hb
      have hla : l < fn.blocks.toArray.size := by simpa using hl'
      have cov := infos_cover fn fn.blocks.toArray LI LO l hla
      have fix := hfix l hla
      simp only [List.getElem_toArray] at cov fix
      obtain ⟨cIn, -, cInstr, cTerm, cOut⟩ := cov
      have hLIl : blockLiveIn LI l = (LI[l]!).toList := by
        simp [blockLiveIn, getElem!_pos LI l (by omega), getElem?_pos LI l (by omega)]
      -- the successors' live-in sets lie in the block's live-out set
      have hout : ∀ v, v ∈ (termSuccs fn.blocks[l].term).flatMap (blockLiveIn LI) →
          v ∈ LO[l]! := by
        intro v hv
        obtain ⟨s, hs, hvs⟩ := List.mem_flatMap.mp hv
        refine (fix v).2 (mem_outOf.mpr ⟨s, ?_, ?_⟩)
        · simpa [getElem?_pos fn.blocks.toArray l hla] using hs
        · simpa [blockLiveIn] using hvs
      -- the registers live at the header lie in the block's live-in set
      have hdr : ∀ v, v ∈ liveFrom (termOut (blockLiveIn LI) fn.blocks[l].term)
          fn.blocks[l].instrs → v ∈ LI[l]! := by
        intro v hv
        refine (fix v).1 (mem_union.mpr ?_)
        rcases liveFrom_genKill fn.blocks[l] _ hv with hg | ⟨ho, hk⟩
        · exact .inl hg
        · refine .inr (mem_diff_of_mem ?_ hk)
          obtain ⟨s, hs, hvs⟩ := List.mem_flatMap.mp ho
          refine mem_outOf.mpr ⟨s, ?_, ?_⟩
          · simpa [getElem?_pos fn.blocks.toArray l hla] using hs
          · simpa [blockLiveIn] using hvs
      simp only [checkBlock, Bool.and_eq_true, List.all_eq_true, checkRun_snd]
      constructor
      · refine checkRun_fst_of fun j hj => ?_
        simp only [interfOk, List.all_eq_true, List.mem_append, Bool.or_eq_true, bne_iff_ne,
          ne_eq, beq_iff_eq]
        intro d hd v hv
        by_cases hvd : v = d
        · exact .inr hvd
        refine .inl (sep hvd ?_ ((cInstr j hj).2 d hd))
        rcases hv with hv | hv
        · -- `v` is live after instruction `j`
          have lo : ∃ a, a ≤ 2 * (blockPos fn.blocks.toArray l + 1 + j) + 1 ∧
              Covers (infos fn fn.blocks.toArray LI LO) v a := by
            rcases liveFrom_drop_earlier hv with h0 | ⟨j', hj', hlt, hd'⟩
            · exact ⟨_, by omega, cIn v (hdr v h0)⟩
            · exact ⟨_, by omega, (cInstr j' hj').2 v hd'⟩
          have hi : ∃ c, 2 * (blockPos fn.blocks.toArray l + 1 + j) + 1 ≤ c ∧
              Covers (infos fn fn.blocks.toArray LI LO) v c := by
            rcases liveFrom_drop_later hv with ⟨j', hj', hle, hu⟩ | ho
            · exact ⟨_, by omega, (cInstr j' hj').1 v hu⟩
            · rcases List.mem_append.mp ho with ht | hs
              · exact ⟨_, by omega, cTerm v ht⟩
              · exact ⟨_, by omega, cOut v (hout v hs)⟩
          obtain ⟨a, ha, ca⟩ := lo
          obtain ⟨c, hc, cc⟩ := hi
          exact ca.between cc ha hc
        · exact (cInstr j hj).2 v hv
      · intro v hv
        exact List.contains_iff_mem.mpr (hLIl ▸ Array.mem_toList_iff.mpr (hdr v hv))

/-- **Completeness of the checker**: it accepts every program whose functions' entry labels
name blocks. -/
theorem checkCert_total (k : Nat) (p : Prog Nat)
    (h : ∀ fn ∈ p.funcs, fn.entry < fn.blocks.length) : checkCert k p = true :=
  List.all_eq_true.mpr fun fn hfn => checkFunc_total k fn (h fn hfn)

/-- **Every numbering of `renumber` has a liveness certificate** on programs whose functions'
entry labels name blocks: the checker's (`certLive`). -/
theorem renumber_certified_wf (k : Nat) (p : Prog Nat)
    (h : ∀ fn ∈ p.funcs, fn.entry < fn.blocks.length) :
    ∃ live, LiveCert p (renumberσ k p) live :=
  ⟨certLive p, checkCert_sound (checkCert_total k p h)⟩

end Silmaril.Compile.Target.RegAlloc
