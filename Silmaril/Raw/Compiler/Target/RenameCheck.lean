module

public import Silmaril.Compiler.Target.RenameCorrect.Defs
/-! # Register renumbering, checked

`RegAlloc.renumber k` is proved correct relative to a liveness certificate
(`renumber_refines`: `LiveCert p (renumberσ k p) live` for some `live`). This file makes
it a checked pass: `checkCert k p` recomputes a certificate from the block live-in sets
that `liveness` returns and checks it, and `renumberChecked k p` renumbers `p` when the
check succeeds and leaves it unchanged otherwise.

The certificate (`certLive p`) of a function whose liveness converges is the backward
transfer, inside each block, of the live-in sets `liveIn` of its successors: before the
terminator `t`, the uses of `t` and the live-in sets of its successors (`termOut`);
before an instruction, its uses and the registers live after it that it does not define
(`liveStep`). These sets satisfy the transfer inequalities of `LiveCert` by construction.
The checker verifies the rest:

* the fixpoint inequality at every block header: the registers live before the first
  instruction of block `l` are in `liveIn[l]`;
* interference-freedom: every register defined by an instruction keeps a new number of
  its own among the registers live after it and those it defines;
* the register parameters of the function have distinct new numbers.

A function whose liveness does not converge is not renamed, and every register counts
as live in it. No minimality of the sets is checked: any sets that pass are a
certificate.

## Theorems

`checkCert_sound`: if `checkCert k p`, then `certLive p` is a liveness certificate for
`renumberσ k p`. `renumberChecked_refines`: for every `k`, `renumberChecked k` refines
the program it renumbers, from start states of the same call, at the identity
observation (`Contract.renumber`, the shape of `Contract.lirPass`).
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine Silmaril.Machine.Lir

/-! ## Live sets inside a block -/

/-- The registers live before instruction `i`, given those live after it. -/
def liveStep (i : Instr Nat) (after : List Nat) : List Nat :=
  instrUses i ++ after.filter fun v => !((instrDefs i).contains v || (instrUses i).contains v)

/-- The registers live before a suffix of a block, given those live before its
terminator. -/
def liveFrom (out : List Nat) : List (Instr Nat) → List Nat
  | [] => out
  | i :: is => liveStep i (liveFrom out is)

/-- The registers live before a terminator: its uses and the live-in sets `LI` of its
successors. -/
def termOut (LI : Label → List Nat) (t : Term Nat) : List Nat :=
  termUses t ++ (termSuccs t).flatMap LI

/-- The live-in set of block `l`, from the result of `liveness`. -/
def blockLiveIn (liveIn : Array (Array Nat)) (l : Label) : List Nat :=
  (liveIn[l]?.getD #[]).toList

/-! ## The checker -/

/-- Every register defined by `i` has a new number of its own among the registers live
after `i` and those `i` defines. -/
def interfOk (σ : Nat → Nat) (i : Instr Nat) (after : List Nat) : Bool :=
  (instrDefs i).all fun d => (after ++ instrDefs i).all fun v => σ v != σ d || v == d

/-- Check the instructions of a suffix of a block and compute the registers live before
it, in one backward pass. -/
def checkRun (σ : Nat → Nat) (out : List Nat) : List (Instr Nat) → Bool × List Nat
  | [] => (true, out)
  | i :: is =>
    let r := checkRun σ out is
    (r.1 && interfOk σ i r.2, liveStep i r.2)

/-- Check block `l`: its instructions, and the registers live at its header against its
live-in set. -/
def checkBlock (σ : Nat → Nat) (LI : Label → List Nat) (l : Label) (b : Block Nat) : Bool :=
  let r := checkRun σ (termOut LI b.term) b.instrs
  r.1 && r.2.all fun v => (LI l).contains v

/-- The register parameters have distinct new numbers. -/
def paramsOk (σ : Nat → Nat) (params : List (Loc Nat)) : Bool :=
  (locRegs params).all fun v => (locRegs params).all fun w => σ v != σ w || v == w

/-- Check the numbering `renumberFunc k` gives one function. -/
def checkFunc (k : Nat) (fn : Func Nat) : Bool :=
  match liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
  | none => true
  | some (liveIn, liveOut) =>
    let m := assign k (infos fn fn.blocks.toArray liveIn liveOut)
    let σ : Nat → Nat := fun v => m.getD v v
    paramsOk σ fn.params && fn.blocks.zipIdx.all fun (b, l) => checkBlock σ (blockLiveIn liveIn) l b

/-- Check the numbering `renumber k` gives every function of a program. -/
def checkCert (k : Nat) (p : Prog Nat) : Bool := p.funcs.all (checkFunc k)

/-- **Checked renumbering**: renumber when the check succeeds, otherwise leave the program
unchanged. -/
def renumberChecked (k : Nat) (p : Prog Nat) : Prog Nat :=
  if checkCert k p then renumber k p else p

/-! ## The certificate -/

/-- The live sets the checker checks: the backward transfer of `liveIn` inside each block
of a function whose liveness converges, every register in the others. -/
def certLive (p : Prog Nat) (pt : Point) : Set Nat :=
  match p.funcs[pt.func]? with
  | none => ∅
  | some fn =>
    match liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
    | none => Set.univ
    | some (liveIn, _) =>
      match fn.blocks[pt.label]? with
      | none => ∅
      | some b => {v | v ∈ liveFrom (termOut (blockLiveIn liveIn) b.term) (b.instrs.drop pt.index)}

theorem mem_liveStep {i : Instr Nat} {after : List Nat} {v : Nat} :
    v ∈ liveStep i after ↔ v ∈ instrUses i ∨ (v ∈ after ∧ v ∉ instrDefs i ∧ v ∉ instrUses i) := by
  simp [liveStep]

theorem checkRun_snd (σ : Nat → Nat) (out : List Nat) :
    ∀ is : List (Instr Nat), (checkRun σ out is).2 = liveFrom out is
  | [] => rfl
  | i :: is => by simp [checkRun, liveFrom, checkRun_snd σ out is]

theorem checkRun_fst {σ : Nat → Nat} {out : List Nat} :
    ∀ {is : List (Instr Nat)} {j : Nat} {i : Instr Nat}, (checkRun σ out is).1 = true →
      is[j]? = some i → interfOk σ i (liveFrom out (is.drop (j + 1))) = true
  | [], _, _, _, hj => by simp at hj
  | i' :: is, j, i, h, hj => by
    simp only [checkRun, Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simpa [checkRun_snd] using h.2
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      simpa using checkRun_fst h.1 hj

theorem liveFrom_drop {out : List Nat} {is : List (Instr Nat)} {j : Nat} {i : Instr Nat}
    (h : is[j]? = some i) : liveFrom out (is.drop j) = liveStep i (liveFrom out (is.drop (j + 1))) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hj]
  rfl

/-- Where a fetched code item comes from. -/
theorem fetch_some {p : Prog Nat} {pt : Point} {c : Code Nat} (h : p.fetch pt = some c) :
    ∃ fn b, p.funcs[pt.func]? = some fn ∧ fn.blocks[pt.label]? = some b ∧
      ((∃ i, b.instrs[pt.index]? = some i ∧ c = .instr i) ∨
        (pt.index = b.instrs.length ∧ c = .term b.term)) := by
  unfold Prog.fetch Prog.block? Prog.func? at h
  cases hf : p.funcs[pt.func]? with
  | none => simp [hf] at h
  | some fn =>
    cases hb : fn.blocks[pt.label]? with
    | none => simp [hf, hb] at h
    | some b =>
      refine ⟨fn, b, rfl, hb, ?_⟩
      simp only [hf, hb, Option.bind_some] at h
      cases hi : b.instrs[pt.index]? with
      | some i => simp only [hi, Option.some.injEq] at h; exact .inl ⟨i, rfl, h.symm⟩
      | none =>
        simp only [hi] at h
        split at h
        · next he => cases h; exact .inr ⟨he, rfl⟩
        · cases h

/-- The certificate's sets in a function whose liveness converged. -/
theorem certLive_eq {p : Prog Nat} {pt : Point} {fn : Func Nat} {b : Block Nat}
    {liveIn liveOut : Array (Array Nat)} (hf : p.funcs[pt.func]? = some fn)
    (hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) = some (liveIn, liveOut))
    (hb : fn.blocks[pt.label]? = some b) :
    certLive p pt = {v | v ∈ liveFrom (termOut (blockLiveIn liveIn) b.term) (b.instrs.drop pt.index)} := by
  simp only [certLive, hf]
  rw [hl]
  simp only [hb]

theorem certLive_univ {p : Prog Nat} {pt : Point} {fn : Func Nat}
    (hf : p.funcs[pt.func]? = some fn)
    (hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) = none) :
    certLive p pt = Set.univ := by
  simp only [certLive, hf]
  rw [hl]

theorem certLive_empty {p : Prog Nat} {pt : Point} {fn : Func Nat}
    {liveIn liveOut : Array (Array Nat)} (hf : p.funcs[pt.func]? = some fn)
    (hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) = some (liveIn, liveOut))
    (hb : fn.blocks[pt.label]? = none) : certLive p pt = ∅ := by
  simp only [certLive, hf]
  rw [hl]
  simp only [hb]

theorem renumberσ_none {k : Nat} {p : Prog Nat} {f : FuncId} {fn : Func Nat}
    (hf : p.funcs[f]? = some fn)
    (hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) = none) :
    renumberσ k p f = id := by
  simp only [renumberσ, hf, Option.map_some, Option.getD_some, funcσ]
  rw [hl]

theorem renumberσ_some {k : Nat} {p : Prog Nat} {f : FuncId} {fn : Func Nat}
    {liveIn liveOut : Array (Array Nat)} (hf : p.funcs[f]? = some fn)
    (hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) = some (liveIn, liveOut)) :
    renumberσ k p f = fun v => (assign k (infos fn fn.blocks.toArray liveIn liveOut)).getD v v := by
  simp only [renumberσ, hf, Option.map_some, Option.getD_some, funcσ]
  rw [hl]

/-- What `checkFunc` gives for a function whose liveness converged. -/
theorem checkFunc_some {k : Nat} {fn : Func Nat} {liveIn liveOut : Array (Array Nat)}
    (hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) = some (liveIn, liveOut))
    (h : checkFunc k fn = true) :
    let σ : Nat → Nat := fun v => (assign k (infos fn fn.blocks.toArray liveIn liveOut)).getD v v
    paramsOk σ fn.params = true ∧
      ∀ l b, fn.blocks[l]? = some b → checkBlock σ (blockLiveIn liveIn) l b = true := by
  intro σ
  simp only [checkFunc, hl, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun l b hb => h.2 (b, l) ?_⟩
  exact List.mem_zipIdx_iff_getElem?.mpr hb

/-- **Soundness of the checker**: a program that passes has a liveness certificate for
the numbering of `renumber k`. -/
theorem checkCert_sound {k : Nat} {p : Prog Nat} (h : checkCert k p = true) :
    LiveCert p (renumberσ k p) (certLive p) := by
  have hfn : ∀ f fn, p.funcs[f]? = some fn → checkFunc k fn = true := fun f fn hf =>
    List.all_eq_true.mp h fn (List.mem_of_getElem? hf)
  -- the facts at a fetched point of a function whose liveness converged
  have key : ∀ {pt : Point} {c : Code Nat}, p.fetch pt = some c →
      ∀ fn b, p.funcs[pt.func]? = some fn → fn.blocks[pt.label]? = some b →
      ∀ liveIn liveOut,
        liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) = some (liveIn, liveOut) →
        paramsOk (renumberσ k p pt.func) fn.params = true ∧
        ∀ l b', fn.blocks[l]? = some b' →
          checkBlock (renumberσ k p pt.func) (blockLiveIn liveIn) l b' = true := by
    intro pt c _ fn b hf _ liveIn liveOut hl
    rw [renumberσ_some hf hl]
    exact checkFunc_some hl (hfn _ _ hf)
  refine ⟨?uses, ?flow, ?interf, ?termUses, ?succ, ?params⟩
  case uses =>
    intro pt ins hfe u hu
    obtain ⟨fn, b, hf, hb, hc⟩ := fetch_some hfe
    rcases hc with ⟨i, hi, he⟩ | ⟨_, he⟩
    · cases he
      cases hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
      | none => rw [certLive_univ hf hl]; trivial
      | some r =>
        obtain ⟨liveIn, liveOut⟩ := r
        rw [certLive_eq hf hl hb]
        show u ∈ liveFrom _ _
        rw [liveFrom_drop hi]
        exact mem_liveStep.mpr (.inl hu)
    · cases he
  case flow =>
    intro pt ins hfe v hv hd
    obtain ⟨fn, b, hf, hb, hc⟩ := fetch_some hfe
    rcases hc with ⟨i, hi, he⟩ | ⟨_, he⟩
    · cases he
      cases hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
      | none => rw [certLive_univ hf hl]; trivial
      | some r =>
        obtain ⟨liveIn, liveOut⟩ := r
        rw [certLive_eq (pt := pt.next) hf hl hb] at hv
        rw [certLive_eq hf hl hb]
        show v ∈ liveFrom _ _
        rw [liveFrom_drop hi]
        by_cases hu : v ∈ instrUses ins
        · exact mem_liveStep.mpr (.inl hu)
        · exact mem_liveStep.mpr (.inr ⟨hv, hd, hu⟩)
    · cases he
  case interf =>
    intro pt ins hfe v hv d hd hσ
    obtain ⟨fn, b, hf, hb, hc⟩ := fetch_some hfe
    rcases hc with ⟨i, hi, he⟩ | ⟨_, he⟩
    · cases he
      cases hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
      | none => rw [renumberσ_none hf hl] at hσ; exact hσ
      | some r =>
        obtain ⟨liveIn, liveOut⟩ := r
        have hblk := (key hfe fn b hf hb liveIn liveOut hl).2 pt.label b hb
        simp only [checkBlock, Bool.and_eq_true] at hblk
        have hi' := checkRun_fst hblk.1 hi
        rw [certLive_eq (pt := pt.next) hf hl hb] at hv
        simp only [interfOk, List.all_eq_true, List.mem_append] at hi'
        have := hi' d hd v (hv.imp id id)
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
        exact this.resolve_left (not_not.mpr hσ)
    · cases he
  case termUses =>
    intro pt t hfe u hu
    obtain ⟨fn, b, hf, hb, hc⟩ := fetch_some hfe
    rcases hc with ⟨i, _, he⟩ | ⟨hn, he⟩
    · cases he
    · cases he
      cases hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
      | none => rw [certLive_univ hf hl]; trivial
      | some r =>
        obtain ⟨liveIn, liveOut⟩ := r
        rw [certLive_eq hf hl hb]
        show u ∈ liveFrom _ _
        rw [hn, List.drop_length]
        exact List.mem_append_left _ hu
  case succ =>
    intro pt t hfe l hl' v hv
    obtain ⟨fn, b, hf, hb, hc⟩ := fetch_some hfe
    rcases hc with ⟨i, _, he⟩ | ⟨hn, he⟩
    · cases he
    · cases he
      cases hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
      | none => rw [certLive_univ hf hl]; trivial
      | some r =>
        obtain ⟨liveIn, liveOut⟩ := r
        rw [certLive_eq hf hl hb]
        show v ∈ liveFrom _ _
        rw [hn, List.drop_length]
        cases hb' : fn.blocks[l]? with
        | none => rw [certLive_empty (pt := ⟨pt.func, l, 0⟩) hf hl hb'] at hv; exact hv.elim
        | some b' =>
          rw [certLive_eq (pt := ⟨pt.func, l, 0⟩) hf hl hb'] at hv
          have hblk := (key hfe fn b hf hb liveIn liveOut hl).2 l b' hb'
          simp only [checkBlock, Bool.and_eq_true, List.all_eq_true, checkRun_snd] at hblk
          have hin := hblk.2 v (by simpa using hv)
          refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, hl', ?_⟩)
          exact List.contains_iff_mem.mp hin
  case params =>
    intro f fn hf v hv w hw hσ
    cases hl : liveness fn.blocks.toArray (fn.blocks.toArray.size + 2) with
    | none => rw [renumberσ_none hf hl] at hσ; exact hσ
    | some r =>
      obtain ⟨liveIn, liveOut⟩ := r
      have hp := (checkFunc_some hl (hfn f fn hf)).1
      rw [← renumberσ_some hf hl] at hp
      simp only [paramsOk, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
        beq_iff_eq] at hp
      exact (hp v hv w hw).resolve_left (not_not.mpr hσ)

/-! ## Correctness of the checked stage -/

theorem renameProg_id (p : Prog Nat) : renameProg (fun _ => id) p = p := by
  obtain ⟨funcs⟩ := p
  simp only [renameProg, Prog.mk.injEq]
  apply List.ext_getElem?
  intro f
  simp only [List.getElem?_mapIdx]
  cases funcs[f]? <;> simp [renameFuncND_id]

open Silmaril.Machine.Behaviour (Refines Mode Obs) in
/-- **Checked renumbering refines the program it renumbers** (`Contract.lirPass`, the
contract of the registry's `renumber` stage): by `renumber_refines` and the checker's
certificate when the check succeeds, by the identity renaming otherwise. -/
theorem renumberChecked_refines (k : Nat) (p : Prog Nat) :
    Refines Mode.strict (sem (renumberChecked k p)) (sem p)
      (fun t s => ∃ f args mem, p.start f args mem = some s ∧
        (renumberChecked k p).start f args mem = some t)
      (fun _ _ => Obs.id) := by
  cases h : checkCert k p with
  | true =>
    simp only [renumberChecked, h, ↓reduceIte]
    exact renumber_refines k (checkCert_sound h)
  | false =>
    simp only [renumberChecked, h, Bool.false_eq_true, ↓reduceIte]
    have := rename_refines (LiveCert.id p)
    rwa [renameProg_id] at this

end Silmaril.Compile.Target.RegAlloc
