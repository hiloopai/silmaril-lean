module

public import Silmaril.X86.Concurrency.Cir.Robust.Defs
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms

/-!
# The explorer: thread steps, concrete memory and registers

`tsucc_complete` and `tsucc_sound`: the enumerated thread steps are
exactly `Csl.TStep`s whose reads agree with the view (for statements without `local`
blocks). Facts about the concrete cell lists (`memOf_setC`, `memOf_updL`, `memOf_applyE`) and
register lists (`rget_rlist`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Csl (Heap Ent TStep view newest)

/-! ## Registers -/

theorem rget_rlist (rs : Regs) : rget (rlist rs) = rs := by
  funext r; cases r <;> rfl

theorem rlist_length (rs : Regs) : (rlist rs).length = 16 := rfl

/-! ## Cells -/

theorem memOf_nil (x : Nat) : memOf [] x = none := rfl

theorem memOf_cons (p : Nat × Nat) (l : List (Nat × Nat)) (x : Nat) :
    memOf (p :: l) x = if p.1 = x then some p.2 else memOf l x := by
  simp only [memOf, List.find?_cons]
  split <;> simp_all

theorem memOf_map_set (l : List (Nat × Nat)) (a v x : Nat) :
    memOf (l.map fun p => if p.1 == a then (a, v) else p) x =
      if x = a then (if l.any (·.1 == a) then some v else none) else memOf l x := by
  induction l with
  | nil => simp [memOf_nil]
  | cons p l ih =>
    rw [List.map_cons, memOf_cons, memOf_cons, ih]
    by_cases hp : p.1 = a
    · simp only [hp, beq_self_eq_true, ↓reduceIte, List.any_cons, Bool.true_or]
      by_cases hx : x = a
      · simp [hx]
      · simp [hx, Ne.symm hx]
    · have : (p.1 == a) = false := by simpa using hp
      simp only [this, Bool.false_eq_true, ↓reduceIte, List.any_cons, Bool.false_or]
      by_cases hx : x = a
      · subst hx; simp [hp]
      · simp [hx]

theorem memOf_setC (l : List (Nat × Nat)) (a v : Nat) :
    memOf (setC l a v) = fun x => if x = a then some v else memOf l x := by
  funext x
  unfold setC
  split
  · rename_i h
    rw [memOf_map_set, h]
    simp
  · rw [memOf_cons]
    simp only
    by_cases hx : x = a
    · simp [hx]
    · simp [hx, Ne.symm hx]

/-! ## Thread steps -/

/-- The reads of a label agree with `vw`. -/
abbrev ReadsIn (vw : Heap) (o : Option Lab) : Prop :=
  ∀ l, o = some l → ∀ p ∈ l.reads, vw p.1 = some p.2

/-- A label that is not a `local` block. -/
def notBlk : Lab → Bool
  | .blk .. => false
  | _ => true

theorem tsucc_complete {vw : Heap} {s : Stmt} {rs : Regs} {o : Option Lab} {s' : Stmt}
    {rs' : Regs} (h : TStep s rs o s' rs') (hb : noBlk s = true) (hr : ReadsIn vw o) :
    (o, s', rs') ∈ tsucc vw s rs := by
  induction h with
  | assign => simp [tsucc]
  | load hv =>
    have := hr _ rfl _ (List.mem_singleton_self _)
    simp [tsucc, this, hv]
  | store => simp [tsucc]
  | rmw hv =>
    have := hr _ rfl _ (List.mem_singleton_self _)
    simp [tsucc, this, hv]
  | fence => simp [tsucc]
  | fwait hv hq =>
    have := hr _ rfl _ (List.mem_singleton_self _)
    simp [tsucc, this]; omega
  | fwake hq => simp [tsucc]; omega
  | spawn => simp [tsucc]
  | join => simp [tsucc]
  | blk => simp [noBlk] at hb
  | seq h ih =>
    simp only [noBlk, Bool.and_eq_true] at hb
    simp only [tsucc, List.mem_append, List.mem_map]
    exact Or.inr ⟨_, ih hb.1 hr, rfl⟩
  | seqSkip => simp [tsucc]
  | iteT h => simp [tsucc, h]
  | iteF h => simp [tsucc, h]
  | loopT h => simp [tsucc, h]
  | loopF h => simp [tsucc, h]

theorem tsucc_complete_tau {vw : Heap} {s : Stmt} {rs : Regs} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs none s' rs') : (none, s', rs') ∈ tsucc vw s rs := by
  generalize ho : (none : Option Lab) = o at h
  induction h with
  | assign => simp [tsucc]
  | seq h ih =>
    subst ho
    simp only [tsucc, List.mem_append, List.mem_map]
    exact Or.inr ⟨_, ih rfl, rfl⟩
  | seqSkip => simp [tsucc]
  | iteT h => simp [tsucc, h]
  | iteF h => simp [tsucc, h]
  | loopT h => simp [tsucc, h]
  | loopF h => simp [tsucc, h]
  | _ => cases ho

theorem noneOk {vw : Heap} : ReadsIn vw none ∧ ∀ l : Lab, none = some l → notBlk l = true :=
  ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩

theorem tsucc_sound {vw : Heap} {s : Stmt} {rs : Regs} {o : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : (o, s', rs') ∈ tsucc vw s rs) :
    TStep s rs o s' rs' ∧ ReadsIn vw o ∧ ∀ l, o = some l → notBlk l = true := by
  induction s generalizing o s' rs' with
  | skip => simp [tsucc] at h
  | assign d e =>
    simp only [tsucc, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.assign, noneOk⟩
  | load d m sz fl a =>
    simp only [tsucc] at h
    split at h
    · rename_i v hv
      split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rename_i hlt
        refine ⟨.load hlt, ?_, (fun _ h => by cases h; rfl)⟩
        intro l hl p hp; cases hl
        simp only [Lab.reads, List.mem_singleton] at hp; subst hp; exact hv
      · simp at h
    · simp at h
  | store m sz fl a v =>
    simp only [tsucc, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.store, (fun _ h p hp => by cases h; simp [Lab.reads] at hp),
      (fun _ h => by cases h; rfl)⟩
  | rmw d m sz op a arg =>
    simp only [tsucc] at h
    split at h
    · rename_i v hv
      split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rename_i hlt
        refine ⟨.rmw hlt, ?_, (fun _ h => by cases h; rfl)⟩
        intro l hl p hp; cases hl
        simp only [Lab.reads, List.mem_singleton] at hp; subst hp; exact hv
      · simp at h
    · simp at h
  | fence k =>
    simp only [tsucc, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.fence, (fun _ h p hp => by cases h; simp [Lab.reads] at hp),
      (fun _ h => by cases h; rfl)⟩
  | futexWait d a v =>
    simp only [tsucc] at h
    split at h
    · rename_i w hw
      split at h
      · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
        obtain ⟨r, hr, rfl, rfl, rfl⟩ := h
        rename_i hlt
        refine ⟨.fwait hlt hr, ?_, (fun _ h => by cases h; rfl)⟩
        intro l hl p hp; cases hl
        simp only [Lab.reads, List.mem_singleton] at hp; subst hp; exact hw
      · simp at h
    · simp at h
  | futexWake a n =>
    simp only [tsucc, List.mem_map, List.mem_range, Prod.mk.injEq] at h
    obtain ⟨q, hq, rfl, rfl, rfl⟩ := h
    exact ⟨.fwake hq, (fun _ h p hp => by cases h; simp [Lab.reads] at hp),
      (fun _ h => by cases h; rfl)⟩
  | spawn t =>
    simp only [tsucc, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.spawn, (fun _ h p hp => by cases h; simp [Lab.reads] at hp),
      (fun _ h => by cases h; rfl)⟩
  | join t =>
    simp only [tsucc, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.join, (fun _ h p hp => by cases h; simp [Lab.reads] at hp),
      (fun _ h => by cases h; rfl)⟩
  | «local» b => simp [tsucc] at h
  | seq a b iha ihb =>
    simp only [tsucc, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨p, hp, hpe⟩
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨.seqSkip, noneOk⟩
      · simp at h
    · simp only [Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl, rfl⟩ := hpe
      obtain ⟨h1, h2, h3⟩ := iha hp
      exact ⟨.seq h1, h2, h3⟩
  | ite c a b =>
    simp only [tsucc, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, h2, h3⟩ := h
    subst h3 h2
    refine ⟨?_, noneOk⟩
    split
    · rename_i hc; exact .iteT hc
    · rename_i hc; exact .iteF (by simpa using hc)
  | loop n c b =>
    simp only [tsucc] at h
    split at h
    · rename_i hc
      split at h
      · simp at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨.loopT hc, noneOk⟩
    · rename_i hc
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨.loopF (by simpa using hc), noneOk⟩

theorem noBlk_step {s : Stmt} {rs : Regs} {o : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs o s' rs') (hb : noBlk s = true) : noBlk s' = true := by
  induction h with
  | seq _ ih =>
    simp only [noBlk, Bool.and_eq_true] at hb ⊢; exact ⟨ih hb.1, hb.2⟩
  | seqSkip => simp only [noBlk, Bool.and_eq_true] at hb; exact hb.2
  | iteT => simp only [noBlk, Bool.and_eq_true] at hb; exact hb.1
  | iteF => simp only [noBlk, Bool.and_eq_true] at hb; exact hb.2
  | loopT => simp only [noBlk, Bool.and_eq_true] at hb ⊢; exact ⟨hb, hb⟩
  | _ => rfl

/-! ## Labels on cell lists -/

theorem memOf_updL (l : List (Nat × Nat)) (lab : Lab) (hb : notBlk lab = true) :
    memOf (updL l lab) = lab.updH (memOf l) := by
  funext x
  cases lab with
  | wr m fl a sz v =>
    simp only [updL, memOf_setC, Lab.updH, Lab.wval]
    by_cases hx : x = a
    · subst hx; simp
    · simp [hx, Ne.symm hx]
  | rmw m a sz o n =>
    simp only [updL, memOf_setC, Lab.updH, Lab.wval]
    by_cases hx : x = a
    · subst hx; simp
    · simp [hx, Ne.symm hx]
  | blk => simp [notBlk] at hb
  | _ => simp [updL, Lab.updH, Lab.wval]

theorem memOf_applyE (l : List (Nat × Nat)) (e : Ent) : memOf (applyE l e) = e.apply (memOf l) := by
  cases e with
  | st a v w => simp only [applyE, memOf_setC, Ent.apply]
  | bar => rfl

/-- The cells a non-block label touches are its `labCells`. -/
theorem touches_cells {lab : Lab} (hb : notBlk lab = true) {a : Nat} (h : lab.Touches a) :
    a ∈ labCells lab := by
  cases lab <;> simp_all [Lab.Touches, Lab.reads, Lab.wval, labCells, notBlk]; omega

theorem cells_touch {lab : Lab} {a : Nat} (h : a ∈ labCells lab) : lab.Touches a := by
  cases lab <;> simp_all [Lab.Touches, Lab.reads, Lab.wval, labCells]

theorem mappedB_iff {mem : List (Nat × Nat)} {lab : Lab} (hb : notBlk lab = true) :
    mappedB mem lab = true ↔ ∀ a, lab.Touches a → (memOf mem a).isSome := by
  simp only [mappedB, List.all_eq_true]
  exact ⟨fun h a ha => h a (touches_cells hb ha), fun h a ha => h a (cells_touch ha)⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Robust
