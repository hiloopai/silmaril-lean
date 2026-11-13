module

public import Silmaril.Proofs.X86.Pool.Split

/-!
# Proofs: disjoint parallel composition with read-only sharing

* `LTriple.toSTripleS`: a frame-requantified triple (no read-only context) is a stable
  step-indexed triple.
* `par_shared_ro`: two threads with frame-requantified triples over the same read-only
  context `C` run in parallel under every schedule; `C` and the frame `F` are unchanged.
* `par_disjoint`: the case `C = emp`.
* `OwnershipSafe.step`, `OwnershipSafe.reach`: ownership safety is an invariant of SC pool
  steps of unfinished threads, and so holds at every SC-reachable pool.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Pool

open Silmaril.X86 (State MState)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.MemEvent (ChangesWithin)
open Silmaril.X86.Pool

variable {Tid : Type}

/-! ## From frame-requantified to stable triples -/

theorem lsafe_toSafeNS {step : MState → Option MState} {Fin : State → Prop} {Q F : SProp}
    (n : Nat) : ∀ (m : MState) (h hF : Frag), Disjoint h hF → toFrag m = union h hF → F hF →
      LSafe step Fin Q Frag.empty n m.core h →
      Silmaril.X86.Safe.SafeNS step (fun mk => (strue ∗ F) (toFrag mk))
        (fun m' => (Q ∗ F) (toFrag m')) n m := by
  induction n with
  | zero => intro _ _ _ _ _ _ _; trivial
  | succ n ih =>
    intro m h hF hd hsplit hFF hs
    have hle : Le (union h Frag.empty) (toFrag ⟨m.core, m.memory⟩) := by
      rw [union_empty]; show Le h (toFrag m); rw [hsplit]; exact le_union_left h hF
    rcases hs m.memory hle with ⟨_, hq⟩ | ⟨_, m', hstep, hcw, hs'⟩
    · exact .inl ⟨h, hF, hd, hsplit, hq, hFF⟩
    · refine .inr ⟨⟨h, hF, hd, hsplit, trivial, hFF⟩, m', hstep, ?_⟩
      refine ih m' (reval h (toFrag m')) hF (disjoint_reval_left hd) ?_ hFF hs'
      funext l
      cases e : h l with
      | none =>
        rw [union_of_none (reval_none e), hcw l e]
        show toFrag m l = hF l
        rw [hsplit, union_of_none e]
      | some v =>
        have hr : reval h (toFrag m') l = toFrag m' l := reval_of_some (by simp [e])
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (toFrag_isSome m' l)
        rw [hw] at hr
        rw [union_of_some hr, hw]

/-- **A frame-requantified triple is a stable triple** (`STripleS`). -/
theorem LTriple.toSTripleS {step : MState → Option MState} {Fin : State → Prop}
    {P Q : SProp} {n : Nat} (h : LTriple step Fin emp P Q n) :
    Silmaril.X86.Safe.STripleS step n P Q := by
  intro F m ⟨h₁, h₂, hd, hsplit, hp, hf⟩
  exact lsafe_toSafeNS n m h₁ h₂ hd hsplit hf (h m.core h₁ Frag.empty rfl hp (fun _ => .inr rfl))


/-! ## Frame-requantified triples from one-step rules -/

theorem disjoint_reval_toFrag {h r : Frag} {m : MState} (hd : Disjoint h r) :
    Disjoint (reval h (toFrag m)) r := disjoint_reval_left hd

theorem lsafe_of_chain {step : MState → Option MState} {Fin : State → Prop} {R Q : SProp}
    {I : Nat → SProp} {N : Nat}
    (hstep : ∀ k < N, Step1 step R (I k) (I (k + 1)))
    (hrun : ∀ k < N, ∀ c mem h r, R r → I k h → Disjoint h r →
      Le (union h r) (toFrag ⟨c, mem⟩) → ¬ Fin c)
    (hfin : ∀ c mem h r, R r → I N h → Disjoint h r → Le (union h r) (toFrag ⟨c, mem⟩) →
      Fin c ∧ Q h) :
    ∀ n k, k ≤ N → ∀ c h r, R r → I k h → Disjoint h r → LSafe step Fin Q r n c h := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _; trivial
  | succ n ih =>
    intro k hk c h r hr hi hd mem hle
    by_cases hkN : k = N
    · subst hkN; exact .inl (hfin c mem h r hr hi hd hle)
    · have hlt : k < N := by omega
      obtain ⟨m', e, hcw, hj⟩ := hstep k hlt c mem h r hr hi hd hle
      exact .inr ⟨hrun k hlt c mem h r hr hi hd hle, m', e, hcw,
        ih (k + 1) (by omega) m'.core _ r hr hj (disjoint_reval_left hd)⟩

/-- **A frame-requantified triple from a chain of one-step rules** `I 0 → I 1 → … → I N`: the
thread is unfinished along the chain, finished at `I N`, and `I N` gives `Q`. -/
theorem LTriple.of_chain {step : MState → Option MState} {Fin : State → Prop} {R Q : SProp}
    {I : Nat → SProp} {N : Nat}
    (hstep : ∀ k < N, Step1 step R (I k) (I (k + 1)))
    (hrun : ∀ k < N, ∀ c mem h r, R r → I k h → Disjoint h r →
      Le (union h r) (toFrag ⟨c, mem⟩) → ¬ Fin c)
    (hfin : ∀ c mem h r, R r → I N h → Disjoint h r → Le (union h r) (toFrag ⟨c, mem⟩) →
      Fin c ∧ Q h) (n : Nat) :
    LTriple step Fin R (I 0) Q n :=
  fun c h r hr hi hd => lsafe_of_chain hstep hrun hfin n 0 (Nat.zero_le _) c h r hr hi hd

/-! ## One thread's view of a split pool -/

section Thread
variable [DecidableEq Tid]
set_option linter.unusedSectionVars false

theorem view_of_split {p : Pool Tid} {t : Tid} {c : State} {h r : Frag} {X : PFrag Tid}
    (ht : p.threads t = some c) (hsplit : poolFrag p = PFrag.union (embed t h) X)
    (hd : PFrag.Disjoint (embed t h) X) (hr : SharedOnly r) (hrX : PFrag.Le (embedS r) X) :
    Le (union h r) (toFrag ⟨c, p.memory⟩) ∧ Disjoint h r := by
  have hv := proj_poolFrag ht
  refine ⟨le_union ?_ ?_, ?_⟩
  · rw [← hv]; apply le_embed_iff; rw [hsplit]; exact PF.le_union_left _ _
  · rw [← hv, ← proj_embedS t hr]
    apply proj_le
    rw [hsplit]
    exact PF.le_trans hrX (PF.le_union_right hd)
  · apply disjoint_of_embed (t := t) hr
    intro L
    rcases hd L with e | e
    · exact .inl e
    · right
      cases e' : (embedS r : PFrag Tid) L with
      | none => rfl
      | some v => rw [hrX L v e'] at e; cases e

/-- One step of a thread whose fragment `h` is split off the pool. -/
theorem thread_step {step : MState → Option MState} {Fin : Tid → State → Prop} {Q : SProp}
    {p p' : Pool Tid} {t : Tid} {c : State} {h r : Frag} {X : PFrag Tid} {k : Nat}
    (ht : p.threads t = some c) (hsplit : poolFrag p = PFrag.union (embed t h) X)
    (hd : PFrag.Disjoint (embed t h) X) (hr : SharedOnly r) (hrX : PFrag.Le (embedS r) X)
    (hs : LSafe step (Fin t) Q r (k + 1) c h) (hnf : ¬ Fin t c) (hstep : SCStep step p t p') :
    ∃ m', p' = ⟨Function.update p.threads t (some m'.core), m'.memory⟩ ∧
      LSafe step (Fin t) Q r k m'.core (reval h (toFrag m')) ∧
      poolFrag p' = PFrag.union (embed t (reval h (toFrag m'))) X ∧
      PFrag.Disjoint (embed t (reval h (toFrag m'))) X := by
  obtain ⟨hle, -⟩ := view_of_split ht hsplit hd hr hrX
  cases hstep with
  | go ht' hs' =>
    rename_i c₀ m₀
    rw [ht] at ht'; cases ht'
    rcases hs p.memory hle with ⟨hf, -⟩ | ⟨-, m', hstep, hcw, hsafe⟩
    · exact absurd hf hnf
    · rw [hs'] at hstep; cases hstep
      exact ⟨m₀, rfl, hsafe, poolFrag_step ht hsplit hcw, disjoint_embed_reval hd⟩

/-- The thread can step. -/
theorem thread_progress {step : MState → Option MState} {Fin : Tid → State → Prop} {Q : SProp}
    {p : Pool Tid} {t : Tid} {c : State} {h r : Frag} {X : PFrag Tid} {k : Nat}
    (ht : p.threads t = some c) (hsplit : poolFrag p = PFrag.union (embed t h) X)
    (hd : PFrag.Disjoint (embed t h) X) (hr : SharedOnly r) (hrX : PFrag.Le (embedS r) X)
    (hs : LSafe step (Fin t) Q r (k + 1) c h) :
    (Fin t c ∧ Q h) ∨ (¬ Fin t c ∧ ∃ p', SCStep step p t p') := by
  obtain ⟨hle, -⟩ := view_of_split ht hsplit hd hr hrX
  rcases hs p.memory hle with hq | ⟨hnf, m', hstep, -, -⟩
  · exact .inl hq
  · exact .inr ⟨hnf, _, .go ht hstep⟩

end Thread

/-! ## Two threads -/

section Par
variable [DecidableEq Tid]
set_option linter.unusedSectionVars false

variable (step : MState → Option MState) (Fin : Tid → State → Prop) (t₁ t₂ : Tid)
  (C P₁ Q₁ P₂ Q₂ : SProp) (F : PProp Tid)

/-- The invariant of the parallel composition. -/
def ParInv (k₁ k₂ : Nat) (p : Pool Tid) : Prop :=
  ∃ c₁ c₂ h₁ h₂ r HF,
    p.threads t₁ = some c₁ ∧ p.threads t₂ = some c₂ ∧
    (∀ t, t ≠ t₁ → t ≠ t₂ → p.threads t = none) ∧
    C r ∧ SharedOnly r ∧ F HF ∧
    PFrag.Disjoint (embed t₁ h₁) (PFrag.union (embed t₂ h₂) (PFrag.union (embedS r) HF)) ∧
    PFrag.Disjoint (embed t₂ h₂) (PFrag.union (embedS r) HF) ∧
    PFrag.Disjoint (embedS r) HF ∧
    poolFrag p = PFrag.union (embed t₁ h₁) (PFrag.union (embed t₂ h₂) (PFrag.union (embedS r) HF)) ∧
    LSafe step (Fin t₁) Q₁ r k₁ c₁ h₁ ∧ LSafe step (Fin t₂) Q₂ r k₂ c₂ h₂

theorem parInv_safe (ht : t₁ ≠ t₂) (N : Nat) :
    ∀ (p : Pool Tid) (k₁ k₂ : Nat), ParInv step Fin t₁ t₂ C Q₁ Q₂ F k₁ k₂ p → N ≤ k₁ → N ≤ k₂ →
      PoolSafe step Fin
        (fun p' => (atThread t₁ Q₁ ∗ₚ atThread t₂ Q₂ ∗ₚ atShared C ∗ₚ F) (poolFrag p')) N p := by
  induction N with
  | zero => intro _ _ _ _ _ _; trivial
  | succ N ih =>
    intro p k₁ k₂ hinv hk₁ hk₂
    obtain ⟨c₁, c₂, h₁, h₂, r, HF, ht₁, ht₂, hoth, hC, hrS, hF, hd₁, hd₂, hd₃, hsplit, hs₁, hs₂⟩ :=
      hinv
    obtain ⟨k₁, rfl⟩ : ∃ k, k₁ = k + 1 := ⟨k₁ - 1, by omega⟩
    obtain ⟨k₂, rfl⟩ : ∃ k, k₂ = k + 1 := ⟨k₂ - 1, by omega⟩
    -- Views of the two threads.
    have hrX₁ : PFrag.Le (embedS r) (PFrag.union (embed t₂ h₂) (PFrag.union (embedS r) HF)) :=
      PF.le_trans (PF.le_union_left _ _) (PF.le_union_right hd₂)
    have hd₁₂ : PFrag.Disjoint (embed t₁ h₁) (embed t₂ h₂) :=
      (PF.disjoint_union_right.mp hd₁).1
    have hd₁R : PFrag.Disjoint (embed t₁ h₁) (PFrag.union (embedS r) HF) :=
      (PF.disjoint_union_right.mp hd₁).2
    have hsplit₂ : poolFrag p =
        PFrag.union (embed t₂ h₂) (PFrag.union (embed t₁ h₁) (PFrag.union (embedS r) HF)) := by
      rw [hsplit, PF.union_left_comm hd₁₂]
    have hd₂' : PFrag.Disjoint (embed t₂ h₂)
        (PFrag.union (embed t₁ h₁) (PFrag.union (embedS r) HF)) :=
      PF.disjoint_union_right.mpr ⟨PF.disjoint_symm hd₁₂, hd₂⟩
    have hrX₂ : PFrag.Le (embedS r) (PFrag.union (embed t₁ h₁) (PFrag.union (embedS r) HF)) :=
      PF.le_trans (PF.le_union_left _ _) (PF.le_union_right hd₁R)
    have hp₁ := thread_progress ht₁ hsplit hd₁ hrS hrX₁ hs₁
    have hp₂ := thread_progress ht₂ hsplit₂ hd₂' hrS hrX₂ hs₂
    have only : ∀ t c, p.threads t = some c → t = t₁ ∨ t = t₂ := by
      intro t c e
      by_contra hc
      push Not at hc
      rw [hoth t hc.1 hc.2] at e; cases e
    by_cases hfin : Fin t₁ c₁ ∧ Fin t₂ c₂
    · -- Both finished: the postcondition.
      left
      refine ⟨fun t c e => ?_, ?_⟩
      · rcases only t c e with rfl | rfl
        · rw [ht₁] at e; cases e; exact hfin.1
        · rw [ht₂] at e; cases e; exact hfin.2
      · have hq₁ : Q₁ h₁ := by
          rcases hp₁ with ⟨-, hq⟩ | ⟨hn, -⟩
          · exact hq
          · exact absurd hfin.1 hn
        have hq₂ : Q₂ h₂ := by
          rcases hp₂ with ⟨-, hq⟩ | ⟨hn, -⟩
          · exact hq
          · exact absurd hfin.2 hn
        exact ⟨_, _, hd₁, hsplit, ⟨h₁, hq₁, rfl⟩, _, _, hd₂, rfl, ⟨h₂, hq₂, rfl⟩, _, _, hd₃, rfl,
          ⟨r, hC, hrS, rfl⟩, hF⟩
    · right
      refine ⟨?_, ?_, ?_⟩
      · by_cases f₁ : Fin t₁ c₁
        · exact ⟨t₂, c₂, ht₂, fun f₂ => hfin ⟨f₁, f₂⟩⟩
        · exact ⟨t₁, c₁, ht₁, f₁⟩
      · intro t c e hn
        rcases only t c e with rfl | rfl
        · rw [ht₁] at e; cases e
          rcases hp₁ with ⟨hf, -⟩ | ⟨-, hst⟩
          · exact absurd hf hn
          · exact hst
        · rw [ht₂] at e; cases e
          rcases hp₂ with ⟨hf, -⟩ | ⟨-, hst⟩
          · exact absurd hf hn
          · exact hst
      · rintro t p' ⟨⟨c, e, hn⟩, hstep⟩
        rcases only t c e with rfl | rfl
        · rw [ht₁] at e; cases e
          obtain ⟨m', rfl, hs', hsplit', hd'⟩ := thread_step ht₁ hsplit hd₁ hrS hrX₁ hs₁ hn hstep
          refine ih _ k₁ (k₂ + 1) ?_ (by omega) (by omega)
          refine ⟨m'.core, c₂, _, h₂, r, HF, by simp, ?_, ?_, hC, hrS, hF, hd', hd₂, hd₃, hsplit',
            hs', hs₂⟩
          · simp only [Function.update_of_ne (Ne.symm ht)]; exact ht₂
          · intro t' h1 h2; simp only [Function.update_of_ne h1]; exact hoth t' h1 h2
        · rw [ht₂] at e; cases e
          obtain ⟨m', rfl, hs', hsplit', hd'⟩ :=
            thread_step ht₂ hsplit₂ hd₂' hrS hrX₂ hs₂ hn hstep
          refine ih _ (k₁ + 1) k₂ ?_ (by omega) (by omega)
          have hd₁₂' := (PF.disjoint_union_right.mp hd').1
          refine ⟨c₁, m'.core, h₁, _, r, HF, ?_, by simp, ?_, hC, hrS, hF, ?_,
            (PF.disjoint_union_right.mp hd').2, hd₃, ?_, hs₁, hs'⟩
          · simp only [Function.update_of_ne ht]; exact ht₁
          · intro t' h1 h2; simp only [Function.update_of_ne h2]; exact hoth t' h1 h2
          · exact PF.disjoint_union_right.mpr ⟨PF.disjoint_symm hd₁₂', hd₁R⟩
          · rw [hsplit', PF.union_left_comm hd₁₂']

/-- **Disjoint parallel composition with read-only sharing.** Two threads with
frame-requantified triples over the same read-only context `C`, started on disjoint
fragments of a pool where no other thread runs, are safe under every schedule; when both have
finished, both postconditions hold, and `C` and the frame `F` are unchanged. -/
theorem par_shared_ro (ht : t₁ ≠ t₂) {n : Nat}
    (h₁ : LTriple step (Fin t₁) C P₁ Q₁ n) (h₂ : LTriple step (Fin t₂) C P₂ Q₂ n)
    {p : Pool Tid} (hr₁ : ∃ c, p.threads t₁ = some c) (hr₂ : ∃ c, p.threads t₂ = some c)
    (hothers : ∀ t, t ≠ t₁ → t ≠ t₂ → p.threads t = none)
    (hpre : (atThread t₁ P₁ ∗ₚ atThread t₂ P₂ ∗ₚ atShared C ∗ₚ F) (poolFrag p)) :
    PoolSafe step Fin
      (fun p' => (atThread t₁ Q₁ ∗ₚ atThread t₂ Q₂ ∗ₚ atShared C ∗ₚ F) (poolFrag p')) n p := by
  obtain ⟨c₁, ht₁⟩ := hr₁
  obtain ⟨c₂, ht₂⟩ := hr₂
  obtain ⟨_, _, hd₁, hsplit, ⟨g₁, hg₁, rfl⟩, _, _, hd₂, rfl, ⟨g₂, hg₂, rfl⟩, _, HF, hd₃, rfl,
    ⟨r, hC, hrS, rfl⟩, hF⟩ := hpre
  have hrX₁ : PFrag.Le (embedS r) (PFrag.union (embed t₂ g₂) (PFrag.union (embedS r) HF)) :=
    PF.le_trans (PF.le_union_left _ _) (PF.le_union_right hd₂)
  have hd₁₂ : PFrag.Disjoint (embed t₁ g₁) (embed t₂ g₂) := (PF.disjoint_union_right.mp hd₁).1
  have hd₁R := (PF.disjoint_union_right.mp hd₁).2
  have hsplit₂ : poolFrag p =
      PFrag.union (embed t₂ g₂) (PFrag.union (embed t₁ g₁) (PFrag.union (embedS r) HF)) := by
    rw [hsplit, PF.union_left_comm hd₁₂]
  have hd₂' : PFrag.Disjoint (embed t₂ g₂)
      (PFrag.union (embed t₁ g₁) (PFrag.union (embedS r) HF)) :=
    PF.disjoint_union_right.mpr ⟨PF.disjoint_symm hd₁₂, hd₂⟩
  have hrX₂ : PFrag.Le (embedS r) (PFrag.union (embed t₁ g₁) (PFrag.union (embedS r) HF)) :=
    PF.le_trans (PF.le_union_left _ _) (PF.le_union_right hd₁R)
  have v₁ := (view_of_split ht₁ hsplit hd₁ hrS hrX₁).2
  have v₂ := (view_of_split ht₂ hsplit₂ hd₂' hrS hrX₂).2
  exact parInv_safe step Fin t₁ t₂ C Q₁ Q₂ F ht n p n n
    ⟨c₁, c₂, g₁, g₂, r, HF, ht₁, ht₂, hothers, hC, hrS, hF, hd₁, hd₂, hd₃, hsplit,
      h₁ c₁ g₁ r hC hg₁ v₁, h₂ c₂ g₂ r hC hg₂ v₂⟩ (Nat.le_refl _) (Nat.le_refl _)

theorem atShared_emp_sep (F : PProp Tid) : (atShared emp ∗ₚ F) = F := by
  funext H
  apply propext
  constructor
  · rintro ⟨_, H₂, -, rfl, ⟨h, hh, -, rfl⟩, hF⟩
    have : h = Frag.empty := hh
    subst this
    rw [embedS_empty, PF.empty_union]; exact hF
  · intro hF
    exact ⟨PFrag.empty, H, PF.disjoint_empty H, (PF.empty_union H).symm,
      ⟨Frag.empty, rfl, fun _ _ => rfl, embedS_empty.symm⟩, hF⟩

/-- **Disjoint parallel composition** (CSL without shared resources, partial correctness,
every schedule). -/
theorem par_disjoint (ht : t₁ ≠ t₂) {n : Nat}
    (h₁ : LTriple step (Fin t₁) emp P₁ Q₁ n) (h₂ : LTriple step (Fin t₂) emp P₂ Q₂ n)
    {p : Pool Tid} (hr₁ : ∃ c, p.threads t₁ = some c) (hr₂ : ∃ c, p.threads t₂ = some c)
    (hothers : ∀ t, t ≠ t₁ → t ≠ t₂ → p.threads t = none)
    (hpre : (atThread t₁ P₁ ∗ₚ atThread t₂ P₂ ∗ₚ F) (poolFrag p)) :
    PoolSafe step Fin
      (fun p' => (atThread t₁ Q₁ ∗ₚ atThread t₂ Q₂ ∗ₚ F) (poolFrag p')) n p := by
  have := par_shared_ro step Fin t₁ t₂ emp P₁ Q₁ P₂ Q₂ F ht h₁ h₂ hr₁ hr₂ hothers
    (by rw [atShared_emp_sep]; exact hpre)
  rwa [atShared_emp_sep] at this

end Par

/-! ## Ownership safety is an SC invariant -/

section Own
variable [DecidableEq Tid]
set_option linter.unusedSectionVars false

theorem le_poolFrag_step_of_disjoint {p : Pool Tid} {t : Tid} {c : State} {h : Frag}
    {m' : MState} {G : PFrag Tid} (ht : p.threads t = some c)
    (hcw : ChangesWithin h ⟨c, p.memory⟩ m') (hG : PFrag.Le G (poolFrag p))
    (hd : PFrag.Disjoint (embed t h) G) :
    PFrag.Le G (poolFrag (⟨Function.update p.threads t (some m'.core), m'.memory⟩ : Pool Tid)) := by
  intro L v e
  rcases hd L with e' | e'
  · rw [poolFrag_step_outside ht hcw e']; exact hG L v e
  · rw [e'] at e; cases e

/-- **Ownership safety is preserved by every SC step of an unfinished thread.** -/
theorem OwnershipSafe.step {step : MState → Option MState} {Fin : Tid → State → Prop}
    {p p' : Pool Tid} {t : Tid} (hown : OwnershipSafe step Fin p) (hst : SCStepF step Fin p t p') :
    OwnershipSafe step Fin p' := by
  obtain ⟨σ, r, Q, hrS, hnone, hdσ, hdr, hleσ, hler, hsafe⟩ := hown
  obtain ⟨⟨c, ht, hnf⟩, hstep⟩ := hst
  have hv := proj_poolFrag ht
  have hle : Le (union (σ t) r) (toFrag ⟨c, p.memory⟩) := by
    rw [← hv]
    refine le_union (le_embed_iff (hleσ t)) ?_
    rw [← proj_embedS t hrS]; exact proj_le hler
  cases hstep with
  | go ht' hs' =>
    rename_i c₀ m₀
    rw [ht] at ht'; cases ht'
    -- The successor and the footprint, from the safety at index 1.
    have hcw : ChangesWithin (σ t) ⟨c, p.memory⟩ m₀ := by
      rcases hsafe t c ht 1 p.memory hle with ⟨hf, -⟩ | ⟨-, m', e, hcw, -⟩
      · exact absurd hf hnf
      · rw [hs'] at e; cases e; exact hcw
    let σ' : Tid → Frag := Function.update σ t (reval (σ t) (toFrag m₀))
    have hσt : σ' t = reval (σ t) (toFrag m₀) := by simp [σ']
    have hσo : ∀ u, u ≠ t → σ' u = σ u := fun u hu => by simp [σ', hu]
    refine ⟨σ', r, Q, hrS, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      by_cases e : u = t
      · subst e; simp at hu
      · simp only [Function.update_of_ne e] at hu; rw [hσo u e]; exact hnone u hu
    · intro u u' huu
      by_cases e : u = t
      · subst e
        rw [hσt, hσo u' (Ne.symm huu)]
        exact disjoint_embed_reval (hdσ u u' huu)
      · by_cases e' : u' = t
        · subst e'
          rw [hσt, hσo u e]
          exact PF.disjoint_symm (disjoint_embed_reval (PF.disjoint_symm (hdσ u u' huu)))
        · rw [hσo u e, hσo u' e']; exact hdσ u u' huu
    · intro u
      by_cases e : u = t
      · subst e; rw [hσt]; exact disjoint_embed_reval (hdr u)
      · rw [hσo u e]; exact hdr u
    · intro u
      by_cases e : u = t
      · subst e
        rw [hσt]
        intro L v eL
        have hs : (embed u (σ u) L).isSome := by
          cases e2 : embed u (σ u) L with
          | none => rw [embed_reval_none.mpr e2] at eL; cases eL
          | some _ => rfl
        rw [poolFrag_step_inside hs, eL]
      · rw [hσo u e]
        exact le_poolFrag_step_of_disjoint ht hcw (hleσ u) (hdσ t u (Ne.symm e))
    · exact le_poolFrag_step_of_disjoint ht hcw hler (hdr t)
    · intro u c' hu n
      by_cases e : u = t
      · subst e
        simp only [Function.update_self, Option.some.injEq] at hu
        subst hu
        rw [hσt]
        rcases hsafe u c ht (n + 1) p.memory hle with ⟨hf, -⟩ | ⟨-, m', e2, -, hs⟩
        · exact absurd hf hnf
        · rw [hs'] at e2; cases e2; exact hs
      · simp only [Function.update_of_ne e] at hu
        rw [hσo u e]
        exact hsafe u c' hu n

/-- **Ownership safety holds at every SC-reachable pool.** -/
theorem OwnershipSafe.reach {step : MState → Option MState} {Fin : Tid → State → Prop}
    {p p' : Pool Tid} (hown : OwnershipSafe step Fin p) (hr : SCReach step Fin p p') :
    OwnershipSafe step Fin p' := by
  induction hr with
  | refl => exact hown
  | tail _ hst ih => obtain ⟨t, hst⟩ := hst; exact OwnershipSafe.step ih hst

/-- **No running, unfinished thread of an ownership-safe pool is stuck.** -/
theorem OwnershipSafe.progress {step : MState → Option MState} {Fin : Tid → State → Prop}
    {p : Pool Tid} (hown : OwnershipSafe step Fin p) {t : Tid} {c : State}
    (ht : p.threads t = some c) (hnf : ¬ Fin t c) : ∃ p', SCStepF step Fin p t p' := by
  obtain ⟨σ, r, Q, hrS, -, -, -, hleσ, hler, hsafe⟩ := hown
  have hle : Le (union (σ t) r) (toFrag ⟨c, p.memory⟩) := by
    rw [← proj_poolFrag ht]
    refine le_union (le_embed_iff (hleσ t)) ?_
    rw [← proj_embedS t hrS]; exact proj_le hler
  rcases hsafe t c ht 1 p.memory hle with ⟨hf, -⟩ | ⟨-, m', e, -, -⟩
  · exact absurd hf hnf
  · exact ⟨_, ⟨c, ht, hnf⟩, .go ht e⟩

end Own

/-! ## Footprint safety forgets to frame-requantified safety -/

theorem LSafeEv.toLSafe {M : EvMachine} {Fin : State → Prop} {Q : SProp} {r : Frag} :
    ∀ n c h, LSafeEv M Fin Q r n c h → LSafe M.step Fin Q r n c h
  | 0, _, _, _ => trivial
  | n + 1, c, h, hs => fun mem hle => by
    rcases hs mem hle with hf | ⟨hnf, -, -, m', -, -, -, e, hcw, hs'⟩
    · exact .inl hf
    · exact .inr ⟨hnf, m', e, hcw, LSafeEv.toLSafe n _ _ hs'⟩

theorem LTripleEv.toLTriple {M : EvMachine} {Fin : State → Prop} {R P Q : SProp} {n : Nat}
    (h : LTripleEv M Fin R P Q n) : LTriple M.step Fin R P Q n :=
  fun c h' r hr hp hd => LSafeEv.toLSafe n c h' (h c h' r hr hp hd)

theorem OwnershipSafeEv.toOwnershipSafe [DecidableEq Tid] {M : EvMachine}
    {Fin : Tid → State → Prop} {p : Pool Tid} (h : OwnershipSafeEv M Fin p) :
    OwnershipSafe M.step Fin p := by
  obtain ⟨σ, r, Q, a, b, c, d, e, f, g⟩ := h
  exact ⟨σ, r, Q, a, b, c, d, e, f, fun t c' ht n => LSafeEv.toLSafe n _ _ (g t c' ht n)⟩

end Silmaril.Proofs.X86.Pool
