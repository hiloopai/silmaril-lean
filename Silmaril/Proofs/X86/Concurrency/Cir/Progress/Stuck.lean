module

public import Silmaril.X86.Concurrency.Cir.Progress.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Progress.Rules

/-!
# Proofs: a stuck configuration of a certified, `Good` program is finished or out of bound

Along every run of the store-buffer machine from a CSL-certified start:

* every thread's state is thread-locally reachable from its start (`reach_inv`);
* buffers of threads `≥ N` stay empty, and every value in memory and in the buffers fits the
  width map, because every label of a reachable thread state writes fitting values.

At a stuck configuration every buffer is empty (a non-empty buffer can flush its oldest entry),
so memory is the abstraction `XInv` speaks about. A thread that is neither finished nor out
of a loop bound is `Good`, so it has a silent step (impossible) or a label step reading memory,
provided the label's cells are mapped, which `Safe` gives. That label step is a machine
step: a contradiction.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Progress

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Progress

/-- The run invariant. -/
def RunI (w : Nat → Option Nat) (N : Nat) (C0 : Cfg) (C : OCfg) : Prop :=
  (∀ t < N, TReach (C0.ts t) (C.ts t)) ∧ (∀ t, N ≤ t → C.buf t = []) ∧
  (∀ a v, C.mem a = some v → fits w a v) ∧
  ∀ t, ∀ e ∈ C.buf t, ∀ a v b, e = .st a v b → fits w a v

theorem upd_eq {α : Type} (f : Nat → α) (t : Nat) (x : α) : upd f t x t = x := by simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) {t u : Nat} (x : α) (h : u ≠ t) : upd f t x u = f u := by
  simp [upd, h]

theorem runI_step {w : Nat → Option Nat} {N : Nat} {C0 : Cfg} {M : OModel} {C C' : OCfg}
    (hg : ∀ t < N, ∀ p, TReach (C0.ts t) p → Good w p.1 p.2) (H : RunI w N C0 C)
    (st : OStep M N C C') : RunI w N C0 C' := by
  obtain ⟨hT, hB, hM, hE⟩ := H
  have tsUpd : ∀ {t : Nat} {l : Option Lab} {s' : Stmt} {rs' : Regs}, t < N →
      TStep (C.ts t).1 (C.ts t).2 l s' rs' →
        ∀ u < N, TReach (C0.ts u) (upd C.ts t (s', rs') u) := by
    intro t l s' rs' ht hs u hu
    by_cases e : u = t
    · subst e; rw [upd_eq]; exact treach_snoc (hT u hu) hs
    · rw [upd_ne _ _ e]; exact hT u hu
  cases st with
  | tau ht hs => exact ⟨tsUpd ht hs, hB, hM, hE⟩
  | @buffered t l s' rs' ht hs hm hd hc hok =>
    have LF := (hg t ht _ (hT t ht)).1 l s' rs' hs
    refine ⟨tsUpd ht hs, fun u hu => ?_, hM, fun u e he a v b hb => ?_⟩
    · have : u ≠ t := by omega
      simp only [upd_ne _ _ this]; exact hB u hu
    · by_cases eu : u = t
      · subst eu
        simp only [upd_eq, List.mem_append] at he
        rcases he with he | he
        · exact hE u e he a v b hb
        · exact LF.2 e he a v b hb
      · simp only [upd_ne _ _ eu] at he
        exact hE u e he a v b hb
  | @drained t l s' rs' ht hs hm hd he hc hok =>
    have LF := (hg t ht _ (hT t ht)).1 l s' rs' hs
    refine ⟨tsUpd ht hs, hB, fun a v h => ?_, hE⟩
    simp only [Lab.updH] at h
    cases e : l.wval a with
    | some v' => rw [e] at h; cases h; exact LF.1 a _ e
    | none => rw [e] at h; exact hM a v h
  | @flush t pre e post ht hb hp hmod =>
    have he : e ∈ C.buf t := by rw [hb]; simp
    refine ⟨hT, fun u hu => ?_, fun a v h => ?_, fun u e' he' a v b hb' => ?_⟩
    · have : u ≠ t := by omega
      simp only [upd_ne _ _ this]; exact hB u hu
    · cases e with
      | bar => exact hM a v h
      | st x y wk =>
        simp only [Ent.apply] at h
        split at h
        · cases h; subst_vars; exact hE t _ he _ _ _ rfl
        · exact hM a v h
    · by_cases eu : u = t
      · subst eu
        simp only [upd_eq, List.mem_append] at he'
        refine hE u e' ?_ a v b hb'
        rw [hb]; rcases he' with h | h <;> simp [h]
      · simp only [upd_ne _ _ eu] at he'
        exact hE u e' he' a v b hb'

theorem runI_reach {w : Nat → Option Nat} {N : Nat} {C0 : Cfg} {M : OModel}
    (hg : ∀ t < N, ∀ p, TReach (C0.ts t) p → Good w p.1 p.2) {C C' : OCfg}
    (h : OReach M N C C') : RunI w N C0 C → RunI w N C0 C' := by
  induction h with
  | refl => exact id
  | step st _ ih => exact fun H => ih (runI_step hg H st)

theorem firstNewest_empty {buf : Nat → List Ent} (hb : ∀ t, buf t = []) (a : Nat) :
    ∀ us, firstNewest buf a us = none
  | [] => rfl
  | u :: us => by simp [firstNewest, hb u, newest, firstNewest_empty hb a us]

theorem abs_drained {N : Nat} {C : OCfg} (hd : C.Drained) : C.abs N = ⟨C.ts, C.mem⟩ := by
  simp only [OCfg.abs, firstNewest_empty hd, Option.getD_none, Option.map_id']

theorem le_isSome {h s : Heap} (hl : Heap.Le h s) {a : Nat} (ha : (h a).isSome) :
    (s a).isSome := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ha
  rw [hl a v hv]; rfl

/-- **The progress theorem.** A stuck configuration reached from a CSL-certified start whose
threads are thread-locally `Good` and whose initial values fit is drained and finished, or has
a thread out of a loop bound. -/
theorem stuck {I : HProp} {Q : Nat → Regs → HProp} {N : Nat} {C0 : Cfg} {hs : Nat → Heap}
    {hI : Heap} {w : Nat → Option Nat} {M : OModel} {Cf : OCfg} (G : GInv I Q N C0 hs hI)
    (hg : ∀ t < N, ∀ p, TReach (C0.ts t) p → Good w p.1 p.2)
    (hw0 : ∀ a v, C0.mem a = some v → fits w a v) (hr : OReach M N C0.toO Cf)
    (hst : ∀ Cf', ¬ OStep M N Cf Cf') :
    (Cf.Drained ∧ ∀ t < N, (Cf.ts t).1 = .skip) ∨ ∃ t < N, Exh (Cf.ts t) := by
  have R0 : RunI w N C0 C0.toO :=
    ⟨fun t _ => .refl, fun _ _ => rfl, hw0, fun _ e he => by simp [Cfg.toO] at he⟩
  obtain ⟨hT, hB, hM, -⟩ := runI_reach hg hr R0
  -- drained: a non-empty buffer can flush
  have hd : Cf.Drained := by
    intro t
    by_cases ht : t < N
    · cases e : Cf.buf t with
      | nil => rfl
      | cons x post =>
        exfalso
        refine hst _ (OStep.flush (pre := []) (e := x) (post := post) ht (by simp [e]) ?_
          (Or.inr rfl))
        cases x <;> simp [Ent.passes]
    · exact hB t (by omega)
  obtain ⟨-, hs', hI', X⟩ := drf_sc G hr
  have GA := X.1
  rw [abs_drained hd] at GA
  obtain ⟨-, hdI, hle, hleI, hIv, hsafe⟩ := GA
  by_cases hall : ∀ t < N, (Cf.ts t).1 = .skip
  · exact Or.inl ⟨hd, hall⟩
  · simp only [not_forall] at hall
    obtain ⟨t, ht, hns⟩ := hall
    rcases (hg t ht _ (hT t ht)).2 with h | h | ⟨s', rs', st⟩ | hH
    · exact absurd h hns
    · exact Or.inr ⟨t, ht, h⟩
    · exact absurd (OStep.tau ht st) (hst _)
    · exfalso
      obtain ⟨R, hR, hpost⟩ := hsafe t ht
      have lab : ∀ l s' rs', TStep (Cf.ts t).1 (Cf.ts t).2 (some l) s' rs' →
          l.isMem = true ∧ ∀ a, l.Touches a → (Cf.mem a).isSome := by
        intro l s' rs' st
        have LO := (hpost _ _ _ hR).2.2 l s' rs' st
        refine ⟨LO.1, fun a ha => ?_⟩
        cases hna : l.na
        · obtain ⟨h1, -, -⟩ := LO.2.2 hna hI' hIv (hdI t)
          have := h1 a ha
          rw [show Heap.union (hs' t) hI' a = (hs' t a).or (hI' a) by
            simp only [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion]
            cases hs' t a <;> rfl] at this
          cases e : hs' t a with
          | some v => exact le_isSome (hle t) (by simp [e])
          | none => rw [e] at this; exact le_isSome hleI (by simpa using this)
        · exact le_isSome (hle t) ((LO.2.1 hna).1 a ha)
      obtain ⟨l, s', rs', st, hok⟩ := hH Cf.mem hM fun l s' rs' st => (lab l s' rs' st).2
      obtain ⟨hm, hc⟩ := lab l s' rs' st
      cases hdr : l.drains
      · refine hst _ (OStep.buffered ht st hm hdr hc ?_)
        rw [hd t]
        have : view Cf.mem [] = Cf.mem := by funext a; simp [view, newest]
        rw [this]; exact hok
      · exact hst _ (OStep.drained ht st hm hdr (hd t) hc hok)

end Silmaril.Proofs.X86.Concurrency.Cir.Progress
