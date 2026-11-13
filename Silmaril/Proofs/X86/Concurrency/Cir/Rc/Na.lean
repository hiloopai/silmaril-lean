module

public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Client

/-!
# Proofs: `Task.drop2Na` by mode insensitivity

`Task.drop2Na` asks the outputs of `Drop2` with a plain (`na`) payload load. The store-buffer
machines never look at a load's mode: a `rd` label reads its view, buffers nothing and does
not drain, whatever its mode. So every run of `bodyNa` is a run of `body`, step for step with
the same memory and buffers, and `drop2_buffered` applies. The mode matters only for `Race`
(two `na` reads race in the CSL), which `Task.drop2Na` does not ask; race freedom of the `na`
variant, i.e. a CSL certificate with read-only sharing, still needs fractional permissions.

* `tstep_na`: the thread-level simulation (`RelNa`: equal, or the three states before and at
  the payload load, which differ only in its mode);
* `ostep_na` / `oreach_na`: the machine-level simulation, for TSO and XL;
* `drop2Na`: `Task.drop2Na`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Rc
open Silmaril.X86.Concurrency.Cir.Rc.Drop2

/-- The rest of a thread after its payload load. -/
def restOf (A : Alloc) (t : Nat) : Stmt :=
  .seq (.store .na 8 .wb (.lit (out t)) (.reg .rbx))
    (.seq (rcDrop .rax (.lit l) (slow A)) (rcDrop .rax (.lit l) (slow A)))

/-- The payload load with mode `m`, then the rest. -/
def fromLd (A : Alloc) (t : Nat) (m : Mode) : Stmt :=
  .seq (.load .rbx m 4 .wb (.lit (l + 4))) (restOf A t)

/-- **The simulation of one thread**: equal, or `bodyNa` against `body` before (and at) the
payload load. -/
def RelNa (A : Alloc) (t : Nat) (σ σ' : Stmt) : Prop :=
  σ = σ' ∨ (σ = .seq (rcInc .rax (.lit l)) (fromLd A t .na) ∧
      σ' = .seq (rcInc .rax (.lit l)) (fromLd A t .rlx)) ∨
    (σ = .seq .skip (fromLd A t .na) ∧ σ' = .seq .skip (fromLd A t .rlx)) ∨
    (σ = fromLd A t .na ∧ σ' = fromLd A t .rlx)

/-- Labels equal up to the mode of a read (`na` against `rlx`). -/
def LabNa (o o' : Option Lab) : Prop :=
  o = o' ∨ ∃ fl a sz v, o = some (.rd .na fl a sz v) ∧ o' = some (.rd .rlx fl a sz v)

theorem tstep_na {A : Alloc} {t : Nat} {σ σ' : Stmt} (hR : RelNa A t σ σ') {rs : Regs}
    {o : Option Lab} {s₁ : Stmt} {rs₁ : Regs} (h : TStep σ rs o s₁ rs₁) :
    ∃ o' s₁', TStep σ' rs o' s₁' rs₁ ∧ LabNa o o' ∧ RelNa A t s₁ s₁' := by
  rcases hR with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨o, s₁, h, Or.inl rfl, Or.inl rfl⟩
  · simp only [rcInc] at h ⊢
    cases h with
    | seq h' =>
      cases h'
      exact ⟨_, _, TStep.seq (TStep.rmw (by assumption)), Or.inl rfl,
        Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · cases h with
    | seq h' => cases h'
    | seqSkip => exact ⟨none, _, TStep.seqSkip, Or.inl rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  · simp only [fromLd] at h ⊢
    cases h with
    | seq h' =>
      cases h' with
      | load hv => exact ⟨_, _, TStep.seq (TStep.load hv), Or.inr ⟨_, _, _, _, rfl, rfl⟩,
          Or.inl rfl⟩

/-- **The simulation of configurations**: same memory and buffers, same registers, threads
related. -/
def CRelNa (A : Alloc) (C C' : OCfg) : Prop :=
  C.mem = C'.mem ∧ C.buf = C'.buf ∧ ∀ t, (C.ts t).2 = (C'.ts t).2 ∧ RelNa A t (C.ts t).1 (C'.ts t).1

theorem crel_upd {A : Alloc} {C C' : OCfg} (hC : CRelNa A C C') {t : Nat} {s₁ s₁' : Stmt}
    {rs₁ : Regs} (hR : RelNa A t s₁ s₁') (u : Nat) :
    (upd C.ts t (s₁, rs₁) u).2 = (upd C'.ts t (s₁', rs₁) u).2 ∧
      RelNa A u (upd C.ts t (s₁, rs₁) u).1 (upd C'.ts t (s₁', rs₁) u).1 := by
  by_cases hu : u = t
  · subst hu; simp [upd, hR]
  · simp only [upd, hu, ite_false]; exact hC.2.2 u

theorem ostep_na {A : Alloc} {Mo : OModel} {N : Nat} {C D C' : OCfg} (hs : OStep Mo N C D)
    (hC : CRelNa A C C') : ∃ D', OStep Mo N C' D' ∧ CRelNa A D D' := by
  obtain ⟨hm, hb, hts⟩ := hC
  cases hs with
  | @tau t s₁ rs₁ ht hst =>
    obtain ⟨o', s₁', hst', hl, hR⟩ := tstep_na (hts t).2 hst
    have ho : o' = none := by
      rcases hl with h | ⟨_, _, _, _, h, -⟩
      · exact h.symm
      · cases h
    subst ho
    rw [(hts t).1] at hst'
    exact ⟨_, OStep.tau ht hst', hm, hb, crel_upd ⟨hm, hb, hts⟩ hR⟩
  | @buffered t lab s₁ rs₁ ht hst hmem hd hc hok =>
    obtain ⟨o', s₁', hst', hl, hR⟩ := tstep_na (hts t).2 hst
    rw [(hts t).1] at hst'
    rcases hl with h | ⟨fl, a, sz, v, h, rfl⟩
    · subst h
      refine ⟨_, OStep.buffered ht hst' hmem hd (hm ▸ hc) (hm ▸ hb ▸ hok), hm, ?_,
        crel_upd ⟨hm, hb, hts⟩ hR⟩
      simp [hb]
    · cases h
      refine ⟨_, OStep.buffered ht hst' rfl rfl (fun x hx => hm ▸ hc x ?_) ?_, hm, ?_,
        crel_upd ⟨hm, hb, hts⟩ hR⟩
      · simpa [Lab.Touches, Lab.reads, Lab.wval] using hx
      · intro p hp
        have := hok p (by simpa [Lab.reads] using hp)
        rwa [hm, hb] at this
      · simp [hb, Lab.ents]
  | @drained t lab s₁ rs₁ ht hst hmem hd he hc hok =>
    obtain ⟨o', s₁', hst', hl, hR⟩ := tstep_na (hts t).2 hst
    rw [(hts t).1] at hst'
    rcases hl with h | ⟨fl, a, sz, v, h, -⟩
    · subst h
      exact ⟨_, OStep.drained ht hst' hmem hd (hb ▸ he) (hm ▸ hc) (hm ▸ hok),
        by simp [hm], hb, crel_upd ⟨hm, hb, hts⟩ hR⟩
    · cases h; simp [Lab.drains] at hd
  | flush ht hbuf hp hmod =>
    exact ⟨_, OStep.flush ht (hb ▸ hbuf) hp hmod, by simp [hm], by simp [hb], hts⟩

theorem oreach_na {A : Alloc} {Mo : OModel} {N : Nat} {C D C' : OCfg} (hr : OReach Mo N C D)
    (hC : CRelNa A C C') : ∃ D', OReach Mo N C' D' ∧ CRelNa A D D' := by
  induction hr generalizing C' with
  | refl => exact ⟨C', Star.refl, hC⟩
  | step hs _ ih =>
    obtain ⟨D₁, h₁, hD₁⟩ := ostep_na hs hC
    obtain ⟨D₂, h₂, hD₂⟩ := ih hD₁
    exact ⟨D₂, Star.step h₁ h₂, hD₂⟩

theorem start_crel (A : Alloc) (hmm hblk : Heap) :
    CRelNa A (startNa A hmm hblk).toO (start A hmm hblk).toO := by
  refine ⟨rfl, rfl, fun t => ⟨rfl, ?_⟩⟩
  by_cases ht : t < 2
  · simp only [startNa, start, Cfg.toO, ht, ite_true]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · simp only [startNa, start, Cfg.toO, ht, ite_false]; exact Or.inl rfl

theorem relNa_skip {A : Alloc} {t : Nat} {σ' : Stmt} (h : RelNa A t .skip σ') : σ' = .skip := by
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h.symm
  all_goals cases h

/-- **`Task.drop2Na`**, by the simulation and `drop2_buffered`. -/
theorem drop2Na : Task.drop2Na := by
  intro A hmm hblk haw hm hb Mo C hr hd hfin t ht
  obtain ⟨D, hD, hm', hb', hts⟩ := oreach_na hr (start_crel A hmm hblk)
  obtain ⟨hs', hI', hq, -, -, -, hle, -⟩ :=
    csl_buffered (drop2_certified A haw hm hb) hD (fun u => hb' ▸ hd u)
      (fun u hu => relNa_skip ((hfin u hu) ▸ (hts u).2))
  rw [hm']
  exact hle t _ _ (post_out ht (hq t ht))

end Silmaril.Proofs.X86.Concurrency.Cir.Rc
