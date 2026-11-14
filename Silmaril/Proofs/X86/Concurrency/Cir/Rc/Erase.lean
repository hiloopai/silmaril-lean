module

public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Client

/-!
# Proofs: erasing the ghost cells

The ledger's ghost cells live in the configuration's memory (at addresses `≥ 2^64`), because
`GInv` asks every owned heap to be contained in memory. A real machine has no such cells.
This file shows that they change nothing a physical run can observe:

* `ostep_mono` / `oreach_mono`: **the store-buffer machines are monotone in memory**. A run
  from memory `m₁` is also a run, with the same threads and buffers, from every extension
  `m₂ ⊇ m₁`, and the extension is kept. (A step only asks its touched cells to be mapped and
  its reads to agree, and writes only touched cells.)
* `oreach_mapped`: a mapped cell stays mapped.
* `drop2_phys`: `Drop2` started from the **physical memory** (the start's memory restricted to
  addresses below `2^64`: no ghost cell) still ends with `42` in both output cells, on TSO and
  XL; `drop2_no_race_phys`: and it is race-free under SC.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Rc
open Silmaril.X86.Concurrency.Cir.Rc.Drop2

theorem view_le {m₁ m₂ : Heap} (hle : Heap.Le m₁ m₂) (b : List Ent) :
    Heap.Le (view m₁ b) (view m₂ b) := by
  intro a v h
  simp only [view] at h ⊢
  cases e : newest b a with
  | none => rw [e] at h; simpa using hle a v (by simpa using h)
  | some w => rw [e] at h; simpa using h

theorem updH_le {m₁ m₂ : Heap} (hle : Heap.Le m₁ m₂) (l : Lab) :
    Heap.Le (l.updH m₁) (l.updH m₂) := by
  intro a v h
  simp only [Lab.updH] at h ⊢
  cases e : l.wval a with
  | none => rw [e] at h; simpa using hle a v (by simpa using h)
  | some w => rw [e] at h; simpa using h

theorem apply_le {m₁ m₂ : Heap} (hle : Heap.Le m₁ m₂) (e : Ent) :
    Heap.Le (e.apply m₁) (e.apply m₂) := by
  intro a v h
  cases e with
  | st b w _ =>
    simp only [Ent.apply] at h ⊢
    split
    · simp_all
    · simp only [‹¬a = b›, ite_false] at h; exact hle a v h
  | bar => exact hle a v h

theorem okH_le {m₁ m₂ : Heap} (hle : Heap.Le m₁ m₂) {l : Lab} (h : l.okH m₁) : l.okH m₂ :=
  fun p hp => hle _ _ (h p hp)

/-- **One step is monotone in memory.** -/
theorem ostep_mono {Mo : OModel} {N : Nat} {C C' : OCfg} (hs : OStep Mo N C C') {m : Heap}
    (hle : Heap.Le C.mem m) :
    ∃ m', OStep Mo N ⟨C.ts, m, C.buf⟩ ⟨C'.ts, m', C'.buf⟩ ∧ Heap.Le C'.mem m' := by
  cases hs with
  | tau ht hst => exact ⟨m, OStep.tau (C := ⟨C.ts, m, C.buf⟩) ht hst, hle⟩
  | buffered ht hst hm hd hc hok =>
    exact ⟨m, OStep.buffered (C := ⟨C.ts, m, C.buf⟩) ht hst hm hd
      (fun a ha => by
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hc a ha)
        simp [hle a v hv])
      (okH_le (view_le hle _) hok), hle⟩
  | drained ht hst hm hd he hc hok =>
    exact ⟨_, OStep.drained (C := ⟨C.ts, m, C.buf⟩) ht hst hm hd he
      (fun a ha => by
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hc a ha)
        simp [hle a v hv])
      (okH_le hle hok), updH_le hle _⟩
  | flush ht hb hp hmod =>
    exact ⟨_, OStep.flush (C := ⟨C.ts, m, C.buf⟩) ht hb hp hmod, apply_le hle _⟩

/-- **Runs are monotone in memory**: a run from `m₁` is a run from every `m₂ ⊇ m₁`. -/
theorem oreach_mono {Mo : OModel} {N : Nat} {C C' : OCfg} (hr : OReach Mo N C C') {m : Heap}
    (hle : Heap.Le C.mem m) :
    ∃ m', OReach Mo N ⟨C.ts, m, C.buf⟩ ⟨C'.ts, m', C'.buf⟩ ∧ Heap.Le C'.mem m' := by
  induction hr generalizing m with
  | refl => exact ⟨m, Star.refl, hle⟩
  | step hs _ ih =>
    obtain ⟨m₁, h₁, hle₁⟩ := ostep_mono hs hle
    obtain ⟨m₂, h₂, hle₂⟩ := ih hle₁
    exact ⟨m₂, Star.step h₁ h₂, hle₂⟩

theorem ostep_mapped {Mo : OModel} {N : Nat} {C C' : OCfg} (hs : OStep Mo N C C') {x : Nat}
    (hx : (C.mem x).isSome) : (C'.mem x).isSome := by
  cases hs with
  | tau => exact hx
  | buffered => exact hx
  | drained =>
    simp only [Lab.updH]
    cases (Lab.wval _ x) <;> simp [hx]
  | @flush t pre e post _ _ _ _ =>
    cases e with
    | st a v w => simp only [Ent.apply]; split <;> simp [hx]
    | bar => exact hx

/-- A mapped cell stays mapped. -/
theorem oreach_mapped {Mo : OModel} {N : Nat} {C C' : OCfg} (hr : OReach Mo N C C') {x : Nat}
    (hx : (C.mem x).isSome) : (C'.mem x).isSome := by
  induction hr with
  | refl => exact hx
  | step hs _ ih => exact ih (ostep_mapped hs hx)

/-- Memory restricted to the physical addresses (below `2^64`): the ghost cells erased. -/
def phys (m : Heap) : Heap := fun x => if x < gbase then m x else none

theorem phys_le (m : Heap) : Heap.Le (phys m) m := by
  intro a v h; simp only [phys] at h; split at h <;> simp_all

/-- `Drop2` from the physical memory: the start with every ghost cell erased. -/
def startPhys (A : Alloc) (hmm hblk : Heap) : Cfg :=
  ⟨(start A hmm hblk).ts, phys (start A hmm hblk).mem⟩

theorem own_out {t : Nat} (ht : t < 2) : own t (out t) = some 0 := by
  have hl := l_lt
  have hot := out_lt ht
  simp [own, ht, union_or, single_ne (gA_ne_lt hot).symm, single_ne (gB_ne_lt hot).symm,
    single_self]

/-- **The ghost cells are unobservable**: `Drop2` without them, on TSO and XL, still ends with
`42` in both output cells. -/
theorem drop2_phys (A : Alloc) {hmm hblk : Heap} (haw : AllocAway hmm hblk) (hm : A.mm hmm)
    (hb : A.blk l hblk) {Mo : OModel} {C : OCfg}
    (h : OReach Mo 2 (startPhys A hmm hblk).toO C) (hd : C.Drained)
    (hfin : ∀ t < 2, (C.ts t).1 = .skip) : ∀ t < 2, C.mem (out t) = some 42 := by
  intro t ht
  obtain ⟨m', h', hle'⟩ := oreach_mono h (phys_le (start A hmm hblk).mem)
  have hG := drop2_certified A haw hm hb
  obtain ⟨hs', hI', hq, -, -, -, hle, -⟩ := csl_buffered hG (C := ⟨C.ts, m', C.buf⟩) h' hd hfin
  have h42 : m' (out t) = some 42 := hle t _ _ (post_out ht (hq t ht))
  have hmap : ((startPhys A hmm hblk).toO.mem (out t)).isSome := by
    have := hG.2.2.1 t _ _ (own_out ht)
    simp [startPhys, Cfg.toO, phys, out_lt ht, this]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (oreach_mapped h hmap)
  rw [hv, ← h42, hle' _ _ hv]

/-- One SC step is monotone in memory. -/
theorem scstep_mono {N : Nat} {C C' : Cfg} (hs : ScStep N C C') {m : Heap}
    (hle : Heap.Le C.mem m) : ∃ m', ScStep N ⟨C.ts, m⟩ ⟨C'.ts, m'⟩ ∧ Heap.Le C'.mem m' := by
  cases hs with
  | tau ht hst => exact ⟨m, ScStep.tau (C := ⟨C.ts, m⟩) ht hst, hle⟩
  | lab ht hst hm hc hok =>
    exact ⟨_, ScStep.lab (C := ⟨C.ts, m⟩) ht hst hm
      (fun a ha => by
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hc a ha)
        simp [hle a v hv])
      (okH_le hle hok), updH_le hle _⟩

/-- SC runs are monotone in memory. -/
theorem screach_mono {N : Nat} {C C' : Cfg} (hr : ScReach N C C') {m : Heap}
    (hle : Heap.Le C.mem m) : ∃ m', ScReach N ⟨C.ts, m⟩ ⟨C'.ts, m'⟩ := by
  induction hr generalizing m with
  | refl => exact ⟨m, Star.refl⟩
  | step hs _ ih =>
    obtain ⟨m₁, h₁, hle₁⟩ := scstep_mono hs hle
    obtain ⟨m₂, h₂⟩ := ih hle₁
    exact ⟨m₂, Star.step h₁ h₂⟩

/-- **Race freedom without the ghost cells**: no SC-reachable state of `Drop2` from the
physical memory has a race (`Race` reads only the threads). -/
theorem drop2_no_race_phys (A : Alloc) {hmm hblk : Heap} (haw : AllocAway hmm hblk)
    (hm : A.mm hmm) (hb : A.blk l hblk) {C : Cfg} (h : ScReach 2 (startPhys A hmm hblk) C) :
    ¬ Race 2 C := by
  obtain ⟨m', h'⟩ := screach_mono h (phys_le (start A hmm hblk).mem)
  exact no_race (drop2_certified A haw hm hb) (C := ⟨C.ts, m'⟩) h'

end Silmaril.Proofs.X86.Concurrency.Cir.Rc
