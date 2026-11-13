module

public import Silmaril.Proofs.Wasm.JcoTool.KCore.Kernel

/-!
# The feed loop feeds the kernel as `Tr.feed` does

(Restyled to the Isar conventions of `docs/projects/wasm-components.md` when moved out of `Silmaril/Raw`; the statements are
restated in `Silmaril.Wasm.JcoTool.KCore.Thms`.)

`feedLoop k` runs the compiled step of the kernel `k` on the bytes `IN[i..n)`, stopping when
the kernel is done (`KM.tr k`'s `done`, evaluated on the byte `0`). `feed_sound`: when it
finishes, the globals and memory hold `(KM.tr k).feed ks bs` (state and outputs appended), the
bounds checks passed (`fitsF`), and the input buffer, the handles and the async store are
unchanged (`FrameL`); `feed_complete`: when the bounds checks pass and there is fuel for every
byte, it finishes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCore

open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

/-- What the feed loop leaves alone. -/
structure FrameL (s s' : St) : Prop where
  st : s'.st = s.st
  rp : s'.rp = s.rp
  task : s'.task = s.task
  g : ∀ i, i ≠ GST → i ≠ BLEN → i ≠ OLEN → s'.g i = s.g i
  m : ∀ a, a < OUT → s'.m a = s.m a

theorem FrameL.refl (s : St) : FrameL s s := ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem FrameL.trans {s₁ s₂ s₃ : St} (h₁ : FrameL s₁ s₂) (h₂ : FrameL s₂ s₃) : FrameL s₁ s₃ :=
  ⟨h₂.st.trans h₁.st, h₂.rp.trans h₁.rp, h₂.task.trans h₁.task,
    fun i a b c => (h₂.g i a b c).trans (h₁.g i a b c), fun a ha => (h₂.m a ha).trans (h₁.m a ha)⟩

theorem Frame.toL {s s' : St} (h : Frame s s') : FrameL s s' := ⟨h.st, h.rp, h.task, h.g, h.m⟩

/-- A change of locals only. -/
theorem frameL_l (s : St) (l : Nat → Nat) : FrameL s { s with l := l } :=
  ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

/-- The body of the feed loop. -/
def body (k : KM) : S :=
  seqs [.brIf 1 (.bin .geu (.l LI) (.l LN)),
    .lset LB (.c 0), .brIf 1 (cE k.done),
    .lset LB (.ld8 (.bin .add (.c IN) (.l LI))), cS k.step,
    .lset LI (.bin .add (.l LI) (.c 1)), .br 0]

theorem feedLoop_eq (k : KM) : feedLoop k = .block (.loop (body k)) := rfl

/-- The kernel's `done` on the state held by the globals, the byte local being `0`. -/
theorem done_eval {s : St} {ks : KSt} (k : KM) (hst : s.g GST = ks.st) (hbl : s.g BLEN = ks.buf.length)
    (h0 : s.l LB = 0) : (cE k.done).eval s ≠ 0 ↔ k.tr.done ks = true := by
  rw [cE_eval hst hbl, h0]
  simp [KM.tr]

theorem body_exit (k : KM) (f : Nat) (s : St) (h : s.l LN ≤ s.l LI) :
    exec (body k) f s = some (.br 1, s) := by
  simp [body, seqs, exec, E.eval, Bin.eval, h]

/-- The state after `local.set LB 0`. -/
def s0 (s : St) : St := { s with l := upd s.l LB 0 }

theorem body_done (k : KM) (f : Nat) (s : St) (h : s.l LI < s.l LN)
    (hd : (cE k.done).eval (s0 s) ≠ 0) : exec (body k) f s = some (.br 1, s0 s) := by
  have h' : ¬ s.l LN ≤ s.l LI := Nat.not_le.mpr h
  simp only [body, seqs, exec, E.eval, Bin.eval, h', ↓reduceIte, ne_eq, not_true_eq_false]
  simp only [s0] at hd
  simp [hd, s0]

/-- The state after `local.set LB (load8 (IN + i))`. -/
def s1 (s : St) : St := { s with l := upd (upd s.l LB 0) LB (s.m ((IN + s.l LI) % M32)) }

theorem body_step_norm {k : KM} {f : Nat} {s s₂ : St} (h : s.l LI < s.l LN)
    (hd : (cE k.done).eval (s0 s) = 0) (h₂ : exec (cS k.step) f (s1 s) = some (.norm, s₂)) :
    exec (body k) f s = some (.br 0, { s₂ with l := upd s₂.l LI ((s₂.l LI + 1) % M32) }) := by
  have h' : ¬ s.l LN ≤ s.l LI := Nat.not_le.mpr h
  have hl : upd s.l LB 0 LI = s.l LI := by simp [upd_apply, LB, LI]
  simp only [s0] at hd
  simp only [s1] at h₂
  simp [body, seqs, exec, E.eval, Bin.eval, h', hd, hl, h₂]

theorem body_step_none {k : KM} {f : Nat} {s : St} (h : s.l LI < s.l LN)
    (hd : (cE k.done).eval (s0 s) = 0) (h₂ : exec (cS k.step) f (s1 s) = none) :
    exec (body k) f s = none := by
  have h' : ¬ s.l LN ≤ s.l LI := Nat.not_le.mpr h
  have hl : upd s.l LB 0 LI = s.l LI := by simp [upd_apply, LB, LI]
  simp only [s0] at hd
  simp only [s1] at h₂
  simp [body, seqs, exec, E.eval, Bin.eval, h', hd, hl, h₂]

/-- The invariant of the feed loop: the kernel state `ks` and the output `out` in globals and
memory, the counter `i` and the count `bs.length` in locals, the bytes `bs` in the input buffer. -/
structure LInv (s : St) (ks : KSt) (out bs : List Nat) (i : Nat) : Prop where
  rep : KRep s.g s.m ks out
  li : s.l LI = i
  ln : s.l LN = bs.length
  inb : slice s.m IN bs.length = bs
  le : i ≤ bs.length
  small : bs.length ≤ 256

/-- What the feed loop establishes when it stops. -/
def LPost (k : KM) (s : St) (ks : KSt) (out bs : List Nat) (i : Nat) (s' : St) : Prop :=
  fitsF k ks (bs.drop i) out.length = true ∧
    KRep s'.g s'.m (k.tr.feed ks (bs.drop i)).1 (out ++ (k.tr.feed ks (bs.drop i)).2) ∧ FrameL s s'

theorem feed_cons (k : KM) (ks : KSt) (b : Nat) (bs : List Nat) (hd : k.tr.done ks = false) :
    k.tr.feed ks (b :: bs) =
      ((k.tr.feed (k.step.exec b ks).1 bs).1, (k.step.exec b ks).2 ++ (k.tr.feed (k.step.exec b ks).1 bs).2) := by
  simp only [Tr.feed, hd, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem fitsF_cons (k : KM) (ks : KSt) (b : Nat) (bs : List Nat) (o : Nat) (hd : k.tr.done ks = false) :
    fitsF k ks (b :: bs) o =
      (fitsS b k.step ks o && fitsF k (k.step.exec b ks).1 bs (o + (k.step.exec b ks).2.length)) := by
  simp [fitsF, hd]

/-- The loop stops at once when the input is exhausted or the kernel is done. -/
theorem lpost_stop {k : KM} {s s' : St} {ks : KSt} {out bs : List Nat} {i : Nat}
    (hI : LInv s ks out bs i) (hs : s'.g = s.g ∧ s'.m = s.m) (hF : FrameL s s')
    (h : bs.length ≤ i ∨ k.tr.done ks = true) : LPost k s ks out bs i s' := by
  have hfeed : k.tr.feed ks (bs.drop i) = (ks, []) ∧ fitsF k ks (bs.drop i) out.length = true := by
    rcases h with h | h
    · simp [List.drop_eq_nil_of_le h, Tr.feed, fitsF]
    · cases hb : bs.drop i with
      | nil => simp [Tr.feed, fitsF]
      | cons b r => simp [Tr.feed, fitsF, h]
  refine ⟨hfeed.2, ?_, hF⟩
  rw [hfeed.1, hs.1, hs.2]
  simpa using hI.rep

/-- The byte local after `local.set LB (load8 (IN + i))` is the `i`th input byte. -/
theorem s1_byte {s : St} {ks : KSt} {out bs : List Nat} {i : Nat} (hI : LInv s ks out bs i)
    (hi : i < bs.length) : (s1 s).l LB = bs[i] := by
  have hm : (IN + s.l LI) % M32 = IN + i := by
    rw [hI.li]
    exact Nat.mod_eq_of_lt (by have := hI.small; simp [IN, M32]; omega)
  have hx : s.m (IN + i) = bs[i]'hi := by
    rw [← getElem_slice s.m IN bs.length i (by simpa [slice_length] using hi)]
    exact List.getElem_of_eq hI.inb _
  simp [s1, upd_apply, hm, hx]

/-- The locals after a step: the counter incremented, the count kept. -/
theorem linv_next {k : KM} {s s₂ : St} {ks : KSt} {out bs : List Nat} {i : Nat}
    (hI : LInv s ks out bs i) (hi : i < bs.length)
    (hP : Post k.step (s1 s) ks out .norm s₂) :
    LInv { s₂ with l := upd s₂.l LI ((s₂.l LI + 1) % M32) }
      (k.step.exec (bs[i]'hi) ks).1 (out ++ (k.step.exec (bs[i]'hi) ks).2) bs (i + 1) := by
  have hb : (s1 s).l LB = bs[i]'hi := s1_byte hI hi
  have hl : s₂.l = (s1 s).l := hP.2.2.2.l
  have hli : (s1 s).l LI = i := by simp [s1, upd_apply, show LI ≠ LB by decide, hI.li]
  have hln : (s1 s).l LN = bs.length := by simp [s1, upd_apply, show LN ≠ LB by decide, hI.ln]
  have hmem : ∀ a, a < OUT → s₂.m a = s.m a := hP.2.2.2.m
  refine ⟨by simpa [hb] using hP.2.2.1, ?_, ?_, ?_, hi, hI.small⟩
  · show upd s₂.l LI ((s₂.l LI + 1) % M32) LI = i + 1
    have hlt : (i + 1) % M32 = i + 1 := Nat.mod_eq_of_lt (by have := hI.small; simp [M32]; omega)
    simp [upd_apply, hl, hli, hlt]
  · show upd s₂.l LI ((s₂.l LI + 1) % M32) LN = bs.length
    simp [upd_apply, show LN ≠ LI by decide, hl, hln]
  · show slice s₂.m IN bs.length = bs
    have e : slice s₂.m IN bs.length = slice s.m IN bs.length :=
      slice_congr fun j hj => hmem _ (by have := hI.small; simp [IN, OUT]; omega)
    rw [e, hI.inb]

theorem drop_cons_getElem {bs : List Nat} {i : Nat} (hi : i < bs.length) :
    bs.drop i = bs[i] :: bs.drop (i + 1) := (List.drop_eq_getElem_cons hi)

/-- One more byte fed: the loop's result for `bs.drop (i + 1)` from the next state is its result
for `bs.drop i`. -/
theorem lpost_cons {k : KM} {s s₁ s' : St} {ks : KSt} {out bs : List Nat} {i : Nat}
    (hi : i < bs.length) (hd : k.tr.done ks = false)
    (hP : fitsS (bs[i]) k.step ks out.length = true) (hF : FrameL s s₁)
    (hQ : LPost k s₁ (k.step.exec (bs[i]) ks).1 (out ++ (k.step.exec (bs[i]) ks).2) bs (i + 1) s') :
    LPost k s ks out bs i s' := by
  have hdrop := drop_cons_getElem hi
  refine ⟨?_, ?_, hF.trans hQ.2.2⟩
  · rw [hdrop, fitsF_cons k ks _ _ _ hd, hP, Bool.true_and]
    simpa using hQ.1
  · rw [hdrop, feed_cons k ks _ _ hd]
    simpa [List.append_assoc] using hQ.2.1

/-- The feed loop with `fuel`, soundness. -/
def LoopSound (k : KM) (f fuel : Nat) : Prop :=
  ∀ {s s' : St} {o : Out} {ks : KSt} {out bs : List Nat} {i : Nat}, LInv s ks out bs i →
    loopN (exec (body k) f) fuel s = some (o, s') → o = .br 0 ∧ LPost k s ks out bs i s'

theorem loop_sound_succ (k : KM) (f : Nat) {fuel : Nat} (ih : LoopSound k f fuel) :
    LoopSound k f (fuel + 1) := by
    intro s s' o ks out bs i hI h
    by_cases hi : i < bs.length
    · show o = .br 0 ∧ LPost k s ks out bs i s'
      have hli : s.l LI < s.l LN := by rw [hI.li, hI.ln]; exact hi
      have hd0 : (s0 s).l LB = 0 := by simp [s0, upd_apply]
      have hR0 : KRep (s0 s).g (s0 s).m ks out := hI.rep
      by_cases hd : k.tr.done ks = true
      · show o = .br 0 ∧ LPost k s ks out bs i s'
        have hdn : (cE k.done).eval (s0 s) ≠ 0 := (done_eval k hR0.st hR0.blen hd0).mpr hd
        have hb : loopN (exec (body k) f) (fuel + 1) s = some (.br 0, s0 s) := by
          simp only [loopN, body_done k f s hli hdn]
        rw [hb] at h
        cases h
        exact ⟨rfl, lpost_stop hI ⟨rfl, rfl⟩ (frameL_l s _) (.inr hd)⟩
      · show o = .br 0 ∧ LPost k s ks out bs i s'
        have hdf : k.tr.done ks = false := by simpa using hd
        have hdz : (cE k.done).eval (s0 s) = 0 :=
          Classical.not_not.mp fun hne => hd ((done_eval k hR0.st hR0.blen hd0).mp hne)
        have hR1 : KRep (s1 s).g (s1 s).m ks out := hI.rep
        cases h₂ : exec (cS k.step) f (s1 s) with
        | none =>
          have hn : loopN (exec (body k) f) (fuel + 1) s = none := by
            simp only [loopN, body_step_none hli hdz h₂]
          rw [hn] at h
          cases h
        | some r =>
          show o = .br 0 ∧ LPost k s ks out bs i s'
          obtain ⟨o₂, s₂⟩ := r
          have hP : Post k.step (s1 s) ks out o₂ s₂ := cS_sound k.step hR1 h₂
          have ho₂ : o₂ = .norm := hP.2.1
          subst ho₂
          have hb1 : (s1 s).l LB = bs[i] := s1_byte hI hi
          have hfit : fitsS (bs[i]) k.step ks out.length = true := hb1 ▸ hP.1
          have hI₃ : LInv { s₂ with l := upd s₂.l LI ((s₂.l LI + 1) % M32) }
              (k.step.exec (bs[i]'hi) ks).1 (out ++ (k.step.exec (bs[i]'hi) ks).2) bs (i + 1) :=
            linv_next hI hi hP
          have hstep : loopN (exec (body k) f) (fuel + 1) s =
              loopN (exec (body k) f) fuel { s₂ with l := upd s₂.l LI ((s₂.l LI + 1) % M32) } := by
            simp only [loopN, body_step_norm hli hdz h₂]
          rw [hstep] at h
          obtain ⟨ho, hQ⟩ := ih hI₃ h
          have hF : FrameL s { s₂ with l := upd s₂.l LI ((s₂.l LI + 1) % M32) } :=
            ((frameL_l s _).trans hP.2.2.2.toL).trans (frameL_l s₂ _)
          exact ⟨ho, lpost_cons hi hdf hfit hF hQ⟩
    · show o = .br 0 ∧ LPost k s ks out bs i s'
      have hex : s.l LN ≤ s.l LI := by rw [hI.li, hI.ln]; omega
      have hb : loopN (exec (body k) f) (fuel + 1) s = some (.br 0, s) := by
        simp only [loopN, body_exit k f s hex]
      rw [hb] at h
      cases h
      exact ⟨rfl, lpost_stop hI ⟨rfl, rfl⟩ (FrameL.refl s) (.inl (by omega))⟩

/-- **The feed loop, soundness.** -/
theorem loop_sound (k : KM) (f : Nat) : ∀ (fuel : Nat) {s s' : St} {o : Out} {ks : KSt}
    {out bs : List Nat} {i : Nat}, LInv s ks out bs i →
    loopN (exec (body k) f) fuel s = some (o, s') → o = .br 0 ∧ LPost k s ks out bs i s' := by
  intro fuel
  induction fuel with
  | zero => intro s s' o ks out bs i _ h; cases h
  | succ fuel ih => exact loop_sound_succ k f ih

/-- **The feed loop, completeness**: with the bounds checks passing and fuel for every byte,
the loop finishes. -/
def LoopDone (k : KM) (f fuel : Nat) : Prop :=
  ∀ {s : St} {ks : KSt} {out bs : List Nat} {i : Nat}, LInv s ks out bs i →
    fitsF k ks (bs.drop i) out.length = true → bs.length - i < fuel →
    ∃ s', loopN (exec (body k) f) fuel s = some (.br 0, s')

theorem loop_complete_succ (k : KM) (f : Nat) {fuel : Nat} (ih : LoopDone k f fuel) :
    LoopDone k f (fuel + 1) := by
    intro s ks out bs i hI hf hfuel
    by_cases hi : i < bs.length
    · show ∃ s', loopN (exec (body k) f) (fuel + 1) s = some (.br 0, s')
      have hli : s.l LI < s.l LN := by rw [hI.li, hI.ln]; exact hi
      have hd0 : (s0 s).l LB = 0 := by simp [s0, upd_apply]
      have hR0 : KRep (s0 s).g (s0 s).m ks out := hI.rep
      by_cases hd : k.tr.done ks = true
      · have hdn : (cE k.done).eval (s0 s) ≠ 0 := (done_eval k hR0.st hR0.blen hd0).mpr hd
        exact ⟨s0 s, by simp only [loopN, body_done k f s hli hdn]⟩
      · show ∃ s', loopN (exec (body k) f) (fuel + 1) s = some (.br 0, s')
        have hdf : k.tr.done ks = false := by simpa using hd
        have hdz : (cE k.done).eval (s0 s) = 0 :=
          Classical.not_not.mp fun hne => hd ((done_eval k hR0.st hR0.blen hd0).mp hne)
        have hR1 : KRep (s1 s).g (s1 s).m ks out := hI.rep
        have hb1 : (s1 s).l LB = bs[i] := s1_byte hI hi
        have hf' : fitsS (bs[i]) k.step ks out.length = true ∧
            fitsF k (k.step.exec (bs[i]) ks).1 (bs.drop (i + 1))
              (out.length + (k.step.exec (bs[i]) ks).2.length) = true := by
          rw [drop_cons_getElem hi, fitsF_cons k ks _ _ _ hdf] at hf
          simpa using hf
        obtain ⟨s₂, h₂⟩ := cS_complete k.step (f := f) hR1 (by rw [hb1]; exact hf'.1)
        have hP : Post k.step (s1 s) ks out .norm s₂ := cS_sound k.step hR1 h₂
        obtain ⟨s', h'⟩ := ih (linv_next hI hi hP) (by simpa using hf'.2) (by omega)
        exact ⟨s', by simp only [loopN, body_step_norm hli hdz h₂, h']⟩
    · have hex : s.l LN ≤ s.l LI := by rw [hI.li, hI.ln]; omega
      exact ⟨s, by simp only [loopN, body_exit k f s hex]⟩

theorem loop_complete (k : KM) (f : Nat) : ∀ (fuel : Nat) {s : St} {ks : KSt}
    {out bs : List Nat} {i : Nat}, LInv s ks out bs i → fitsF k ks (bs.drop i) out.length = true →
    bs.length - i < fuel → ∃ s', loopN (exec (body k) f) fuel s = some (.br 0, s') := by
  intro fuel
  induction fuel with
  | zero => intro s ks out bs i _ _ h; omega
  | succ fuel ih => exact loop_complete_succ k f ih

/-- **The feed loop as a statement**: when it finishes, it finishes normally with `LPost`. -/
theorem feed_sound {k : KM} {f : Nat} {s s' : St} {o : Out} {ks : KSt} {out bs : List Nat}
    (hI : LInv s ks out bs 0) (h : exec (feedLoop k) f s = some (o, s')) :
    o = .norm ∧ LPost k s ks out bs 0 s' := by
  rw [feedLoop_eq] at h
  cases hl : loopN (exec (body k) f) f s with
  | none =>
    have hn : exec (.block (.loop (body k))) f s = none := by simp only [exec, hl, lab_none]
    rw [hn] at h
    cases h
  | some r =>
    obtain ⟨o₁, s₁⟩ := r
    obtain ⟨rfl, hP⟩ := loop_sound k f f hI hl
    have hb : exec (.block (.loop (body k))) f s = some (.norm, s₁) := by simp only [exec, hl]; rfl
    rw [hb] at h
    cases h
    exact ⟨rfl, hP⟩

theorem feed_complete {k : KM} {f : Nat} {s : St} {ks : KSt} {out bs : List Nat}
    (hI : LInv s ks out bs 0) (hf : fitsF k ks bs out.length = true) (hfuel : bs.length < f) :
    ∃ s', exec (feedLoop k) f s = some (.norm, s') := by
  obtain ⟨s', h⟩ := loop_complete k f f hI (by simpa using hf) (by omega)
  exact ⟨s', by rw [feedLoop_eq]; simp only [exec, h]; rfl⟩

end Silmaril.Proofs.Wasm.JcoTool.KCore
