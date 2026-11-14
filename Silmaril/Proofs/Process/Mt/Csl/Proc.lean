module

public import Silmaril.Process.Mt.Csl.Proc.Defs

/-!
# The process refines the thread machine (proofs)

Every `MtStep` under SC is a run of `procT` from the encoded configuration (`step_reach`): one
step, except a `futex` wake and an `exit` that wakes a waiter, which are the waker's step
followed by one `wake` step per woken waiter (`wake_reach`). Process faults are thread-machine
faults (`fault_enc`).
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Csl.Proc

open Silmaril.Process.Mt
open Silmaril.Process.Mt.Csl
open Silmaril.Process.Mt.Csl.Proc

variable {γ : Type} {U : UIsa γ} {P : PrimTable γ} {base : Base γ}

theorem star_trans {α : Type} {r : α → α → Prop} {a b c : α} (h1 : Star r a b)
    (h2 : Star r b c) : Star r a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Star.step h (ih h2)

theorem star_one {α : Type} {r : α → α → Prop} {a b : α} (h : r a b) : Star r a b :=
  Star.step h Star.refl

/-- Waking a list of distinct waiters: one `wake` step each. -/
theorem wake_reach {G : Glob γ} (hl : G.Live U) {a : Nat} :
    ∀ {ws : List Nat} {th : Nat → Option (TRec U.St)}, ws.Nodup → (∀ w ∈ ws, Waiting th a w) →
      Reach (procT U P base) ⟨th, G⟩ ⟨wakeAll th ws, G⟩
  | [], th, _, _ => by
    have e : wakeAll th [] = th := by funext x; simp [wakeAll]
    rw [e]; exact Star.refl
  | w :: rest, th, hnd, hw => by
    obtain ⟨r, k, hth, hst⟩ := hw w (by simp)
    have hnd' := List.nodup_cons.mp hnd
    have st1 : Step (procT U P base) ⟨th, G⟩
        ⟨Heap.upd th w (some { r with st := .run (k 0) }), G⟩ :=
      Step.atom hth ⟨hl, PAtom.wake hst⟩
    have ih : Reach (procT U P base) ⟨Heap.upd th w (some { r with st := .run (k 0) }), G⟩ _ :=
      wake_reach hl (ws := rest) (th := Heap.upd th w (some { r with st := .run (k 0) })) hnd'.2
      (fun x hx => by
        obtain ⟨r', k', h1, h2⟩ := hw x (by simp [hx])
        have hxw : x ≠ w := fun e => hnd'.1 (e ▸ hx)
        exact ⟨r', k', by simp [Heap.upd, hxw, h1], h2⟩)
    have e : wakeAll (Heap.upd th w (some { r with st := .run (k 0) })) rest =
        wakeAll th (w :: rest) := by
      funext x
      by_cases hxw : x = w
      · subst hxw; simp [wakeAll, Heap.upd, hnd'.1, hth, TRec.wake, hst]
      · simp [wakeAll, Heap.upd, hxw]
    rw [← e]; exact Star.step st1 ih

/-- A running thread is not among the waiters. -/
theorem not_waiting {th : Nat → Option (TRec U.St)} {t : Nat} {r : TRec U.St} {s : U.St}
    (ht : th t = some r) (hr : r.st = .run s) {a : Nat} : ¬ Waiting th a t := by
  rintro ⟨r', k, h1, h2⟩
  rw [ht] at h1; cases h1; rw [hr] at h2; cases h2

theorem step_reach {C C' : MtCfg U.St γ sc.S} (h : MtStep U sc P base C C') :
    Reach (procT U P base) (enc P base C) (enc P base C') := by
  cases h with
  | user hl ht hr hs hm =>
    cases hm
    exact star_one (Step.loc ht ⟨hl, PPlain.user hr hs⟩)
  | lib hl ht hr hy hs => exact star_one (Step.atom ht ⟨hl, PAtom.lib hr hs⟩)
  | prim hl ht hr hy hs hp hpre hpost =>
    exact star_one (Step.atom ht ⟨hl, PAtom.prim hr hs hp hpre hpost⟩)
  | gettid hl ht hr hy hs => exact star_one (Step.atom ht ⟨hl, PAtom.gettid hr hs⟩)
  | setTid hl ht hr hy hs => exact star_one (Step.atom ht ⟨hl, PAtom.setTid hr hs⟩)
  | futexBlock hl ht hr hy hs hop hal hw =>
    exact star_one (Step.atom ht ⟨hl, PAtom.futexBlock hr hs hop hal hw⟩)
  | futexAgain hl ht hr hy hs hop hal hw hne =>
    exact star_one (Step.atom ht ⟨hl, PAtom.futexAgain hr hs hop hal hw hne⟩)
  | @futexWake t r s a op n args k ch ws hl ht hr hy hs hop hal hws =>
    have st1 := Step.atom (U := procT U P base) (C := enc P base C) ht ⟨hl, PAtom.futexWake (c := ws.length) hr hs hop hal hws.2.1⟩
    refine Star.step st1 ?_
    have hw := wake_reach (P := P) (base := base) (G := (enc P base C).mem) hl (a := a.toNat)
      (ws := ws) (th := Heap.upd C.th t (some { r with st := .run (k (BitVec.ofNat 64 ws.length)) }))
      hws.1 (fun w hw => by
        obtain ⟨r', k', h1, h2⟩ := hws.2.2 w hw
        have hwt : w ≠ t := fun e => not_waiting ht hr (e ▸ hws.2.2 w hw)
        exact ⟨r', k', by simp [Heap.upd, hwt, h1], h2⟩)
    have e : wakeAll (Heap.upd C.th t (some { r with st := .run (k (BitVec.ofNat 64 ws.length)) })) ws =
        setTh (wakeAll C.th ws) t { r with st := .run (k (BitVec.ofNat 64 ws.length)) } := by
      funext x
      by_cases hxt : x = t
      · subst hxt
        have : x ∉ ws := fun hx => not_waiting ht hr (hws.2.2 x hx)
        simp [wakeAll, Heap.upd, setTh, upd, this]
      · simp [wakeAll, Heap.upd, setTh, upd, hxt]
    rw [e] at hw
    exact hw
  | spurious hl ht hr => exact star_one (Step.atom ht ⟨hl, PAtom.wake hr⟩)
  | clone hl ht hr hy hs hf hfresh h0 hmax hpt =>
    exact star_one (Step.spawn ht hfresh ⟨hl, PSpawn.clone hr hs hf h0 hmax hpt⟩)
  | @exitClear t r s code args k ch a ws m' hl ht hr hy hs hct hmap hlive hws =>
    have st1 := Step.atom (U := procT U P base) (C := enc P base C) ht ⟨hl, PAtom.exitClear hr hs hct hmap⟩
    refine Star.step st1 ?_
    exact wake_reach (U := U) (P := P) (base := base) (G := { (enc P base C).mem with mem := m' })
      hl hws.1 hws.2.2
  | @exitPlain t r s code args k ch hl ht hr hy hs hnc =>
    refine star_one (Step.atom (U := procT U P base) (C := enc P base C) ht ⟨hl, PAtom.exitPlain hr hs ?_⟩)
    unfold lastExit; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  | @exitGroup t r s code args k ch hl ht hr hy hs =>
    have st := Step.atom (U := procT U P base) (C := enc P base C) ht
      ⟨hl, PAtom.exitGroup (G := (enc P base C).mem) hr hs⟩
    have e : Heap.upd (enc P base C).th t (some r) = (enc P base C).th := by
      funext x
      by_cases hx : x = t
      · subst hx; simp only [Heap.upd]; exact ht.symm
      · simp [Heap.upd, hx]
    rw [e] at st
    exact star_one st
  | base hl ht hr hy hs hn hb => exact star_one (Step.atom ht ⟨hl, PAtom.base hr hs hn hb⟩)
  | flush hf => exact (hf : False).elim

theorem reach_reach {C C' : MtCfg U.St γ sc.S} (h : MtReach U sc P base C C') :
    Reach (procT U P base) (enc P base C) (enc P base C') := by
  induction h with
  | refl => exact Star.refl
  | tail _ hs ih => exact star_trans ih (step_reach hs)

theorem fault_enc {C : MtCfg U.St γ sc.S} (h : MtFault U sc P C) :
    Fault (procT U P base) (enc P base C) := by
  obtain ⟨hl, t, r, s, hth, hr, h | ⟨p, args, k, hs, hn⟩⟩ := h
  · exact ⟨t, r, hth, Or.inl ⟨hl, s, hr, h⟩⟩
  · exact ⟨t, r, hth, Or.inr ⟨hl, s, p, args, k, hr, hs, hn⟩⟩

end Silmaril.Proofs.Process.Mt.Csl.Proc
