module

public import Silmaril.Wasm.Component.Streams.ACancel.Defs
public import Silmaril.Wasm.Component.Streams.Cancel.Thms

/-!
# Asynchronous cancellation: item flow

Every operation on an `AChan` is an operation of `Cancel` on its `DChan`, or leaves the `DChan`
unchanged (a cancel that returns `BLOCKED` only sets the flag; handing an end to the host only
changes the flags); likewise for futures. So `Cancel.csteps_sent` and `Cancel.fsteps_once` carry
over (`asteps_sent`, `afsteps_once`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.ACancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res packCopy blocked)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Cancel
open Silmaril.Wasm.Component.Streams.ACancel

theorem read_cstep {a a' : AChan} {n : Nat} {r : Res} (h : a.read n = some (a', r)) :
    CStep a.c a'.c (delivered r) := by
  obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
  have ha : a' = { a with c := q.1 } := (Prod.mk.inj he).1.symm
  have hr : r = q.2 := (Prod.mk.inj he).2.symm
  rw [ha, hr]
  exact CStep.read hq

theorem write_cstep {a a' : AChan} {xs : List Val} {r : Res} (h : a.write xs = some (a', r)) :
    CStep a.c a'.c [] := by
  obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
  have ha : a' = { a with c := q.1 } := (Prod.mk.inj he).1.symm
  rw [ha]
  exact CStep.write hq

theorem dropR_cstep {a a' : AChan} (h : a.dropR = some a') : CStep a.c a'.c [] := by
  obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
  rw [← he]
  exact CStep.dropR hq

theorem dropW_cstep {a a' : AChan} (h : a.dropW = some a') : CStep a.c a'.c [] := by
  obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
  rw [← he]
  exact CStep.dropW hq

/-- The `DChan` part of an event delivery is `Drop`'s. -/
theorem takeR_c {a a' : AChan} {p : Nat} {ys : List Val} (h : a.takeR = some (a', p, ys)) :
    ∃ p', a.c.takeR = some (a'.c, p', ys) := by
  unfold AChan.takeR at h
  unfold DChan.takeR
  cases he : a.c.r.ev with
  | none => rw [he] at h; cases h
  | some q =>
    rw [he] at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨-, h3⟩ := Prod.mk.inj h2
    rw [← h1, ← h3]
    exact ⟨_, rfl⟩

theorem takeW_c {a a' : AChan} {p : Nat} (h : a.takeW = some (a', p)) :
    ∃ p', a.c.takeW = some (a'.c, p') := by
  unfold AChan.takeW at h
  unfold DChan.takeW
  cases he : a.c.w.ev with
  | none => rw [he] at h; cases h
  | some q =>
    rw [he] at h
    obtain ⟨h1, -⟩ := Prod.mk.inj (Option.some.inj h)
    rw [← h1]
    exact ⟨_, rfl⟩

/-- The event `End.cancel` leaves on the readable end is the pending one, or a new one with
progress `0`. -/
theorem startCancelR_ev {a : AChan} {now : Bool} {q : Nat}
    (h : (a.startCancelR now).c.r.ev = some q) : q = a.c.r.ev.getD 0 := by
  unfold AChan.startCancelR at h
  by_cases hc : a.c.r.ev = none ∧ (a.f.hostW = false ∨ now = true)
  · simp only [hc, and_self, ↓reduceIte] at h
    simp [hc.1, ← Option.some.inj h]
  · simp only [hc, ↓reduceIte] at h
    simp [h]

theorem startCancelR_none {a : AChan} {now : Bool} (h : (a.startCancelR now).c.r.ev = none) :
    (a.startCancelR now).c = a.c := by
  unfold AChan.startCancelR at h ⊢
  by_cases hc : a.c.r.ev = none ∧ (a.f.hostW = false ∨ now = true)
  · simp [hc] at h
  · simp [hc]

theorem startCancelW_ev {a : AChan} {now : Bool} {q : Nat}
    (h : (a.startCancelW now).c.w.ev = some q) : q = a.c.w.ev.getD 0 := by
  unfold AChan.startCancelW at h
  by_cases hc : a.c.w.ev = none ∧ (a.f.hostR = false ∨ now = true)
  · simp only [hc, and_self, ↓reduceIte] at h
    simp [hc.1, ← Option.some.inj h]
  · simp only [hc, ↓reduceIte] at h
    simp [h]

theorem startCancelW_none {a : AChan} {now : Bool} (h : (a.startCancelW now).c.w.ev = none) :
    (a.startCancelW now).c = a.c := by
  unfold AChan.startCancelW at h ⊢
  by_cases hc : a.c.w.ev = none ∧ (a.f.hostR = false ∨ now = true)
  · simp [hc] at h
  · simp [hc]

theorem takeR_none {a : AChan} (h : a.takeR = none) : a.c.r.ev = none := by
  unfold AChan.takeR at h
  split at h
  · assumption
  · cases h

theorem takeW_none {a : AChan} (h : a.takeW = none) : a.c.w.ev = none := by
  unfold AChan.takeW at h
  split at h
  · assumption
  · cases h

/-- An immediate cancel of a read is `Cancel.cancelR` on the `DChan`. -/
theorem cancelR_now {a b' : AChan} {now : Bool} {p : Nat} {ys : List Val}
    (hg : a.c.r.gone = false) (hc : a.c.r.st = .copying)
    (ht : (a.startCancelR now).takeR = some (b', p, ys)) :
    ∃ r, a.c.cancelR = some (b'.c, r) ∧ delivered r = ys := by
  unfold AChan.takeR at ht
  split at ht
  · cases ht
  · rename_i q hq
    have h1 := (Prod.mk.inj (Option.some.inj ht)).1
    have h3 := (Prod.mk.inj (Prod.mk.inj (Option.some.inj ht)).2).2
    refine ⟨.read (if a.c.w.gone then packCopy .dropped (a.c.r.ev.getD 0)
      else packCopy .cancelled (a.c.r.ev.getD 0)) a.c.rgot, ?_, ?_⟩
    · rw [← h1]
      simp [DChan.cancelR, hg, hc, AChan.startCancelR]
    · rw [← h3]
      simp [delivered, AChan.startCancelR]

/-- An immediate cancel of a write is `Cancel.cancelW` on the `DChan`. -/
theorem cancelW_now {a b' : AChan} {now : Bool} {p : Nat}
    (hg : a.c.w.gone = false) (hc : a.c.w.st = .copying)
    (ht : (a.startCancelW now).takeW = some (b', p)) :
    ∃ r, a.c.cancelW = some (b'.c, r) := by
  unfold AChan.takeW at ht
  split at ht
  · cases ht
  · have h1 := (Prod.mk.inj (Option.some.inj ht)).1
    refine ⟨.nat (if a.c.r.gone then packCopy .dropped (a.c.w.ev.getD 0)
      else packCopy .cancelled (a.c.w.ev.getD 0)), ?_⟩
    rw [← h1]
    simp [DChan.cancelW, hg, hc, AChan.startCancelW]

theorem guard_r {a : AChan} (hg : ¬(a.c.r.gone = true ∨ a.c.r.st ≠ .copying ∨ a.f.rc = true)) :
    a.c.r.gone = false ∧ a.c.r.st = .copying := by
  simp only [not_or, Bool.not_eq_true, ne_eq, not_not] at hg
  exact ⟨hg.1, hg.2.1⟩

theorem guard_w {a : AChan} (hg : ¬(a.c.w.gone = true ∨ a.c.w.st ≠ .copying ∨ a.f.wc = true)) :
    a.c.w.gone = false ∧ a.c.w.st = .copying := by
  simp only [not_or, Bool.not_eq_true, ne_eq, not_not] at hg
  exact ⟨hg.1, hg.2.1⟩

/-- What a cancel of a read did: delivered its event at once, or returned `BLOCKED`. -/
theorem cancelR_inv {a a' : AChan} {now : Bool} {r : Res} (h : a.cancelR now = some (a', r)) :
    a.c.r.gone = false ∧ a.c.r.st = .copying ∧
      ((∃ p ys, (a.startCancelR now).takeR = some (a', p, ys) ∧ r = .read p ys) ∨
        ((a.startCancelR now).takeR = none ∧ a' = a.startCancelR now ∧ r = .nat blocked)) := by
  unfold AChan.cancelR at h
  split at h
  · cases h
  · rename_i hg
    refine ⟨(guard_r hg).1, (guard_r hg).2, ?_⟩
    dsimp only at h
    split at h
    · rename_i b' p ys ht
      cases h
      exact Or.inl ⟨p, ys, ht, rfl⟩
    · rename_i ht
      cases h
      exact Or.inr ⟨ht, rfl, rfl⟩

/-- What a cancel of a write did. -/
theorem cancelW_inv {a a' : AChan} {now : Bool} {r : Res} (h : a.cancelW now = some (a', r)) :
    a.c.w.gone = false ∧ a.c.w.st = .copying ∧
      ((∃ p, (a.startCancelW now).takeW = some (a', p) ∧ r = .nat p) ∨
        ((a.startCancelW now).takeW = none ∧ a' = a.startCancelW now ∧ r = .nat blocked)) := by
  unfold AChan.cancelW at h
  split at h
  · cases h
  · rename_i hg
    refine ⟨(guard_w hg).1, (guard_w hg).2, ?_⟩
    dsimp only at h
    split at h
    · rename_i b' p ht
      cases h
      exact Or.inl ⟨p, ht, rfl⟩
    · rename_i ht
      cases h
      exact Or.inr ⟨ht, rfl, rfl⟩

/-- A cancel of a read: `Cancel.cancelR` on the `DChan` when it delivers at once, nothing when it
returns `BLOCKED`. -/
theorem cancelR_cstep {a a' : AChan} {now : Bool} {r : Res} (h : a.cancelR now = some (a', r)) :
    CStep a.c a'.c (delivered r) ∨ (a'.c = a.c ∧ delivered r = []) := by
  obtain ⟨hg, hc, hcase⟩ := cancelR_inv h
  rcases hcase with ⟨p, ys, ht, hr⟩ | ⟨ht, ha, hr⟩
  · obtain ⟨r', hr', hd⟩ := cancelR_now hg hc ht
    have hdel : delivered r = ys := by rw [hr]; rfl
    exact Or.inl (hdel ▸ hd ▸ CStep.cancelR hr')
  · have hc' : a'.c = a.c := ha ▸ startCancelR_none (takeR_none ht)
    have hdel : delivered r = [] := by rw [hr]; rfl
    exact Or.inr ⟨hc', hdel⟩

theorem cancelW_cstep {a a' : AChan} {now : Bool} {r : Res} (h : a.cancelW now = some (a', r)) :
    CStep a.c a'.c [] ∨ a'.c = a.c := by
  obtain ⟨hg, hc, hcase⟩ := cancelW_inv h
  rcases hcase with ⟨p, ht, -⟩ | ⟨ht, ha, -⟩
  · obtain ⟨r', hr'⟩ := cancelW_now hg hc ht
    exact Or.inl (CStep.cancelW hr')
  · exact Or.inr (ha ▸ startCancelW_none (takeW_none ht))

/-- **Every operation on a stream is one of `Cancel`'s on its `DChan`, or leaves it unchanged.** -/
theorem astep_cstep {a a' : AChan} {zs : List Val} (h : AStep a a' zs) :
    CStep a.c a'.c zs ∨ (a'.c = a.c ∧ zs = []) := by
  cases h with
  | read h => exact Or.inl (read_cstep h)
  | write h => exact Or.inl (write_cstep h)
  | cancelR h => exact cancelR_cstep h
  | cancelW h =>
    rcases cancelW_cstep h with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', rfl⟩
  | takeR h =>
    obtain ⟨p', hp⟩ := takeR_c h
    exact Or.inl (CStep.takeR hp)
  | takeW h =>
    obtain ⟨p', hp⟩ := takeW_c h
    exact Or.inl (CStep.takeW hp)
  | dropR h => exact Or.inl (dropR_cstep h)
  | dropW h => exact Or.inl (dropW_cstep h)
  | give => exact Or.inr ⟨rfl, rfl⟩

/-- Operations of this variant are operations of `Cancel`. -/
theorem asteps_csteps {a a' : AChan} {ys : List Val} (h : ASteps a a' ys) : CSteps a.c a'.c ys := by
  induction h with
  | refl => exact CSteps.refl _
  | tail _ hs ih =>
    rcases astep_cstep hs with h' | ⟨h₁, h₂⟩
    · exact CSteps.tail ih h'
    · rw [h₁, h₂, List.append_nil]
      exact ih

theorem asteps_sent {a : AChan} {ys : List Val} (h : ASteps {} a ys) : a.c.sent = ys ++ a.c.rgot :=
  csteps_sent (asteps_csteps h)

/-! ## Futures -/

theorem fstartR_none {a : AFChan} {now : Bool} (h : (a.startCancelR now).c.r.ev = none) :
    (a.startCancelR now).c = a.c := by
  unfold AFChan.startCancelR at h ⊢
  by_cases hc : a.c.r.ev = none ∧ (a.f.hostW = false ∨ now = true)
  · simp [hc] at h
  · simp [hc]

theorem fstartW_none {a : AFChan} {now : Bool} (h : (a.startCancelW now).c.w.ev = none) :
    (a.startCancelW now).c = a.c := by
  unfold AFChan.startCancelW at h ⊢
  by_cases hc : a.c.w.ev = none ∧ (a.f.hostR = false ∨ now = true)
  · simp [hc] at h
  · simp [hc]

/-- With a pending event after `End.cancel`, its `FChan` is the one `fcancelR` delivers from. -/
theorem fstartR_some {a : AFChan} {now : Bool} {q : Nat} (h : (a.startCancelR now).c.r.ev = some q) :
    (a.startCancelR now).c = { a.c with r := { a.c.r with ev := some (a.c.r.ev.getD 0) } } := by
  unfold AFChan.startCancelR at h ⊢
  by_cases hc : a.c.r.ev = none ∧ (a.f.hostW = false ∨ now = true)
  · simp [hc]
  · simp only [hc, ↓reduceIte] at h ⊢
    simp [h]

theorem fstartW_some {a : AFChan} {now : Bool} {q : Nat} (h : (a.startCancelW now).c.w.ev = some q) :
    (a.startCancelW now).c = { a.c with w := { a.c.w with ev := some (a.c.w.ev.getD 0) } } := by
  unfold AFChan.startCancelW at h ⊢
  by_cases hc : a.c.w.ev = none ∧ (a.f.hostR = false ∨ now = true)
  · simp [hc]
  · simp only [hc, ↓reduceIte] at h ⊢
    simp [h]

theorem ftakeR_ev {c : FChan} (h : c.ftakeR = none) : c.r.ev = none := by
  unfold FChan.ftakeR at h
  split at h
  · assumption
  · split at h <;> (try split at h) <;> cases h

theorem ftakeW_ev {c : FChan} (h : c.ftakeW = none) : c.w.ev = none := by
  unfold FChan.ftakeW at h
  split at h
  · assumption
  · split at h <;> (try split at h) <;> cases h

theorem ftakeR_some_ev {c c' : FChan} {p : Nat × List Val} (h : c.ftakeR = some (c', p)) :
    ∃ q, c.r.ev = some q := by
  unfold FChan.ftakeR at h
  split at h
  · cases h
  · exact ⟨_, by assumption⟩

theorem ftakeW_some_ev {c c' : FChan} {p : Nat} (h : c.ftakeW = some (c', p)) :
    ∃ q, c.w.ev = some q := by
  unfold FChan.ftakeW at h
  split at h
  · cases h
  · exact ⟨_, by assumption⟩

theorem fguard_r {a : AFChan} (hg : ¬(a.c.r.gone = true ∨ a.c.r.st ≠ .copying ∨ a.f.rc = true)) :
    a.c.r.gone = false ∧ a.c.r.st = .copying := by
  simp only [not_or, Bool.not_eq_true, ne_eq, not_not] at hg
  exact ⟨hg.1, hg.2.1⟩

theorem fguard_w {a : AFChan} (hg : ¬(a.c.w.gone = true ∨ a.c.w.st ≠ .copying ∨ a.f.wc = true)) :
    a.c.w.gone = false ∧ a.c.w.st = .copying := by
  simp only [not_or, Bool.not_eq_true, ne_eq, not_not] at hg
  exact ⟨hg.1, hg.2.1⟩

/-- What a cancel of a future read did. -/
theorem fcancelR_inv {a a' : AFChan} {now : Bool} {r : Res} (h : a.cancelR now = some (a', r)) :
    a.c.r.gone = false ∧ a.c.r.st = .copying ∧
      ((∃ p ys, (a.startCancelR now).takeR = some (a', p, ys) ∧ r = .read p ys) ∨
        ((a.startCancelR now).takeR = none ∧ a' = a.startCancelR now ∧ r = .nat blocked)) := by
  unfold AFChan.cancelR at h
  split at h
  · cases h
  · rename_i hg
    refine ⟨(fguard_r hg).1, (fguard_r hg).2, ?_⟩
    dsimp only at h
    split at h
    · rename_i b' p ys ht
      cases h
      exact Or.inl ⟨p, ys, ht, rfl⟩
    · rename_i ht
      cases h
      exact Or.inr ⟨ht, rfl, rfl⟩

theorem fcancelW_inv {a a' : AFChan} {now : Bool} {r : Res} (h : a.cancelW now = some (a', r)) :
    a.c.w.gone = false ∧ a.c.w.st = .copying ∧
      ((∃ p, (a.startCancelW now).takeW = some (a', p) ∧ r = .nat p) ∨
        ((a.startCancelW now).takeW = none ∧ a' = a.startCancelW now ∧ r = .nat blocked)) := by
  unfold AFChan.cancelW at h
  split at h
  · cases h
  · rename_i hg
    refine ⟨(fguard_w hg).1, (fguard_w hg).2, ?_⟩
    dsimp only at h
    split at h
    · rename_i b' p ht
      cases h
      exact Or.inl ⟨p, ht, rfl⟩
    · rename_i ht
      cases h
      exact Or.inr ⟨ht, rfl, rfl⟩

/-- An immediate cancel of a future read is `fcancelR` on the `FChan`. -/
theorem fcancelR_now {a a' : AFChan} {now : Bool} {p : Nat} {ys : List Val}
    (hg : a.c.r.gone = false) (hc : a.c.r.st = .copying)
    (ht : (a.startCancelR now).takeR = some (a', p, ys)) : a.c.fcancelR = some (a'.c, p, ys) := by
  obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.1 ht
  obtain ⟨v, hv⟩ := ftakeR_some_ev hq
  have hc' : (a.startCancelR now).c = { a.c with r := { a.c.r with ev := some (a.c.r.ev.getD 0) } } :=
    fstartR_some hv
  have hq' : FChan.ftakeR { a.c with r := { a.c.r with ev := some (a.c.r.ev.getD 0) } } = some q :=
    hc' ▸ hq
  have hcan : a.c.fcancelR = some q := by
    unfold FChan.fcancelR
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [hg, hc]))]
    exact hq'
  have ha : a'.c = q.1 := by rw [← (Prod.mk.inj hqe).1]
  have hp : (p, ys) = q.2 := (Prod.mk.inj hqe).2.symm
  rw [hcan, ha, hp]

theorem fcancelW_now {a a' : AFChan} {now : Bool} {p : Nat}
    (hg : a.c.w.gone = false) (hc : a.c.w.st = .copying)
    (ht : (a.startCancelW now).takeW = some (a', p)) : a.c.fcancelW = some (a'.c, p) := by
  obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.1 ht
  obtain ⟨v, hv⟩ := ftakeW_some_ev hq
  have hc' : (a.startCancelW now).c = { a.c with w := { a.c.w with ev := some (a.c.w.ev.getD 0) } } :=
    fstartW_some hv
  have hq' : FChan.ftakeW { a.c with w := { a.c.w with ev := some (a.c.w.ev.getD 0) } } = some q :=
    hc' ▸ hq
  have hcan : a.c.fcancelW = some q := by
    unfold FChan.fcancelW
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [hg, hc]))]
    exact hq'
  have ha : a'.c = q.1 := by rw [← (Prod.mk.inj hqe).1]
  have hp : p = q.2 := (Prod.mk.inj hqe).2.symm
  rw [hcan, ha, hp]

theorem ftakeR_none' {a : AFChan} (h : a.takeR = none) : a.c.r.ev = none := by
  cases hx : a.c.ftakeR with
  | none => exact ftakeR_ev hx
  | some y => simp [AFChan.takeR, hx] at h

theorem ftakeW_none' {a : AFChan} (h : a.takeW = none) : a.c.w.ev = none := by
  cases hx : a.c.ftakeW with
  | none => exact ftakeW_ev hx
  | some y => simp [AFChan.takeW, hx] at h

theorem fcancelR_fstep {a a' : AFChan} {now : Bool} {r : Res} (h : a.cancelR now = some (a', r)) :
    FStep a.c a'.c (delivered r) ∨ (a'.c = a.c ∧ delivered r = []) := by
  obtain ⟨hg, hc, hcase⟩ := fcancelR_inv h
  rcases hcase with ⟨p, ys, ht, hr⟩ | ⟨ht, ha, hr⟩
  · have hdel : delivered r = ys := by rw [hr]; rfl
    exact Or.inl (hdel ▸ FStep.cancelR (fcancelR_now hg hc ht))
  · have hc' : a'.c = a.c := ha ▸ fstartR_none (ftakeR_none' ht)
    have hdel : delivered r = [] := by rw [hr]; rfl
    exact Or.inr ⟨hc', hdel⟩

theorem fcancelW_fstep {a a' : AFChan} {now : Bool} {r : Res} (h : a.cancelW now = some (a', r)) :
    FStep a.c a'.c [] ∨ a'.c = a.c := by
  obtain ⟨hg, hc, hcase⟩ := fcancelW_inv h
  rcases hcase with ⟨p, ht, -⟩ | ⟨ht, ha, -⟩
  · exact Or.inl (FStep.cancelW (fcancelW_now hg hc ht))
  · exact Or.inr (ha ▸ fstartW_none (ftakeW_none' ht))

theorem afstep_fstep {a a' : AFChan} {zs : List Val} (h : AFStep a a' zs) :
    FStep a.c a'.c zs ∨ (a'.c = a.c ∧ zs = []) := by
  cases h with
  | read h =>
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← (Prod.mk.inj he).1, ← (Prod.mk.inj he).2]
    exact Or.inl (FStep.read hq)
  | write h =>
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← (Prod.mk.inj he).1]
    exact Or.inl (FStep.write hq)
  | takeR h =>
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← (Prod.mk.inj he).1, ← (Prod.mk.inj (Prod.mk.inj he).2).2]
    exact Or.inl (FStep.takeR hq)
  | takeW h =>
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← (Prod.mk.inj he).1]
    exact Or.inl (FStep.takeW hq)
  | cancelR h => exact fcancelR_fstep h
  | cancelW h =>
    rcases fcancelW_fstep h with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', rfl⟩
  | dropR h =>
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← he]
    exact Or.inl (FStep.dropR hq)
  | dropW h =>
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← he]
    exact Or.inl (FStep.dropW hq)
  | give => exact Or.inr ⟨rfl, rfl⟩

theorem afsteps_fsteps {a a' : AFChan} {ys : List Val} (h : AFSteps a a' ys) :
    FSteps a.c a'.c ys := by
  induction h with
  | refl => exact FSteps.refl _
  | tail _ hs ih =>
    rcases afstep_fstep hs with h' | ⟨h₁, h₂⟩
    · exact FSteps.tail ih h'
    · rw [h₁, h₂, List.append_nil]
      exact ih

theorem afsteps_once {a : AFChan} {ys : List Val} (h : AFSteps {} a ys) :
    ys = [] ∨ ∃ v, ys = [v] ∧ a.c.sent = some v :=
  fsteps_once (afsteps_fsteps h)

end Silmaril.Proofs.Wasm.Component.Streams.ACancel
