module

public import Silmaril.Wasm.Component.Async.CabiSim2.Defs
public import Silmaril.Wasm.Component.Async.CabiSim.Thms

@[expose] public section

/-!
# The store model simulates `definitions.py` with a waitable set and values (unbounded)

PROVED (`agree_fragment2`): from a new stream whose two ends joined one waitable set, every
trace inside the fragment of `Silmaril.Wasm.Component.Async.CabiSim2` (the copies and event takes
of `CabiSim`, plus `waitable-set.poll` at any time and `waitable-set.wait` when an event is
there), of any length, with any chunk size `c > 0` and any values, gets the same answers from
the store model and from the transcription of `definitions.py`, including **which waitable**
`poll`/`wait` takes an event from (both take the reader's first: the store model by handle
order, the transcription by join order), and at the end **the reader has received the same
values in the same order** (`hostRecv` of the reader's end is the store model's `sent`).

The proof extends the simulation `CabiSim.Rel` with `Rel2` (the set and its members on both
sides, the values received) and reuses `CabiSim.sim_step` for the copies and takes;
`poll`/`wait` with an event are `CabiSim.sim_takeR`/`sim_takeW` on the first ready member.

Scope: one stream, its two ends in one set, at the level of the end state machine and
`WaitableSet.get_pending_event`. Handle tables (indices of the canon built-ins) and guest
memory are not part of it; handles are compared through the fixed numbering above. Drops,
unequal chunks, zero-length copies, untaken events before a copy and futures stay outside (the
differences of `CabiAgree`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.CabiSim2

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async.CabiSim
open Silmaril.Wasm.Component.Async (Pend Event)

/-! ## Frames -/

/-- The fields `poll` and the values read: what the reader received and the waitable sets. -/
def HW (st st1 : Cabi.Store Val) : Prop := st1.hostRecv = st.hostRecv ∧ st1.wsets = st.wsets

theorem HW.trans {a b c : Cabi.Store Val} (h1 : HW a b) (h2 : HW b c) : HW a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem notify_hw (st st1 : Cabi.Store Val) (e p : Nat) (h : st.notify e p = .ok st1) :
    HW st st1 := by
  cases he : st.ends e with
  | none => simp [Cabi.Store.notify, Cabi.Store.getEnd, Cabi.need, he, bind, Except.bind] at h
  | some x =>
    simp only [Cabi.Store.notify, Cabi.Store.getEnd, Cabi.need, he, Cabi.check, bind,
      Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩

theorem notifyBoth_hw (st st1 : Cabi.Store Val) (e b o ob : Nat)
    (h : st.notifyBoth e b o ob = .ok st1) : HW st st1 := by
  unfold Cabi.Store.notifyBoth at h
  obtain ⟨buf, -, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨obuf, -, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨s3, h3, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨s4, h4, h⟩ := Cabi.bind_ok.1 h
  have h34 := (notify_hw _ _ _ _ h3).trans (notify_hw _ _ _ _ h4)
  split at h
  · obtain ⟨y, -, h⟩ := Cabi.bind_ok.1 h
    injection h with h; subst h; exact h34
  · injection h with h; subst h; exact h34

set_option linter.unusedTactic false in
/-- Delivering an end's event changes only the end. -/
theorem deliverEnd_hw (st st1 : Cabi.Store Val) (e : Nat) (ev : Cabi.EventCode × Nat × Nat)
    (h : st.deliverEnd e = .ok (st1, ev)) : HW st st1 := by
  cases hx : st.ends e with
  | none => simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, hx, bind, Except.bind] at h
  | some z =>
    unfold Cabi.Store.deliverEnd at h
    simp only [Cabi.Store.getEnd, Cabi.need, hx, bind, Except.bind, pure, Except.pure] at h
    revert h
    cases z.pending with
    | none => intro h; cases h
    | some p =>
      simp only [Cabi.check]
      split <;> (try split) <;> (try split) <;> (try split) <;>
        intro h <;> cases h <;> exact ⟨rfl, rfl⟩

/-- A read of a host buffer. -/
theorem bufRead_host (st st1 : Cabi.Store Val) (b n : Nat) (vs : List Val) (bx : Cabi.Buf Val)
    (hb : st.bufs b = some bx) (hi : bx.inst = none) (h : st.bufRead b n = .ok (st1, vs)) :
    HW st st1 ∧ vs = (bx.src.drop bx.progress).take n := by
  simp only [Cabi.Store.bufRead, Cabi.Store.getBuf, Cabi.need, hb, hi, Cabi.check, bind,
    Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · injection h with h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- A write into a host buffer: the values are recorded for the end. -/
theorem bufWrite_host (st st1 : Cabi.Store Val) (e b : Nat) (vs : List Val) (bx : Cabi.Buf Val)
    (hb : st.bufs b = some bx) (hi : bx.inst = none) (h : st.bufWrite e b vs = .ok st1) :
    st1.hostRecv = Cabi.upd st.hostRecv e (st.hostRecv e ++ vs) ∧ st1.wsets = st.wsets := by
  simp only [Cabi.Store.bufWrite, Cabi.Store.getBuf, Cabi.need, hb, hi, Cabi.check, bind,
    Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · injection h with h; subst h; exact ⟨rfl, rfl⟩

/-- **The values a copy moves between host buffers** go to the reader's `hostRecv`. -/
theorem moveElems_host (st st1 : Cabi.Store Val) (isRead : Bool) (e b o ob n : Nat)
    (bx obx : Cabi.Buf Val) (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx)
    (hbo : b ≠ ob) (hi : bx.inst = none) (hoi : obx.inst = none)
    (h : st.moveElems isRead e b o ob n = .ok st1) :
    st1.wsets = st.wsets ∧ st1.hostRecv = Cabi.upd st.hostRecv (if isRead then e else o)
      (st.hostRecv (if isRead then e else o) ++
        (((if isRead then obx else bx).src.drop (if isRead then obx else bx).progress).take n)) := by
  cases isRead with
  | true =>
    obtain ⟨⟨s1, vs⟩, h1, h2⟩ : ∃ r, st.bufRead ob n = .ok r ∧ r.1.bufWrite e b r.2 = .ok st1 :=
      Cabi.bind_ok.1 h
    obtain ⟨hw1, hvs⟩ := bufRead_host _ _ _ _ _ _ hob hoi h1
    obtain ⟨-, -, hb1, -⟩ := Cabi.Store.bufRead_spec _ _ _ _ _ _ hob h1
    obtain ⟨h2r, h2w⟩ := bufWrite_host _ _ _ _ _ _ (by rw [hb1 _ hbo, hb]) hi h2
    refine ⟨h2w.trans hw1.2, ?_⟩
    simp only [ite_true]
    rw [h2r, hw1.1, ← hvs]
  | false =>
    obtain ⟨⟨s1, vs⟩, h1, h2⟩ : ∃ r, st.bufRead b n = .ok r ∧ r.1.bufWrite o ob r.2 = .ok st1 :=
      Cabi.bind_ok.1 h
    obtain ⟨hw1, hvs⟩ := bufRead_host _ _ _ _ _ _ hb hi h1
    obtain ⟨-, -, hb1, -⟩ := Cabi.Store.bufRead_spec _ _ _ _ _ _ hb h1
    obtain ⟨h2r, h2w⟩ := bufWrite_host _ _ _ _ _ _ (by rw [hb1 _ (Ne.symm hbo), hob]) hoi h2
    refine ⟨h2w.trans hw1.2, ?_⟩
    simp only [Bool.false_eq_true, ite_false]
    rw [h2r, hw1.1, ← hvs]

/-- **A copy meeting a parked host buffer of the same size**: the reader receives the
writer's `c` values; the waitable sets do not change. -/
theorem cCopy_transfer_recv (st st1 : Cabi.Store Val) (e o ob c a : Nat) (x y : Cabi.End)
    (bx obx : Cabi.Buf Val) (he : st.ends e = some x) (hxb : x.buffer = none)
    (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hob : st.bufs ob = some obx) (hlt : ob < st.nBufs)
    (htrap : (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) = false)
    (hbi : bx.inst = none) (hobi : obx.inst = none) (hbl : bx.length = c) (hbp : bx.progress = 0)
    (hobl : obx.length = c) (hobp : obx.progress = 0) (hc : 0 < c)
    (h : cCopy st e bx = .ok (st1, a)) :
    st1.wsets = st.wsets ∧ st1.hostRecv = Cabi.upd st.hostRecv (if x.kind.isReadable then e else o)
      (st.hostRecv (if x.kind.isReadable then e else o) ++
        ((if x.kind.isReadable then obx else bx).src.take c)) := by
  have hne : st.nBufs ≠ ob := Nat.ne_of_gt hlt
  have hSb : (st.newBuf bx).1.bufs st.nBufs = some bx := by simp [newBuf_eq, Cabi.upd]
  have hSob : (st.newBuf bx).1.bufs ob = some obx := by
    simp [newBuf_eq, Cabi.upd, Ne.symm hne, hob]
  have hrem : 0 < bx.remain ∧ 0 < obx.remain := by
    simp only [Cabi.Buf.remain, hbl, hbp, hobl, hobp]; omega
  have hmin : min bx.remain obx.remain = c := by
    simp only [Cabi.Buf.remain, hbl, hbp, hobl, hobp]; omega
  have hcp := Cabi.Store.copyEnd_meets_parked (st.newBuf bx).1 e st.nBufs o ob x y bx obx he hxb
    hxo hoe ho hyb hSb hSob htrap hrem.1 hrem.2
  unfold cCopy at h
  simp only [] at h
  obtain ⟨s2, h2, h⟩ := Cabi.bind_ok.1 h
  rw [show (st.newBuf bx).2 = st.nBufs from rfl, hcp] at h2
  obtain ⟨s1, h1, h1'⟩ := Cabi.bind_ok.1 h2
  have hS1b : ((st.newBuf bx).1.setEnd e (x.withState .copying)).bufs st.nBufs = some bx := hSb
  have hS1ob : ((st.newBuf bx).1.setEnd e (x.withState .copying)).bufs ob = some obx := hSob
  obtain ⟨hm1, hm2⟩ := moveElems_host _ _ _ _ _ _ _ _ _ _ hS1b hS1ob hne hbi hobi h1
  have hnb := notifyBoth_hw _ _ _ _ _ _ h1'
  -- the delivery (if any) only changes ends
  have hfin : HW s2 st1 := by
    split at h
    · obtain ⟨⟨s3, ev⟩, h3, h⟩ := Cabi.bind_ok.1 h
      injection h with h
      obtain ⟨rfl, -⟩ := Prod.mk.inj h
      exact deliverEnd_hw _ _ _ _ h3
    · injection h with h
      obtain ⟨rfl, -⟩ := Prod.mk.inj h
      exact ⟨rfl, rfl⟩
  refine ⟨hfin.2.trans (hnb.2.trans hm1), ?_⟩
  rw [hfin.1, hnb.1, hm2, hmin]
  have hr : ((if x.kind.isReadable then obx else bx).src.drop
      (if x.kind.isReadable then obx else bx).progress) =
      (if x.kind.isReadable then obx else bx).src := by
    cases x.kind.isReadable <;> simp [hbp, hobp]
  rw [hr]
  rfl

/-! ## The relation -/

/-- **The simulation relation**: `CabiSim.Rel` for the reader's handle `1`, the writer's `2`,
the channel `1` and the ends `0`, `1`; the set `3` of the store model with exactly the two
ends joined (handles below `4`); the transcription's set `0` with members `[end 0, end 1]`;
and the reader's received values equal to the store model's `sent`. -/
structure Rel2 (c : Nat) (m : Silmaril.Wasm.Component.Async.Store) (st : Cabi.Store Val) :
    Prop where
  rel : Rel 1 2 1 0 1 c m st
  recv : st.hostRecv 0 = (m.chans 1).sent
  next : m.next = 4
  tbl3 : m.tbl 3 = some .wset
  j0 : m.joined 0 = none
  j1 : m.joined 1 = some 3
  j2 : m.joined 2 = some 3
  j3 : m.joined 3 = none
  ws : st.wsets 0 = some { elems := [.end_ 0, .end_ 1] }

variable {c : Nat} {m : Silmaril.Wasm.Component.Async.Store} {st : Cabi.Store Val}

/-- The store model's first ready member of the set: the reader before the writer. -/
theorem firstReady_eq (hR : Rel2 c m st) :
    Silmaril.Wasm.Component.Async.firstReady m 3 (List.range m.next) =
      if (m.ev 1).isSome then some 1 else if (m.ev 2).isSome then some 2 else none := by
  rw [hR.next, show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [Silmaril.Wasm.Component.Async.firstReady, hR.j0, hR.j1, hR.j2, hR.j3]
  cases (m.ev 1).isSome <;> cases (m.ev 2).isSome <;> simp

/-- The reader's end has a pending event exactly when the store model's reader has one. -/
theorem hasPending_r (hR : Rel 1 2 1 0 1 c m st) : st.hasPending (.end_ 0) = (m.ev 1).isSome := by
  obtain ⟨x, hx, -, -, -, hs⟩ := hR.endR
  simp only [Cabi.Store.hasPending, hx]
  cases hev : m.ev 1 with
  | some e => simp [RShape, hev] at hs; simp [hs.2.2]
  | none =>
    cases hp : (m.chans 1).pend <;> simp [RShape, hev, hp] at hs <;> simp [hs]

/-- The writer's end likewise. -/
theorem hasPending_w (hR : Rel 1 2 1 0 1 c m st) : st.hasPending (.end_ 1) = (m.ev 2).isSome := by
  obtain ⟨x, hx, -, -, -, hs⟩ := hR.endW
  simp only [Cabi.Store.hasPending, hx]
  cases hev : m.ev 2 with
  | some e => simp [WShape, hev] at hs; simp [hs.2.2]
  | none =>
    cases hp : (m.chans 1).pend <;> simp [WShape, hev, hp] at hs <;> simp [hs]

/-- Taking an event keeps everything but the events. -/
theorem take_eq (h : Nat) (m' : Silmaril.Wasm.Component.Async.Store) (e : Event)
    (ht : Silmaril.Wasm.Component.Async.take m h = some (m', e)) :
    m' = { m with ev := Silmaril.Wasm.Component.Async.upd m.ev h none } := by
  unfold Silmaril.Wasm.Component.Async.take at ht
  cases hev : m.ev h with
  | none => simp [hev] at ht
  | some e' => simp [hev] at ht; exact ht.1.symm

/-- The extra parts of `Rel2` after taking an event in both models. -/
theorem rel2_take (hR : Rel2 c m st) (h : Nat) (m' : Silmaril.Wasm.Component.Async.Store)
    (st' : Cabi.Store Val) (hm : m' = { m with ev := Silmaril.Wasm.Component.Async.upd m.ev h none })
    (hw : HW st st') (hrel : Rel 1 2 1 0 1 c m' st') : Rel2 c m' st' := by
  subst hm
  exact { rel := hrel, recv := by rw [hw.1]; exact hR.recv, next := hR.next, tbl3 := hR.tbl3,
          j0 := hR.j0, j1 := hR.j1, j2 := hR.j2, j3 := hR.j3, ws := by rw [hw.2]; exact hR.ws }

/-- A take of the store model, as `take`. -/
theorem mStep_takeR_eq (m' : Silmaril.Wasm.Component.Async.Store) (a : Nat)
    (hm : mStep 1 2 c m .takeR = some (m', a)) :
    ∃ e, Silmaril.Wasm.Component.Async.take m 1 = some (m', e) ∧ e.payload = a := by
  simp only [mStep, Option.map_eq_some_iff] at hm
  obtain ⟨⟨m1, e1⟩, h1, h2⟩ := hm
  simp only [Prod.mk.injEq] at h2
  exact ⟨e1, h2.1 ▸ h1, h2.2⟩

theorem mStep_takeW_eq (m' : Silmaril.Wasm.Component.Async.Store) (a : Nat)
    (hm : mStep 1 2 c m .takeW = some (m', a)) :
    ∃ e, Silmaril.Wasm.Component.Async.take m 2 = some (m', e) ∧ e.payload = a := by
  simp only [mStep, Option.map_eq_some_iff] at hm
  obtain ⟨⟨m1, e1⟩, h1, h2⟩ := hm
  simp only [Prod.mk.injEq] at h2
  exact ⟨e1, h2.1 ▸ h1, h2.2⟩

/-- A take of the transcription, as `deliverEnd`. -/
theorem cStep_take_eq (o : FOp) (e : Nat) (he : o = .takeR ∧ e = 0 ∨ o = .takeW ∧ e = 1)
    (st' : Cabi.Store Val) (a : Nat) (hc : cStep 0 1 c st o = .ok (st', a)) :
    ∃ ev, st.deliverEnd e = .ok (st', ev) ∧ ev.2.2 = a := by
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [cStep, Except.map] at hc
    split at hc
    · cases hc
    · next p hp =>
      injection hc with hc
      simp only [Prod.mk.injEq] at hc
      exact ⟨p.2, by rw [hp, ← hc.1], hc.2⟩

/-- `poll` when the reader has an event. -/
theorem sim_poll_r (hR : Rel2 c m st) (e : Event) (hev1 : m.ev 1 = some e) :
    ∃ m' st' a, mPoll m = some (m', a) ∧ cPoll st = .ok (st', a) ∧ Rel2 c m' st' := by
  obtain ⟨m', st', hm, hc, hR'⟩ := sim_takeR hR.rel e hev1
  obtain ⟨e', ht, hpay⟩ := mStep_takeR_eq m' _ hm
  obtain ⟨ev, hd, hpay'⟩ := cStep_take_eq .takeR 0 (.inl ⟨rfl, rfl⟩) st' _ hc
  have hpr : st.hasPending (.end_ 0) = true := by rw [hasPending_r hR.rel, hev1]; rfl
  have hwp : st.wsHasPending 0 = true := by simp [Cabi.Store.wsHasPending, hR.ws, hpr]
  refine ⟨m', st', [1, 16 * c], ?_, ?_, ?_⟩
  · simp [mPoll, hR.tbl3, firstReady_eq hR, hev1, ht, hpay]
  · simp [cPoll, hwp, Cabi.Store.getWs, Cabi.need, hR.ws, List.find?, hpr, Cabi.Store.deliver, hd,
      handleOf, hpay', bind, Except.bind, pure, Except.pure]
  · exact rel2_take hR 1 m' st' (take_eq 1 m' e' ht) (deliverEnd_hw _ _ _ _ hd) hR'

/-- `poll` when only the writer has an event. -/
theorem sim_poll_w (hR : Rel2 c m st) (e : Event) (hev1 : m.ev 1 = none) (hev2 : m.ev 2 = some e) :
    ∃ m' st' a, mPoll m = some (m', a) ∧ cPoll st = .ok (st', a) ∧ Rel2 c m' st' := by
  obtain ⟨m', st', hm, hc, hR'⟩ := sim_takeW hR.rel e hev2
  obtain ⟨e', ht, hpay⟩ := mStep_takeW_eq m' _ hm
  obtain ⟨ev, hd, hpay'⟩ := cStep_take_eq .takeW 1 (.inr ⟨rfl, rfl⟩) st' _ hc
  have hpr : st.hasPending (.end_ 0) = false := by rw [hasPending_r hR.rel, hev1]; rfl
  have hpw : st.hasPending (.end_ 1) = true := by rw [hasPending_w hR.rel, hev2]; rfl
  have hwp : st.wsHasPending 0 = true := by simp [Cabi.Store.wsHasPending, hR.ws, hpw]
  refine ⟨m', st', [2, 16 * c], ?_, ?_, ?_⟩
  · simp [mPoll, hR.tbl3, firstReady_eq hR, hev1, hev2, ht, hpay]
  · simp [cPoll, hwp, Cabi.Store.getWs, Cabi.need, hR.ws, List.find?, hpr, hpw,
      Cabi.Store.deliver, hd, handleOf, hpay', bind, Except.bind, pure, Except.pure]
  · exact rel2_take hR 2 m' st' (take_eq 2 m' e' ht) (deliverEnd_hw _ _ _ _ hd) hR'

/-- **`poll` (and `wait`) in both models**: the same waitable, the same payload. -/
theorem sim_poll (hR : Rel2 c m st) :
    ∃ m' st' a, mPoll m = some (m', a) ∧ cPoll st = .ok (st', a) ∧ Rel2 c m' st' := by
  cases hev1 : m.ev 1 with
  | some e => exact sim_poll_r hR e hev1
  | none =>
    cases hev2 : m.ev 2 with
    | some e => exact sim_poll_w hR e hev1 hev2
    | none =>
      have hpr : st.hasPending (.end_ 0) = false := by rw [hasPending_r hR.rel, hev1]; rfl
      have hpw : st.hasPending (.end_ 1) = false := by rw [hasPending_w hR.rel, hev2]; rfl
      have hwp : st.wsHasPending 0 = false := by
        simp [Cabi.Store.wsHasPending, hR.ws, hpr, hpw]
      exact ⟨m, st, [0, 0], by simp [mPoll, hR.tbl3, firstReady_eq hR, hev1, hev2],
        by simp [cPoll, hwp, pure, Except.pure], hR⟩

/-- `stream.write`/`stream.read` of the store model keep the handles and the set. -/
theorem mStep_frame_copy (o : FOp) (ho : (∃ xs, o = .write xs) ∨ o = .read)
    (m' : Silmaril.Wasm.Component.Async.Store) (a : Nat) (hm : mStep 1 2 c m o = some (m', a)) :
    m'.next = m.next ∧ m'.tbl = m.tbl ∧ m'.joined = m.joined := by
  rcases ho with ⟨xs, rfl⟩ | rfl
  all_goals
    simp only [mStep, Silmaril.Wasm.Component.Async.streamWrite,
      Silmaril.Wasm.Component.Async.streamRead, Option.map_eq_some_iff] at hm
    obtain ⟨⟨m1, r1⟩, h1, h2⟩ := hm
    obtain ⟨rfl, -⟩ := Prod.mk.inj h2
    revert h1
    split
    · split <;> intro h1 <;> (try split at h1) <;> cases h1 <;> exact ⟨rfl, rfl, rfl⟩
    · intro h1; cases h1

/-- The store model's copies and takes keep the handles, the set and its members. -/
theorem mStep_frame (o : FOp) (m' : Silmaril.Wasm.Component.Async.Store) (a : Nat)
    (hm : mStep 1 2 c m o = some (m', a)) :
    m'.next = m.next ∧ m'.tbl = m.tbl ∧ m'.joined = m.joined := by
  cases o with
  | write xs => exact mStep_frame_copy _ (.inl ⟨xs, rfl⟩) m' a hm
  | read => exact mStep_frame_copy _ (.inr rfl) m' a hm
  | takeR =>
    obtain ⟨e, ht, -⟩ := mStep_takeR_eq m' a hm
    rw [take_eq 1 m' e ht]; exact ⟨rfl, rfl, rfl⟩
  | takeW =>
    obtain ⟨e, ht, -⟩ := mStep_takeW_eq m' a hm
    rw [take_eq 2 m' e ht]; exact ⟨rfl, rfl, rfl⟩

/-- The values after a write that parks: nothing moves. -/
theorem op_recv_write_idle (hR : Rel2 c m st) (xs : List Val) (hev : m.ev 2 = none)
    (hp : (m.chans 1).pend = .idle) (m' : Silmaril.Wasm.Component.Async.Store) (st' : Cabi.Store Val)
    (a : Nat) (hm : mStep 1 2 c m (.write xs) = some (m', a))
    (hc : cStep 0 1 c st (.write xs) = .ok (st', a)) :
    st'.hostRecv 0 = (m'.chans 1).sent ∧ st'.wsets = st.wsets := by
  obtain ⟨xr, hxr, -, -, -, hRs⟩ := hR.rel.endR
  obtain ⟨xw, hxw, -, hxwo, -, hWs⟩ := hR.rel.endW
  have hW : xw.state = .idle ∧ xw.buffer = none ∧ xw.pending = none := by
    simpa [WShape, hev, hp] using hWs
  have hRb : xr.buffer = none := by cases hevr : m.ev 1 <;> simp_all [RShape]
  have hcp : cStep 0 1 c st (.write xs) = .ok (_, Cabi.BLOCKED) :=
    cCopy_park st 1 0 xw xr { inst := none, length := xs.length, src := xs } hxw hW.2.1 hW.2.2
      hxwo (by decide) hxr hRb
  have hm' : mStep 1 2 c m (.write xs) =
      some (m.setChan 1 { m.chans 1 with pend := .write 2 xs }, Cabi.BLOCKED) := by
    simp [mStep, Silmaril.Wasm.Component.Async.streamWrite, hR.rel.tblW, hp, hR.rel.noDropR, resNat,
      Silmaril.Wasm.Component.Async.blocked, Cabi.BLOCKED]
  rw [(Prod.mk.inj (Except.ok.inj (hc.symm.trans hcp))).1,
    (Prod.mk.inj (Option.some.inj (hm.symm.trans hm'))).1]
  refine ⟨?_, rfl⟩
  simp only [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd, ite_true]
  exact hR.recv

/-- The values after a read that parks: nothing moves. -/
theorem op_recv_read_idle (hR : Rel2 c m st) (hev : m.ev 1 = none)
    (hp : (m.chans 1).pend = .idle) (m' : Silmaril.Wasm.Component.Async.Store) (st' : Cabi.Store Val)
    (a : Nat) (hm : mStep 1 2 c m .read = some (m', a))
    (hc : cStep 0 1 c st .read = .ok (st', a)) :
    st'.hostRecv 0 = (m'.chans 1).sent ∧ st'.wsets = st.wsets := by
  obtain ⟨xr, hxr, -, hxro, -, hRs⟩ := hR.rel.endR
  obtain ⟨xw, hxw, -, -, -, hWs⟩ := hR.rel.endW
  have hRx : xr.state = .idle ∧ xr.buffer = none ∧ xr.pending = none := by
    simpa [RShape, hev, hp] using hRs
  have hWb : xw.buffer = none := by cases hevw : m.ev 2 <;> simp_all [WShape]
  have hcp : cStep 0 1 c st .read = .ok (_, Cabi.BLOCKED) :=
    cCopy_park st 0 1 xr xw { inst := none, length := c } hxr hRx.2.1 hRx.2.2 hxro (by decide)
      hxw hWb
  have hm' : mStep 1 2 c m .read =
      some (m.setChan 1 { m.chans 1 with pend := .read 1 c }, Cabi.BLOCKED) := by
    simp [mStep, Silmaril.Wasm.Component.Async.streamRead, hR.rel.tblR, hp, hR.rel.noDropW, resNat,
      Silmaril.Wasm.Component.Async.blocked, Cabi.BLOCKED]
  rw [(Prod.mk.inj (Except.ok.inj (hc.symm.trans hcp))).1,
    (Prod.mk.inj (Option.some.inj (hm.symm.trans hm'))).1]
  refine ⟨?_, rfl⟩
  simp only [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd, ite_true]
  exact hR.recv

/-- The values after a write meeting the parked read: the reader receives the `c` values. -/
theorem op_recv_write_read (hR : Rel2 c m st) (xs : List Val) (hlen : xs.length = c)
    (hev : m.ev 2 = none) (hp : (m.chans 1).pend = .read 1 c)
    (m' : Silmaril.Wasm.Component.Async.Store) (st' : Cabi.Store Val) (a : Nat)
    (hm : mStep 1 2 c m (.write xs) = some (m', a)) (hc : cStep 0 1 c st (.write xs) = .ok (st', a)) :
    st'.hostRecv 0 = (m'.chans 1).sent ∧ st'.wsets = st.wsets := by
  obtain ⟨xr, hxr, -, -, -, hRs⟩ := hR.rel.endR
  obtain ⟨xw, hxw, hxwk, hxwo, hxwow, hWs⟩ := hR.rel.endW
  obtain ⟨-, -, br, brx, hrb, hbr, hbrlt, hbri, hbrl, hbrp⟩ :
      xr.state = .copying ∧ xr.pending = none ∧ ∃ b bx, xr.buffer = some b ∧
        st.bufs b = some bx ∧ b < st.nBufs ∧ bx.inst = none ∧ bx.length = c ∧ bx.progress = 0 := by
    simpa [RShape, (hR.rel.pendRead 1 c hp).2.2, hp] using hRs
  have hW : xw.state = .idle ∧ xw.buffer = none ∧ xw.pending = none := by
    simpa [WShape, hev, hp] using hWs
  obtain ⟨hws, hrecv⟩ := cCopy_transfer_recv st st' 1 0 br c a xw xr
    { inst := none, length := xs.length, src := xs } brx hxw hW.2.1 hxwo (by decide) hxr hrb
    hbr hbrlt (by simp [hxwow]) rfl hbri hlen rfl hbrl hbrp hR.rel.pos hc
  have hm' : mStep 1 2 c m (.write xs) = some ((m.setChan 1 ⟨.idle, (m.chans 1).rDropped,
      (m.chans 1).wDropped, (m.chans 1).done, (m.chans 1).sent ++ xs.take c⟩).post 1
        ⟨.streamRead, 1, Silmaril.Wasm.Component.Async.packCopy .completed c, xs.take c⟩, 16 * c) := by
    simp [mStep, Silmaril.Wasm.Component.Async.streamWrite, hR.rel.tblW, hp, resNat, hlen,
      Silmaril.Wasm.Component.Async.packCopy, Silmaril.Wasm.Component.Async.CopyResult.toNat]
  rw [(Prod.mk.inj (Option.some.inj (hm.symm.trans hm'))).1, hrecv]
  exact ⟨by simp [hxwk, Cabi.EndKind.isReadable, Cabi.upd, hR.recv,
    Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
    Silmaril.Wasm.Component.Async.upd], hws⟩

/-- The values after a read meeting the parked write: the reader receives the `c` values. -/
theorem op_recv_read_write (hR : Rel2 c m st) (xs : List Val) (hev : m.ev 1 = none)
    (hp : (m.chans 1).pend = .write 2 xs) (m' : Silmaril.Wasm.Component.Async.Store)
    (st' : Cabi.Store Val) (a : Nat) (hm : mStep 1 2 c m .read = some (m', a))
    (hc : cStep 0 1 c st .read = .ok (st', a)) :
    st'.hostRecv 0 = (m'.chans 1).sent ∧ st'.wsets = st.wsets := by
  obtain ⟨-, hlen, hevw⟩ := hR.rel.pendWrite 2 xs hp
  obtain ⟨xr, hxr, hxrk, hxro, hxrow, hRs⟩ := hR.rel.endR
  obtain ⟨xw, hxw, -, -, -, hWs⟩ := hR.rel.endW
  obtain ⟨-, -, bw, bwx, hwb, hbw, hbwlt, hbwi, hbwl, hbwp, hbws⟩ :
      xw.state = .copying ∧ xw.pending = none ∧ ∃ b bx, xw.buffer = some b ∧
        st.bufs b = some bx ∧ b < st.nBufs ∧ bx.inst = none ∧ bx.length = c ∧
          bx.progress = 0 ∧ bx.src = xs := by
    simpa [WShape, hevw, hp] using hWs
  have hRx : xr.state = .idle ∧ xr.buffer = none ∧ xr.pending = none := by
    simpa [RShape, hev, hp] using hRs
  obtain ⟨hws, hrecv⟩ := cCopy_transfer_recv st st' 0 1 bw c a xr xw
    { inst := none, length := c } bwx hxr hRx.2.1 hxro (by decide) hxw hwb hbw hbwlt
    (by simp [hxrow]) rfl hbwi rfl rfl hbwl hbwp hR.rel.pos hc
  have hm' : mStep 1 2 c m .read = some ((m.setChan 1 ⟨.idle, (m.chans 1).rDropped,
      (m.chans 1).wDropped, (m.chans 1).done, (m.chans 1).sent ++ xs.take c⟩).post 2
        ⟨.streamWrite, 2, Silmaril.Wasm.Component.Async.packCopy .completed c, []⟩, 16 * c) := by
    simp [mStep, Silmaril.Wasm.Component.Async.streamRead, hR.rel.tblR, hp, resNat, hlen,
      Silmaril.Wasm.Component.Async.packCopy, Silmaril.Wasm.Component.Async.CopyResult.toNat]
  rw [(Prod.mk.inj (Option.some.inj (hm.symm.trans hm'))).1, hrecv]
  exact ⟨by simp [hxrk, Cabi.EndKind.isReadable, Cabi.upd, hR.recv, hbws,
    Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
    Silmaril.Wasm.Component.Async.upd], hws⟩

/-- The values after taking an event: nothing moves. -/
theorem op_recv_take (hR : Rel2 c m st) (o : FOp) (e : Nat) (h : Nat)
    (he : o = .takeR ∧ e = 0 ∧ h = 1 ∨ o = .takeW ∧ e = 1 ∧ h = 2)
    (m' : Silmaril.Wasm.Component.Async.Store) (st' : Cabi.Store Val) (a : Nat)
    (hm : mStep 1 2 c m o = some (m', a)) (hc : cStep 0 1 c st o = .ok (st', a)) :
    st'.hostRecv 0 = (m'.chans 1).sent ∧ st'.wsets = st.wsets := by
  obtain ⟨ev, hd, -⟩ := cStep_take_eq o e (he.imp (fun h' => ⟨h'.1, h'.2.1⟩)
    (fun h' => ⟨h'.1, h'.2.1⟩)) st' a hc
  have hw : HW st st' := deliverEnd_hw _ _ _ _ hd
  have hmm : m'.chans = m.chans := by
    rcases he with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · obtain ⟨e1, ht, -⟩ := mStep_takeR_eq m' a hm
      rw [take_eq 1 m' e1 ht]
    · obtain ⟨e1, ht, -⟩ := mStep_takeW_eq m' a hm
      rw [take_eq 2 m' e1 ht]
  rw [hw.1, hmm]
  exact ⟨hR.recv, hw.2⟩

/-- **The values and the set after a copy or take**: the reader received what the store
model sent, and the transcription's set is unchanged. -/
theorem op_recv (hR : Rel2 c m st) (o : FOp) (hA : Allowed 1 2 c 1 m o)
    (m' : Silmaril.Wasm.Component.Async.Store) (st' : Cabi.Store Val) (a : Nat)
    (hm : mStep 1 2 c m o = some (m', a)) (hc : cStep 0 1 c st o = .ok (st', a)) :
    st'.hostRecv 0 = (m'.chans 1).sent ∧ st'.wsets = st.wsets := by
  cases o with
  | write xs =>
    obtain ⟨hlen, hev, hnw⟩ := hA
    cases hp : (m.chans 1).pend with
    | write h ys => exact absurd hp (hnw h ys)
    | idle => exact op_recv_write_idle hR xs hev hp m' st' a hm hc
    | read h n =>
      obtain ⟨hhr, hnc, -⟩ := hR.rel.pendRead h n hp
      exact op_recv_write_read hR xs hlen hev (by rw [hp, hhr, hnc]) m' st' a hm hc
  | read =>
    obtain ⟨hev, hnr⟩ := hA
    cases hp : (m.chans 1).pend with
    | read h n => exact absurd hp (hnr h n)
    | idle => exact op_recv_read_idle hR hev hp m' st' a hm hc
    | write h xs =>
      obtain ⟨hhw, -, -⟩ := hR.rel.pendWrite h xs hp
      exact op_recv_read_write hR xs hev (by rw [hp, hhw]) m' st' a hm hc
  | takeR => exact op_recv_take hR .takeR 0 1 (.inl ⟨rfl, rfl, rfl⟩) m' st' a hm hc
  | takeW => exact op_recv_take hR .takeW 1 2 (.inr ⟨rfl, rfl, rfl⟩) m' st' a hm hc

/-- **One step of the simulation**, with the set and the values. -/
theorem sim_step2 (hR : Rel2 c m st) (o : POp) (hA : Allowed2 c m o) :
    ∃ m' st' a, mStep2 c m o = some (m', a) ∧ cStep2 c st o = .ok (st', a) ∧ Rel2 c m' st' := by
  cases o with
  | op o =>
    obtain ⟨m', st', a, hm, hc, hR'⟩ := sim_step hR.rel o hA
    obtain ⟨hn, ht, hj⟩ := mStep_frame o m' a hm
    obtain ⟨hrecv, hws⟩ := op_recv hR o hA m' st' a hm hc
    refine ⟨m', st', [a], by simp [mStep2, hm], by simp [cStep2, hc, Except.map], ?_⟩
    exact { rel := hR', recv := hrecv, next := hn.trans hR.next, tbl3 := ht ▸ hR.tbl3,
            j0 := hj ▸ hR.j0, j1 := hj ▸ hR.j1, j2 := hj ▸ hR.j2, j3 := hj ▸ hR.j3,
            ws := hws ▸ hR.ws }
  | poll => exact sim_poll hR
  | wait => exact sim_poll hR

/-- **The simulation**, with the final stores. -/
theorem sim_run2 (ops : List POp) (as : List (List Nat)) (m'' : Silmaril.Wasm.Component.Async.Store)
    (hrun : MRun2 c m ops as m'') :
    ∀ st, Rel2 c m st → ∃ st'', cRun2 c st ops = .ok (st'', as) ∧ Rel2 c m'' st'' := by
  induction hrun with
  | nil => intro st hR; exact ⟨st, rfl, hR⟩
  | cons hA hm _ ih =>
    intro st hR
    obtain ⟨m1, st1, a1, hm1, hc1, hR1⟩ := sim_step2 hR _ hA
    rw [hm] at hm1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm1)
    obtain ⟨st'', hc'', hR''⟩ := ih st1 hR1
    exact ⟨st'', by simp [cRun2, hc1, hc'', bind, Except.bind, pure, Except.pure], hR''⟩

/-- The initial stores are related, for every chunk size. -/
theorem rel2_init (t : Cabi.Ty) (c : Nat) (hc : 0 < c) : Rel2 c mInit2 (cInit2 t) where
  rel := {
    pos := hc
    tblR := rfl
    tblW := rfl
    hrw := by decide
    noDropR := rfl
    noDropW := rfl
    pendRead := fun _ _ h => nomatch h
    pendWrite := fun _ _ h => nomatch h
    evR := fun _ h => nomatch h
    evW := fun _ h => nomatch h
    hne := by decide
    endR := ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩
    endW := ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩ }
  recv := rfl
  next := rfl
  tbl3 := rfl
  j0 := rfl
  j1 := rfl
  j2 := rfl
  j3 := rfl
  ws := rfl

/-- **Agreement with a waitable set and values, unbounded**: from a new stream whose ends joined
one set, every trace inside the fragment (copies of `c > 0` values, event takes, `poll` at any
time, `wait` with an event there; any length, any values) gets the same answers from the store
model and from the transcription, `poll`/`wait` taking from the same waitable, and the reader
has received exactly the values the store model sent, in order. -/
theorem agree_fragment2 (t : Cabi.Ty) (c : Nat) (hc : 0 < c) (ops : List POp)
    (as : List (List Nat)) (m'' : Silmaril.Wasm.Component.Async.Store)
    (hrun : MRun2 c mInit2 ops as m'') :
    ∃ st'', cRun2 c (cInit2 t) ops = .ok (st'', as) ∧ st''.hostRecv 0 = (m''.chans 1).sent := by
  obtain ⟨st'', h1, h2⟩ := sim_run2 ops as m'' hrun _ (rel2_init t c hc)
  exact ⟨st'', h1, h2.recv⟩

/-- `mPoll` is the store model's `waitable-set.poll 3` (store and payload). -/
theorem mPoll_step (m' : Silmaril.Wasm.Component.Async.Store) (h p : Nat)
    (hp : mPoll m = some (m', [h, p])) (hh : h ≠ 0) :
    ∃ e, Silmaril.Wasm.Component.Async.step m (.poll 3) = some (m', .event e) ∧ e.payload = p := by
  unfold mPoll at hp
  split at hp
  · next h3 =>
    split at hp
    · next h' hfr =>
      simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨m1, e1⟩, ht, he⟩ := hp
      simp only [Prod.mk.injEq, List.cons.injEq, and_true] at he
      obtain ⟨rfl, -, rfl⟩ := he
      exact ⟨e1, by simp [Silmaril.Wasm.Component.Async.step, h3, hfr, ht], rfl⟩
    · simp at hp; exact absurd hp.2.1.symm hh
  · cases hp

end Silmaril.Wasm.Component.Async.CabiSim2
