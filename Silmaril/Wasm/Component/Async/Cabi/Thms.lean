module

public import Silmaril.Wasm.Component.Async.Cabi.Defs

@[expose] public section

/-!
# The transcribed async Canonical ABI: general laws

PROVED, for every store (standard axioms), the general forms of the behaviours on which
`Silmaril.Wasm.Component.Async.CabiAgree` found the store model of
`Silmaril.Wasm.Component.Async` to differ from `definitions.py`:

* `Table.add_reuses`: `Table.add` reuses the last freed index (difference 8);
* `opCopy_traps_of_not_idle`: a `stream.read`/`stream.write`/`future.*` copy on an end that is
  not `IDLE` traps (differences 4 and 5: an end whose completion was not delivered, or that
  is `DONE` after `DROPPED`);
* `deliverEnd_dropped`: the event of a stream end whose peer is gone reports `DROPPED`
  with the progress recorded at `notify` (difference 3: the result is computed at delivery);
* `dropEnd_notifies_idle`: dropping an end posts a progress-`0` event for a peer that is not
  `DONE` and has no pending event, whatever its state (difference 1), using the frame lemma
  `join_ends_ne`.

Difference 2 (a partly used parked buffer stays parked) is proved in general in
`Silmaril.Wasm.Component.Async.CabiCopy` (`Store.copyEnd_partial_keeps_parked`); concrete traces
are `CabiAgree.differ_partialWriteParked`, `differ_partialReadParked`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.Cabi

/-- **Index reuse**: `add` takes the last freed index. -/
theorem Table.add_reuses {ε : Type} (t : Table ε) (e : ε) (i : Nat) (fs : List Nat)
    (h : t.free = i :: fs) :
    t.add e = .ok ({ arr := t.arr.set i (some e), free := fs }, i) := by
  simp [Table.add, h, pure, Except.pure]

/-- Decomposing a successful bind. -/
theorem bind_ok {β γ : Type} {m : M β} {f : β → M γ} {c : γ} :
    (m >>= f) = .ok c ↔ ∃ b, m = .ok b ∧ f b = .ok c := by
  cases m <;> simp [bind, Except.bind]

namespace Store

variable {α : Type}

/-- **A copy on an end that is not idle traps.** -/
theorem opCopy_traps_of_not_idle [Inhabited α] (st : Store α) (kind : EndKind) (t : Ty) (async : Bool)
    (i ptr len th : Nat) (thr : Thread) (x : Task) (ins : Inst α) (e : Nat) (y : End)
    (hctx : st.ctx = .ok (th, thr, x, ins)) (hml : ins.mayLeave = true)
    (hi : ins.handles.get i = .ok (.end_ e)) (he : st.ends e = some y) (hk : y.kind = kind)
    (ht : y.t = t) (hs : y.state ≠ .idle) :
    ∃ why, st.opCopy kind t async i ptr len = .error (.trap why) := by
  refine ⟨"copy: not idle", ?_⟩
  simp [opCopy, hctx, hml, hi, getEnd, need, he, hk, ht, hs, trapIf, bind, Except.bind, pure,
    Except.pure]

/-- **Results are computed at delivery**: a stream end with a pending event whose peer is gone
delivers `DROPPED` with the progress of its last `notify`. -/
theorem deliverEnd_dropped (st : Store α) (e p : Nat) (x : End) (he : st.ends e = some x)
    (hs : x.kind.isStream = true) (hp : x.pending = some p) (ho : x.other = none)
    (hd : x.state ≠ .done) :
    ∃ st', st.deliverEnd e =
      .ok (st', (x.kind.eventCode, x.index.getD 0, CopyResult.dropped.toNat + 16 * p)) := by
  refine ⟨st.setEnd e { x with pending := none, buffer := none, state := .done }, ?_⟩
  simp [deliverEnd, getEnd, need, he, hs, hp, ho, check, hd, bind, Except.bind, pure, Except.pure]

/-- Leaving a set does not touch ends. -/
theorem leaveSet_ends (st st' : Store α) (w : WRef) (h : st.leaveSet w = .ok st') :
    st'.ends = st.ends := by
  unfold leaveSet at h
  revert h
  cases st.wsetOf w with
  | none => intro h; injection h with h; subst h; rfl
  | some old =>
    intro h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    injection h with h; subst h; rfl

/-- Entering a set does not touch ends. -/
theorem enterSet_ends (st st' : Store α) (w : WRef) (v : Option Nat)
    (h : st.enterSet w v = .ok st') : st'.ends = st.ends := by
  cases v with
  | none => injection h with h; subst h; rfl
  | some n =>
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    injection h with h; subst h; rfl

/-- Setting the set field of the end `e` leaves the other ends alone. -/
theorem setWsetField_ends_ne (st st' : Store α) (e o : Nat) (v : Option Nat)
    (h : st.setWsetField (.end_ e) v = .ok st') (hne : o ≠ e) : st'.ends o = st.ends o := by
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  injection h with h; subst h
  simp [setEnd, upd, hne]

/-- Joining a waitable set leaves the other ends alone. -/
theorem join_ends_ne (st st' : Store α) (e o : Nat) (v : Option Nat)
    (h : st.join (.end_ e) v = .ok st') (hne : o ≠ e) : st'.ends o = st.ends o := by
  unfold join at h
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  obtain ⟨s1, h1, h⟩ := bind_ok.1 h
  obtain ⟨s2, h2, h⟩ := bind_ok.1 h
  rw [enterSet_ends _ _ _ _ h, setWsetField_ends_ne _ _ _ _ _ h2 hne, leaveSet_ends _ _ _ h1]

/-- Notifying an idle peer records progress `0` for it. -/
theorem notifyIfIdle_pending (st st' : Store α) (o : Nat) (y z : End)
    (ho : st.ends o = some z) (hd : y.state ≠ .done) (hp : y.pending = none)
    (h : st.notifyIfIdle o y = .ok st') : st'.ends o = some { z with pending := some 0 } := by
  have hc : (y.state != EndState.done && y.pending.isNone) = true := by simp [hd, hp]
  simp only [notifyIfIdle, hc, ite_true, notify] at h
  obtain ⟨z', hz', h⟩ := bind_ok.1 h
  have hzz : z' = z := by
    simp only [getEnd, need, ho] at hz'
    injection hz' with hz'; exact hz'.symm
  subst hzz
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  injection h with h; subst h
  simp [setEnd, upd]

/-- Reading an end that is there. -/
theorem getEnd_of (st : Store α) (e : Nat) (x : End) (he : st.ends e = some x) :
    st.getEnd e = .ok x := by
  simp [getEnd, need, he, pure, Except.pure]

/-- Unlinking the peer `o` of `e` notifies it when it is idle. -/
theorem unlinkPeer_pending (st s1 : Store α) (e o : Nat) (x y : End)
    (ho : st.ends o = some y) (hxo : x.other = some o) (hne : o ≠ e) (hd : y.state ≠ .done)
    (hp : y.pending = none) (h : st.unlinkPeer e x = .ok s1) :
    s1.ends o = some { y with other := none, pending := some 0 } := by
  simp only [unlinkPeer, hxo, getEnd_of _ _ _ ho] at h
  obtain ⟨y', hy', h⟩ := bind_ok.1 h
  have hyy : y = y' := by injection hy'
  subst hyy
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  obtain ⟨s2, h2, h⟩ := bind_ok.1 h
  have hs2 : s2.ends o = some { y with other := none, pending := some 0 } :=
    notifyIfIdle_pending _ _ _ _ { y with other := none } (by simp [setEnd, upd]) hd hp h2
  injection h with h; subst h
  simp [setEnd, upd, hne, hs2]

/-- **Dropping notifies an idle peer**: after `dropEnd e`, a peer `o` that was not `DONE` and
had no pending event has the pending progress `0`. -/
theorem dropEnd_notifies_idle (st st' : Store α) (e o : Nat) (x y : End)
    (he : st.ends e = some x) (ho : st.ends o = some y) (hxo : x.other = some o)
    (hne : o ≠ e) (hd : y.state ≠ .done) (hp : y.pending = none)
    (h : st.dropEnd e = .ok st') :
    ∃ y', st'.ends o = some y' ∧ y'.pending = some 0 := by
  unfold dropEnd at h
  rw [getEnd_of _ _ _ he] at h
  obtain ⟨x', hx', h⟩ := bind_ok.1 h
  have hxx : x = x' := by injection hx'
  subst hxx
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  obtain ⟨s1, h1, h⟩ := bind_ok.1 h
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  exact ⟨_, (join_ends_ne _ _ _ _ _ h hne).trans (unlinkPeer_pending _ _ _ _ _ _ ho hxo hne hd hp h1),
    rfl⟩

end Store

end Silmaril.Wasm.Component.Async.Cabi
