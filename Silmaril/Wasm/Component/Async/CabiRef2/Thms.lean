module

public import Silmaril.Wasm.Component.Async.CabiRef2.Defs
public import Silmaril.Wasm.Component.Async.CabiRef.Thms
import Silmaril.Raw.Wasm.Component.Reference

@[expose] public section

/-!
# The transcription simulates silmaril's whole end state machine

PROVED, for stores related by `CabiRef.EndsRel` (every end has the same `View`):

* `copyEnd_sim`: **every successful `End.copy`** (`Cabi.Store.copyEnd`) is silmaril's
  `copyCore`, and the stores stay related. New cases: a peer that was dropped (case 1,
  `copyEnd_sim_dropped`), a zero-length peer or a read meeting a zero-length write (case 4,
  `copyEnd_sim_zero_peer`), a zero-length copy that completes at once (case 5,
  `copyEnd_sim_zero_self`); cases 2 and 3 are `CabiRef.copyEnd_sim_park` and
  `CabiRef.copyEnd_sim_transfer`. Side conditions: the end is not linked to itself, no end parks
  the new buffer, no two ends park one buffer, and the buffer that is read holds its values.
* `cancelEnd_sim`: `End.cancel` with Python's coin `coin` is silmaril's `cancel` with
  `notifyNow = det || coin` (the deterministic profile notifies at once).
* `dropEnd_sim`: `End.drop` is silmaril's `dropEnd` (the peer unlinked and, if it is not
  `DONE` and has no pending event, notified with progress `0`).
* `deliverEnd_sim_future`: delivering a future end's event (`future_event`: `COMPLETED`,
  `DROPPED` or `CANCELLED`) is silmaril's `takeEvent`, with the same code, index and payload.
* `forwardEnd_sim_drop`: `End.forward` when the source is linked to the destination or a peer
  is gone: both drop both ends.
* `forwardEnd_sim_splice`: `End.forward` splicing the peers when not both of them have a parked
  buffer: related **except at the two forwarded ends**, which silmaril unlinks and the
  transcription leaves pointing at the old peers (`forward_links_differ`, refuted with a
  concrete pair of stores: the full relation is not kept).

With `Silmaril.Wasm.Component.Async.CabiRef` this covers every step of the stream/future end state
machine except the splice of `End.forward` when both peers have a parked buffer (the re-issued
copy; it is `copyCore` on the spliced stores, but the relation there holds only up to the two
retired ends, so `copyEnd_sim` does not apply as stated). Above the end state machine (tasks,
threads, waitable sets, canon built-ins) nothing is related here.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.CabiRef

open Silmaril.Wasm.Component.Runtime

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {α : Type}

/-! ## Frames -/

/-- Updating two ends keeps the relation at the other ends. -/
theorem rel_frame2 (st st1 : Cabi.Store α) (s s1 : CStore E) (e o : Nat) (hR : EndsRel st s)
    (hb : st1.bufs = st.bufs) (hst : ∀ c, c ≠ e → c ≠ o → st1.ends c = st.ends c)
    (hs : ∀ c : EndId, c ≠ ⟨e⟩ → c ≠ ⟨o⟩ → s1.end? c = s.end? c)
    (he : (s1.end? ⟨e⟩).map viewS = (st1.ends e).bind (viewC st1 e))
    (ho : (s1.end? ⟨o⟩).map viewS = (st1.ends o).bind (viewC st1 o)) : EndsRel st1 s1 := by
  intro c
  by_cases hce : c = e
  · rw [hce]; exact he
  by_cases hco : c = o
  · rw [hco]; exact ho
  have hc' : (⟨c⟩ : EndId) ≠ ⟨e⟩ := fun h' => hce (EndId.mk.inj h')
  have hco' : (⟨c⟩ : EndId) ≠ ⟨o⟩ := fun h' => hco (EndId.mk.inj h')
  rw [hs _ hc' hco', hst c hce hco, hR c]
  cases st.ends c with
  | none => rfl
  | some z => exact (viewC_congr st st1 c z (fun bz _ => by rw [hb])).symm

/-- The relation at one end, after both machines update it the same way on views. -/
theorem rel_at_update (st st1 : Cabi.Store α) (s : CStore E) (e : Nat) (x x' : Cabi.End)
    (xs xs' : End E) (F : View E → View E) (hR : EndsRel st s) (hxs : s.end? ⟨e⟩ = some xs)
    (he : st.ends e = some x) (hS : viewS xs' = F (viewS xs))
    (hC : viewC st1 e x' = (viewC st e x).map F) : some (viewS xs') = viewC st1 e x' := by
  have h := hR e
  rw [hxs, he] at h
  simp only [Option.map_some, Option.bind_some] at h
  rw [hS, hC, ← h]
  rfl

/-- `viewC` after a change of state. -/
theorem viewC_withState (st : Cabi.Store α) (e : Nat) (x : Cabi.End) (ns : Cabi.EndState) :
    (viewC st e (x.withState ns) : Option (View E)) =
      (viewC st e x).map fun v => { v with state := stateR ns } := by
  unfold viewC
  cases hb : x.buffer with
  | none => simp [Cabi.End.withState, hb]
  | some b => cases hbb : st.bufs b <;> simp [Cabi.End.withState, hb, hbb]

/-- `viewC` after `notify(p)`. -/
theorem viewC_withPending (st : Cabi.Store α) (e : Nat) (x : Cabi.End) (p : Nat) :
    (viewC st e (x.withPending p) : Option (View E)) =
      (viewC st e x).map fun v => { v with pending := pendR x.kind e (some p) } := by
  unfold viewC
  cases hb : x.buffer with
  | none => simp [Cabi.End.withPending, hb]
  | some b => cases hbb : st.bufs b <;> simp [Cabi.End.withPending, hb, hbb]

/-- `viewC` after unlinking the peer (and leaving the waitable set). -/
theorem viewC_unlink (st : Cabi.Store α) (e : Nat) (x : Cabi.End) (w : Option Nat) :
    (viewC st e { x with other := none, wset := w } : Option (View E)) =
      (viewC st e x).map fun v => { v with other := none } := by
  unfold viewC
  cases hb : x.buffer with
  | none => simp
  | some b => cases hbb : st.bufs b <;> simp [hbb]

/-- `viewC` of an end with the same parked buffer: every other field is read off the end. -/
theorem viewC_eq (st : Cabi.Store α) (e : Nat) (x x' : Cabi.End) (hb : x'.buffer = x.buffer) :
    (viewC st e x' : Option (View E)) = (viewC st e x).map fun v =>
      { v with kind := kindR x'.kind, t := tyR x'.t, state := stateR x'.state,
               other := x'.other.map EndId.mk, owner := x'.owner.map InstId.mk,
               index := x'.index, pending := pendR x'.kind e x'.pending } := by
  unfold viewC
  rw [hb]
  cases hxb : x.buffer with
  | none => simp
  | some b => cases hbb : st.bufs b <;> simp [hbb]

/-- **The relation at an updated end**: both machines update the end `e` keeping its parked
buffer, and the new records agree field by field. -/
theorem rel_at (st st1 : Cabi.Store α) (s : CStore E) (e : Nat) (x x' : Cabi.End)
    (xs xs' : End E) (hR : EndsRel st s) (hxs : s.end? ⟨e⟩ = some xs)
    (he : st.ends e = some x) (hb1 : st1.bufs = st.bufs) (hbuf : x'.buffer = x.buffer)
    (hbuf' : xs'.buffer = xs.buffer) (hk : xs'.kind = kindR x'.kind) (ht : xs'.t = tyR x'.t)
    (hs : xs'.state = stateR x'.state) (ho : xs'.other = x'.other.map EndId.mk)
    (how : xs'.owner = x'.owner.map InstId.mk) (hi : xs'.index = x'.index)
    (hp : xs'.common.pending = pendR x'.kind e x'.pending) :
    some (viewS xs') = viewC st1 e x' := by
  have h := hR e
  rw [hxs, he] at h
  simp only [Option.map_some, Option.bind_some] at h
  rw [viewC_congr st st1 e x' (fun _ _ => by rw [hb1]), viewC_eq st e x x' hbuf, ← h]
  simp [viewS, hbuf', hk, ht, hs, ho, how, hi, hp]

/-- The view of an end without a parked buffer, field by field. -/
theorem view_unparked (st1 : Cabi.Store α) (e : Nat) (x' : Cabi.End) (xs' : End E)
    (hbuf : x'.buffer = none) (hbuf' : xs'.buffer = none) (hk : xs'.kind = kindR x'.kind)
    (ht : xs'.t = tyR x'.t) (hs : xs'.state = stateR x'.state)
    (ho : xs'.other = x'.other.map EndId.mk) (how : xs'.owner = x'.owner.map InstId.mk)
    (hi : xs'.index = x'.index) (hp : xs'.common.pending = pendR x'.kind e x'.pending) :
    some (viewS xs') = viewC st1 e x' := by
  simp [viewS, viewC, hbuf, hbuf', hk, ht, hs, ho, how, hi, hp]

/-! ## `End.copy`: the transcription's cases 1, 4 and 5 -/

section Copy

variable [Inhabited α]

/-- A successful copy starts without a parked buffer. -/
theorem copyEnd_buffer_none (st st1 : Cabi.Store α) (e b : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (h : st.copyEnd e b = .ok st1) : x.buffer = none := by
  cases hxb : x.buffer with
  | none => rfl
  | some c =>
    simp [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, Cabi.check, bind,
      Except.bind, pure, Except.pure] at h

/-- Case 1, as an equation: the peer is gone (its drop left an event pending). -/
theorem copyEnd_dropped_eq (st : Cabi.Store α) (e b : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = none)
    (hp : x.pending.isSome = true) :
    st.copyEnd e b = .ok (st.setEnd e (x.withState .copying)) := by
  simp [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, hp, Cabi.check,
    Cabi.End.withState, bind, Except.bind, pure, Except.pure]

/-- **`End.copy` towards a dropped peer, in both machines** (case 1): only the state changes. -/
theorem copyEnd_sim_dropped (st st1 : Cabi.Store α) (s : CStore E) (e b : Nat)
    (x : Cabi.End) (bx : Cabi.Buf α) (hR : EndsRel st s) (he : st.ends e = some x)
    (hxo : x.other = none) (h : st.copyEnd e b = .ok st1) :
    ∃ s1, copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (s1, .none) ∧ EndsRel st1 s1 := by
  have hxb := copyEnd_buffer_none st st1 e b x he h
  have hp : x.pending.isSome = true := by
    cases hp : x.pending with
    | none =>
      simp [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, hp, Cabi.check,
        bind, Except.bind, pure, Except.pure] at h
    | some _ => rfl
  have hst1 : st1 = st.setEnd e (x.withState .copying) :=
    Except.ok.inj (h.symm.trans (copyEnd_dropped_eq st e b x he hxb hxo hp))
  obtain ⟨xs, hxs, hxk, -, -, hxso, -, -, -, -⟩ := view_of_unparked st s hR e x he hxb
  have hc : copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s =
      .ok (setEnd s ⟨e⟩ { xs with state := .copying }, .none) := by
    simp [copyCore, hxs, hxk, isReadable_kindR, hxso, hxo]
  refine ⟨_, hc, ?_⟩
  rw [hst1]
  refine rel_frame st _ s _ e hR rfl (fun c hc => by simp [Cabi.Store.setEnd, Cabi.upd, hc])
    (fun c hc => by rw [end?_setEnd_ne _ _ hc]) ?_
  rw [end?_setEnd_self hxs]
  have h' := rel_at_update st (st.setEnd e (x.withState .copying)) s e x (x.withState .copying)
    xs { xs with state := .copying } (fun v => { v with state := stateR .copying }) hR hxs he rfl
    (by rw [viewC_withState]; exact congrArg _ (viewC_congr _ _ e x (fun _ _ => rfl)))
  simpa [Cabi.Store.setEnd, Cabi.upd] using h'

/-- Case 4, as an equation: the peer's zero-length copy completes (or a read meets a
zero-length write); the new buffer parks. -/
theorem copyEnd_zero_peer_spec (st st1 : Cabi.Store α) (e b o ob : Nat) (x y : Cabi.End)
    (bx obx : Cabi.Buf α) (he : st.ends e = some x) (hxb : x.buffer = none)
    (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx)
    (h3 : ¬ (0 < bx.remain ∧ 0 < obx.remain))
    (h4 : 0 < bx.remain ∨ (x.kind.isReadable = true ∧ obx.remain = 0))
    (h : st.copyEnd e b = .ok st1) :
    st1.bufs = st.bufs ∧ (∀ c, c ≠ e → c ≠ o → st1.ends c = st.ends c) ∧
      st1.ends e = some ((x.withState .copying).withBuffer (some b)) ∧
      st1.ends o = some ((y.withPending 0).withBuffer none) := by
  have h3' : (decide (0 < bx.remain) && decide (0 < obx.remain)) = false := by
    simpa using h3
  have h4' : (decide (0 < bx.remain) || (x.kind.isReadable && decide (obx.remain = 0))) = true := by
    simpa using h4
  simp [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, Cabi.check,
    Cabi.Store.setEnd, Cabi.upd, hoe, Ne.symm hoe, ho, hyb, Cabi.Store.getBuf, hb, hob,
    Cabi.Store.notify, bind, Except.bind, pure, Except.pure, h3', h4'] at h
  subst h
  refine ⟨rfl, fun c hce hco => by simp [Cabi.upd, hce, hco], ?_, ?_⟩
  · cases x; simp_all [Cabi.upd, Cabi.End.withState, Cabi.End.withBuffer]
  · cases y; simp_all [Cabi.upd, Cabi.End.withPending, Cabi.End.withBuffer]

/-- **`End.copy` meeting a zero-length peer, in both machines** (case 4). -/
theorem copyEnd_sim_zero_peer (st st1 : Cabi.Store α) (s : CStore E) (e b o ob : Nat)
    (x y : Cabi.End) (bx obx : Cabi.Buf α) (hR : EndsRel st s)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx)
    (h3 : ¬ (0 < bx.remain ∧ 0 < obx.remain))
    (h4 : 0 < bx.remain ∨ (x.kind.isReadable = true ∧ obx.remain = 0))
    (h : st.copyEnd e b = .ok st1) :
    ∃ s1, copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (s1, .none) ∧ EndsRel st1 s1 := by
  obtain ⟨hfb, hfr, hfe, hfo⟩ := copyEnd_zero_peer_spec st st1 e b o ob x y bx obx he hxb hxo hoe
    ho hyb hb hob h3 h4 h
  obtain ⟨xs, hxs, hxk, hxt, -, hxso, hxsb, hxow, hxi, hxp⟩ := view_of_unparked st s hR e x he hxb
  obtain ⟨ys, hys, hyk, hyt, hyst, hyo, hysb, hyow, hyi, hyp⟩ :=
    view_of_parked st s hR o y ob obx ho hyb hob
  have hoe' : (⟨o⟩ : EndId) ≠ ⟨e⟩ := fun h' => hoe (EndId.mk.inj h')
  have hc : copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (setEnd (setEnd s ⟨e⟩
      { xs with state := .copying, buffer := some (bufR b bx) }) ⟨o⟩
      { ys.withNotify ⟨o⟩ 0 with buffer := none }, .none) := by
    have h3s : ¬ (0 < (bufR b bx : BufferDesc E).remain ∧ 0 < (bufR ob obx : BufferDesc E).remain) := by
      rw [remain_bufR, remain_bufR]; exact h3
    have h4s : 0 < (bufR b bx : BufferDesc E).remain ∨
        (x.kind.isReadable = true ∧ (bufR ob obx : BufferDesc E).remain = 0) := by
      rw [remain_bufR, remain_bufR]; exact h4
    simp [copyCore, hxs, hxk, isReadable_kindR, hxso, hxo, hoe', hys, hysb, h3s, h4s]
  refine ⟨_, hc, rel_frame2 st st1 s _ e o hR hfb hfr (fun c h1 h2 => by
    rw [end?_setEnd_ne _ _ h2, end?_setEnd_ne _ _ h1]) ?_ ?_⟩
  · rw [end?_setEnd_ne _ _ (Ne.symm hoe'), end?_setEnd_self hxs, hfe]
    simp [viewS, viewC, Cabi.End.withState, Cabi.End.withBuffer, hfb, hb, hxk, hxt, hxso, hxow, hxi,
      hxp, stateR]
  · rw [end?_setEnd_self (by rw [end?_setEnd_ne _ _ hoe']; exact hys), hfo]
    simp [viewS, viewC, Cabi.End.withPending, Cabi.End.withBuffer, hyk, hyt, hyst, hyo, hyow, hyi,
      ← pendR_some _ _ _ ys hyk, End.withNotify]

/-- Case 5, as an equation: a zero-length copy that completes at once with progress `0`. -/
theorem copyEnd_zero_self_spec (st st1 : Cabi.Store α) (e b o ob : Nat) (x y : Cabi.End)
    (bx obx : Cabi.Buf α) (he : st.ends e = some x) (hxb : x.buffer = none)
    (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx)
    (h0 : bx.remain = 0) (h5 : ¬ (x.kind.isReadable = true ∧ obx.remain = 0))
    (h : st.copyEnd e b = .ok st1) :
    st1.bufs = st.bufs ∧ (∀ c, c ≠ e → st1.ends c = st.ends c) ∧
      st1.ends e = some ((x.withState .copying).withPending 0) := by
  have h5' : (x.kind.isReadable && decide (obx.remain = 0)) = false := by simpa using h5
  simp [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, Cabi.check,
    Cabi.Store.setEnd, Cabi.upd, hoe, ho, hyb, Cabi.Store.getBuf, hb, hob,
    Cabi.Store.notify, bind, Except.bind, pure, Except.pure, h0, h5'] at h
  subst h
  refine ⟨rfl, fun c hce => by simp [Cabi.upd, hce], ?_⟩
  cases x; simp_all [Cabi.upd, Cabi.End.withState, Cabi.End.withPending]

/-- **A zero-length copy that completes at once, in both machines** (case 5). -/
theorem copyEnd_sim_zero_self (st st1 : Cabi.Store α) (s : CStore E) (e b o ob : Nat)
    (x y : Cabi.End) (bx obx : Cabi.Buf α) (hR : EndsRel st s)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx)
    (h0 : bx.remain = 0) (h5 : ¬ (x.kind.isReadable = true ∧ obx.remain = 0))
    (h : st.copyEnd e b = .ok st1) :
    ∃ s1, copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (s1, .none) ∧ EndsRel st1 s1 := by
  obtain ⟨hfb, hfr, hfe⟩ := copyEnd_zero_self_spec st st1 e b o ob x y bx obx he hxb hxo hoe
    ho hyb hb hob h0 h5 h
  obtain ⟨xs, hxs, hxk, hxt, -, hxso, hxsb, hxow, hxi, -⟩ := view_of_unparked st s hR e x he hxb
  obtain ⟨ys, hys, -, -, -, -, hysb, -, -, -⟩ := view_of_parked st s hR o y ob obx ho hyb hob
  have hoe' : (⟨o⟩ : EndId) ≠ ⟨e⟩ := fun h' => hoe (EndId.mk.inj h')
  have hc : copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s =
      .ok (setEnd s ⟨e⟩ ({ xs with state := .copying }.withNotify ⟨e⟩ 0), .none) := by
    have h3s : ¬ (0 < (bufR b bx : BufferDesc E).remain ∧ 0 < (bufR ob obx : BufferDesc E).remain) := by
      rw [remain_bufR, h0]; omega
    have h4s : ¬ (0 < (bufR b bx : BufferDesc E).remain ∨
        (x.kind.isReadable = true ∧ (bufR ob obx : BufferDesc E).remain = 0)) := by
      rw [remain_bufR, remain_bufR, h0]
      rintro (h' | h')
      · omega
      · exact h5 h'
    simp [copyCore, hxs, hxk, isReadable_kindR, hxso, hxo, hoe', hys, hysb, h3s, h4s]
  refine ⟨_, hc, rel_frame st st1 s _ e hR hfb hfr (fun c hc => by rw [end?_setEnd_ne _ _ hc]) ?_⟩
  rw [end?_setEnd_self hxs, hfe]
  simp only [Option.map_some, Option.bind_some]
  exact view_unparked st1 e _ _ hxb hxsb hxk hxt rfl hxso hxow hxi
    (pendR_some x.kind e 0 xs hxk)

/-- A successful copy whose peer is linked has the peer. -/
theorem copyEnd_peer (st st1 : Cabi.Store α) (e b o : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (h : st.copyEnd e b = .ok st1) : ∃ y, st.ends o = some y := by
  cases ho : st.ends o with
  | none =>
    simp [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, Cabi.check,
      Cabi.Store.setEnd, Cabi.upd, hoe, ho, bind, Except.bind, pure,
      Except.pure] at h
  | some y => exact ⟨y, rfl⟩

/-- A successful copy meeting a parked buffer has both buffers. -/
theorem copyEnd_bufs (st st1 : Cabi.Store α) (e b o ob : Nat) (x y : Cabi.End)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (ho : st.ends o = some y) (hyb : y.buffer = some ob) (h : st.copyEnd e b = .ok st1) :
    (∃ bx, st.bufs b = some bx) ∧ ∃ obx, st.bufs ob = some obx := by
  obtain ⟨bx, hb⟩ : ∃ bx, st.bufs b = some bx := by
    cases hb : st.bufs b with
    | none =>
      simp [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, Cabi.check,
        Cabi.Store.setEnd, Cabi.upd, hoe, ho, hyb, Cabi.Store.getBuf, hb, bind,
        Except.bind, pure, Except.pure] at h
    | some bx => exact ⟨bx, rfl⟩
  refine ⟨⟨bx, hb⟩, ?_⟩
  cases hob : st.bufs ob with
  | none =>
    simp [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, Cabi.check,
      Cabi.Store.setEnd, Cabi.upd, hoe, ho, hyb, Cabi.Store.getBuf, hb, hob, bind,
      Except.bind, pure, Except.pure] at h
  | some obx => exact ⟨obx, rfl⟩

/-- A successful case 3 did not trap. -/
theorem copyEnd_no_trap (st st1 : Cabi.Store α) (e b o ob : Nat) (x y : Cabi.End)
    (bx obx : Cabi.Buf α) (he : st.ends e = some x) (hxb : x.buffer = none)
    (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx) (h3 : 0 < bx.remain ∧ 0 < obx.remain)
    (h : st.copyEnd e b = .ok st1) :
    (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) = false := by
  cases ht : (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) with
  | false => rfl
  | true =>
    have hc : st.copyEnd e b = .error (.trap "copy to self") := by
      simp only [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, Cabi.check,
        Cabi.Store.setEnd, Cabi.upd, hoe, ho, hyb, Cabi.Store.getBuf, hb, hob, bind, Except.bind,
        pure, Except.pure, Option.isNone_none, ite_true, ite_false, gt_iff_lt, h3.1, h3.2,
        decide_true, Bool.and_self, Cabi.trapIf, ht, ite_true, ite_false]
    rw [hc] at h; cases h

/-- **Every successful `End.copy`, in both machines**: the transcription's `End.copy` is
silmaril's `copyCore` (cases 1 to 5), and the stores stay related. -/
theorem copyEnd_sim (st st1 : Cabi.Store α) (s : CStore E) (e b : Nat) (x : Cabi.End)
    (bx : Cabi.Buf α) (hR : EndsRel st s) (hD : BufsDistinct st)
    (hfresh : ∀ c z, st.ends c = some z → z.buffer ≠ some b)
    (he : st.ends e = some x) (hb : st.bufs b = some bx) (hself : x.other ≠ some e)
    (hwf : ∀ o y ob obx, x.other = some o → st.ends o = some y → y.buffer = some ob →
      st.bufs ob = some obx → (if x.kind.isReadable then obx else bx).ReadOk)
    (h : st.copyEnd e b = .ok st1) :
    ∃ s1 a, copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (s1, a) ∧ EndsRel st1 s1 := by
  have hxb : x.buffer = none := copyEnd_buffer_none st st1 e b x he h
  cases hxo : x.other with
  | none =>
    obtain ⟨s1, h1, h2⟩ := copyEnd_sim_dropped st st1 s e b x bx hR he hxo h
    exact ⟨s1, _, h1, h2⟩
  | some o =>
    show ∃ s1 a, copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (s1, a) ∧ EndsRel st1 s1
    have hoe : o ≠ e := fun h' => hself (h' ▸ hxo)
    obtain ⟨y, ho⟩ := copyEnd_peer st st1 e b o x he hxb hxo hoe h
    cases hyb : y.buffer with
    | none =>
      obtain ⟨s1, h1, h2⟩ := copyEnd_sim_park st st1 s e b o x y bx hR he hxb hxo hoe ho hyb hb h
      exact ⟨s1, _, h1, h2⟩
    | some ob =>
      show ∃ s1 a, copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (s1, a) ∧ EndsRel st1 s1
      obtain ⟨-, obx, hob⟩ := copyEnd_bufs st st1 e b o ob x y he hxb hxo hoe ho hyb h
      by_cases h3 : 0 < bx.remain ∧ 0 < obx.remain
      · have hbo : b ≠ ob := fun h' => hfresh o y ho (h' ▸ hyb)
        exact copyEnd_sim_transfer st st1 s e b o ob x y bx obx hR hD hfresh he hxb hxo hoe ho hyb
          hb hob hbo (copyEnd_no_trap st st1 e b o ob x y bx obx he hxb hxo hoe ho hyb hb hob h3 h)
          h3.1 h3.2 (hwf o y ob obx hxo ho hyb hob) h
      · by_cases h4 : 0 < bx.remain ∨ (x.kind.isReadable = true ∧ obx.remain = 0)
        · obtain ⟨s1, h1, h2⟩ := copyEnd_sim_zero_peer st st1 s e b o ob x y bx obx hR he hxb hxo
            hoe ho hyb hb hob h3 h4 h
          exact ⟨s1, _, h1, h2⟩
        · have h0 : bx.remain = 0 := by omega
          obtain ⟨s1, h1, h2⟩ := copyEnd_sim_zero_self st st1 s e b o ob x y bx obx hR he hxb hxo
            hoe ho hyb hb hob h0 (fun h' => h4 (.inr h')) h
          exact ⟨s1, _, h1, h2⟩

end Copy

/-! ## `End.cancel` -/

/-- A successful `End.cancel` cancels a copying end. -/
theorem cancelEnd_copying (st st1 : Cabi.Store α) (e : Nat) (coin : Bool) (x : Cabi.End)
    (he : st.ends e = some x) (h : st.cancelEnd e coin = .ok st1) : x.state = .copying := by
  by_contra hne
  simp [Cabi.Store.cancelEnd, Cabi.Store.getEnd, Cabi.need, he, Cabi.check, hne, bind,
    Except.bind, pure, Except.pure] at h

/-- `End.cancel` with an event pending: only the state changes. -/
theorem cancelEnd_some (st st1 : Cabi.Store α) (e p : Nat) (coin : Bool) (x : Cabi.End)
    (he : st.ends e = some x) (hst : x.state = .copying) (hp : x.pending = some p)
    (h : st.cancelEnd e coin = .ok st1) :
    st1.bufs = st.bufs ∧ (∀ c, c ≠ e → st1.ends c = st.ends c) ∧
      st1.ends e = some (x.withState .cancelling) := by
  have hst1 : st.setEnd e { x with state := .cancelling } = st1 := by
    simpa [Cabi.Store.cancelEnd, Cabi.Store.getEnd, Cabi.need, he, Cabi.check, hst, hp, bind,
      Except.bind, pure, Except.pure] using h
  rw [← hst1]
  exact ⟨rfl, fun c hc => by simp [Cabi.Store.setEnd, Cabi.upd, hc],
    by simp [Cabi.Store.setEnd, Cabi.upd, Cabi.End.withState]⟩

/-- `End.cancel` without a pending event reads the peer. -/
theorem cancelEnd_peer (st st1 : Cabi.Store α) (e : Nat) (coin : Bool) (x : Cabi.End)
    (he : st.ends e = some x) (hself : x.other ≠ some e) (hst : x.state = .copying)
    (hp : x.pending = none) (h : st.cancelEnd e coin = .ok st1) :
    ∃ o y, x.other = some o ∧ o ≠ e ∧ st.ends o = some y := by
  cases hxo : x.other with
  | none =>
    simp [Cabi.Store.cancelEnd, Cabi.Store.getEnd, Cabi.need, he, Cabi.check, hst, hp, hxo,
      bind, Except.bind, pure, Except.pure] at h
  | some o =>
    have hoe : o ≠ e := fun h' => hself (h' ▸ hxo)
    cases ho : st.ends o with
    | none =>
      simp [Cabi.Store.cancelEnd, Cabi.Store.getEnd, Cabi.need, he, Cabi.check, hst, hp, hxo,
        Cabi.Store.setEnd, Cabi.upd, hoe, ho, bind, Except.bind, pure, Except.pure] at h
    | some y => exact ⟨o, y, rfl, hoe, ho⟩

/-- `End.cancel` notifying at once (guest peer, deterministic profile, or the coin). -/
theorem cancelEnd_notify (st st1 : Cabi.Store α) (e o : Nat) (coin : Bool) (x y : Cabi.End)
    (he : st.ends e = some x) (hst : x.state = .copying) (hp : x.pending = none)
    (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y)
    (hcoin : (y.owner.isSome || st.det || coin) = true) (h : st.cancelEnd e coin = .ok st1) :
    st1.bufs = st.bufs ∧ (∀ c, c ≠ e → st1.ends c = st.ends c) ∧
      st1.ends e = some ((x.withState .cancelling).withPending 0) := by
  have hc' : (y.owner.isSome = true ∨ st.det = true) ∨ coin = true := by
    simpa only [Bool.or_eq_true] using hcoin
  have hst1 : (st.setEnd e { x with state := .cancelling }).setEnd e
      { x with state := .cancelling, pending := some 0 } = st1 := by
    simpa [Cabi.Store.cancelEnd, Cabi.Store.getEnd, Cabi.need, he, Cabi.check, hst, hp, hxo,
      Cabi.Store.setEnd, Cabi.upd, hoe, ho, hc', Cabi.Store.notify, bind, Except.bind, pure,
      Except.pure] using h
  rw [← hst1]
  exact ⟨rfl, fun c hc => by simp [Cabi.Store.setEnd, Cabi.upd, hc],
    by simp [Cabi.Store.setEnd, Cabi.upd, Cabi.End.withState, Cabi.End.withPending]⟩

/-- `End.cancel` leaving the event to the host (host peer, the coin says later). -/
theorem cancelEnd_quiet (st st1 : Cabi.Store α) (e o : Nat) (coin : Bool) (x y : Cabi.End)
    (he : st.ends e = some x) (hst : x.state = .copying) (hp : x.pending = none)
    (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y)
    (hcoin : (y.owner.isSome || st.det || coin) = false) (h : st.cancelEnd e coin = .ok st1) :
    st1.bufs = st.bufs ∧ (∀ c, c ≠ e → st1.ends c = st.ends c) ∧
      st1.ends e = some (x.withState .cancelling) := by
  have hc' : (y.owner.isSome = false ∧ st.det = false) ∧ coin = false := by
    simpa only [Bool.or_eq_false_iff] using hcoin
  have hst1 : st.setEnd e { x with state := .cancelling } = st1 := by
    simpa [Cabi.Store.cancelEnd, Cabi.Store.getEnd, Cabi.need, he, Cabi.check, hst, hp, hxo,
      Cabi.Store.setEnd, Cabi.upd, hoe, ho, hc', bind, Except.bind, pure, Except.pure] using h
  rw [← hst1]
  exact ⟨rfl, fun c hc => by simp [Cabi.Store.setEnd, Cabi.upd, hc],
    by simp [Cabi.Store.setEnd, Cabi.upd, Cabi.End.withState]⟩

/-- Silmaril's `cancel` notifying at once. -/
theorem cancel_eq_notify (s : CStore E) (e : Nat) (n : Bool) (xs : End E)
    (hxs : s.end? ⟨e⟩ = some xs) (hst : xs.state = .copying)
    (hc : xs.hasPending = false ∧ (peerGuest xs s = true ∨ n = true)) :
    cancel ⟨e⟩ n s = setEnd s ⟨e⟩ ({ xs with state := .cancellingCopy }.withNotify ⟨e⟩ 0) := by
  unfold cancel
  rw [hxs]
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h' hst)),
    ite_eq_left_of_eq_true _ _ (eq_true hc)]

/-- Silmaril's `cancel` without notifying. -/
theorem cancel_eq_quiet (s : CStore E) (e : Nat) (n : Bool) (xs : End E)
    (hxs : s.end? ⟨e⟩ = some xs) (hst : xs.state = .copying)
    (hc : ¬ (xs.hasPending = false ∧ (peerGuest xs s = true ∨ n = true))) :
    cancel ⟨e⟩ n s = setEnd s ⟨e⟩ { xs with state := .cancellingCopy } := by
  unfold cancel
  rw [hxs]
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h' hst)),
    ite_eq_right_of_eq_false _ _ (eq_false hc)]

/-- Both machines update one end, keeping its parked buffer, with agreeing fields: the stores
stay related. -/
theorem rel_update1 (st st1 : Cabi.Store α) (s : CStore E) (e : Nat) (x x' : Cabi.End)
    (xs xs' : End E) (hR : EndsRel st s) (hxs : s.end? ⟨e⟩ = some xs)
    (he : st.ends e = some x) (hb1 : st1.bufs = st.bufs) (hfr : ∀ c, c ≠ e → st1.ends c = st.ends c)
    (hfe : st1.ends e = some x') (hbuf : x'.buffer = x.buffer)
    (hbuf' : xs'.buffer = xs.buffer) (hk : xs'.kind = kindR x'.kind) (ht : xs'.t = tyR x'.t)
    (hs : xs'.state = stateR x'.state) (ho : xs'.other = x'.other.map EndId.mk)
    (how : xs'.owner = x'.owner.map InstId.mk) (hi : xs'.index = x'.index)
    (hp : xs'.common.pending = pendR x'.kind e x'.pending) :
    EndsRel st1 (setEnd s ⟨e⟩ xs') := by
  refine rel_frame st st1 s _ e hR hb1 hfr (fun c hc => by rw [end?_setEnd_ne _ _ hc]) ?_
  rw [end?_setEnd_self hxs, hfe]
  exact rel_at st st1 s e x x' xs xs' hR hxs he hb1 hbuf hbuf' hk ht hs ho how hi hp

/-- **`End.cancel`, in both machines**: Python's coin `coin` is silmaril's `notifyNow` (with
the deterministic profile's `det`: `det || coin`); the stores stay related. -/
theorem cancelEnd_sim (st st1 : Cabi.Store α) (s : CStore E) (e : Nat) (coin : Bool)
    (x : Cabi.End) (hR : EndsRel st s) (hPB : BufsPresent st) (he : st.ends e = some x)
    (hself : x.other ≠ some e) (h : st.cancelEnd e coin = .ok st1) :
    EndsRel st1 (cancel ⟨e⟩ (st.det || coin) s) := by
  have hst : x.state = .copying := cancelEnd_copying st st1 e coin x he h
  obtain ⟨xs, hxs, hxk, hxt, hxst, hxo, hxow, hxi, hxp⟩ := view_of st s hR e x he (hPB e x he)
  have hxst' : xs.state = .copying := by rw [hxst, hst]; rfl
  cases hp : x.pending with
  | some p =>
    show EndsRel st1 (cancel ⟨e⟩ (st.det || coin) s)
    obtain ⟨hb1, hfr, hfe⟩ := cancelEnd_some st st1 e p coin x he hst hp h
    have hhp : xs.hasPending = true := by simp [End.hasPending, hxp, hp, pendR]
    rw [cancel_eq_quiet s e _ xs hxs hxst' (fun h' => Bool.false_ne_true (h'.1.symm.trans hhp))]
    exact rel_update1 st st1 s e x _ xs _ hR hxs he hb1 hfr hfe rfl rfl hxk hxt rfl hxo hxow hxi
      (by simp [hxp, hp, Cabi.End.withState])
  | none =>
    show EndsRel st1 (cancel ⟨e⟩ (st.det || coin) s)
    obtain ⟨o, y, hxoo, hoe, ho⟩ := cancelEnd_peer st st1 e coin x he hself hst hp h
    obtain ⟨ys, hys, -, -, -, -, hyow, -, -⟩ := view_of st s hR o y ho (hPB o y ho)
    have hpg : peerGuest xs s = y.owner.isSome := by simp [peerGuest, hxo, hxoo, hys, hyow]
    have hhp : xs.hasPending = false := by simp [End.hasPending, hxp, hp, pendR]
    cases hcoin : (y.owner.isSome || st.det || coin) with
    | true =>
      show EndsRel st1 (cancel ⟨e⟩ (st.det || coin) s)
      obtain ⟨hb1, hfr, hfe⟩ := cancelEnd_notify st st1 e o coin x y he hst hp hxoo hoe ho hcoin h
      have hor : y.owner.isSome = true ∨ (st.det || coin) = true :=
        Bool.or_eq_true_iff.mp (by rw [← Bool.or_assoc]; exact hcoin)
      rw [cancel_eq_notify s e _ xs hxs hxst' ⟨hhp, hpg ▸ hor⟩]
      exact rel_update1 st st1 s e x _ xs _ hR hxs he hb1 hfr hfe rfl rfl hxk hxt rfl hxo hxow hxi
        (pendR_some x.kind e 0 xs hxk)
    | false =>
      show EndsRel st1 (cancel ⟨e⟩ (st.det || coin) s)
      obtain ⟨hb1, hfr, hfe⟩ := cancelEnd_quiet st st1 e o coin x y he hst hp hxoo hoe ho hcoin h
      have hf : y.owner.isSome = false ∧ (st.det || coin) = false :=
        Bool.or_eq_false_iff.mp (by rw [← Bool.or_assoc]; exact hcoin)
      have hnc : ¬ (xs.hasPending = false ∧ (peerGuest xs s = true ∨ (st.det || coin) = true)) :=
        fun ⟨_, hor⟩ => hor.elim (fun h' => Bool.false_ne_true ((hpg.symm.trans h').symm.trans hf.1).symm)
          (fun h' => Bool.false_ne_true (h'.symm.trans hf.2).symm)
      rw [cancel_eq_quiet s e _ xs hxs hxst' hnc]
      exact rel_update1 st st1 s e x _ xs _ hR hxs he hb1 hfr hfe rfl rfl hxk hxt rfl hxo hxow hxi
        (by simp [hxp, hp, Cabi.End.withState])

/-! ## `End.drop` -/

theorem leaveSet_bufs (st st' : Cabi.Store α) (w : Cabi.WRef) (h : st.leaveSet w = .ok st') :
    st'.bufs = st.bufs := by
  unfold Cabi.Store.leaveSet at h
  revert h
  cases st.wsetOf w with
  | none => intro h; injection h with h; subst h; rfl
  | some old =>
    intro h
    obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
    injection h with h; subst h; rfl

/-- `join(None)` of an end: only its `wset` field (and the sets) change. -/
theorem join_none_spec (st st1 : Cabi.Store α) (e : Nat)
    (h : st.join (.end_ e) none = .ok st1) :
    st1.bufs = st.bufs ∧ (∀ c, c ≠ e → st1.ends c = st.ends c) ∧
      ∀ z, st.ends e = some z → st1.ends e = some { z with wset := none } := by
  refine ⟨?_, fun c hc => Cabi.Store.join_ends_ne _ _ _ _ _ h hc, ?_⟩
  · unfold Cabi.Store.join at h
    obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
    obtain ⟨s1, h1, h⟩ := Cabi.bind_ok.1 h
    obtain ⟨s2, h2, h⟩ := Cabi.bind_ok.1 h
    simp only [Cabi.Store.enterSet, pure, Except.pure] at h
    injection h with h; subst h
    obtain ⟨_, -, h2⟩ := Cabi.bind_ok.1 h2
    injection h2 with h2; subst h2
    exact (leaveSet_bufs st s1 _ h1 : s1.bufs = st.bufs)
  · intro z hz
    unfold Cabi.Store.join at h
    obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
    obtain ⟨s1, h1, h⟩ := Cabi.bind_ok.1 h
    obtain ⟨s2, h2, h⟩ := Cabi.bind_ok.1 h
    simp only [Cabi.Store.enterSet, pure, Except.pure] at h
    injection h with h; subst h
    have hz1 : s1.ends e = some z := by rw [Cabi.Store.leaveSet_ends _ _ _ h1, hz]
    simp only [Cabi.Store.setWsetField, Cabi.Store.getEnd_of _ _ _ hz1, bind, Except.bind, pure,
      Except.pure] at h2
    injection h2 with h2; subst h2
    simp [Cabi.Store.setEnd, Cabi.upd]

/-- The peer after `End.drop`: unlinked, and notified with progress `0` if it was not `DONE`
and had no pending event. -/
def dropPeerC (y : Cabi.End) : Cabi.End :=
  if y.state ≠ .done ∧ y.pending = none then { y with other := none, pending := some 0 }
  else { y with other := none }

/-- The transcription's `End.drop`. -/
theorem dropEnd_spec (st st1 : Cabi.Store α) (e : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (hself : x.other ≠ some e) (h : st.dropEnd e = .ok st1) :
    st1.bufs = st.bufs ∧ st1.ends e = some { x with other := none, wset := none } ∧
      (∀ c, c ≠ e → x.other ≠ some c → st1.ends c = st.ends c) ∧
      ∀ o, x.other = some o → ∃ y, st.ends o = some y ∧ st1.ends o = some (dropPeerC y) := by
  unfold Cabi.Store.dropEnd at h
  rw [Cabi.Store.getEnd_of _ _ _ he] at h
  obtain ⟨x', hx', h⟩ := Cabi.bind_ok.1 h
  injection hx' with hx'
  subst hx'
  obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨s1, h1, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨hjb, hjfr, hje⟩ := join_none_spec s1 st1 e h
  cases hxo : x.other with
  | none =>
    simp only [Cabi.Store.unlinkPeer, hxo, pure, Except.pure] at h1
    injection h1 with h1; subst h1
    refine ⟨hjb, ?_, fun c hc _ => hjfr c hc, fun o ho => nomatch ho⟩
    rw [hje x he]; cases x; simp_all
  | some o =>
    have hoe : o ≠ e := fun h' => hself (h' ▸ hxo)
    obtain ⟨y, ho⟩ : ∃ y, st.ends o = some y := by
      cases ho : st.ends o with
      | none =>
        simp [Cabi.Store.unlinkPeer, hxo, Cabi.Store.getEnd, Cabi.need, ho, bind, Except.bind]
          at h1
      | some y => exact ⟨y, rfl⟩
    simp only [Cabi.Store.unlinkPeer, hxo, Cabi.Store.getEnd_of _ _ _ ho, bind, Except.bind] at h1
    obtain ⟨_, -, h1⟩ := Cabi.bind_ok.1 h1
    obtain ⟨s2, h2, h1⟩ := Cabi.bind_ok.1 h1
    simp only [pure, Except.pure] at h1
    injection h1 with h1; subst h1
    -- `s2` is `st` with the peer unlinked (and maybe notified)
    have hs2 : s2.bufs = st.bufs ∧ (∀ c, c ≠ o → s2.ends c = st.ends c) ∧
        s2.ends o = some (dropPeerC y) := by
      unfold Cabi.Store.notifyIfIdle at h2
      by_cases hc : y.state ≠ .done ∧ y.pending = none
      · have hc' : (y.state != .done && y.pending.isNone) = true := by simp [hc.1, hc.2]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc')] at h2
        obtain ⟨_, h2b, h2o, h2e⟩ := Cabi.Store.notify_spec _ _ _ _ { y with other := none }
          (by simp [Cabi.Store.setEnd, Cabi.upd]) h2
        refine ⟨h2b, fun c hc2 => by rw [h2o c hc2]; simp [Cabi.Store.setEnd, Cabi.upd, hc2], ?_⟩
        rw [h2e]
        simp [dropPeerC, hc, Cabi.End.withPending]
      · have hc' : (y.state != .done && y.pending.isNone) = false := by
          simp only [Bool.and_eq_false_iff, 
            ]
          by_contra hh
          push Not at hh
          exact hc ⟨by simpa using hh.1, by simpa using hh.2⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [hc']))] at h2
        simp only [pure, Except.pure] at h2
        injection h2 with h2; subst h2
        refine ⟨rfl, fun c hc2 => by simp [Cabi.Store.setEnd, Cabi.upd, hc2], ?_⟩
        simp [Cabi.Store.setEnd, Cabi.upd, dropPeerC, hc]
    obtain ⟨h2b, h2fr, h2o⟩ := hs2
    refine ⟨hjb.trans h2b, ?_, fun c hce hco => ?_, fun o' ho' => ?_⟩
    · rw [hje { x with other := none } (by simp [Cabi.Store.setEnd, Cabi.upd])]
    · have hco' : c ≠ o := fun h' => hco (by rw [h'])
      rw [hjfr c hce]
      simp [Cabi.Store.setEnd, Cabi.upd, hce, h2fr c hco']
    · cases ho'
      refine ⟨y, ho, ?_⟩
      rw [hjfr o hoe]
      simp [Cabi.Store.setEnd, Cabi.upd, hoe, h2o]

theorem stateR_done (s : Cabi.EndState) : stateR s = .done ↔ s = .done := by
  cases s <;> simp [stateR]

theorem end?_leaveSet (w : Option WsetId) (e c : EndId) (s : CStore E) :
    (leaveSet w e s).end? c = s.end? c := end?_of_ends_eq (leaveSet_ends w e s) c

/-- The peer after `End.drop`, in both machines. -/
theorem dropPeer_view (st st1 : Cabi.Store α) (s : CStore E) (o : Nat) (y : Cabi.End) (ys : End E)
    (hR : EndsRel st s) (hys : s.end? ⟨o⟩ = some ys) (ho : st.ends o = some y)
    (hb1 : st1.bufs = st.bufs) (hyk : ys.kind = kindR y.kind) (hyt : ys.t = tyR y.t)
    (hyst : ys.state = stateR y.state) (hyow : ys.owner = y.owner.map InstId.mk)
    (hyi : ys.index = y.index) (hyp : ys.common.pending = pendR y.kind o y.pending) :
    some (viewS (ys.dropPeer ⟨o⟩)) = viewC st1 o (dropPeerC y) := by
  have hhp : ys.hasPending = false ↔ y.pending = none := by
    simp only [End.hasPending, hyp, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    cases y.pending <;> simp [pendR]
  have hsd : ys.state ≠ .done ↔ y.state ≠ .done := by rw [hyst]; exact not_congr (stateR_done _)
  by_cases hc : y.state ≠ .done ∧ y.pending = none
  · show some (viewS (ys.dropPeer ⟨o⟩)) = viewC st1 o (dropPeerC y)
    have hc' : ys.state ≠ .done ∧ ys.hasPending = false := ⟨hsd.2 hc.1, hhp.2 hc.2⟩
    have hdp : ys.dropPeer ⟨o⟩ = { ys with other := none }.withNotify ⟨o⟩ 0 := by
      simp only [End.dropPeer, ite_eq_left_of_eq_true _ _ (eq_true hc')]
    rw [hdp]
    refine rel_at st st1 s o y _ ys _ hR hys ho hb1 ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ (by
      rw [show dropPeerC y = { y with other := none, pending := some 0 } from
        ite_eq_left_of_eq_true _ _ (eq_true hc)]
      exact pendR_some y.kind o 0 ys hyk)
    all_goals simp [dropPeerC, hc, End.withNotify, hyk, hyt, hyst, hyow, hyi]
  · show some (viewS (ys.dropPeer ⟨o⟩)) = viewC st1 o (dropPeerC y)
    have hc' : ¬ (ys.state ≠ .done ∧ ys.hasPending = false) :=
      fun h' => hc ⟨hsd.1 h'.1, hhp.1 h'.2⟩
    have hdp : ys.dropPeer ⟨o⟩ = { ys with other := none } := by
      simp only [End.dropPeer, ite_eq_right_of_eq_false _ _ (eq_false hc')]
    rw [hdp]
    refine rel_at st st1 s o y _ ys _ hR hys ho hb1 ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp [dropPeerC, hc, hyk, hyt, hyst, hyow, hyi, hyp]

/-- **`End.drop`, in both machines**: the stores stay related. -/
theorem dropEnd_sim (st st1 : Cabi.Store α) (s : CStore E) (e : Nat) (x : Cabi.End)
    (hR : EndsRel st s) (hPB : BufsPresent st) (he : st.ends e = some x)
    (hself : x.other ≠ some e) (h : st.dropEnd e = .ok st1) :
    EndsRel st1 (dropEnd ⟨e⟩ s) := by
  obtain ⟨hb1, hfe, hfr, hfo⟩ := dropEnd_spec st st1 e x he hself h
  obtain ⟨xs, hxs, hxk, hxt, hxst, hxo, hxow, hxi, hxp⟩ := view_of st s hR e x he (hPB e x he)
  have hatE : ∀ s1 : CStore E, s1.end? ⟨e⟩ =
      some { xs with other := none, common := { xs.common with wset := none } } →
      (s1.end? ⟨e⟩).map viewS = (st1.ends e).bind (viewC st1 e) := by
    intro s1 hs1
    rw [hs1, hfe]
    exact rel_at st st1 s e x _ xs _ hR hxs he hb1 rfl rfl hxk hxt hxst (by simp) hxow hxi hxp
  cases hxoo : x.other with
  | none =>
    have hs : dropEnd ⟨e⟩ s = leaveSet xs.common.wset ⟨e⟩
        (setEnd s ⟨e⟩ { xs with other := none, common := { xs.common with wset := none } }) := by
      simp [dropEnd, hxs, hxo, hxoo]
    rw [hs]
    refine rel_frame st st1 s _ e hR hb1 (fun c hc => hfr c hc (by simp [hxoo]))
      (fun c hc => by rw [end?_leaveSet, end?_setEnd_ne _ _ hc]) (hatE _ ?_)
    rw [end?_leaveSet, end?_setEnd_self hxs]
  | some o =>
    show EndsRel st1 (dropEnd ⟨e⟩ s)
    have hoe : o ≠ e := fun h' => hself (h' ▸ hxoo)
    have hoe' : (⟨o⟩ : EndId) ≠ ⟨e⟩ := fun h' => hoe (EndId.mk.inj h')
    obtain ⟨y, ho, hfo'⟩ := hfo o hxoo
    obtain ⟨ys, hys, hyk, hyt, hyst, hyo, hyow, hyi, hyp⟩ := view_of st s hR o y ho (hPB o y ho)
    have hs : dropEnd ⟨e⟩ s = leaveSet xs.common.wset ⟨e⟩
        (setEnd (setEnd s ⟨o⟩ (ys.dropPeer ⟨o⟩)) ⟨e⟩
          { xs with other := none, common := { xs.common with wset := none } }) := by
      simp [dropEnd, hxs, hxo, hxoo, hoe, hys]
    rw [hs]
    refine rel_frame2 st st1 s _ e o hR hb1 (fun c hce hco => hfr c hce
      (fun h' => hco (Option.some.inj (h'.symm.trans hxoo)))) (fun c hce hco => by
        rw [end?_leaveSet, end?_setEnd_ne _ _ hce, end?_setEnd_ne _ _ hco]) (hatE _ ?_) ?_
    · rw [end?_leaveSet, end?_setEnd_self (by rw [end?_setEnd_ne _ _ (Ne.symm hoe')]; exact hxs)]
    · rw [end?_leaveSet, end?_setEnd_ne _ _ hoe', end?_setEnd_self hys, hfo']
      exact dropPeer_view st st1 s o y ys hR hys ho hb1 hyk hyt hyst hyow hyi hyp

/-! ## Future events -/

/-- The transcription's `future_event`, as an equation. -/
theorem deliverEnd_future_eq (st : Cabi.Store α) (e p : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (hst : x.kind.isStream = false) (hp : x.pending = some p)
    (ns : Cabi.EndState) (r : Cabi.CopyResult) (hout : FutureOutcome x p ns r) :
    st.deliverEnd e = .ok (st.setEnd e (delivered x ns),
      (x.kind.eventCode, x.index.getD 0, r.toNat)) := by
  rcases hout with ⟨rfl, hs, hb, rfl, rfl⟩ | ⟨rfl, ho, hd, rfl, rfl⟩ | ⟨rfl, ho, hc, rfl, rfl⟩
  · have hs' : (x.state == .copying || x.state == .cancelling) = true := by
      rcases hs with hs | hs <;> simp [hs]
    have hx : ({ x with pending := none, state := .done } : Cabi.End) = delivered x .done := by
      cases x; simp_all [delivered]
    simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst, Cabi.check, hb,
      bind, Except.bind, pure, Except.pure, ← hx]
    rcases hs with hs | hs <;> simp [hs]
  · simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst, ho, hd, Cabi.check,
      delivered, bind, Except.bind, pure, Except.pure]
  · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
    simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst, ho', hc, Cabi.check,
      delivered, bind, Except.bind, pure, Except.pure]

/-- A successful `future_event` after a value moved: `COMPLETED`. -/
theorem deliverEnd_future_one (st st1 : Cabi.Store α) (e : Nat) (x : Cabi.End)
    (ev : Cabi.EventCode × Nat × Nat) (he : st.ends e = some x) (hst : x.kind.isStream = false)
    (hp : x.pending = some 1) (h : st.deliverEnd e = .ok (st1, ev)) :
    ∃ ns r, FutureOutcome x 1 ns r := by
  have hfail : ∀ why, st.deliverEnd e ≠ .error why := fun why h' => by rw [h'] at h; cases h
  by_cases hs : x.state = .copying ∨ x.state = .cancelling
  · by_cases hb : x.buffer = none
    · exact ⟨.done, .completed, .inl ⟨rfl, hs, hb, rfl, rfl⟩⟩
    · refine absurd ?_ (hfail (.assert "future_event: buffer"))
      rcases hs with hs | hs <;>
        simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst, Cabi.check, hb, hs,
          bind, Except.bind, pure, Except.pure]
  · have hs' : x.state ≠ .copying ∧ x.state ≠ .cancelling := not_or.mp hs
    exact absurd (by
      simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst, Cabi.check, hs'.1,
        hs'.2, bind, Except.bind, pure, Except.pure]) (hfail (.assert "future_event: copying"))

/-- A successful `future_event` with no value moved: `DROPPED` or `CANCELLED`. -/
theorem deliverEnd_future_zero (st st1 : Cabi.Store α) (e : Nat) (x : Cabi.End)
    (ev : Cabi.EventCode × Nat × Nat) (he : st.ends e = some x) (hst : x.kind.isStream = false)
    (hp : x.pending = some 0) (h : st.deliverEnd e = .ok (st1, ev)) :
    ∃ ns r, FutureOutcome x 0 ns r := by
  have hfail : ∀ why, st.deliverEnd e ≠ .error why := fun why h' => by rw [h'] at h; cases h
  by_cases ho : x.other = none
  · by_cases hd : x.state = .done
    · exact absurd (by simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst,
        ho, hd, Cabi.check, bind, Except.bind, pure, Except.pure])
        (hfail (.assert "future_event: done"))
    · exact ⟨.done, .dropped, .inr (.inl ⟨rfl, ho, hd, rfl, rfl⟩)⟩
  · by_cases hc : x.state = .cancelling
    · exact ⟨.idle, .cancelled, .inr (.inr ⟨rfl, ho, hc, rfl, rfl⟩)⟩
    · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
      exact absurd (by simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst,
        ho', hc, Cabi.check, bind, Except.bind, pure, Except.pure])
        (hfail (.assert "future_event: cancelling"))

/-- A successful `future_event` with a recorded progress `p ≤ 1` has one of the three
outcomes. (`FutureEnd.notify` asserts `p ≤ 1`: `Cabi.Store.notify`.) -/
theorem deliverEnd_future_outcome (st st1 : Cabi.Store α) (e p : Nat) (x : Cabi.End)
    (ev : Cabi.EventCode × Nat × Nat) (he : st.ends e = some x) (hst : x.kind.isStream = false)
    (hp : x.pending = some p) (hp1 : p ≤ 1) (h : st.deliverEnd e = .ok (st1, ev)) :
    ∃ ns r, FutureOutcome x p ns r := by
  by_cases h1 : p = 1
  · rw [h1]
    exact deliverEnd_future_one st st1 e x ev he hst (h1 ▸ hp) h
  · have h0 : p = 0 := by omega
    rw [h0]
    exact deliverEnd_future_zero st st1 e x ev he hst (h0 ▸ hp) h

/-- Silmaril's `deliverStep` of a future on the same outcome: the same state and result. -/
theorem deliverStep_future_outcome (x : Cabi.End) (xs : End E) (p : Nat) (ns : Cabi.EndState)
    (r : Cabi.CopyResult) (hout : FutureOutcome x p ns r) (hks : xs.kind.isStream = false)
    (hxo : xs.other = x.other.map EndId.mk) :
    (xs.clearPending.deliverStep p).1.state = stateR ns ∧
      (xs.clearPending.deliverStep p).2.toNat = r.toNat := by
  rcases hout with ⟨rfl, -, -, rfl, rfl⟩ | ⟨rfl, ho, -, rfl, rfl⟩ | ⟨rfl, ho, -, rfl, rfl⟩
  · simp [End.deliverStep, End.clearPending, hks, stateR]; rfl
  · simp [End.deliverStep, End.clearPending, hks, hxo, ho, stateR]; rfl
  · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
    simp [End.deliverStep, End.clearPending, hks, hxo, ho', stateR]; rfl

/-- Silmaril's `takeEvent` of a future end with a pending event, as an equation. -/
theorem takeEvent_future_eq (s : CStore E) (e p : Nat) (xs : End E)
    (hxs : s.end? ⟨e⟩ = some xs) (hxp : xs.common.pending = some (.futureEnd ⟨e⟩ p)) :
    takeEvent ⟨e⟩ s = (setEnd (setEnd s ⟨e⟩ xs.clearPending) ⟨e⟩
      (xs.clearPending.deliverStep p).1, some ⟨xs.kind.eventCode, xs.index.getD 0,
        xs.payload (xs.clearPending.deliverStep p).2 p⟩) := by
  have hxs' : (setEnd s ⟨e⟩ xs.clearPending).end? ⟨e⟩ = some xs.clearPending :=
    end?_setEnd_self hxs _
  simp only [takeEvent, hxs, hxp, deliver, hxs']; rfl

/-- **Delivering a future end's event, in both machines**: the transcription's
`future_event` closure is silmaril's `takeEvent`, with the same event, and the stores stay
related. -/
theorem deliverEnd_sim_future (st st1 : Cabi.Store α) (s : CStore E) (e p : Nat) (x : Cabi.End)
    (ev : Cabi.EventCode × Nat × Nat) (hR : EndsRel st s) (he : st.ends e = some x)
    (hpb : ∀ b, x.buffer = some b → (st.bufs b).isSome) (hst : x.kind.isStream = false)
    (hp : x.pending = some p) (hp1 : p ≤ 1) (h : st.deliverEnd e = .ok (st1, ev)) :
    ∃ s1 ev', takeEvent ⟨e⟩ s = (s1, some ev') ∧ ev'.code.toNat = ev.1.toNat ∧
      ev'.index = ev.2.1 ∧ ev'.payload = ev.2.2 ∧ EndsRel st1 s1 := by
  obtain ⟨xs, hxs, hxk, hxt, hxst, hxo, hxow, hxi, hxp⟩ := view_of st s hR e x he hpb
  have hxp' : xs.common.pending = some (.futureEnd ⟨e⟩ p) := by simp [hxp, hp, pendR, hst]
  have hks : xs.kind.isStream = false := by rw [hxk, isStream_kindR, hst]
  obtain ⟨ns, r, hout⟩ := deliverEnd_future_outcome st st1 e p x ev he hst hp hp1 h
  have hres : (st1, ev) = (st.setEnd e (delivered x ns),
      (x.kind.eventCode, x.index.getD 0, r.toNat)) :=
    Except.ok.inj (h.symm.trans (deliverEnd_future_eq st e p x he hst hp ns r hout))
  obtain ⟨hstate, hres2⟩ := deliverStep_future_outcome x xs p ns r hout hks hxo
  have hpay : xs.payload (xs.clearPending.deliverStep p).2 p = r.toNat := by
    simp only [End.payload, hks, Bool.false_eq_true, ite_false,
      Silmaril.Wasm.Component.AsyncRef.futureCopyPayload]
    exact hres2
  refine ⟨_, _, takeEvent_future_eq s e p xs hxs hxp', ?_, ?_, ?_, ?_⟩
  · rw [(Prod.mk.inj hres).2, hxk, eventCode_kindR]
  · rw [(Prod.mk.inj hres).2, hxi]
  · rw [(Prod.mk.inj hres).2, hpay]
  · show EndsRel st1 _
    rw [(Prod.mk.inj hres).1]
    refine rel_frame st _ s _ e hR rfl (fun c hc => by simp [Cabi.Store.setEnd, Cabi.upd, hc])
      (fun c hc => by rw [end?_setEnd_ne _ _ hc, end?_setEnd_ne _ _ hc]) ?_
    rw [end?_setEnd_self (end?_setEnd_self hxs _)]
    simpa [Cabi.Store.setEnd, Cabi.upd] using view_delivered e x xs p ns hxk hxt hxo hxow hxi hstate
      (st.setEnd e (delivered x ns))

/-! ## `End.forward` -/

theorem notify_hooks (st st1 : Cabi.Store α) (e p : Nat) (h : st.notify e p = .ok st1) :
    st1.hooks = st.hooks := by
  cases he : st.ends e with
  | none => simp [Cabi.Store.notify, Cabi.Store.getEnd, Cabi.need, he, bind, Except.bind] at h
  | some x =>
    simp only [Cabi.Store.notify, Cabi.Store.getEnd, Cabi.need, he, Cabi.check, bind,
      Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · injection h with h; subst h; rfl

theorem join_hooks (st st1 : Cabi.Store α) (w : Cabi.WRef) (v : Option Nat)
    (h : st.join w v = .ok st1) : st1.hooks = st.hooks := by
  unfold Cabi.Store.join at h
  obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨s1, h1, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨s2, h2, h⟩ := Cabi.bind_ok.1 h
  have e1 : s1.hooks = st.hooks := by
    unfold Cabi.Store.leaveSet at h1
    revert h1
    cases st.wsetOf w with
    | none => intro h1; injection h1 with h1; subst h1; rfl
    | some old =>
      intro h1
      obtain ⟨_, -, h1⟩ := Cabi.bind_ok.1 h1
      injection h1 with h1; subst h1; rfl
  have e2 : s2.hooks = s1.hooks := by
    cases w with
    | end_ e =>
      obtain ⟨_, -, h2⟩ := Cabi.bind_ok.1 h2
      injection h2 with h2; subst h2; rfl
    | sub q =>
      obtain ⟨_, -, h2⟩ := Cabi.bind_ok.1 h2
      injection h2 with h2; subst h2; rfl
  have e3 : st1.hooks = s2.hooks := by
    cases v with
    | none => injection h with h; subst h; rfl
    | some n =>
      obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
      injection h with h; subst h; rfl
  rw [e3, e2, e1]

theorem notifyIfIdle_hooks (st st1 : Cabi.Store α) (o : Nat) (y : Cabi.End)
    (h : st.notifyIfIdle o y = .ok st1) : st1.hooks = st.hooks := by
  unfold Cabi.Store.notifyIfIdle at h
  split at h
  · exact notify_hooks _ _ _ _ h
  · injection h with h; subst h; rfl

theorem unlinkPeer_hooks (st st1 : Cabi.Store α) (e : Nat) (x : Cabi.End)
    (h : st.unlinkPeer e x = .ok st1) : st1.hooks = st.hooks := by
  unfold Cabi.Store.unlinkPeer at h
  revert h
  cases x.other with
  | none => intro h; injection h with h; subst h; rfl
  | some o =>
    intro h
    obtain ⟨y, -, h⟩ := Cabi.bind_ok.1 h
    obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
    obtain ⟨s2, h2, h⟩ := Cabi.bind_ok.1 h
    injection h with h; subst h
    have h3 := notifyIfIdle_hooks _ _ _ _ h2
    exact h3

/-- `End.drop` keeps the pumps. -/
theorem dropEnd_hooks (st st1 : Cabi.Store α) (e : Nat) (h : st.dropEnd e = .ok st1) :
    st1.hooks = st.hooks := by
  unfold Cabi.Store.dropEnd at h
  obtain ⟨x, -, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨s1, h1, h⟩ := Cabi.bind_ok.1 h
  obtain ⟨_, -, h⟩ := Cabi.bind_ok.1 h
  rw [join_hooks _ _ _ _ h, unlinkPeer_hooks _ _ _ _ h1]

/-- `dropH` with no pumps hooked to the end is `End.drop`. -/
theorem dropH_eq [Inhabited α] (st : Cabi.Store α) (e n : Nat) (hk : st.hooks e = []) :
    Cabi.Store.dropH (n + 1) st e = st.dropEnd e := by
  simp only [Cabi.Store.dropH]
  cases hd : st.dropEnd e with
  | error err => rfl
  | ok st1 =>
    simp only [bind, Except.bind]
    rw [dropEnd_hooks _ _ _ hd, hk]
    simp [Cabi.Store.runHooks, pure, Except.pure]

/-- `End.drop` keeps every parked buffer present. -/
theorem dropEnd_bufsPresent (st st1 : Cabi.Store α) (e : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (hself : x.other ≠ some e) (hPB : BufsPresent st)
    (h : st.dropEnd e = .ok st1) : BufsPresent st1 := by
  obtain ⟨hb1, hfe, hfr, hfo⟩ := dropEnd_spec st st1 e x he hself h
  intro c z hz b hzb
  rw [hb1]
  by_cases hce : c = e
  · subst hce
    rw [hfe] at hz; injection hz with hz; subst hz
    exact hPB c x he b hzb
  by_cases hco : x.other = some c
  · obtain ⟨y, hy, hy1⟩ := hfo c hco
    rw [hy1] at hz; injection hz with hz; subst hz
    refine hPB c y hy b ?_
    unfold dropPeerC at hzb; split at hzb <;> exact hzb
  · rw [hfr c hce hco] at hz
    exact hPB c z hz b hzb

/-- Silmaril's `forward` in the drop branch. -/
theorem forward_eq_drop (s : CStore E) (src dst : Nat) (x y : Cabi.End) (xs ys : End E)
    (hxs' : s.end? ⟨src⟩ = some xs) (hys' : s.end? ⟨dst⟩ = some ys)
    (hxk : xs.kind = kindR x.kind) (hyk : ys.kind = kindR y.kind)
    (hxo : xs.other = x.other.map EndId.mk) (hyo : ys.other = y.other.map EndId.mk)
    (hk : (kindR x.kind).isReadable = true) (hkd : kindR y.kind = (kindR x.kind).dual)
    (hbr : (x.other == some dst || x.other.isNone || y.other.isNone) = true) :
    forward ⟨src⟩ ⟨dst⟩ s = .ok (dropEnd ⟨dst⟩ (dropEnd ⟨src⟩ s), .none) := by
  have hk' : ¬ (xs.kind.isReadable = false ∨ ys.kind ≠ xs.kind.dual) := by
    rw [hxk, hyk]; simp [hk, hkd]
  unfold forward
  rw [hxs', hys']
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false hk')]
  cases hxo' : x.other with
  | none => simp [hxo, hxo']
  | some w =>
    cases hyo' : y.other with
    | none => simp [hxo, hxo', hyo, hyo']
    | some r =>
      have hw : w = dst := by simpa [hxo', hyo'] using hbr
      simp [hxo, hxo', hyo, hyo', hw]

/-- The transcription's `End.forward` in the drop branch, with no pumps on the two ends: drop
the source, then the destination. -/
theorem forwardEnd_eq_drops [Inhabited α] (st : Cabi.Store α) (src dst : Nat) (x y : Cabi.End)
    (hx : st.ends src = some x) (hy : st.ends dst = some y)
    (hks : st.hooks src = []) (hkd' : st.hooks dst = [])
    (hbr : (x.other == some dst || x.other.isNone || y.other.isNone) = true) :
    st.forwardEnd src dst = (st.dropEnd src >>= fun s1 => s1.dropEnd dst) := by
  unfold Cabi.Store.forwardEnd
  rw [Cabi.Store.getEnd_of _ _ _ hx, Cabi.Store.getEnd_of _ _ _ hy]
  simp only [bind, Except.bind, hbr, ite_true, Cabi.pumpFuel]
  rw [show (64 : Nat) = 63 + 1 from rfl, dropH_eq st src 63 hks]
  cases h1 : st.dropEnd src with
  | error err => rfl
  | ok s1 =>
    have hk1 : s1.hooks dst = [] := by rw [dropEnd_hooks _ _ _ h1]; exact hkd'
    exact dropH_eq s1 dst 63 hk1

/-- After dropping the source, the destination is still there and not linked to itself. -/
theorem dst_after_drop (st s1 : Cabi.Store α) (src dst : Nat) (x y : Cabi.End)
    (hx : st.ends src = some x) (hy : st.ends dst = some y) (hsd : src ≠ dst)
    (hxs : x.other ≠ some src) (hyd : y.other ≠ some dst) (h1 : st.dropEnd src = .ok s1) :
    ∃ y1, s1.ends dst = some y1 ∧ y1.other ≠ some dst := by
  obtain ⟨-, -, hfr, hfo⟩ := dropEnd_spec st s1 src x hx hxs h1
  by_cases hco : x.other = some dst
  · obtain ⟨y', hy', hy1⟩ := hfo dst hco
    have hyy : y' = y := Option.some.inj (hy'.symm.trans hy)
    refine ⟨_, hy1, ?_⟩
    rw [hyy]
    unfold dropPeerC; split <;> simp
  · exact ⟨y, by rw [hfr dst (Ne.symm hsd) hco]; exact hy, hyd⟩

/-- **`End.forward` dropping both ends, in both machines**: when the source is linked to the
destination or a peer is gone, both machines drop the source, then the destination; the
stores stay related. Side conditions: no pumps hooked to the two ends, no self-links, the
source is a readable end and the destination an end of the dual class. -/
theorem forwardEnd_sim_drop [Inhabited α] (st st1 : Cabi.Store α) (s : CStore E) (src dst : Nat)
    (x y : Cabi.End) (hR : EndsRel st s) (hPB : BufsPresent st)
    (hx : st.ends src = some x) (hy : st.ends dst = some y) (hsd : src ≠ dst)
    (hxs : x.other ≠ some src) (hyd : y.other ≠ some dst)
    (hk : (kindR x.kind).isReadable = true) (hkd : kindR y.kind = (kindR x.kind).dual)
    (hks : st.hooks src = []) (hkd' : st.hooks dst = [])
    (hbr : (x.other == some dst || x.other.isNone || y.other.isNone) = true)
    (h : st.forwardEnd src dst = .ok st1) :
    forward ⟨src⟩ ⟨dst⟩ s = .ok (dropEnd ⟨dst⟩ (dropEnd ⟨src⟩ s), .none) ∧
      EndsRel st1 (dropEnd ⟨dst⟩ (dropEnd ⟨src⟩ s)) := by
  obtain ⟨xs, hxs', hxk, -, -, hxo, -, -, -⟩ := view_of st s hR src x hx (hPB src x hx)
  obtain ⟨ys, hys', hyk, -, -, hyo, -, -, -⟩ := view_of st s hR dst y hy (hPB dst y hy)
  refine ⟨forward_eq_drop s src dst x y xs ys hxs' hys' hxk hyk hxo hyo hk hkd hbr, ?_⟩
  obtain ⟨s1, h1, h2⟩ := Cabi.bind_ok.1
    ((forwardEnd_eq_drops st src dst x y hx hy hks hkd' hbr).symm.trans h)
  have hR1 : EndsRel s1 (dropEnd ⟨src⟩ s) := dropEnd_sim st s1 s src x hR hPB hx hxs h1
  have hPB1 : BufsPresent s1 := dropEnd_bufsPresent st s1 src x hx hxs hPB h1
  obtain ⟨y1, hy1, hy1o⟩ := dst_after_drop st s1 src dst x y hx hy hsd hxs hyd h1
  exact dropEnd_sim s1 st1 (dropEnd ⟨src⟩ s) dst y1 hR1 hPB1 hy1 hy1o h2

/-- The transcription's splice branch of `End.forward` when not both peers have a parked
buffer: the peers are linked to each other; nothing else changes. -/
theorem forwardEnd_splice_eq [Inhabited α] (st : Cabi.Store α) (src dst w r : Nat) (x y yw yr : Cabi.End)
    (hx : st.ends src = some x) (hy : st.ends dst = some y) (hxo : x.other = some w)
    (hyo : y.other = some r) (hwd : w ≠ dst) (hwr : w ≠ r)
    (hyw : st.ends w = some yw) (hyr : st.ends r = some yr)
    (hnb : yw.buffer = none ∨ yr.buffer = none) :
    st.forwardEnd src dst = .ok ((st.setEnd w { yw with other := some r }).setEnd r
      { yr with other := some w }) := by
  have hbr : (x.other == some dst || x.other.isNone || y.other.isNone) = false := by
    simp [hxo, hyo, hwd]
  unfold Cabi.Store.forwardEnd
  rw [Cabi.Store.getEnd_of _ _ _ hx, Cabi.Store.getEnd_of _ _ _ hy]
  simp only [bind, Except.bind, hxo, hyo, Cabi.need, pure,
    Except.pure, Cabi.Store.getEnd_of _ _ _ hyw]
  rw [Cabi.Store.getEnd_of (st.setEnd w { yw with other := some r }) r yr
    (by simp [Cabi.Store.setEnd, Cabi.upd, Ne.symm hwr, hyr])]
  simp only []
  rw [Cabi.Store.getEnd_of _ w { yw with other := some r }
      (by simp [Cabi.Store.setEnd, Cabi.upd, hwr]),
    Cabi.Store.getEnd_of _ r { yr with other := some w } (by simp [Cabi.Store.setEnd, Cabi.upd])]
  rcases hnb with hb | hb
  · simp [hb, hwd]
  · cases yw.buffer <;> simp [hb, hwd]

/-- A peer that silmaril sees parked is parked in the transcription. -/
theorem parked_of_view (st : Cabi.Store α) (s : CStore E) (w : Nat) (yw : Cabi.End) (zw : End E)
    (hR : EndsRel st s) (hzw : s.end? ⟨w⟩ = some zw) (hyw : st.ends w = some yw) (b : BufferDesc E)
    (hb : zw.buffer = some b) : yw.buffer ≠ none := by
  intro hn
  have h' : (s.end? ⟨w⟩).map viewS = (st.ends w).bind (viewC st w) := hR w
  rw [hzw, hyw] at h'
  simp [viewC, hn, viewS, hb] at h'

/-- Distinct ids are distinct ends. -/
theorem endId_ne {a b : Nat} (h : a ≠ b) : (⟨a⟩ : EndId) ≠ ⟨b⟩ := fun h' => h (EndId.mk.inj h')

/-- Silmaril's `forward` in the splice branch when not both peers have a parked buffer: the
forwarded ends are unlinked and the peers linked to each other. -/
theorem forward_eq_splice (s : CStore E) (src dst w r : Nat) (xs ys zw zr : End E)
    (hxs' : s.end? ⟨src⟩ = some xs) (hys' : s.end? ⟨dst⟩ = some ys)
    (hzw : s.end? ⟨w⟩ = some zw) (hzr : s.end? ⟨r⟩ = some zr)
    (hk' : ¬ (xs.kind.isReadable = false ∨ ys.kind ≠ xs.kind.dual))
    (hxso : xs.other = some ⟨w⟩) (hyso : ys.other = some ⟨r⟩) (hwd : w ≠ dst) (hrs : r ≠ src)
    (hws : w ≠ src) (hrd : r ≠ dst) (hwr : w ≠ r) (hnb : zw.buffer = none ∨ zr.buffer = none) :
    forward ⟨src⟩ ⟨dst⟩ s = .ok (setEnd (setEnd (setEnd (setEnd s ⟨src⟩ { xs with other := none })
      ⟨dst⟩ { ys with other := none }) ⟨w⟩ { zw with other := some ⟨r⟩ }) ⟨r⟩
      { zr with other := some ⟨w⟩ }, .none) := by
  unfold forward
  rw [hxs', hys']
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false hk')]
  simp only [hxso, hyso]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [hwd])),
    ite_eq_right_of_eq_false _ _ (eq_false (by simp [hrs, hws, hrd, hwr]))]
  rw [hzw, hzr]
  dsimp only
  rcases hnb with hb | hb
  · simp [hb]
  · cases zw.buffer <;> simp [hb]

/-- The splice keeps the relation at every end but the two forwarded ones. -/
theorem splice_except (st : Cabi.Store α) (s : CStore E) (src dst w r : Nat) (yw yr : Cabi.End)
    (xs ys zw zr : End E) (hR : EndsRel st s) (hzw : s.end? ⟨w⟩ = some zw) (hzr : s.end? ⟨r⟩ = some zr)
    (hw : some (viewS { zw with other := some ⟨r⟩ }) = viewC ((st.setEnd w
      { yw with other := some r }).setEnd r { yr with other := some w }) w { yw with other := some r })
    (hr : some (viewS { zr with other := some ⟨w⟩ }) = viewC ((st.setEnd w
      { yw with other := some r }).setEnd r { yr with other := some w }) r { yr with other := some w })
    (hwd : w ≠ dst) (hrs : r ≠ src) (hws : w ≠ src) (hrd : r ≠ dst) (hwr : w ≠ r) :
    EndsRelExcept src dst ((st.setEnd w { yw with other := some r }).setEnd r
      { yr with other := some w }) (setEnd (setEnd (setEnd (setEnd s ⟨src⟩
        { xs with other := none }) ⟨dst⟩ { ys with other := none }) ⟨w⟩
        { zw with other := some ⟨r⟩ }) ⟨r⟩ { zr with other := some ⟨w⟩ }) := by
  intro c ⟨hcs, hcd⟩
  by_cases hcr : c = r
  · rw [hcr, end?_setEnd_self (by rw [end?_setEnd_ne _ _ (endId_ne (Ne.symm hwr)),
      end?_setEnd_ne _ _ (endId_ne hrd), end?_setEnd_ne _ _ (endId_ne hrs)]; exact hzr)]
    rw [show ((st.setEnd w { yw with other := some r }).setEnd r
      { yr with other := some w }).ends r = some { yr with other := some w } by
        simp [Cabi.Store.setEnd, Cabi.upd]]
    exact hr
  by_cases hcw : c = w
  · rw [hcw, end?_setEnd_ne _ _ (endId_ne hwr), end?_setEnd_self (by
      rw [end?_setEnd_ne _ _ (endId_ne hwd), end?_setEnd_ne _ _ (endId_ne hws)]; exact hzw)]
    rw [show ((st.setEnd w { yw with other := some r }).setEnd r
      { yr with other := some w }).ends w = some { yw with other := some r } by
        simp [Cabi.Store.setEnd, Cabi.upd, hwr]]
    exact hw
  rw [end?_setEnd_ne _ _ (endId_ne hcr), end?_setEnd_ne _ _ (endId_ne hcw),
    end?_setEnd_ne _ _ (endId_ne hcd), end?_setEnd_ne _ _ (endId_ne hcs), hR c]
  simp only [Cabi.Store.setEnd, Cabi.upd, hcr, hcw, ite_false]
  cases st.ends c with
  | none => rfl
  | some z => exact (viewC_congr st _ c z (fun _ _ => rfl)).symm

/-- The splice does not keep the relation at the source: silmaril unlinks it, the
transcription does not. -/
theorem splice_not_rel (st st1 : Cabi.Store α) (s s1 : CStore E) (src w : Nat) (x : Cabi.End)
    (xs : End E) (hR : EndsRel st s) (hx : st.ends src = some x) (hxs' : s.end? ⟨src⟩ = some xs)
    (hxso : xs.other = x.other.map EndId.mk) (hxo : x.other = some w)
    (hb1 : st1.bufs = st.bufs) (hst : st1.ends src = some x)
    (h1s : s1.end? ⟨src⟩ = some { xs with other := none }) : ¬ EndsRel st1 s1 := by
  intro hall
  have h' : some (viewS { xs with other := none }) = viewC st1 src x := by
    simpa [h1s, hst] using hall src
  have hcg : (viewC st1 src x : Option (View E)) = viewC st src x :=
    viewC_congr _ _ _ _ (fun _ _ => by rw [hb1])
  have h0 : some (viewS xs) = viewC st src x := by simpa [hxs', hx] using hR src
  have h2 : some (viewS { xs with other := none }) = some (viewS xs) := h'.trans (hcg.trans h0.symm)
  have h3 := congrArg (Option.map View.other) h2
  simp [viewS, hxso, hxo] at h3

/-- **`End.forward` splicing the peers, in both machines** (when not both peers have a parked
buffer): silmaril's `forward` takes the splice branch and the stores stay related **except at
the two forwarded ends**, and they are **not** related at them: silmaril unlinks the forwarded
ends, the transcription (like `definitions.py`) leaves them pointing at their old peers. -/
theorem forwardEnd_sim_splice [Inhabited α] (st st1 : Cabi.Store α) (s : CStore E)
    (src dst w r : Nat) (x y yw yr : Cabi.End) (hR : EndsRel st s) (hPB : BufsPresent st)
    (hx : st.ends src = some x) (hy : st.ends dst = some y) (hxo : x.other = some w)
    (hyo : y.other = some r) (hwd : w ≠ dst) (hrs : r ≠ src) (hws : w ≠ src) (hrd : r ≠ dst)
    (hwr : w ≠ r) (hsd : src ≠ dst)
    (hyw : st.ends w = some yw) (hyr : st.ends r = some yr)
    (hnb : yw.buffer = none ∨ yr.buffer = none)
    (hk : (kindR x.kind).isReadable = true) (hkd : kindR y.kind = (kindR x.kind).dual)
    (h : st.forwardEnd src dst = .ok st1) :
    ∃ s1, forward ⟨src⟩ ⟨dst⟩ s = .ok (s1, .none) ∧ EndsRelExcept src dst st1 s1 ∧
      ¬ EndsRel st1 s1 := by
  have hst1 : st1 = (st.setEnd w { yw with other := some r }).setEnd r { yr with other := some w } :=
    Except.ok.inj (h.symm.trans (forwardEnd_splice_eq st src dst w r x y yw yr hx hy hxo hyo hwd
      hwr hyw hyr hnb))
  obtain ⟨xs, hxs', hxk, -, -, hxso, -, -, -⟩ := view_of st s hR src x hx (hPB src x hx)
  obtain ⟨ys, hys', hyk, -, -, hyso, -, -, -⟩ := view_of st s hR dst y hy (hPB dst y hy)
  obtain ⟨zw, hzw, hzwk, hzwt, hzwst, -, hzwow, hzwi, hzwp⟩ := view_of st s hR w yw hyw (hPB w yw hyw)
  obtain ⟨zr, hzr, hzrk, hzrt, hzrst, -, hzrow, hzri, hzrp⟩ := view_of st s hR r yr hyr (hPB r yr hyr)
  have hnb' : zw.buffer = none ∨ zr.buffer = none := by
    rcases hnb with hb | hb
    · exact .inl (Option.eq_none_iff_forall_not_mem.mpr fun b hz => parked_of_view st s w yw zw hR hzw hyw b hz hb)
    · exact .inr (Option.eq_none_iff_forall_not_mem.mpr fun b hz => parked_of_view st s r yr zr hR hzr hyr b hz hb)
  have hk' : ¬ (xs.kind.isReadable = false ∨ ys.kind ≠ xs.kind.dual) := by
    rw [hxk, hyk]; simp [hk, hkd]
  refine ⟨_, forward_eq_splice s src dst w r xs ys zw zr hxs' hys' hzw hzr hk'
    (by simp [hxso, hxo]) (by simp [hyso, hyo]) hwd hrs hws hrd hwr hnb', ?_, ?_⟩
  · rw [hst1]
    exact splice_except st s src dst w r yw yr xs ys zw zr hR hzw hzr
      (rel_at st _ s w yw _ zw _ hR hzw hyw rfl rfl rfl hzwk hzwt hzwst (by simp) hzwow hzwi hzwp)
      (rel_at st _ s r yr _ zr _ hR hzr hyr rfl rfl rfl hzrk hzrt hzrst (by simp) hzrow hzri hzrp)
      hwd hrs hws hrd hwr
  · refine splice_not_rel st st1 s _ src w x xs hR hx hxs' hxso hxo (by rw [hst1]; rfl)
      (by rw [hst1]; simp [Cabi.Store.setEnd, Cabi.upd, Ne.symm hrs, Ne.symm hws, hx]) ?_
    rw [end?_setEnd_ne _ _ (endId_ne (Ne.symm hrs)), end?_setEnd_ne _ _ (endId_ne (Ne.symm hws)),
      end?_setEnd_ne _ _ (endId_ne hsd), end?_setEnd_self hxs']

end Silmaril.Wasm.Component.Async.CabiRef
