module

public import Silmaril.Wasm.Component.Async.CabiRef.Defs
public import Silmaril.Wasm.Component.Async.CabiCopy.Thms
import Silmaril.Raw.Wasm.Component.Reference

@[expose] public section

/-!
# The transcription simulates silmaril's end state machine

PROVED, for every pair of stores related by `EndsRel` (every end has the same `View`):

* `copyEnd_sim_park`: `End.copy` towards a peer with no parked buffer (case 2): both machines
  park the buffer; the stores stay related.
* `copyEnd_sim_transfer`: `End.copy` meeting the peer's parked buffer with room on both sides
  (case 3, with the move of `n = min` elements and both notifications, and the peer's buffer
  unparked exactly when full): silmaril's `copyCore` succeeds and the stores stay related.
  Side conditions: no end parks the new buffer, no two ends park the same buffer
  (`BufsDistinct`), the copy does not trap (`copy to self`), and the buffer that is read holds
  its values.
* `deliverEnd_sim_stream`: delivering a stream end's pending event (the `stream_event`
  closure: `DROPPED` if the peer is gone, else `CANCELLED` or `COMPLETED`, with the progress
  recorded at `notify`) is silmaril's `takeEvent`, with the same event code, index and payload;
  the stores stay related.

So on these steps the transcription at `d095e2f` and silmaril's machine at `a25fc0b` agree,
which confirms (on this fragment) that no async state machine changed between the revisions.

NOT PROVED here: zero-length copies (cases 4 and 5), a copy towards a dropped peer (case 1),
`End.cancel`, `End.drop`, `End.forward`, future events, and the layers above the end state
machine (tasks, threads, waitable sets, the canon built-ins); see
`tools/wasm-tools/README.md`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.CabiRef

open Silmaril.Wasm.Component.Runtime

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {α : Type}

theorem isReadable_kindR (k : Cabi.EndKind) : (kindR k).isReadable = k.isReadable := by
  cases k <;> rfl
theorem isStream_kindR (k : Cabi.EndKind) : (kindR k).isStream = k.isStream := by
  cases k <;> rfl
theorem noneOrNumber_tyR (t : Cabi.Ty) :
    Silmaril.Wasm.Component.ABI.noneOrNumberType (tyR t) = t.noneOrNumber := by
  rcases t with ⟨_, k⟩; cases k <;> rfl
theorem remain_bufR (b : Nat) (x : Cabi.Buf α) : (bufR b x : BufferDesc E).remain = x.remain := rfl
theorem progress_bufR (b : Nat) (x : Cabi.Buf α) : (bufR b x : BufferDesc E).progress = x.progress := rfl

/-- The view of an end without a parked buffer. -/
theorem view_of_unparked (st : Cabi.Store α) (s : CStore E) (hR : EndsRel st s) (e : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (hxb : x.buffer = none) :
    ∃ xs, s.end? ⟨e⟩ = some xs ∧ xs.kind = kindR x.kind ∧ xs.t = tyR x.t ∧
      xs.state = stateR x.state ∧ xs.other = x.other.map EndId.mk ∧ xs.buffer = none ∧
      xs.owner = x.owner.map InstId.mk ∧ xs.index = x.index ∧ xs.common.pending = pendR x.kind e x.pending := by
  have h := hR e
  rw [he] at h
  simp only [Option.bind_some, viewC, hxb] at h
  obtain ⟨xs, hxs, hv⟩ := Option.map_eq_some_iff.1 h
  simp only [viewS, View.mk.injEq] at hv
  exact ⟨xs, hxs, hv⟩


/-- The view of an end with a parked buffer. -/
theorem view_of_parked (st : Cabi.Store α) (s : CStore E) (hR : EndsRel st s) (e : Nat) (x : Cabi.End)
    (b : Nat) (bx : Cabi.Buf α) (he : st.ends e = some x) (hxb : x.buffer = some b) (hb : st.bufs b = some bx) :
    ∃ xs, s.end? ⟨e⟩ = some xs ∧ xs.kind = kindR x.kind ∧ xs.t = tyR x.t ∧
      xs.state = stateR x.state ∧ xs.other = x.other.map EndId.mk ∧ xs.buffer = some (bufR b bx) ∧
      xs.owner = x.owner.map InstId.mk ∧ xs.index = x.index ∧ xs.common.pending = pendR x.kind e x.pending := by
  have h := hR e
  rw [he] at h
  simp only [Option.bind_some, viewC, hxb, hb, Option.map_some] at h
  obtain ⟨xs, hxs, hv⟩ := Option.map_eq_some_iff.1 h
  simp only [viewS, View.mk.injEq] at hv
  exact ⟨xs, hxs, hv⟩

/-- `copyCore` case 3, by views. -/
theorem copyCore_meets_parked (s : CStore E) (e o : EndId) (xs ys : End E) (buf ob : BufferDesc E)
    (isRead : Bool) (hxs : s.end? e = some xs) (hr : isRead = xs.kind.isReadable)
    (hxo : xs.other = some o) (hoe : o ≠ e) (hys : s.end? o = some ys) (hyb : ys.buffer = some ob)
    (hpos : 0 < buf.remain) (hpos' : 0 < ob.remain)
    (htrap : ¬ (xs.owner.isSome ∧ xs.owner = ys.owner ∧
      Silmaril.Wasm.Component.ABI.noneOrNumberType xs.t = false)) :
    ∃ s1 a, copyCore e buf isRead s = .ok (s1, a) ∧ (∀ c, c ≠ e → c ≠ o → s1.end? c = s.end? c) ∧
      (s1.end? e).map viewS = some ⟨xs.kind, xs.t, .copying, xs.other, xs.buffer, xs.owner,
        xs.index, some (xs.pendingFor e (buf.progress + min buf.remain ob.remain))⟩ ∧
      (s1.end? o).map viewS = some ⟨ys.kind, ys.t, ys.state, ys.other,
        if ob.remain - min buf.remain ob.remain = 0 then none
        else some (ob.advance (min buf.remain ob.remain)), ys.owner, ys.index,
        some (ys.pendingFor o (ob.progress + min buf.remain ob.remain))⟩ := by
  have hoe' : e ≠ o := Ne.symm hoe
  have htr : ¬ (0 < buf.remain ∧ 0 < ob.remain → False) := fun h => h ⟨hpos, hpos'⟩
  have hc : copyCore e buf isRead s = .ok (setEnd (setEnd s e
      ({ xs with state := .copying }.withNotify e (buf.advance (min buf.remain ob.remain)).progress)) o
      { ys.withNotify o (ob.advance (min buf.remain ob.remain)).progress with
        buffer := if (ob.advance (min buf.remain ob.remain)).remain = 0 then none
          else some (ob.advance (min buf.remain ob.remain)) },
      if isRead then .transfer o e (min buf.remain ob.remain) ob buf
      else .transfer e o (min buf.remain ob.remain) buf ob) := by
    simp [copyCore, hxs, hr, hxo, hoe, hys, hyb, hpos, hpos', htrap]
  refine ⟨_, _, hc, fun c hce hco => ?_, ?_, ?_⟩
  · rw [end?_setEnd_ne _ _ hco, end?_setEnd_ne _ _ hce]
  · rw [end?_setEnd_ne _ _ hoe', end?_setEnd_self hxs]
    simp [viewS, End.withNotify, End.pendingFor]
  · rw [end?_setEnd_self (by rw [end?_setEnd_ne _ _ hoe]; exact hys)]
    simp [viewS, End.withNotify, End.pendingFor, BufferDesc.remain_advance, BufferDesc.progress_advance]

/-- The view of an end depends on the buffers only through its parked buffer. -/
theorem viewC_congr (st st1 : Cabi.Store α) (e : Nat) (z : Cabi.End)
    (hb : ∀ bz, z.buffer = some bz → st1.bufs bz = st.bufs bz) :
    (viewC st1 e z : Option (View E)) = viewC st e z := by
  unfold viewC
  split
  · rfl
  · next bz hbz => rw [hb bz hbz]

theorem pendR_some (k : Cabi.EndKind) (e p : Nat) (xs : End E) (hk : xs.kind = kindR k) :
    some (xs.pendingFor ⟨e⟩ p) = pendR k e (some p) := by
  simp [pendR, End.pendingFor, hk, isStream_kindR]

/-- **`End.copy` meeting a parked buffer, in both machines**: the transcription's case 3 is
silmaril's `copyCore` case 3, and the stores stay related. -/
theorem copyEnd_sim_transfer [Inhabited α] (st st1 : Cabi.Store α) (s : CStore E) (e b o ob : Nat)
    (x y : Cabi.End) (bx obx : Cabi.Buf α)
    (hR : EndsRel st s) (hD : BufsDistinct st)
    (hfresh : ∀ c z, st.ends c = some z → z.buffer ≠ some b)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx) (hbo : b ≠ ob)
    (htrap : (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) = false)
    (hpos : 0 < bx.remain) (hpos' : 0 < obx.remain)
    (hwf : (if x.kind.isReadable then obx else bx).ReadOk)
    (h : st.copyEnd e b = .ok st1) :
    ∃ s1 a, copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (s1, a) ∧ EndsRel st1 s1 := by
  obtain ⟨-, hfr, hfe, hfo, hbufs, obx', hobx', hop, hol⟩ := Cabi.Store.copyEnd_transfer st st1 e b o
    ob x y bx obx he hxb hxo hoe ho hyb hb hob hbo htrap hpos hpos' hwf h
  obtain ⟨xs, hxs, hxk, hxt, -, hxso, hxsb, hxow, hxi, -⟩ := view_of_unparked st s hR e x he hxb
  obtain ⟨ys, hys, hyk, hyt, hyst, hyo, hysb, hyow, hyi, hyp⟩ :=
    view_of_parked st s hR o y ob obx ho hyb hob
  have hoe' : (⟨o⟩ : EndId) ≠ ⟨e⟩ := fun h' => hoe (EndId.mk.inj h')
  have htrap' : ¬ (xs.owner.isSome ∧ xs.owner = ys.owner ∧
      Silmaril.Wasm.Component.ABI.noneOrNumberType xs.t = false) := by
    rw [hxow, hyow, hxt, noneOrNumber_tyR]
    intro ⟨h1, h2, h3⟩
    have h2' : x.owner = y.owner := Option.map_injective (fun _ _ h => InstId.mk.inj h) h2
    simp_all
  obtain ⟨s1, a, hc, hsfr, hse, hso⟩ := copyCore_meets_parked s ⟨e⟩ ⟨o⟩ xs ys (bufR b bx)
    (bufR ob obx) x.kind.isReadable hxs (by rw [hxk, isReadable_kindR]) (by rw [hxso, hxo]; rfl)
    hoe' hys hysb hpos hpos' htrap'
  refine ⟨s1, a, hc, fun c => ?_⟩
  show (s1.end? ⟨c⟩).map viewS = (st1.ends c).bind (viewC st1 c)
  by_cases hce : c = e
  · rw [hce, hse, hfe]
    simp [viewC, Cabi.End.withPending, Cabi.End.withState, hxb, hxk, hxt, hxso, hxsb, hxow, hxi, stateR,
      pendR_some _ _ _ xs hxk, progress_bufR, remain_bufR]
  by_cases hco : c = o
  · rw [hco, hso, hfo]
    by_cases h0 : obx.remain - min bx.remain obx.remain = 0
    · simp [viewC, Cabi.End.withPending, Cabi.End.withBuffer, h0, hyk, hyt, hyst, hyo, hyow, hyi,
        pendR_some _ _ _ ys hyk, remain_bufR, progress_bufR]
    · have hadv : (bufR ob obx : BufferDesc E).advance (min bx.remain obx.remain) = bufR ob obx' := by
        simp [bufR, BufferDesc.advance, hop, hol]
      simp [viewC, Cabi.End.withPending, Cabi.End.withBuffer, h0, hyk, hyt, hyst, hyo, hyow, hyi,
        pendR_some _ _ _ ys hyk, remain_bufR, progress_bufR, hobx', hadv]
  have hc' : (⟨c⟩ : EndId) ≠ ⟨e⟩ := fun h' => hce (EndId.mk.inj h')
  have hco' : (⟨c⟩ : EndId) ≠ ⟨o⟩ := fun h' => hco (EndId.mk.inj h')
  rw [hsfr ⟨c⟩ hc' hco', hfr c hce hco, hR c]
  cases hz : st.ends c with
  | none => rfl
  | some z =>
    have hzb : ∀ bz, z.buffer = some bz → st1.bufs bz = st.bufs bz := fun bz hbz =>
      hbufs bz (fun h' => hfresh c z hz (h' ▸ hbz))
        (fun h' => hco (hD c o z y bz hz ho hbz (h' ▸ hyb)))
    exact (viewC_congr st st1 c z hzb).symm

/-- The view of an end whose parked buffer (if any) exists. -/
theorem view_of (st : Cabi.Store α) (s : CStore E) (hR : EndsRel st s) (e : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (hpb : ∀ b, x.buffer = some b → (st.bufs b).isSome) :
    ∃ xs, s.end? ⟨e⟩ = some xs ∧ xs.kind = kindR x.kind ∧ xs.t = tyR x.t ∧
      xs.state = stateR x.state ∧ xs.other = x.other.map EndId.mk ∧
      xs.owner = x.owner.map InstId.mk ∧ xs.index = x.index ∧
      xs.common.pending = pendR x.kind e x.pending := by
  cases hxb : x.buffer with
  | none =>
    obtain ⟨xs, hxs, h1, h2, h3, h4, -, h6, h7, h8⟩ := view_of_unparked st s hR e x he hxb
    exact ⟨xs, hxs, h1, h2, h3, h4, h6, h7, h8⟩
  | some b =>
    obtain ⟨bx, hbx⟩ : ∃ bx, st.bufs b = some bx := Option.isSome_iff_exists.1 (hpb b hxb)
    obtain ⟨xs, hxs, h1, h2, h3, h4, -, h6, h7, h8⟩ := view_of_parked st s hR e x b bx he hxb hbx
    exact ⟨xs, hxs, h1, h2, h3, h4, h6, h7, h8⟩

/-- `result | progress << 4` as a sum. -/
theorem packStreamCopyResult_eq (r : Silmaril.Wasm.Component.AsyncRef.CopyResult) (p : Nat) :
    Silmaril.Wasm.Component.AsyncRef.packStreamCopyResult r p = r.toNat + 16 * p := by
  have hr : r.toNat < 2 ^ 4 := by cases r <;> decide
  rw [Silmaril.Wasm.Component.AsyncRef.packStreamCopyResult, Silmaril.Wasm.Component.AsyncRef.packLow4,
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hr, Nat.shiftLeft_eq]
  omega

/-- The event codes agree. -/
theorem eventCode_kindR (k : Cabi.EndKind) : (kindR k).eventCode.toNat = k.eventCode.toNat := by
  cases k <;> rfl


/-- What a delivery leaves alone. -/
theorem deliverStep_keeps (x : End E) (p : Nat) :
    (x.deliverStep p).1.t = x.t ∧ (x.deliverStep p).1.owner = x.owner ∧
      (x.deliverStep p).1.index = x.index ∧ (x.deliverStep p).1.common = x.common := by
  unfold End.deliverStep; split
  · split <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Updating one end keeps the relation at the other ends. -/
theorem rel_frame (st st1 : Cabi.Store α) (s s1 : CStore E) (e : Nat) (hR : EndsRel st s)
    (hb : st1.bufs = st.bufs) (hst : ∀ c, c ≠ e → st1.ends c = st.ends c)
    (hs : ∀ c : EndId, c ≠ ⟨e⟩ → s1.end? c = s.end? c) (he : (s1.end? ⟨e⟩).map viewS =
      (st1.ends e).bind (viewC st1 e)) : EndsRel st1 s1 := by
  intro c
  by_cases hce : c = e
  · rw [hce]; exact he
  · have hc' : (⟨c⟩ : EndId) ≠ ⟨e⟩ := fun h' => hce (EndId.mk.inj h')
    rw [hs _ hc', hst c hce, hR c]
    cases st.ends c with
    | none => rfl
    | some z => exact (viewC_congr st st1 c z (fun bz _ => by rw [hb])).symm

/-- The transcription's `stream_event`, as an equation. -/
theorem deliverEnd_stream_eq (st : Cabi.Store α) (e p : Nat) (x : Cabi.End)
    (he : st.ends e = some x) (hst : x.kind.isStream = true) (hp : x.pending = some p)
    (ns : Cabi.EndState) (r : Cabi.CopyResult) (hout : StreamOutcome x ns r) :
    st.deliverEnd e = .ok (st.setEnd e (delivered x ns),
      (x.kind.eventCode, x.index.getD 0, r.toNat + 16 * p)) := by
  rcases hout with ⟨ho, hd, rfl, rfl⟩ | ⟨ho, hc, rfl, rfl⟩ | ⟨ho, hc, rfl, rfl⟩
  · simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst, ho, hd, Cabi.check,
      delivered, bind, Except.bind, pure, Except.pure]
  · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
    simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst, ho', hc,
      delivered, bind, Except.bind, pure, Except.pure]
  · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
    simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst, ho', hc, Cabi.check,
      delivered, bind, Except.bind, pure, Except.pure]

/-- A successful `stream_event` has one of the three outcomes. -/
theorem deliverEnd_stream_outcome (st st1 : Cabi.Store α) (e p : Nat) (x : Cabi.End)
    (ev : Cabi.EventCode × Nat × Nat) (he : st.ends e = some x) (hst : x.kind.isStream = true)
    (hp : x.pending = some p) (h : st.deliverEnd e = .ok (st1, ev)) :
    ∃ ns r, StreamOutcome x ns r := by
  have hfail : ∀ why, st.deliverEnd e ≠ .error why := fun why h' => by rw [h'] at h; cases h
  by_cases ho : x.other = none
  · by_cases hd : x.state = .done
    · exact absurd (by simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst,
        ho, hd, Cabi.check, bind, Except.bind, pure, Except.pure])
        (hfail (.assert "stream_event: done"))
    · exact ⟨.done, .dropped, .inl ⟨ho, hd, rfl, rfl⟩⟩
  · by_cases hc : x.state = .cancelling
    · exact ⟨.idle, .cancelled, .inr (.inl ⟨ho, hc, rfl, rfl⟩)⟩
    · by_cases hcp : x.state = .copying
      · exact ⟨.idle, .completed, .inr (.inr ⟨ho, hcp, rfl, rfl⟩)⟩
      · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
        exact absurd (by simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, hst,
          ho', hc, hcp, Cabi.check, bind, Except.bind, pure, Except.pure])
          (hfail (.assert "stream_event: copying"))

/-- Silmaril's `deliverStep` on the same outcome: the same state and copy result. -/
theorem deliverStep_outcome (x : Cabi.End) (xs : End E) (p : Nat) (ns : Cabi.EndState)
    (r : Cabi.CopyResult) (hout : StreamOutcome x ns r) (hks : xs.kind.isStream = true)
    (hxo : xs.other = x.other.map EndId.mk) (hxst : xs.state = stateR x.state) :
    (xs.clearPending.deliverStep p).1.state = stateR ns ∧
      (xs.clearPending.deliverStep p).2.toNat = r.toNat := by
  rcases hout with ⟨ho, -, rfl, rfl⟩ | ⟨ho, hc, rfl, rfl⟩ | ⟨ho, hc, rfl, rfl⟩
  · simp [End.deliverStep, End.clearPending, hks, hxo, ho, stateR]; rfl
  · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
    simp [End.deliverStep, End.clearPending, hks, hxo, ho', hxst, hc, stateR]; rfl
  · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
    simp [End.deliverStep, End.clearPending, hks, hxo, ho', hxst, hc, stateR]; rfl

/-- Silmaril's `takeEvent` of a stream end with a pending event, as an equation. -/
theorem takeEvent_stream_eq (s : CStore E) (e p : Nat) (xs : End E)
    (hxs : s.end? ⟨e⟩ = some xs) (hxp : xs.common.pending = some (.streamEnd ⟨e⟩ p)) :
    takeEvent ⟨e⟩ s = (setEnd (setEnd s ⟨e⟩ xs.clearPending) ⟨e⟩
      (xs.clearPending.deliverStep p).1, some ⟨xs.kind.eventCode, xs.index.getD 0,
        xs.payload (xs.clearPending.deliverStep p).2 p⟩) := by
  have hxs' : (setEnd s ⟨e⟩ xs.clearPending).end? ⟨e⟩ = some xs.clearPending :=
    end?_setEnd_self hxs _
  simp only [takeEvent, hxs, hxp, deliver, hxs']; rfl

/-- The view of a delivered end. -/
theorem view_delivered (e : Nat) (x : Cabi.End) (xs : End E) (p : Nat) (ns : Cabi.EndState)
    (hxk : xs.kind = kindR x.kind) (hxt : xs.t = tyR x.t) (hxo : xs.other = x.other.map EndId.mk)
    (hxow : xs.owner = x.owner.map InstId.mk) (hxi : xs.index = x.index)
    (hstate : (xs.clearPending.deliverStep p).1.state = stateR ns) (st : Cabi.Store α) :
    some (viewS (xs.clearPending.deliverStep p).1) = viewC st e (delivered x ns) := by
  obtain ⟨hkt, hko, hki, hkc⟩ := deliverStep_keeps xs.clearPending p
  have hcommon : (xs.clearPending.deliverStep p).1.common.pending = none := by rw [hkc]; rfl
  simp [viewS, viewC, delivered, End.deliverStep_kind, End.deliverStep_other,
    End.deliverStep_buffer, hstate, hcommon, hxk, hxt, hxo, hxow, hxi, pendR, hkt, hko, hki,
    show xs.clearPending.t = xs.t from rfl, show xs.clearPending.owner = xs.owner from rfl,
    show xs.clearPending.index = xs.index from rfl]

/-- **Delivering a stream end's event, in both machines**: the transcription's
`stream_event` closure is silmaril's `takeEvent`, with the same event, and the stores stay
related. -/
theorem deliverEnd_sim_stream (st st1 : Cabi.Store α) (s : CStore E) (e : Nat) (x : Cabi.End)
    (ev : Cabi.EventCode × Nat × Nat) (hR : EndsRel st s) (he : st.ends e = some x)
    (hpb : ∀ b, x.buffer = some b → (st.bufs b).isSome) (hst : x.kind.isStream = true)
    (h : st.deliverEnd e = .ok (st1, ev)) :
    ∃ s1 ev', takeEvent ⟨e⟩ s = (s1, some ev') ∧ ev'.code.toNat = ev.1.toNat ∧
      ev'.index = ev.2.1 ∧ ev'.payload = ev.2.2 ∧ EndsRel st1 s1 := by
  obtain ⟨xs, hxs, hxk, hxt, hxst, hxo, hxow, hxi, hxp⟩ := view_of st s hR e x he hpb
  obtain ⟨p, hp⟩ : ∃ p, x.pending = some p := by
    cases hp : x.pending with
    | none =>
      have hfail : st.deliverEnd e = .error (.assert "deliver: no pending event") := by
        simp [Cabi.Store.deliverEnd, Cabi.Store.getEnd, Cabi.need, he, hp, bind, Except.bind, pure,
          Except.pure]
      rw [hfail] at h; cases h
    | some p => exact ⟨p, rfl⟩
  have hxp' : xs.common.pending = some (.streamEnd ⟨e⟩ p) := by simp [hxp, hp, pendR, hst]
  have hks : xs.kind.isStream = true := by rw [hxk, isStream_kindR, hst]
  obtain ⟨ns, r, hout⟩ := deliverEnd_stream_outcome st st1 e p x ev he hst hp h
  have hres : (st1, ev) = (st.setEnd e (delivered x ns),
      (x.kind.eventCode, x.index.getD 0, r.toNat + 16 * p)) :=
    Except.ok.inj (h.symm.trans (deliverEnd_stream_eq st e p x he hst hp ns r hout))
  obtain ⟨hstate, hres2⟩ := deliverStep_outcome x xs p ns r hout hks hxo hxst
  have hpay : xs.payload (xs.clearPending.deliverStep p).2 p = r.toNat + 16 * p := by
    rw [End.payload, ite_eq_left_iff.mpr (fun h' => absurd hks h'), packStreamCopyResult_eq, hres2]
  refine ⟨_, _, takeEvent_stream_eq s e p xs hxs hxp', ?_, ?_, ?_, ?_⟩
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

/-- **`End.copy` with an idle peer, in both machines**: both park the buffer, and the stores
stay related. -/
theorem copyEnd_sim_park [Inhabited α] (st st1 : Cabi.Store α) (s : CStore E) (e b o : Nat)
    (x y : Cabi.End) (bx : Cabi.Buf α) (hR : EndsRel st s)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (ho : st.ends o = some y) (hyb : y.buffer = none) (hb : st.bufs b = some bx)
    (h : st.copyEnd e b = .ok st1) :
    ∃ s1, copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (s1, .none) ∧ EndsRel st1 s1 := by
  obtain ⟨xs, hxs, hxk, hxt, -, hxso, hxsb, hxow, hxi, hxp⟩ := view_of_unparked st s hR e x he hxb
  obtain ⟨ys, hys, -, -, -, -, hysb, -, -, -⟩ := view_of_unparked st s hR o y ho hyb
  have hoe' : (⟨o⟩ : EndId) ≠ ⟨e⟩ := fun h' => hoe (EndId.mk.inj h')
  have hcopy : st.copyEnd e b = .ok (st.setEnd e ((x.withState .copying).withBuffer (some b))) := by
    simp only [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, Cabi.check,
      Cabi.Store.setEnd, Cabi.upd, hoe, ho, hyb, bind, Except.bind, pure, Except.pure,
      Option.isNone_none, ite_true, ite_false, Cabi.End.withState, Cabi.End.withBuffer,
      Cabi.Store.mk.injEq, and_true, true_and, Except.ok.injEq]
    funext j
    by_cases hj : j = e
    · simp [Cabi.upd, hj]
    · simp [Cabi.upd, hj]
  have hst1 : st1 = st.setEnd e ((x.withState .copying).withBuffer (some b)) :=
    Except.ok.inj (h.symm.trans hcopy)
  have hc : copyCore ⟨e⟩ (bufR b bx) x.kind.isReadable s = .ok (setEnd s ⟨e⟩
      { xs with state := .copying, buffer := some (bufR b bx) }, .none) := by
    simp [copyCore, hxs, hxk, isReadable_kindR, hxso, hxo, hoe', hys, hysb]
  refine ⟨_, hc, ?_⟩
  rw [hst1]
  refine rel_frame st _ s _ e hR rfl (fun c hc => by simp [Cabi.Store.setEnd, Cabi.upd, hc])
    (fun c hc => by rw [end?_setEnd_ne _ _ hc]) ?_
  rw [end?_setEnd_self hxs]
  simp [viewS, viewC, Cabi.Store.setEnd, Cabi.upd, Cabi.End.withState, Cabi.End.withBuffer, hb,
    hxk, hxt, hxso, hxow, hxi, hxp, stateR]

end Silmaril.Wasm.Component.Async.CabiRef
