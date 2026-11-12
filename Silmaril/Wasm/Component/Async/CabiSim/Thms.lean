module

public import Silmaril.Wasm.Component.Async.CabiSim.Defs
public import Silmaril.Wasm.Component.Async.CabiRef.Thms

@[expose] public section

/-!
# The store model simulates `definitions.py` on a protocol fragment (unbounded)

PROVED (`agree_fragment`): from a new stream, **every** trace inside the protocol fragment of
`Silmaril.Wasm.Component.Async.CabiSim` (`Allowed`: copies of exactly `c > 0` values, an end
starts a copy only with no pending copy and no untaken event, events are taken only when
present, no drops), of any length, with any values and any chunk size, gets the same answers
from the store model `Silmaril.Wasm.Component.Async` and from the transcription
`Silmaril.Wasm.Component.Async.Cabi` of `definitions.py` at `d095e2f`: `BLOCKED` for a copy that
parks, `COMPLETED | c << 4` for a copy that meets the parked peer and for every event taken.
The transcription never traps there and the store model never fails.

The proof is a simulation: `Rel` relates the store model's pending copy and events to the
transcription's end states, parked buffers and recorded progress; `sim_step` shows that each
allowed operation is taken by both models with the same answer and keeps `Rel` (cases:
`sim_write_idle`, `sim_read_idle` park; `sim_write_read`, `sim_read_write` meet the parked
peer, through `Cabi.Store.copyEnd_transfer`; `sim_takeR`, `sim_takeW` deliver through
`CabiRef.deliverEnd_stream_eq`), and `sim_run` composes the steps.

Scope: one stream, at the level of the stream state machine (`End.copy` + immediate
delivery, as the canon `copy` does, and event delivery); the handle table, waitable sets
(`poll`/`wait`) and guest memory are not part of this fragment, and the values a read
delivers are not compared here (the bounded families of `CabiAgree` compare them, with
`poll`/`wait`). The fragment excludes exactly the differences of `CabiAgree`: unequal chunk
sizes (difference 2, `Cabi.Store.copyEnd_partial_keeps_parked`), drops (1, 3, 5, 6),
untaken events (4), zero-length copies (7) and new handles (8).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.CabiSim

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Pend Event)

/-- `newBuf`, unfolded. -/
theorem newBuf_eq (st : Cabi.Store Val) (bx : Cabi.Buf Val) :
    st.newBuf bx = ({ st with bufs := Cabi.upd st.bufs st.nBufs (some bx), nBufs := st.nBufs + 1 },
      st.nBufs) := rfl

/-- `End.copy` towards a peer with no parked buffer parks the buffer. -/
theorem copyEnd_park_eq (st : Cabi.Store Val) (e b o : Nat) (x y : Cabi.End) (he : st.ends e = some x)
    (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y)
    (hyb : y.buffer = none) :
    st.copyEnd e b = .ok (st.setEnd e ((x.withState .copying).withBuffer (some b))) := by
  simp only [Cabi.Store.copyEnd, Cabi.Store.getEnd, Cabi.need, he, hxb, hxo, Cabi.check,
    Cabi.Store.setEnd, Cabi.upd, hoe, ho, hyb, bind, Except.bind, pure, Except.pure,
    Option.isNone_none, ite_true, ite_false, Cabi.End.withState, Cabi.End.withBuffer,
    Cabi.Store.mk.injEq, and_true, true_and, Except.ok.injEq]
  funext j
  by_cases hj : j = e
  · simp [Cabi.upd, hj]
  · simp [Cabi.upd, hj]

/-- **A copy that parks**: `BLOCKED`. -/
theorem cCopy_park (st : Cabi.Store Val) (e o : Nat) (x y : Cabi.End) (bx : Cabi.Buf Val)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxp : x.pending = none)
    (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y) (hyb : y.buffer = none) :
    cCopy st e bx = .ok ((st.newBuf bx).1.setEnd e ((x.withState .copying).withBuffer
      (some st.nBufs)), Cabi.BLOCKED) := by
  have hpark := copyEnd_park_eq (st.newBuf bx).1 e st.nBufs o x y he hxb hxo hoe ho hyb
  have hnp : ((st.newBuf bx).1.setEnd e ((x.withState .copying).withBuffer
      (some st.nBufs))).hasPending (.end_ e) = false := by
    simp [Cabi.Store.hasPending, Cabi.Store.setEnd, Cabi.upd, Cabi.End.withState, Cabi.End.withBuffer, hxp]
  simp only [cCopy, newBuf_eq] at hpark hnp ⊢
  simp [hpark, hnp, bind, Except.bind, pure, Except.pure]


/-- The move of case 3 succeeds on host buffers with room. -/
theorem moveElems_ok_host (st : Cabi.Store Val) (isRead : Bool) (e b o ob n : Nat)
    (bx obx : Cabi.Buf Val) (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx) (hbo : b ≠ ob)
    (hbi : bx.inst = none) (hobi : obx.inst = none) (hn1 : n ≤ bx.remain)
    (hn2 : n ≤ obx.remain) : ∃ st1, st.moveElems isRead e b o ob n = .ok st1 := by
  have hn1' : n ≤ bx.length - bx.progress := hn1
  have hn2' : n ≤ obx.length - obx.progress := hn2
  cases isRead <;>
    simp [Cabi.Store.moveElems, Cabi.Store.bufRead, Cabi.Store.bufWrite, Cabi.Store.getBuf,
      Cabi.need, hb, hob, hbi, hobi, Cabi.check, Cabi.Store.setBuf, Cabi.upd, hbo,
      Ne.symm hbo, bind, Except.bind, pure, Except.pure, Cabi.Buf.remain, hn1', hn2']


/-- The notifications of case 3 succeed on stream ends. -/
theorem notifyBoth_ok (st : Cabi.Store Val) (e b o ob : Nat) (x y : Cabi.End)
    (bx obx : Cabi.Buf Val) (he : st.ends e = some x) (ho : st.ends o = some y) (hoe : o ≠ e)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx) (hxs : x.kind.isStream = true)
    (hys : y.kind.isStream = true) : ∃ st1, st.notifyBoth e b o ob = .ok st1 := by
  by_cases h0 : obx.remain = 0 <;>
    simp [Cabi.Store.notifyBoth, Cabi.Store.getBuf, Cabi.need, hb, hob, Cabi.Store.notify,
      Cabi.Store.getEnd, he, ho, Cabi.check, hxs, hys, Cabi.Store.setEnd, Cabi.upd, hoe, h0,
      bind, Except.bind, pure, Except.pure]


/-- **A copy that meets a parked buffer of the same size** completes at once: `COMPLETED`
with `c` values; the copying end is idle again, the peer has its completion pending and its
buffer unparked. -/
theorem cCopy_transfer (st : Cabi.Store Val) (e o ob c : Nat) (x y : Cabi.End)
    (bx obx : Cabi.Buf Val) (he : st.ends e = some x) (hxb : x.buffer = none)
    (hxo : x.other = some o) (hoe : o ≠ e) (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hob : st.bufs ob = some obx) (hlt : ob < st.nBufs) (hown : x.owner = none)
    (hxs : x.kind.isStream = true) (hys : y.kind.isStream = true)
    (hbi : bx.inst = none) (hobi : obx.inst = none) (hbl : bx.length = c) (hbp : bx.progress = 0)
    (hobl : obx.length = c) (hobp : obx.progress = 0) (hc : 0 < c)
    (hwf : (if x.kind.isReadable then obx else bx).ReadOk) :
    ∃ st1, cCopy st e bx = .ok (st1, 16 * c) ∧
      (∀ j, j ≠ e → j ≠ o → st1.ends j = st.ends j) ∧
      st1.ends e = some (CabiRef.delivered ((x.withState .copying).withPending c) .idle) ∧
      st1.ends o = some ((y.withPending c).withBuffer none) ∧ st1.nBufs = st.nBufs + 1 := by
  have hne : st.nBufs ≠ ob := Nat.ne_of_gt hlt
  have hSb : (st.newBuf bx).1.bufs st.nBufs = some bx := by simp [newBuf_eq, Cabi.upd]
  have hSob : (st.newBuf bx).1.bufs ob = some obx := by simp [newBuf_eq, Cabi.upd, Ne.symm hne, hob]
  have hrem : 0 < bx.remain ∧ 0 < obx.remain := by
    simp only [Cabi.Buf.remain, hbl, hbp, hobl, hobp]; omega
  have hmin : min bx.remain obx.remain = c := by simp only [Cabi.Buf.remain, hbl, hbp, hobl, hobp]; omega
  have htrap : (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) = false := by
    simp [hown]
  obtain ⟨st1, h1⟩ := moveElems_ok_host ((st.newBuf bx).1.setEnd e (x.withState .copying))
    x.kind.isReadable e st.nBufs o ob (min bx.remain obx.remain) bx obx hSb hSob hne hbi hobi
    (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  obtain ⟨-, h1e, -, ⟨bx', hbx', -⟩, ⟨obx', hobx', -⟩⟩ := Cabi.Store.moveElems_spec
    ((st.newBuf bx).1.setEnd e (x.withState .copying)) st1 _ _ _ _ _ _ bx obx hSb hSob hne hwf h1
  have hs1e : st1.ends e = some (x.withState .copying) := by
    rw [h1e]; simp [Cabi.Store.setEnd, Cabi.upd]
  have hs1o : st1.ends o = some y := by
    rw [h1e]; simp [Cabi.Store.setEnd, Cabi.upd, hoe, newBuf_eq, ho]
  obtain ⟨st2, h2⟩ := notifyBoth_ok st1 e st.nBufs o ob _ y bx' obx' hs1e hs1o hoe hbx' hobx'
    (by simpa [Cabi.End.withState] using hxs) hys
  have hcopy : (st.newBuf bx).1.copyEnd e st.nBufs = .ok st2 := by
    rw [Cabi.Store.copyEnd_meets_parked (st.newBuf bx).1 e st.nBufs o ob x y bx obx he hxb hxo hoe
      ho hyb hSb hSob htrap hrem.1 hrem.2]
    simp [h1, h2, bind, Except.bind]
  obtain ⟨hfn, hfr, hfe, hfo, -⟩ := Cabi.Store.copyEnd_transfer (st.newBuf bx).1 st2 e st.nBufs o
    ob x y bx obx he hxb hxo hoe ho hyb hSb hSob hne htrap hrem.1 hrem.2 hwf hcopy
  have hobr : obx.remain = c := by simp only [Cabi.Buf.remain, hobl, hobp]; omega
  have hfe' : st2.ends e = some ((x.withState .copying).withPending c) := by
    rw [hfe, hmin, hbp, Nat.zero_add]
  have hfo' : st2.ends o = some ((y.withPending c).withBuffer none) := by
    rw [hfo, hmin, hobp, Nat.zero_add, hobr, Nat.sub_self]; rfl
  have hout : CabiRef.StreamOutcome ((x.withState .copying).withPending c) .idle .completed :=
    .inr (.inr ⟨by simp [Cabi.End.withPending, Cabi.End.withState, hxo], rfl, rfl, rfl⟩)
  have hdel := CabiRef.deliverEnd_stream_eq st2 e c _ hfe' (by simpa [Cabi.End.withPending,
    Cabi.End.withState] using hxs) rfl .idle .completed hout
  have hpend : st2.hasPending (.end_ e) = true := by
    simp [Cabi.Store.hasPending, hfe', Cabi.End.withPending]
  refine ⟨st2.setEnd e (CabiRef.delivered ((x.withState .copying).withPending c) .idle), ?_,
    fun j hje hjo => ?_, ?_, ?_, ?_⟩
  · have hb2 : (st.newBuf bx).2 = st.nBufs := rfl
    simp only [cCopy, hb2, hcopy, hpend, hdel, ite_true, bind, Except.bind, pure, Except.pure]
    simp [Cabi.CopyResult.toNat]
  · simp [Cabi.Store.setEnd, Cabi.upd, hje, hfr j hje hjo, newBuf_eq]
  · simp [Cabi.Store.setEnd, Cabi.upd]
  · simp [Cabi.Store.setEnd, Cabi.upd, hoe, hfo']
  · simp [Cabi.Store.setEnd, hfn, newBuf_eq]



variable {r w s er ew c : Nat} {m : Silmaril.Wasm.Component.Async.Store} {st : Cabi.Store Val}

/-- A write while nothing is pending parks in both models: `BLOCKED`. -/
theorem sim_write_idle (hR : Rel r w s er ew c m st) (xs : List Val) (hlen : xs.length = c)
    (hev : m.ev w = none) (hidle : (m.chans s).pend = .idle) :
    ∃ m' st', mStep r w c m (.write xs) = some (m', Cabi.BLOCKED) ∧
      cStep er ew c st (.write xs) = .ok (st', Cabi.BLOCKED) ∧ Rel r w s er ew c m' st' := by
  obtain ⟨xr, hxr, hxrk, hxro, hxrow, hRs⟩ := hR.endR
  obtain ⟨xw, hxw, hxwk, hxwo, hxwow, hWs⟩ := hR.endW
  have hW : xw.state = .idle ∧ xw.buffer = none ∧ xw.pending = none := by
    simpa [WShape, hev, hidle] using hWs
  have hRb : xr.buffer = none := by
    cases hevr : m.ev r <;> simp_all [RShape]
  have hm : mStep r w c m (.write xs) =
      some (m.setChan s { m.chans s with pend := .write w xs }, Cabi.BLOCKED) := by
    have hd := hR.noDropR
    simp [mStep, Silmaril.Wasm.Component.Async.streamWrite, hR.tblW, hidle, hd, resNat,
      Silmaril.Wasm.Component.Async.blocked, Cabi.BLOCKED]
  refine ⟨_, _, hm, cCopy_park st ew er xw xr _ hxw hW.2.1 hW.2.2 hxwo hR.hne hxr hRb, ?_⟩
  have hRs' : ∀ st' : Cabi.Store Val, RShape c st' (.write w xs) (m.ev r) xr := by
    intro st'
    cases hevr : m.ev r <;> simp_all [RShape]
  exact {
    pos := hR.pos
    tblR := by simp [Silmaril.Wasm.Component.Async.Store.setChan, hR.tblR]
    tblW := by simp [Silmaril.Wasm.Component.Async.Store.setChan, hR.tblW]
    hrw := hR.hrw
    noDropR := by simp [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd,
      hR.noDropR]
    noDropW := by simp [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd,
      hR.noDropW]
    pendRead := by simp [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd]
    pendWrite := by
      simp [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd, hlen, hev]
    evR := hR.evR
    evW := hR.evW
    hne := hR.hne
    endR := ⟨xr, by simp [Cabi.Store.setEnd, Cabi.upd, hR.hne, newBuf_eq, hxr], hxrk, hxro, hxrow,
      by simpa [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd] using
        hRs' _⟩
    endW := ⟨(xw.withState .copying).withBuffer (some st.nBufs), by simp [Cabi.Store.setEnd,
      Cabi.upd], hxwk, hxwo, hxwow, by
        simp [WShape, Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd,
          hev, Cabi.End.withState, Cabi.End.withBuffer, hW.2.2, Cabi.Store.setEnd, newBuf_eq,
          Cabi.upd, hlen]⟩ }



/-- A read while nothing is pending parks in both models: `BLOCKED`. -/
theorem sim_read_idle (hR : Rel r w s er ew c m st) (hev : m.ev r = none)
    (hidle : (m.chans s).pend = .idle) :
    ∃ m' st', mStep r w c m .read = some (m', Cabi.BLOCKED) ∧
      cStep er ew c st .read = .ok (st', Cabi.BLOCKED) ∧ Rel r w s er ew c m' st' := by
  obtain ⟨xr, hxr, hxrk, hxro, hxrow, hRs⟩ := hR.endR
  obtain ⟨xw, hxw, hxwk, hxwo, hxwow, hWs⟩ := hR.endW
  have hRx : xr.state = .idle ∧ xr.buffer = none ∧ xr.pending = none := by
    simpa [RShape, hev, hidle] using hRs
  have hWb : xw.buffer = none := by
    cases hevw : m.ev w <;> simp_all [WShape]
  have hm : mStep r w c m .read =
      some (m.setChan s { m.chans s with pend := .read r c }, Cabi.BLOCKED) := by
    have hd := hR.noDropW
    simp [mStep, Silmaril.Wasm.Component.Async.streamRead, hR.tblR, hidle, hd, resNat,
      Silmaril.Wasm.Component.Async.blocked, Cabi.BLOCKED]
  refine ⟨_, _, hm, cCopy_park st er ew xr xw _ hxr hRx.2.1 hRx.2.2 hxro (Ne.symm hR.hne) hxw hWb,
    ?_⟩
  have hWs' : ∀ st' : Cabi.Store Val, WShape c st' (.read r c) (m.ev w) xw := by
    intro st'
    cases hevw : m.ev w <;> simp_all [WShape]
  exact {
    pos := hR.pos
    tblR := by simp [Silmaril.Wasm.Component.Async.Store.setChan, hR.tblR]
    tblW := by simp [Silmaril.Wasm.Component.Async.Store.setChan, hR.tblW]
    hrw := hR.hrw
    noDropR := by simp [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd,
      hR.noDropR]
    noDropW := by simp [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd,
      hR.noDropW]
    pendRead := by simp [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd, hev]
    pendWrite := by simp [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd]
    evR := hR.evR
    evW := hR.evW
    hne := hR.hne
    endR := ⟨(xr.withState .copying).withBuffer (some st.nBufs), by simp [Cabi.Store.setEnd,
      Cabi.upd], hxrk, hxro, hxrow, by
        simp [RShape, Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd,
          hev, Cabi.End.withState, Cabi.End.withBuffer, hRx.2.2, Cabi.Store.setEnd, newBuf_eq,
          Cabi.upd]⟩
    endW := ⟨xw, by simp [Cabi.Store.setEnd, Cabi.upd, Ne.symm hR.hne, newBuf_eq, hxw], hxwk, hxwo,
      hxwow, by simpa [Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd]
        using hWs' _⟩ }



/-- A write meeting the pending read completes both in both models: `COMPLETED` with `c`
values; the reader's event is pending. -/
theorem sim_write_read (hR : Rel r w s er ew c m st) (xs : List Val) (hlen : xs.length = c)
    (hev : m.ev w = none) (h n : Nat) (hpend : (m.chans s).pend = .read h n) :
    ∃ m' st', mStep r w c m (.write xs) = some (m', 16 * c) ∧
      cStep er ew c st (.write xs) = .ok (st', 16 * c) ∧ Rel r w s er ew c m' st' := by
  obtain ⟨hhr, hnc, hevr⟩ := hR.pendRead h n hpend
  subst hhr hnc
  obtain ⟨xr, hxr, hxrk, hxro, hxrow, hRs⟩ := hR.endR
  obtain ⟨xw, hxw, hxwk, hxwo, hxwow, hWs⟩ := hR.endW
  obtain ⟨hrst, hrp, br, brx, hrb, hbr, hbrlt, hbri, hbrl, hbrp⟩ :
      xr.state = .copying ∧ xr.pending = none ∧ ∃ b bx, xr.buffer = some b ∧ st.bufs b = some bx ∧
        b < st.nBufs ∧ bx.inst = none ∧ bx.length = n ∧ bx.progress = 0 := by
    simpa [RShape, hevr, hpend] using hRs
  have hW : xw.state = .idle ∧ xw.buffer = none ∧ xw.pending = none := by
    simpa [WShape, hev, hpend] using hWs
  obtain ⟨st1, hc1, hfr, hfe, hfo, hfn⟩ := cCopy_transfer st ew er br n xw xr
    { inst := none, length := xs.length, src := xs } brx hxw hW.2.1 hxwo hR.hne hxr hrb hbr hbrlt
    hxwow (by simp [hxwk, Cabi.EndKind.isStream]) (by simp [hxrk, Cabi.EndKind.isStream]) rfl
    hbri hlen rfl hbrl hbrp hR.pos (by simp [hxwk, Cabi.EndKind.isReadable, Cabi.Buf.ReadOk])
  have hmin : min n xs.length = n := by rw [hlen, Nat.min_self]
  have hm : mStep h w n m (.write xs) = some ((m.setChan s ⟨.idle, (m.chans s).rDropped,
      (m.chans s).wDropped, (m.chans s).done, (m.chans s).sent ++ xs.take n⟩).post h
        ⟨.streamRead, h, Silmaril.Wasm.Component.Async.packCopy .completed n, xs.take n⟩,
      16 * n) := by
    simp [mStep, Silmaril.Wasm.Component.Async.streamWrite, hR.tblW, hpend, resNat, hmin,
      Silmaril.Wasm.Component.Async.packCopy, Silmaril.Wasm.Component.Async.CopyResult.toNat]
  refine ⟨_, st1, hm, hc1, ?_⟩
  have hwr : w ≠ h := Ne.symm hR.hrw
  exact {
    pos := hR.pos
    tblR := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      hR.tblR]
    tblW := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      hR.tblW]
    hrw := hR.hrw
    noDropR := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      Silmaril.Wasm.Component.Async.upd, hR.noDropR]
    noDropW := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      Silmaril.Wasm.Component.Async.upd, hR.noDropW]
    pendRead := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      Silmaril.Wasm.Component.Async.upd]
    pendWrite := by simp [Silmaril.Wasm.Component.Async.Store.post,
      Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd]
    evR := by
      simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
        Silmaril.Wasm.Component.Async.upd, Silmaril.Wasm.Component.Async.packCopy,
        Silmaril.Wasm.Component.Async.CopyResult.toNat]
    evW := by
      simpa [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
        Silmaril.Wasm.Component.Async.upd, hwr] using hR.evW
    hne := hR.hne
    endR := ⟨_, hfo, by simp [Cabi.End.withPending, Cabi.End.withBuffer, hxrk],
      by simp [Cabi.End.withPending, Cabi.End.withBuffer, hxro],
      by simp [Cabi.End.withPending, Cabi.End.withBuffer, hxrow],
      by simp [RShape, Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.upd,
        Cabi.End.withPending, Cabi.End.withBuffer, hrst]⟩
    endW := ⟨_, hfe, by simp [CabiRef.delivered, Cabi.End.withPending, Cabi.End.withState, hxwk],
      by simp [CabiRef.delivered, Cabi.End.withPending, Cabi.End.withState, hxwo],
      by simp [CabiRef.delivered, Cabi.End.withPending, Cabi.End.withState, hxwow],
      by simp [WShape, Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.upd,
        Silmaril.Wasm.Component.Async.Store.setChan, hwr, hev, CabiRef.delivered]⟩ }



/-- A read meeting the pending write completes both in both models: `COMPLETED` with `c`
values; the writer's event is pending. -/
theorem sim_read_write (hR : Rel r w s er ew c m st) (hev : m.ev r = none) (h : Nat)
    (xs : List Val) (hpend : (m.chans s).pend = .write h xs) :
    ∃ m' st', mStep r w c m .read = some (m', 16 * c) ∧
      cStep er ew c st .read = .ok (st', 16 * c) ∧ Rel r w s er ew c m' st' := by
  obtain ⟨hhw, hlen, hevw⟩ := hR.pendWrite h xs hpend
  subst hhw
  obtain ⟨xr, hxr, hxrk, hxro, hxrow, hRs⟩ := hR.endR
  obtain ⟨xw, hxw, hxwk, hxwo, hxwow, hWs⟩ := hR.endW
  obtain ⟨hwst, hwp, bw, bwx, hwb, hbw, hbwlt, hbwi, hbwl, hbwp, hbws⟩ :
      xw.state = .copying ∧ xw.pending = none ∧ ∃ b bx, xw.buffer = some b ∧ st.bufs b = some bx ∧
        b < st.nBufs ∧ bx.inst = none ∧ bx.length = c ∧ bx.progress = 0 ∧ bx.src = xs := by
    simpa [WShape, hevw, hpend] using hWs
  have hRx : xr.state = .idle ∧ xr.buffer = none ∧ xr.pending = none := by
    simpa [RShape, hev, hpend] using hRs
  obtain ⟨st1, hc1, hfr, hfe, hfo, hfn⟩ := cCopy_transfer st er ew bw c xr xw
    { inst := none, length := c } bwx hxr hRx.2.1 hxro (Ne.symm hR.hne) hxw hwb hbw hbwlt
    hxrow (by simp [hxrk, Cabi.EndKind.isStream]) (by simp [hxwk, Cabi.EndKind.isStream]) rfl
    hbwi rfl rfl hbwl hbwp hR.pos
    (by simp [hxrk, Cabi.EndKind.isReadable, Cabi.Buf.ReadOk, hbwi, hbwl, hbws, hlen])
  have hmin : min c xs.length = c := by rw [hlen, Nat.min_self]
  have hm : mStep r h c m .read = some ((m.setChan s ⟨.idle, (m.chans s).rDropped,
      (m.chans s).wDropped, (m.chans s).done, (m.chans s).sent ++ xs.take c⟩).post h
        ⟨.streamWrite, h, Silmaril.Wasm.Component.Async.packCopy .completed c, []⟩,
      16 * c) := by
    simp [mStep, Silmaril.Wasm.Component.Async.streamRead, hR.tblR, hpend, resNat, hmin,
      Silmaril.Wasm.Component.Async.packCopy, Silmaril.Wasm.Component.Async.CopyResult.toNat]
  refine ⟨_, st1, hm, hc1, ?_⟩
  have hrw : r ≠ h := hR.hrw
  exact {
    pos := hR.pos
    tblR := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      hR.tblR]
    tblW := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      hR.tblW]
    hrw := hR.hrw
    noDropR := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      Silmaril.Wasm.Component.Async.upd, hR.noDropR]
    noDropW := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      Silmaril.Wasm.Component.Async.upd, hR.noDropW]
    pendRead := by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
      Silmaril.Wasm.Component.Async.upd]
    pendWrite := by simp [Silmaril.Wasm.Component.Async.Store.post,
      Silmaril.Wasm.Component.Async.Store.setChan, Silmaril.Wasm.Component.Async.upd]
    evR := by
      simpa [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
        Silmaril.Wasm.Component.Async.upd, hrw] using hR.evR
    evW := by
      simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.Store.setChan,
        Silmaril.Wasm.Component.Async.upd, Silmaril.Wasm.Component.Async.packCopy,
        Silmaril.Wasm.Component.Async.CopyResult.toNat]
    hne := hR.hne
    endR := ⟨_, hfe, by simp [CabiRef.delivered, Cabi.End.withPending, Cabi.End.withState, hxrk],
      by simp [CabiRef.delivered, Cabi.End.withPending, Cabi.End.withState, hxro],
      by simp [CabiRef.delivered, Cabi.End.withPending, Cabi.End.withState, hxrow],
      by simp [RShape, Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.upd,
        Silmaril.Wasm.Component.Async.Store.setChan, hrw, hev, CabiRef.delivered]⟩
    endW := ⟨_, hfo, by simp [Cabi.End.withPending, Cabi.End.withBuffer, hxwk],
      by simp [Cabi.End.withPending, Cabi.End.withBuffer, hxwo],
      by simp [Cabi.End.withPending, Cabi.End.withBuffer, hxwow],
      by simp [WShape, Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.upd,
        Cabi.End.withPending, Cabi.End.withBuffer, hwst]⟩ }



/-- WShape does not look at the ends of the store. -/
theorem wshape_setEnd (st : Cabi.Store Val) (e : Nat) (z : Cabi.End) (pend : Pend)
    (ev : Option Event) (x : Cabi.End) (h : WShape c st pend ev x) :
    WShape c (st.setEnd e z) pend ev x := h

/-- RShape does not look at the ends of the store. -/
theorem rshape_setEnd (st : Cabi.Store Val) (e : Nat) (z : Cabi.End) (pend : Pend)
    (ev : Option Event) (x : Cabi.End) (h : RShape c st pend ev x) :
    RShape c (st.setEnd e z) pend ev x := h

/-- Taking the reader's event: the same payload in both models. -/
theorem sim_takeR (hR : Rel r w s er ew c m st) (e : Event) (hev : m.ev r = some e) :
    ∃ m' st', mStep r w c m .takeR = some (m', 16 * c) ∧
      cStep er ew c st .takeR = .ok (st', 16 * c) ∧ Rel r w s er ew c m' st' := by
  obtain ⟨xr, hxr, hxrk, hxro, hxrow, hRs⟩ := hR.endR
  obtain ⟨xw, hxw, hxwk, hxwo, hxwow, hWs⟩ := hR.endW
  have hRx : xr.state = .copying ∧ xr.buffer = none ∧ xr.pending = some c := by
    simpa [RShape, hev] using hRs
  have hout : CabiRef.StreamOutcome xr .idle .completed :=
    .inr (.inr ⟨by simp [hxro], hRx.1, rfl, rfl⟩)
  have hdel := CabiRef.deliverEnd_stream_eq st er c xr hxr (by simp [hxrk, Cabi.EndKind.isStream])
    hRx.2.2 .idle .completed hout
  have hm : mStep r w c m .takeR = some ({ m with ev := Silmaril.Wasm.Component.Async.upd m.ev r none },
      16 * c) := by
    simp [mStep, Silmaril.Wasm.Component.Async.take, hev, hR.evR e hev]
  have hc : cStep er ew c st .takeR = .ok (st.setEnd er (CabiRef.delivered xr .idle), 16 * c) := by
    simp [cStep, hdel, Except.map, Cabi.CopyResult.toNat]
  refine ⟨_, _, hm, hc, ?_⟩
  have hnotread : ∀ h n, (m.chans s).pend ≠ .read h n := fun h n hp => by
    simp [(hR.pendRead h n hp).2.2] at hev
  have hwr : w ≠ r := Ne.symm hR.hrw
  exact {
    pos := hR.pos
    tblR := hR.tblR
    tblW := hR.tblW
    hrw := hR.hrw
    noDropR := hR.noDropR
    noDropW := hR.noDropW
    pendRead := fun h n hp => absurd hp (hnotread h n)
    pendWrite := fun h xs hp => by
      obtain ⟨h1, h2, h3⟩ := hR.pendWrite h xs hp
      exact ⟨h1, h2, by simp [Silmaril.Wasm.Component.Async.upd, hwr, h3]⟩
    evR := by simp [Silmaril.Wasm.Component.Async.upd]
    evW := by simpa [Silmaril.Wasm.Component.Async.upd, hwr] using hR.evW
    hne := hR.hne
    endR := ⟨CabiRef.delivered xr .idle, by simp [Cabi.Store.setEnd, Cabi.upd],
      by simp [CabiRef.delivered, hxrk],
      by simp [CabiRef.delivered, hxro], by simp [CabiRef.delivered, hxrow], by
        cases hp : (m.chans s).pend with
        | read h n => exact absurd hp (hnotread h n)
        | _ => simp [RShape, Silmaril.Wasm.Component.Async.upd, CabiRef.delivered]⟩
    endW := ⟨xw, by simp [Cabi.Store.setEnd, Cabi.upd, Ne.symm hR.hne, hxw], hxwk, hxwo, hxwow,
      by simpa [Silmaril.Wasm.Component.Async.upd, hwr] using wshape_setEnd st er _ _ _ xw hWs⟩ }

/-- Taking the writer's event: the same payload in both models. -/
theorem sim_takeW (hR : Rel r w s er ew c m st) (e : Event) (hev : m.ev w = some e) :
    ∃ m' st', mStep r w c m .takeW = some (m', 16 * c) ∧
      cStep er ew c st .takeW = .ok (st', 16 * c) ∧ Rel r w s er ew c m' st' := by
  obtain ⟨xr, hxr, hxrk, hxro, hxrow, hRs⟩ := hR.endR
  obtain ⟨xw, hxw, hxwk, hxwo, hxwow, hWs⟩ := hR.endW
  have hWx : xw.state = .copying ∧ xw.buffer = none ∧ xw.pending = some c := by
    simpa [WShape, hev] using hWs
  have hout : CabiRef.StreamOutcome xw .idle .completed :=
    .inr (.inr ⟨by simp [hxwo], hWx.1, rfl, rfl⟩)
  have hdel := CabiRef.deliverEnd_stream_eq st ew c xw hxw (by simp [hxwk, Cabi.EndKind.isStream])
    hWx.2.2 .idle .completed hout
  have hm : mStep r w c m .takeW = some ({ m with ev := Silmaril.Wasm.Component.Async.upd m.ev w none },
      16 * c) := by
    simp [mStep, Silmaril.Wasm.Component.Async.take, hev, hR.evW e hev]
  have hc : cStep er ew c st .takeW = .ok (st.setEnd ew (CabiRef.delivered xw .idle), 16 * c) := by
    simp [cStep, hdel, Except.map, Cabi.CopyResult.toNat]
  refine ⟨_, _, hm, hc, ?_⟩
  have hnotwrite : ∀ h xs, (m.chans s).pend ≠ .write h xs := fun h xs hp => by
    simp [(hR.pendWrite h xs hp).2.2] at hev
  have hrw : r ≠ w := hR.hrw
  exact {
    pos := hR.pos
    tblR := hR.tblR
    tblW := hR.tblW
    hrw := hR.hrw
    noDropR := hR.noDropR
    noDropW := hR.noDropW
    pendRead := fun h n hp => by
      obtain ⟨h1, h2, h3⟩ := hR.pendRead h n hp
      exact ⟨h1, h2, by simp [Silmaril.Wasm.Component.Async.upd, hrw, h3]⟩
    pendWrite := fun h xs hp => absurd hp (hnotwrite h xs)
    evR := by simpa [Silmaril.Wasm.Component.Async.upd, hrw] using hR.evR
    evW := by simp [Silmaril.Wasm.Component.Async.upd]
    hne := hR.hne
    endR := ⟨xr, by simp [Cabi.Store.setEnd, Cabi.upd, hR.hne, hxr], hxrk, hxro, hxrow,
      by simpa [Silmaril.Wasm.Component.Async.upd, hrw] using rshape_setEnd st ew _ _ _ xr hRs⟩
    endW := ⟨CabiRef.delivered xw .idle, by simp [Cabi.Store.setEnd, Cabi.upd],
      by simp [CabiRef.delivered, hxwk],
      by simp [CabiRef.delivered, hxwo], by simp [CabiRef.delivered, hxwow], by
        cases hp : (m.chans s).pend with
        | write h xs => exact absurd hp (hnotwrite h xs)
        | _ => simp [WShape, Silmaril.Wasm.Component.Async.upd, CabiRef.delivered]⟩ }



/-- **One step of the simulation**: inside the fragment, both models take the step, with the
same answer, and stay related. -/
theorem sim_step (hR : Rel r w s er ew c m st) (o : FOp) (hA : Allowed r w c s m o) :
    ∃ m' st' a, mStep r w c m o = some (m', a) ∧ cStep er ew c st o = .ok (st', a) ∧
      Rel r w s er ew c m' st' := by
  cases o with
  | write xs =>
    obtain ⟨hlen, hev, hnw⟩ := hA
    cases hp : (m.chans s).pend with
    | idle => exact (fun ⟨m1, s1, hh⟩ => ⟨m1, s1, _, hh⟩) (sim_write_idle hR xs hlen hev hp)
    | read h n => exact (fun ⟨m1, s1, hh⟩ => ⟨m1, s1, _, hh⟩) (sim_write_read hR xs hlen hev h n hp)
    | write h ys => exact absurd hp (hnw h ys)
  | read =>
    obtain ⟨hev, hnr⟩ := hA
    cases hp : (m.chans s).pend with
    | idle => exact (fun ⟨m1, s1, hh⟩ => ⟨m1, s1, _, hh⟩) (sim_read_idle hR hev hp)
    | read h n => exact absurd hp (hnr h n)
    | write h ys => exact (fun ⟨m1, s1, hh⟩ => ⟨m1, s1, _, hh⟩) (sim_read_write hR hev h ys hp)
  | takeR =>
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hA
    exact (fun ⟨m1, s1, hh⟩ => ⟨m1, s1, _, hh⟩) (sim_takeR hR e he)
  | takeW =>
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hA
    exact (fun ⟨m1, s1, hh⟩ => ⟨m1, s1, _, hh⟩) (sim_takeW hR e he)

/-- **The simulation**: on every trace inside the fragment, of any length, the transcription
gives the store model's answers. -/
theorem sim_run (ops : List FOp) (as : List Nat) (hrun : MRun r w c s m ops as) :
    ∀ st, Rel r w s er ew c m st → cRun er ew c st ops = .ok as := by
  induction hrun with
  | nil => intro st _; rfl
  | cons hA hm _ ih =>
    intro st hR
    obtain ⟨m'', st', a', hm', hc', hR'⟩ := sim_step hR _ hA
    rw [hm] at hm'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
    simp [cRun, hc', ih st' hR', bind, Except.bind, pure, Except.pure]


/-- The new stream is related, for every chunk size. -/
theorem rel_init (t : Cabi.Ty) (c : Nat) (hc : 0 < c) : Rel 1 2 1 0 1 c mInit (cInit t) where
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
  endW := ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩

/-- **Agreement on the fragment, unbounded**: from a new stream, every trace inside the
fragment (any length, any chunk size `c > 0`, any values) gets the same answers from the
store model and from the transcription. -/
theorem agree_fragment (t : Cabi.Ty) (c : Nat) (hc : 0 < c) (ops : List FOp) (as : List Nat)
    (hrun : MRun 1 2 c 1 mInit ops as) : cRun 0 1 c (cInit t) ops = .ok as :=
  sim_run ops as hrun _ (rel_init t c hc)

end Silmaril.Wasm.Component.Async.CabiSim
