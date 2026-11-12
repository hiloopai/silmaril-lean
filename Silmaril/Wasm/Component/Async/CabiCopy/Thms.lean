module

public import Silmaril.Wasm.Component.Async.Cabi.Thms
public import Silmaril.Wasm.Component.Async.CabiCopy.Defs
public import Silmaril.Wasm.Component.Async.Defs

@[expose] public section

/-!
# Copies that meet a parked buffer (difference 2)

PROVED, for every store of the transcription `Silmaril.Wasm.Component.Async.Cabi`
(`definitions.py` at `d095e2f`, `End.copy` L958–981, case 3):

* `copyEnd_transfer_w`, `copyEnd_transfer_r`: when the copying end `e` meets the parked
  buffer `ob` of its peer `o` and both have room, `n = min remain remain` elements move; both
  ends get a pending event with their cumulative progress; the copying end is `COPYING` with no
  parked buffer; the peer's buffer stays parked **unless it is full**; no other end changes.
* `copyEnd_partial_keeps_parked` (**difference 2**, general form): if the peer's parked buffer
  has more room than the copy, it stays parked with its progress advanced, so the next copy of
  the copying end continues from it.

STORE MODEL (`Silmaril.Wasm.Component.Async`), for every store:
`streamRead_clears_pend`, `streamWrite_clears_pend`: a rendezvous always leaves the channel
with no pending copy (the pending side completes), whatever the lengths.

So on every partial rendezvous the two models disagree on the parked side
(`CabiAgree.differ_partialWriteParked`, `differ_partialReadParked` are instances).

The host-buffer side condition (`hwf`): the buffer that is read is a guest buffer or holds
values for its whole length (true of every `HostReadableBuffer` the steps create).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.Cabi

namespace Store
variable {α : Type} [Inhabited α]

/-- What `bufRead` changes: the progress of the buffer (and nothing of the ends). -/
theorem bufRead_spec (st st1 : Store α) (b n : Nat) (vs : List α) (bx : Buf α)
    (hb : st.bufs b = some bx) (h : st.bufRead b n = .ok (st1, vs)) :
    st1.nBufs = st.nBufs ∧ st1.ends = st.ends ∧ (∀ c, c ≠ b → st1.bufs c = st.bufs c) ∧
      ∃ bx', st1.bufs b = some bx' ∧ bx'.progress = bx.progress + n ∧ bx'.length = bx.length ∧
        bx'.inst = bx.inst ∧ bx'.src = bx.src := by
  unfold bufRead at h
  cases hi : bx.inst with
  | none =>
    simp only [getBuf, need, hb, hi, check, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, rfl, fun c hc => by simp [setBuf, upd, hc], by simp [setBuf, upd]⟩
  | some i =>
    simp only [getBuf, need, hb, hi, check, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨rfl, -⟩ := h
        exact ⟨rfl, rfl, fun c hc => by simp [setBuf, upd, hc], by simp [setBuf, upd]⟩

/-- What `bufWrite` changes: the progress of the buffer (and nothing of the ends). -/
theorem bufWrite_spec (st st1 : Store α) (e b : Nat) (vs : List α) (bx : Buf α)
    (hb : st.bufs b = some bx) (h : st.bufWrite e b vs = .ok st1) :
    st1.nBufs = st.nBufs ∧ st1.ends = st.ends ∧ (∀ c, c ≠ b → st1.bufs c = st.bufs c) ∧
      ∃ bx', st1.bufs b = some bx' ∧ bx'.progress = bx.progress + vs.length ∧
        bx'.length = bx.length ∧ bx'.inst = bx.inst ∧ bx'.src = bx.src := by
  unfold bufWrite at h
  cases hi : bx.inst with
  | none =>
    simp only [getBuf, need, hb, hi, check, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl, fun c hc => by simp [setBuf, upd, hc], by simp [setBuf, upd]⟩
  | some i =>
    simp only [getBuf, need, hb, hi, check, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl, fun c hc => by simp [setInst, setBuf, upd, hc],
          by simp [setInst, setBuf, upd]⟩

/-- `bufRead` returns `n` values from a guest buffer, or from a host buffer whose values cover
its length. -/
theorem bufRead_length (st st1 : Store α) (b n : Nat) (vs : List α) (bx : Buf α)
    (hb : st.bufs b = some bx) (hwf : bx.inst.isSome ∨ bx.length ≤ bx.src.length)
    (h : st.bufRead b n = .ok (st1, vs)) : vs.length = n := by
  unfold bufRead at h
  by_cases hle : n ≤ bx.remain
  · cases hi : bx.inst with
    | none =>
      have hl : bx.length ≤ bx.src.length := by simpa [hi] using hwf
      simp only [getBuf, need, hb, hi, check, hle, decide_true, ite_true, bind, Except.bind, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [Buf.remain] at hle
      simp only [List.length_take, List.length_drop]
      omega
    | some i =>
      simp only [getBuf, need, hb, hi, check, hle, decide_true, ite_true, bind, Except.bind, pure,
        Except.pure] at h
      split at h
      · cases h
      · obtain ⟨-, rfl⟩ := h
        split <;> simp
  · simp [getBuf, need, hb, check, hle, bind, Except.bind, pure, Except.pure] at h

omit [Inhabited α] in
/-- What `notify` changes: the pending event of the end. -/
theorem notify_spec (st st1 : Store α) (e p : Nat) (x : End)
    (he : st.ends e = some x) (h : st.notify e p = .ok st1) :
    st1.nBufs = st.nBufs ∧ st1.bufs = st.bufs ∧ (∀ c, c ≠ e → st1.ends c = st.ends c) ∧
      st1.ends e = some (x.withPending p) := by
  simp only [notify, getEnd, need, he, check, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl, fun c hc => by simp [setEnd, upd, hc], by simp [setEnd, upd, End.withPending]⟩


/-- **The move of case 3**: both buffers advance by `n`; nothing else changes but memory. -/
theorem moveElems_spec (st st1 : Store α) (isRead : Bool) (e b o ob n : Nat) (bx obx : Buf α)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx) (hbo : b ≠ ob)
    (hwf : (if isRead then obx else bx).ReadOk) (h : st.moveElems isRead e b o ob n = .ok st1) :
    st1.nBufs = st.nBufs ∧ st1.ends = st.ends ∧ (∀ c, c ≠ b → c ≠ ob → st1.bufs c = st.bufs c) ∧
      (∃ bx', st1.bufs b = some bx' ∧ bx'.progress = bx.progress + n ∧ bx'.length = bx.length) ∧
      (∃ obx', st1.bufs ob = some obx' ∧ obx'.progress = obx.progress + n ∧
        obx'.length = obx.length) := by
  cases isRead with
  | true =>
    show st1.nBufs = st.nBufs ∧ _
    obtain ⟨⟨s1, vs⟩, h1, h2⟩ : ∃ r, st.bufRead ob n = .ok r ∧ r.1.bufWrite e b r.2 = .ok st1 :=
      bind_ok.1 h
    obtain ⟨h1n, h1e, h1b, obx', hobx', hp1, hl1, -, -⟩ := bufRead_spec _ _ _ _ _ _ hob h1
    have hlen : vs.length = n := bufRead_length _ _ _ _ _ _ hob hwf h1
    have hb1 : s1.bufs b = some bx := by rw [h1b _ hbo, hb]
    obtain ⟨h2n, h2e, h2b, bx', hbx', hp2, hl2, -, -⟩ := bufWrite_spec _ _ _ _ _ _ hb1 h2
    refine ⟨h2n.trans h1n, h2e.trans h1e, fun c hc hc' => (h2b c hc).trans (h1b c hc'), ⟨bx', hbx', ?_, hl2⟩,
      ⟨obx', (h2b ob (Ne.symm hbo)).trans hobx', hp1, hl1⟩⟩
    rw [hp2, hlen]
  | false =>
    show st1.nBufs = st.nBufs ∧ _
    obtain ⟨⟨s1, vs⟩, h1, h2⟩ : ∃ r, st.bufRead b n = .ok r ∧ r.1.bufWrite o ob r.2 = .ok st1 :=
      bind_ok.1 h
    obtain ⟨h1n, h1e, h1b, bx', hbx', hp1, hl1, -, -⟩ := bufRead_spec _ _ _ _ _ _ hb h1
    have hlen : vs.length = n := bufRead_length _ _ _ _ _ _ hb hwf h1
    have hob1 : s1.bufs ob = some obx := by rw [h1b _ (Ne.symm hbo), hob]
    obtain ⟨h2n, h2e, h2b, obx', hobx', hp2, hl2, -, -⟩ := bufWrite_spec _ _ _ _ _ _ hob1 h2
    refine ⟨h2n.trans h1n, h2e.trans h1e, fun c hc hc' => (h2b c hc').trans (h1b c hc),
      ⟨bx', (h2b b hbo).trans hbx', hp1, hl1⟩, ⟨obx', hobx', ?_, hl2⟩⟩
    rw [hp2, hlen]

omit [Inhabited α] in
/-- **The notifications of case 3**: both ends get their buffers' progress; the peer's buffer
is unparked when full. -/
theorem notifyBoth_spec (st st1 : Store α) (e b o ob : Nat) (x y : End) (bx obx : Buf α)
    (he : st.ends e = some x) (ho : st.ends o = some y) (hoe : o ≠ e)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx)
    (h : st.notifyBoth e b o ob = .ok st1) :
    st1.nBufs = st.nBufs ∧ st1.bufs = st.bufs ∧ (∀ c, c ≠ e → c ≠ o → st1.ends c = st.ends c) ∧
      st1.ends e = some (x.withPending bx.progress) ∧
      st1.ends o = some ((y.withPending obx.progress).withBuffer
        (if obx.remain = 0 then none else y.buffer)) := by
  have hgb : st.getBuf b = .ok bx := by simp [getBuf, need, hb, pure, Except.pure]
  have hgob : st.getBuf ob = .ok obx := by simp [getBuf, need, hob, pure, Except.pure]
  have hstep : st.notifyBoth e b o ob = (st.notify e bx.progress >>= fun s3 =>
      s3.notify o obx.progress >>= fun s4 =>
        if obx.remain = 0 then s4.getEnd o >>= fun z => pure (s4.setEnd o (z.withBuffer none))
        else pure s4) := by
    simp only [notifyBoth, hgb, hgob, End.withBuffer, bind, Except.bind]
  obtain ⟨s3, h3, h4⟩ : ∃ s3, st.notify e bx.progress = .ok s3 ∧ (s3.notify o obx.progress >>=
      fun s4 => if obx.remain = 0 then s4.getEnd o >>= fun z => pure (s4.setEnd o (z.withBuffer none))
        else pure s4) = .ok st1 := bind_ok.1 (hstep ▸ h)
  obtain ⟨h3n, h3b, h3o, h3e⟩ := notify_spec _ _ _ _ _ he h3
  obtain ⟨s4, h4n, hfin⟩ : ∃ s4, s3.notify o obx.progress = .ok s4 ∧ (if obx.remain = 0 then
      s4.getEnd o >>= fun z => pure (s4.setEnd o (z.withBuffer none)) else pure s4) = .ok st1 :=
    bind_ok.1 h4
  obtain ⟨h4n', h4b, h4o, h4e⟩ := notify_spec _ _ _ _ _ (by rw [h3o _ hoe, ho]) h4n
  have hframe : ∀ c, c ≠ e → c ≠ o → s4.ends c = st.ends c := fun c hce hco => by
    rw [h4o _ hco, h3o _ hce]
  have he4 : s4.ends e = some (x.withPending bx.progress) := by rw [h4o _ (Ne.symm hoe), h3e]
  by_cases h0 : obx.remain = 0
  · show st1.nBufs = st.nBufs ∧ _
    have hst1 : st1 = s4.setEnd o ((y.withPending obx.progress).withBuffer none) := by
      simpa [h0, getEnd, need, h4e, pure, Except.pure, bind, Except.bind, eq_comm] using hfin
    rw [hst1]
    exact ⟨h4n'.trans h3n, h4b.trans h3b, fun c hce hco => by simp [setEnd, upd, hco, hframe c hce hco],
      by simp [setEnd, upd, Ne.symm hoe, he4], by simp [setEnd, upd, h0]⟩
  · show st1.nBufs = st.nBufs ∧ _
    have hst1 : st1 = s4 := by simpa [h0, pure, Except.pure, eq_comm] using hfin
    rw [hst1]
    refine ⟨h4n'.trans h3n, h4b.trans h3b, hframe, he4, ?_⟩
    rw [h4e]
    cases y; simp [End.withBuffer, End.withPending, h0]

/-- **A copy that meets a parked buffer with room on both sides** runs case 3: the move, then
the notifications. -/
theorem copyEnd_meets_parked (st : Store α) (e b o ob : Nat) (x y : End) (bx obx : Buf α)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx)
    (htrap : (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) = false)
    (hpos : 0 < bx.remain) (hpos' : 0 < obx.remain) :
    st.copyEnd e b = ((st.setEnd e (x.withState .copying)).moveElems x.kind.isReadable e b o ob
      (min bx.remain obx.remain) >>= fun s => s.notifyBoth e b o ob) := by
  simp [copyEnd, getEnd, need, he, hxb, hxo, check, setEnd, upd, hoe, ho, hyb, getBuf, hb, hob,
    trapIf, htrap, hpos, hpos', End.withState, bind, Except.bind, pure, Except.pure]

/-- **Case 3 of `End.copy`, for every store**: `n = min` elements move; both ends get a
pending event with their buffers' cumulative progress; the copying end is `COPYING` without a
parked buffer; the peer's buffer stays parked unless it is full; no other end changes. -/
theorem copyEnd_transfer (st st1 : Store α) (e b o ob : Nat) (x y : End) (bx obx : Buf α)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx) (hbo : b ≠ ob)
    (htrap : (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) = false)
    (hpos : 0 < bx.remain) (hpos' : 0 < obx.remain)
    (hwf : (if x.kind.isReadable then obx else bx).ReadOk)
    (h : st.copyEnd e b = .ok st1) :
    st1.nBufs = st.nBufs ∧ (∀ c, c ≠ e → c ≠ o → st1.ends c = st.ends c) ∧
      st1.ends e = some ((x.withState .copying).withPending
        (bx.progress + min bx.remain obx.remain)) ∧
      st1.ends o = some ((y.withPending (obx.progress + min bx.remain obx.remain)).withBuffer
        (if obx.remain - min bx.remain obx.remain = 0 then none else some ob)) ∧
      (∀ c, c ≠ b → c ≠ ob → st1.bufs c = st.bufs c) ∧
      ∃ obx', st1.bufs ob = some obx' ∧
        obx'.progress = obx.progress + min bx.remain obx.remain ∧ obx'.length = obx.length := by
  have hsb : (st.setEnd e (x.withState .copying)).bufs b = some bx := hb
  have hsob : (st.setEnd e (x.withState .copying)).bufs ob = some obx := hob
  obtain ⟨s1, h1, h2⟩ : ∃ s1, (st.setEnd e (x.withState .copying)).moveElems x.kind.isReadable
      e b o ob (min bx.remain obx.remain) = .ok s1 ∧ s1.notifyBoth e b o ob = .ok st1 :=
    bind_ok.1 ((copyEnd_meets_parked st e b o ob x y bx obx he hxb hxo hoe ho hyb hb hob htrap
      hpos hpos').symm ▸ h)
  obtain ⟨h1n, h1e, h1b, ⟨bx', hbx', hp, hl⟩, ⟨obx', hobx', hop, hol⟩⟩ :=
    moveElems_spec _ _ _ _ _ _ _ _ _ _ hsb hsob hbo hwf h1
  have hs1e : s1.ends e = some (x.withState .copying) := by rw [h1e]; simp [setEnd, upd]
  have hs1o : s1.ends o = some y := by rw [h1e]; simp [setEnd, upd, hoe, ho]
  obtain ⟨hfn, hfb, hfr, hfe, hfo⟩ := notifyBoth_spec _ _ _ _ _ _ _ _ _ _ hs1e hs1o hoe hbx' hobx' h2
  have hrem : obx'.remain = obx.remain - min bx.remain obx.remain := by
    simp only [Buf.remain, hop, hol]; omega
  refine ⟨hfn.trans h1n, fun c hce hco => ?_, ?_, ?_, fun c hcb hcob => ?_, obx', ?_, hop, hol⟩
  · rw [hfr c hce hco, h1e]; simp [setEnd, upd, hce]
  · rw [hfe, hp]
  · rw [hfo, hop, hrem, hyb]
  · rw [hfb, h1b c hcb hcob]; rfl
  · rw [hfb, hobx']

/-- **Difference 2, general form**: when the copy has less room than the peer's parked buffer,
that buffer **stays parked**, with its progress advanced by the whole copy; the copying end
has its event pending (`COMPLETED` with its full length, once delivered). The store model
instead always completes the pending side (`streamRead_clears_pend`,
`streamWrite_clears_pend`). -/
theorem copyEnd_partial_keeps_parked (st st1 : Store α) (e b o ob : Nat) (x y : End)
    (bx obx : Buf α)
    (he : st.ends e = some x) (hxb : x.buffer = none) (hxo : x.other = some o) (hoe : o ≠ e)
    (ho : st.ends o = some y) (hyb : y.buffer = some ob)
    (hb : st.bufs b = some bx) (hob : st.bufs ob = some obx) (hbo : b ≠ ob)
    (htrap : (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) = false)
    (hpos : 0 < bx.remain) (hlt : bx.remain < obx.remain)
    (hwf : (if x.kind.isReadable then obx else bx).ReadOk)
    (h : st.copyEnd e b = .ok st1) :
    st1.ends o = some ((y.withPending (obx.progress + bx.remain)).withBuffer (some ob)) ∧
      st1.ends e = some ((x.withState .copying).withPending (bx.progress + bx.remain)) := by
  have hmin : min bx.remain obx.remain = bx.remain := Nat.min_eq_left (Nat.le_of_lt hlt)
  have hne : obx.remain - bx.remain ≠ 0 := by omega
  obtain ⟨-, -, hfe, hfo, -⟩ := copyEnd_transfer st st1 e b o ob x y bx obx he hxb hxo hoe ho hyb hb
    hob hbo htrap hpos (Nat.lt_trans hpos hlt) hwf h
  rw [hmin] at hfe hfo
  exact ⟨by simpa [hne] using hfo, hfe⟩

end Store

end Silmaril.Wasm.Component.Async.Cabi

namespace Silmaril.Wasm.Component.Async

/-- **Store model**: a `stream.read` meeting a pending write leaves no pending copy, whatever
the lengths. -/
theorem streamRead_clears_pend (st st1 : Store) (r n s hw : Nat) (xs : List Val) (res : Res)
    (hr : st.tbl r = some (.streamR s)) (hp : (st.chans s).pend = .write hw xs)
    (h : streamRead st r n = some (st1, res)) : (st1.chans s).pend = .idle := by
  simp only [streamRead, hr, hp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp [Store.post, Store.setChan, upd]

/-- **Store model**: a `stream.write` meeting a pending read leaves no pending copy, whatever
the lengths. -/
theorem streamWrite_clears_pend (st st1 : Store) (w s hr' n : Nat) (xs : List Val) (res : Res)
    (hw : st.tbl w = some (.streamW s)) (hp : (st.chans s).pend = .read hr' n)
    (h : streamWrite st w xs = some (st1, res)) : (st1.chans s).pend = .idle := by
  simp only [streamWrite, hw, hp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp [Store.post, Store.setChan, upd]

end Silmaril.Wasm.Component.Async
