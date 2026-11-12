module

public import Silmaril.Wasm.Component.Reference.Runtime.Stream.Properties.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Stream

/-!
# Invariants of the stream/future `End` state machine

Properties of the pure transcription of REF `End` (`Runtime/Stream.lean`;
`design/mvp/canonical-abi/definitions.py` L931-1098 at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>).

* `EndWF s`: every `other` link is symmetric and joins a readable end to the writable end of the
  same class (`EndKind.dual`), and a parked buffer only exists while the end is `COPYING` or
  `CANCELLING_COPY` (`End.BufOK`). `EndWF.other_iff` restates symmetry as
  `e.other = some f ↔ f.other = some e`.
* Preservation: `copy_EndWF`, `copyCore_EndWF`, `notify_EndWF`, `deliver_EndWF`,
  `takeEvent_EndWF`, `cancel_EndWF`, `forward_EndWF` (drop and splice branches),
  `dropEnd_EndWF`, `newStream_EndWF`, `newFuture_EndWF`; `empty_EndWF`.
* `EndWF` also requires that a `DONE` end has no pending event (`End.DoneQuiet`), which is what
  makes `DONE` absorbing under event delivery. Hence `notify_EndWF` assumes the notified end is
  not `DONE` and `deliver_EndWF` assumes its pending event was cleared (both hold at every REF
  call site; `takeEvent_EndWF` has no side condition).
* Done ends never re-enter copying. Per step, `KeepsDone s s'` (every `DONE` end of `s` is
  `DONE` in `s'`) holds for every operation: `copy_keepsDone`, `notify_keepsDone`,
  `cancel_keepsDone`, `dropEnd_keepsDone`, `newEnds_keepsDone`, and under `EndWF`
  `forward_keepsDone` and `takeEvent_keepsDone` (`deliver_keepsDone` for a non-`DONE` end).
  Over traces: `EndStep`/`EndSteps` collect the operations, `EndSteps.endWF` and
  `EndSteps.keepsDone` lift preservation, and `done_never_copying` gives `DoneStable s s'`
  (a `DONE` end of `s` is neither `COPYING` nor `CANCELLING_COPY` in `s'`) for every trace from
  a well-formed store. The single-step `*_doneStable` corollaries are also stated.
* Progress monotonicity (`BufProgressMono s s'`: a buffer parked on an end in both `s` and `s'`
  has not lost progress): `copy_progress_mono` (under `EndWF`), `notify_progress_mono`, bundled
  as `progress_mono`.
* `future_written_once`: after a copy that transfers a value out of a future's writable end,
  delivering that end's event makes it `DONE`, and a second write traps.

Everything is proved for all stores; nothing here is tested only. Not claimed: other invariants
tying pending events to states, handle tables, or the Prog layer's element transfer.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async

variable {E : CoreEngine}

theorem _root_.Silmaril.Wasm.Component.Async.EndState.copyingOrCancelling_iff (st : EndState) :
    st.copyingOrCancelling = true ↔ st = .copying ∨ st = .cancellingCopy := by
  cases st <;> decide

/-! ## Lookup lemmas -/

theorem end?_setEnd (s : CStore E) (e f : EndId) (x : End E) :
    (setEnd s e x).end? f = if e = f then (s.end? f).map (fun _ => x) else s.end? f :=
  ArenaField.ends.get?_set s e f x

theorem end?_setEnd_of {s : CStore E} {e : EndId} {x₀ : End E} (h : s.end? e = some x₀)
    (x : End E) (f : EndId) : (setEnd s e x).end? f = if f = e then some x else s.end? f := by
  rw [end?_setEnd]
  by_cases hf : f = e
  · subst hf; simp [h]
  · simp [hf, Ne.symm hf]

theorem end?_setEnd_self {s : CStore E} {e : EndId} {x₀ : End E} (h : s.end? e = some x₀)
    (x : End E) : (setEnd s e x).end? e = some x := by
  simp [end?_setEnd_of h]

theorem end?_setEnd_ne (s : CStore E) {e f : EndId} (x : End E) (h : f ≠ e) :
    (setEnd s e x).end? f = s.end? f := by
  rw [end?_setEnd]; simp [Ne.symm h]

theorem end?_of_ends_eq {s s' : CStore E} (h : s'.ends = s.ends) (e : EndId) :
    s'.end? e = s.end? e := by
  simp [CStore.end?, ArenaField.get?, ArenaField.ends, h]

theorem end?_newEnds (k : EndKind) (t : Option (WIT.ClosedType RtId)) (o : Option InstId)
    (s : CStore E) (f : EndId) :
    (newEnds k t o s).1.end? f =
      if f.idx = s.ends.length + 1 then
        some { kind := k.dual, t, owner := o, other := some ⟨s.ends.length⟩ }
      else if f.idx = s.ends.length then
        some { kind := k, t, owner := o, other := some ⟨s.ends.length + 1⟩ }
      else s.end? f := by
  simp only [newEnds, CStore.end?]
  rw [ArenaField.get?_alloc, ArenaField.get?_alloc]
  simp only [ArenaField.size, ArenaField.alloc, ArenaField.ends, Arena.alloc, List.length_append,
    List.length_singleton]
  rfl

theorem idx_lt_of_end? {s : CStore E} {e : EndId} {x : End E} (h : s.end? e = some x) :
    e.idx < s.ends.length := by
  have h' : (ArenaField.ends.get? s e).isSome = true := by
    rw [show ArenaField.ends.get? s e = s.end? e from rfl, h]; rfl
  exact (ArenaField.get?_isSome_iff ArenaField.ends s e).1 h'

/-! ## `EndWF` -/

namespace EndWF

theorem ne_of_other {s : CStore E} (hw : EndWF s) {e f : EndId} {x : End E}
    (he : s.end? e = some x) (ho : x.other = some f) : f ≠ e := by
  rintro rfl
  obtain ⟨y, hy, -, hk⟩ := hw.paired _ x _ he ho
  rw [he] at hy; cases hy
  exact x.kind.dual_ne hk.symm

/-- Symmetry of links, as an iff. -/
theorem other_iff {s : CStore E} (hw : EndWF s) {e f : EndId} {x y : End E}
    (he : s.end? e = some x) (hf : s.end? f = some y) :
    x.other = some f ↔ y.other = some e := by
  constructor
  · intro h
    obtain ⟨y', hy', h', -⟩ := hw.paired e x f he h
    rw [hf] at hy'; cases hy'; exact h'
  · intro h
    obtain ⟨x', hx', h', -⟩ := hw.paired f y e hf h
    rw [he] at hx'; cases hx'; exact h'

/-- Replacing an end by one with the same link and class preserves `EndWF`. -/
theorem setEnd {s : CStore E} (hw : EndWF s) {e : EndId} {x x' : End E}
    (he : s.end? e = some x) (ho : x'.other = x.other) (hk : x'.kind = x.kind) (hb : x'.BufOK)
    (hq : x'.DoneQuiet) : EndWF (Runtime.setEnd s e x') := by
  constructor
  · intro f z hz
    rw [end?_setEnd_of he] at hz
    split at hz
    · cases hz; exact hb
    · exact hw.bufOK f z hz
  · intro f z hz
    rw [end?_setEnd_of he] at hz
    split at hz
    · cases hz; exact hq
    · exact hw.doneQuiet f z hz
  · intro f z g hz hg
    rw [end?_setEnd_of he] at hz
    split at hz
    · rename_i hfe
      subst hfe; cases hz
      rw [ho] at hg
      have hge := hw.ne_of_other he hg
      obtain ⟨y, hy, hyo, hyk⟩ := hw.paired _ x g he hg
      refine ⟨y, ?_, hyo, by rw [hk]; exact hyk⟩
      rw [end?_setEnd_ne _ _ hge]; exact hy
    · rename_i hfe
      obtain ⟨y, hy, hyo, hyk⟩ := hw.paired f z g hz hg
      by_cases hge : g = e
      · subst hge
        rw [he] at hy; cases hy
        exact ⟨x', end?_setEnd_self he _, ho ▸ hyo, hk ▸ hyk⟩
      · exact ⟨y, by rw [end?_setEnd_ne _ _ hge]; exact hy, hyo, hyk⟩

theorem of_ends_eq {s s' : CStore E} (hw : EndWF s) (h : s'.ends = s.ends) : EndWF s' := by
  constructor
  · intro e x hx; rw [end?_of_ends_eq h] at hx; exact hw.bufOK e x hx
  · intro e x hx; rw [end?_of_ends_eq h] at hx; exact hw.doneQuiet e x hx
  · intro e x f hx ho
    rw [end?_of_ends_eq h] at hx
    obtain ⟨y, hy, h1, h2⟩ := hw.paired e x f hx ho
    exact ⟨y, by rw [end?_of_ends_eq h]; exact hy, h1, h2⟩

/-- Unlinking a pair of ends preserves `EndWF`. -/
theorem unlink {s : CStore E} (hw : EndWF s) {e o : EndId} {x y : End E}
    (he : s.end? e = some x) (hx : x.other = some o) (ho : s.end? o = some y)
    {x' y' : End E} (hx' : x'.other = none) (hy' : y'.other = none)
    (hbx : x'.BufOK) (hby : y'.BufOK) (hqx : x'.DoneQuiet) (hqy : y'.DoneQuiet) :
    EndWF (Runtime.setEnd (Runtime.setEnd s o y') e x') := by
  have hoe : o ≠ e := hw.ne_of_other he hx
  have hyo : y.other = some e := (hw.other_iff he ho).1 hx
  have hlook : ∀ f, (Runtime.setEnd (Runtime.setEnd s o y') e x').end? f =
      if f = e then some x' else if f = o then some y' else s.end? f := by
    intro f
    have h1 : (Runtime.setEnd s o y').end? e = some x := by
      rw [end?_setEnd_ne _ _ (Ne.symm hoe)]; exact he
    rw [end?_setEnd_of h1, end?_setEnd_of ho]
  constructor
  · intro f z hz
    rw [hlook] at hz
    split at hz
    · cases hz; exact hbx
    · split at hz
      · cases hz; exact hby
      · exact hw.bufOK f z hz
  · intro f z hz
    rw [hlook] at hz
    split at hz
    · cases hz; exact hqx
    · split at hz
      · cases hz; exact hqy
      · exact hw.doneQuiet f z hz
  · intro f z g hz hg
    rw [hlook] at hz
    split at hz
    · cases hz; rw [hx'] at hg; cases hg
    · split at hz
      · cases hz; rw [hy'] at hg; cases hg
      · rename_i h1 h2
        obtain ⟨w, hw1, hw2, hw3⟩ := hw.paired f z g hz hg
        have hge : g ≠ e := by
          rintro rfl; rw [he] at hw1; cases hw1; rw [hx] at hw2; cases hw2; exact h2 rfl
        have hgo : g ≠ o := by
          rintro rfl; rw [ho] at hw1; cases hw1; rw [hyo] at hw2; cases hw2; exact h1 rfl
        refine ⟨w, ?_, hw2, hw3⟩
        rw [hlook, ite_eq_right hge, ite_eq_right hgo]; exact hw1

/-- Splicing `W = src.other` to `R = dst.other` and unlinking `src`, `dst` preserves `EndWF`. -/
theorem splice {s : CStore E} (hw : EndWF s) {src dst w r : EndId} {xs xd yw yr : End E}
    (hs : s.end? src = some xs) (hd : s.end? dst = some xd) (hW : s.end? w = some yw)
    (hR : s.end? r = some yr) (hsw : xs.other = some w) (hdr : xd.other = some r)
    (hk : xd.kind = xs.kind.dual) (hwd : w ≠ dst) (hwr : w ≠ r)
    {xs' xd' yw' yr' : End E} (hxs' : xs'.other = none) (hxd' : xd'.other = none)
    (hyw' : yw'.other = some r) (hyr' : yr'.other = some w)
    (hkw : yw'.kind = yw.kind) (hkr : yr'.kind = yr.kind)
    (hbs : xs'.BufOK) (hbd : xd'.BufOK) (hbw : yw'.BufOK) (hbr : yr'.BufOK)
    (hqs : xs'.DoneQuiet) (hqd : xd'.DoneQuiet) (hqw : yw'.DoneQuiet) (hqr : yr'.DoneQuiet) :
    EndWF (Runtime.setEnd (Runtime.setEnd (Runtime.setEnd (Runtime.setEnd s src xs') dst xd')
      w yw') r yr') := by
  have hws : w ≠ src := hw.ne_of_other hs hsw
  have hrd : r ≠ dst := hw.ne_of_other hd hdr
  obtain ⟨yw₀, hyw₀, hywo, hywk⟩ := hw.paired _ _ _ hs hsw
  rw [hW] at hyw₀; cases hyw₀
  obtain ⟨yr₀, hyr₀, hyro, hyrk⟩ := hw.paired _ _ _ hd hdr
  rw [hR] at hyr₀; cases hyr₀
  have hrs : r ≠ src := by
    rintro rfl; rw [hs] at hR; cases hR; rw [hsw] at hyro; cases hyro; exact hwd rfl
  have hsd : src ≠ dst := by
    rintro rfl; rw [hs] at hd; cases hd; exact xs.kind.dual_ne hk.symm
  have hlook : ∀ f, (Runtime.setEnd (Runtime.setEnd (Runtime.setEnd (Runtime.setEnd s src xs')
      dst xd') w yw') r yr').end? f =
      if f = r then some yr' else if f = w then some yw' else if f = dst then some xd'
      else if f = src then some xs' else s.end? f := by
    intro f
    have h1 : (Runtime.setEnd s src xs').end? dst = some xd := by
      rw [end?_setEnd_ne _ _ (Ne.symm hsd)]; exact hd
    have h2 : (Runtime.setEnd (Runtime.setEnd s src xs') dst xd').end? w = some yw := by
      rw [end?_setEnd_ne _ _ hwd, end?_setEnd_ne _ _ hws]; exact hW
    have h3 : (Runtime.setEnd (Runtime.setEnd (Runtime.setEnd s src xs') dst xd') w yw').end? r
        = some yr := by
      rw [end?_setEnd_ne _ _ (Ne.symm hwr), end?_setEnd_ne _ _ hrd, end?_setEnd_ne _ _ hrs]
      exact hR
    rw [end?_setEnd_of h3, end?_setEnd_of h2, end?_setEnd_of h1, end?_setEnd_of hs]
  constructor
  · intro f z hz
    rw [hlook] at hz
    split at hz
    · cases hz; exact hbr
    split at hz
    · cases hz; exact hbw
    split at hz
    · cases hz; exact hbd
    split at hz
    · cases hz; exact hbs
    exact hw.bufOK f z hz
  · intro f z hz
    rw [hlook] at hz
    split at hz
    · cases hz; exact hqr
    split at hz
    · cases hz; exact hqw
    split at hz
    · cases hz; exact hqd
    split at hz
    · cases hz; exact hqs
    exact hw.doneQuiet f z hz
  · intro f z g hz hg
    rw [hlook] at hz
    split at hz
    · rename_i hfr; subst hfr; cases hz; rw [hyr'] at hg; cases hg
      refine ⟨yw', ?_, hyw', ?_⟩
      · rw [hlook, ite_eq_right hwr, ite_eq_left rfl]
      · rw [hkw, hkr, hywk, hyrk, hk, EndKind.dual_dual]
    split at hz
    · rename_i _ hfw; subst hfw; cases hz; rw [hyw'] at hg; cases hg
      refine ⟨yr', ?_, hyr', ?_⟩
      · rw [hlook, ite_eq_left rfl]
      · rw [hkw, hkr, hywk, hyrk, hk, EndKind.dual_dual]
    split at hz
    · cases hz; rw [hxd'] at hg; cases hg
    split at hz
    · cases hz; rw [hxs'] at hg; cases hg
    rename_i h1 h2 h3 h4
    obtain ⟨y, hy1, hy2, hy3⟩ := hw.paired f z g hz hg
    have hgr : g ≠ r := by
      rintro rfl; rw [hR] at hy1; cases hy1; rw [hyro] at hy2; cases hy2; exact h3 rfl
    have hgw : g ≠ w := by
      rintro rfl; rw [hW] at hy1; cases hy1; rw [hywo] at hy2; cases hy2; exact h4 rfl
    have hgd : g ≠ dst := by
      rintro rfl; rw [hd] at hy1; cases hy1; rw [hdr] at hy2; cases hy2; exact h1 rfl
    have hgs : g ≠ src := by
      rintro rfl; rw [hs] at hy1; cases hy1; rw [hsw] at hy2; cases hy2; exact h2 rfl
    refine ⟨y, ?_, hy2, hy3⟩
    rw [hlook, ite_eq_right hgr, ite_eq_right hgw, ite_eq_right hgd, ite_eq_right hgs]; exact hy1

end EndWF

theorem empty_EndWF : EndWF (CStore.empty : CStore E) := by
  constructor
  · intro e x h; simp [CStore.end?, ArenaField.get?, ArenaField.ends, Arena.get?] at h
  · intro e x h; simp [CStore.end?, ArenaField.get?, ArenaField.ends, Arena.get?] at h
  · intro e x f h; simp [CStore.end?, ArenaField.get?, ArenaField.ends, Arena.get?] at h

/-! ## Preservation of `EndWF` -/

theorem End.deliverStep_pending (x : End E) (p : Nat) :
    (x.deliverStep p).1.common.pending = x.common.pending := by
  unfold deliverStep; split
  · split <;> (try split) <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem End.doneQuiet_of_ne {x : End E} (h : x.state ≠ .done) : x.DoneQuiet :=
  fun hd => absurd hd h

theorem End.dropPeer_doneQuiet {y : End E} (o : EndId) (h : y.DoneQuiet) :
    (y.dropPeer o).DoneQuiet := by
  unfold End.dropPeer; split
  · rename_i hc; intro hd; exact absurd hd hc.1
  · exact h

/-- `notify` preserves `EndWF` when the notified end is not `DONE` (REF only notifies an end
that is copying, or, in `End.drop`, a peer that is not `DONE`). -/
theorem notify_EndWF {s : CStore E} (hw : EndWF s) (e : EndId) (p : Nat)
    (hnd : ∀ x, s.end? e = some x → x.state ≠ .done) : EndWF (notify e p s) := by
  unfold notify
  split
  · rename_i x hx
    exact hw.setEnd hx rfl rfl (by simpa [End.BufOK] using hw.bufOK e x hx)
      (End.doneQuiet_of_ne (hnd x hx))
  · exact hw

/-- Running an end's event closure preserves `EndWF` once the pending event has been cleared
(as `get_pending_event`/`takeEvent` does before running it). -/
theorem deliver_EndWF {s : CStore E} (hw : EndWF s) (e : EndId) (p : Nat)
    (hp : ∀ x, s.end? e = some x → x.common.pending = none) : EndWF (deliver e p s).1 := by
  unfold deliver
  split
  · exact hw
  · rename_i x hx
    exact hw.setEnd hx (End.deliverStep_other x p) (End.deliverStep_kind x p)
      (by simp [End.BufOK, End.deliverStep_buffer])
      (fun _ => by rw [End.deliverStep_pending]; exact hp x hx)

theorem takeEvent_EndWF {s : CStore E} (hw : EndWF s) (e : EndId) : EndWF (takeEvent e s).1 := by
  unfold takeEvent
  split
  · exact hw
  · rename_i x hx
    have h1 : EndWF (setEnd s e x.clearPending) :=
      hw.setEnd hx rfl rfl (by simpa [End.BufOK] using hw.bufOK e x hx) (fun _ => rfl)
    have hp : ∀ y, (setEnd s e x.clearPending).end? e = some y → y.common.pending = none :=
      fun y hy => by rw [end?_setEnd_self hx] at hy; cases hy; rfl
    split
    · exact deliver_EndWF h1 _ _ hp
    · exact deliver_EndWF h1 _ _ hp
    · exact hw

theorem cancel_EndWF {s : CStore E} (hw : EndWF s) (e : EndId) (b : Bool) :
    EndWF (cancel e b s) := by
  unfold cancel
  split
  · exact hw
  · rename_i x hx
    split
    · exact hw
    · split
      · exact hw.setEnd hx rfl rfl (by simp [End.BufOK, EndState.copyingOrCancelling])
          (by intro h; cases h)
      · exact hw.setEnd hx rfl rfl (by simp [End.BufOK, EndState.copyingOrCancelling])
          (by intro h; cases h)

theorem copyCore_EndWF {s s' : CStore E} {e : EndId} {buf : BufferDesc E} {isRead : Bool}
    {a : CopyAction E} (hw : EndWF s) (h : copyCore e buf isRead s = .ok (s', a)) :
    EndWF s' := by
  unfold copyCore at h
  split at h
  · cases h
  rename_i x hx
  split at h
  · cases h
  have hbc : ∀ x' : End E, x'.state = .copying → x'.BufOK := by
    intro x' hs; simp [End.BufOK, hs, EndState.copyingOrCancelling]
  have hqc : ∀ x' : End E, x'.state = .copying → x'.DoneQuiet := by
    intro x' hs hd; rw [hs] at hd; cases hd
  split at h
  · cases h; exact hw.setEnd hx (by rfl) (by rfl) (hbc _ (by rfl)) (hqc _ (by rfl))
  rename_i o ho
  split at h
  · cases h
  rename_i hoe
  split at h
  · cases h
  rename_i y hy
  have hy1 : ∀ x' : End E, (setEnd s e x').end? o = some y := fun x' => by
    rw [end?_setEnd_ne _ _ hoe]; exact hy
  split at h
  · cases h; exact hw.setEnd hx (by rfl) (by rfl) (hbc _ (by rfl)) (hqc _ (by rfl))
  rename_i ob hob
  have hyc : y.state.copyingOrCancelling = true := hw.bufOK o y hy (by simp [hob])
  split at h
  · split at h
    · cases h
    · cases h
      refine (hw.setEnd hx (by rfl) (by rfl) (hbc _ (by rfl)) (hqc _ (by rfl))).setEnd (hy1 _)
        (by rfl) (by rfl) ?_ ?_
      · intro _; simpa using hyc
      · intro hd; have hd' : y.state = .done := hd; rw [hd'] at hyc; cases hyc
  · split at h
    · cases h
      refine (hw.setEnd hx (by rfl) (by rfl) (hbc _ (by rfl)) (hqc _ (by rfl))).setEnd (hy1 _)
        (by rfl) (by rfl) (by simp [End.BufOK]) ?_
      intro hd; have hd' : y.state = .done := hd; rw [hd'] at hyc; cases hyc
    · cases h; exact hw.setEnd hx (by rfl) (by rfl) (hbc _ (by rfl)) (hqc _ (by rfl))

theorem copy_EndWF {s s' : CStore E} {e : EndId} {buf : BufferDesc E} {isRead : Bool}
    {a : CopyAction E} (hw : EndWF s) (h : copy e buf isRead s = .ok (s', a)) : EndWF s' := by
  unfold copy at h
  split at h
  · cases h
  split at h
  · exact copyCore_EndWF hw h
  all_goals cases h

theorem dropEnd_EndWF {s : CStore E} (hw : EndWF s) (e : EndId) : EndWF (dropEnd e s) := by
  unfold dropEnd
  split
  · exact hw
  rename_i x hx
  refine EndWF.of_ends_eq ?_ (leaveSet_ends _ _ _)
  split
  · rename_i ho
    exact hw.setEnd hx (by simp [ho]) rfl (by simpa [End.BufOK] using hw.bufOK e x hx)
      (hw.doneQuiet e x hx)
  · rename_i o ho
    split
    · rename_i hoe; exact absurd hoe (hw.ne_of_other hx ho)
    split
    · rename_i hy
      obtain ⟨y, hy', -⟩ := hw.paired e x o hx ho
      rw [hy] at hy'; cases hy'
    rename_i y hy
    refine hw.unlink hx ho hy rfl (End.dropPeer_other y o)
      (by simpa [End.BufOK] using hw.bufOK e x hx) ?_ (hw.doneQuiet e x hx)
      (End.dropPeer_doneQuiet o (hw.doneQuiet o y hy))
    have := hw.bufOK o y hy
    simpa [End.BufOK, End.dropPeer_buffer, End.dropPeer_state] using this

theorem forward_EndWF {s s' : CStore E} {src dst : EndId} {a : CopyAction E} (hw : EndWF s)
    (h : forward src dst s = .ok (s', a)) : EndWF s' := by
  unfold forward at h
  split at h
  · rename_i xs xd hs hd
    split at h
    · cases h
    rename_i hkind
    have hk : xd.kind = xs.kind.dual := by
      by_contra hc; exact hkind (.inr hc)
    split at h
    · rename_i w r hsw hdr
      split at h
      · cases h; exact dropEnd_EndWF (dropEnd_EndWF hw _) _
      rename_i hwd
      split at h
      · cases h
      rename_i hbad
      have hwr : w ≠ r := fun h' => hbad (.inr (.inr (.inr h')))
      split at h
      · rename_i yw yr hW hR
        have hbw := hw.bufOK w yw hW
        have hbr := hw.bufOK r yr hR
        have hbs := hw.bufOK src xs hs
        have hbd := hw.bufOK dst xd hd
        have hqs := hw.doneQuiet src xs hs
        have hqd := hw.doneQuiet dst xd hd
        have hqw := hw.doneQuiet w yw hW
        have hqr := hw.doneQuiet r yr hR
        split at h
        · rename_i bw br hbw' hbr'
          split at h
          · refine copyCore_EndWF ?_ h
            exact hw.splice hs hd hW hR hsw hdr hk hwd hwr rfl rfl rfl rfl rfl rfl
              (by simpa [End.BufOK] using hbs) (by simpa [End.BufOK] using hbd)
              (by simp [End.BufOK]) (by simpa [End.BufOK] using hbr)
              hqs hqd hqw hqr
          · refine copyCore_EndWF ?_ h
            exact hw.splice hs hd hW hR hsw hdr hk hwd hwr rfl rfl rfl rfl rfl rfl
              (by simpa [End.BufOK] using hbs) (by simpa [End.BufOK] using hbd)
              (by simpa [End.BufOK] using hbw) (by simp [End.BufOK])
              hqs hqd hqw hqr
        · cases h
          exact hw.splice hs hd hW hR hsw hdr hk hwd hwr rfl rfl rfl rfl rfl rfl
            (by simpa [End.BufOK] using hbs) (by simpa [End.BufOK] using hbd)
            (by simpa [End.BufOK] using hbw) (by simpa [End.BufOK] using hbr)
            hqs hqd hqw hqr
      · cases h
    · cases h; exact dropEnd_EndWF (dropEnd_EndWF hw _) _
  · cases h

theorem newEnds_EndWF {s : CStore E} (hw : EndWF s) (k : EndKind)
    (t : Option (WIT.ClosedType RtId)) (o : Option InstId) : EndWF (newEnds k t o s).1 := by
  constructor
  · intro f z hz
    rw [end?_newEnds] at hz
    split at hz
    · cases hz; simp [End.BufOK]
    split at hz
    · cases hz; simp [End.BufOK]
    exact hw.bufOK f z hz
  · intro f z hz
    rw [end?_newEnds] at hz
    split at hz
    · cases hz; intro h; cases h
    split at hz
    · cases hz; intro h; cases h
    exact hw.doneQuiet f z hz
  · intro f z g hz hg
    rw [end?_newEnds] at hz
    split at hz
    · cases hz; cases hg
      refine ⟨{ kind := k, t, owner := o, other := some ⟨s.ends.length + 1⟩ }, ?_, ?_, by simp⟩
      · rw [end?_newEnds]; simp
      · rename_i hf; cases f; simp_all
    split at hz
    · cases hz; cases hg
      refine ⟨{ kind := k.dual, t, owner := o, other := some ⟨s.ends.length⟩ }, ?_, ?_, rfl⟩
      · rw [end?_newEnds]; simp
      · rename_i _ hf; cases f; simp_all
    rename_i h1 h2
    obtain ⟨y, hy1, hy2, hy3⟩ := hw.paired f z g hz hg
    have hlt := idx_lt_of_end? hy1
    refine ⟨y, ?_, hy2, hy3⟩
    rw [end?_newEnds, ite_eq_right (by omega), ite_eq_right (by omega)]; exact hy1

theorem newStream_EndWF {s : CStore E} (hw : EndWF s) (t : Option (WIT.ClosedType RtId))
    (o : Option InstId) : EndWF (newStream t o s).1 := newEnds_EndWF hw _ t o

theorem newFuture_EndWF {s : CStore E} (hw : EndWF s) (t : Option (WIT.ClosedType RtId))
    (o : Option InstId) : EndWF (newFuture t o s).1 := newEnds_EndWF hw _ t o

/-! ## Done ends never re-enter copying -/

namespace KeepsDone

theorem trans {s₁ s₂ s₃ : CStore E} (h₁ : KeepsDone s₁ s₂) (h₂ : KeepsDone s₂ s₃) :
    KeepsDone s₁ s₃ := fun e x hx hd =>
  let ⟨y, hy, hyd⟩ := h₁ e x hx hd
  h₂ e y hy hyd

theorem doneStable {s s' : CStore E} (h : KeepsDone s s') : DoneStable s s' := by
  intro e x y hx hd hy
  obtain ⟨z, hz, hzd⟩ := h e x hx hd
  rw [hy] at hz; cases hz; simp [hzd, EndState.copyingOrCancelling]

theorem trans_doneStable {s₁ s₂ s₃ : CStore E} (h₁ : KeepsDone s₁ s₂) (h₂ : DoneStable s₂ s₃) :
    DoneStable s₁ s₃ := by
  intro e x y hx hd hy
  obtain ⟨z, hz, hzd⟩ := h₁ e x hx hd
  exact h₂ e z y hz hzd hy

theorem setEnd {s : CStore E} {e : EndId} {x' : End E}
    (h : ∀ x, s.end? e = some x → x.state = .done → x'.state = .done) :
    KeepsDone s (Runtime.setEnd s e x') := by
  intro f x hx hd
  by_cases hf : f = e
  · subst hf; exact ⟨x', end?_setEnd_self hx _, h x hx hd⟩
  · rw [end?_setEnd_ne _ _ hf]; exact ⟨x, hx, hd⟩

theorem of_ends_eq {s s' : CStore E} (h : s'.ends = s.ends) : KeepsDone s s' := by
  intro e x hx hd; exact ⟨x, by rw [end?_of_ends_eq h]; exact hx, hd⟩

end KeepsDone

theorem eq_of_end?_setEnd_self {s : CStore E} {e : EndId} {x' z : End E}
    (h : (setEnd s e x').end? e = some z) : z = x' := by
  rw [end?_setEnd] at h; simp only [ite_true, Option.map_eq_some_iff] at h
  obtain ⟨_, -, h⟩ := h; exact h.symm

theorem end?_setEnd_ne_of {s : CStore E} {e f : EndId} {x' z : End E}
    (h : (setEnd s e x').end? f = some z) (hf : f ≠ e) : s.end? f = some z := by
  rwa [end?_setEnd_ne _ _ hf] at h

theorem notify_keepsDone (s : CStore E) (e : EndId) (p : Nat) : KeepsDone s (notify e p s) := by
  unfold notify; split
  · rename_i x hx; exact KeepsDone.setEnd fun y hy hd => by rw [hx] at hy; cases hy; exact hd
  · exact .refl s

theorem notify_doneStable (s : CStore E) (e : EndId) (p : Nat) : DoneStable s (notify e p s) :=
  (notify_keepsDone s e p).doneStable

theorem deliver_doneStable (s : CStore E) (e : EndId) (p : Nat) :
    DoneStable s (deliver e p s).1 := by
  unfold deliver; split
  · exact (KeepsDone.refl s).doneStable
  · rename_i x hx
    intro f z y hz hd hy
    by_cases hf : f = e
    · subst hf
      rw [eq_of_end?_setEnd_self hy]
      rcases End.deliverStep_state x p with h | h <;> simp [h, EndState.copyingOrCancelling]
    · rw [end?_setEnd_ne _ _ hf, hz] at hy; cases hy
      simp [hd, EndState.copyingOrCancelling]

theorem takeEvent_doneStable (s : CStore E) (e : EndId) : DoneStable s (takeEvent e s).1 := by
  unfold takeEvent; split
  · exact (KeepsDone.refl s).doneStable
  · rename_i x hx
    have h1 : KeepsDone s (setEnd s e x.clearPending) :=
      KeepsDone.setEnd fun y hy hd => by rw [hx] at hy; cases hy; exact hd
    split
    · exact h1.trans_doneStable (deliver_doneStable _ _ _)
    · exact h1.trans_doneStable (deliver_doneStable _ _ _)
    · exact (KeepsDone.refl s).doneStable

theorem cancel_keepsDone (s : CStore E) (e : EndId) (b : Bool) : KeepsDone s (cancel e b s) := by
  unfold cancel; split
  · exact .refl s
  · rename_i x hx
    split
    · exact .refl s
    · rename_i hc
      have : ∀ y, s.end? e = some y → y.state = .done → False := by
        intro y hy hd; rw [hx] at hy; cases hy; rw [hd] at hc; exact hc (by decide)
      split
      · exact KeepsDone.setEnd fun y hy hd => (this y hy hd).elim
      · exact KeepsDone.setEnd fun y hy hd => (this y hy hd).elim

theorem cancel_doneStable (s : CStore E) (e : EndId) (b : Bool) : DoneStable s (cancel e b s) :=
  (cancel_keepsDone s e b).doneStable

theorem copyCore_keepsDone {s s' : CStore E} {e : EndId} {buf : BufferDesc E} {isRead : Bool}
    {a : CopyAction E} (hne : ∀ x, s.end? e = some x → x.state ≠ .done)
    (h : copyCore e buf isRead s = .ok (s', a)) : KeepsDone s s' := by
  unfold copyCore at h
  split at h
  · cases h
  rename_i x hx
  have hk : ∀ x' : End E, KeepsDone s (setEnd s e x') := fun x' =>
    KeepsDone.setEnd fun y hy hd => (hne y hy hd).elim
  split at h
  · cases h
  split at h
  · cases h; exact hk _
  rename_i o _
  split at h
  · cases h
  rename_i hoe
  split at h
  · cases h
  rename_i y hy
  have hy1 : ∀ x' y' : End E, y'.state = y.state →
      KeepsDone (setEnd s e x') (setEnd (setEnd s e x') o y') := fun x' y' hs =>
    KeepsDone.setEnd fun z hz hd => by
      rw [end?_setEnd_ne _ _ hoe, hy] at hz; cases hz; rw [hs]; exact hd
  split at h
  · cases h; exact hk _
  split at h
  · split at h
    · cases h
    · cases h; exact (hk _).trans (hy1 _ _ rfl)
  · split at h
    · cases h; exact (hk _).trans (hy1 _ _ rfl)
    · cases h; exact hk _

theorem copy_keepsDone {s s' : CStore E} {e : EndId} {buf : BufferDesc E} {isRead : Bool}
    {a : CopyAction E} (h : copy e buf isRead s = .ok (s', a)) : KeepsDone s s' := by
  unfold copy at h
  split at h
  · cases h
  rename_i x hx
  split at h
  · rename_i hs
    exact copyCore_keepsDone (fun y hy => by rw [hx] at hy; cases hy; rw [hs]; decide) h
  all_goals cases h

theorem copy_doneStable {s s' : CStore E} {e : EndId} {buf : BufferDesc E} {isRead : Bool}
    {a : CopyAction E} (h : copy e buf isRead s = .ok (s', a)) : DoneStable s s' :=
  (copy_keepsDone h).doneStable

theorem dropEnd_keepsDone (s : CStore E) (e : EndId) : KeepsDone s (dropEnd e s) := by
  unfold dropEnd
  split
  · exact .refl s
  rename_i x hx
  refine KeepsDone.trans ?_ (KeepsDone.of_ends_eq (leaveSet_ends _ _ _))
  have hself : ∀ s₁ : CStore E, s₁.end? e = some x →
      KeepsDone s₁ (setEnd s₁ e { x with other := none, common := { x.common with wset := none } })
      := fun s₁ h₁ => KeepsDone.setEnd fun y hy hd => by rw [h₁] at hy; cases hy; exact hd
  split
  · exact hself s hx
  · rename_i o _
    split
    · exact hself s hx
    split
    · exact hself s hx
    rename_i y hy
    by_cases hoe : o = e
    · subst hoe; rw [hx] at hy; cases hy
      refine (KeepsDone.setEnd fun z hz hd => ?_).trans
        (KeepsDone.setEnd fun z hz hd => ?_)
      · rw [hx] at hz; cases hz; rw [End.dropPeer_state]; exact hd
      · have := eq_of_end?_setEnd_self hz; subst this
        rw [End.dropPeer_state] at hd; exact hd
    · refine (KeepsDone.setEnd fun z hz hd => ?_).trans (hself _ ?_)
      · rw [hy] at hz; cases hz; rw [End.dropPeer_state]; exact hd
      · rw [end?_setEnd_ne _ _ (Ne.symm hoe)]; exact hx

theorem dropEnd_doneStable (s : CStore E) (e : EndId) : DoneStable s (dropEnd e s) :=
  (dropEnd_keepsDone s e).doneStable

/-- Forwarding keeps DONE ends DONE (the re-issued copy runs on an end with a parked buffer, which
is copying by `EndWF`). -/
theorem forward_keepsDone {s s' : CStore E} {src dst : EndId} {a : CopyAction E} (hw : EndWF s)
    (h : forward src dst s = .ok (s', a)) : KeepsDone s s' := by
  unfold forward at h
  split at h
  · rename_i xs xd hs hd
    split at h
    · cases h
    rename_i hkind
    have hk : xd.kind = xs.kind.dual := by
      by_contra hc; exact hkind (.inr hc)
    split at h
    · rename_i w r hsw hdr
      split at h
      · cases h; exact (dropEnd_keepsDone _ _).trans (dropEnd_keepsDone _ _)
      rename_i hwd
      split at h
      · cases h
      rename_i hbad
      have hwr : w ≠ r := fun h' => hbad (.inr (.inr (.inr h')))
      have hrs : r ≠ src := fun h' => hbad (.inl h')
      have hws : w ≠ src := hw.ne_of_other hs hsw
      have hrd : r ≠ dst := hw.ne_of_other hd hdr
      have hsd : dst ≠ src := by
        rintro rfl; rw [hs] at hd; cases hd; exact xs.kind.dual_ne hk.symm
      split at h
      · rename_i yw yr hW hR
        have hany : ∀ (e : EndId) (x₀ x' : End E) (s₁ : CStore E), s₁.end? e = some x₀ →
            x'.state = x₀.state → KeepsDone s₁ (setEnd s₁ e x') :=
          fun e x₀ x' s₁ hx hs' => KeepsDone.setEnd fun y hy hd' => by
            rw [hx] at hy; cases hy; rw [hs']; exact hd'
        have h4 : ∀ (xs' xd' yw' yr' : End E), xs'.state = xs.state → xd'.state = xd.state →
            yw'.state = yw.state → yr'.state = yr.state →
            KeepsDone s (setEnd (setEnd (setEnd (setEnd s src xs') dst xd') w yw') r yr') := by
          intro xs' xd' yw' yr' h1 h2 h3 h4
          refine (hany _ _ _ _ hs h1).trans ((hany _ _ _ _ ?_ h2).trans
            ((hany _ _ _ _ ?_ h3).trans (hany _ _ _ _ ?_ h4)))
          · rw [end?_setEnd_ne _ _ hsd]; exact hd
          · rw [end?_setEnd_ne _ _ hwd, end?_setEnd_ne _ _ hws]; exact hW
          · rw [end?_setEnd_ne _ _ (Ne.symm hwr), end?_setEnd_ne _ _ hrd,
              end?_setEnd_ne _ _ hrs]; exact hR
        split at h
        · rename_i bw br hbw hbr
          split at h
          · refine (h4 _ _ _ _ (by rfl) (by rfl) (by rfl) (by rfl)).trans (copyCore_keepsDone ?_ h)
            intro z hz
            rw [end?_setEnd_ne _ _ hwr] at hz
            have := eq_of_end?_setEnd_self hz; subst this
            have hc := hw.bufOK w yw hW (by simp [hbw])
            intro hd'; have h' : yw.state = .done := hd'
            rw [h'] at hc; exact absurd hc (by decide)
          · refine (h4 _ _ _ _ (by rfl) (by rfl) (by rfl) (by rfl)).trans (copyCore_keepsDone ?_ h)
            intro z hz
            have := eq_of_end?_setEnd_self hz; subst this
            have hc := hw.bufOK r yr hR (by simp [hbr])
            intro hd'; have h' : yr.state = .done := hd'
            rw [h'] at hc; exact absurd hc (by decide)
        · cases h; exact h4 _ _ _ _ (by rfl) (by rfl) (by rfl) (by rfl)
      · cases h
    · cases h; exact (dropEnd_keepsDone _ _).trans (dropEnd_keepsDone _ _)
  · cases h

theorem forward_doneStable {s s' : CStore E} {src dst : EndId} {a : CopyAction E} (hw : EndWF s)
    (h : forward src dst s = .ok (s', a)) : DoneStable s s' :=
  (forward_keepsDone hw h).doneStable

theorem newEnds_keepsDone (s : CStore E) (k : EndKind) (t : Option (WIT.ClosedType RtId))
    (o : Option InstId) : KeepsDone s (newEnds k t o s).1 := by
  intro f x hx hd
  have hlt := idx_lt_of_end? hx
  refine ⟨x, ?_, hd⟩
  rw [end?_newEnds, ite_eq_right (by omega), ite_eq_right (by omega)]; exact hx

theorem newStream_doneStable (s : CStore E) (t : Option (WIT.ClosedType RtId))
    (o : Option InstId) : DoneStable s (newStream t o s).1 :=
  (newEnds_keepsDone s _ t o).doneStable

theorem newFuture_doneStable (s : CStore E) (t : Option (WIT.ClosedType RtId))
    (o : Option InstId) : DoneStable s (newFuture t o s).1 :=
  (newEnds_keepsDone s _ t o).doneStable

/-- Running the event closure of an end that is not `DONE` keeps every `DONE` end `DONE`. -/
theorem deliver_keepsDone (s : CStore E) (e : EndId) (p : Nat)
    (hnd : ∀ x, s.end? e = some x → x.state ≠ .done) : KeepsDone s (deliver e p s).1 := by
  unfold deliver; split
  · exact .refl s
  · rename_i x hx
    exact KeepsDone.setEnd fun y hy hd => by rw [hx] at hy; cases hy; exact absurd hd (hnd x hx)

/-- Under `EndWF`, taking an end's pending event keeps every `DONE` end `DONE`: a `DONE` end has
no pending event (`EndWF.doneQuiet`), so `takeEvent` leaves it unchanged. -/
theorem takeEvent_keepsDone {s : CStore E} (hw : EndWF s) (e : EndId) :
    KeepsDone s (takeEvent e s).1 := by
  unfold takeEvent; split
  · exact .refl s
  · rename_i x hx
    by_cases hxd : x.state = .done
    · rw [hw.doneQuiet e x hx hxd]; exact .refl s
    have h1 : KeepsDone s (setEnd s e x.clearPending) :=
      KeepsDone.setEnd fun y hy hd => by rw [hx] at hy; cases hy; exact hd
    have hnd : ∀ y, (setEnd s e x.clearPending).end? e = some y → y.state ≠ .done :=
      fun y hy => by rw [end?_setEnd_self hx] at hy; cases hy; exact hxd
    split
    · exact h1.trans (deliver_keepsDone _ _ _ hnd)
    · exact h1.trans (deliver_keepsDone _ _ _ hnd)
    · exact .refl s

/-! ## Traces: done ends never re-enter copying -/

theorem EndStep.endWF {s s' : CStore E} (h : EndStep s s') (hw : EndWF s) : EndWF s' := by
  cases h with
  | copy h => exact copy_EndWF hw h
  | notify p hnd => exact notify_EndWF hw _ p hnd
  | takeEvent => exact takeEvent_EndWF hw _
  | cancel => exact cancel_EndWF hw _ _
  | forward h => exact forward_EndWF hw h
  | dropEnd => exact dropEnd_EndWF hw _
  | newStream => exact newStream_EndWF hw _ _
  | newFuture => exact newFuture_EndWF hw _ _

theorem EndStep.keepsDone {s s' : CStore E} (h : EndStep s s') (hw : EndWF s) :
    KeepsDone s s' := by
  cases h with
  | copy h => exact copy_keepsDone h
  | notify p _ => exact notify_keepsDone _ _ p
  | takeEvent => exact takeEvent_keepsDone hw _
  | cancel => exact cancel_keepsDone _ _ _
  | forward h => exact forward_keepsDone hw h
  | dropEnd => exact dropEnd_keepsDone _ _
  | newStream => exact newEnds_keepsDone _ _ _ _
  | newFuture => exact newEnds_keepsDone _ _ _ _

theorem EndSteps.endWF {s s' : CStore E} (h : EndSteps s s') (hw : EndWF s) : EndWF s' := by
  induction h with
  | refl => exact hw
  | tail _ h ih => exact h.endWF ih

theorem EndSteps.keepsDone {s s' : CStore E} (h : EndSteps s s') (hw : EndWF s) :
    KeepsDone s s' := by
  induction h with
  | refl => exact .refl _
  | tail h₁ h ih => exact ih.trans (h.keepsDone (h₁.endWF hw))

/-- Done ends never re-enter copying: from a well-formed store, along any finite trace of end
operations, an end that is `DONE` stays `DONE` (so it is never `COPYING` or
`CANCELLING_COPY` again). -/
theorem done_never_copying {s s' : CStore E} (hw : EndWF s) (h : EndSteps s s') :
    DoneStable s s' :=
  (h.keepsDone hw).doneStable

/-- Every store reachable from the empty store by end operations is well formed. -/
theorem EndSteps.endWF_of_empty {s : CStore E} (h : EndSteps CStore.empty s) : EndWF s :=
  h.endWF empty_EndWF

/-! ## Progress monotonicity -/

namespace BufProgressMono

theorem setEnd_of {s s₁ : CStore E} {o : EndId} {Y : End E} (h₁ : BufProgressMono s s₁)
    (ho : s₁.end? o = s.end? o)
    (hY : ∀ y b b', s.end? o = some y → y.buffer = some b → Y.buffer = some b' →
      b.progress ≤ b'.progress) :
    BufProgressMono s (Runtime.setEnd s₁ o Y) := by
  intro f x z b b' hx hb hz hb'
  by_cases hf : f = o
  · subst hf
    rw [eq_of_end?_setEnd_self hz] at hb'
    exact hY x b b' hx hb hb'
  · rw [end?_setEnd_ne _ _ hf] at hz
    exact h₁ f x z b b' hx hb hz hb'

theorem setEnd {s : CStore E} {e : EndId} {X : End E}
    (hX : ∀ x b b', s.end? e = some x → x.buffer = some b → X.buffer = some b' →
      b.progress ≤ b'.progress) :
    BufProgressMono s (Runtime.setEnd s e X) :=
  setEnd_of (refl s) rfl hX

end BufProgressMono

theorem notify_progress_mono (s : CStore E) (e : EndId) (p : Nat) :
    BufProgressMono s (notify e p s) := by
  unfold notify; split
  · rename_i x hx
    refine BufProgressMono.setEnd fun y b b' hy hb hb' => ?_
    rw [hx] at hy; cases hy
    rw [End.buffer_withNotify, hb] at hb'; cases hb'; exact Nat.le_refl _
  · exact .refl s

/-- A `copy` never decreases the progress of a parked buffer (in REF case 3 the peer's parked
buffer advances by the number of transferred elements). -/
theorem copy_progress_mono {s s' : CStore E} {e : EndId} {buf : BufferDesc E} {isRead : Bool}
    {a : CopyAction E} (hw : EndWF s) (h : copy e buf isRead s = .ok (s', a)) :
    BufProgressMono s s' := by
  unfold copy at h
  split at h
  · cases h
  rename_i x hx
  split at h
  all_goals try first | exact (by cases h)
  rename_i hidle
  have hnb : x.buffer = none := by
    cases hb : x.buffer with
    | none => rfl
    | some b =>
      have := hw.bufOK e x hx (by simp [hb])
      rw [hidle] at this; exact absurd this (by decide)
  have hX : ∀ X : End E, BufProgressMono s (setEnd s e X) := fun X =>
    BufProgressMono.setEnd fun y b b' hy hb _ => by
      rw [hx] at hy; cases hy; rw [hnb] at hb; cases hb
  unfold copyCore at h
  split at h
  · cases h
  rename_i x' hx'
  rw [hx] at hx'; cases hx'
  split at h
  · cases h
  split at h
  · cases h; exact hX _
  rename_i o _
  split at h
  · cases h
  rename_i hoe
  split at h
  · cases h
  rename_i y hy
  have hso : ∀ X : End E, (setEnd s e X).end? o = s.end? o := fun X => end?_setEnd_ne _ _ hoe
  split at h
  · cases h; exact hX _
  rename_i ob hob
  split at h
  · split at h
    · cases h
    · cases h
      refine (hX _).setEnd_of (hso _) fun y' b b' hy' hb hb' => ?_
      rw [hy] at hy'; cases hy'; rw [hob] at hb; cases hb
      simp only at hb'
      split at hb'
      · cases hb'
      · cases hb'; simp
  · split at h
    · cases h
      exact (hX _).setEnd_of (hso _) fun y' b b' _ _ hb' => by cases hb'
    · cases h; exact hX _

/-- Progress monotonicity for `copy` (under `EndWF`) and `notify`. -/
theorem progress_mono (s : CStore E) :
    (∀ {s' : CStore E} {e : EndId} {buf : BufferDesc E} {isRead : Bool} {a : CopyAction E},
      EndWF s → copy e buf isRead s = .ok (s', a) → BufProgressMono s s') ∧
    (∀ e p, BufProgressMono s (notify e p s)) :=
  ⟨fun hw h => copy_progress_mono hw h, notify_progress_mono s⟩

/-! ## Futures are written once -/

theorem copy_done {s : CStore E} {e : EndId} {x : End E} (hx : s.end? e = some x)
    (hd : x.state = .done) (buf : BufferDesc E) (isRead : Bool) :
    ∃ err, copy e buf isRead s = .error err := by
  unfold copy; rw [hx]; simp only [hd]; exact ⟨_, rfl⟩

theorem takeEvent_future_done {s : CStore E} {w w' : EndId} {Y : End E} {p : Nat} {b : Bool}
    (hY : s.end? w = some Y) (hk : Y.kind.isStream = false)
    (hp : Y.common.pending = some (if b then .streamEnd w' p else .futureEnd w' p))
    (hb : b = false) (hp0 : p ≠ 0) :
    ((takeEvent w s).1.end? w).map End.state = some .done := by
  subst hb
  have h1 := end?_setEnd_self hY Y.clearPending
  simp [takeEvent, hY, hp, deliver, h1, end?_setEnd_self h1, End.deliverStep, hk, hp0]

/-- After a transfer involving a future's writable end, delivering that end's event makes it
DONE, and a second write traps. -/
theorem future_written_once {s s₁ : CStore E} {e w r : EndId} {buf wb rb : BufferDesc E}
    {isRead : Bool} {n : Nat}
    (hc : copy e buf isRead s = .ok (s₁, .transfer w r n wb rb))
    (hk : (s.end? w).map End.kind = some .writableFuture) :
    ((takeEvent w s₁).1.end? w).map End.state = some .done ∧
      ∀ buf', ∃ err, copy w buf' false (takeEvent w s₁).1 = .error err := by
  suffices h : ((takeEvent w s₁).1.end? w).map End.state = some .done by
    refine ⟨h, fun buf' => ?_⟩
    obtain ⟨z, hz, hzd⟩ := Option.map_eq_some_iff.1 h
    exact copy_done hz hzd _ _
  unfold copy at hc
  split at hc
  · cases hc
  rename_i x hx
  split at hc
  all_goals try first | exact (by cases hc)
  unfold copyCore at hc
  split at hc
  · cases hc
  rename_i x' hx'
  rw [hx] at hx'; cases hx'
  split at hc
  · cases hc
  split at hc
  · cases hc
  rename_i o _
  split at hc
  · cases hc
  rename_i hoe
  split at hc
  · cases hc
  rename_i y hy
  split at hc
  · cases hc
  rename_i ob hob
  split at hc
  · rename_i hrem
    split at hc
    · cases hc
    · have hn : 0 < min buf.remain ob.remain := Nat.lt_min.2 hrem
      cases isRead
      · simp only [Bool.false_eq_true, ite_false, Except.ok.injEq, Prod.mk.injEq,
          CopyAction.transfer.injEq] at hc
        obtain ⟨rfl, rfl, -, -, -, -⟩ := hc
        rw [hx] at hk; simp only [Option.map_some, Option.some.injEq] at hk
        refine takeEvent_future_done (w' := e) (b := x.kind.isStream)
          (Y := ({ x with state := .copying } : End E).withNotify e
            ((buf.advance (min buf.remain ob.remain)).progress))
          (p := (buf.advance (min buf.remain ob.remain)).progress) ?_ ?_ ?_ ?_ ?_
        · rw [end?_setEnd_ne _ _ (Ne.symm hoe)]; exact end?_setEnd_self hx _
        · simp [hk, EndKind.isStream]
        · rfl
        · simp [hk, EndKind.isStream]
        · simp only [BufferDesc.progress_advance]; omega
      · simp only [ite_true, Except.ok.injEq, Prod.mk.injEq, CopyAction.transfer.injEq] at hc
        obtain ⟨rfl, rfl, -, -, -, -⟩ := hc
        rw [hy] at hk; simp only [Option.map_some, Option.some.injEq] at hk
        refine takeEvent_future_done (w' := o) (b := y.kind.isStream)
          (Y := { y.withNotify o ((ob.advance (min buf.remain ob.remain)).progress) with
            buffer := if (ob.advance (min buf.remain ob.remain)).remain = 0 then none
              else some (ob.advance (min buf.remain ob.remain)) })
          (p := (ob.advance (min buf.remain ob.remain)).progress) ?_ ?_ ?_ ?_ ?_
        · exact end?_setEnd_self (by rw [end?_setEnd_ne _ _ hoe]; exact hy) _
        · simp [hk, EndKind.isStream]
        · rfl
        · simp [hk, EndKind.isStream]
        · simp only [BufferDesc.progress_advance]; omega
  · split at hc
    · cases hc
    · cases hc

end Silmaril.Wasm.Component.Runtime
