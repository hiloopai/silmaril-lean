module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Basic
public import Silmaril.Wasm.Component.Async.Thms

/-!
# Proofs: WASI 0.3 over 0.2, how each function changes the state

For every function, the next free handle (`Store.next`) does not decrease (`*_next`), and the
stdout and input bindings change only as stated: `outs` grows only by `write-via-stream`, the
futures of `ins` are kept by the other functions, and `wdrop` grows only by
`stream.drop-writable`. These are the frame facts of the invariants of
`Silmaril.Proofs.Wasi.Versions.P3OverP2.Stdout` and `.Read`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Obj Res packCopy CopyResult blocked)

/-- A step of the async store does not decrease `next`. -/
theorem astep_next {st st' : Store} {op : Silmaril.Wasm.Component.Async.Op} {r : Res}
    (h : Silmaril.Wasm.Component.Async.step st op = some (st', r)) : st.next ≤ st'.next :=
  Silmaril.Wasm.Component.Async.step_next h

/-- `remove` keeps `next`. -/
theorem remove_next (st : Store) (h : Nat) : (st.remove h).next = st.next := rfl

/-- `alloc2` returns `next` and `next + 1` and advances `next` by two. -/
theorem alloc2_spec (st : Store) (a b : Nat → Obj) :
    (st.alloc2 a b).2.1 = st.next ∧ (st.alloc2 a b).2.2 = st.next + 1 ∧
      (st.alloc2 a b).1.next = st.next + 2 := ⟨rfl, rfl, rfl⟩

/-- The frame of a function: `next` does not decrease, `outs` is unchanged, every input binding
comes with the future of an old one, `wdrop` is unchanged. -/
structure Frame (c c' : Core) : Prop where
  next : c.st.next ≤ c'.st.next
  outs : c'.outs = c.outs
  ins : ∀ e ∈ c'.ins, ∃ e' ∈ c.ins, e'.1 = e.1 ∧ e'.2.fut = e.2.fut ∧ e'.2.is = e.2.is ∧
    e'.2.file = e.2.file
  wdrop : c'.wdrop = c.wdrop

theorem Frame.refl (c : Core) : Frame c c :=
  ⟨Nat.le_refl _, rfl, fun e he => ⟨e, he, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem Frame.trans {c c' c'' : Core} (h : Frame c c') (h' : Frame c' c'') : Frame c c'' := by
  refine ⟨Nat.le_trans h.next h'.next, h'.outs.trans h.outs, fun e he => ?_, h'.wdrop.trans h.wdrop⟩
  obtain ⟨e', he', h1, h2, h3, h4⟩ := h'.ins e he
  obtain ⟨e'', he'', h1', h2', h3', h4'⟩ := h.ins e' he'
  exact ⟨e'', he'', h1'.trans h1, h2'.trans h2, h3'.trans h3, h4'.trans h4⟩

/-- A step of the async store is a frame. -/
theorem Frame.st {c : Core} {st' : Store} (h : c.st.next ≤ st'.next) :
    Frame c { c with st := st' } :=
  ⟨h, rfl, fun e he => ⟨e, he, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Changing pending writes or error futures is a frame. -/
theorem Frame.pend (c : Core) (p : List (Nat × BitVec 32 × List (BitVec 8))) (ef : List Nat) :
    Frame c { c with pend := p, errF := ef } :=
  ⟨Nat.le_refl _, rfl, fun e he => ⟨e, he, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Setting a mode is a frame. -/
theorem Frame.setMode (c : Core) (r : Nat) (m : IMode) : Frame c (c.setMode r m) := by
  refine ⟨Nat.le_refl _, rfl, fun e he => ?_, rfl⟩
  simp only [Core.setMode, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  refine ⟨e', he', ?_⟩
  split <;> simp

/-- The result of an optional async step is a frame. -/
theorem Frame.astep {c : Core} {op : Silmaril.Wasm.Component.Async.Op} {r : Res} {st' : Store}
    (h : Silmaril.Wasm.Component.Async.step c.st op = some (st', r)) : Frame c { c with st := st' } :=
  Frame.st (astep_next h)

/-- `stream.read` is a frame. -/
theorem finSr_frame (c : Core) (a : List Val) (d : Option (List Val)) :
    Frame c (finSr c a d).1 := by
  unfold finSr
  repeat' split
  all_goals first
    | exact Frame.refl _
    | exact Frame.setMode _ _ _
    | (apply Frame.astep; assumption)

/-- `stream.drop-readable` is a frame. -/
theorem finDropR_frame (c : Core) (a : List Val) : Frame c (finDropR c a) := by
  unfold finDropR
  split
  · dsimp only
    split <;> split
    all_goals first
      | exact Frame.refl _
      | exact Frame.setMode _ _ _
      | (apply Frame.astep; assumption)
      | exact (Frame.astep ‹_›).trans (Frame.setMode _ _ _)
  · exact Frame.refl _

/-- `future.drop-readable` is a frame. -/
theorem finFDropR_frame (c : Core) (a : List Val) : Frame c (finFDropR c a) := by
  unfold finFDropR
  repeat' split
  all_goals first | exact Frame.refl _ | (apply Frame.astep; assumption)

/-- `waitable.join` is a frame. -/
theorem finJoin_frame (c : Core) (a : List Val) : Frame c (finJoin c a) := by
  unfold finJoin
  repeat' split
  all_goals first | exact Frame.refl _ | (apply Frame.astep; assumption)

/-- `waitable-set.new` is a frame. -/
theorem finWsNew_frame (c : Core) : Frame c (finWsNew c).1 := by
  unfold finWsNew
  repeat' split
  all_goals first | exact Frame.refl _ | (apply Frame.astep; assumption)

/-- `waitable-set.wait` is a frame. -/
theorem finWait_frame (c : Core) (a : List Val) (d : Option (Option Nat)) :
    Frame c (finWait c a d).1 := by
  unfold finWait
  repeat' split
  all_goals first
    | exact Frame.refl _
    | (apply Frame.astep; assumption)
    | exact Frame.pend c _ c.errF

/-- `stream.write` is a frame. -/
theorem finSw_frame (c : Core) (a : List Val) (d : Option Nat) : Frame c (finSw c a d).1 := by
  unfold finSw
  repeat' split
  all_goals first
    | exact Frame.refl _
    | (apply Frame.astep; assumption)
    | exact Frame.pend c _ c.errF

/-- `stream.new` is a frame. -/
theorem finNew_frame (c : Core) : Frame c (finNew c).1 := by
  unfold finNew
  split
  · exact Frame.st (by simp [Store.alloc2])
  · exact Frame.refl _

end Silmaril.Wasi.Versions.P3OverP2

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Obj Res)

/-- `finIn` with room: two streams' worth of handles, a new binding of the readable end. -/
theorem finIn_room {c : Core} (h : c.room = true) (file : Bool) (d : Option (BitVec 32)) :
    (finIn c file d).2.1 = c.st.next ∧ (finIn c file d).2.2 = c.st.next + 2 ∧
    (finIn c file d).1.st.next = c.st.next + 4 ∧ (finIn c file d).1.outs = c.outs ∧
    (finIn c file d).1.wdrop = c.wdrop ∧
    (finIn c file d).1.ins = (c.st.next, ⟨d.getD 0, file, c.st.next + 2,
      if d.isSome then .live else .dead⟩) ::
      (match d with | some is => killIs is c.ins | none => c.ins) := by
  simp only [finIn, h, ite_true, Store.alloc2]
  cases d <;> simp [Store.remove]

/-- `finIn` without room changes nothing. -/
theorem finIn_noroom {c : Core} (h : c.room = false) (file : Bool) (d : Option (BitVec 32)) :
    finIn c file d = (c, 0, 0) := by
  simp [finIn, h]

/-- `finWvs` with room: a fresh future; the stream is bound when it is a live guest stream and
`get-stdout` answered. -/
theorem finWvs_room {c : Core} (h : c.room = true) (a : List Val) (d : Option (BitVec 32)) :
    (finWvs c a d).2 = c.st.next ∧ (finWvs c a d).1.st.next = c.st.next + 2 ∧
    (finWvs c a d).1.ins = c.ins ∧ (finWvs c a d).1.wdrop = c.wdrop ∧
    (finWvs c a d).1.outs = (match wvsSrc c a, d with
      | some r, some os => (r, ⟨os, c.st.next⟩) :: c.outs
      | _, _ => c.outs) := by
  simp only [finWvs, h, ite_true, Store.alloc2]
  split <;> simp_all [Store.remove]

/-- `finWvs` without room changes nothing. -/
theorem finWvs_noroom {c : Core} (h : c.room = false) (a : List Val) (d : Option (BitVec 32)) :
    finWvs c a d = (c, 0) := by
  simp [finWvs, h]

/-- `finNew` with room. -/
theorem finNew_room {c : Core} (h : c.room = true) :
    (finNew c).2 = (c.st.next, c.st.next + 1) ∧ (finNew c).1.st.next = c.st.next + 2 := by
  simp [finNew, h, Store.alloc2]

/-- `finNew` without room changes nothing. -/
theorem finNew_noroom {c : Core} (h : c.room = false) : finNew c = (c, 0, 0) := by
  simp [finNew, h]

/-- `stream.drop-writable` records the end. -/
theorem finDropW_spec (c : Core) (a : List Val) :
    c.st.next ≤ (finDropW c a).st.next ∧ (finDropW c a).outs = c.outs ∧
    (finDropW c a).ins = c.ins ∧
    (finDropW c a).wdrop = (match arg1 a with | some w => w :: c.wdrop | none => c.wdrop) := by
  cases ha : arg1 a with
  | none => simp [finDropW, ha]
  | some w =>
    simp only [finDropW, ha]
    split
    · rename_i h; exact ⟨astep_next h, rfl, rfl, rfl⟩
    · exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩

/-- With room, handles up to `next + 3` are below `2^32`. -/
theorem room_lt {c : Core} (h : c.room = true) : c.st.next + 4 < 2 ^ 32 := by
  simpa [Core.room] using h

end Silmaril.Wasi.Versions.P3OverP2
