module

public import Silmaril.Wasm.Component.Streams.Live.Defs

/-!
# Positivity facts of the drop-faithful streams

`DChan.Pos c`: the writer's and the reader's buffers are never both open, a reader's open buffer
has room, and a pending `COMPLETED` progress is positive on both ends (an event of a live peer
reports at least one item). Every built-in keeps it (`read_pos`, `write_pos`, `takeR_pos`,
`takeW_pos`, `dropR_pos`, `dropW_pos`), and so does every operation on a store
(`dstep_pos`, `takeEv_pos`). These facts are what makes every step of a node productive.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Live

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event upd)
open Silmaril.Wasm.Component.Streams.Drop

/-- **Positivity facts of a stream.** -/
structure _root_.Silmaril.Wasm.Component.Streams.Drop.DChan.Pos (c : DChan) : Prop where
  excl : c.wbuf = none ∨ c.rcap = none
  rcap : c.rcap ≠ some 0
  rev : c.w.gone = false → ∀ p, c.r.ev = some p → 0 < p
  wev : c.r.gone = false → ∀ p, c.w.ev = some p → 0 < p

theorem pos_empty : DChan.Pos {} :=
  ⟨Or.inl rfl, by simp, by simp, by simp⟩

/-- The copying branch of `read`: the writer's buffer was open, so the reader's is closed. -/
theorem read_copy_pos {c : DChan} {n : Nat} {xs : List Val} (hP : c.Pos) (hb : c.wbuf = some xs)
    (hx : xs ≠ []) (hn : n ≠ 0) :
    DChan.Pos
      { c with
        w := { c.w with ev := some (c.w.ev.getD 0 + min n xs.length) },
        wbuf := if xs.drop (min n xs.length) = [] then none else some (xs.drop (min n xs.length)),
        sent := c.sent ++ xs.take (min n xs.length) } := by
  have hrc : c.rcap = none := hP.excl.resolve_left (by simp [hb])
  have hm : 0 < min n xs.length := by
    have : 0 < xs.length := List.length_pos_iff.2 hx
    omega
  refine ⟨Or.inr hrc, by simp [hrc], hP.rev, fun _ p hp => ?_⟩
  have hp' : c.w.ev.getD 0 + min n xs.length = p := by simpa using hp
  omega

theorem read_pos {c c' : DChan} {n : Nat} {r : Res} (hP : c.Pos) (h : c.read n = some (c', r)) :
    c'.Pos := by
  unfold DChan.read at h
  split_ifs at h with h1 h2
  · split at h
    · obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
      exact ⟨Or.inr rfl, by simp, fun _ p hp => by simp at hp, fun hr p hp => hP.wev hr p hp⟩
    · cases h
  · have hn : n ≠ 0 := fun e => h1 (Or.inr (Or.inr e))
    split at h
    · obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
      exact ⟨Or.inl ‹_›, by simpa using hn, hP.rev, hP.wev⟩
    · cases h
    · rename_i xs hx hb
      obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
      exact read_copy_pos hP hb hx hn

/-- The copying branch of `write`: the reader's buffer was open, so the writer's is closed. -/
theorem write_copy_pos {c : DChan} {n : Nat} {xs : List Val} (hP : c.Pos)
    (hrc : c.rcap = some n) (hx : xs ≠ []) :
    DChan.Pos
      { c with
        r := { c.r with ev := some (c.rgot.length + min n xs.length) },
        rgot := c.rgot ++ xs.take (min n xs.length),
        rcap := if n - min n xs.length = 0 then none else some (n - min n xs.length),
        sent := c.sent ++ xs.take (min n xs.length) } := by
  have hn : n ≠ 0 := fun e => hP.rcap (by rw [hrc, e])
  have hwb : c.wbuf = none := hP.excl.resolve_right (by simp [hrc])
  have hm : 0 < min n xs.length := by
    have : 0 < xs.length := List.length_pos_iff.2 hx
    omega
  have hcap : (if n - min n xs.length = 0 then none else some (n - min n xs.length)) ≠ some 0 := by
    split <;> simp_all
  refine ⟨Or.inl hwb, hcap, fun _ p hp => ?_, hP.wev⟩
  have hp' : c.rgot.length + min n xs.length = p := by simpa using hp
  omega

theorem write_pos {c c' : DChan} {xs : List Val} {r : Res} (hP : c.Pos)
    (h : c.write xs = some (c', r)) : c'.Pos := by
  unfold DChan.write at h
  split_ifs at h with h1 h2
  · split at h
    · obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
      exact ⟨Or.inl rfl, hP.rcap, hP.rev, fun _ p hp => by simp at hp⟩
    · cases h
  · split at h
    · rename_i hrc
      obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
      exact ⟨Or.inr hrc, hP.rcap, hP.rev, hP.wev⟩
    · rename_i n hrc
      obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
      exact write_copy_pos hP hrc (fun e => h1 (Or.inr (Or.inr e)))

theorem takeR_pos {c c' : DChan} {p : Nat} {ys : List Val} (hP : c.Pos)
    (h : c.takeR = some (c', p, ys)) : c'.Pos := by
  unfold DChan.takeR at h
  split at h
  · cases h
  · obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
    exact ⟨Or.inr rfl, by simp, fun _ q hq => by simp at hq, hP.wev⟩

theorem takeW_pos {c c' : DChan} {p : Nat} (hP : c.Pos) (h : c.takeW = some (c', p)) :
    c'.Pos := by
  unfold DChan.takeW at h
  split at h
  · cases h
  · obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
    exact ⟨Or.inl rfl, hP.rcap, hP.rev, fun _ q hq => by simp at hq⟩

theorem dropR_pos {c c' : DChan} (hP : c.Pos) (h : c.dropR = some c') : c'.Pos := by
  unfold DChan.dropR at h
  split_ifs at h
  all_goals
    obtain rfl := Option.some.inj h
    exact ⟨hP.excl, hP.rcap, fun _ q hq => by simp at hq, fun hr => by simp at hr⟩

theorem dropW_pos {c c' : DChan} (hP : c.Pos) (h : c.dropW = some c') : c'.Pos := by
  unfold DChan.dropW at h
  split_ifs at h
  all_goals
    obtain rfl := Option.some.inj h
    exact ⟨hP.excl, hP.rcap, fun hw => by simp at hw, fun _ q hq => by simp at hq⟩

/-! ## Stores -/

/-- Every stream of the store has the positivity facts. -/
def StPos (st : DStore) : Prop := ∀ h, (st.chans h).Pos

theorem setChan_pos {st : DStore} (hP : StPos st) {s : Nat} {c : DChan} (hc : c.Pos) :
    StPos (st.setChan s c) := by
  intro h
  simp only [DStore.setChan, upd]
  split
  · exact hc
  · exact hP h

/-- A built-in on the stream `s` of a store. -/
theorem chanOp_pos {st st' : DStore} {r : Res} {res : Option (DChan × Res)} (hP : StPos st)
    {s : Nat} (hok : ∀ c' a, res = some (c', a) → c'.Pos)
    (h : res.map (fun p => (st.setChan s p.1, p.2)) = some (st', r)) : StPos st' := by
  obtain ⟨⟨c', a⟩, h1, h2⟩ := Option.map_eq_some_iff.1 h
  have hst : st' = st.setChan s c' := (Prod.mk.inj h2).1.symm
  rw [hst]
  exact setChan_pos hP (hok c' a h1)

theorem write_dstep_pos {st st' : DStore} {w : Nat} {xs : List Val} {r : Res} (hP : StPos st)
    (h : dstep st (.streamWrite w xs) = some (st', r)) : StPos st' := by
  simp only [dstep] at h
  split at h
  · exact chanOp_pos hP (fun _ _ e => write_pos (hP _) e) h
  · cases h

theorem read_dstep_pos {st st' : DStore} {r' n : Nat} {r : Res} (hP : StPos st)
    (h : dstep st (.streamRead r' n) = some (st', r)) : StPos st' := by
  simp only [dstep] at h
  split at h
  · exact chanOp_pos hP (fun _ _ e => read_pos (hP _) e) h
  · cases h

theorem dropR_dstep_pos {st st' : DStore} {r' : Nat} {r : Res} (hP : StPos st)
    (h : dstep st (.streamDropR r') = some (st', r)) : StPos st' := by
  simp only [dstep] at h
  split at h
  · obtain ⟨c', h1, h2⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h2
    exact setChan_pos hP (dropR_pos (hP _) h1)
  · cases h

theorem dropW_dstep_pos {st st' : DStore} {w : Nat} {r : Res} (hP : StPos st)
    (h : dstep st (.streamDropW w) = some (st', r)) : StPos st' := by
  simp only [dstep] at h
  split at h
  · obtain ⟨c', h1, h2⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h2
    exact setChan_pos hP (dropW_pos (hP _) h1)
  · cases h

theorem join_pos {st st' : DStore} {h' s : Nat} {r : Res} (hP : StPos st)
    (h : dstep st (.join h' s) = some (st', r)) : StPos st' := by
  simp only [dstep] at h
  split at h <;> (try split at h) <;>
    first
    | (obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj; exact hP)
    | cases h

theorem dstep_pos {st st' : DStore} {op : DOp} {r : Res} (hP : StPos st)
    (h : dstep st op = some (st', r)) : StPos st' := by
  cases op with
  | streamNew =>
    obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
    exact setChan_pos hP pos_empty
  | streamWrite w xs => exact write_dstep_pos hP h
  | streamRead r' n => exact read_dstep_pos hP h
  | streamDropR r' => exact dropR_dstep_pos hP h
  | streamDropW w => exact dropW_dstep_pos hP h
  | wsNew =>
    obtain ⟨rfl, -⟩ := Option.some.inj h |> Prod.mk.inj
    exact hP
  | join h' s => exact join_pos hP h

theorem takeEv_pos {st st' : DStore} {h : Nat} {e : Event} (hP : StPos st)
    (he : takeEv st h = some (st', e)) : StPos st' := by
  simp only [takeEv] at he
  split at he
  · obtain ⟨⟨c', p, ys⟩, h1, h2⟩ := Option.map_eq_some_iff.1 he
    obtain ⟨rfl, -⟩ := Prod.mk.inj h2
    exact setChan_pos hP (takeR_pos (hP _) h1)
  · obtain ⟨⟨c', p⟩, h1, h2⟩ := Option.map_eq_some_iff.1 he
    obtain ⟨rfl, -⟩ := Prod.mk.inj h2
    exact setChan_pos hP (takeW_pos (hP _) h1)
  · cases he

theorem wait_pos {st st' : DStore} {s h : Nat} {e : Event} (hP : StPos st)
    (hw : DWait st s h st' e) : StPos st' :=
  takeEv_pos hP hw.2.2

end Silmaril.Proofs.Wasm.Component.Streams.Live
