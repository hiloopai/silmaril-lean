module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Core

/-!
# Proofs: the async store under the component's operations (for the OS image)

`SI st`: handles are in `[1, next)`; a readable end `h` of a stream denotes its own channel
`h` whose reader is not dropped; a writable end of the channel `s` is `s + 1`; a readable end of
a future denotes its own channel; channels from `next` on have no dropped reader.

`Dead st s`: the reader of the channel `s` is dropped and no read is pending on it; a
`stream.write` to it reports `DROPPED` or traps, it never completes.

`AOk st st'` (`AOk.step`): every op of the async store that the component uses keeps `SI`,
keeps dead channels dead, only removes handles or adds a waitable set at `next`, and advances
`next` by at most one; a removed readable end leaves its channel dead.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Obj Res Chan Pend Event upd)

/-- The store invariant behind the OS image. -/
structure SI (st : Store) : Prop where
  pos : 1 ≤ st.next
  lt : ∀ h o, st.tbl h = some o → 1 ≤ h ∧ h < st.next
  rEnd : ∀ h s, st.tbl h = some (.streamR s) → h = s ∧ (st.chans s).rDropped = false
  wEnd : ∀ h s, st.tbl h = some (.streamW s) → h = s + 1
  fEnd : ∀ h s, st.tbl h = some (.futureR s) → h = s
  fresh : ∀ s, st.next ≤ s → (st.chans s).rDropped = false

/-- A channel whose reader is gone and that has no pending read. -/
def Dead (st : Store) (s : Nat) : Prop :=
  (st.chans s).rDropped = true ∧ ∀ hr k, (st.chans s).pend ≠ .read hr k

theorem SI.init : SI ({} : Store) :=
  ⟨Nat.le_refl _, (fun _ _ h => by cases h), (fun _ _ h => by cases h),
    (fun _ _ h => by cases h), (fun _ _ h => by cases h), fun _ _ => rfl⟩

@[simp] theorem setChan_tbl (st : Store) (s : Nat) (c : Chan) : (st.setChan s c).tbl = st.tbl := rfl
@[simp] theorem setChan_next (st : Store) (s : Nat) (c : Chan) :
    (st.setChan s c).next = st.next := rfl
@[simp] theorem setChan_chans (st : Store) (s : Nat) (c : Chan) (s' : Nat) :
    (st.setChan s c).chans s' = if s' = s then c else st.chans s' := rfl
@[simp] theorem post_tbl (st : Store) (h : Nat) (e : Event) : (st.post h e).tbl = st.tbl := rfl
@[simp] theorem post_next (st : Store) (h : Nat) (e : Event) : (st.post h e).next = st.next := rfl
@[simp] theorem post_chans (st : Store) (h : Nat) (e : Event) : (st.post h e).chans = st.chans := rfl
@[simp] theorem remove_tbl (st : Store) (h h' : Nat) :
    (st.remove h).tbl h' = if h' = h then none else st.tbl h' := rfl
@[simp] theorem remove_chans (st : Store) (h : Nat) : (st.remove h).chans = st.chans := rfl
@[simp] theorem remove_next' (st : Store) (h : Nat) : (st.remove h).next = st.next := rfl

/-- A change of the store that removes handles, keeps `next`, and drops readers only of
channels below `next` whose readable end it removed. -/
theorem SI.of_shrink {st st' : Store} (h : SI st) (ht : ∀ x o, st'.tbl x = some o → st.tbl x = some o)
    (hn : st'.next = st.next)
    (hr : ∀ s, (st'.chans s).rDropped = true → (st.chans s).rDropped = false →
      s < st.next ∧ ∀ x, st'.tbl x ≠ some (.streamR s)) : SI st' := by
  refine ⟨hn ▸ h.pos, fun x o hx => hn ▸ h.lt x o (ht x o hx), fun x s hx => ?_,
    fun x s hx => h.wEnd x s (ht x _ hx), fun x s hx => h.fEnd x s (ht x _ hx), fun s hs => ?_⟩
  · obtain ⟨hxs, hd⟩ := h.rEnd x s (ht x _ hx)
    refine ⟨hxs, ?_⟩
    cases hd' : (st'.chans s).rDropped
    · rfl
    · exact absurd hx ((hr s hd' hd).2 x)
  · cases hd' : (st'.chans s).rDropped
    · rfl
    · have h0 := h.fresh s (hn ▸ hs)
      exact absurd (hn ▸ hs) (Nat.not_le.2 (hr s hd' h0).1)

/-- A dead channel stays dead when its reader flag is kept and no read becomes pending. -/
theorem Dead.of {st st' : Store} {s : Nat} (hd : Dead st s)
    (hr : (st.chans s).rDropped = true → (st'.chans s).rDropped = true)
    (hp : ∀ hr k, (st'.chans s).pend = .read hr k → (st.chans s).pend = .read hr k) :
    Dead st' s :=
  ⟨hr hd.1, fun x k hx => hd.2 x k (hp x k hx)⟩


/-- A step of the async store as the OS image needs it. -/
structure AOk (st st' : Store) : Prop where
  si : SI st'
  dead : ∀ s, Dead st s → Dead st' s
  tbl : ∀ x o, st'.tbl x = some o → st.tbl x = some o ∨ (x = st.next ∧ o = .wset)
  next : st.next ≤ st'.next ∧ st'.next ≤ st.next + 1
  rGone : ∀ x s, st.tbl x = some (.streamR s) → st'.tbl x = none → Dead st' s

/-- A step that only shrinks the table. -/
theorem AOk.of_shrink {st st' : Store} (h : SI st)
    (ht : ∀ x o, st'.tbl x = some o → st.tbl x = some o) (hn : st'.next = st.next)
    (hr : ∀ s, (st'.chans s).rDropped = true → (st.chans s).rDropped = false →
      s < st.next ∧ ∀ x, st'.tbl x ≠ some (.streamR s))
    (hd : ∀ s, Dead st s → Dead st' s)
    (hg : ∀ x s, st.tbl x = some (.streamR s) → st'.tbl x = none → Dead st' s) : AOk st st' :=
  ⟨h.of_shrink ht hn hr, hd, fun x o hx => Or.inl (ht x o hx), by omega, hg⟩

/-- A table that does not change loses no readable end. -/
theorem gone_of_eq {st st' : Store} (ht : st'.tbl = st.tbl) :
    ∀ x s, st.tbl x = some (.streamR s) → st'.tbl x = none → Dead st' s := by
  intro x s h1 h2
  rw [ht, h1] at h2
  cases h2

/-- No change of the store. -/
theorem AOk.refl {st : Store} (h : SI st) : AOk st st :=
  AOk.of_shrink h (fun _ _ hx => hx) rfl (fun _ h1 h2 => by rw [h1] at h2; cases h2) (fun _ hd => hd)
    (gone_of_eq rfl)

/-- A step that changes neither the table, nor the channels, nor `next`. -/
theorem AOk.of_same {st st' : Store} (h : SI st) (ht : st'.tbl = st.tbl) (hc : st'.chans = st.chans)
    (hn : st'.next = st.next) : AOk st st' :=
  AOk.of_shrink h (fun _ _ hx => by rw [ht] at hx; exact hx) hn
    (fun s h1 h2 => by rw [hc, h2] at h1; cases h1) (fun s hd => by unfold Dead; rw [hc]; exact hd)
    (gone_of_eq ht)

/-- Removing a handle keeps the store invariant. -/
theorem SI.remove {st : Store} (h : SI st) (x : Nat) : SI (st.remove x) :=
  h.of_shrink (fun y o hy => by
    simp only [remove_tbl] at hy
    split at hy
    · cases hy
    · exact hy) rfl (fun s h1 h2 => by simp only [remove_chans] at h1; rw [h1] at h2; cases h2)

/-- A change of the channel `s` that keeps its reader flag keeps every reader flag. -/
theorem chans_rd {st st1 : Store} {s : Nat} (hc : (st1.chans s).rDropped = (st.chans s).rDropped)
    (h1c : ∀ s', s' ≠ s → st1.chans s' = st.chans s') (s' : Nat) :
    (st1.chans s').rDropped = (st.chans s').rDropped := by
  by_cases he : s' = s
  · subst he; exact hc
  · rw [h1c s' he]

/-- **A change of one channel** that keeps its reader flag, and starts a read only on a channel
whose reader is not dropped. -/
theorem AOk.chan {st st1 : Store} (s : Nat) (h : SI st)
    (hc : (st1.chans s).rDropped = (st.chans s).rDropped)
    (hcp : ∀ hr k, (st1.chans s).pend = .read hr k → (st.chans s).rDropped = false)
    (h1t : st1.tbl = st.tbl) (h1n : st1.next = st.next)
    (h1c : ∀ s', s' ≠ s → st1.chans s' = st.chans s') : AOk st st1 := by
  have hrd := chans_rd hc h1c
  refine AOk.of_shrink h (fun _ _ hx => by rwa [h1t] at hx) h1n
    (fun s' h1 h2 => by rw [hrd, h2] at h1; cases h1)
    (fun s' hd => hd.of (fun h1 => by rw [hrd]; exact h1) (fun x k hx => ?_)) (gone_of_eq h1t)
  by_cases he : s' = s
  · subst he
    exact absurd hd.1 (by simp [hcp x k hx])
  · rwa [h1c s' he] at hx

/-- `stream.write`. -/
theorem AOk.streamWrite {st st' : Store} {w : Nat} {xs : List Val} {r : Res} (h : SI st)
    (hs : Silmaril.Wasm.Component.Async.streamWrite st w xs = some (st', r)) : AOk st st' := by
  unfold Silmaril.Wasm.Component.Async.streamWrite at hs
  split at hs
  · rename_i s _
    dsimp only at hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, -⟩ := hs
      exact AOk.chan s h (by simp) (fun _ _ hx => by simp at hx) rfl rfl (fun s' hs' => by simp [hs'])
    · split at hs <;> simp only [Option.some.injEq, Prod.mk.injEq] at hs <;> obtain ⟨rfl, -⟩ := hs
      · exact AOk.refl h
      · exact AOk.chan s h (by simp) (fun _ _ hx => by simp at hx) rfl rfl
          (fun s' hs' => by simp [hs'])
  · cases hs

/-- `stream.read`. -/
theorem AOk.streamRead {st st' : Store} {r n : Nat} {res : Res} (h : SI st)
    (hs : Silmaril.Wasm.Component.Async.streamRead st r n = some (st', res)) : AOk st st' := by
  unfold Silmaril.Wasm.Component.Async.streamRead at hs
  split at hs
  · rename_i s hr
    have hnd : (st.chans s).rDropped = false := (h.rEnd r s hr).2
    dsimp only at hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, -⟩ := hs
      exact AOk.chan s h (by simp) (fun _ _ hx => by simp at hx) rfl rfl (fun s' hs' => by simp [hs'])
    · split at hs <;> simp only [Option.some.injEq, Prod.mk.injEq] at hs <;> obtain ⟨rfl, -⟩ := hs
      · exact AOk.refl h
      · exact AOk.chan s h (by simp) (fun _ _ _ => hnd) rfl rfl (fun s' hs' => by simp [hs'])
  · cases hs

/-- The table after dropping a reader and removing `r`. -/
theorem dr_tbl {st st1 : Store} {r : Nat} (h1t : st1.tbl = st.tbl) (x : Nat) (o : Obj)
    (hx : (st1.remove r).tbl x = some o) : st.tbl x = some o := by
  simp only [remove_tbl] at hx
  split at hx
  · cases hx
  · rwa [h1t] at hx

/-- The reader flags after dropping the reader of `s` and removing its readable end `r`. -/
theorem dr_rd {st st1 : Store} {r s : Nat} {c : Chan} (hlt : s < st.next)
    (hno : ∀ x, st.tbl x = some (.streamR s) → x = r) (h1t : st1.tbl = st.tbl)
    (h1c : ∀ s', st1.chans s' = if s' = s then c else st.chans s') (s' : Nat)
    (hd1 : ((st1.remove r).chans s').rDropped = true) (hd2 : (st.chans s').rDropped = false) :
    s' < st.next ∧ ∀ x, (st1.remove r).tbl x ≠ some (.streamR s') := by
  simp only [remove_chans, h1c] at hd1
  split at hd1
  · rename_i he
    subst he
    refine ⟨hlt, fun x hx => ?_⟩
    simp only [remove_tbl] at hx
    split at hx
    · cases hx
    · rename_i hxr; rw [h1t] at hx; exact hxr (hno x hx)
  · rw [hd1] at hd2; cases hd2

/-- Dead channels after dropping the reader of `s`. -/
theorem dr_dead {st st1 : Store} {r s : Nat} {c : Chan} (hc : c.rDropped = true)
    (hcp : ∀ hr k, c.pend = .read hr k → (st.chans s).pend = .read hr k)
    (h1c : ∀ s', st1.chans s' = if s' = s then c else st.chans s') (s' : Nat) (hd : Dead st s') :
    Dead (st1.remove r) s' := by
  refine hd.of (fun h1 => ?_) (fun x k hx => ?_)
  · simp only [remove_chans, h1c]
    split
    · exact hc
    · exact h1
  · simp only [remove_chans, h1c] at hx
    split at hx
    · rename_i he; subst he; exact hcp x k hx
    · exact hx

/-- The channel of the removed readable end is dead. -/
theorem dr_gone {st st1 : Store} {r s : Nat} {c : Chan} (hc : c.rDropped = true)
    (hcr : ∀ hr k, c.pend ≠ .read hr k) (hrx : ∀ s', st.tbl r = some (.streamR s') → s' = s)
    (h1t : st1.tbl = st.tbl) (h1c : ∀ s', st1.chans s' = if s' = s then c else st.chans s')
    (x s' : Nat) (hx : st.tbl x = some (.streamR s')) (hx' : (st1.remove r).tbl x = none) :
    Dead (st1.remove r) s' := by
  simp only [remove_tbl] at hx'
  split at hx'
  · rename_i hxr
    subst hxr
    have hs' : s' = s := hrx s' hx
    subst hs'
    refine ⟨by simp only [remove_chans, h1c, ↓reduceIte]; exact hc, fun k n hk => hcr k n ?_⟩
    simpa only [remove_chans, h1c, ↓reduceIte] using hk
  · rw [h1t, hx] at hx'; cases hx'

/-- **Removing the readable end `r` of the channel `s` and dropping its reader.** -/
theorem AOk.dropReader {st : Store} {r s : Nat} (h : SI st) (hlt : s < st.next)
    (hno : ∀ x, st.tbl x = some (.streamR s) → x = r) (c : Chan) (hc : c.rDropped = true)
    (hcp : ∀ hr k, c.pend = .read hr k → (st.chans s).pend = .read hr k)
    (hcr : ∀ hr k, c.pend ≠ .read hr k) (hrx : ∀ s', st.tbl r = some (.streamR s') → s' = s)
    (st1 : Store) (h1t : st1.tbl = st.tbl) (h1n : st1.next = st.next)
    (h1c : ∀ s', st1.chans s' = if s' = s then c else st.chans s') :
    AOk st (st1.remove r) :=
  AOk.of_shrink h (dr_tbl h1t) (by simp [h1n]) (dr_rd hlt hno h1t h1c) (dr_dead hc hcp h1c)
    (dr_gone hc hcr hrx h1t h1c)

/-- The only readable end of a stream channel is the handle of the channel. -/
theorem SI.only_reader {st : Store} (h : SI st) {r s : Nat} (hr : st.tbl r = some (.streamR s)) :
    ∀ x, st.tbl x = some (.streamR s) → x = r :=
  fun x hx => (h.rEnd x s hx).1.trans (h.rEnd r s hr).1.symm

/-- Dropping the reader of the stream whose readable end is `r`. -/
theorem AOk.dropStream {st : Store} {r s : Nat} (h : SI st) (hr : st.tbl r = some (.streamR s))
    (c : Chan) (hc : c.rDropped = true)
    (hcp : ∀ hr k, c.pend = .read hr k → (st.chans s).pend = .read hr k)
    (hcr : ∀ hr k, c.pend ≠ .read hr k) (st1 : Store) (h1t : st1.tbl = st.tbl)
    (h1n : st1.next = st.next) (h1c : ∀ s', st1.chans s' = if s' = s then c else st.chans s') :
    AOk st (st1.remove r) := by
  have hlt : s < st.next := (h.rEnd r s hr).1 ▸ (h.lt r _ hr).2
  have hrx : ∀ s', st.tbl r = some (.streamR s') → s' = s := fun s' hs' => by
    rw [hr] at hs'; cases hs'; rfl
  exact AOk.dropReader h hlt (h.only_reader hr) c hc hcp hcr hrx st1 h1t h1n h1c

/-- `stream.drop-readable`. -/
theorem AOk.streamDropR {st st' : Store} {r : Nat} {res : Res} (h : SI st)
    (hs : Silmaril.Wasm.Component.Async.streamDropR st r = some (st', res)) : AOk st st' := by
  unfold Silmaril.Wasm.Component.Async.streamDropR at hs
  split at hs
  · rename_i s hr
    dsimp only at hs
    split at hs
    · cases hs
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs)
      exact AOk.dropStream h hr { st.chans s with pend := .idle, rDropped := true } rfl
        (fun _ _ hx => by cases hx) (fun _ _ hx => by cases hx) _ rfl rfl (fun _ => rfl)
    · rename_i hp
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs)
      exact AOk.dropStream h hr { st.chans s with rDropped := true } rfl (fun _ _ hx => hx)
        (fun _ _ hx => by simp only at hx; rw [hp] at hx; cases hx) _ rfl rfl (fun _ => rfl)
  · cases hs

/-- **A step followed by the removal of a handle that is not a readable end of a stream.** -/
theorem AOk.then_remove {st st1 : Store} (ha : AOk st st1) {w : Nat}
    (hw : ∀ s', st.tbl w ≠ some (.streamR s')) : AOk st (st1.remove w) := by
  refine ⟨ha.si.remove w, fun s hd => ha.dead s hd, fun x o hx => ?_, ha.next,
    fun x s hx hx' => ?_⟩
  · simp only [remove_tbl] at hx
    split at hx
    · cases hx
    · exact ha.tbl x o hx
  · simp only [remove_tbl] at hx'
    split at hx'
    · rename_i hxw; subst hxw; exact absurd hx (hw s)
    · exact ha.rGone x s hx hx'

/-- Dropping the writable end `w` of the channel `s`. -/
theorem AOk.dropWriter {st : Store} {w s : Nat} (h : SI st) (hw : st.tbl w = some (.streamW s))
    (st1 : Store) (hc : (st1.chans s).rDropped = (st.chans s).rDropped)
    (hcp : ∀ hr k, (st1.chans s).pend ≠ .read hr k) (h1t : st1.tbl = st.tbl)
    (h1n : st1.next = st.next) (h1c : ∀ s', s' ≠ s → st1.chans s' = st.chans s') :
    AOk st (st1.remove w) := by
  have hw' : ∀ s', st.tbl w ≠ some (.streamR s') := fun s' hs' => by rw [hw] at hs'; cases hs'
  exact AOk.then_remove (AOk.chan s h hc (fun x k hx => absurd hx (hcp x k)) h1t h1n h1c) hw'

/-- `stream.drop-writable`. -/
theorem AOk.streamDropW {st st' : Store} {w : Nat} {res : Res} (h : SI st)
    (hs : Silmaril.Wasm.Component.Async.streamDropW st w = some (st', res)) : AOk st st' := by
  unfold Silmaril.Wasm.Component.Async.streamDropW at hs
  split at hs
  · rename_i s hw
    dsimp only at hs
    split at hs
    · cases hs
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs)
      refine AOk.dropWriter h hw _ (by simp) (fun _ _ hx => by simp at hx) rfl rfl
        (fun s' hs' => by simp [hs'])
    · rename_i hp
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs)
      refine AOk.dropWriter h hw _ (by simp) (fun _ _ hx => by simp [hp] at hx) rfl rfl
        (fun s' hs' => by simp [hs'])
  · cases hs

/-- A future channel has no readable end of a stream. -/
theorem SI.no_reader {st : Store} (h : SI st) {r s : Nat} (hr : st.tbl r = some (.futureR s)) :
    ∀ x, st.tbl x = some (.streamR s) → x = r := by
  intro x hx
  have hxs : x = s := (h.rEnd x s hx).1
  have hrs : r = s := h.fEnd r s hr
  subst hxs
  rw [← hrs, hr] at hx
  cases hx

/-- Dropping the reader of the future whose readable end is `r`. -/
theorem AOk.dropFuture {st : Store} {r s : Nat} (h : SI st) (hr : st.tbl r = some (.futureR s))
    (c : Chan) (hc : c.rDropped = true)
    (hcp : ∀ hr k, c.pend = .read hr k → (st.chans s).pend = .read hr k)
    (hcr : ∀ hr k, c.pend ≠ .read hr k) (st1 : Store) (h1t : st1.tbl = st.tbl)
    (h1n : st1.next = st.next) (h1c : ∀ s', st1.chans s' = if s' = s then c else st.chans s') :
    AOk st (st1.remove r) := by
  have hlt : s < st.next := h.fEnd r s hr ▸ (h.lt r _ hr).2
  have hrx : ∀ s', st.tbl r = some (.streamR s') → s' = s := fun s' hs' => by
    rw [hr] at hs'; cases hs'
  exact AOk.dropReader h hlt (h.no_reader hr) c hc hcp hcr hrx st1 h1t h1n h1c

/-- `future.drop-readable`. -/
theorem AOk.futureDropR {st st' : Store} {r : Nat} {res : Res} (h : SI st)
    (hs : Silmaril.Wasm.Component.Async.futureDropR st r = some (st', res)) : AOk st st' := by
  unfold Silmaril.Wasm.Component.Async.futureDropR at hs
  split at hs
  · rename_i s hr
    dsimp only at hs
    split at hs
    · cases hs
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs)
      exact AOk.dropFuture h hr { st.chans s with pend := .idle, rDropped := true, done := true } rfl
        (fun _ _ hx => by cases hx) (fun _ _ hx => by cases hx) _ rfl rfl (fun _ => rfl)
    · rename_i hp
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs)
      exact AOk.dropFuture h hr { st.chans s with rDropped := true } rfl (fun _ _ hx => hx)
        (fun _ _ hx => by simp only at hx; rw [hp] at hx; cases hx) _ rfl rfl (fun _ => rfl)
  · cases hs

/-- `waitable-set.new`: a waitable set at `next`. -/
theorem AOk.wsNew {st : Store} (h : SI st) :
    AOk st { st with next := st.next + 1, tbl := upd st.tbl st.next (some .wset) } := by
  have hold : ∀ x o, (upd st.tbl st.next (some Obj.wset)) x = some o →
      st.tbl x = some o ∨ (x = st.next ∧ o = .wset) := by
    intro x o hx
    simp only [upd] at hx
    split at hx
    · rename_i he; cases hx; exact Or.inr ⟨he, rfl⟩
    · exact Or.inl hx
  have hnw : ∀ x o, (upd st.tbl st.next (some Obj.wset)) x = some o → o ≠ .wset →
      st.tbl x = some o := fun x o hx ho => (hold x o hx).resolve_right fun h' => ho h'.2
  have hsi : SI { st with next := st.next + 1, tbl := upd st.tbl st.next (some .wset) } :=
    ⟨Nat.le_add_left 1 st.next, fun x o hx => (hold x o hx).elim
      (fun hx' => ⟨(h.lt x o hx').1, Nat.lt_succ_of_lt (h.lt x o hx').2⟩)
      (fun hx' => ⟨hx'.1 ▸ h.pos, hx'.1 ▸ Nat.lt_succ_self _⟩),
      fun x s hx => h.rEnd x s (hnw x _ hx (by simp)), fun x s hx => h.wEnd x s (hnw x _ hx (by simp)),
      fun x s hx => h.fEnd x s (hnw x _ hx (by simp)), fun s hs => h.fresh s (by simp at hs; omega)⟩
  refine ⟨hsi, fun s hd => hd, hold, by simp, fun x s hx hx' => ?_⟩
  simp only [upd] at hx'
  split at hx'
  · cases hx'
  · rw [hx] at hx'; cases hx'

/-- `waitable.join`. -/
theorem AOk.join {st st' : Store} {x s : Nat} {res : Res} (h : SI st)
    (hs : Silmaril.Wasm.Component.Async.step st (.join x s) = some (st', res)) : AOk st st' := by
  simp only [Silmaril.Wasm.Component.Async.step] at hs
  repeat' split at hs
  all_goals first
    | (cases hs; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at hs
       obtain ⟨rfl, -⟩ := hs
       exact AOk.of_same h rfl rfl rfl)

/-- `waitable-set.wait`. -/
theorem AOk.wait {st st' : Store} {s : Nat} {res : Res} (h : SI st)
    (hs : Silmaril.Wasm.Component.Async.step st (.wait s) = some (st', res)) : AOk st st' := by
  simp only [Silmaril.Wasm.Component.Async.step] at hs
  split_ifs at hs
  cases hf : Silmaril.Wasm.Component.Async.firstReady st s (List.range st.next) with
  | none =>
    simp only [hf, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    exact AOk.refl h
  | some x =>
    simp only [hf, Option.map_eq_some_iff, Silmaril.Wasm.Component.Async.take] at hs
    obtain ⟨⟨st'', e⟩, ht, hp⟩ := hs
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    cases he : st.ev x with
    | none => simp [he] at ht
    | some e' =>
      simp only [he, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨_, _, rfl, _⟩ := ht
      exact AOk.of_same h rfl rfl rfl

/-- The ops of the async store that the component uses. -/
def UsedOp : Silmaril.Wasm.Component.Async.Op → Prop
  | .streamWrite .. | .streamRead .. | .streamDropR _ | .streamDropW _ | .futureDropR _
  | .wsNew | .join .. | .wait _ => True
  | _ => False

/-- **Every used op of the async store keeps the store invariant.** -/
theorem AOk.step {st st' : Store} {op : Silmaril.Wasm.Component.Async.Op} {res : Res} (h : SI st)
    (hop : UsedOp op) (hs : Silmaril.Wasm.Component.Async.step st op = some (st', res)) :
    AOk st st' := by
  cases op with
  | streamWrite w xs => exact AOk.streamWrite h hs
  | streamRead r n => exact AOk.streamRead h hs
  | streamDropR r => exact AOk.streamDropR h hs
  | streamDropW w => exact AOk.streamDropW h hs
  | futureDropR r => exact AOk.futureDropR h hs
  | wsNew =>
    simp only [Silmaril.Wasm.Component.Async.step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    exact AOk.wsNew h
  | join x s => exact AOk.join h hs
  | wait s => exact AOk.wait h hs
  | _ => exact absurd hop id

/-- The table after `alloc2`: the two new handles, or an old one. -/
theorem alloc2_cases {st : Store} {a b : Nat → Obj} {x : Nat} {o : Obj}
    (hx : (st.alloc2 a b).1.tbl x = some o) :
    (x = st.next ∧ o = a st.next) ∨ (x = st.next + 1 ∧ o = b st.next) ∨ st.tbl x = some o := by
  simp only [Store.alloc2, upd] at hx
  split at hx
  · rename_i hx1; cases hx; exact Or.inr (Or.inl ⟨hx1, rfl⟩)
  · split at hx
    · rename_i _ hx1; cases hx; exact Or.inl ⟨hx1, rfl⟩
    · exact Or.inr (Or.inr hx)

/-- The ends of a stream or a future after `alloc2`. -/
theorem SI.alloc2_ends {st : Store} (h : SI st) (a b : Nat → Obj)
    (hab : (∀ r, a r = .streamR r ∧ b r = .streamW r) ∨ (∀ r, a r = .futureR r ∧ b r = .futureW r))
    (x s : Nat) :
    ((st.alloc2 a b).1.tbl x = some (.streamR s) → x = s ∧ (st.chans s).rDropped = false) ∧
    ((st.alloc2 a b).1.tbl x = some (.streamW s) → x = s + 1) ∧
    ((st.alloc2 a b).1.tbl x = some (.futureR s) → x = s) := by
  have hfr : (st.chans st.next).rDropped = false := h.fresh st.next (Nat.le_refl _)
  rcases hab with hab | hab
  all_goals refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  all_goals rcases alloc2_cases hx with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | hx'
  all_goals first
    | exact h.rEnd x s hx'
    | exact h.wEnd x s hx'
    | exact h.fEnd x s hx'
    | (rw [(hab _).1] at hs; cases hs; done)
    | (rw [(hab _).2] at hs; cases hs; done)
    | (rw [(hab _).1] at hs; cases hs; exact ⟨rfl, hfr⟩)
    | (rw [(hab _).1] at hs; cases hs; rfl)
    | (rw [(hab _).2] at hs; cases hs; rfl)

/-- **Allocating the two ends of a stream or of a future keeps the store invariant.** -/
theorem SI.alloc2 {st : Store} (h : SI st) (a b : Nat → Obj)
    (hab : (∀ r, a r = .streamR r ∧ b r = .streamW r) ∨ (∀ r, a r = .futureR r ∧ b r = .futureW r)) :
    SI (st.alloc2 a b).1 := by
  have hpos : 1 ≤ st.next := h.pos
  have hnx : (st.alloc2 a b).1.next = st.next + 2 := rfl
  have hch : (st.alloc2 a b).1.chans = st.chans := rfl
  refine ⟨by omega, fun x o hx => ?_, fun x s hx => ?_, fun x s hx => (h.alloc2_ends a b hab x s).2.1 hx,
    fun x s hx => (h.alloc2_ends a b hab x s).2.2 hx,
    fun s hs => by rw [hch]; exact h.fresh s (by omega)⟩
  · rcases alloc2_cases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | hx'
    · omega
    · omega
    · have := h.lt x o hx'; omega
  · rw [hch]; exact (h.alloc2_ends a b hab x s).1 hx

end Silmaril.Wasi.Versions.P3OverP2
