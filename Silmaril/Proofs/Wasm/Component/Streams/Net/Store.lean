module

public import Silmaril.Proofs.Wasm.Component.Streams.Net.Chan

/-!
# The store of a network

A store is **coherent** with a network (`Coh`) when its handle table and its waitable-set
membership are those the network's streams determine (`tblOf`, `joinedOf`): an end is present,
and in its node's set, until it is dropped. On a coherent store, a built-in on the handle of an
end of stream `c` is the corresponding `DChan` operation on that stream (`dstep_read`,
`dstep_write`, `dstep_dropR`, `dstep_dropW`, `wait_rh`, `wait_wh`), and the resulting store is
coherent again.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Net

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event upd)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net

/-- **Coherence** of a store with a network. -/
def Coh (net : Network) (st : DStore) : Prop :=
  st.tbl = tblOf net st.chans ∧ st.joined = joinedOf net st.chans

variable {net : Network}

theorem tblOf_rh {ch : Nat → DChan} {c s : Nat} (h : tblOf net ch (rh c) = some (.streamR s)) :
    s = rh c ∧ (ch (rh c)).r.gone = false ∧ c < net.m := by
  have hne : rh c ≠ 0 := by simp [rh]
  have hodd : rh c % 2 = 1 := by simp only [rh]; omega
  unfold tblOf at h
  simp only [hne, ↓reduceIte] at h
  by_cases hle : rh c ≤ 2 * net.m
  · simp only [hle, hodd, ↓reduceIte] at h
    by_cases hg : (ch (rh c)).r.gone = true
    · simp [hg] at h
    · simp only [hg, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Obj.streamR.injEq] at h
      refine ⟨h.symm, by simpa using hg, ?_⟩
      simp only [rh] at hle
      omega
  · simp only [hle, ↓reduceIte] at h
    split_ifs at h
    simp at h

theorem tblOf_wh {ch : Nat → DChan} {c s : Nat} (h : tblOf net ch (wh c) = some (.streamW s)) :
    s = rh c ∧ (ch (rh c)).w.gone = false ∧ c < net.m := by
  have hne : wh c ≠ 0 := by simp [wh]
  have hev : ¬ wh c % 2 = 1 := by simp only [wh]; omega
  have e1 : wh c - 1 = rh c := by simp [wh, rh]
  unfold tblOf at h
  simp only [hne, ↓reduceIte] at h
  by_cases hle : wh c ≤ 2 * net.m
  · simp only [hle, hev, e1, ↓reduceIte] at h
    by_cases hg : (ch (rh c)).w.gone = true
    · simp [hg] at h
    · simp only [hg, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Obj.streamW.injEq] at h
      refine ⟨h.symm, by simpa using hg, ?_⟩
      simp only [wh] at hle
      omega
  · simp only [hle, ↓reduceIte] at h
    split_ifs at h
    simp at h

/-- Changing a stream without dropping an end keeps the table. -/
theorem tblOf_upd (ch : Nat → DChan) (s : Nat) (c' : DChan) (hr : c'.r.gone = (ch s).r.gone)
    (hw : c'.w.gone = (ch s).w.gone) : tblOf net (upd ch s c') = tblOf net ch := by
  funext h
  have h1 : (upd ch s c' h).r.gone = (ch h).r.gone := by
    by_cases e : h = s
    · subst e; simp [upd, hr]
    · simp [upd, e]
  have h2 : (upd ch s c' (h - 1)).w.gone = (ch (h - 1)).w.gone := by
    by_cases e : h - 1 = s
    · rw [e]; simp [upd, hw]
    · simp [upd, e]
  unfold tblOf
  rw [h1, h2]

theorem joinedOf_upd (ch : Nat → DChan) (s : Nat) (c' : DChan) (hr : c'.r.gone = (ch s).r.gone)
    (hw : c'.w.gone = (ch s).w.gone) : joinedOf net (upd ch s c') = joinedOf net ch := by
  funext h
  have h1 : (upd ch s c' h).r.gone = (ch h).r.gone := by
    by_cases e : h = s
    · subst e; simp [upd, hr]
    · simp [upd, e]
  have h2 : (upd ch s c' (h - 1)).w.gone = (ch (h - 1)).w.gone := by
    by_cases e : h - 1 = s
    · rw [e]; simp [upd, hw]
    · simp [upd, e]
  unfold joinedOf
  rw [h1, h2]

theorem coh_setChan {st : DStore} (hc : Coh net st) (s : Nat) (c' : DChan)
    (hr : c'.r.gone = (st.chans s).r.gone) (hw : c'.w.gone = (st.chans s).w.gone) :
    Coh net (st.setChan s c') := by
  refine ⟨?_, ?_⟩
  · simp only [DStore.setChan]
    rw [tblOf_upd _ _ _ hr hw]
    exact hc.1
  · simp only [DStore.setChan]
    rw [joinedOf_upd _ _ _ hr hw]
    exact hc.2

/-- The table after dropping the readable end of stream `c`. -/
theorem tblOf_dropR (ch : Nat → DChan) (c : Nat) (hm : c < net.m) (c' : DChan)
    (hr : c'.r.gone = true) (hw : c'.w.gone = (ch (rh c)).w.gone) :
    tblOf net (upd ch (rh c) c') = upd (tblOf net ch) (rh c) none := by
  funext h
  by_cases e : h = rh c
  · subst e
    have hle : rh c ≤ 2 * net.m := by simp only [rh]; omega
    have hne : rh c ≠ 0 := by simp [rh]
    have hodd : rh c % 2 = 1 := by simp only [rh]; omega
    simp [tblOf, upd, hle, hne, hodd, hr]
  · have h2 : (upd ch (rh c) c' (h - 1)).w.gone = (ch (h - 1)).w.gone := by
      by_cases e' : h - 1 = rh c
      · rw [e']; simp [upd, hw]
      · simp [upd, e']
    have h1 : upd ch (rh c) c' h = ch h := by simp [upd, e]
    simp only [upd, e, ↓reduceIte]
    unfold tblOf
    rw [h1, h2]

theorem joinedOf_dropR (ch : Nat → DChan) (c : Nat) (hm : c < net.m) (c' : DChan)
    (hr : c'.r.gone = true) (hw : c'.w.gone = (ch (rh c)).w.gone) :
    joinedOf net (upd ch (rh c) c') = upd (joinedOf net ch) (rh c) none := by
  funext h
  by_cases e : h = rh c
  · subst e
    have hle : rh c ≤ 2 * net.m := by simp only [rh]; omega
    have hne : rh c ≠ 0 := by simp [rh]
    have hodd : rh c % 2 = 1 := by simp only [rh]; omega
    simp [joinedOf, upd, hle, hne, hodd, hr]
  · have h2 : (upd ch (rh c) c' (h - 1)).w.gone = (ch (h - 1)).w.gone := by
      by_cases e' : h - 1 = rh c
      · rw [e']; simp [upd, hw]
      · simp [upd, e']
    simp only [upd, e, ↓reduceIte]
    unfold joinedOf
    rw [h2]
    simp [upd, e]

/-- The table after dropping the writable end of stream `c`. -/
theorem tblOf_dropW (ch : Nat → DChan) (c : Nat) (hm : c < net.m) (c' : DChan)
    (hw : c'.w.gone = true) (hr : c'.r.gone = (ch (rh c)).r.gone) :
    tblOf net (upd ch (rh c) c') = upd (tblOf net ch) (wh c) none := by
  funext h
  have h1 : (upd ch (rh c) c' h).r.gone = (ch h).r.gone := by
    by_cases e : h = rh c
    · subst e; simp [upd, hr]
    · simp [upd, e]
  by_cases e : h = wh c
  · subst e
    have hle : wh c ≤ 2 * net.m := by simp only [wh]; omega
    have hne : wh c ≠ 0 := by simp [wh]
    have hev : ¬ wh c % 2 = 1 := by simp only [wh]; omega
    have e1 : wh c - 1 = rh c := by simp [wh, rh]
    simp [tblOf, upd, hle, hne, hev, e1, hw]
  · show tblOf net (upd ch (rh c) c') h = upd (tblOf net ch) (wh c) none h
    have h2 : upd ch (rh c) c' (h - 1) = ch (h - 1) ∨ h % 2 = 1 ∨ h = 0 := by
      by_cases e' : h - 1 = rh c
      · right; left; simp only [wh, rh] at e e' ⊢; omega
      · left; simp [upd, e']
    simp only [upd, e, ↓reduceIte]
    unfold tblOf
    rw [h1]
    rcases h2 with h2 | h2 | h2
    · rw [h2]
    · simp [h2]
    · simp [h2]

theorem joinedOf_dropW (ch : Nat → DChan) (c : Nat) (hm : c < net.m) (c' : DChan)
    (hw : c'.w.gone = true) (hr : c'.r.gone = (ch (rh c)).r.gone) :
    joinedOf net (upd ch (rh c) c') = upd (joinedOf net ch) (wh c) none := by
  funext h
  have h1 : (upd ch (rh c) c' h).r.gone = (ch h).r.gone := by
    by_cases e : h = rh c
    · subst e; simp [upd, hr]
    · simp [upd, e]
  by_cases e : h = wh c
  · subst e
    have hle : wh c ≤ 2 * net.m := by simp only [wh]; omega
    have hne : wh c ≠ 0 := by simp [wh]
    have hev : ¬ wh c % 2 = 1 := by simp only [wh]; omega
    have e1 : wh c - 1 = rh c := by simp [wh, rh]
    simp [joinedOf, upd, hle, hne, hev, e1, hw]
  · show joinedOf net (upd ch (rh c) c') h = upd (joinedOf net ch) (wh c) none h
    have h2 : upd ch (rh c) c' (h - 1) = ch (h - 1) ∨ h % 2 = 1 ∨ h = 0 := by
      by_cases e' : h - 1 = rh c
      · right; left; simp only [wh, rh] at e e' ⊢; omega
      · left; simp [upd, e']
    simp only [upd, e, ↓reduceIte]
    unfold joinedOf
    rw [h1]
    rcases h2 with h2 | h2 | h2
    · rw [h2]
    · simp [h2]
    · simp [h2]

/-- Dropping the readable end of stream `c`. -/
theorem coh_dropR {st : DStore} (hc : Coh net st) (c : Nat) (hm : c < net.m) (c' : DChan)
    (hr : c'.r.gone = true) (hw : c'.w.gone = (st.chans (rh c)).w.gone) :
    Coh net ((st.setChan (rh c) c').remove (rh c)) := by
  refine ⟨?_, ?_⟩
  · simp only [DStore.remove, DStore.setChan, hc.1]
    exact (tblOf_dropR _ c hm c' hr hw).symm
  · simp only [DStore.remove, DStore.setChan, hc.2]
    exact (joinedOf_dropR _ c hm c' hr hw).symm

/-- Dropping the writable end of stream `c`. -/
theorem coh_dropW {st : DStore} (hc : Coh net st) (c : Nat) (hm : c < net.m) (c' : DChan)
    (hw : c'.w.gone = true) (hr : c'.r.gone = (st.chans (rh c)).r.gone) :
    Coh net ((st.setChan (rh c) c').remove (wh c)) := by
  refine ⟨?_, ?_⟩
  · simp only [DStore.remove, DStore.setChan, hc.1]
    exact (tblOf_dropW _ c hm c' hw hr).symm
  · simp only [DStore.remove, DStore.setChan, hc.2]
    exact (joinedOf_dropW _ c hm c' hw hr).symm

/-! ## Built-ins on a coherent store -/

theorem dstep_read {st st' : DStore} {c n : Nat} {r : Res} (hc : Coh net st)
    (h : dstep st (.streamRead (rh c) n) = some (st', r)) :
    c < net.m ∧ ∃ c', (st.chans (rh c)).read n = some (c', r) ∧ st' = st.setChan (rh c) c' := by
  simp only [dstep] at h
  split at h
  · rename_i s ht
    rw [hc.1] at ht
    obtain ⟨rfl, -, hm⟩ := tblOf_rh ht
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨c', r'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨hm, c', h1, rfl⟩
  · simp at h

theorem dstep_write {st st' : DStore} {c : Nat} {xs : List Val} {r : Res} (hc : Coh net st)
    (h : dstep st (.streamWrite (wh c) xs) = some (st', r)) :
    c < net.m ∧ ∃ c', (st.chans (rh c)).write xs = some (c', r) ∧ st' = st.setChan (rh c) c' := by
  simp only [dstep] at h
  split at h
  · rename_i s ht
    rw [hc.1] at ht
    obtain ⟨rfl, -, hm⟩ := tblOf_wh ht
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨c', r'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨hm, c', h1, rfl⟩
  · simp at h

theorem dstep_dropR {st st' : DStore} {c : Nat} {r : Res} (hc : Coh net st)
    (h : dstep st (.streamDropR (rh c)) = some (st', r)) :
    c < net.m ∧ ∃ c', (st.chans (rh c)).dropR = some c' ∧
      st' = (st.setChan (rh c) c').remove (rh c) := by
  simp only [dstep] at h
  split at h
  · rename_i s ht
    rw [hc.1] at ht
    obtain ⟨rfl, -, hm⟩ := tblOf_rh ht
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨c', h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    exact ⟨hm, c', h1, h2.1.symm⟩
  · simp at h

theorem dstep_dropW {st st' : DStore} {c : Nat} {r : Res} (hc : Coh net st)
    (h : dstep st (.streamDropW (wh c)) = some (st', r)) :
    c < net.m ∧ ∃ c', (st.chans (rh c)).dropW = some c' ∧
      st' = (st.setChan (rh c) c').remove (wh c) := by
  simp only [dstep] at h
  split at h
  · rename_i s ht
    rw [hc.1] at ht
    obtain ⟨rfl, -, hm⟩ := tblOf_wh ht
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨c', h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    exact ⟨hm, c', h1, h2.1.symm⟩
  · simp at h

theorem wait_rh {st st' : DStore} {s c : Nat} {e : Event} (hc : Coh net st)
    (h : DWait st s (rh c) st' e) :
    c < net.m ∧ ∃ c', (st.chans (rh c)).takeR = some (c', e.payload, e.items) ∧
      st' = st.setChan (rh c) c' := by
  obtain ⟨-, -, h⟩ := h
  simp only [takeEv] at h
  split at h
  · rename_i s' ht
    rw [hc.1] at ht
    obtain ⟨rfl, -, hm⟩ := tblOf_rh ht
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨c', p, ys⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨hm, c', h1, rfl⟩
  · rename_i s' ht
    rw [hc.1] at ht
    unfold tblOf rh at ht
    split_ifs at ht <;> simp_all
  · simp at h

theorem wait_wh {st st' : DStore} {s c : Nat} {e : Event} (hc : Coh net st)
    (h : DWait st s (wh c) st' e) :
    c < net.m ∧ ∃ c', (st.chans (rh c)).takeW = some (c', e.payload) ∧
      st' = st.setChan (rh c) c' := by
  obtain ⟨-, -, h⟩ := h
  simp only [takeEv] at h
  split at h
  · rename_i s' ht
    rw [hc.1] at ht
    unfold tblOf wh at ht
    split_ifs at ht <;> simp_all
  · rename_i s' ht
    rw [hc.1] at ht
    obtain ⟨rfl, -, hm⟩ := tblOf_wh ht
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨c', p⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨hm, c', h1, rfl⟩
  · simp at h

/-! ## The built-ins keep the ends that are not dropped -/

theorem read_gone {c c' : DChan} {n : Nat} {r : Res} (h : c.read n = some (c', r)) :
    c'.r.gone = c.r.gone ∧ c'.w.gone = c.w.gone := by
  unfold DChan.read at h
  split_ifs at h <;> (try split at h) <;> simp_all <;> (obtain ⟨rfl, rfl⟩ := h) <;> simp_all

theorem write_gone {c c' : DChan} {xs : List Val} {r : Res} (h : c.write xs = some (c', r)) :
    c'.r.gone = c.r.gone ∧ c'.w.gone = c.w.gone := by
  unfold DChan.write at h
  split_ifs at h <;> (try split at h) <;> simp_all <;> (obtain ⟨rfl, rfl⟩ := h) <;> simp_all

theorem takeR_gone {c c' : DChan} {p : Nat} {ys : List Val} (h : c.takeR = some (c', p, ys)) :
    c'.r.gone = c.r.gone ∧ c'.w.gone = c.w.gone := by
  unfold DChan.takeR at h
  split at h <;> simp_all
  obtain ⟨rfl, -, -⟩ := h
  simp

theorem takeW_gone {c c' : DChan} {p : Nat} (h : c.takeW = some (c', p)) :
    c'.r.gone = c.r.gone ∧ c'.w.gone = c.w.gone := by
  unfold DChan.takeW at h
  split at h <;> simp_all
  obtain ⟨rfl, -⟩ := h
  simp

theorem dropR_gone {c c' : DChan} (h : c.dropR = some c') :
    c'.r.gone = true ∧ c'.w.gone = c.w.gone := by
  unfold DChan.dropR at h
  by_cases h1 : c.r.gone = true ∨ c.r.st = .copying
  · simp [h1] at h
  · simp only [h1, ↓reduceIte] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, by split <;> rfl⟩

theorem dropW_gone {c c' : DChan} (h : c.dropW = some c') :
    c'.w.gone = true ∧ c'.r.gone = c.r.gone := by
  unfold DChan.dropW at h
  by_cases h1 : c.w.gone = true ∨ c.w.st = .copying
  · simp [h1] at h
  · simp only [h1, ↓reduceIte] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, by split <;> rfl⟩

end Silmaril.Proofs.Wasm.Component.Streams.Net
