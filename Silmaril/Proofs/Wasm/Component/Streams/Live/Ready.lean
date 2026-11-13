module

public import Silmaril.Proofs.Wasm.Component.Streams.Live.Pot

/-!
# The built-ins a node needs are defined

On a coherent store (`Coh`), the handles of a live end are in the table and in the waitable set
of their node (`tbl_rh`, `tbl_wh`, `tbl_ws`, `joined_rh`, `joined_wh`). Under the stream
protocol invariant, the built-in a node wants to call does not trap: a read by an idle reader
(`read_ok`), a write by an idle writer (`write_ok`), the drops (`dropR_ok`, `dropW_ok`), and the
delivery of a pending event (`takeR_ok`, `takeW_ok`). Each `*_step` lemma turns one of them into
a step of the node.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Live

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event upd blocked packCopy CopyResult)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Proofs.Wasm.Component.Streams.Net

variable {net : Network}

/-! ## The handle table of a coherent store -/

theorem tblOf_rh_eq {ch : Nat → DChan} {c : Nat} (hm : c < net.m) (hr : (ch (rh c)).r.gone = false) :
    tblOf net ch (rh c) = some (.streamR (rh c)) := by
  have h1 : rh c ≠ 0 := by simp [rh]
  have h2 : rh c ≤ 2 * net.m := by simp only [rh]; omega
  have h3 : rh c % 2 = 1 := by simp only [rh]; omega
  simp [tblOf, h1, h2, h3, hr]

theorem tblOf_wh_eq {ch : Nat → DChan} {c : Nat} (hm : c < net.m) (hw : (ch (rh c)).w.gone = false) :
    tblOf net ch (wh c) = some (.streamW (rh c)) := by
  have h1 : wh c ≠ 0 := by simp [wh]
  have h2 : wh c ≤ 2 * net.m := by simp only [wh]; omega
  have h3 : ¬ wh c % 2 = 1 := by simp only [wh]; omega
  have h4 : wh c - 1 = rh c := by simp [wh, rh]
  simp [tblOf, h1, h2, h3, h4, hw]

theorem tblOf_ws_eq (ch : Nat → DChan) (i : Fin net.k) :
    tblOf net ch (net.ws i) = some .wset := by
  have h1 : net.ws i ≠ 0 := by simp [Network.ws]
  have h2 : ¬ net.ws i ≤ 2 * net.m := by simp only [Network.ws]; omega
  have h3 : net.ws i ≤ 2 * net.m + net.k := by simp only [Network.ws]; omega
  simp [tblOf, h1, h2, h3]

theorem joinedOf_rh_eq {ch : Nat → DChan} {c : Nat} (hm : c < net.m)
    (hr : (ch (rh c)).r.gone = false) :
    joinedOf net ch (rh c) = some (net.ws (net.rd c)) := by
  have h1 : rh c ≠ 0 := by simp [rh]
  have h2 : rh c ≤ 2 * net.m := by simp only [rh]; omega
  have h3 : rh c % 2 = 1 := by simp only [rh]; omega
  have h4 : rh c / 2 = c := by simp only [rh]; omega
  simp [joinedOf, h1, h2, h3, h4, hr]

theorem joinedOf_wh_eq {ch : Nat → DChan} {c : Nat} (hm : c < net.m)
    (hw : (ch (rh c)).w.gone = false) :
    joinedOf net ch (wh c) = some (net.ws (net.wr c).1) := by
  have h1 : wh c ≠ 0 := by simp [wh]
  have h2 : wh c ≤ 2 * net.m := by simp only [wh]; omega
  have h3 : ¬ wh c % 2 = 1 := by simp only [wh]; omega
  have h4 : wh c - 1 = rh c := by simp [wh, rh]
  have h5 : wh c / 2 - 1 = c := by simp only [wh]; omega
  simp [joinedOf, h1, h2, h3, h4, h5, hw]

/-! ## Built-ins that do not trap -/

theorem read_ok {c : DChan} {n : Nat} (hr : c.r.gone = false) (hst : c.r.st = .idle)
    (hev : c.w.gone = true → c.r.ev.isSome) (hb : c.wbuf ≠ some []) (hn : 0 < n) :
    ∃ c' res, c.read n = some (c', res) ∧ (res = .nat blocked ∨ ∃ p ys, res = .read p ys) := by
  have h0 : ¬(c.r.gone = true ∨ c.r.st ≠ .idle ∨ n = 0) := by simp [hr, hst]; omega
  unfold DChan.read
  simp only [h0, ↓reduceIte]
  by_cases hw : c.w.gone = true
  · simp only [hw, ↓reduceIte]
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hev hw)
    rw [hp]
    exact ⟨_, _, rfl, Or.inr ⟨_, _, rfl⟩⟩
  · simp only [hw]
    rcases hwb : c.wbuf with _ | xs
    · exact ⟨_, _, rfl, Or.inl rfl⟩
    · cases xs with
      | nil => exact absurd hwb hb
      | cons x xs => exact ⟨_, _, rfl, Or.inr ⟨_, _, rfl⟩⟩

theorem write_ok {c : DChan} {xs : List Val} (hw : c.w.gone = false) (hst : c.w.st = .idle)
    (hev : c.r.gone = true → c.w.ev.isSome) (hx : xs ≠ []) :
    ∃ c' r, c.write xs = some (c', .nat r) := by
  have h0 : ¬(c.w.gone = true ∨ c.w.st ≠ .idle ∨ xs = []) := by simp [hw, hst, hx]
  unfold DChan.write
  simp only [h0, ↓reduceIte]
  by_cases hr : c.r.gone = true
  · simp only [hr, ↓reduceIte]
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hev hr)
    rw [hp]
    exact ⟨_, _, rfl⟩
  · simp only [hr]
    rcases c.rcap with _ | n
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

theorem dropR_ok {c : DChan} (hr : c.r.gone = false) (hst : c.r.st ≠ .copying) :
    ∃ c', c.dropR = some c' := by
  have h0 : ¬(c.r.gone = true ∨ c.r.st = .copying) := by simp [hr, hst]
  unfold DChan.dropR
  simp only [h0, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem dropW_ok {c : DChan} (hw : c.w.gone = false) (hst : c.w.st ≠ .copying) :
    ∃ c', c.dropW = some c' := by
  have h0 : ¬(c.w.gone = true ∨ c.w.st = .copying) := by simp [hw, hst]
  unfold DChan.dropW
  simp only [h0, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem takeR_ok {c : DChan} (hev : c.r.ev.isSome) : ∃ c' p ys, c.takeR = some (c', p, ys) := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hev
  unfold DChan.takeR
  rw [hp]
  exact ⟨_, _, _, rfl⟩

theorem takeW_ok {c : DChan} (hev : c.w.ev.isSome) : ∃ c' p, c.takeW = some (c', p) := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hev
  unfold DChan.takeW
  rw [hp]
  exact ⟨_, _, rfl⟩

/-! ## On a coherent store -/

theorem dstep_read_eq {st : DStore} (hc : Coh net st) {c n : Nat} (hm : c < net.m)
    (hr : (st.chans (rh c)).r.gone = false) {c' : DChan} {res : Res}
    (h : (st.chans (rh c)).read n = some (c', res)) :
    dstep st (.streamRead (rh c) n) = some (st.setChan (rh c) c', res) := by
  have ht : st.tbl (rh c) = some (.streamR (rh c)) := by rw [hc.1]; exact tblOf_rh_eq hm hr
  simp [dstep, ht, h]

theorem dstep_write_eq {st : DStore} (hc : Coh net st) {c : Nat} {xs : List Val} (hm : c < net.m)
    (hw : (st.chans (rh c)).w.gone = false) {c' : DChan} {res : Res}
    (h : (st.chans (rh c)).write xs = some (c', res)) :
    dstep st (.streamWrite (wh c) xs) = some (st.setChan (rh c) c', res) := by
  have ht : st.tbl (wh c) = some (.streamW (rh c)) := by rw [hc.1]; exact tblOf_wh_eq hm hw
  simp [dstep, ht, h]

theorem dstep_dropR_eq {st : DStore} (hc : Coh net st) {c : Nat} (hm : c < net.m)
    (hr : (st.chans (rh c)).r.gone = false) {c' : DChan} (h : (st.chans (rh c)).dropR = some c') :
    dstep st (.streamDropR (rh c)) = some ((st.setChan (rh c) c').remove (rh c), .unit) := by
  have ht : st.tbl (rh c) = some (.streamR (rh c)) := by rw [hc.1]; exact tblOf_rh_eq hm hr
  simp [dstep, ht, h]

theorem dstep_dropW_eq {st : DStore} (hc : Coh net st) {c : Nat} (hm : c < net.m)
    (hw : (st.chans (rh c)).w.gone = false) {c' : DChan} (h : (st.chans (rh c)).dropW = some c') :
    dstep st (.streamDropW (wh c)) = some ((st.setChan (rh c) c').remove (wh c), .unit) := by
  have ht : st.tbl (wh c) = some (.streamW (rh c)) := by rw [hc.1]; exact tblOf_wh_eq hm hw
  simp [dstep, ht, h]

theorem wait_rh_ok {st : DStore} (hc : Coh net st) {c : Nat} (hm : c < net.m)
    (hr : (st.chans (rh c)).r.gone = false) (hev : (st.chans (rh c)).r.ev.isSome) :
    ∃ st' e, DWait st (net.ws (net.rd c)) (rh c) st' e := by
  obtain ⟨c', p, ys, h⟩ := takeR_ok hev
  have ht : st.tbl (rh c) = some (.streamR (rh c)) := by rw [hc.1]; exact tblOf_rh_eq hm hr
  have hte : takeEv st (rh c) = some (st.setChan (rh c) c', ⟨.streamRead, rh c, p, ys⟩) := by
    simp [takeEv, ht, h]
  have hs : st.tbl (net.ws (net.rd c)) = some .wset := by rw [hc.1]; exact tblOf_ws_eq _ _
  have hj : st.joined (rh c) = some (net.ws (net.rd c)) := by rw [hc.2]; exact joinedOf_rh_eq hm hr
  exact ⟨_, _, hs, hj, hte⟩

theorem wait_wh_ok {st : DStore} (hc : Coh net st) {c : Nat} (hm : c < net.m)
    (hw : (st.chans (rh c)).w.gone = false) (hev : (st.chans (rh c)).w.ev.isSome) :
    ∃ st' e, DWait st (net.ws (net.wr c).1) (wh c) st' e := by
  obtain ⟨c', p, h⟩ := takeW_ok hev
  have ht : st.tbl (wh c) = some (.streamW (rh c)) := by rw [hc.1]; exact tblOf_wh_eq hm hw
  have hte : takeEv st (wh c) = some (st.setChan (rh c) c', ⟨.streamWrite, wh c, p, []⟩) := by
    simp [takeEv, ht, h]
  have hs : st.tbl (net.ws (net.wr c).1) = some .wset := by rw [hc.1]; exact tblOf_ws_eq _ _
  have hj : st.joined (wh c) = some (net.ws (net.wr c).1) := by
    rw [hc.2]; exact joinedOf_wh_eq hm hw
  exact ⟨_, _, hs, hj, hte⟩

end Silmaril.Proofs.Wasm.Component.Streams.Live
