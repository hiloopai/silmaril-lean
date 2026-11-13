module

public import Silmaril.Wasm.Component.Streams.Net.Defs

/-!
# The stream protocol invariant under the drop-faithful built-ins

One stream (`DChan`) seen by its two ends. The writer's view `WV` (idle, a write of `xs` in
progress, dead, closed) with the items it knows were transferred (`ack`), and the reader's view
`RV` with the items it has received (`got`), are related to the stream's state by `WInv` and
`RInv`, and to each other by `WLink`, `RLink` (a dead writer's reader has gone without seeing the
end; a reader that saw the end has a writer that closed normally).

Each built-in of `Silmaril.Wasm.Component.Streams.Drop` preserves the invariant of the other end and
determines the acting end's new view (`read_spec`, `write_spec`, `takeR_spec`, `takeW_spec`,
`dropR_spec`, `dropW_spec`). In particular a `DROPPED` result carries the items copied before
the peer dropped, and an idle end's `DROPPED` notification is a `DROPPED 0` event.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Net

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res packCopy CopyResult blocked)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net

/-- The writer's view of a stream. -/
inductive WV where
  | idle
  | busy (xs : List Val)
  | dead
  | closed (d : Bool)

/-- The view of an output. -/
def _root_.Silmaril.Wasm.Component.Streams.Net.OS.view : OS → WV
  | .idle _ => .idle
  | .busy xs _ => .busy xs
  | .dead => .dead
  | .closed d => .closed d

/-- The progress of the writer's copy. -/
def _root_.Silmaril.Wasm.Component.Streams.Drop.DChan.wp (c : DChan) : Nat := c.w.ev.getD 0

/-- **The writer's invariant.** -/
def WInv : WV → List Val → DChan → Prop
  | .idle, ack, c => c.w.gone = false ∧ c.w.st = .idle ∧ c.wbuf = none ∧ c.sent = ack ∧
      c.w.ev = (if c.r.gone then some 0 else none)
  | .busy xs, ack, c => c.w.gone = false ∧ c.w.st = .copying ∧ xs ≠ [] ∧ c.wp ≤ xs.length ∧
      c.sent = ack ++ xs.take c.wp ∧
      (c.r.gone = false → c.wbuf = (if c.wp = xs.length then none else some (xs.drop c.wp)) ∧
        (c.wp = xs.length → c.w.ev.isSome)) ∧
      (c.r.gone = true → c.w.ev.isSome)
  | .dead, ack, c => c.w.gone = false ∧ c.w.st = .done ∧ c.r.gone = true ∧ c.w.ev = none ∧
      c.wbuf = none ∧ c.sent = ack
  | .closed _, ack, c => c.w.gone = true ∧ c.wbuf = none ∧ c.sent = ack ∧ c.w.ev = none

/-- **The reader's invariant.** -/
def RInv : RV → List Val → DChan → Prop
  | .idle, got, c => c.sent = got ∧ c.r.gone = false ∧ c.r.st = .idle ∧ c.rcap = none ∧
      c.rgot = [] ∧ c.r.ev = (if c.w.gone then some 0 else none)
  | .busy, got, c => c.sent = got ++ c.rgot ∧ c.r.gone = false ∧ c.r.st = .copying ∧
      (c.r.ev = none → c.rgot = []) ∧ (∀ p, c.r.ev = some p → p = c.rgot.length) ∧
      c.rcap ≠ some 0 ∧ (c.w.gone = false → c.rcap = none → c.r.ev.isSome) ∧
      (c.w.gone = true → c.r.ev.isSome)
  | .ended, got, c => c.sent = got ∧ c.r.gone = false ∧ c.r.st = .done ∧ c.w.gone = true ∧
      c.r.ev = none ∧ c.rgot = [] ∧ c.rcap = none
  | .gone _, got, c => c.sent = got ∧ c.r.gone = true ∧ c.rgot = [] ∧ c.rcap = none ∧
      c.r.ev = none

/-- A dead (or dead, then closed) writer's reader has gone without seeing the end. -/
def WLink (W : WV) (R : RV) : Prop := (W = .dead ∨ W = .closed true) → R = .gone false

/-- A reader that saw the end has a writer that closed normally. -/
def RLink (R : RV) (W : WV) : Prop := (R = .ended ∨ R = .gone true) → W = .closed false

/-- **The stream invariant.** -/
def ChanInv (W : WV) (ack : List Val) (R : RV) (got : List Val) (c : DChan) : Prop :=
  WInv W ack c ∧ RInv R got c ∧ WLink W R ∧ RLink R W

theorem status_packCopy (r : CopyResult) (k : Nat) : status (packCopy r k) = r.toNat := by
  cases r <;> simp [status, packCopy, CopyResult.toNat]

theorem count_packCopy (r : CopyResult) (k : Nat) : count (packCopy r k) = k := by
  cases r <;> simp [count, packCopy, CopyResult.toNat] <;> omega

theorem packCopy_ne_blocked (r : CopyResult) (k : Nat) : packCopy r k ≠ blocked := by
  cases r <;> simp [packCopy, CopyResult.toNat, blocked] <;> omega

/-! ## Frames -/

/-- The writer's invariant depends only on the writer's end, its buffer, the transferred items
and whether the reader has gone. -/
theorem WInv.frame {W : WV} {ack : List Val} {c c' : DChan} (h : WInv W ack c)
    (hw : c'.w = c.w) (hb : c'.wbuf = c.wbuf) (hs : c'.sent = c.sent) (hr : c'.r.gone = c.r.gone) :
    WInv W ack c' := by
  have hp : c'.wp = c.wp := by simp [DChan.wp, hw]
  cases W <;> simp only [WInv, hw, hb, hs, hr, hp] at h ⊢ <;> exact h

/-- The reader's invariant depends only on the reader's end, its buffer, the transferred items
and whether the writer has gone. -/
theorem RInv.frame {R : RV} {got : List Val} {c c' : DChan} (h : RInv R got c)
    (hr : c'.r = c.r) (hc : c'.rcap = c.rcap) (hg : c'.rgot = c.rgot) (hs : c'.sent = c.sent)
    (hw : c'.w.gone = c.w.gone) : RInv R got c' := by
  cases R <;> simp only [RInv, hr, hc, hg, hs, hw] at h ⊢ <;> exact h

theorem WLink.of_idle {W : WV} (h : WLink W .idle) (R : RV) :
    WLink W R := fun hx => absurd (h hx) (by intro h'; cases h')

theorem RLink.not_eof {R : RV} {W : WV} (hR : R = .idle ∨ R = .busy) : RLink R W := by
  intro hx
  rcases hR with rfl | rfl <;> rcases hx with hx | hx <;> cases hx

/-- A writer seen by a reader that has not gone is not dead. -/
theorem WLink.closed_false {d : Bool} {R : RV} (h : WLink (.closed d) R) (hR : R ≠ .gone false) :
    d = false := by
  cases d
  · rfl
  · exact absurd (h (Or.inr rfl)) hR

theorem ite_drop (xs : List Val) (k : Nat) (hk : k ≤ xs.length) :
    (if xs.drop k = [] then none else some (xs.drop k)) =
      (if k = xs.length then none else some (xs.drop k)) := by
  by_cases he : k = xs.length
  · simp [he]
  · have hne : xs.drop k ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff]
      omega
    simp [he, hne]

/-! ## Reading -/

/-- A writer that has gone is closed. -/
theorem W_closed {W : WV} {ack : List Val} {c : DChan} (hW : WInv W ack c)
    (hwg : c.w.gone = true) : ∃ d, W = .closed d := by
  cases W with
  | closed d => exact ⟨d, rfl⟩
  | idle => exact absurd hW.1 (by simp [hwg])
  | busy xs => exact absurd hW.1 (by simp [hwg])
  | dead => exact absurd hW.1 (by simp [hwg])

/-- A reader that has gone has dropped its end. -/
theorem R_gone {R : RV} {got : List Val} {c : DChan} (hR : RInv R got c)
    (hrg : c.r.gone = true) : ∃ e, R = .gone e := by
  cases R with
  | gone e => exact ⟨e, rfl⟩
  | idle => exact absurd hR.2.1 (by simp [hrg])
  | busy => exact absurd hR.2.1 (by simp [hrg])
  | ended => exact absurd hR.2.1 (by simp [hrg])

/-- The writer's open buffer is the rest of its write. -/
theorem wbuf_busy {xs ack zs : List Val} {c : DChan} (hW : WInv (.busy xs) ack c)
    (hrg : c.r.gone = false) (hwb : c.wbuf = some zs) : c.wp < xs.length ∧ xs.drop c.wp = zs := by
  obtain ⟨hbuf, -⟩ := hW.2.2.2.2.2.1 hrg
  have hle : c.wp ≤ xs.length := hW.2.2.2.1
  rw [hwb] at hbuf
  have hlt : c.wp < xs.length := by
    by_contra hc
    have : c.wp = xs.length := by omega
    simp [this] at hbuf
  have hz : some zs = some (xs.drop c.wp) := by simpa [Nat.ne_of_lt hlt] using hbuf
  exact ⟨hlt, (Option.some.inj hz).symm⟩

/-- Copying `m` more items of a write whose first `k` items were copied. -/
theorem copy_arith {xs zs : List Val} {k m : Nat} (hlt : k < xs.length) (hd : xs.drop k = zs)
    (hm : m ≤ zs.length) :
    k + m ≤ xs.length ∧ xs.take k ++ zs.take m = xs.take (k + m) ∧
      zs.drop m = xs.drop (k + m) := by
  have hlen : zs.length = xs.length - k := by rw [← hd, List.length_drop]
  refine ⟨by omega, ?_, ?_⟩
  · rw [← hd, ← List.take_add]
  · rw [← hd, List.drop_drop]

/-- The writer's invariant after a read copies `m = min n |zs|` items from its open buffer `zs`. -/
theorem read_copy_W {xs ack zs : List Val} {c c' : DChan} {n : Nat} (hW : WInv (.busy xs) ack c)
    (hrg : c.r.gone = false) (hwb : c.wbuf = some zs) (h1 : c'.w.gone = c.w.gone)
    (h2 : c'.w.st = c.w.st) (h3 : c'.w.ev = some (c.w.ev.getD 0 + min n zs.length))
    (h4 : c'.wbuf = if zs.drop (min n zs.length) = [] then none
      else some (zs.drop (min n zs.length)))
    (h5 : c'.sent = c.sent ++ zs.take (min n zs.length)) : WInv (.busy xs) ack c' := by
  obtain ⟨hlt, hd⟩ := wbuf_busy hW hrg hwb
  obtain ⟨hmle, htake, hdrop⟩ := copy_arith (m := min n zs.length) hlt hd (Nat.min_le_right _ _)
  have hsent : c.sent = ack ++ xs.take c.wp := hW.2.2.2.2.1
  have hwp : c'.wp = c.wp + min n zs.length := by simp [DChan.wp, h3]
  refine ⟨h1.trans hW.1, h2.trans hW.2.1, hW.2.2.1, hwp ▸ hmle, ?_, fun _ => ?_, fun _ => ?_⟩
  · rw [h5, hwp, hsent, List.append_assoc, htake]
  · refine ⟨?_, fun _ => by simp [h3]⟩
    rw [h4, hwp, hdrop]
    exact ite_drop _ _ hmle
  · simp [h3]

theorem read_blocked {W : WV} {ack got : List Val} {c c' : DChan} {n : Nat} {res : Res}
    (hW : WInv W ack c) (hWL : WLink W .idle) (hR : RInv .idle got c) (hwg : c.w.gone = false)
    (hwb : c.wbuf = none) (hn : n ≠ 0) (h : c.read n = some (c', res)) :
    res = .nat blocked ∧ ChanInv W ack .busy got c' := by
  obtain ⟨hs, hrg, hrst, hrc, hrgot, hrev⟩ := hR
  simp only [DChan.read, hrg, hrst, hn, hwg, hwb, Bool.false_eq_true, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, hW.frame rfl (by simp [hwb]) rfl (by simp [hrg]), ?_, WLink.of_idle hWL _,
    RLink.not_eof (Or.inr rfl)⟩
  simp [RInv, hs, hrev, hwg, hn]

theorem read_copy {W : WV} {ack got : List Val} {c c' : DChan} {n : Nat} {res : Res}
    {y : Val} {ys : List Val} (hW : WInv W ack c) (hWL : WLink W .idle) (hR : RInv .idle got c)
    (hwg : c.w.gone = false) (hwb : c.wbuf = some (y :: ys)) (hn : n ≠ 0)
    (h : c.read n = some (c', res)) :
    ∃ p ys, res = .read p ys ∧
      ChanInv W ack (if status p = 0 then .idle else .ended) (got ++ ys) c' := by
  obtain ⟨hs, hrg, hrst, hrc, hrgot, hrev⟩ := hR
  simp only [DChan.read, hrg, hrst, hn, hwg, hwb, Bool.false_eq_true, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨_, _, rfl, ?_⟩
  have hst : status (packCopy .completed (min n (y :: ys).length)) = 0 := by
    rw [status_packCopy]; rfl
  obtain ⟨xs, rfl⟩ : ∃ xs, W = .busy xs := by
    cases W with
    | busy xs => exact ⟨xs, rfl⟩
    | idle | dead | closed _ => simp [WInv, hwb] at hW
  simp only [hst, ↓reduceIte]
  refine ⟨read_copy_W (n := n) hW hrg hwb hwg.symm rfl rfl rfl rfl, ?_, WLink.of_idle hWL _,
    RLink.not_eof (Or.inl rfl)⟩
  exact ⟨by rw [hs], hrg, hrst, hrc, hrgot, by simpa [hwg] using hrev⟩

theorem read_dropped {W : WV} {ack got : List Val} {c c' : DChan} {n : Nat} {res : Res}
    (hW : WInv W ack c) (hWL : WLink W .idle) (hR : RInv .idle got c) (hwg : c.w.gone = true)
    (hn : n ≠ 0) (h : c.read n = some (c', res)) :
    ∃ p ys, res = .read p ys ∧
      ChanInv W ack (if status p = 0 then .idle else .ended) (got ++ ys) c' := by
  obtain ⟨hs, hrg, hrst, hrc, hrgot, hrev⟩ := hR
  have hrev' : c.r.ev = some 0 := by simpa [hwg] using hrev
  simp only [DChan.read, hrg, hrst, hn, hwg, hrev', Bool.false_eq_true, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨_, _, rfl, ?_⟩
  have hst : status (packCopy .dropped 0) ≠ 0 := by rw [status_packCopy]; decide
  obtain ⟨d, rfl⟩ := W_closed hW hwg
  obtain rfl := hWL.closed_false (R := .idle) (by intro h; cases h)
  simp only [hst, ↓reduceIte]
  refine ⟨hW.frame rfl rfl rfl (by simp [hrg]), ?_, fun hx => ?_, fun _ => rfl⟩
  · simp [RInv, hs, hrgot, hwg]
  · rcases hx with hx | hx <;> cases hx

/-- **`stream.read` by an idle reader.** Either it blocks, or it completes at once with the items
it delivers (and the reader stays idle), or it reports the end (`DROPPED`, with no items). -/
theorem read_spec {W : WV} {ack got : List Val} {c c' : DChan} {n : Nat} {res : Res}
    (hI : ChanInv W ack .idle got c) (h : c.read n = some (c', res)) :
    (res = .nat blocked ∧ ChanInv W ack .busy got c') ∨
    (∃ p ys, res = .read p ys ∧
      ChanInv W ack (if status p = 0 then .idle else .ended) (got ++ ys) c') := by
  obtain ⟨hW, hR, hWL, -⟩ := hI
  have hn : n ≠ 0 := by
    intro hn
    simp [DChan.read, hn] at h
  cases hwg : c.w.gone
  · rcases hwb : c.wbuf with _ | _ | ⟨y, ys⟩
    · exact Or.inl (read_blocked hW hWL hR hwg hwb hn h)
    · exact absurd h (by simp [DChan.read, hR.2.1, hR.2.2.1, hn, hwg, hwb])
    · exact Or.inr (read_copy hW hWL hR hwg hwb hn h)
  · exact Or.inr (read_dropped hW hWL hR hwg hn h)

/-! ## Writing -/

theorem write_blocked {R : RV} {ack got ys rest : List Val} {c c' : DChan} {res : Res}
    (hW : WInv .idle ack c) (hR : RInv R got c) (hRL : RLink R .idle) (hys : ys ≠ [])
    (hrg : c.r.gone = false) (hrc : c.rcap = none) (h : c.write ys = some (c', res)) :
    ∃ r, res = .nat r ∧ ChanInv (Out.afterWrite ys rest ack r).st.view
      (Out.afterWrite ys rest ack r).ack R got c' := by
  obtain ⟨hwg, hwst, hwb, hs, hwev⟩ := hW
  have hev : c.w.ev = none := by simpa [hrg] using hwev
  simp only [DChan.write, hwg, hwst, hys, hrg, hrc, Bool.false_eq_true, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hl : ys.length ≠ 0 := by simpa using hys
  refine ⟨_, rfl, ?_⟩
  simp only [Out.afterWrite, ↓reduceIte, OS.view]
  refine ⟨⟨rfl, rfl, hys, by simp [DChan.wp, hev], by simp [DChan.wp, hev, hs],
    fun _ => ⟨by simp [DChan.wp, hev, Ne.symm hl], fun he => by simp [DChan.wp, hev] at he; omega⟩,
    fun hx => by simp [hrg] at hx⟩, hR.frame rfl hrc.symm rfl rfl (by simp [hwg]),
    fun hx => ?_, fun hx => absurd (hRL hx) (by intro h; cases h)⟩
  rcases hx with hx | hx <;> cases hx

/-- The reader's invariant after a write copies `m = min n |ys|` items into its open buffer. -/
theorem write_copy_R {got ys : List Val} {c c' : DChan} {n : Nat} (hR : RInv .busy got c)
    (h1 : c'.r.gone = c.r.gone) (h2 : c'.r.st = c.r.st)
    (h3 : c'.r.ev = some (c.rgot.length + min n ys.length))
    (h4 : c'.rgot = c.rgot ++ ys.take (min n ys.length))
    (h5 : c'.rcap = if n - min n ys.length = 0 then none else some (n - min n ys.length))
    (h6 : c'.sent = c.sent ++ ys.take (min n ys.length)) : RInv .busy got c' := by
  obtain ⟨hsR, hrg', hrst, -, -, -, -, -⟩ := hR
  have hm : (ys.take (min n ys.length)).length = min n ys.length := by simp
  refine ⟨by simp [h6, h4, hsR], h1.trans hrg', h2.trans hrst, fun hx => by simp [h3] at hx,
    fun p hp => ?_, ?_, fun _ _ => by simp [h3], fun _ => by simp [h3]⟩
  · have hp' : c.rgot.length + min n ys.length = p := by simpa [h3] using hp
    simp [h4, ← hp', hm]
  · rw [h5]
    by_cases hz : n - min n ys.length = 0 <;> simp [hz]

theorem write_copy {R : RV} {ack got ys rest : List Val} {c c' : DChan} {res : Res} {n : Nat}
    (hW : WInv .idle ack c) (hR : RInv R got c) (hys : ys ≠ [])
    (hrg : c.r.gone = false) (hrc : c.rcap = some n) (h : c.write ys = some (c', res)) :
    ∃ r, res = .nat r ∧ ChanInv (Out.afterWrite ys rest ack r).st.view
      (Out.afterWrite ys rest ack r).ack R got c' := by
  obtain ⟨hwg, hwst, hwb, hs, hwev⟩ := hW
  simp only [DChan.write, hwg, hwst, hys, hrg, hrc, Bool.false_eq_true, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨_, rfl, ?_⟩
  have hnb := packCopy_ne_blocked .completed (min n ys.length)
  simp only [Out.afterWrite, hnb, ↓reduceIte, Out.onWrite, status_packCopy, count_packCopy,
    CopyResult.toNat, OS.view]
  obtain rfl : R = .busy := by
    cases R with
    | busy => rfl
    | idle | ended | gone _ => simp [RInv, hrc] at hR
  refine ⟨⟨hwg, hwst, hwb, by simp [hs], by simp [hwev, hrg]⟩,
    write_copy_R (ys := ys) hR hrg.symm rfl rfl rfl rfl rfl,
    fun hx => ?_, fun hx => ?_⟩ <;> rcases hx with hx | hx <;> cases hx

theorem write_dropped {R : RV} {ack got ys rest : List Val} {c c' : DChan} {res : Res}
    (hW : WInv .idle ack c) (hR : RInv R got c) (hRL : RLink R .idle) (hys : ys ≠ [])
    (hrg : c.r.gone = true) (h : c.write ys = some (c', res)) :
    ∃ r, res = .nat r ∧ ChanInv (Out.afterWrite ys rest ack r).st.view
      (Out.afterWrite ys rest ack r).ack R got c' := by
  obtain ⟨hwg, hwst, hwb, hs, hwev⟩ := hW
  have hev : c.w.ev = some 0 := by simpa [hrg] using hwev
  simp only [DChan.write, hwg, hwst, hys, hrg, hev, Bool.false_eq_true, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨_, rfl, ?_⟩
  have hnb := packCopy_ne_blocked .dropped 0
  simp only [Out.afterWrite, hnb, ↓reduceIte, Out.onWrite, status_packCopy, count_packCopy,
    CopyResult.toNat, OS.view, Nat.one_ne_zero, List.take_zero, List.append_nil]
  obtain ⟨e, rfl⟩ := R_gone hR hrg
  obtain rfl : e = false := by
    cases e
    · rfl
    · exact absurd (hRL (Or.inr rfl)) (by intro h; cases h)
  exact ⟨⟨rfl, rfl, hrg, rfl, rfl, hs⟩, hR.frame rfl rfl rfl rfl (by simp [hwg]), fun _ => rfl,
    fun hx => by rcases hx with hx | hx <;> cases hx⟩

/-- **`stream.write` by an idle writer** of a nonempty `ys` (then `rest`): the writer's new view is
`Out.afterWrite` of the result. -/
theorem write_spec {R : RV} {ack got ys rest : List Val} {c c' : DChan} {res : Res}
    (hI : ChanInv .idle ack R got c) (h : c.write ys = some (c', res)) :
    ∃ r, res = .nat r ∧ ChanInv (Out.afterWrite ys rest ack r).st.view
      (Out.afterWrite ys rest ack r).ack R got c' := by
  obtain ⟨hW, hR, -, hRL⟩ := hI
  have hys : ys ≠ [] := by
    intro he
    simp [DChan.write, he] at h
  cases hrg : c.r.gone
  · rcases hrc : c.rcap with _ | n
    · exact write_blocked hW hR hRL hys hrg hrc h
    · exact write_copy hW hR hys hrg hrc h
  · exact write_dropped hW hR hRL hys hrg h

/-! ## Events -/

/-- A reader with a pending event is idle or busy, and the stream's items are those it has read and
those in its buffer. -/
theorem takeR_R {R : RV} {got : List Val} {c : DChan} {q : Nat} (hR : RInv R got c)
    (hev : c.r.ev = some q) :
    (R = .idle ∨ R = .busy) ∧ c.sent = got ++ c.rgot ∧ c.r.gone = false := by
  cases R with
  | idle => exact ⟨Or.inl rfl, by simp [hR.1, hR.2.2.2.2.1], hR.2.1⟩
  | busy => exact ⟨Or.inr rfl, hR.1, hR.2.1⟩
  | ended => exact absurd hev (by simp [hR.2.2.2.2.1])
  | gone e => exact absurd hev (by simp [hR.2.2.2.2])

theorem takeR_live {W : WV} {ack got ys : List Val} {c c' : DChan} {p q : Nat}
    (hW : WInv W ack c) (hWL : WLink W .idle) (hsent : c.sent = got ++ c.rgot)
    (hrg : c.r.gone = false) (hev : c.r.ev = some q) (hwg : c.w.gone = false)
    (h : c.takeR = some (c', p, ys)) :
    ChanInv W ack (if status p = 0 then .idle else .ended) (got ++ ys) c' := by
  simp only [DChan.takeR, hev, hwg, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hst : status (packCopy .completed q) = 0 := by rw [status_packCopy]; rfl
  simp only [hst, ↓reduceIte]
  refine ⟨hW.frame rfl rfl rfl (by simp [hrg]), ?_, WLink.of_idle hWL _, RLink.not_eof (Or.inl rfl)⟩
  simp [RInv, hsent, hrg, hwg]

theorem takeR_dropped {W : WV} {ack got ys : List Val} {c c' : DChan} {p q : Nat}
    (hW : WInv W ack c) (hWL : WLink W .idle) (hsent : c.sent = got ++ c.rgot)
    (hrg : c.r.gone = false) (hev : c.r.ev = some q) (hwg : c.w.gone = true)
    (h : c.takeR = some (c', p, ys)) :
    ChanInv W ack (if status p = 0 then .idle else .ended) (got ++ ys) c' := by
  simp only [DChan.takeR, hev, hwg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hst : status (packCopy .dropped q) ≠ 0 := by rw [status_packCopy]; decide
  simp only [hst, ↓reduceIte]
  obtain ⟨d, rfl⟩ := W_closed hW hwg
  obtain rfl := hWL.closed_false (by intro h; cases h)
  refine ⟨hW.frame rfl rfl rfl (by simp [hrg]), ?_, fun hx => ?_, fun _ => rfl⟩
  · simp [RInv, hsent, hrg, hwg]
  · rcases hx with hx | hx <;> cases hx

/-- **A read event**: delivered to an idle reader (the writer dropped) or a busy one. -/
theorem takeR_spec {W : WV} {R : RV} {ack got ys : List Val} {c c' : DChan} {p : Nat}
    (hI : ChanInv W ack R got c) (h : c.takeR = some (c', p, ys)) :
    (R = .idle ∨ R = .busy) ∧
      ChanInv W ack (if status p = 0 then .idle else .ended) (got ++ ys) c' := by
  obtain ⟨hW, hR, hWL, -⟩ := hI
  rcases hev : c.r.ev with _ | q
  · simp [DChan.takeR, hev] at h
  obtain ⟨hRi, hsent, hrg⟩ := takeR_R hR hev
  have hWL' : WLink W .idle := fun hx => by
    have := hWL hx
    rcases hRi with rfl | rfl <;> cases this
  refine ⟨hRi, ?_⟩
  cases hwg : c.w.gone
  · exact takeR_live hW hWL' hsent hrg hev hwg h
  · exact takeR_dropped hW hWL' hsent hrg hev hwg h

theorem takeW_live {R : RV} {got : List Val} {o : Out} {c c' : DChan} {p q : Nat}
    (hW : WInv o.st.view o.ack c) (hR : RInv R got c) (hRL : RLink R o.st.view)
    (hev : c.w.ev = some q) (hrg : c.r.gone = false) (h : c.takeW = some (c', p)) :
    ChanInv (o.onWrite p).st.view (o.onWrite p).ack R got c' := by
  simp only [DChan.takeW, hev, hrg, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨st, ack⟩ := o
  obtain ⟨xs, q', rfl⟩ : ∃ xs q', st = .busy xs q' := by
    cases st with
    | busy xs q' => exact ⟨xs, q', rfl⟩
    | idle _ | dead | closed _ => simp [OS.view, WInv, hev, hrg] at hW
  obtain ⟨hg, hst, hne, hle, hsent, hb, -⟩ := hW
  have hq : c.wp = q := by simp [DChan.wp, hev]
  simp only [Out.onWrite, status_packCopy, count_packCopy, CopyResult.toNat, ↓reduceIte, OS.view]
  refine ⟨⟨hg, rfl, rfl, by rw [← hq]; exact hsent, by simp [hrg]⟩,
    hR.frame rfl rfl rfl rfl rfl, fun hx => ?_, fun hx => absurd (hRL hx) (by intro h; cases h)⟩
  rcases hx with hx | hx <;> cases hx

/-- A reader that has gone, with an idle or busy writer, has not seen the end. -/
theorem gone_false {e : Bool} {W : WV} (hRL : RLink (.gone e) W) (hW : W ≠ .closed false) :
    e = false := by
  cases e
  · rfl
  · exact absurd (hRL (Or.inr rfl)) hW

theorem takeW_gone_idle {got : List Val} {q' ack : List Val} {c c' : DChan} {p q : Nat} {e : Bool}
    (hW : WInv .idle ack c) (hR : RInv (.gone e) got c) (hRL : RLink (.gone e) .idle)
    (hev : c.w.ev = some q) (hrg : c.r.gone = true) (h : c.takeW = some (c', p)) :
    ChanInv (Out.onWrite ⟨.idle q', ack⟩ p).st.view (Out.onWrite ⟨.idle q', ack⟩ p).ack
      (.gone e) got c' := by
  simp only [DChan.takeW, hev, hrg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl := gone_false hRL (by intro h; cases h)
  have hst : status (packCopy .dropped q) ≠ 0 := by rw [status_packCopy]; decide
  obtain ⟨hg, -, -, hsent, -⟩ := hW
  simp only [Out.onWrite, hst, ↓reduceIte, OS.view]
  exact ⟨⟨hg, rfl, hrg, rfl, rfl, hsent⟩, hR.frame rfl rfl rfl rfl rfl, fun _ => rfl,
    fun hx => by rcases hx with hx | hx <;> cases hx⟩

theorem takeW_gone_busy {got : List Val} {xs q' ack : List Val} {c c' : DChan} {p q : Nat}
    {e : Bool} (hW : WInv (.busy xs) ack c) (hR : RInv (.gone e) got c)
    (hRL : RLink (.gone e) (.busy xs)) (hev : c.w.ev = some q) (hrg : c.r.gone = true)
    (h : c.takeW = some (c', p)) :
    ChanInv (Out.onWrite ⟨.busy xs q', ack⟩ p).st.view (Out.onWrite ⟨.busy xs q', ack⟩ p).ack
      (.gone e) got c' := by
  simp only [DChan.takeW, hev, hrg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl := gone_false hRL (by intro h; cases h)
  have hst : status (packCopy .dropped q) ≠ 0 := by rw [status_packCopy]; decide
  obtain ⟨hg, -, -, -, hsent, -, -⟩ := hW
  have hq : c.wp = q := by simp [DChan.wp, hev]
  simp only [Out.onWrite, hst, ↓reduceIte, OS.view, count_packCopy]
  exact ⟨⟨hg, rfl, hrg, rfl, rfl, by rw [← hq]; exact hsent⟩, hR.frame rfl rfl rfl rfl rfl,
    fun _ => rfl, fun hx => by rcases hx with hx | hx <;> cases hx⟩

theorem takeW_dropped {R : RV} {got : List Val} {o : Out} {c c' : DChan} {p q : Nat}
    (hW : WInv o.st.view o.ack c) (hR : RInv R got c) (hRL : RLink R o.st.view)
    (hev : c.w.ev = some q) (hrg : c.r.gone = true) (h : c.takeW = some (c', p)) :
    ChanInv (o.onWrite p).st.view (o.onWrite p).ack R got c' := by
  obtain ⟨e, rfl⟩ := R_gone hR hrg
  obtain ⟨st, ack⟩ := o
  cases st with
  | dead | closed _ => simp [OS.view, WInv, hev] at hW
  | idle q' => exact takeW_gone_idle hW hR hRL hev hrg h
  | busy xs q' => exact takeW_gone_busy hW hR hRL hev hrg h

/-- **A write event** on the output `o`: its new state is `o.onWrite` of the result. -/
theorem takeW_spec {R : RV} {got : List Val} {o : Out} {c c' : DChan} {p : Nat}
    (hI : ChanInv o.st.view o.ack R got c) (h : c.takeW = some (c', p)) :
    ChanInv (o.onWrite p).st.view (o.onWrite p).ack R got c' := by
  obtain ⟨hW, hR, -, hRL⟩ := hI
  rcases hev : c.w.ev with _ | q
  · simp [DChan.takeW, hev] at h
  cases hrg : c.r.gone
  · exact takeW_live hW hR hRL hev hrg h
  · exact takeW_dropped hW hR hRL hev hrg h

/-! ## Dropping -/

/-- The writer's invariant after the reader drops its end. -/
theorem dropR_W {W : WV} {ack : List Val} {c : DChan} (hW : WInv W ack c)
    (hrg : c.r.gone = false) :
    WInv W ack
      { c with
        r := { c.r with gone := true, ev := none },
        w := if c.w.gone = false ∧ c.w.st ≠ .done ∧ c.w.ev = none
          then { c.w with ev := some 0 } else c.w } := by
  cases W with
  | idle =>
    obtain ⟨hg, hst, hwb, hsent, hev⟩ := hW
    have hev' : c.w.ev = none := by simpa [hrg] using hev
    simp [WInv, hg, hst, hwb, hsent, hev']
  | busy xs =>
    obtain ⟨hg, hst, hne, hle, hsent, hb, -⟩ := hW
    obtain ⟨hbuf, hfull⟩ := hb hrg
    by_cases hev : c.w.ev = none
    · refine ⟨?_, ?_, hne, ?_, ?_, ?_, ?_⟩ <;> simp_all [DChan.wp]
    · refine ⟨?_, ?_, hne, ?_, ?_, ?_, ?_⟩ <;> simp_all [DChan.wp, Option.isSome_iff_ne_none]
  | dead => simp [WInv, hrg] at hW
  | closed d =>
    obtain ⟨hg, hwb, hsent, hev⟩ := hW
    simp [WInv, hg, hwb, hsent, hev]

/-- The reader's invariant after it drops its end. -/
theorem dropR_R {R : RV} {got : List Val} {c : DChan} (hR : RInv R got c)
    (hR0 : R = .idle ∨ R = .ended) :
    RInv (.gone (decide (R = .ended))) got
      { c with
        r := { c.r with gone := true, ev := none },
        w := if c.w.gone = false ∧ c.w.st ≠ .done ∧ c.w.ev = none
          then { c.w with ev := some 0 } else c.w } := by
  rcases hR0 with rfl | rfl
  · obtain ⟨hs, -, -, hrc, hrgot, -⟩ := hR
    simp [RInv, hs, hrc, hrgot]
  · obtain ⟨hs, -, -, -, -, hrgot, hrc⟩ := hR
    simp [RInv, hs, hrc, hrgot]

/-- **`stream.drop-readable`** by an idle reader or one that saw the end. -/
theorem dropR_spec {W : WV} {R : RV} {ack got : List Val} {c c' : DChan}
    (hI : ChanInv W ack R got c) (hR0 : R = .idle ∨ R = .ended) (h : c.dropR = some c') :
    ChanInv W ack (.gone (decide (R = .ended))) got c' := by
  obtain ⟨hW, hR, hWL, hRL⟩ := hI
  have hrg : c.r.gone = false := by rcases hR0 with rfl | rfl <;> exact hR.2.1
  have hrst : c.r.st ≠ .copying := by rcases hR0 with rfl | rfl <;> simp [hR.2.2.1]
  simp only [DChan.dropR, hrg, hrst, Bool.false_eq_true, false_or, ↓reduceIte,
    Option.some.injEq] at h
  subst h
  refine ⟨dropR_W hW hrg, dropR_R hR hR0, fun hx => ?_, fun hx => ?_⟩
  · have := hWL hx
    rcases hR0 with rfl | rfl <;> cases this
  · rcases hR0 with rfl | rfl
    · simp at hx
    · exact hRL (Or.inl rfl)

/-- The reader's invariant after the writer drops its end. -/
theorem dropW_R {R : RV} {got : List Val} {c : DChan} (hR : RInv R got c)
    (hwg : c.w.gone = false) (hRne : R ≠ .ended) :
    RInv R got
      { c with
        w := { c.w with gone := true, ev := none },
        r := if c.r.gone = false ∧ c.r.st ≠ .done ∧ c.r.ev = none
          then { c.r with ev := some 0 } else c.r } := by
  cases R with
  | idle =>
    obtain ⟨hs, hrg, hrst, hrc, hrgot, hev⟩ := hR
    have hev' : c.r.ev = none := by simpa [hwg] using hev
    simp [RInv, hs, hrg, hrst, hrc, hrgot, hev']
  | busy =>
    obtain ⟨hs, hrg, hrst, hev0, hevp, hc0, -, -⟩ := hR
    by_cases hev : c.r.ev = none
    · have hrgot := hev0 hev
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Option.isSome_iff_ne_none]
  | ended => exact absurd rfl hRne
  | gone e =>
    obtain ⟨hs, hrg, hrgot, hrc, hev⟩ := hR
    simp [RInv, hs, hrg, hrgot, hrc, hev]

/-- A reader whose writer is idle or dead has not seen the end. -/
theorem R_not_eof {W : WV} {R : RV} (hRL : RLink R W) (hW0 : W = .idle ∨ W = .dead) :
    R ≠ .ended ∧ R ≠ .gone true := by
  constructor <;> intro hx <;> subst hx
  · have := hRL (Or.inl rfl)
    rcases hW0 with rfl | rfl <;> cases this
  · have := hRL (Or.inr rfl)
    rcases hW0 with rfl | rfl <;> cases this

/-- The writer's invariant after it drops its end. -/
theorem dropW_W {W : WV} {ack : List Val} {c : DChan} {d : Bool} (hW : WInv W ack c)
    (hW0 : W = .idle ∨ W = .dead) :
    WInv (.closed d) ack
      { c with
        w := { c.w with gone := true, ev := none },
        r := if c.r.gone = false ∧ c.r.st ≠ .done ∧ c.r.ev = none
          then { c.r with ev := some 0 } else c.r } := by
  rcases hW0 with rfl | rfl
  · obtain ⟨-, -, hwb, hsent, -⟩ := hW
    simp [WInv, hwb, hsent]
  · obtain ⟨-, -, -, -, hwb, hsent⟩ := hW
    simp [WInv, hwb, hsent]

/-- **`stream.drop-writable`** of an idle or dead output. -/
theorem dropW_spec {W : WV} {R : RV} {ack got : List Val} {c c' : DChan} {d : Bool}
    (hI : ChanInv W ack R got c) (hWd : W = .idle ∧ d = false ∨ W = .dead ∧ d = true)
    (h : c.dropW = some c') : ChanInv (.closed d) ack R got c' := by
  obtain ⟨hW, hR, hWL, hRL⟩ := hI
  have hW0 : W = .idle ∨ W = .dead := by rcases hWd with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hwg : c.w.gone = false := by rcases hW0 with rfl | rfl <;> exact hW.1
  have hwst : c.w.st ≠ .copying := by rcases hW0 with rfl | rfl <;> simp [hW.2.1]
  simp only [DChan.dropW, hwg, hwst, Bool.false_eq_true, false_or, ↓reduceIte,
    Option.some.injEq] at h
  subst h
  have hRne : R ≠ .ended ∧ R ≠ .gone true := R_not_eof hRL hW0
  refine ⟨dropW_W hW hW0, dropW_R hR hwg hRne.1, fun hx => ?_, fun hx => ?_⟩
  · rcases hWd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hx with hx | hx <;> cases hx
    · exact hWL (Or.inl rfl)
  · rcases hx with rfl | rfl
    · exact absurd rfl hRne.1
    · exact absurd rfl hRne.2

end Silmaril.Proofs.Wasm.Component.Streams.Net
