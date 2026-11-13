module

public import Silmaril.Wasm.Component.Streams.Cancel.Defs
public import Silmaril.Wasm.Component.Streams.Net.Defs

/-!
# Cancellation, zero-length copies and futures: proofs

* conservativity: on the channels `Drop` creates (`Good`), `zread`/`zwrite` are `Drop`'s
  `read`/`write` for nonzero copies, `Drop`'s operations keep channels `Good`, and `cstep`
  answers every operation `dstep` answers, in the same way;
* item flow: across every operation, including cancellation and zero-length copies, the items
  transferred are the items handed to the reader followed by those still in its buffer;
* futures: the reader receives at most one value, and it is the value written.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Cancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event EventCode CopyResult packCopy blocked upd)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Cancel

/-! ## Conservativity -/

theorem zread_eq {c : DChan} {n : Nat} (hc : c.Good) (hn : 0 < n) : c.zread n = c.read n := by
  have hn' : n ≠ 0 := by omega
  unfold DChan.zread DChan.read
  by_cases h1 : c.r.gone = true ∨ c.r.st ≠ .idle
  · rw [ite_eq_left h1, ite_eq_left (by tauto)]
  have h1' : ¬(c.r.gone = true ∨ c.r.st ≠ .idle ∨ n = 0) := by tauto
  rw [ite_eq_right h1, ite_eq_right h1']
  split
  · rfl
  · rcases hw : c.wbuf with _ | _ | ⟨x, xs⟩
    · rfl
    · exact absurd hw hc.1
    · simp

theorem zwrite_eq {c : DChan} {xs : List Val} (hc : c.Good) (hx : xs ≠ []) :
    c.zwrite xs = c.write xs := by
  unfold DChan.zwrite DChan.write
  by_cases h1 : c.w.gone = true ∨ c.w.st ≠ .idle
  · rw [ite_eq_left h1, ite_eq_left (by tauto)]
  have h1' : ¬(c.w.gone = true ∨ c.w.st ≠ .idle ∨ xs = []) := by tauto
  rw [ite_eq_right h1, ite_eq_right h1']
  split
  · rfl
  · rcases hr : c.rcap with _ | _ | n
    · rfl
    · exact absurd hr hc.2
    · simp

theorem zread_of_read {c : DChan} {n : Nat} {p : DChan × Res} (hc : c.Good)
    (h : c.read n = some p) : c.zread n = some p := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [DChan.read] at h
  · rw [zread_eq hc hn]; exact h

theorem zwrite_of_write {c : DChan} {xs : List Val} {p : DChan × Res} (hc : c.Good)
    (h : c.write xs = some p) : c.zwrite xs = some p := by
  by_cases hx : xs = []
  · subst hx; simp [DChan.write] at h
  · rw [zwrite_eq hc hx]; exact h

theorem good_read {c c' : DChan} {n : Nat} {r : Res} (hc : c.Good) (h : c.read n = some (c', r)) :
    c'.Good := by
  unfold DChan.read at h
  by_cases h1 : c.r.gone = true ∨ c.r.st ≠ .idle ∨ n = 0
  · rw [ite_eq_left h1] at h; simp at h
  have hn : n ≠ 0 := by tauto
  rw [ite_eq_right h1] at h
  by_cases h2 : c.w.gone = true
  · rw [ite_eq_left h2] at h
    cases he : c.r.ev <;> simp [he] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hc.1, by simp⟩
  rw [ite_eq_right h2] at h
  rcases hw : c.wbuf with _ | _ | ⟨x, xs⟩ <;> simp [hw] at h
  · obtain ⟨rfl, -⟩ := h
    exact ⟨by simp, by simpa using hn⟩
  · obtain ⟨rfl, -⟩ := h
    refine ⟨?_, hc.2⟩
    split <;> simp_all

theorem good_write {c c' : DChan} {xs : List Val} {r : Res} (hc : c.Good)
    (h : c.write xs = some (c', r)) : c'.Good := by
  unfold DChan.write at h
  by_cases h1 : c.w.gone = true ∨ c.w.st ≠ .idle ∨ xs = []
  · rw [ite_eq_left h1] at h; simp at h
  have hx : xs ≠ [] := by tauto
  rw [ite_eq_right h1] at h
  by_cases h2 : c.r.gone = true
  · rw [ite_eq_left h2] at h
    cases he : c.w.ev <;> simp [he] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨by simp, hc.2⟩
  rw [ite_eq_right h2] at h
  rcases hr : c.rcap with _ | n <;> simp [hr] at h
  · obtain ⟨rfl, -⟩ := h
    exact ⟨by simpa using hx, by simp⟩
  · obtain ⟨rfl, -⟩ := h
    refine ⟨hc.1, ?_⟩
    split <;> simp_all

theorem good_takeR {c c' : DChan} {p : Nat} {ys : List Val} (hc : c.Good)
    (h : c.takeR = some (c', p, ys)) : c'.Good := by
  unfold DChan.takeR at h
  cases he : c.r.ev <;> simp [he] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨hc.1, by simp⟩

theorem good_takeW {c c' : DChan} {p : Nat} (hc : c.Good) (h : c.takeW = some (c', p)) :
    c'.Good := by
  unfold DChan.takeW at h
  cases he : c.w.ev <;> simp [he] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨by simp, hc.2⟩

theorem good_dropR {c c' : DChan} (hc : c.Good) (h : c.dropR = some c') : c'.Good := by
  unfold DChan.dropR at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h; subst h; exact hc)

theorem good_dropW {c c' : DChan} (hc : c.Good) (h : c.dropW = some c') : c'.Good := by
  unfold DChan.dropW at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h; subst h; exact hc)

theorem goodS_setChan {st : DStore} {s : Nat} {c : DChan} (hst : GoodS st) (hc : c.Good) :
    GoodS (st.setChan s c) := by
  intro t
  by_cases h : t = s
  · subst h; simpa [DStore.setChan, upd] using hc
  · simpa [DStore.setChan, upd, h] using hst t

theorem goodS_remove {st : DStore} {h : Nat} (hst : GoodS st) : GoodS (st.remove h) := hst

theorem dstep_good_rw {st st' : DStore} {w : Nat} {xs : List Val} {r : Res} (hst : GoodS st)
    (h : dstep st (.streamWrite w xs) = some (st', r)) : GoodS st' := by
  simp only [dstep] at h
  split at h
  · obtain ⟨⟨c', r'⟩, hc, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact goodS_setChan hst (good_write (hst _) hc)
  · simp at h

theorem dstep_good_rd {st st' : DStore} {r' n : Nat} {r : Res} (hst : GoodS st)
    (h : dstep st (.streamRead r' n) = some (st', r)) : GoodS st' := by
  simp only [dstep] at h
  split at h
  · obtain ⟨⟨c', r''⟩, hc, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact goodS_setChan hst (good_read (hst _) hc)
  · simp at h

theorem dstep_good_dr {st st' : DStore} {r' : Nat} {r : Res} (hst : GoodS st)
    (h : dstep st (.streamDropR r') = some (st', r)) : GoodS st' := by
  simp only [dstep] at h
  split at h
  · obtain ⟨c', hc, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact goodS_remove (goodS_setChan hst (good_dropR (hst _) hc))
  · simp at h

theorem dstep_good_dw {st st' : DStore} {w : Nat} {r : Res} (hst : GoodS st)
    (h : dstep st (.streamDropW w) = some (st', r)) : GoodS st' := by
  simp only [dstep] at h
  split at h
  · obtain ⟨c', hc, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact goodS_remove (goodS_setChan hst (good_dropW (hst _) hc))
  · simp at h

theorem dstep_good_join {st st' : DStore} {h' s : Nat} {r : Res} (hst : GoodS st)
    (h : dstep st (.join h' s) = some (st', r)) : GoodS st' := by
  simp only [dstep] at h
  split at h <;> (try split_ifs at h) <;> simp at h
  all_goals (obtain ⟨rfl, -⟩ := h; exact hst)

/-- `Drop`'s built-ins keep every stream `Good`. -/
theorem dstep_good {st st' : DStore} {o : DOp} {r : Res} (hst : GoodS st)
    (h : dstep st o = some (st', r)) : GoodS st' := by
  cases o with
  | streamNew =>
    simp only [dstep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro t
    by_cases ht : t = st.next
    · subst ht; simp [upd, DChan.Good]
    · simpa [upd, ht] using hst t
  | streamWrite w xs => exact dstep_good_rw hst h
  | streamRead r' n => exact dstep_good_rd hst h
  | streamDropR r' => exact dstep_good_dr hst h
  | streamDropW w => exact dstep_good_dw hst h
  | wsNew =>
    simp only [dstep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hst
  | join h' s => exact dstep_good_join hst h

/-- Delivering an event keeps every stream `Good`. -/
theorem takeEv_good {st st' : DStore} {h : Nat} {e : Event} (hst : GoodS st)
    (he : takeEv st h = some (st', e)) : GoodS st' := by
  unfold takeEv at he
  split at he
  · obtain ⟨⟨c', p, ys⟩, hc, hq⟩ := Option.map_eq_some_iff.mp he
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, -⟩ := hq
    exact goodS_setChan hst (good_takeR (hst _) hc)
  · obtain ⟨⟨c', p⟩, hc, hq⟩ := Option.map_eq_some_iff.mp he
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, -⟩ := hq
    exact goodS_setChan hst (good_takeW (hst _) hc)
  · simp at he

theorem wait_good {st st' : DStore} {s h : Nat} {e : Event} (hst : GoodS st)
    (hw : DWait st s h st' e) : GoodS st' := takeEv_good hst hw.2.2

/-- **Every answer of `Drop` is an answer of this variant**: on a store of `Good` streams,
`cstep` answers every operation `dstep` answers, in the same way. -/
theorem dstep_cstep {st : DStore} {o : DOp} {p : DStore × Res} (hst : GoodS st)
    (h : dstep st o = some p) : cstep st (.op o) = some p := by
  cases o with
  | streamWrite w xs =>
    simp only [dstep] at h
    simp only [cstep]
    split at h
    · rename_i s hs
      obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp h
      simp [hs, zwrite_of_write (hst s) hq, he]
    · simp at h
  | streamRead r n =>
    simp only [dstep] at h
    simp only [cstep]
    split at h
    · rename_i s hs
      obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp h
      simp [hs, zread_of_read (hst s) hq, he]
    · simp at h
  | _ => exact h

/-- The operations of `Drop` that copy something. -/
def nonzero : DOp → Prop
  | .streamWrite _ xs => xs ≠ []
  | .streamRead _ n => 0 < n
  | _ => True

/-- **Nonzero operations are answered alike**: on a store of `Good` streams, `cstep` and `dstep`
agree on every operation that copies something (also when `dstep` traps). -/
theorem cstep_eq {st : DStore} {o : DOp} (hst : GoodS st) (ho : nonzero o) :
    cstep st (.op o) = dstep st o := by
  cases o with
  | streamWrite w xs =>
    simp only [cstep, dstep]
    cases ht : st.tbl w with
    | none => rfl
    | some ob => cases ob <;> simp [zwrite_eq (hst _) ho]
  | streamRead r n =>
    simp only [cstep, dstep]
    cases ht : st.tbl r with
    | none => rfl
    | some ob => cases ob <;> simp [zread_eq (hst _) ho]
  | _ => rfl

/-! ## Networks reach only `Good` stores -/

open Silmaril.Wasm.Component.Streams.Net (Node NSt NStep Network Sys Step Steps Reach initStore init)

theorem nstep_good {N : Node} {ws : Nat} {st st' : DStore} {x x' : NSt N.σ} (hst : GoodS st)
    (h : NStep N ws st x st' x') : GoodS st' := by
  cases h with
  | readBlk _ _ _ _ hd => exact dstep_good hst hd
  | readNow _ _ _ _ hd => exact dstep_good hst hd
  | write _ _ _ _ hd => exact dstep_good hst hd
  | waitIn _ hw => exact wait_good hst hw
  | waitOut _ _ hw => exact wait_good hst hw
  | dropIn _ _ hd => exact dstep_good hst hd
  | dropOut _ _ _ hd => exact dstep_good hst hd

theorem steps_good {net : Network} {s s' : Sys net} (hst : GoodS s.st) (h : Steps net s s') :
    GoodS s'.st := by
  induction h with
  | refl => exact hst
  | tail _ hs ih =>
    cases hs with
    | node i hn => exact nstep_good ih hn

/-- **Every store a network reaches is `Good`.** -/
theorem reach_good {net : Network} {s : Sys net} (h : Reach net s) : GoodS s.st :=
  steps_good (s := init net) (fun _ => ⟨by simp [initStore, init], by simp [initStore, init]⟩) h

/-! ## Item flow -/

/-- The reader's buffer is empty and closed unless a read is in progress. -/
def RI (c : DChan) : Prop := c.r.st ≠ .copying → c.rgot = [] ∧ c.rcap = none

/-- One step moves items from the writer to the reader: `new` is transferred, and the reader's
buffer before, followed by `new`, is what it is handed followed by its buffer after. -/
def Flow (c c' : DChan) (ys : List Val) : Prop :=
  ∃ new, c'.sent = c.sent ++ new ∧ c.rgot ++ new = ys ++ c'.rgot

theorem flow_zread_dropped {c c' : DChan} {n : Nat} {r : Res}
    (h1 : ¬(c.r.gone = true ∨ c.r.st ≠ .idle)) (h2 : c.w.gone = true)
    (h : c.zread n = some (c', r)) : Flow c c' (delivered r) ∧ RI c' := by
  unfold DChan.zread at h
  rw [ite_eq_right h1, ite_eq_left h2] at h
  cases he : c.r.ev <;> simp [he] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨⟨[], by simp, by simp [delivered]⟩, fun _ => by simp⟩

theorem flow_zread_copy {c c' : DChan} {n : Nat} {r : Res} {x : Val} {xs : List Val}
    (hI' : c.rgot = [] ∧ c.rcap = none) (hw : c.wbuf = some (x :: xs))
    (h1 : ¬(c.r.gone = true ∨ c.r.st ≠ .idle)) (h2 : ¬c.w.gone = true)
    (h : c.zread n = some (c', r)) : Flow c c' (delivered r) ∧ RI c' := by
  unfold DChan.zread at h
  rw [ite_eq_right h1, ite_eq_right h2] at h
  by_cases hn : n = 0
  · simp [hw, hn] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨[], by simp, by simp [delivered]⟩, fun _ => hI'⟩
  · simp [hw, hn] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨_, rfl, by simp [delivered, hI'.1]⟩, fun _ => hI'⟩

theorem flow_zread_open {c c' : DChan} {n : Nat} {r : Res} (hI' : c.rgot = [] ∧ c.rcap = none)
    (h1 : ¬(c.r.gone = true ∨ c.r.st ≠ .idle)) (h2 : ¬c.w.gone = true)
    (h : c.zread n = some (c', r)) : Flow c c' (delivered r) ∧ RI c' := by
  rcases hw : c.wbuf with _ | _ | ⟨x, xs⟩
  · unfold DChan.zread at h
    rw [ite_eq_right h1, ite_eq_right h2] at h
    simp [hw] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨[], by simp, by simp [delivered, hI'.1]⟩, fun h => absurd rfl h⟩
  · unfold DChan.zread at h
    rw [ite_eq_right h1, ite_eq_right h2] at h
    simp [hw] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨[], by simp, by simp [delivered, hI'.1]⟩, fun h => absurd rfl h⟩
  · exact flow_zread_copy hI' hw h1 h2 h

theorem flow_zread {c c' : DChan} {n : Nat} {r : Res} (hI : RI c) (h : c.zread n = some (c', r)) :
    Flow c c' (delivered r) ∧ RI c' := by
  by_cases h1 : c.r.gone = true ∨ c.r.st ≠ .idle
  · unfold DChan.zread at h; rw [ite_eq_left h1] at h; simp at h
  have hidle : c.r.st = .idle := by tauto
  have hI' : c.rgot = [] ∧ c.rcap = none := hI (by rw [hidle]; simp)
  by_cases h2 : c.w.gone = true
  · exact flow_zread_dropped h1 h2 h
  · exact flow_zread_open hI' h1 h2 h

theorem flow_zwrite_dropped {c c' : DChan} {xs : List Val} {r : Res} (hI : RI c)
    (h1 : ¬(c.w.gone = true ∨ c.w.st ≠ .idle)) (h2 : c.r.gone = true)
    (h : c.zwrite xs = some (c', r)) : Flow c c' [] ∧ RI c' := by
  unfold DChan.zwrite at h
  rw [ite_eq_right h1, ite_eq_left h2] at h
  cases he : c.w.ev <;> simp [he] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨⟨[], by simp, by simp⟩, hI⟩

theorem flow_zwrite_buf {c c' : DChan} {xs : List Val} {r : Res} {n : Nat} (hI : RI c)
    (hr : c.rcap = some n) (hcp : c.r.st = .copying)
    (h1 : ¬(c.w.gone = true ∨ c.w.st ≠ .idle)) (h2 : ¬c.r.gone = true)
    (h : c.zwrite xs = some (c', r)) : Flow c c' [] ∧ RI c' := by
  unfold DChan.zwrite at h
  rw [ite_eq_right h1, ite_eq_right h2] at h
  by_cases hx : xs = []
  · simp [hr, hx] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨⟨[], by simp, by simp⟩, hI⟩
  by_cases hn : n = 0
  · simp [hr, hx, hn] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨⟨[], by simp, by simp⟩, fun h => absurd hcp (by simpa using h)⟩
  · simp [hr, hx, hn] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨⟨_, rfl, by simp⟩, fun h => absurd hcp (by simpa using h)⟩

theorem flow_zwrite {c c' : DChan} {xs : List Val} {r : Res} (hI : RI c)
    (h : c.zwrite xs = some (c', r)) : Flow c c' [] ∧ RI c' := by
  by_cases h1 : c.w.gone = true ∨ c.w.st ≠ .idle
  · unfold DChan.zwrite at h; rw [ite_eq_left h1] at h; simp at h
  by_cases h2 : c.r.gone = true
  · exact flow_zwrite_dropped hI h1 h2 h
  rcases hr : c.rcap with _ | n
  · unfold DChan.zwrite at h
    rw [ite_eq_right h1, ite_eq_right h2] at h
    simp [hr] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨⟨[], by simp, by simp⟩, fun hc => ⟨(hI hc).1, rfl⟩⟩
  have hcp : c.r.st = .copying := by
    by_contra hc; have := (hI hc).2; rw [hr] at this; simp at this
  exact flow_zwrite_buf hI hr hcp h1 h2 h

theorem flow_cancelR {c c' : DChan} {r : Res} (h : c.cancelR = some (c', r)) :
    Flow c c' (delivered r) ∧ RI c' := by
  unfold DChan.cancelR at h
  by_cases h1 : c.r.gone = true ∨ c.r.st ≠ .copying
  · rw [ite_eq_left h1] at h; simp at h
  simp [h1] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨⟨[], by simp, by simp [delivered]⟩, fun _ => by simp⟩

theorem flow_cancelW {c c' : DChan} {r : Res} (hI : RI c) (h : c.cancelW = some (c', r)) :
    Flow c c' [] ∧ RI c' := by
  unfold DChan.cancelW at h
  by_cases h1 : c.w.gone = true ∨ c.w.st ≠ .copying
  · rw [ite_eq_left h1] at h; simp at h
  simp [h1] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨⟨[], by simp, by simp⟩, hI⟩

theorem flow_takeR {c c' : DChan} {p : Nat} {ys : List Val} (h : c.takeR = some (c', p, ys)) :
    Flow c c' ys ∧ RI c' := by
  unfold DChan.takeR at h
  cases he : c.r.ev <;> simp [he] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact ⟨⟨[], by simp, by simp⟩, fun _ => by simp⟩

theorem flow_takeW {c c' : DChan} {p : Nat} (hI : RI c) (h : c.takeW = some (c', p)) :
    Flow c c' [] ∧ RI c' := by
  unfold DChan.takeW at h
  cases he : c.w.ev <;> simp [he] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨⟨[], by simp, by simp⟩, hI⟩

theorem flow_dropR {c c' : DChan} (hI : RI c) (h : c.dropR = some c') : Flow c c' [] ∧ RI c' := by
  unfold DChan.dropR at h
  by_cases h1 : c.r.gone = true ∨ c.r.st = .copying
  · rw [ite_eq_left h1] at h; simp at h
  have hI' := hI (fun h => h1 (Or.inr h))
  rw [ite_eq_right h1] at h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨⟨[], by simp, by simp [hI'.1]⟩, fun _ => hI'⟩

theorem flow_dropW {c c' : DChan} (hI : RI c) (h : c.dropW = some c') : Flow c c' [] ∧ RI c' := by
  unfold DChan.dropW at h
  by_cases h1 : c.w.gone = true ∨ c.w.st = .copying
  · rw [ite_eq_left h1] at h; simp at h
  rw [ite_eq_right h1] at h
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨⟨[], by simp, by simp⟩, fun hc => ?_⟩
  by_cases h2 : c.r.gone = false ∧ c.r.st ≠ .done ∧ c.r.ev = none
  · rw [ite_eq_left h2] at hc; exact hI hc
  · rw [ite_eq_right h2] at hc; exact hI hc

theorem flow_step {c c' : DChan} {ys : List Val} (hI : RI c) (h : CStep c c' ys) :
    Flow c c' ys ∧ RI c' := by
  cases h with
  | read h => exact flow_zread hI h
  | write h => exact flow_zwrite hI h
  | cancelR h => exact flow_cancelR h
  | cancelW h => exact flow_cancelW hI h
  | takeR h => exact flow_takeR h
  | takeW h => exact flow_takeW hI h
  | dropR h => exact flow_dropR hI h
  | dropW h => exact flow_dropW hI h

/-- Along any sequence of operations: the items transferred since the start, after the reader's
buffer at the start, are the items handed to the reader followed by its buffer now. -/
theorem flow_steps {c c' : DChan} {ys : List Val} (hI : RI c) (h : CSteps c c' ys) :
    (∃ new, c'.sent = c.sent ++ new ∧ c.rgot ++ new = ys ++ c'.rgot) ∧ RI c' := by
  induction h with
  | refl => exact ⟨⟨[], by simp, by simp⟩, hI⟩
  | tail _ hs ih =>
    obtain ⟨⟨n1, h1, h2⟩, hI1⟩ := ih
    obtain ⟨⟨n2, h3, h4⟩, hI2⟩ := flow_step hI1 hs
    refine ⟨⟨n1 ++ n2, by rw [h3, h1, List.append_assoc], ?_⟩, hI2⟩
    rw [← List.append_assoc, h2, List.append_assoc, h4, List.append_assoc]

/-- **No item is lost or duplicated**, with cancellation and zero-length copies: from a new
stream, the items transferred are exactly those handed to the reader, then those still in its
buffer. -/
theorem csteps_sent {c : DChan} {ys : List Val} (h : CSteps {} c ys) : c.sent = ys ++ c.rgot := by
  obtain ⟨⟨new, h1, h2⟩, -⟩ := flow_steps (fun _ => ⟨rfl, rfl⟩) h
  simpa using h1.trans h2

/-! ## Futures -/

/-- The three phases of a future: nothing transferred; transferred into the reader's buffer,
not delivered; delivered. -/
def FI (c : FChan) (ys : List Val) : Prop :=
  (c.sent = none ∧ ys = [] ∧ c.rgot = none ∧ (c.r.ev = none ∨ (c.r.ev = some 0 ∧ c.w.gone = true)) ∧
      (c.w.ev = none ∨ (c.w.ev = some 0 ∧ c.r.gone = true)) ∧ (c.wval = none ∨ c.w.st = .copying) ∧
      (c.rbuf = false ∨ c.r.st = .copying)) ∨
  (c.sent ≠ none ∧ ys = [] ∧ c.rgot = c.sent ∧ c.r.st = .copying ∧ c.r.gone = false ∧
      c.r.ev = some 1 ∧ c.w.st = .done ∧ c.w.ev = none ∧ c.wval = none ∧ c.rbuf = false) ∨
  (c.sent ≠ none ∧ ys = c.sent.toList ∧ c.r.st = .done ∧ c.r.ev = none ∧ c.rgot = none ∧
      c.wval = none ∧
      ((c.w.st = .done ∧ c.w.ev = none) ∨ (c.w.st = .copying ∧ c.w.ev = some 1 ∧ c.w.gone = false)))

set_option hygiene false in
/-- Split the invariant into its atoms and let `simp_all` run the operation. -/
local macro "fi_tac" : tactic => `(tactic| (
  unfold FI at hI ⊢
  simp only [FChan.fread, FChan.fwrite, FChan.ftakeR, FChan.ftakeW, FChan.fcancelR,
    FChan.fcancelW, FChan.fdropR, FChan.fdropW] at h
  repeat' (first | split_ifs at h | split at h)
  all_goals (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals ((try casesm* _ ∧ _); try subst_vars)
  all_goals (rcases hI with ⟨hs, hy, hg, hre | ⟨hre, hwg⟩, hwe | ⟨hwe, hrg⟩, hwv | hwv, hrb | hrb⟩ |
    ⟨hs, hy, hg, hst, hgo, hre, hws, hwe, hwv, hrb⟩ |
    ⟨hs, hy, hst, hre, hg, hwv, ⟨hws, hwe⟩ | ⟨hws, hwe, hwg⟩⟩)
  all_goals (simp_all [delivered, fcode])))

theorem fi_read {c c' : FChan} {r : Res} {ys : List Val} (hI : FI c ys) (h : c.fread = some (c', r)) :
    FI c' (ys ++ delivered r) := by fi_tac

theorem fi_write {c c' : FChan} {v : Val} {r : Res} {ys : List Val} (hI : FI c ys)
    (h : c.fwrite v = some (c', r)) : FI c' ys := by fi_tac

theorem fi_takeR {c c' : FChan} {p : Nat} {zs ys : List Val} (hI : FI c ys)
    (h : c.ftakeR = some (c', p, zs)) : FI c' (ys ++ zs) := by fi_tac

theorem fi_takeW {c c' : FChan} {p : Nat} {ys : List Val} (hI : FI c ys)
    (h : c.ftakeW = some (c', p)) : FI c' ys := by fi_tac

theorem fi_cancelR {c c' : FChan} {p : Nat} {zs ys : List Val} (hI : FI c ys)
    (h : c.fcancelR = some (c', p, zs)) : FI c' (ys ++ zs) := by fi_tac

theorem fi_cancelW {c c' : FChan} {p : Nat} {ys : List Val} (hI : FI c ys)
    (h : c.fcancelW = some (c', p)) : FI c' ys := by fi_tac

theorem fi_dropR {c c' : FChan} {ys : List Val} (hI : FI c ys) (h : c.fdropR = some c') :
    FI c' ys := by fi_tac

theorem fi_dropW {c c' : FChan} {ys : List Val} (hI : FI c ys) (h : c.fdropW = some c') :
    FI c' ys := by fi_tac

theorem fi_step {c c' : FChan} {ys zs : List Val} (hI : FI c ys) (h : FStep c c' zs) :
    FI c' (ys ++ zs) := by
  cases h with
  | read h => exact fi_read hI h
  | write h => simpa using fi_write hI h
  | takeR h => exact fi_takeR hI h
  | takeW h => simpa using fi_takeW hI h
  | cancelR h => exact fi_cancelR hI h
  | cancelW h => simpa using fi_cancelW hI h
  | dropR h => simpa using fi_dropR hI h
  | dropW h => simpa using fi_dropW hI h

theorem fi_steps {c c' : FChan} {ys : List Val} (hI : FI c []) (h : FSteps c c' ys) : FI c' ys := by
  induction h with
  | refl => exact hI
  | tail _ hs ih => exact fi_step ih hs

/-- **A future delivers at most one value, the value written**: along any operations from a new
future, the reader is handed nothing, or exactly the one value transferred. -/
theorem fsteps_once {c : FChan} {ys : List Val} (h : FSteps {} c ys) :
    ys = [] ∨ ∃ v, ys = [v] ∧ c.sent = some v := by
  rcases fi_steps (Or.inl ⟨rfl, rfl, rfl, by simp, by simp, by simp, by simp⟩) h with
    ⟨-, hy, -⟩ | ⟨-, hy, -⟩ | ⟨hs, hy, -⟩
  · exact Or.inl hy
  · exact Or.inl hy
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hs
    exact Or.inr ⟨v, by rw [hy, hv]; rfl, hv⟩

end Silmaril.Proofs.Wasm.Component.Streams.Cancel
