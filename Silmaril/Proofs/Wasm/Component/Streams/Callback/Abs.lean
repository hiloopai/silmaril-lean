module

public import Silmaril.Proofs.Wasm.Component.Streams.Callback.Inv
public import Silmaril.Proofs.Wasm.Component.Streams.Live.Progress

/-!
# The refinement map on single steps of the module

How `CB.abs` changes on each step of the module, without the store: the steps that call no
built-in leave it unchanged (`abs_waitW`, `abs_flush`, `abs_wait`, `abs_stopEnd`), and the others
change it as the node program of `Net` does (`abs_dropR`, `abs_write_blocked`, `abs_onwrite`,
`abs_read_blocked`, `abs_onread`, …).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Callback

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event blocked)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Callback

variable {σ : Type} {T : Tr σ Val Val}

theorem abs_stopReading (c : CB σ) : c.stopReading.abs T = c.abs T := rfl

theorem absOut_pc {c : CB σ} {p : PC} (hc : c.pc ≠ .exit) (hp : p ≠ .exit) :
    ({ c with pc := p } : CB σ).absOut T = c.absOut T := by
  simp [CB.absOut, CB.fl, hc, hp]

theorem abs_pc {c : CB σ} {p : PC} (hc : c.pc ≠ .exit) (hp : p ≠ .exit) :
    ({ c with pc := p } : CB σ).abs T = c.abs T := by
  simp only [CB.abs, absOut_pc hc hp]

/-- Resetting an empty or dead output buffer. -/
theorem absOut_reset {c : CB σ} (h : c.dead = true ∨ c.out = []) (hw : c.wpend = false) :
    ({ c with out := [] } : CB σ).absOut T = c.absOut T := by
  rcases h with h | h
  · simp [CB.absOut, h]
  · simp [CB.absOut, CB.fl, h, hw]

theorem abs_wait {c : CB σ} (h : c.dead = true ∨ c.out = []) (hw : c.wpend = false)
    (hc : c.pc = .run) : ({ c with pc := .wait, out := [] } : CB σ).abs T = c.abs T := by
  have e : ({ c with pc := .wait, out := [] } : CB σ) =
      { ({ c with out := [] } : CB σ) with pc := .wait } := rfl
  rw [e, abs_pc (by simp [hc]) (by simp)]
  simp only [CB.abs, absOut_reset h hw]

theorem abs_flush {c : CB σ} (hout : c.out = []) (hr : c.rdropped = true)
    (hf : c.flushed = false) (hd : c.dead = false) (hw : c.wpend = false) :
    ({ c with flushed := true, out := T.flush c.s } : CB σ).abs T = c.abs T := by
  simp [CB.abs, CB.absOut, CB.fl, hout, hr, hf, hd, hw]

/-! ## Dropping the readable end -/

theorem absOut_push_flush {c : CB σ} (hr : c.rdropped = false) (hf : c.flushed = false)
    (hpc : c.pc ≠ .exit) :
    ({ c with pdrop := false, rdropped := true } : CB σ).absOut T =
      (c.absOut T).push (T.flush c.s) := by
  by_cases hd : c.dead = true
  · simp [CB.absOut, hd, hpc, Out.push]
  · by_cases hw : c.wpend = true
    · simp [CB.absOut, CB.fl, hd, hw, hpc, hr, hf, Out.push]
    · simp [CB.absOut, CB.fl, hd, hw, hpc, hr, hf, Out.push]

theorem abs_dropR {c : CB σ} (h : c.Inv T) (hpd : c.pdrop = true) :
    ({ c with pdrop := false, rdropped := true } : CB σ).abs T = (c.abs T).stop T := by
  obtain ⟨hr, hrp, -⟩ := h.i4 hpd
  have hf : c.flushed = false := by
    cases hf : c.flushed
    · rfl
    · rw [h.i6 hf] at hr; cases hr
  have hpc : c.pc ≠ .exit := fun hx => by rw [(h.i9 hx).1] at hr; cases hr
  have ho := absOut_push_flush (T := T) hr hf hpc
  have e : ({ c with pdrop := false, rdropped := true } : CB σ).abs T =
      ⟨c.s, c.got, .gone c.ended, [({ c with pdrop := false, rdropped := true } : CB σ).absOut T]⟩ :=
    rfl
  rw [e, ho]
  cases he : c.ended <;> simp [CB.abs, NSt.stop, hr, hrp, he]

/-- The node may drop its input when the module asked for the drop. -/
theorem abs_mayStop {c : CB σ} (h : c.Inv T) (hpd : c.pdrop = true) : (c.abs T).mayStop T := by
  obtain ⟨hr, hrp, hwhy⟩ := h.i4 hpd
  have hpc : c.pc ≠ .exit := fun hx => by rw [(h.i9 hx).1] at hr; cases hr
  by_cases he : c.ended = true
  · left; simp [CB.abs, hr, hrp, he]
  · right
    refine ⟨by simp [CB.abs, hr, hrp, he], ?_⟩
    rcases hwhy with h1 | h1 | h1
    · exact absurd h1 he
    · exact Or.inl h1
    · refine Or.inr ⟨by simp [CB.abs], fun o ho => ?_⟩
      simp only [CB.abs, List.mem_singleton] at ho
      subst ho
      left
      simp [CB.absOut, hpc, h1]

/-! ## Outputs -/

theorem abs_outs (c : CB σ) : (c.abs T).outs = [c.absOut T] := rfl

theorem set_abs (c : CB σ) (o : Out) : (c.abs T).outs.set 0 o = [o] := rfl

/-- Writing `n` items of the pending output, then the flush still to come. -/
theorem take_out_fl (c : CB σ) {n : Nat} (hn : n ≤ c.out.length) :
    (c.out ++ c.fl T).take n = c.out.take n ∧
      (c.out ++ c.fl T).drop n = c.out.drop n ++ c.fl T := by
  exact ⟨List.take_append_of_le_length hn, List.drop_append_of_le_length hn⟩

/-- The items left and acknowledged after a copy of `k ≤ n` of the `n` items offered. -/
theorem drop_take_append {l f : List Val} {k n : Nat} (hk : k ≤ n) (hn : n ≤ l.length) :
    (l.take n).drop k ++ (l.drop n ++ f) = l.drop k ++ f ∧ (l.take n).take k = l.take k := by
  have hl : k ≤ (l.take n).length := by simp; omega
  refine ⟨?_, by rw [List.take_take, Nat.min_eq_left hk]⟩
  rw [← List.append_assoc, ← List.drop_append_of_le_length hl, List.take_append_drop]

/-- **`$onwrite`** on an output whose `n` first items were offered. -/
theorem absOut_onwrite {c : CB σ} {n : Nat} (r : Nat) (hpc : c.pc ≠ .exit)
    (hd : c.dead = false) (hw : c.wpend = false) (hk : count r ≤ n) (hn : n ≤ c.out.length) :
    (c.onwrite r).absOut T =
      Out.onWrite ⟨.busy (c.out.take n) (c.out.drop n ++ c.fl T), c.ack⟩ r := by
  obtain ⟨h1, h2⟩ := drop_take_append (f := c.fl T) hk hn
  rw [onwrite_eq]
  by_cases hs : status r = 0
  · have hfl : ({ c with out := c.out.drop (count r), ack := c.ack ++ c.out.take (count r) } :
        CB σ).fl T = c.fl T := rfl
    simp only [hs, ↓reduceIte, CB.absOut, hpc, hd, hw, Bool.false_eq_true, Out.onWrite, h2]
    simp only [CB.fl, hd, OS.idle.injEq, Out.mk.injEq, and_true]
    exact (drop_take_append hk hn).1.symm
  · simp [CB.absOut, hs, hpc, Out.onWrite, h2]

/-- `$onwrite` changes only the output. -/
theorem abs_onwrite_eq (d : CB σ) (p : Nat) :
    (d.onwrite p).abs T = { d.abs T with outs := [(d.onwrite p).absOut T] } := by
  rw [onwrite_eq]
  split <;> rfl

/-- A write that blocks. -/
theorem abs_write_blocked {c : CB σ} {n : Nat} (hd : c.dead = false) (hn : n ≤ c.out.length) :
    ({ c with pc := .wait, wpend := true, wl := n } : CB σ).abs T =
      { c.abs T with
        outs := [Out.afterWrite ((c.out ++ c.fl T).take n) ((c.out ++ c.fl T).drop n) c.ack
          blocked] } := by
  obtain ⟨h1, h2⟩ := take_out_fl (T := T) c hn
  rw [h1, h2]
  simp [CB.abs, CB.absOut, CB.fl, Out.afterWrite, hd]

/-- A write that completes or reports `DROPPED` at once. -/
theorem abs_write_now {c : CB σ} {n r : Nat} (hpc : c.pc = .run) (hd : c.dead = false)
    (hw : c.wpend = false) (hn : n ≤ c.out.length) (hr : r ≠ blocked) (hk : count r ≤ n) :
    (c.onwrite r).abs T =
      { c.abs T with
        outs := [Out.afterWrite ((c.out ++ c.fl T).take n) ((c.out ++ c.fl T).drop n) c.ack r] } := by
  obtain ⟨h1, h2⟩ := take_out_fl (T := T) c hn
  rw [h1, h2]
  have ho := absOut_onwrite (T := T) r (by simp [hpc]) hd hw hk hn
  simp only [Out.afterWrite, hr, ↓reduceIte, ← ho]
  exact abs_onwrite_eq c r

/-- A write event on an output with a write pending. -/
theorem abs_evOut_busy {c : CB σ} {p : Nat} (hpc : c.pc = .wait) (hw : c.wpend = true)
    (hd : c.dead = false) (hk : count p ≤ c.wl) (hn : c.wl ≤ c.out.length) :
    ((({ c with pc := .run, wpend := false } : CB σ).onwrite p)).abs T =
      { c.abs T with outs := [(c.absOut T).onWrite p] } := by
  have ho := absOut_onwrite (T := T) (c := { c with pc := .run, wpend := false }) p (by simp) hd rfl
    hk hn
  have hc : c.absOut T = ⟨.busy (c.out.take c.wl) (c.out.drop c.wl ++ c.fl T), c.ack⟩ := by
    simp [CB.absOut, hpc, hd, hw]
  have hfl : ({ c with pc := .run, wpend := false } : CB σ).fl T = c.fl T := rfl
  rw [abs_onwrite_eq, ho, hc, hfl]
  rfl

/-- A write event on an idle output: the reader has gone. -/
theorem abs_evOut_idle {c : CB σ} {p : Nat} (hpc : c.pc = .wait) (hw : c.wpend = false)
    (hs : status p ≠ 0) :
    ({ c with pc := .run, dead := true } : CB σ).stopReading.abs T =
      { c.abs T with outs := [(c.absOut T).onWrite p] } := by
  rw [abs_stopReading]
  by_cases hd : c.dead = true
  · simp [CB.abs, CB.absOut, hpc, hd, Out.onWrite]
  · simp [CB.abs, CB.absOut, hpc, hd, hw, Out.onWrite, hs]

/-- Dropping the writable end. -/
theorem abs_dropW {c : CB σ} :
    ({ c with pc := .exit, out := [] } : CB σ).abs T =
      { c.abs T with outs := [⟨.closed c.dead, c.ack⟩] } := by
  simp [CB.abs, CB.absOut]

/-! ## Inputs -/

theorem abs_read_blocked {c : CB σ} (hpc : c.pc = .run) (h0 : c.dead = true ∨ c.out = [])
    (hw : c.wpend = false) (hr : c.rdropped = false) :
    ({ c with pc := .wait, rpend := true, out := [] } : CB σ).abs T =
      { c.abs T with rd := .busy } := by
  rcases h0 with hd | hout
  · simp [CB.abs, CB.absOut, hd, hr, hpc]
  · simp [CB.abs, CB.absOut, CB.fl, hout, hr, hw, hpc]

theorem push_nil (o : Out) : o.push [] = o := by
  obtain ⟨st, a⟩ := o
  cases st <;> simp [Out.push]

/-- **`$onread`** from a state that has not stopped reading. -/
theorem abs_onread {c : CB σ} (p : Nat) (ys : List Val) (hpc : c.pc ≠ .exit)
    (hr : c.rdropped = false) (hrp : c.rpend = false) (he : c.ended = false)
    (hwl : c.wpend = true → c.wl ≤ c.out.length) :
    (c.onread T p ys).abs T = (c.abs T).onRead T p ys := by
  have F := onread_fields T c p ys
  have hfl : (c.onread T p ys).fl T = [] := by simp [CB.fl, F.rdropped, hr]
  have hfl0 : c.fl T = [] := by simp [CB.fl, hr]
  have hrd : ((c.onread T p ys).abs T).rd = if status p = 0 then .idle else .ended := by
    by_cases hs : status p = 0 <;> simp [CB.abs, F.rdropped, F.rpend, F.ended, hr, hrp, he, hs]
  have ho : (c.onread T p ys).absOut T = (c.absOut T).push (T.feed c.s ys).2 := by
    by_cases hd : c.dead = true
    · simp [CB.absOut, F.pc, F.dead, F.ack, hpc, hd, Out.push]
    · by_cases hw : c.wpend = true
      · have hl := hwl hw
        simp [CB.absOut, F.pc, F.dead, F.ack, F.wpend, F.wl, F.out, hpc, hd, hw, hfl, hfl0,
          Out.push, List.take_append_of_le_length hl, List.drop_append_of_le_length hl]
      · simp [CB.absOut, F.pc, F.dead, F.ack, F.wpend, F.out, hpc, hd, hw, hfl, hfl0, Out.push]
  show NSt.mk _ _ _ _ = NSt.mk _ _ _ _
  rw [NSt.mk.injEq]
  exact ⟨F.s, F.got, hrd, by rw [abs_outs, ho]; rfl⟩

/-- A read event on an idle input: the writer has gone. -/
theorem abs_evIn_idle {c : CB σ} {p : Nat} (hpc : c.pc = .wait) (hr : c.rdropped = false)
    (hrp : c.rpend = false) (hs : status p ≠ 0) :
    ({ c with pc := .run, ended := true } : CB σ).stopReading.abs T =
      (c.abs T).onRead T p [] := by
  rw [abs_stopReading]
  simp [CB.abs, NSt.onRead, hr, hrp, hs, Tr.feed, push_nil, CB.absOut, CB.fl, hpc]

end Silmaril.Proofs.Wasm.Component.Streams.Callback
