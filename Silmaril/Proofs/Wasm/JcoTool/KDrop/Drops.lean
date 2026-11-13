module

public import Silmaril.Proofs.Wasm.JcoTool.KDrop.Pieces

/-!
# The runtime's steps, and the cases of the callback that drop an end

* `ready_inv`, `event_inv`: what a step of `DRStep` tells about the callback's run.
* `sim_cl` (`CL`: drop the output, exit), `sim_dead` (`DEAD`: drop the input, then close),
  `sim_eoi` (`EOI`: drop the input, flush), `rd_done` (`RD` when the kernel is done): each is
  one `dropIn` or `dropOut` step of the `Net` node.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KDrop

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Wasm.Component.Async (Res Event EventCode blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (NSt OS RV Node NStep rh wh status count)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

/-- The invocation state of the callback with parameters `ps`. -/
def inv0 (ms : MS) (ps : List Nat) (st : DStore) : DSt := ⟨ms.g, ms.m, locals ps, st, ms.rp⟩

/-- A machine state is determined by its parts. -/
theorem ms_eq {ms' : MS} {s' : DSt} {md : Mode} (hmd : ms'.mode = md) (hg : ms'.g = s'.g)
    (hm : ms'.m = s'.m) (hrp : ms'.rp = s'.rp) : ms' = ⟨s'.g, s'.m, s'.rp, md⟩ := by
  cases ms'
  simp_all

/-- **A step after `YIELD`**: the case of `pc` ran with no event and returned a code. -/
theorem ready_inv {k : KM} {N : Nat} {st st' : DStore} {ms ms' : MS} (hm : ms.mode = .ready)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ code s', dexec (callbackD k N) FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') ∧
      modeOf code = some ms'.mode ∧ st' = s'.st ∧ ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩ := by
  cases h with
  | ready _ hi =>
    obtain ⟨code, s', hx, hmd, hst, hg, hmm, hrp⟩ := dinvoke_inv hi
    exact ⟨code, s', hx, hmd, hst, ms_eq rfl hg hmm hrp⟩
  | event hw _ _ _ => rw [hm] at hw; cases hw

/-- **A step after `WAIT`**: an event of the set was taken and the case of `pc` ran with it. -/
theorem event_inv {k : KM} {N s : Nat} {st st' : DStore} {ms ms' : MS} (hm : ms.mode = .waiting s)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ hd st₁ e, DWait st s hd st₁ e ∧ wfD e = true ∧ ∃ code s',
      dexec (callbackD k N) FUEL (inv0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
        some (.ret code, s') ∧ modeOf code = some ms'.mode ∧ st' = s'.st ∧
      ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩ := by
  cases h with
  | ready hr _ => rw [hm] at hr; cases hr
  | event hw hd hwf hi =>
    rw [hm] at hw
    cases hw
    obtain ⟨code, s', hx, hmd, hst, hg, hmm, hrp⟩ := dinvoke_inv hi
    exact ⟨_, _, _, hd, hwf, code, s', hx, hmd, hst, ms_eq rfl hg hmm hrp⟩

/-! ## Codes -/

theorem modeOf_yield : modeOf 1 = some .ready := rfl

theorem modeOf_exit : modeOf 0 = some .exited := rfl

theorem waitCode_evalD (t : St) {s : Nat} (hws : t.g WS = s) (hs : s < 2 ^ 28) :
    waitCode.eval t = 2 + 16 * s := by
  simp only [waitCode, E.eval, Bin.eval, hws]
  norm_num [M32]
  omega

theorem modeOf_wait (s : Nat) : modeOf (2 + 16 * s) = some (.waiting s) := by
  have h1 : (2 + 16 * s) % 16 = 2 := by omega
  have h2 : (2 + 16 * s) / 16 = s := by omega
  have h4 : ¬ 2 + 16 * s = 1 := by omega
  simp [modeOf, h1, h2, h4]

/-- The event's index is the handle it was taken from. -/
theorem dwait_index {st st' : DStore} {s h : Nat} {e : Event} (hw : DWait st s h st' e) :
    e.index = h := by
  obtain ⟨-, -, ht⟩ := hw
  unfold takeEv at ht
  split at ht
  · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp ht
    rw [← (Prod.mk.inj hp).2]
  · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp ht
    rw [← (Prod.mk.inj hp).2]
  · cases ht

/-! ## The relation, case by case -/

theorem relD_of {r w s : Nat} {ms : MS} {x : NSt KSt} (hm : ms.mode ≠ .exited)
    (hok : okD ms r w s) (hL : RelL r s ms x) : RelD r w s ms x := by
  unfold RelD
  rw [ite_eq_right hm]
  exact ⟨hok, hL⟩

theorem relD_exit {r w s : Nat} {ms : MS} {x : NSt KSt} (hm : ms.mode = .exited) {b d : Bool}
    (hrd : x.rd = .gone b) (ho : outIs x (.closed d)) : RelD r w s ms x := by
  unfold RelD
  rw [ite_eq_left hm]
  exact ⟨b, hrd, d, ho⟩

/-- The case of the callback for `pc = p`. -/
def caseOf (k : KM) (N p : Nat) : S :=
  if p = pWTR then dWTR k else if p = pWTW then dWTW else if p = pRD then dRD k N
  else if p = pEOI then dEOI k else if p = pWR then dWR else if p = pCL then dCL
  else if p = pDEAD then dDEAD else dWTRD

/-- **Dispatch**, by `caseOf`. -/
theorem cb_at {k : KM} {N f : Nat} {s s' : DSt} {v : Nat}
    (h : dexec (callbackD k N) f s = some (.ret v, s')) :
    dexec (caseOf k N (s.g PC)) f s = some (.ret v, s') := by
  rcases cb_case h with ⟨hp, h⟩ | ⟨hp, h⟩ | ⟨hp, h⟩ | ⟨hp, h⟩ | ⟨hp, h⟩ | ⟨hp, h⟩ | ⟨hp, h⟩ | ⟨hp, h⟩ <;>
    · rw [hp]
      simpa [caseOf, pWTR, pWTW, pRD, pEOI, pWR, pCL, pDEAD, pWTRD] using h

/-- The handles and bounds of a machine with new globals that keep them. -/
theorem okD_of {ms ms' : MS} {r w s : Nat} (h : okD ms r w s)
    (hg : ∀ j, j ≠ GST → j ≠ BLEN → j ≠ OLEN → j ≠ OOFF → j ≠ PC → j ≠ NXT → ms'.g j = ms.g j)
    (hb : ms'.g BLEN ≤ CAP) (ho : ms'.g OLEN ≤ CAP) (hoff : ms'.g OOFF ≤ ms'.g OLEN) :
    okD ms' r w s := by
  obtain ⟨h₁, h₂, h₃, -⟩ := h
  refine ⟨?_, ?_, ?_, hb, ho, hoff⟩
  · rw [hg INSR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁]
  · rw [hg OUTSW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₂]
  · rw [hg WS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₃]

/-! ## `CL` -/

theorem dCL_exec {st : DStore} {ms : MS} {ps : List Nat} {w code : Nat} {s' : DSt}
    (hw : ms.g OUTSW = w) (h : dexec dCL FUEL (inv0 ms ps st) = some (.ret code, s')) :
    ∃ st₁ res, dstep st (.streamDropW w) = some (st₁, res) ∧ code = 0 ∧ s'.st = st₁ := by
  rcases hd : dstep st (.streamDropW w) with _ | ⟨st₁, res⟩
  · simp [dCL, seqs, dexec, dcallBI, E.eval, inv0, DSt.down, hw, hd] at h
  · simp [dCL, seqs, dexec, dcallBI, E.eval, inv0, DSt.down, hw, hd] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨st₁, res, rfl, rfl, rfl⟩

theorem outs_get {x : NSt KSt} {o : OS} (h : outIs x o) : ∃ a, x.outs[0]? = some ⟨o, a⟩ ∧ x.outs = [⟨o, a⟩] := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by simp [ha], ha⟩

/-- **`CL`**: one `dropOut` step; the machine exits. -/
theorem sim_cl {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pCL)
    (hrd : ∃ b, x.rd = .gone b) (hout : outIs x (.idle []) ∨ outIs x .dead)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ NStep (node k c c') s st x st' x' := by
  obtain ⟨code, s', hx, hmd, hst, hms⟩ := ready_inv hm h
  have hc : dexec dCL FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pCL, pWTR, pWTW, pRD, pEOI, pWR, inv0] using cb_at hx
  obtain ⟨st₁, res, hd, rfl, hs₁⟩ := dCL_exec hok.2.1 hc
  have hex : ms'.mode = .exited := by simpa [modeOf_exit] using hmd.symm
  obtain ⟨a, d, ha, hd'⟩ : ∃ a d, (x.outs[0]? = some ⟨.idle [], a⟩ ∧ d = false ∨
      x.outs[0]? = some ⟨.dead, a⟩ ∧ d = true) ∧ x.outs.length = 1 := by
    rcases hout with ho | ho
    · obtain ⟨a, h1, h2⟩ := outs_get ho
      exact ⟨a, false, .inl ⟨h1, rfl⟩, by simp [h2]⟩
    · obtain ⟨a, h1, h2⟩ := outs_get ho
      exact ⟨a, true, .inr ⟨h1, rfl⟩, by simp [h2]⟩
  refine ⟨{ x with outs := x.outs.set 0 ⟨.closed d, a⟩ }, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hrd
    refine relD_exit (d := d) hex hb ⟨a, ?_⟩
    rcases hout with ⟨a', ho⟩ | ⟨a', ho⟩ <;> simp [ho]
  · rw [hst, hs₁]
    exact NStep.dropOut (j := 0) rfl hrd ha hd

/-! ## Building the relation -/

/-- **`WR` after a write-out**: the output `out` pending from offset `0`, `NXT = nx`. -/
theorem relD_wr {r w s nx : Nat} {ms' : MS} {x' : NSt KSt} {ks : KSt} {out : List Nat}
    (hm : ms'.mode = .ready) (hpc : ms'.g PC = pWR) (hnx : ms'.g NXT = nx) (hoff : ms'.g OOFF = 0)
    (hrep : KRep ms'.g ms'.m ks out) (hh : ms'.g INSR = r ∧ ms'.g OUTSW = w ∧ ms'.g WS = s)
    (hx : outIs x' (.idle (out.map u8v)))
    (hn : (nx = 1 ∧ x'.rd = .idle ∧ ks = x'.s) ∨ (nx = 2 ∧ x'.rd = .ended ∧ ks = x'.s) ∨
      (nx = 0 ∧ ∃ b, x'.rd = .gone b)) : RelD r w s ms' x' := by
  have hpend : ms'.pending = out.map u8v := by
    have := pending_eq hrep hoff ms'.rp ms'.mode
    cases ms'; exact this
  have hkst : ms'.kst = ks := by
    have := kst_eq hrep ms'.rp ms'.mode
    cases ms'; exact this
  have hok : okD ms' r w s := ⟨hh.1, hh.2.1, hh.2.2, by rw [hrep.blen]; exact hrep.bcap,
    by rw [hrep.olen]; exact hrep.ocap, by rw [hoff]; exact Nat.zero_le _⟩
  have hnr : NxtRel ms' x' := by
    rcases hn with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩
    · exact .inl ⟨hnx, h1, hkst.trans h2⟩
    · exact .inr (.inl ⟨hnx, h1, hkst.trans h2⟩)
    · exact .inr (.inr ⟨hnx, h1⟩)
  refine relD_of (by rw [hm]; decide) hok (.inr (.inr (.inr (.inr (.inl ⟨hm, hpc, ?_, hnr⟩)))))
  rw [hpend]
  exact hx

/-! ## Dropping the input -/

theorem dropR_seq {rest : S} {f r : Nat} {s s' : DSt} {o : Out} (hr : s.g INSR = r)
    (h : dexec (.seq (.call .dropR [.g INSR] []) rest) f s = some (o, s')) :
    ∃ st₁ res, dstep s.st (.streamDropR r) = some (st₁, res) ∧ dexec rest f { s with st := st₁ } = some (o, s') := by
  rcases hd : dstep s.st (.streamDropR r) with _ | ⟨st₁, res⟩
  · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd] at h
  · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd] at h
    exact ⟨st₁, res, rfl, h⟩

/-- `dropR`, the flush and `YIELD` (`EOI`, and `RD` when the kernel is done). -/
theorem dropFlush_exec {k : KM} {f r code : Nat} {s s' : DSt} {ks : KSt} (hr : s.g INSR = r)
    (hK : KS s.g s.m ks) (h : dexec (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) f s = some (.ret code, s')) :
    ∃ st₁ res, dstep s.st (.streamDropR r) = some (st₁, res) ∧ code = 1 ∧ s'.st = st₁ ∧
      WrPost s.down s'.down (k.flush.exec 0 ks).1 (k.flush.exec 0 ks).2 0 := by
  obtain ⟨st₁, res, hd, h₁⟩ := dropR_seq hr (by simpa [seqs] using h)
  rcases hf : dexec (flushOut k) f { s with st := st₁ } with _ | ⟨o, s₂⟩
  · rw [dexec_seq_none hf] at h₁; cases h₁
  · obtain ⟨rfl, hst, hW⟩ := flushD_sound (s := { s with st := st₁ }) hK hf
    rw [dexec_seq_norm hf] at h₁
    simp only [yield_, dexec, Option.some.injEq, Prod.mk.injEq] at h₁
    obtain ⟨h1, rfl⟩ := h₁
    refine ⟨st₁, res, hd, by simpa [E.eval, M32] using h1.symm, hst, ?_⟩
    exact ⟨hW.pc, hW.nxt, hW.off, hW.rep, hW.hs, rfl, hW.rp⟩

theorem upd_pc_ne {g : Nat → Nat} {v j : Nat} (h : j ≠ PC) : upd g PC v j = g j := by
  simp [upd_apply, h]

/-- The kernel state held by a machine, in its globals and memory. -/
theorem ks_ofD {ms : MS} {ks : KSt} (hb : ms.g BLEN ≤ CAP) (hk : ms.kst = ks) : KS ms.g ms.m ks := by
  subst hk
  have hl : (slice ms.m KBUF (ms.g BLEN)).length = ms.g BLEN := slice_length _ _ _
  refine ⟨rfl, hl.symm, ?_, ?_⟩
  · show slice ms.m KBUF (slice ms.m KBUF (ms.g BLEN)).length = slice ms.m KBUF (ms.g BLEN)
    rw [hl]
  · show (slice ms.m KBUF (ms.g BLEN)).length ≤ CAP
    rw [hl]; exact hb

/-- The node after dropping its input, with output `[idle []]`. -/
theorem stop_idle {k : KM} {c c' : Nat} {x : NSt KSt} {a : List Val} (ha : x.outs = [⟨.idle [], a⟩]) :
    (x.stop (node k c c').T).outs = [⟨.idle ((trV k).flush x.s), a⟩] := by
  simp [NSt.stop, ha, Silmaril.Wasm.Component.Streams.Net.Out.push, node]

/-- **Drop the input and flush** from a machine holding the node's kernel state, with an idle,
empty output: one `dropIn` step, to `WR` with `NXT = 0`. -/
theorem sim_dropFlush {k : KM} {c c' s code : Nat} {st : DStore} {ms ms' : MS} {x : NSt KSt}
    {s₀ s' : DSt} (hok : okD ms (rh c) (wh c') s) (hkst : ms.kst = x.s)
    (hout : outIs x (.idle [])) (hms : x.mayStop (node k c c').T)
    (h0 : s₀.g = ms.g ∧ s₀.m = ms.m ∧ s₀.st = st)
    (hc : dexec (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) FUEL s₀ = some (.ret code, s'))
    (hmd : modeOf code = some ms'.mode) (hms' : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩) :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ NStep (node k c c') s st x s'.st x' := by
  obtain ⟨hg0, hm0, hs0⟩ := h0
  have hK : KS s₀.g s₀.m x.s := by rw [hg0, hm0]; exact ks_ofD hok.2.2.2.1 hkst
  have hr0 : s₀.g INSR = rh c := by rw [hg0]; exact hok.1
  obtain ⟨st₁, res, hd, rfl, hst, hW⟩ := dropFlush_exec (s := s₀) hr0 hK hc
  rw [hs0] at hd
  have hm : ms'.mode = .ready := by simpa [modeOf_yield] using hmd.symm
  obtain ⟨a, ha⟩ := hout
  refine ⟨x.stop (node k c c').T, ?_, ?_⟩
  · rw [hms']
    refine relD_wr (nx := 0) hm hW.pc hW.nxt hW.off hW.rep ⟨?_, ?_, ?_⟩ ⟨a, stop_idle ha⟩
      (.inr (.inr ⟨rfl, _, rfl⟩))
    · exact hW.hs.1.trans (by rw [DSt.down, hg0]; exact hok.1)
    · exact hW.hs.2.1.trans (by rw [DSt.down, hg0]; exact hok.2.1)
    · exact hW.hs.2.2.trans (by rw [DSt.down, hg0]; exact hok.2.2.1)
  · rw [hst]
    exact NStep.dropIn rfl hms hd

/-- **`EOI`**: drop the input, flush. -/
theorem sim_eoi {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pEOI)
    (hkst : ms.kst = x.s) (hrd : x.rd = .ended) (hout : outIs x (.idle []))
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ NStep (node k c c') s st x st' x' := by
  obtain ⟨code, s', hx, hmd, hst, hms⟩ := ready_inv hm h
  have hc : dexec (dEOI k) FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pEOI, pWTR, pWTW, pRD, inv0] using cb_at hx
  rw [hst]
  exact sim_dropFlush hok hkst hout (.inl hrd) ⟨rfl, rfl, rfl⟩ hc hmd hms

theorem dDEAD_exec {st : DStore} {ms : MS} {ps : List Nat} {r code : Nat} {s' : DSt}
    (hr : ms.g INSR = r) (h : dexec dDEAD FUEL (inv0 ms ps st) = some (.ret code, s')) :
    ∃ st₁ res, dstep st (.streamDropR r) = some (st₁, res) ∧ code = 1 ∧ s'.st = st₁ ∧
      s'.g = upd ms.g PC pCL ∧ s'.m = ms.m ∧ s'.rp = ms.rp := by
  obtain ⟨st₁, res, hd, h₁⟩ := dropR_seq (s := inv0 ms ps st) hr (by simpa [dDEAD, seqs] using h)
  simp only [yield_, dexec, Option.some.injEq, Prod.mk.injEq] at h₁
  obtain ⟨h1, rfl⟩ := h₁
  exact ⟨st₁, res, hd, by simpa [E.eval, M32] using h1.symm, rfl, by simp [E.eval, inv0, pCL, M32], rfl, rfl⟩

/-- **`DEAD`**: drop the input of a node whose output is dead; then `CL`. -/
theorem sim_dead {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pDEAD)
    (hrd : x.rd = .idle ∨ x.rd = .ended) (hout : outIs x .dead)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ NStep (node k c c') s st x st' x' := by
  obtain ⟨code, s', hx, hmd, hst, hms⟩ := ready_inv hm h
  have hc : dexec dDEAD FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pEOI, pWTR, pWTW, pRD, pWR, pCL, pDEAD, inv0] using cb_at hx
  obtain ⟨st₁, res, hd, rfl, hs₁, hg, -, -⟩ := dDEAD_exec hok.1 hc
  have hm' : ms'.mode = .ready := by simpa [modeOf_yield] using hmd.symm
  obtain ⟨a, ha⟩ := hout
  have hstop : x.mayStop (node k c c').T := by
    rcases hrd with h1 | h1
    · exact .inr ⟨h1, .inr ⟨by simp [ha], by simp [ha, Silmaril.Wasm.Component.Streams.Net.Out.isDead]⟩⟩
    · exact .inl h1
  refine ⟨x.stop (node k c c').T, ?_, by rw [hst, hs₁]; exact NStep.dropIn rfl hstop hd⟩
  have hok' : okD ms' (rh c) (wh c') s := by
    rw [hms]
    refine okD_of hok (fun j _ _ _ _ h5 _ => by simp [hg, upd_pc_ne h5]) ?_ ?_ ?_
    · show s'.g BLEN ≤ CAP
      rw [hg, upd_pc_ne (by decide)]; exact hok.2.2.2.1
    · show s'.g OLEN ≤ CAP
      rw [hg, upd_pc_ne (by decide)]; exact hok.2.2.2.2.1
    · show s'.g OOFF ≤ s'.g OLEN
      rw [hg, upd_pc_ne (by decide), upd_pc_ne (by decide)]; exact hok.2.2.2.2.2
  refine relD_of (by rw [hm']; decide) hok'
    (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hm', ?_, ⟨_, rfl⟩, .inr ⟨a, ?_⟩⟩)))))))
  · rw [hms]; simp [hg, upd_apply]
  · simp [NSt.stop, ha, Silmaril.Wasm.Component.Streams.Net.Out.push]

end Silmaril.Proofs.Wasm.JcoTool.KDrop
