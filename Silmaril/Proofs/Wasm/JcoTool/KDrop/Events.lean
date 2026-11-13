module

public import Silmaril.Proofs.Wasm.JcoTool.KDrop.Reads

/-!
# The callback with an event: `WTR` and `WTRD`

* `sim_wtr`: the read's event (`waitIn`, its items fed, to `WR`), or `DROPPED` on the idle output
  (`waitOut`, the output dead, to `WTRD`).
* `sim_wtrd`: the read's event (`waitIn`, to `DEAD`).
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

/-! ## The event tests -/

theorem andE_iff (a b : E) (t : St) : (andE a b).eval t ≠ 0 ↔ a.eval t ≠ 0 ∧ b.eval t ≠ 0 := by
  by_cases ha : a.eval t = 0 <;> by_cases hb : b.eval t = 0 <;> simp [andE, E.eval, Bin.eval, ha, hb, M32]

theorem eq_iff (a b : E) (t : St) : (E.bin .eq a b).eval t ≠ 0 ↔ a.eval t = b.eval t := by
  by_cases h : a.eval t = b.eval t <;> simp [E.eval, Bin.eval, h]

theorem evIn_iff (t : St) : evIn.eval t ≠ 0 ↔ t.l 0 = 2 ∧ t.l 1 = t.g INSR := by
  rw [evIn, andE_iff, isE, eq_iff, eq_iff]
  simp [E.eval, M32]

theorem evOut_iff (t : St) : evOut.eval t ≠ 0 ↔ t.l 0 = 3 ∧ t.l 1 = t.g OUTSW := by
  rw [evOut, andE_iff, isE, eq_iff, eq_iff]
  simp [E.eval, M32]

theorem evDropped_iff (t : St) : evDropped.eval t ≠ 0 ↔ t.l 2 % 16 ≠ 0 := by
  by_cases h : t.l 2 % 16 = 0 <;> simp [evDropped, E.eval, Bin.eval, h, M32]

theorem evDropped0_iff (t : St) : evDropped0.eval t ≠ 0 ↔ t.l 2 % 16 ≠ 0 ∧ t.l 2 / 16 = 0 := by
  rw [evDropped0, andE_iff, evDropped_iff, isE, eq_iff]
  simp [E.eval, Bin.eval, M32]

theorem code_two {c : EventCode} (h : c.toNat = 2) : c = .streamRead := by
  cases c <;> simp_all [EventCode.toNat]

theorem code_three {c : EventCode} (h : c.toNat = 3) : c = .streamWrite := by
  cases c <;> simp_all [EventCode.toNat]

/-- The invocation state's locals are the event's code, index and payload. -/
theorem inv0_l (ms : MS) (a b p : Nat) (st : DStore) :
    (inv0 ms [a, b, p] st).down.l 0 = a ∧ (inv0 ms [a, b, p] st).down.l 1 = b ∧
      (inv0 ms [a, b, p] st).down.l 2 = p := ⟨rfl, rfl, rfl⟩

/-- The runtime's delivery of a read event to the pending read's buffer. -/
theorem deliver_read {e : Event} {ms : MS} {r : Nat} (hc : e.code = .streamRead) (hi : e.index = r)
    (hrp : ms.rp = some (r, IN)) :
    deliver e ms = { ms with m := writeBytes ms.m IN (e.items.map byteOf), rp := none } := by
  simp [deliver, hc, hrp, hi]

/-- Other events are not delivered to memory. -/
theorem deliver_write {e : Event} {ms : MS} (hc : e.code = .streamWrite) : deliver e ms = ms := by
  simp [deliver, hc]

theorem wfD_inv {e : Event} (h : wfD e = true) :
    e.items.length ≤ 256 ∧ (e.code = .streamRead → e.payload / 16 = e.items.length) := by
  simp only [wfD, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  refine ⟨(wellFormed_inv h.1).2.2.1, fun hc => ?_⟩
  rcases h.2 with h2 | h2
  · exact absurd hc h2
  · exact h2

/-- `pc := v; return WAIT | s << 4`. -/
theorem wait_exec {f v code s : Nat} {t s' : DSt} (hws : t.g WS = s) (hs : s < 2 ^ 28) (hv : v ≤ 8)
    (h : dexec (.seq (.gset PC (.c v)) (.ret waitCode)) f t = some (.ret code, s')) :
    code = 2 + 16 * s ∧ s' = { t with g := upd t.g PC v } := by
  have hv' : v % M32 = v := Nat.mod_eq_of_lt (by simp [M32]; omega)
  simp only [dexec, Option.some.injEq, Prod.mk.injEq, Out.ret.injEq] at h
  obtain ⟨hcode, rfl⟩ := h
  refine ⟨?_, by simp [E.eval, hv']⟩
  rw [← hcode]
  apply waitCode_evalD _ _ hs
  simp only [DSt.down]
  rw [upd_pc_ne (by decide)]
  exact hws

theorem not_wait_exited {md : Mode} {s : Nat} (h : md = .waiting s) : md ≠ .exited := by
  rw [h]; exact fun h' => by cases h'

/-- **`WTR`**: the read's event, or `DROPPED` on the idle output. -/
theorem sim_wtr {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hs : s < 2 ^ 28) (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .waiting s)
    (hpc : ms.g PC = pWTR) (hkst : ms.kst = x.s) (h0 : ms.g OLEN = 0) (hoff : ms.g OOFF = 0)
    (hrp : ms.rp = some (rh c, IN)) (hrd : x.rd = .busy) (hout : outIs x (.idle []))
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ NStep (node k c c') s st x st' x' := by
  obtain ⟨hd, st₁, e, hw, hwf, code, s', hx, hmd, hst, hms⟩ := event_inv hm h
  have hg1 : (deliver e ms).g = ms.g := deliver_g e ms
  have hc : dexec (dWTR k) FUEL (inv0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.ret code, s') := by
    simpa [inv0, hg1, hpc, caseOf, pWTR] using cb_at hx
  have hst₁ : s'.st = st₁ := noCall_st (by simp [dWTR, noCall, noCall_onReadD, yield_]) hc
  obtain ⟨a, ha⟩ := hout
  have hidx := dwait_index hw
  rcases dexec_ite_ret hc with ⟨hin, hA⟩ | ⟨-, hB⟩
  · show ∃ x', _
    obtain ⟨h0', h1'⟩ := (evIn_iff _).mp hin
    have hcode : e.code = .streamRead := code_two h0'
    have hie : e.index = rh c := by rw [← hok.1, ← hg1]; exact h1'
    have hdel := deliver_read hcode hie hrp
    obtain ⟨hlen, hcnt⟩ := wfD_inv hwf
    refine ⟨x.onRead (node k c c').T e.payload e.items, ?_, ?_⟩
    · have hK : KS (deliver e ms).g (deliver e ms).m x.s := by
        rw [hdel]; exact KS.writeIn (kst_KS hok hkst) (by simpa using hlen)
      exact after_read (i := 2) hok hoff ha hg1 hK (by show (deliver e ms).g OLEN = 0; rw [hg1]; exact h0)
        (by rw [hdel]; exact slice_writeBytes _ _ _) rfl (hcnt hcode) hlen hA hmd hms
    · rw [hst, hst₁]
      exact NStep.waitIn rfl (by rw [← hidx, hie] at hw; exact hw)
  rcases dexec_ite_ret hB with ⟨hev, hC⟩ | ⟨-, hD⟩
  · show ∃ x', _
    obtain ⟨hev₁, hev₂⟩ := (andE_iff _ _ _).mp hev
    obtain ⟨h0', h1'⟩ := (evOut_iff _).mp hev₁
    have hdr : e.payload % 16 ≠ 0 := (evDropped_iff _).mp hev₂
    have hcode : e.code = .streamWrite := code_three h0'
    have hie : e.index = wh c' := by rw [← hok.2.1, ← hg1]; exact h1'
    obtain ⟨hcd, rfl⟩ := wait_exec (by rw [inv0, hg1]; exact hok.2.2.1) hs (by decide) hC
    rw [hcd, modeOf_wait] at hmd
    have hm' : ms'.mode = .waiting s := (Option.some.inj hmd).symm
    refine ⟨{ x with outs := x.outs.set 0 ⟨.dead, a⟩ }, ?_, ?_⟩
    · rw [hms]
      refine relD_of (not_wait_exited hm') ?_ (.inr (.inr (.inl ⟨hm', ?_, ?_, ?_, a, by simp [ha]⟩)))
      · simpa [inv0, deliver_write hcode] using okD_pc (m := ms.m) (rp := ms.rp) (md := ms'.mode)
          (v := pWTRD) hok
      · simp [inv0, upd_apply, pWTRD]
      · simp [inv0, deliver_write hcode, hrp]
      · exact hrd
    · rw [hst]
      have hon : (⟨.idle [], a⟩ : Silmaril.Wasm.Component.Streams.Net.Out).onWrite e.payload = ⟨.dead, a⟩ := by
        simp [Silmaril.Wasm.Component.Streams.Net.Out.onWrite, status, hdr]
      rw [← hon]
      exact NStep.waitOut (j := 0) rfl (by simp [ha]) (by rw [← hidx, hie] at hw; exact hw)
  · simp [dexec] at hD

/-- `pc := v; YIELD`. -/
theorem pcYield_exec {f v code : Nat} {t s' : DSt} (hv : v ≤ 8)
    (h : dexec (.seq (.gset PC (.c v)) yield_) f t = some (.ret code, s')) :
    code = 1 ∧ s' = { t with g := upd t.g PC v } := by
  have hv' : v % M32 = v := Nat.mod_eq_of_lt (by simp [M32]; omega)
  simp only [yield_, dexec, Option.some.injEq, Prod.mk.injEq, Out.ret.injEq] at h
  obtain ⟨hcode, rfl⟩ := h
  exact ⟨by simpa [E.eval, M32] using hcode.symm, by simp [E.eval, hv']⟩

/-- **`WTRD`**: the read's event, with a dead output; then `DEAD`. -/
theorem sim_wtrd {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .waiting s) (hpc : ms.g PC = pWTRD)
    (hout : outIs x .dead) (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ NStep (node k c c') s st x st' x' := by
  obtain ⟨hd, st₁, e, hw, -, code, s', hx, hmd, hst, hms⟩ := event_inv hm h
  have hg1 : (deliver e ms).g = ms.g := deliver_g e ms
  have hc : dexec dWTRD FUEL (inv0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.ret code, s') := by
    simpa [inv0, hg1, hpc, caseOf, pWTR, pWTW, pRD, pEOI, pWR, pCL, pDEAD, pWTRD] using cb_at hx
  obtain ⟨a, ha⟩ := hout
  rcases dexec_ite_ret hc with ⟨hin, hA⟩ | ⟨-, hB⟩
  · show ∃ x', _
    obtain ⟨-, h1'⟩ := (evIn_iff _).mp hin
    have hie : e.index = rh c := by rw [← hok.1, ← hg1]; exact h1'
    obtain ⟨rfl, rfl⟩ := pcYield_exec (by decide) hA
    have hm' : ms'.mode = .ready := by simpa [modeOf_yield] using hmd.symm
    refine ⟨x.onRead (node k c c').T e.payload e.items, ?_, ?_⟩
    · show RelD _ _ _ _ _
      rw [hms]
      refine relD_of (by rw [hm']; decide) ?_
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hm', ?_, ?_, a, ?_⟩)))))))
      · have h₀ : okD ⟨upd ms.g PC pDEAD, (deliver e ms).m, (deliver e ms).rp, ms'.mode⟩ (rh c) (wh c') s :=
          okD_pc hok
        simpa [inv0, hg1] using h₀
      · simp [inv0, upd_apply, pDEAD]
      · by_cases h0 : e.payload % 16 = 0
        · exact .inl (by simp [NSt.onRead, status, h0])
        · exact .inr (by simp [NSt.onRead, status, h0])
      · simp [NSt.onRead, ha, Silmaril.Wasm.Component.Streams.Net.Out.push]
    · rw [hst]
      exact NStep.waitIn rfl (by rw [← dwait_index hw, hie] at hw; exact hw)
  · simp [dexec] at hB

end Silmaril.Proofs.Wasm.JcoTool.KDrop
