module

public import Silmaril.Proofs.Wasm.JcoTool.KDrop.Drops

/-!
# The reading cases of the callback

* `sim_rd` (`RD`): drop the input when the kernel is done; else `stream.read`: blocked
  (`readBlk`, to `WTR`) or answered at once, `COMPLETED` or `DROPPED` with its items
  (`readNow`, the items fed, to `WR`).
* `sim_wtr` (`WTR`): the read's event (`waitIn`, the items fed, to `WR`), or `DROPPED` on the
  idle output (`waitOut`, the output dead, to `WTRD`).
* `sim_wtrd` (`WTRD`): the read's event (`waitIn`, to `DEAD`).
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

/-! ## `stream.read` -/

/-- The state after a read answered at once with `code` and the items `xs`. -/
def sRead (s : DSt) (st₁ : DStore) (code : Nat) (xs : List Val) : DSt :=
  { s with st := st₁, m := writeBytes s.m IN (xs.map byteOf), l := upd s.l LR code }

/-- The state after a blocked read. -/
def sBlk (s : DSt) (st₁ : DStore) (r : Nat) : DSt :=
  { s with st := st₁, rp := some (r, IN), l := upd s.l LR blocked }

theorem read_call {rest : S} {f r N : Nat} {s s' : DSt} {o : Out} (hr : s.g INSR = r)
    (hN : N < M32) (h : dexec (.seq (.call .streamRead [.g INSR, .c IN, .c N] [LR]) rest) f s = some (o, s')) :
    (∃ st₁ code xs, dstep s.st (.streamRead r N) = some (st₁, .read code xs) ∧ code / 16 = xs.length ∧
      xs.length ≤ N ∧ dexec rest f (sRead s st₁ code xs) = some (o, s')) ∨
    (∃ st₁, dstep s.st (.streamRead r N) = some (st₁, .nat blocked) ∧
      dexec rest f (sBlk s st₁ r) = some (o, s')) := by
  have hN' : N % M32 = N := Nat.mod_eq_of_lt hN
  rcases hd : dstep s.st (.streamRead r N) with _ | ⟨st₁, res⟩
  · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN'] at h
  · rcases res with _ | v | _ | ⟨code, xs⟩ | _ | _
    · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN'] at h
    · by_cases hv : v = blocked
      · subst hv
        simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN'] at h
        exact .inr ⟨st₁, rfl, h⟩
      · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN', hv] at h
    · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN'] at h
    · by_cases hc : code < M32 ∧ code / 16 = xs.length ∧ xs.length ≤ N
      · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN', hc] at h
        exact .inl ⟨st₁, code, xs, rfl, hc.2.1, hc.2.2, h⟩
      · simp only [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN', List.map, ite_eq_right hc] at h
        cases h
    · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN'] at h
    · simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN'] at h

/-- A count of at most `256` items is not `BLOCKED`. -/
theorem code_ne_blocked {code n : Nat} (h : code / 16 = n) (hn : n ≤ 256) : code ≠ blocked := by
  simp only [blocked]
  omega

theorem isE_eval (t : St) (e : E) (v : Nat) (hv : v < M32) :
    (isE e v).eval t = if e.eval t = v then 1 else 0 := by
  simp [isE, E.eval, Bin.eval, Nat.mod_eq_of_lt hv]

theorem blocked_lt : blocked < M32 := by decide

theorem yield_exec {f code : Nat} {s s' : DSt} (h : dexec yield_ f s = some (.ret code, s')) :
    code = 1 ∧ s' = s := by
  simp only [yield_, dexec, Option.some.injEq, Prod.mk.injEq, Out.ret.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  exact ⟨by simpa [E.eval, M32] using h1.symm, rfl⟩

/-- The node after a read with packed result `p` delivering `xs`, from an idle empty output. -/
theorem onRead_outs {k : KM} {c c' p : Nat} {x : NSt KSt} {xs : List Val} {a : List Val}
    (hout : x.outs = [⟨.idle [], a⟩]) :
    outIs (x.onRead (node k c c').T p xs) (.idle ((k.tr.feed x.s (xs.map byteOf)).2.map u8v)) :=
  ⟨a, by simp [NSt.onRead, hout, Silmaril.Wasm.Component.Streams.Net.Out.push, node, feed_trV]⟩

theorem onRead_s {k : KM} {c c' p : Nat} {x : NSt KSt} {xs : List Val} :
    (x.onRead (node k c c').T p xs).s = (k.tr.feed x.s (xs.map byteOf)).1 := by
  simp [NSt.onRead, node, feed_trV]

/-- **After a read's result** (`COMPLETED` or `DROPPED`) in local `i`, its `count` items in the
input buffer: `onReadD` then `YIELD` stand for the node's `onRead`. -/
theorem after_read {k : KM} {c c' s i code p : Nat} {ms ms' : MS} {s₂ s' : DSt} {x : NSt KSt}
    {xs : List Val} {a : List Val} (hok : okD ms (rh c) (wh c') s) (hoff : ms.g OOFF = 0)
    (hout : x.outs = [⟨.idle [], a⟩]) (hg : s₂.g = ms.g) (hK : KS s₂.g s₂.m x.s) (h0 : s₂.g OLEN = 0)
    (hin : slice s₂.m IN (xs.map byteOf).length = xs.map byteOf) (hp : s₂.l i = p)
    (hcnt : p / 16 = xs.length) (hlen : xs.length ≤ 256)
    (h : dexec (.seq (onReadD k (.l i)) yield_) FUEL s₂ = some (.ret code, s'))
    (hmd : modeOf code = some ms'.mode) (hms : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩) :
    RelD (rh c) (wh c') s ms' (x.onRead (node k c c').T p xs) := by
  have hcnt' : s₂.l i / 16 = (xs.map byteOf).length := by rw [hp, hcnt, List.length_map]
  have hlen' : (xs.map byteOf).length ≤ 256 := by rw [List.length_map]; exact hlen
  rcases dexec_seq_ret h with hr | ⟨s₃, h3, hy⟩
  · cases (onReadD_sound hK h0 hin hlen' hcnt' hr).1
  obtain ⟨-, -, hP⟩ := onReadD_sound hK h0 hin hlen' hcnt' h3
  obtain ⟨rfl, rfl⟩ := yield_exec hy
  have hm : ms'.mode = .ready := by simpa [modeOf_yield] using hmd.symm
  have hkeep : ∀ j, j ≠ GST → j ≠ BLEN → j ≠ OLEN → j ≠ PC → j ≠ NXT → s'.g j = ms.g j :=
    fun j h1 h2 h3 h4 h5 => (hP.g j h1 h2 h3 h4 h5).trans (congrFun hg j)
  rw [hms]
  refine relD_wr hm hP.pc hP.nxt ?_ hP.rep ⟨?_, ?_, ?_⟩ (onRead_outs hout) ?_
  · exact (hkeep OOFF (by decide) (by decide) (by decide) (by decide) (by decide)).trans hoff
  · exact (hkeep INSR (by decide) (by decide) (by decide) (by decide) (by decide)).trans hok.1
  · exact (hkeep OUTSW (by decide) (by decide) (by decide) (by decide) (by decide)).trans hok.2.1
  · exact (hkeep WS (by decide) (by decide) (by decide) (by decide) (by decide)).trans hok.2.2.1
  · rw [hp]
    by_cases hs0 : p % 16 = 0
    · exact .inl ⟨by simp [hs0], by simp [NSt.onRead, status, hs0], onRead_s.symm⟩
    · exact .inr (.inl ⟨by simp [hs0], by simp [NSt.onRead, status, hs0], onRead_s.symm⟩)

/-! ## `RD` -/

/-- The state after `LB := 0`. -/
def sL (s : DSt) : DSt := { s with l := upd s.l LB 0 }

/-- The handles and bounds survive a change of `pc`. -/
theorem okD_pc {ms : MS} {m : Nat → Nat} {rp : Option (Nat × Nat)} {md : Mode}
    {r w s v : Nat} (hok : okD ms r w s) : okD ⟨upd ms.g PC v, m, rp, md⟩ r w s := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok
  have e : ∀ j, j ≠ PC → upd ms.g PC v j = ms.g j := fun j hj => upd_pc_ne hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show upd ms.g PC v INSR = r
    rw [e INSR (by decide)]; exact h1
  · show upd ms.g PC v OUTSW = w
    rw [e OUTSW (by decide)]; exact h2
  · show upd ms.g PC v WS = s
    rw [e WS (by decide)]; exact h3
  · show upd ms.g PC v BLEN ≤ CAP
    rw [e BLEN (by decide)]; exact h4
  · show upd ms.g PC v OLEN ≤ CAP
    rw [e OLEN (by decide)]; exact h5
  · show upd ms.g PC v OOFF ≤ upd ms.g PC v OLEN
    rw [e OOFF (by decide), e OLEN (by decide)]; exact h6

theorem kst_KS {ms : MS} {x : NSt KSt} {r w s : Nat} (hok : okD ms r w s) (hkst : ms.kst = x.s) :
    KS ms.g ms.m x.s := ks_ofD hok.2.2.2.1 hkst

/-- A blocked read: `readBlk`, to `WTR`. -/
theorem rd_blocked {k : KM} {c c' s code : Nat} {st st₁ : DStore} {ms ms' : MS} {x : NSt KSt}
    {s' : DSt} (hs : s < 2 ^ 28) (hok : okD ms (rh c) (wh c') s) (hkst : ms.kst = x.s)
    (h0 : ms.g OLEN = 0) (hoff : ms.g OOFF = 0) (hout : outIs x (.idle []))
    (hR : dexec (.ite (isE (.l LR) blocked) (.seq (.gset PC (.c pWTR)) (.ret waitCode))
      (.seq (onReadD k (.l LR)) yield_)) FUEL (sBlk (sL (inv0 ms [0, 0, 0] st)) st₁ (rh c)) =
        some (.ret code, s'))
    (hmd : modeOf code = some ms'.mode) (hms : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩) :
    RelD (rh c) (wh c') s ms' { x with rd := .busy } := by
  have hc : (isE (.l LR) blocked).eval (sBlk (sL (inv0 ms [0, 0, 0] st)) st₁ (rh c)).down ≠ 0 := by
    rw [isE_eval _ _ _ blocked_lt]
    simp [E.eval, sBlk, upd_apply]
  rw [dexec_ite, ite_eq_left hc] at hR
  simp only [dexec, dexec.dlab, Option.some.injEq, Prod.mk.injEq, Out.ret.injEq] at hR
  obtain ⟨hcode, hs'⟩ := hR
  have hcode' : code = 2 + 16 * s := by
    rw [← hcode]
    apply waitCode_evalD _ _ hs
    simp only [DSt.down]
    rw [upd_pc_ne (by decide)]
    exact hok.2.2.1
  rw [hcode', modeOf_wait] at hmd
  have hm : ms'.mode = .waiting s := (Option.some.inj hmd).symm
  subst hs'
  rw [hms]
  refine relD_of (fun h => by rw [hm] at h; cases h) (okD_pc hok) (.inr (.inl ⟨hm, ?_, ?_, ?_, ?_, rfl, rfl, hout⟩))
  · simp [upd_apply, E.eval, pWTR, M32]
  · rw [← hkst]
    simp only [MS.kst, upd_pc_ne (show GST ≠ PC by decide), upd_pc_ne (show BLEN ≠ PC by decide)]
    rfl
  · simp only [upd_pc_ne (show OLEN ≠ PC by decide)]; exact h0
  · simp only [upd_pc_ne (show OOFF ≠ PC by decide)]; exact hoff

/-- The kernel's `done`, evaluated after `LB := 0`. -/
theorem done_evalD {k : KM} {ms : MS} {x : NSt KSt} {ps : List Nat} {st : DStore} {r w s : Nat}
    (hok : okD ms r w s) (hkst : ms.kst = x.s) :
    (cE k.done).eval (sL (inv0 ms ps st)).down ≠ 0 ↔ k.tr.done x.s = true := by
  have hK := kst_KS hok hkst
  exact done_eval k hK.st hK.blen (by simp [sL, upd_apply, DSt.down])

/-- The input buffer after a read answered at once. -/
theorem sRead_in (s : DSt) (st₁ : DStore) (code : Nat) (xs : List Val) :
    slice (sRead s st₁ code xs).m IN (xs.map byteOf).length = xs.map byteOf :=
  slice_writeBytes _ _ _

/-- **`RD`**: drop the input when the kernel is done; else read: `readBlk` or `readNow`. -/
theorem sim_rd {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hN : 0 < N ∧ N ≤ 256) (hs : s < 2 ^ 28) (hok : okD ms (rh c) (wh c') s)
    (hm : ms.mode = .ready) (hpc : ms.g PC = pRD) (hkst : ms.kst = x.s) (h0 : ms.g OLEN = 0)
    (hoff : ms.g OOFF = 0) (hrd : x.rd = .idle) (hout : outIs x (.idle []))
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ NStep (node k c c') s st x st' x' := by
  obtain ⟨code, s', hx, hmd, hst, hms⟩ := ready_inv hm h
  have hc : dexec (dRD k N) FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pRD, pWTR, pWTW, inv0] using cb_at hx
  have hc₁ := hc
  rw [dRD, dexec_seq_norm (s₁ := sL (inv0 ms [0, 0, 0] st)) (by simp [dexec, E.eval, sL, M32])] at hc₁
  rcases dexec_ite_ret hc₁ with ⟨hd, hA⟩ | ⟨hnd, hB⟩
  · rw [hst]
    exact sim_dropFlush hok hkst hout (.inr ⟨hrd, .inl ((done_evalD hok hkst).mp hd)⟩)
      ⟨rfl, rfl, rfl⟩ hA hmd hms
  have hnd' : (node k c c').T.done x.s = false := by
    have := mt (done_evalD (k := k) (ps := [0, 0, 0]) (st := st) hok hkst).mpr (by simpa using hnd)
    simpa [node, trV] using this
  have hNm : N < M32 := by simp [M32]; omega
  rcases read_call (s := sL (inv0 ms [0, 0, 0] st)) hok.1 hNm hB with
    ⟨st₁, p, xs, hd, hcnt, hl, hR⟩ | ⟨st₁, hd, hR⟩
  · show ∃ x', _
    have hnb : ¬ (isE (.l LR) blocked).eval (sRead (sL (inv0 ms [0, 0, 0] st)) st₁ p xs).down ≠ 0 := by
      rw [isE_eval _ _ _ blocked_lt]
      simp [E.eval, sRead, upd_apply, code_ne_blocked hcnt (hl.trans hN.2)]
    have hst₁ : s'.st = st₁ := noCall_st (by simp [noCall, noCall_onReadD, yield_]) hR
    rw [dexec_ite, ite_eq_right hnb] at hR
    obtain ⟨a, ha⟩ := hout
    refine ⟨x.onRead (node k c c').T p xs, ?_, by rw [hst, hst₁]; exact NStep.readNow rfl hrd hnd' hN.1 hd⟩
    exact after_read hok hoff ha rfl (KS.writeIn (kst_KS hok hkst) (by simpa using hl.trans hN.2))
      h0 (sRead_in _ _ _ _) (by simp [sRead, upd_apply]) hcnt (hl.trans hN.2) (dlab_ret hR) hmd hms
  · have hst₁ : s'.st = st₁ := noCall_st (by simp [noCall, noCall_onReadD, yield_]) hR
    refine ⟨{ x with rd := .busy }, rd_blocked hs hok hkst h0 hoff hout hR hmd hms, ?_⟩
    rw [hst, hst₁]
    exact NStep.readBlk rfl hrd hnd' hN.1 hd

end Silmaril.Proofs.Wasm.JcoTool.KDrop
