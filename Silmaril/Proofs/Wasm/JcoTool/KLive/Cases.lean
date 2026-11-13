module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Term

/-!
# The generated module does not trap: the cases of the callback

For each case of `KDrop.callbackD`, under the stream facts the network's invariant gives (the
input `RInv`, the output `WInv`, a pending read of at most `N` items) and the kernel's bounds
(`KFits`), the case returns a code the runtime accepts (`SRet`): no built-in traps, no
`unreachable` is reached, no loop runs out of fuel. `ready_step` and `event_step` turn that into
a step of the runtime `DRStep`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event EventCode blocked packCopy CopyResult)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt KStmt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Proofs.Wasm.JcoTool.KDrop

/-! ## Returning, and the steps of the runtime -/

/-- The statement returns a code the runtime accepts. -/
def SRet (b : S) (s : DSt) : Prop :=
  ∃ code s', dexec b FUEL s = some (.ret code, s') ∧ ∃ md, modeOf code = some md

theorem ready_step {k : KM} {N : Nat} {st : DStore} {ms : MS} (hm : ms.mode = .ready)
    (h : SRet (callbackD k N) (inv0 ms [0, 0, 0] st)) : ∃ st' ms', DRStep (genD k N) st ms st' ms' := by
  obtain ⟨code, s', hx, md, hmd⟩ := h
  refine ⟨s'.st, ⟨s'.g, s'.m, s'.rp, md⟩, DRStep.ready hm ?_⟩
  have hx' : dexec (genD k N).cb FUEL ⟨ms.g, ms.m, locals [0, 0, 0], st, ms.rp⟩ =
      some (.ret code, s') := hx
  simp only [dinvoke, hx', hmd, Option.map_some]

theorem event_step {k : KM} {N s h : Nat} {st st₁ : DStore} {ms : MS} {e : Event}
    (hm : ms.mode = .waiting s) (hw : DWait st s h st₁ e) (hwf : wfD e = true)
    (hc : SRet (callbackD k N) (inv0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁)) :
    ∃ st' ms', DRStep (genD k N) st ms st' ms' := by
  obtain ⟨code, s', hx, md, hmd⟩ := hc
  refine ⟨s'.st, ⟨s'.g, s'.m, s'.rp, md⟩, DRStep.event hm hw hwf ?_⟩
  have hx' : dexec (genD k N).cb FUEL ⟨(deliver e ms).g, (deliver e ms).m,
      locals [e.code.toNat, e.index, e.payload], st₁, (deliver e ms).rp⟩ = some (.ret code, s') := hx
  simp only [dinvoke, hx', hmd, Option.map_some]

theorem sret_ite_t {c : E} {t e : S} {s : DSt} (hc : c.eval s.down ≠ 0) (h : SRet t s) :
    SRet (.ite c t e) s := by
  obtain ⟨code, s', hx, hmd⟩ := h
  exact ⟨code, s', by simp only [dexec_ite, hc, ne_eq, not_false_eq_true, ↓reduceIte, hx]; rfl, hmd⟩

theorem sret_ite_e {c : E} {t e : S} {s : DSt} (hc : c.eval s.down = 0) (h : SRet e s) :
    SRet (.ite c t e) s := by
  obtain ⟨code, s', hx, hmd⟩ := h
  exact ⟨code, s', by simp only [dexec_ite, hc, ne_eq, not_true_eq_false, ↓reduceIte, hx]; rfl, hmd⟩

theorem sret_seq {a b : S} {s s₁ : DSt} (h₁ : dexec a FUEL s = some (.norm, s₁)) (h : SRet b s₁) :
    SRet (.seq a b) s := by
  obtain ⟨code, s', hx, hmd⟩ := h
  exact ⟨code, s', by rw [dexec_seq_norm h₁, hx], hmd⟩

theorem sret_yield (s : DSt) : SRet yield_ s :=
  ⟨1, s, by simp [yield_, dexec, E.eval, M32], .ready, rfl⟩

theorem sret_wait {s : DSt} {ws : Nat} (hws : s.g WS = ws) (hs : ws < 2 ^ 28) : SRet (.ret waitCode) s :=
  ⟨2 + 16 * ws, s, by simp only [dexec, waitCode_evalD s.down hws hs], _, modeOf_wait ws⟩

theorem dexec_gsetD (i : Nat) (e : E) (f : Nat) (s : DSt) :
    dexec (.gset i e) f s = some (.norm, { s with g := upd s.g i (e.eval s.down) }) := rfl

theorem dexec_lsetD (i : Nat) (e : E) (f : Nat) (s : DSt) :
    dexec (.lset i e) f s = some (.norm, { s with l := upd s.l i (e.eval s.down) }) := rfl

/-- A statement without calls, run by `exec`. -/
theorem dexec_of_exec {b : S} (hb : noCall b = true) {f : Nat} {s : DSt} {o : Silmaril.Wasm.JcoTool.KCore.Out} {t : St}
    (h : exec b f s.down = some (o, t)) : dexec b f s = some (o, DSt.up t s.st) := by
  rw [dexec_down hb, h]
  rfl

/-! ## Dispatch -/

/-- The callback runs the case of `pc`. -/
theorem cb_of {k : KM} {N : Nat} {s : DSt} {b : S}
    (hb : (s.g PC = pWTR ∧ b = dWTR k) ∨ (s.g PC = pWTW ∧ b = dWTW) ∨ (s.g PC = pRD ∧ b = dRD k N) ∨
      (s.g PC = pEOI ∧ b = dEOI k) ∨ (s.g PC = pWR ∧ b = dWR) ∨ (s.g PC = pCL ∧ b = dCL) ∨
      (s.g PC = pDEAD ∧ b = dDEAD) ∨ (s.g PC = pWTRD ∧ b = dWTRD))
    (h : SRet b s) : SRet (callbackD k N) s := by
  have e : ∀ n, n ≤ 8 → (pcIs n).eval s.down = if s.g PC = n then 1 else 0 :=
    fun n hn => pcIs_evalD s hn
  rcases hb with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩ |
    ⟨hp, rfl⟩ | ⟨hp, rfl⟩ <;>
  · unfold callbackD
    repeat first
      | exact h
      | (apply sret_ite_t (by rw [e _ (by decide), hp]; decide))
      | (apply sret_ite_e (by rw [e _ (by decide), hp]; decide))

/-! ## Without built-ins -/

theorem exec_ite_gset (c : E) (i j : Nat) (e₁ e₂ : E) (f : Nat) (t : St) :
    ∃ t', exec (.ite c (.gset i e₁) (.gset j e₂)) f t = some (.norm, t') := by
  rw [exec_ite]
  by_cases hc : c.eval t ≠ 0
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte]; exact ⟨_, rfl⟩
  · simp only [hc, ↓reduceIte]; exact ⟨_, rfl⟩

/-- `onWriteD` returns normally. -/
theorem onWriteD_complete (p : E) (f : Nat) (s : DSt) : ∃ s', dexec (onWriteD p) f s = some (.norm, s') := by
  have h : ∃ t, exec (onWriteD p) f s.down = some (.norm, t) := by
    unfold onWriteD
    rw [exec_ite]
    by_cases hc : (E.bin .remu p (.c 16)).eval s.down ≠ 0
    · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte]
      obtain ⟨t, ht⟩ := exec_ite_gset (.g NXT) PC PC (.c pDEAD) (.c pCL) f s.down
      exact ⟨t, by rw [ht]; rfl⟩
    · simp only [hc, ↓reduceIte]
      simp only [seqs]
      rw [exec_seq_norm (exec_lset _ _ _ _)]
      obtain ⟨t, ht⟩ := exec_ite_gset (.bin .geu (.l LN) (.bin .sub (.g OLEN) (.g OOFF))) OOFF OOFF
        (.g OLEN) (.bin .add (.g OOFF) (.l LN)) f
        { s.down with l := upd s.down.l LN ((E.bin .divu p (.c 16)).eval s.down) }
      rw [exec_seq_norm ht, exec_gset]
      exact ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := h
  exact ⟨_, dexec_of_exec (noCall_onWriteD p) ht⟩

/-- The output written: reset, continue as `NXT` says, `YIELD`. -/
theorem sret_reset (s : DSt) : SRet (seqs [.gset OOFF (.c 0), .gset OLEN (.c 0), nextPC, yield_]) s := by
  have hn : upd (upd s.g OOFF 0) OLEN 0 NXT = s.g NXT := by simp [upd_apply, NXT, OOFF, OLEN]
  by_cases h1 : s.g NXT = 1
  · exact ⟨1, _, by simp [seqs, nextPC, dexec, isE, E.eval, Bin.eval, yield_, dexec.dlab, hn, h1, M32]; rfl,
      .ready, rfl⟩
  by_cases h2 : s.g NXT = 2
  · exact ⟨1, _, by simp [seqs, nextPC, dexec, isE, E.eval, Bin.eval, yield_, dexec.dlab, hn, h2, M32]; rfl,
      .ready, rfl⟩
  · exact ⟨1, _, by simp [seqs, nextPC, dexec, isE, E.eval, Bin.eval, yield_, dexec.dlab, hn, h1, h2, M32]; rfl,
      .ready, rfl⟩

/-! ## `CL`, `DEAD`, `EOI` -/

theorem sret_cl {st st₁ : DStore} {ms : MS} {ps : List Nat} {w : Nat} {r : Res} (hw : ms.g OUTSW = w)
    (hd : dstep st (.streamDropW w) = some (st₁, r)) : SRet dCL (inv0 ms ps st) :=
  ⟨0, _, by simp [dCL, seqs, dexec, dcallBI, E.eval, inv0, DSt.down, hw, hd]; rfl, .exited, rfl⟩

theorem dropR_norm {st st₁ : DStore} {s : DSt} {r' : Nat} {r : Res} (hr : s.g INSR = r')
    (hst : s.st = st) (hd : dstep st (.streamDropR r') = some (st₁, r)) :
    dexec (.call .dropR [.g INSR] []) FUEL s = some (.norm, { s with st := st₁ }) := by
  subst hst
  simp [dexec, dcallBI, E.eval, DSt.down, hr, hd]

theorem sret_dead {st st₁ : DStore} {ms : MS} {ps : List Nat} {r' : Nat} {r : Res}
    (hr : ms.g INSR = r') (hd : dstep st (.streamDropR r') = some (st₁, r)) :
    SRet dDEAD (inv0 ms ps st) := by
  have e₁ := dropR_norm (s := inv0 ms ps st) hr rfl hd
  exact sret_seq e₁ (sret_seq (dexec_gsetD _ _ _ _) (sret_yield _))

/-- Drop the input, run the flush, `YIELD` (`EOI`, and `RD` when the kernel is done). -/
theorem sret_dropFlush {k : KM} {st st₁ : DStore} {s : DSt} {r' : Nat} {r : Res} {ks : KSt}
    (hr : s.g INSR = r') (hst : s.st = st) (hK : KS s.g s.m ks) (hfit : fitsS 0 k.flush ks 0 = true)
    (hd : dstep st (.streamDropR r') = some (st₁, r)) :
    SRet (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) s := by
  have e₁ := dropR_norm hr hst hd
  obtain ⟨t, ht⟩ := flushOut_complete (k := k) (f := FUEL) (s := ({ s with st := st₁ } : DSt).down) hK hfit
  have e₂ := dexec_of_exec (noCall_flushOut k) ht
  exact sret_seq e₁ (sret_seq e₂ (sret_yield _))

/-! ## `WR` -/

/-- What a `stream.write` of the pending output returns, when it returns. -/
theorem sret_wr_write {st st₁ : DStore} {ms : MS} {w ws : Nat} {r : Nat} (hw : ms.g OUTSW = w)
    (hws : ms.g WS = ws) (hs : ws < 2 ^ 28) (hle : ms.g OOFF ≤ ms.g OLEN) (hcap : ms.g OLEN ≤ CAP)
    (hr : r < M32) (hd : dstep st (.streamWrite w ms.pending) = some (st₁, .nat r)) :
    SRet (.seq (.call .streamWrite [.g OUTSW, .bin .add (.c OUT) (.g OOFF),
      .bin .sub (.g OLEN) (.g OOFF)] [LR]) (.ite (isE (.l LR) blocked) (.seq (.gset PC (.c pWTW))
        (.ret waitCode)) (.seq (onWriteD (.l LR)) yield_))) (inv0 ms [0, 0, 0] st) := by
  obtain ⟨ha, hb⟩ := write_args (s := inv0 ms [0, 0, 0] st) hle hcap
  have hit : (slice ms.m (OUT + ms.g OOFF) (ms.g OLEN - ms.g OOFF)).map u8v = ms.pending := write_items ms
  have e₁ : dexec (.call .streamWrite [.g OUTSW, .bin .add (.c OUT) (.g OOFF),
      .bin .sub (.g OLEN) (.g OOFF)] [LR]) FUEL (inv0 ms [0, 0, 0] st) =
      some (.norm, { inv0 ms [0, 0, 0] st with st := st₁, l := upd (inv0 ms [0, 0, 0] st).l LR r }) := by
    simp only [dexec, dcallBI, List.map]
    rw [show (E.g OUTSW).eval (inv0 ms [0, 0, 0] st).down = w from hw, ha, hb]
    simp only [inv0] at hit ⊢
    rw [hit, hd]
    simp [hr]
  refine sret_seq e₁ ?_
  by_cases hbl : r = blocked
  · refine sret_ite_t (by rw [isE_LR_upd]; simp [hbl]) ?_
    exact sret_seq (dexec_gsetD _ _ _ _)
      (sret_wait (by simp only [inv0]; rw [upd_pc_ne (show WS ≠ PC by decide)]; exact hws) hs)
  · refine sret_ite_e (by rw [isE_LR_upd]; simp [hbl]) ?_
    obtain ⟨s₂, h₂⟩ := onWriteD_complete (.l LR) FUEL
      { inv0 ms [0, 0, 0] st with st := st₁, l := upd (inv0 ms [0, 0, 0] st).l LR r }
    exact sret_seq h₂ (sret_yield _)

/-! ## `RD` -/

/-- **After a read's result, the feed loop finishes**, under the kernel's bounds. -/
theorem onReadD_complete {k : KM} {f i : Nat} {s : DSt} {ks : KSt} {bs : List Nat}
    (hK : KS s.g s.m ks) (h0 : s.g OLEN = 0) (hin : slice s.m IN bs.length = bs)
    (hlen : bs.length ≤ 256) (hcnt : s.l i / 16 = bs.length) (hfit : fitsF k ks bs 0 = true)
    (hf : bs.length < f) : ∃ s', dexec (onReadD k (.l i)) f s = some (.norm, s') := by
  have h : ∃ t, exec (onReadD k (.l i)) f s.down = some (.norm, t) := by
    rw [onReadD_pre k f i s.down]
    have hc : s.down.l i / 16 = bs.length := hcnt
    rw [hc]
    obtain ⟨t₂, h₂⟩ := feed_complete (linv_sN (t := s.down) (if s.down.l i % 16 = 0 then 1 else 2) hK h0 hin hlen)
      (by simpa using hfit) hf
    exact ⟨_, by rw [exec_seq_norm h₂, exec_gset]⟩
  obtain ⟨t, ht⟩ := h
  exact ⟨_, dexec_of_exec (noCall_onReadD k _) ht⟩

/-- The results of `stream.read` the module accepts. -/
def ReadOK (N : Nat) (res : Res) : Prop :=
  res = .nat blocked ∨ ∃ p ys, res = .read p ys ∧ p < M32 ∧ p / 16 = ys.length ∧ ys.length ≤ N

theorem read_blk_norm {st st₁ : DStore} {s : DSt} {r N : Nat} (hr : s.g INSR = r) (hst : s.st = st)
    (hN : N < M32) (hd : dstep st (.streamRead r N) = some (st₁, .nat blocked)) :
    dexec (.call .streamRead [.g INSR, .c IN, .c N] [LR]) FUEL s = some (.norm, sBlk s st₁ r) := by
  subst hst
  have hN' : N % M32 = N := Nat.mod_eq_of_lt hN
  simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN', sBlk]

theorem read_now_norm {st st₁ : DStore} {s : DSt} {r N p : Nat} {ys : List Val} (hr : s.g INSR = r)
    (hst : s.st = st) (hN : N < M32) (hp : p < M32 ∧ p / 16 = ys.length ∧ ys.length ≤ N)
    (hd : dstep st (.streamRead r N) = some (st₁, .read p ys)) :
    dexec (.call .streamRead [.g INSR, .c IN, .c N] [LR]) FUEL s = some (.norm, sRead s st₁ p ys) := by
  subst hst
  have hN' : N % M32 = N := Nat.mod_eq_of_lt hN
  simp [dexec, dcallBI, E.eval, DSt.down, hr, hd, hN', hp, sRead]

/-- The kernel's bounds at the module's kernel state. -/
structure Fit (k : KM) (N : Nat) (ks : KSt) : Prop where
  flush : fitsS 0 k.flush ks 0 = true
  feed : ∀ bs : List Nat, (∀ b ∈ bs, b < 256) → bs.length ≤ N → fitsF k ks bs 0 = true

theorem bytes_map (ys : List Val) : ∀ b ∈ ys.map byteOf, b < 256 := by
  intro b hb
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hb
  exact Silmaril.Wasm.JcoTool.KCore.byteOf_lt v

/-- After a read answered at once: feed, `YIELD`. -/
theorem sret_rd_now {k : KM} {N : Nat} {st₁ : DStore} {s : DSt} {p : Nat} {ys : List Val} {ks : KSt}
    (hN : N ≤ 256) (hK : KS s.g s.m ks) (h0 : s.g OLEN = 0) (hF : Fit k N ks)
    (hp : p < M32 ∧ p / 16 = ys.length ∧ ys.length ≤ N) :
    SRet (.ite (isE (.l LR) blocked) (.seq (.gset PC (.c pWTR)) (.ret waitCode))
      (.seq (onReadD k (.l LR)) yield_)) (sRead s st₁ p ys) := by
  have hnb : (isE (.l LR) blocked).eval (sRead s st₁ p ys).down = 0 := by
    rw [isE_eval _ _ _ blocked_lt]
    simp [E.eval, sRead, upd_apply, code_ne_blocked hp.2.1 (hp.2.2.trans hN)]
  refine sret_ite_e hnb ?_
  have hlen : (ys.map byteOf).length ≤ N := by rw [List.length_map]; exact hp.2.2
  obtain ⟨s₂, h₂⟩ := onReadD_complete (k := k) (f := FUEL) (i := LR) (s := sRead s st₁ p ys) (ks := ks)
    (bs := ys.map byteOf) (KS.writeIn hK (hlen.trans hN)) h0 (sRead_in _ _ _ _) (hlen.trans hN)
    (by simp [sRead, upd_apply, hp.2.1]) (hF.feed _ (bytes_map ys) hlen)
    (by simp only [FUEL, M32]; omega)
  exact sret_seq h₂ (sret_yield _)

/-- `RD` when the kernel is not done: the read, blocked or answered. -/
theorem sret_rd_read {k : KM} {N c c' s : Nat} {st : DStore} {ms : MS} {ks : KSt}
    (hN : 0 < N ∧ N ≤ 256) (hs : s < 2 ^ 28) (hok : okD ms (rh c) (wh c') s) (hK : KS ms.g ms.m ks)
    (h0 : ms.g OLEN = 0) (hF : Fit k N ks)
    (hread : ∃ st₁ res, dstep st (.streamRead (rh c) N) = some (st₁, res) ∧ ReadOK N res) :
    SRet (.seq (.call .streamRead [.g INSR, .c IN, .c N] [LR])
      (.ite (isE (.l LR) blocked) (.seq (.gset PC (.c pWTR)) (.ret waitCode))
        (.seq (onReadD k (.l LR)) yield_))) (sL (inv0 ms [0, 0, 0] st)) := by
  have hNm : N < M32 := by simp only [M32]; omega
  obtain ⟨st₁, res, hdr, hres⟩ := hread
  rcases hres with rfl | ⟨p, ys, rfl, hp⟩
  · refine sret_seq (read_blk_norm hok.1 rfl hNm hdr) ?_
    have hbl : (isE (.l LR) blocked).eval (sBlk (sL (inv0 ms [0, 0, 0] st)) st₁ (rh c)).down ≠ 0 := by
      rw [isE_eval _ _ _ blocked_lt]
      simp [E.eval, sBlk, upd_apply]
    have hws : (sBlk (sL (inv0 ms [0, 0, 0] st)) st₁ (rh c)).g WS = s := hok.2.2.1
    refine sret_ite_t hbl (sret_seq (dexec_gsetD _ _ _ _) (sret_wait ?_ hs))
    simp only [sBlk, sL, inv0] at hws ⊢
    rw [upd_pc_ne (show WS ≠ PC by decide)]
    exact hws
  · exact sret_seq (read_now_norm hok.1 rfl hNm hp hdr) (sret_rd_now hN.2 hK h0 hF hp)

/-- **`RD`** returns: the kernel done (drop, flush), or a read, blocked or answered. -/
theorem sret_rd {k : KM} {N c c' s : Nat} {st : DStore} {ms : MS} {ks : KSt} (hN : 0 < N ∧ N ≤ 256)
    (hs : s < 2 ^ 28) (hok : okD ms (rh c) (wh c') s) (hkst : ms.kst = ks) (h0 : ms.g OLEN = 0)
    (hF : Fit k N ks) (hdrop : ∃ st₁ r, dstep st (.streamDropR (rh c)) = some (st₁, r))
    (hread : ∃ st₁ res, dstep st (.streamRead (rh c) N) = some (st₁, res) ∧ ReadOK N res) :
    SRet (dRD k N) (inv0 ms [0, 0, 0] st) := by
  have hK : KS ms.g ms.m ks := ks_ofD hok.2.2.2.1 hkst
  have e₀ : dexec (.lset LB (.c 0)) FUEL (inv0 ms [0, 0, 0] st) = some (.norm, sL (inv0 ms [0, 0, 0] st)) := by
    simp [dexec, E.eval, sL, M32]
  refine sret_seq e₀ ?_
  have hde : (cE k.done).eval (sL (inv0 ms [0, 0, 0] st)).down ≠ 0 ↔ k.tr.done ks = true :=
    done_evalD (k := k) (x := ⟨ks, [], .idle, []⟩) (ps := [0, 0, 0]) (st := st) hok hkst
  by_cases hd : k.tr.done ks = true
  · have hc := hde.mpr hd
    obtain ⟨st₁, r, hdr⟩ := hdrop
    exact sret_ite_t hc (sret_dropFlush hok.1 rfl hK hF.flush hdr)
  · have hc : (cE k.done).eval (sL (inv0 ms [0, 0, 0] st)).down = 0 := by
      by_contra hne
      exact hd (hde.mp hne)
    exact sret_ite_e hc (sret_rd_read hN hs hok hK h0 hF hread)

/-! ## `WR` and `EOI` -/

/-- **`WR`** returns: the output written (resume), or a write of the rest. -/
theorem sret_wr {st : DStore} {ms : MS} {w ws : Nat} (hw : ms.g OUTSW = w) (hws : ms.g WS = ws)
    (hs : ws < 2 ^ 28) (hle : ms.g OOFF ≤ ms.g OLEN) (hcap : ms.g OLEN ≤ CAP)
    (hwrite : ms.g OOFF < ms.g OLEN →
      ∃ st₁ r, dstep st (.streamWrite w ms.pending) = some (st₁, .nat r) ∧ r < M32) :
    SRet dWR (inv0 ms [0, 0, 0] st) := by
  by_cases hge : ms.g OLEN ≤ ms.g OOFF
  · exact sret_ite_t ((geu_iff (inv0 ms [0, 0, 0] st)).mpr hge) (sret_reset _)
  · have hc : (E.bin .geu (.g OOFF) (.g OLEN)).eval (inv0 ms [0, 0, 0] st).down = 0 := by
      by_contra hne
      exact hge ((geu_iff (inv0 ms [0, 0, 0] st)).mp hne)
    obtain ⟨st₁, r, hd, hr⟩ := hwrite (Nat.lt_of_not_le hge)
    exact sret_ite_e hc (sret_wr_write hw hws hs hle hcap hr hd)

/-! ## Events -/

/-- **`WTR`, the read's event**: feed the items, `YIELD`. -/
theorem sret_wtr_in {k : KM} {N r p : Nat} {st₁ : DStore} {ms : MS} {ys : List Val} {ks : KSt}
    (hN : N ≤ 256) (hr : ms.g INSR = r) (hK : KS ms.g ms.m ks) (h0 : ms.g OLEN = 0)
    (hF : Fit k N ks) (hp : p / 16 = ys.length) (hyl : ys.length ≤ N) :
    SRet (dWTR k) (inv0 { ms with m := writeBytes ms.m IN (ys.map byteOf), rp := none } [2, r, p] st₁) := by
  have hin : evIn.eval (inv0 { ms with m := writeBytes ms.m IN (ys.map byteOf), rp := none } [2, r, p] st₁).down ≠ 0 :=
    (evIn_iff _).mpr ⟨rfl, hr.symm⟩
  refine sret_ite_t hin ?_
  have hlen : (ys.map byteOf).length ≤ N := by rw [List.length_map]; exact hyl
  obtain ⟨s₂, h₂⟩ := onReadD_complete (k := k) (f := FUEL) (i := 2) (ks := ks) (bs := ys.map byteOf)
    (s := inv0 { ms with m := writeBytes ms.m IN (ys.map byteOf), rp := none } [2, r, p] st₁)
    (KS.writeIn hK (hlen.trans hN)) h0 (slice_writeBytes _ _ _) (hlen.trans hN)
    (by simp [inv0, locals, hp]) (hF.feed _ (bytes_map ys) hlen) (by simp only [FUEL, M32]; omega)
  exact sret_seq h₂ (sret_yield _)

/-- **`WTRD`, the read's event**: to `DEAD`, `YIELD`. -/
theorem sret_wtrd_in {r p : Nat} {st₁ : DStore} {ms : MS} (hr : ms.g INSR = r) :
    SRet dWTRD (inv0 ms [2, r, p] st₁) := by
  have hin : evIn.eval (inv0 ms [2, r, p] st₁).down ≠ 0 := (evIn_iff _).mpr ⟨rfl, hr.symm⟩
  exact sret_ite_t hin (sret_seq (dexec_gsetD _ _ _ _) (sret_yield _))

/-- **`WTW`, the write's event**: advance or kill the output, `YIELD`. -/
theorem sret_wtw_out {w p : Nat} {st₁ : DStore} {ms : MS} (hw : ms.g OUTSW = w) :
    SRet dWTW (inv0 ms [3, w, p] st₁) := by
  have hout : evOut.eval (inv0 ms [3, w, p] st₁).down ≠ 0 := (evOut_iff _).mpr ⟨rfl, hw.symm⟩
  obtain ⟨s₂, h₂⟩ := onWriteD_complete (.l 2) FUEL (inv0 ms [3, w, p] st₁)
  exact sret_ite_t hout (sret_seq h₂ (sret_yield _))

end Silmaril.Proofs.Wasm.JcoTool.KLive
