module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Cases

/-!
# A generated module in a network can step, or waits for its peers

`mod_progress`: a module related (`RelD`) to the state `y` of its node, under the facts the
network's invariant gives about its two streams (`Env`), steps; or it waits for a read with
nothing pending on its input, or for a write with nothing pending on its output. Under `Env`
the built-ins it calls do not trap (`read_res`, `write_res_lt`), the events it receives are well
formed (`wfD`), and the callback's cases return (`Cases`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event EventCode blocked packCopy CopyResult)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (Network NSt RV OS Out rh wh tblOf joinedOf)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Proofs.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.Component.Streams.Net (RInv WInv WV Coh)
open Silmaril.Proofs.Wasm.Component.Streams.Live (tblOf_rh_eq tblOf_wh_eq tblOf_ws_eq joinedOf_rh_eq
  joinedOf_wh_eq read_ok write_ok dropR_ok dropW_ok dstep_read_eq dstep_write_eq dstep_dropR_eq
  dstep_dropW_eq)

/-! ## The built-ins on streams in the invariant's states -/

theorem packCopy_lt (r : CopyResult) {q : Nat} (hq : q ≤ CAP) : packCopy r q < M32 := by
  cases r <;> simp only [packCopy, CopyResult.toNat, CAP, M32] at hq ⊢ <;> omega

theorem packCopy_div (r : CopyResult) (q : Nat) : packCopy r q / 16 = q := by
  cases r <;> simp only [packCopy, CopyResult.toNat] <;> omega

/-- **What a read from an idle input answers at once**: at most `n` items, counted. -/
theorem read_res {c c' : DChan} {got ys : List Val} {n p : Nat} (hR : RInv .idle got c)
    (hn : n ≤ 256) (h : c.read n = some (c', .read p ys)) :
    p < M32 ∧ p / 16 = ys.length ∧ ys.length ≤ n := by
  obtain ⟨-, -, -, -, hrg, hev⟩ := hR
  unfold DChan.read at h
  split at h
  · cases h
  · split at h
    · rename_i hw
      simp only [hev, hw, ↓reduceIte] at h
      have hy := (Prod.mk.inj (Option.some.inj h)).2
      cases hy
      simp [packCopy, CopyResult.toNat, hrg, M32]
    · split at h
      · cases h
      · cases h
      · have hy := (Prod.mk.inj (Option.some.inj h)).2
        cases hy
        refine ⟨packCopy_lt _ (by simp only [CAP]; omega), ?_, ?_⟩
        · rw [packCopy_div]; simp
        · simp

/-- **What a write to an idle output returns**: a code below `2 ^ 32`. -/
theorem write_res_lt {c c' : DChan} {ack xs : List Val} {r : Nat} (hW : WInv .idle ack c)
    (hx : xs.length ≤ CAP) (h : c.write xs = some (c', .nat r)) : r < M32 := by
  obtain ⟨-, -, -, -, hev⟩ := hW
  unfold DChan.write at h
  split at h
  · cases h
  · split at h
    · rename_i hr
      simp only [hev, hr, ↓reduceIte] at h
      have hy := (Prod.mk.inj (Option.some.inj h)).2
      cases hy
      exact packCopy_lt _ (by simp [CAP])
    · split at h
      · have hy := (Prod.mk.inj (Option.some.inj h)).2
        cases hy
        decide
      · have hy := (Prod.mk.inj (Option.some.inj h)).2
        cases hy
        exact packCopy_lt _ ((Nat.min_le_right _ _).trans hx)

/-! ## The events of the module's ends -/

/-- The read event of a busy input, delivered by `waitable-set.wait`. -/
theorem wait_rh_ev {net : Network} {st : DStore} (hc : Coh net st) {c : Nat} (hm : c < net.m)
    (hr : (st.chans (rh c)).r.gone = false) {q : Nat} (hq : (st.chans (rh c)).r.ev = some q) :
    ∃ st₁, DWait st (net.ws (net.rd c)) (rh c) st₁
      ⟨.streamRead, rh c, if (st.chans (rh c)).w.gone then packCopy .dropped q else packCopy .completed q,
        (st.chans (rh c)).rgot⟩ := by
  have ht : st.tbl (rh c) = some (.streamR (rh c)) := by rw [hc.1]; exact tblOf_rh_eq hm hr
  have hs : st.tbl (net.ws (net.rd c)) = some .wset := by rw [hc.1]; exact tblOf_ws_eq _ _
  have hj : st.joined (rh c) = some (net.ws (net.rd c)) := by rw [hc.2]; exact joinedOf_rh_eq hm hr
  exact ⟨_, hs, hj, by simp [takeEv, ht, DChan.takeR, hq]; rfl⟩

/-- The write event of an output, delivered by `waitable-set.wait`. -/
theorem wait_wh_ev {net : Network} {st : DStore} (hc : Coh net st) {c : Nat} (hm : c < net.m)
    (hw : (st.chans (rh c)).w.gone = false) {q : Nat} (hq : (st.chans (rh c)).w.ev = some q) :
    ∃ st₁, DWait st (net.ws (net.wr c).1) (wh c) st₁
      ⟨.streamWrite, wh c, if (st.chans (rh c)).r.gone then packCopy .dropped q else packCopy .completed q,
        []⟩ := by
  have ht : st.tbl (wh c) = some (.streamW (rh c)) := by rw [hc.1]; exact tblOf_wh_eq hm hw
  have hs : st.tbl (net.ws (net.wr c).1) = some .wset := by rw [hc.1]; exact tblOf_ws_eq _ _
  have hj : st.joined (wh c) = some (net.ws (net.wr c).1) := by rw [hc.2]; exact joinedOf_wh_eq hm hw
  exact ⟨_, hs, hj, by simp [takeEv, ht, DChan.takeW, hq]; rfl⟩

theorem wfD_read {h p : Nat} {ys : List Val} (hp : p < M32) (hh : h < M32) (hc : p / 16 = ys.length)
    (hy : ys.length ≤ 256) : wfD ⟨.streamRead, h, p, ys⟩ = true := by
  simp [wfD, wellFormed, hp, hh, hc, hy]

theorem wfD_write {h p : Nat} (hp : p < M32) (hh : h < M32) : wfD ⟨.streamWrite, h, p, []⟩ = true := by
  simp [wfD, wellFormed, hp, hh]

/-- The kernel's bounds at a state the kernel reaches. -/
theorem fit_of {k : KM} {N : Nat} (hfit : KFits k N) {ks : KSt} {got : List Val}
    (hks : ks = ((trV k).feed (trV k).init got).1) : Fit k N ks := by
  have he : ks = (k.tr.feed k.tr.init (got.map byteOf)).1 := by rw [hks, feed_trV]; rfl
  have h := fun bs hb hl => hfit (got.map byteOf) bs (bytes_map got) hb hl
  exact ⟨he ▸ (h [] (by simp) (by simp)).2, fun bs hb hl => he ▸ (h bs hb hl).1⟩

/-! ## The module's environment -/

/-- **What the network's invariant says about a module's streams**: the store is coherent, the
module waits on the set `s` that holds both its ends, its input `c` and output `c'` are in the
states of its node `y` (`RInv`, `WInv`), the input has no zero-length buffer, and a pending read
holds at most `N` items. -/
structure Env (net : Network) (st : DStore) (c c' s N : Nat) (y : NSt KSt) : Prop where
  coh : Coh net st
  hc : c < net.m
  hc' : c' < net.m
  sin : net.ws (net.rd c) = s
  sout : net.ws (net.wr c').1 = s
  hs : s < 2 ^ 28
  idx : rh c < M32 ∧ wh c' < M32
  rin : RInv y.rd y.got (st.chans (rh c))
  wout : ∀ o, y.outs[0]? = some o → WInv o.st.view o.ack (st.chans (rh c'))
  nz : (st.chans (rh c)).wbuf ≠ some []
  bound : (st.chans (rh c)).rgot.length ≤ N

theorem out0 {y : NSt KSt} {o : OS} (h : outIs y o) : ∃ a, y.outs[0]? = some ⟨o, a⟩ ∧ y.outs = [⟨o, a⟩] := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by simp [ha], ha⟩

/-- The input can be dropped when the node's input is idle or ended. -/
theorem env_dropR {net : Network} {st : DStore} {c c' s N : Nat} {y : NSt KSt}
    (hE : Env net st c c' s N y) (hrd : y.rd = .idle ∨ y.rd = .ended) :
    ∃ st₁ r, dstep st (.streamDropR (rh c)) = some (st₁, r) := by
  have hok : (st.chans (rh c)).r.gone = false ∧ (st.chans (rh c)).r.st ≠ .copying := by
    have hR := hE.rin
    rcases hrd with h | h
    · rw [h] at hR
      exact ⟨hR.2.1, by rw [hR.2.2.1]; decide⟩
    · rw [h] at hR
      exact ⟨hR.2.1, by rw [hR.2.2.1]; decide⟩
  obtain ⟨c₁, hd⟩ := dropR_ok hok.1 hok.2
  exact ⟨_, _, dstep_dropR_eq hE.coh hE.hc hok.1 hd⟩

/-- The output can be dropped when it is idle or dead. -/
theorem env_dropW {net : Network} {st : DStore} {c c' s N : Nat} {y : NSt KSt}
    (hE : Env net st c c' s N y) {o : OS} (ho : o = .idle [] ∨ o = .dead) (hout : outIs y o) :
    ∃ st₁ r, dstep st (.streamDropW (wh c')) = some (st₁, r) := by
  obtain ⟨a, h0, -⟩ := out0 hout
  have hW := hE.wout _ h0
  have hok : (st.chans (rh c')).w.gone = false ∧ (st.chans (rh c')).w.st ≠ .copying := by
    rcases ho with rfl | rfl
    · exact ⟨hW.1, by rw [hW.2.1]; decide⟩
    · exact ⟨hW.1, by rw [hW.2.1]; decide⟩
  obtain ⟨c₁, hd⟩ := dropW_ok hok.1 hok.2
  exact ⟨_, _, dstep_dropW_eq hE.coh hE.hc' hok.1 hd⟩

/-- An idle input can be read. -/
theorem env_read {net : Network} {st : DStore} {c c' s N : Nat} {y : NSt KSt}
    (hN : 0 < N ∧ N ≤ 256) (hE : Env net st c c' s N y) (hrd : y.rd = .idle) :
    ∃ st₁ res, dstep st (.streamRead (rh c) N) = some (st₁, res) ∧ ReadOK N res := by
  have hR : RInv .idle y.got (st.chans (rh c)) := hrd ▸ hE.rin
  obtain ⟨-, hr, hst, -, -, hev⟩ := hR
  have hev' : (st.chans (rh c)).w.gone = true → (st.chans (rh c)).r.ev.isSome := by
    intro hw; rw [hev]; simp [hw]
  obtain ⟨c₁, res, hd, hres⟩ := read_ok hr hst hev' hE.nz hN.1
  refine ⟨_, res, dstep_read_eq hE.coh hE.hc hr hd, ?_⟩
  rcases hres with rfl | ⟨p, ys, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨p, ys, rfl, read_res (hrd ▸ hE.rin) hN.2 hd⟩

/-- An idle output can be written. -/
theorem env_write {net : Network} {st : DStore} {c c' s N : Nat} {y : NSt KSt}
    (hE : Env net st c c' s N y) {xs : List Val} (hout : outIs y (.idle xs)) (hx : xs ≠ [])
    (hcap : xs.length ≤ CAP) :
    ∃ st₁ r, dstep st (.streamWrite (wh c') xs) = some (st₁, .nat r) ∧ r < M32 := by
  obtain ⟨a, h0, -⟩ := out0 hout
  have hW : WInv .idle a (st.chans (rh c')) := hE.wout _ h0
  obtain ⟨hw, hst, -, -, hev⟩ := hW
  have hev' : (st.chans (rh c')).r.gone = true → (st.chans (rh c')).w.ev.isSome := by
    intro hr; rw [hev]; simp [hr]
  obtain ⟨c₁, r, hd⟩ := write_ok hw hst hev' hx
  exact ⟨_, r, dstep_write_eq hE.coh hE.hc' hw hd, write_res_lt (hE.wout _ h0) hcap hd⟩

/-! ## Case by case -/

/-- The module can step. -/
def CanStep (k : KM) (N : Nat) (st : DStore) (ms : MS) : Prop :=
  ∃ st' ms', DRStep (genD k N) st ms st' ms'

theorem mp_rd {k : KM} {N c c' s : Nat} {net : Network} {st : DStore} {ms : MS} {y : NSt KSt}
    (hN : 0 < N ∧ N ≤ 256) (hE : Env net st c c' s N y) (hF : Fit k N y.s)
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pRD)
    (hk : ms.kst = y.s) (h0 : ms.g OLEN = 0) (hrd : y.rd = .idle) : CanStep k N st ms :=
  ready_step hm (cb_of (.inr (.inr (.inl ⟨hpc, rfl⟩)))
    (sret_rd hN hE.hs hok hk h0 hF (env_dropR hE (.inl hrd)) (env_read hN hE hrd)))

theorem mp_eoi {k : KM} {N c c' s : Nat} {net : Network} {st : DStore} {ms : MS} {y : NSt KSt}
    (hE : Env net st c c' s N y) (hF : Fit k N y.s) (hok : okD ms (rh c) (wh c') s)
    (hm : ms.mode = .ready) (hpc : ms.g PC = pEOI) (hk : ms.kst = y.s) (hrd : y.rd = .ended) :
    CanStep k N st ms := by
  obtain ⟨st₁, r, hd⟩ := env_dropR hE (.inr hrd)
  exact ready_step hm (cb_of (.inr (.inr (.inr (.inl ⟨hpc, rfl⟩))))
    (sret_dropFlush hok.1 rfl (ks_ofD hok.2.2.2.1 hk) hF.flush hd))

theorem mp_cl {k : KM} {N c c' s : Nat} {net : Network} {st : DStore} {ms : MS} {y : NSt KSt}
    (hE : Env net st c c' s N y) (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready)
    (hpc : ms.g PC = pCL) (hout : outIs y (.idle []) ∨ outIs y .dead) : CanStep k N st ms := by
  obtain ⟨st₁, r, hd⟩ : ∃ st₁ r, dstep st (.streamDropW (wh c')) = some (st₁, r) := by
    rcases hout with h | h
    · exact env_dropW hE (.inl rfl) h
    · exact env_dropW hE (.inr rfl) h
  exact ready_step hm (cb_of (.inr (.inr (.inr (.inr (.inr (.inl ⟨hpc, rfl⟩)))))) (sret_cl hok.2.1 hd))

theorem mp_dead {k : KM} {N c c' s : Nat} {net : Network} {st : DStore} {ms : MS} {y : NSt KSt}
    (hE : Env net st c c' s N y) (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready)
    (hpc : ms.g PC = pDEAD) (hrd : y.rd = .idle ∨ y.rd = .ended) : CanStep k N st ms := by
  obtain ⟨st₁, r, hd⟩ := env_dropR hE hrd
  exact ready_step hm (cb_of (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hpc, rfl⟩))))))) (sret_dead hok.1 hd))

theorem mp_wr {k : KM} {N c c' s : Nat} {net : Network} {st : DStore} {ms : MS} {y : NSt KSt}
    (hE : Env net st c c' s N y) (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready)
    (hpc : ms.g PC = pWR) (hout : outIs y (.idle ms.pending)) : CanStep k N st ms := by
  have hw : ms.g OOFF < ms.g OLEN →
      ∃ st₁ r, dstep st (.streamWrite (wh c') ms.pending) = some (st₁, .nat r) ∧ r < M32 := by
    intro hlt
    have hlen : ms.pending.length = ms.g OLEN - ms.g OOFF := pending_len ms
    have hx : ms.pending ≠ [] := by
      intro he; rw [he] at hlen; simp at hlen; omega
    have hcap : ms.pending.length ≤ CAP := by have := hok.2.2.2.2.1; omega
    exact env_write hE hout hx hcap
  exact ready_step hm (cb_of (.inr (.inr (.inr (.inr (.inl ⟨hpc, rfl⟩)))))
    (sret_wr hok.2.1 hok.2.2.1 hE.hs hok.2.2.2.2.2 hok.2.2.2.2.1 hw))

/-- The read event of a busy input, its payload and items. -/
theorem busy_ev {net : Network} {st : DStore} {c c' s N : Nat} {y : NSt KSt}
    (hE : Env net st c c' s N y) (hrd : y.rd = .busy) {q : Nat}
    (hq : (st.chans (rh c)).r.ev = some q) (hN : N ≤ 256) :
    ∃ st₁ p ys, DWait st s (rh c) st₁ ⟨.streamRead, rh c, p, ys⟩ ∧ p < M32 ∧ p / 16 = ys.length ∧
      ys.length ≤ N := by
  have hR : RInv .busy y.got (st.chans (rh c)) := hrd ▸ hE.rin
  have hr : (st.chans (rh c)).r.gone = false := hR.2.1
  have hql : q = (st.chans (rh c)).rgot.length := hR.2.2.2.2.1 q hq
  obtain ⟨st₁, hw⟩ := wait_rh_ev hE.coh hE.hc hr hq
  refine ⟨st₁, _, _, hE.sin ▸ hw, ?_, ?_, hE.bound⟩
  · split <;> exact packCopy_lt _ (by simp only [CAP]; have := hE.bound; omega)
  · split <;> rw [packCopy_div, hql]

theorem mp_wtr {k : KM} {N c c' s : Nat} {net : Network} {st : DStore} {ms : MS} {y : NSt KSt}
    (hN : 0 < N ∧ N ≤ 256) (hE : Env net st c c' s N y) (hF : Fit k N y.s)
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .waiting s) (hpc : ms.g PC = pWTR)
    (hk : ms.kst = y.s) (h0 : ms.g OLEN = 0) (hrp : ms.rp = some (rh c, IN)) (hrd : y.rd = .busy)
    {q : Nat} (hq : (st.chans (rh c)).r.ev = some q) : CanStep k N st ms := by
  obtain ⟨st₁, p, ys, hw, hp, hc, hy⟩ := busy_ev hE hrd hq hN.2
  have hd : deliver ⟨.streamRead, rh c, p, ys⟩ ms =
      { ms with m := writeBytes ms.m IN (ys.map byteOf), rp := none } := deliver_read rfl rfl hrp
  have hwf : wfD ⟨.streamRead, rh c, p, ys⟩ = true := wfD_read hp hE.idx.1 hc (hy.trans hN.2)
  refine event_step hm hw hwf ?_
  rw [hd]
  exact cb_of (.inl ⟨hpc, rfl⟩) (sret_wtr_in hN.2 hok.1 (ks_ofD hok.2.2.2.1 hk) h0 hF hc hy)

theorem mp_wtrd {k : KM} {N c c' s : Nat} {net : Network} {st : DStore} {ms : MS} {y : NSt KSt}
    (hN : 0 < N ∧ N ≤ 256) (hE : Env net st c c' s N y) (hok : okD ms (rh c) (wh c') s)
    (hm : ms.mode = .waiting s) (hpc : ms.g PC = pWTRD) (hrp : ms.rp = some (rh c, IN))
    (hrd : y.rd = .busy) {q : Nat} (hq : (st.chans (rh c)).r.ev = some q) : CanStep k N st ms := by
  obtain ⟨st₁, p, ys, hw, hp, hc, hy⟩ := busy_ev hE hrd hq hN.2
  have hd : deliver ⟨.streamRead, rh c, p, ys⟩ ms =
      { ms with m := writeBytes ms.m IN (ys.map byteOf), rp := none } := deliver_read rfl rfl hrp
  have hwf : wfD ⟨.streamRead, rh c, p, ys⟩ = true := wfD_read hp hE.idx.1 hc (hy.trans hN.2)
  refine event_step hm hw hwf ?_
  rw [hd]
  exact cb_of (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hpc, rfl⟩))))))) (sret_wtrd_in hok.1)

theorem mp_wtw {k : KM} {N c c' s : Nat} {net : Network} {st : DStore} {ms : MS} {y : NSt KSt}
    (hE : Env net st c c' s N y) (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .waiting s)
    (hpc : ms.g PC = pWTW) (hout : outIs y (.busy ms.pending [])) {q : Nat}
    (hq : (st.chans (rh c')).w.ev = some q) : CanStep k N st ms := by
  obtain ⟨a, h0, -⟩ := out0 hout
  have hW : WInv (.busy ms.pending) a (st.chans (rh c')) := hE.wout _ h0
  have hwg : (st.chans (rh c')).w.gone = false := hW.1
  have hqle : q ≤ CAP := by
    have hwp : (st.chans (rh c')).wp ≤ ms.pending.length := hW.2.2.2.1
    have hlen : ms.pending.length = ms.g OLEN - ms.g OOFF := pending_len ms
    have hcap := hok.2.2.2.2.1
    simp only [DChan.wp, hq, Option.getD_some] at hwp
    omega
  obtain ⟨st₁, hw⟩ := wait_wh_ev hE.coh hE.hc' hwg hq
  have hp : (if (st.chans (rh c')).r.gone then packCopy .dropped q else packCopy .completed q) < M32 := by
    split <;> exact packCopy_lt _ hqle
  refine event_step hm (hE.sout ▸ hw) (wfD_write hp hE.idx.2) ?_
  rw [deliver_write rfl]
  exact cb_of (.inr (.inl ⟨hpc, rfl⟩)) (sret_wtw_out hok.2.1)

/-- **A module steps, or waits for a peer**: for a read with nothing pending on its input, or
for a write with nothing pending on its output. -/
theorem mod_progress {k : KM} {N c c' s : Nat} {net : Network} (hN : 0 < N ∧ N ≤ 256)
    (hfit : KFits k N) {st : DStore} {ms : MS} {y : NSt KSt} (hR : RelD (rh c) (wh c') s ms y)
    (hex : ms.mode ≠ .exited) (hE : Env net st c c' s N y)
    (hks : y.s = ((trV k).feed (trV k).init y.got).1) :
    CanStep k N st ms ∨ (y.rd = .busy ∧ (st.chans (rh c)).r.ev = none) ∨
      (∃ xs q a, y.outs = [⟨.busy xs q, a⟩] ∧ (st.chans (rh c')).w.ev = none) := by
  have hF : Fit k N y.s := fit_of hfit hks
  obtain ⟨hok, hL⟩ := relD_live hR hex
  rcases hL with ⟨hm, hpc, hk, h0, -, hrd, -⟩ | ⟨hm, hpc, hk, h0, -, hrp, hrd, -⟩ |
    ⟨hm, hpc, hrp, hrd, -⟩ | ⟨hm, hpc, hk, hrd, -⟩ | ⟨hm, hpc, hout, -⟩ |
    ⟨hm, hpc, hout, -, -⟩ | ⟨hm, hpc, -, hout⟩ | ⟨hm, hpc, hrd, -⟩
  · exact .inl (mp_rd hN hE hF hok hm hpc hk h0 hrd)
  · cases hq : (st.chans (rh c)).r.ev with
    | none => exact .inr (.inl ⟨hrd, rfl⟩)
    | some q => exact .inl (mp_wtr hN hE hF hok hm hpc hk h0 hrp hrd hq)
  · cases hq : (st.chans (rh c)).r.ev with
    | none => exact .inr (.inl ⟨hrd, rfl⟩)
    | some q => exact .inl (mp_wtrd hN hE hok hm hpc hrp hrd hq)
  · exact .inl (mp_eoi hE hF hok hm hpc hk hrd)
  · exact .inl (mp_wr hE hok hm hpc hout)
  · cases hq : (st.chans (rh c')).w.ev with
    | none =>
      obtain ⟨a, -, ha⟩ := out0 hout
      exact .inr (.inr ⟨_, _, a, ha, rfl⟩)
    | some q => exact .inl (mp_wtw hE hok hm hpc hout hq)
  · exact .inl (mp_cl hE hok hm hpc hout)
  · exact .inl (mp_dead hE hok hm hpc hrd)

end Silmaril.Proofs.Wasm.JcoTool.KLive
