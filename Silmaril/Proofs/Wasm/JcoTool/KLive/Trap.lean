module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Main
public import Silmaril.Wasm.JcoTool.KRead.Defs

/-!
# A generated module in a live network never traps

`KRead.NoTrap P st ms`: after `YIELD` the callback returns a mode, and after `WAIT` it returns one
for **every** event the store can deliver. `KLive`'s progress shows that *some* step of every
module is possible; here every event of its waitable set is handled:

* the set of a module holds only its two ends (`joined_two`);
* while it waits for its read (`WTR`), the other event is `DROPPED` on its idle output (the
  reader went), which `dWTR` handles (`sret_wtr_out`);
* while it waits for its write (`WTW`), the other event is `DROPPED` (count `0`) on its idle
  input (the writer went), which `dWTW` handles (`sret_wtw_in`);
* with a dead output (`WTRD`) the output has no event.

**`mreach_notrap`**: in a live network every reachable module does not trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Event EventCode packCopy CopyResult)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (Network NSt RV OS rh wh joinedOf)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Wasm.JcoTool.KRead (NoTrap)
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Proofs.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.Component.Streams.Net (Coh RInv WInv wait_rh wait_wh)

/-! ## Events and invocations -/

/-- A callback case that returns an accepted code is an invocation that returns. -/
theorem dinvoke_of_sret {b : S} {ps : List Nat} {st : DStore} {ms : MS}
    (h : SRet b (inv0 ms ps st)) : ∃ r, dinvoke b ps st ms = some r := by
  obtain ⟨code, s', hx, md, hmd⟩ := h
  refine ⟨(s'.st, ⟨s'.g, s'.m, s'.rp, md⟩), ?_⟩
  have hx' : dexec b FUEL ⟨ms.g, ms.m, locals ps, st, ms.rp⟩ = some (.ret code, s') := hx
  simp only [dinvoke, hx', hmd, Option.map_some]

/-- `waitable-set.wait` on one handle is deterministic. -/
theorem dwait_det {st st₁ st₂ : DStore} {s s' h : Nat} {e₁ e₂ : Event} (h₁ : DWait st s h st₁ e₁)
    (h₂ : DWait st s' h st₂ e₂) : st₁ = st₂ ∧ e₁ = e₂ := by
  have he := h₁.2.2.symm.trans h₂.2.2
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact he

theorem takeR_ev {c c' : DChan} {p : Nat} {ys : List Val} (h : c.takeR = some (c', p, ys)) :
    ∃ q, c.r.ev = some q := by
  unfold DChan.takeR at h
  split at h
  · cases h
  · exact ⟨_, ‹_›⟩

theorem takeW_ev {c c' : DChan} {p : Nat} (h : c.takeW = some (c', p)) : ∃ q, c.w.ev = some q := by
  unfold DChan.takeW at h
  split at h
  · cases h
  · exact ⟨_, ‹_›⟩

/-- Delivering an event does not change the globals. -/
theorem deliver_g (e : Event) (ms : MS) : (deliver e ms).g = ms.g := by
  unfold deliver
  split
  · split <;> rfl
  · rfl

/-- The set an end joins: a readable end (odd handle) its reader's, a writable end its writer's. -/
theorem joinedOf_cases {net : Network} {ch : Nat → DChan} {h s : Nat}
    (hj : joinedOf net ch h = some s) :
    (h % 2 = 1 ∧ h ≤ 2 * net.m ∧ net.ws (net.rd (h / 2)) = s) ∨
      (h % 2 = 0 ∧ 0 < h ∧ h ≤ 2 * net.m ∧ net.ws (net.wr (h / 2 - 1)).1 = s) := by
  unfold joinedOf at hj
  by_cases h0 : h = 0
  · simp [h0] at hj
  by_cases h1 : h ≤ 2 * net.m
  · by_cases h2 : h % 2 = 1
    · simp only [h0, h1, h2, ↓reduceIte, Bool.not_eq_true, Option.ite_none_left_eq_some,
        Option.some.injEq] at hj
      exact .inl ⟨h2, h1, hj.2⟩
    · simp only [h0, h1, h2, ↓reduceIte, Option.ite_none_left_eq_some, Option.some.injEq] at hj
      exact .inr ⟨by omega, by omega, h1, hj.2⟩
  · simp [h0, h1] at hj

theorem rd_eq {net : Network} (hwf : net.WF) {i : Fin net.k} {c x : Nat}
    (hinp : (net.node i).inp = some c) (hx : x < net.m) (he : net.ws (net.rd x) = net.ws i) :
    x = c := by
  have hfin : net.rd x = i := Fin.ext (by simp only [Network.ws] at he; omega)
  have hr : (net.node (net.rd x)).inp = some x := hwf.rd_inp x hx
  rw [hfin, hinp] at hr
  exact (Option.some.inj hr).symm

theorem wr_eq {net : Network} (hwf : net.WF) {i : Fin net.k} {c' x : Nat}
    (hout : (net.node i).outs = [c']) (hx : x < net.m) (he : net.ws (net.wr x).1 = net.ws i) :
    x = c' := by
  have hfin : (net.wr x).1 = i := Fin.ext (by simp only [Network.ws] at he; omega)
  have hw : (net.node (net.wr x).1).outs[(net.wr x).2]? = some x := hwf.wr_out x hx
  rw [hfin, hout] at hw
  rcases hj : (net.wr x).2 with _ | j
  · rw [hj] at hw; exact (Option.some.inj hw).symm
  · rw [hj] at hw; simp at hw

/-- **The waitable set of a module holds only its two ends.** -/
theorem joined_two {net : Network} (hwf : net.WF) {st : DStore} (hc : Coh net st) {i : Fin net.k}
    {k : KM} {c c' : Nat} (hn : net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c') {h : Nat}
    (hj : st.joined h = some (net.ws i)) : h = rh c ∨ h = wh c' := by
  have hinp : (net.node i).inp = some c := by rw [hn]; rfl
  have hout : (net.node i).outs = [c'] := by rw [hn]; rfl
  have hj' : joinedOf net st.chans h = some (net.ws i) := hc.2 ▸ hj
  rcases joinedOf_cases hj' with ⟨h2, h1, he⟩ | ⟨h2, h0, h1, he⟩
  · have hx : h / 2 = c := rd_eq hwf hinp (by omega) he
    exact .inl (by simp only [rh]; omega)
  · have hx : h / 2 - 1 = c' := wr_eq hwf hout (by omega) he
    exact .inr (by simp only [wh]; omega)

/-! ## The cases the drop behaviour adds -/

/-- **`WTR`, `DROPPED` on the idle output**: wait for the read. -/
theorem sret_wtr_out {k : KM} {w p ws : Nat} {st₁ : DStore} {ms : MS} (hw : ms.g OUTSW = w)
    (hp : p % 16 ≠ 0) (hws : ms.g WS = ws) (hs : ws < 2 ^ 28) : SRet (dWTR k) (inv0 ms [3, w, p] st₁) := by
  have hin : evIn.eval (inv0 ms [3, w, p] st₁).down = 0 := by
    by_contra hne
    have h3 : (3 : Nat) = 2 := ((evIn_iff _).1 hne).1
    omega
  have hout : (andE evOut evDropped).eval (inv0 ms [3, w, p] st₁).down ≠ 0 :=
    (andE_iff _ _ _).2 ⟨(evOut_iff _).2 ⟨rfl, hw.symm⟩, (evDropped_iff _).2 hp⟩
  refine sret_ite_e hin (sret_ite_t hout (sret_seq (dexec_gsetD _ _ _ _) (sret_wait ?_ hs)))
  simpa [upd_apply, WS, PC, inv0] using hws

/-- **`WTW`, `DROPPED` (count `0`) on the idle input while reading**: the input has ended; wait
again. -/
theorem sret_wtw_in {r p ws : Nat} {st₁ : DStore} {ms : MS} (hr : ms.g INSR = r) (hnx : ms.g NXT = 1)
    (hp : p % 16 ≠ 0) (hp0 : p / 16 = 0) (hws : ms.g WS = ws) (hs : ws < 2 ^ 28) :
    SRet dWTW (inv0 ms [2, r, p] st₁) := by
  have hout : evOut.eval (inv0 ms [2, r, p] st₁).down = 0 := by
    by_contra hne
    have h3 : (2 : Nat) = 3 := ((evOut_iff _).1 hne).1
    omega
  have hnx' : (isE (.g NXT) 1).eval (inv0 ms [2, r, p] st₁).down ≠ 0 := by
    rw [isE_eval _ _ _ (by decide)]
    have : (E.g NXT).eval (inv0 ms [2, r, p] st₁).down = 1 := hnx
    simp [this]
  have hin : (andE (andE evIn evDropped0) (isE (.g NXT) 1)).eval (inv0 ms [2, r, p] st₁).down ≠ 0 :=
    (andE_iff _ _ _).2 ⟨(andE_iff _ _ _).2 ⟨(evIn_iff _).2 ⟨rfl, hr.symm⟩,
      (evDropped0_iff _).2 ⟨hp, hp0⟩⟩, hnx'⟩
  refine sret_ite_e hout (sret_ite_t hin (sret_seq (dexec_gsetD _ _ _ _) (sret_wait ?_ hs)))
  simpa [upd_apply, WS, NXT, inv0] using hws

/-! ## No trap, case by case -/

/-- A ready module that can step does not trap. -/
theorem notrap_ready {k : KM} {N : Nat} {st : DStore} {ms : MS} (hm : ms.mode = .ready)
    (h : CanStep k N st ms) : NoTrap (genD k N) st ms := by
  obtain ⟨st', ms', hd⟩ := h
  refine ⟨fun _ => ?_, fun s h st₁ e hw => by (rw [hm] at hw; cases hw)⟩
  cases hd with
  | ready _ hi => exact ⟨_, hi⟩
  | event hw' _ _ _ => rw [hm] at hw'; cases hw'

/-- A waiting module whose callback handles every event of its set does not trap. -/
theorem notrap_wait {k : KM} {N : Nat} {st : DStore} {ms : MS} {s : Nat} (hm : ms.mode = .waiting s)
    (h : ∀ h st₁ e, DWait st s h st₁ e →
      SRet (callbackD k N) (inv0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁)) :
    NoTrap (genD k N) st ms := by
  refine ⟨fun hr => by (rw [hm] at hr; cases hr), fun s' h' st₁ e hm' hw _ => ?_⟩
  rw [hm] at hm'
  injection hm' with he
  subst he
  exact dinvoke_of_sret (h h' st₁ e hw)

section
variable {net : Network} {i : Fin net.k} {k : KM} {N c c' : Nat} {st : DStore} {ms : MS}
  {y : NSt KSt}

/-- The read event of the module's busy input, whatever handle `wait` picked it from. -/
theorem in_event (hN : N ≤ 256) (hE : Env net st c c' (net.ws i) N y) (hrd : y.rd = .busy)
    {st₁ : DStore} {e : Event} (hw : DWait st (net.ws i) (rh c) st₁ e) :
    ∃ p ys, e = ⟨.streamRead, rh c, p, ys⟩ ∧ p / 16 = ys.length ∧ ys.length ≤ N := by
  obtain ⟨-, c₁, htk, -⟩ := wait_rh hE.coh hw
  obtain ⟨q, hq⟩ := takeR_ev htk
  obtain ⟨st₂, p, ys, hw2, -, hc, hy⟩ := busy_ev hE hrd hq hN
  exact ⟨p, ys, (dwait_det hw hw2).2, hc, hy⟩

/-- On an idle output, the only event is the reader's drop. -/
theorem out_idle_event (hE : Env net st c c' (net.ws i) N y) {a : List Val}
    (h0 : y.outs[0]? = some ⟨.idle [], a⟩) {st₁ : DStore} {e : Event}
    (hw : DWait st (net.ws i) (wh c') st₁ e) :
    e = ⟨.streamWrite, wh c', packCopy .dropped 0, []⟩ := by
  obtain ⟨-, c₁, htk, -⟩ := wait_wh hE.coh hw
  obtain ⟨q, hq⟩ := takeW_ev htk
  have hW : WInv .idle a (st.chans (rh c')) := hE.wout _ h0
  have hrg : (st.chans (rh c')).r.gone = true := by
    by_contra hg
    have hnone : (st.chans (rh c')).w.ev = none := by rw [hW.2.2.2.2]; simp [hg]
    simp [hnone] at hq
  have hq0 : (st.chans (rh c')).w.ev = some 0 := by rw [hW.2.2.2.2, hrg]; rfl
  obtain ⟨st₂, hw2⟩ := wait_wh_ev hE.coh hE.hc' hW.1 hq0
  have he : e = ⟨.streamWrite, wh c', if (st.chans (rh c')).r.gone then packCopy .dropped 0
      else packCopy .completed 0, []⟩ := (dwait_det hw (hE.sout ▸ hw2)).2
  simpa [hrg] using he

/-- On an idle input, the only event is the writer's drop. -/
theorem in_idle_event (hE : Env net st c c' (net.ws i) N y) (hrd : y.rd = .idle) {st₁ : DStore}
    {e : Event} (hw : DWait st (net.ws i) (rh c) st₁ e) :
    e = ⟨.streamRead, rh c, packCopy .dropped 0, []⟩ := by
  obtain ⟨-, c₁, htk, -⟩ := wait_rh hE.coh hw
  obtain ⟨q, hq⟩ := takeR_ev htk
  have hR : RInv .idle y.got (st.chans (rh c)) := hrd ▸ hE.rin
  have hwg : (st.chans (rh c)).w.gone = true := by
    by_contra hg
    have hnone : (st.chans (rh c)).r.ev = none := by rw [hR.2.2.2.2.2]; simp [hg]
    simp [hnone] at hq
  have hq0 : (st.chans (rh c)).r.ev = some 0 := by rw [hR.2.2.2.2.2, hwg]; rfl
  obtain ⟨st₂, hw2⟩ := wait_rh_ev hE.coh hE.hc hR.2.1 hq0
  have he : e = ⟨.streamRead, rh c, if (st.chans (rh c)).w.gone then packCopy .dropped 0
      else packCopy .completed 0, (st.chans (rh c)).rgot⟩ := (dwait_det hw (hE.sin ▸ hw2)).2
  simpa [hwg, hR.2.2.2.2.1] using he

/-- An ended or dropped input has no event. -/
theorem in_done_none (hE : Env net st c c' (net.ws i) N y)
    (hrd : y.rd = .ended ∨ ∃ b, y.rd = .gone b) {st₁ : DStore} {e : Event}
    (hw : DWait st (net.ws i) (rh c) st₁ e) : False := by
  obtain ⟨-, c₁, htk, -⟩ := wait_rh hE.coh hw
  obtain ⟨q, hq⟩ := takeR_ev htk
  have hnone : (st.chans (rh c)).r.ev = none := by
    rcases hrd with hrd | ⟨b, hrd⟩
    · exact (hrd ▸ hE.rin : RInv .ended y.got _).2.2.2.2.1
    · exact (hrd ▸ hE.rin : RInv (.gone b) y.got _).2.2.2.2
  simp [hnone] at hq

/-- A dead output has no event. -/
theorem out_dead_none (hE : Env net st c c' (net.ws i) N y) {a : List Val}
    (h0 : y.outs[0]? = some ⟨.dead, a⟩) {st₁ : DStore} {e : Event}
    (hw : DWait st (net.ws i) (wh c') st₁ e) : False := by
  obtain ⟨-, c₁, htk, -⟩ := wait_wh hE.coh hw
  obtain ⟨q, hq⟩ := takeW_ev htk
  have hnone : (st.chans (rh c')).w.ev = none := (hE.wout _ h0 : WInv .dead a _).2.2.2.1
  simp [hnone] at hq

/-- The event of a busy output: its write's result. -/
theorem out_busy_event (hE : Env net st c c' (net.ws i) N y)
    {a : List Val} (h0 : y.outs[0]? = some ⟨.busy ms.pending [], a⟩) {st₁ : DStore} {e : Event}
    (hw : DWait st (net.ws i) (wh c') st₁ e) : ∃ p, e = ⟨.streamWrite, wh c', p, []⟩ := by
  obtain ⟨-, c₁, htk, -⟩ := wait_wh hE.coh hw
  obtain ⟨q, hq⟩ := takeW_ev htk
  have hW : WInv (.busy ms.pending) a (st.chans (rh c')) := hE.wout _ h0
  obtain ⟨st₂, hw2⟩ := wait_wh_ev hE.coh hE.hc' hW.1 hq
  exact ⟨_, (dwait_det hw (hE.sout ▸ hw2)).2⟩

theorem nt_wtr (hwf : net.WF) (hn : net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c')
    (hN : 0 < N ∧ N ≤ 256) (hE : Env net st c c' (net.ws i) N y) (hF : Fit k N y.s)
    (hok : okD ms (rh c) (wh c') (net.ws i)) (hm : ms.mode = .waiting (net.ws i))
    (hpc : ms.g PC = pWTR) (hk : ms.kst = y.s) (h0 : ms.g OLEN = 0) (hrp : ms.rp = some (rh c, IN))
    (hrd : y.rd = .busy) (hout : outIs y (.idle [])) : NoTrap (genD k N) st ms := by
  refine notrap_wait hm fun h st₁ e hw => ?_
  rcases joined_two hwf hE.coh hn hw.2.1 with rfl | rfl
  · obtain ⟨p, ys, rfl, hc, hy⟩ := in_event hN.2 hE hrd hw
    rw [deliver_read rfl rfl hrp]
    exact cb_of (.inl ⟨hpc, rfl⟩) (sret_wtr_in hN.2 hok.1 (ks_ofD hok.2.2.2.1 hk) h0 hF hc hy)
  · obtain ⟨a, h0', -⟩ := out0 hout
    rw [out_idle_event hE h0' hw, deliver_write rfl]
    exact cb_of (.inl ⟨hpc, rfl⟩)
      (sret_wtr_out hok.2.1 (show packCopy .dropped 0 % 16 ≠ 0 by decide) hok.2.2.1 hE.hs)

theorem nt_wtrd (hwf : net.WF) (hn : net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c')
    (hN : 0 < N ∧ N ≤ 256) (hE : Env net st c c' (net.ws i) N y)
    (hok : okD ms (rh c) (wh c') (net.ws i)) (hm : ms.mode = .waiting (net.ws i))
    (hpc : ms.g PC = pWTRD) (hrp : ms.rp = some (rh c, IN)) (hrd : y.rd = .busy)
    (hout : outIs y .dead) : NoTrap (genD k N) st ms := by
  refine notrap_wait hm fun h st₁ e hw => ?_
  rcases joined_two hwf hE.coh hn hw.2.1 with rfl | rfl
  · obtain ⟨p, ys, rfl, -, -⟩ := in_event hN.2 hE hrd hw
    rw [deliver_read rfl rfl hrp]
    exact cb_of (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hpc, rfl⟩))))))) (sret_wtrd_in hok.1)
  · obtain ⟨a, h0', -⟩ := out0 hout
    exact (out_dead_none hE h0' hw).elim

theorem nt_wtw (hwf : net.WF) (hn : net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c')
    (hE : Env net st c c' (net.ws i) N y)
    (hok : okD ms (rh c) (wh c') (net.ws i)) (hm : ms.mode = .waiting (net.ws i))
    (hpc : ms.g PC = pWTW) (hout : outIs y (.busy ms.pending [])) (hnx : NxtRel ms y) :
    NoTrap (genD k N) st ms := by
  refine notrap_wait hm fun h st₁ e hw => ?_
  rcases joined_two hwf hE.coh hn hw.2.1 with rfl | rfl
  · rcases hnx with ⟨h1, hrd, -⟩ | ⟨-, hrd, -⟩ | ⟨-, b, hrd⟩
    · rw [in_idle_event hE hrd hw]
      refine cb_of (.inr (.inl ⟨(congrFun (deliver_g _ ms) PC).trans hpc, rfl⟩)) ?_
      exact sret_wtw_in ((congrFun (deliver_g _ ms) INSR).trans hok.1)
        ((congrFun (deliver_g _ ms) NXT).trans h1) (show packCopy .dropped 0 % 16 ≠ 0 by decide)
        (show packCopy .dropped 0 / 16 = 0 by decide)
        ((congrFun (deliver_g _ ms) WS).trans hok.2.2.1) hE.hs
    · exact (in_done_none hE (.inl hrd) hw).elim
    · exact (in_done_none hE (.inr ⟨b, hrd⟩) hw).elim
  · obtain ⟨a, h0, -⟩ := out0 hout
    obtain ⟨p, rfl⟩ := out_busy_event hE h0 hw
    rw [deliver_write rfl]
    exact cb_of (.inr (.inl ⟨hpc, rfl⟩)) (sret_wtw_out hok.2.1)

/-- **A related module whose environment holds does not trap.** -/
theorem notrap_of_env (hwf : net.WF) (hn : net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c')
    (hN : 0 < N ∧ N ≤ 256) (hE : Env net st c c' (net.ws i) N y) (hF : Fit k N y.s)
    (hok : okD ms (rh c) (wh c') (net.ws i)) (hL : RelL (rh c) (net.ws i) ms y) :
    NoTrap (genD k N) st ms := by
  rcases hL with ⟨hm, hpc, hk, h0, -, hrd, -⟩ | ⟨hm, hpc, hk, h0, -, hrp, hrd, hout⟩ |
    ⟨hm, hpc, hrp, hrd, hout⟩ | ⟨hm, hpc, hk, hrd, -⟩ | ⟨hm, hpc, hout, -⟩ |
    ⟨hm, hpc, hout, hnx, -⟩ | ⟨hm, hpc, -, hout⟩ | ⟨hm, hpc, hrd, -⟩
  · exact notrap_ready hm (mp_rd hN hE hF hok hm hpc hk h0 hrd)
  · exact nt_wtr hwf hn hN hE hF hok hm hpc hk h0 hrp hrd hout
  · exact nt_wtrd hwf hn hN hE hok hm hpc hrp hrd hout
  · exact notrap_ready hm (mp_eoi hE hF hok hm hpc hk hrd)
  · exact notrap_ready hm (mp_wr hE hok hm hpc hout)
  · exact nt_wtw hwf hn hE hok hm hpc hout hnx
  · exact notrap_ready hm (mp_cl hE hok hm hpc hout)
  · exact notrap_ready hm (mp_dead hE hok hm hpc hrd)

end

/-- **In a live network, no reachable module traps**: every invocation of its callback, after
`YIELD` or on any event its waitable set delivers, returns a mode. -/
theorem mreach_notrap {M : MNet} (hL : M.Live) {m : MSys M.net} (h : MReach M m)
    {i : Fin M.net.k} {k : KM} {N : Nat} (hg : M.gen i = some (k, N)) :
    NoTrap (genD k N) m.st (m.ms i) := by
  obtain ⟨s, -, hC⟩ := mctx hL h
  obtain ⟨c, c', hn, hR⟩ := (hC.abs.2 i).2 k N hg
  obtain ⟨hy1, hy2, hy3, hy4⟩ := cast_fields hn (s.ns i)
  have hE := mod_env hC hg hn ⟨hy1, hy2, hy3⟩
  have hF : Fit k N _ := fit_of (hC.fits i k N hg) (hy4 (hC.inv.node i).hs)
  by_cases hex : (m.ms i).mode = .exited
  · exact ⟨fun hm => by (rw [hex] at hm; cases hm), fun _ _ _ _ hm => by (rw [hex] at hm; cases hm)⟩
  obtain ⟨hok, hL'⟩ := relD_live hR hex
  exact notrap_of_env hC.ok.wf hn (hC.ok.size i k N hg) hE hF hok hL'

end Silmaril.Proofs.Wasm.JcoTool.KLive
