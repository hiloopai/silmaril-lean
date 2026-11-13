module

public import Silmaril.Proofs.Wasm.JcoTool.KTee.Drops

/-!
# The generated tee: events are `waitIn` and `waitOut` steps of the tee node

`sim_evR`: a read event of the input (the pending read's batch, or `DROPPED` on the idle input)
is `NStep.waitIn`. `sim_evW`: a write event of output `j` is `NStep.waitOut`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KTee

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Event EventCode blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (NSt OS RV Node NStep rh wh status count)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KTee

/-- An event is a stream read's or a stream write's. -/
theorem dwait_code {st st' : DStore} {s h : Nat} {e : Event} (hw : DWait st s h st' e) :
    e.code = .streamRead ∨ e.code = .streamWrite := by
  obtain ⟨-, -, ht⟩ := hw
  unfold takeEv at ht
  split at ht
  · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp ht
    exact .inl (by rw [← (Prod.mk.inj hp).2])
  · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp ht
    exact .inr (by rw [← (Prod.mk.inj hp).2])
  · cases ht

/-- An output when the batch is empty: drained (a pending write would have bytes to write). -/
theorem drained_of_empty {ms : MS} {j : Nat} {o : NOut} (h : ORel ms j o) (hL : ms.g LENg = 0) :
    Drained ms j o := by
  have hq : qOf ms j = [] := qOf_nil (by rw [hL]; omega)
  rcases h with ⟨e, ho⟩ | ⟨-, -, hne⟩ | h2 | h3
  · exact .inl ⟨e, by rw [ho, hq]⟩
  · exact absurd hq hne
  · exact .inr (.inl h2)
  · exact .inr (.inr h3)

/-- **`DROPPED` on the idle input**: the input has ended (or, with `COMPLETED`, nothing). -/
theorem relT_inEnd {r w₀ w₁ s p : Nat} {ms : MS} {x : NSt Unit} (hR : RelT r w₀ w₁ s ms x)
    (hne : ms.mode ≠ .exited) (hrpn : ms.rp = none) :
    RelT r w₀ w₁ s ⟨ms.g, upd ms.m aRS (if p % 16 = 0 then 0 else 2), ms.rp, .ready⟩
      (x.onRead trB p []) := by
  obtain ⟨hlen, -, hok, -, hOs⟩ := relT_inv hR hne
  have hI : IRel r ⟨ms.g, upd ms.m aRS (if p % 16 = 0 then 0 else 2), ms.rp, .ready⟩
      (x.onRead trB p []) := by
    by_cases hs : p % 16 = 0
    · exact .inl ⟨by simp [upd_apply, hs], by simp [NSt.onRead, status, hs], hrpn⟩
    · exact .inr (.inr (.inl ⟨by simp [upd_apply, hs], by simp [NSt.onRead, status, hs], hrpn⟩))
  refine relT_live (by simp [NSt.onRead, hlen]) (.inl rfl) hok hI fun j hj => ?_
  obtain ⟨o, ho, hr⟩ := hOs j hj
  exact ⟨o, by simp [NSt.onRead, ho, trB_feed, push_nil], ORel_upd_RS hr _ _⟩

/-- The input's event while it is idle. -/
theorem sim_evR_idle {r w₀ w₁ s f v : Nat} {st₁ : DStore} {ms : MS} {x : NSt Unit} {e : Event}
    {s' : DSt} (hR : RelT r w₀ w₁ s ms x) (hne : ms.mode ≠ .exited) (hpl : e.payload / 16 = e.items.length)
    (hc : e.code = .streamRead) (eR : ms.m aRS = 0) (hrpn : ms.rp = none)
    (hx : dexec evR f (inv (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) = some (.ret v, s')) :
    v = 1 ∧ s'.st = st₁ ∧ RelT r w₀ w₁ s ⟨s'.g, s'.m, s'.rp, .ready⟩ (x.onRead trB e.payload e.items) := by
  have hdel : deliver e ms = ms := by simp [deliver, hc, hrpn]
  obtain ⟨hv, hst, hrp, hcase⟩ := evR_ret hx
  rw [hdel] at hcase hrp
  rcases hcase with ⟨h1, -⟩ | ⟨-, hz, hg, hm⟩
  · exact absurd (h1.symm.trans eR) (by decide)
  have hnil : e.items = [] := by rw [← List.length_eq_zero_iff, ← hpl]; exact hz
  have e' : (⟨s'.g, s'.m, s'.rp, .ready⟩ : MS) =
      ⟨ms.g, upd ms.m aRS (if e.payload % 16 = 0 then 0 else 2), ms.rp, .ready⟩ := by
    rw [hg, hm, hrp]; rfl
  rw [e', hnil]
  exact ⟨hv, hst, relT_inEnd hR hne hrpn⟩

/-- The input's event with the pending read's batch. -/
theorem sim_evR_batch {r w₀ w₁ s f v : Nat} {st₁ : DStore} {ms : MS} {x : NSt Unit} {e : Event}
    {s' : DSt} (hR : RelT r w₀ w₁ s ms x) (hne : ms.mode ≠ .exited) (hpl : e.payload / 16 = e.items.length)
    (hil : e.items.length ≤ 256) (hc : e.code = .streamRead) (hidx : e.index = r)
    (eR : ms.m aRS = 1) (hrp1 : ms.rp = some (r, IN)) (hL0 : ms.g LENg = 0)
    (hx : dexec evR f (inv (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) = some (.ret v, s')) :
    v = 1 ∧ s'.st = st₁ ∧ RelT r w₀ w₁ s ⟨s'.g, s'.m, s'.rp, .ready⟩ (x.onRead trB e.payload e.items) := by
  obtain ⟨hlen, -, hok, -, hOs⟩ := relT_inv hR hne
  have hdel : deliver e ms = { ms with m := writeBytes ms.m IN (e.items.map byteOf), rp := none } := by
    simp [deliver, hc, hrp1, hidx]
  obtain ⟨hv, hst, hrp, hcase⟩ := evR_ret hx
  rw [hdel] at hcase hrp
  rcases hcase with ⟨-, hg, hm⟩ | ⟨h0, -⟩
  swap
  · have h0' : ms.m aRS = 0 := by simpa [writeBytes, aRS, IN, inv] using h0
    exact absurd (h0'.symm.trans eR) (by decide)
  rw [hg, hm]
  refine ⟨hv, hst, relT_batch hlen hok (fun j hj => ?_) hpl hil hrp⟩
  obtain ⟨o, ho, hr⟩ := hOs j hj
  exact ⟨o, ho, drained_of_empty hr hL0⟩

/-- **A read event of the input** is `NStep.waitIn`. -/
theorem sim_evR {a b c s f v : Nat} {st st₁ : DStore} {ms : MS} {x : NSt Unit} {e : Event}
    {s' : DSt} (hR : RelT (rh a) (wh b) (wh c) s ms x) (hne : ms.mode ≠ .exited)
    (hw : DWait st s (rh a) st₁ e) (hwf : wfD e = true) (hc : e.code = .streamRead)
    (hx : dexec evR f (inv (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) = some (.ret v, s')) :
    v = 1 ∧ ∃ x', RelT (rh a) (wh b) (wh c) s ⟨s'.g, s'.m, s'.rp, .ready⟩ x' ∧
      NStep (teeNode a b c) s st x s'.st x' := by
  obtain ⟨-, -, hI, -⟩ := (relT_inv hR hne).2
  obtain ⟨-, -, hil, hpl⟩ := wfD_inv hwf
  have hpl' : e.payload / 16 = e.items.length := hpl hc
  have hidx : e.index = rh a := dwait_index hw
  have hstep : ∀ st', s'.st = st' → st' = st₁ → NStep (teeNode a b c) s st x s'.st
      (x.onRead trB e.payload e.items) := fun _ h1 h2 => by rw [h1, h2]; exact .waitIn rfl hw
  rcases hI with ⟨eR, hrd, hrpn⟩ | ⟨eR, -, hrp1, hL0⟩ | ⟨eR, -, hrpn⟩ | ⟨eR, -, hrpn⟩
  · obtain ⟨hv, hst, hR'⟩ := sim_evR_idle hR hne hpl' hc eR hrpn hx
    exact ⟨hv, _, hR', hstep _ rfl hst⟩
  · obtain ⟨hv, hst, hR'⟩ := sim_evR_batch hR hne hpl' hil hc hidx eR hrp1 hL0 hx
    exact ⟨hv, _, hR', hstep _ rfl hst⟩
  all_goals
    have hdel : deliver e ms = ms := by simp [deliver, hc, hrpn]
    obtain ⟨-, -, -, hcase⟩ := evR_ret hx
    rw [hdel] at hcase
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> (have h' : ms.m aRS = _ := h; rw [eR] at h'; cases h')

theorem set_self_of {l : List NOut} {j : Nat} {o : NOut} (h : l[j]? = some o) : l.set j o = l := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.set_getElem_self hj

theorem ORel_busy {ms : MS} {j : Nat} {o : NOut} (h : ORel ms j o) (h1 : ms.m (aO j) = 1) :
    o.st = .busy (qOf ms j) [] := by
  rcases h with ⟨e', -⟩ | ⟨-, h, -⟩ | ⟨e', -⟩ | ⟨e', -⟩ <;> first | exact h | (rw [h1] at e'; cases e')

theorem ORel_idle {ms : MS} {j : Nat} {o : NOut} (h : ORel ms j o) (h0 : ms.m (aO j) = 0) :
    o.st = .idle (qOf ms j) := by
  rcases h with ⟨-, h⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ <;> first | exact h | (rw [h0] at e'; cases e')

/-- A write event leaves a dead or dropped output as it is. -/
theorem onWr_fixed {ms : MS} {j p : Nat} {o : NOut} (h : ORel ms j o) (h0 : ms.m (aO j) ≠ 0)
    (h1 : ms.m (aO j) ≠ 1) : onWr o p = o := by
  rcases h with ⟨e', -⟩ | ⟨e', -⟩ | ⟨-, h⟩ | ⟨-, d, h⟩
  · exact absurd e' h0
  · exact absurd e' h1
  · simp [onWr, Silmaril.Wasm.Component.Streams.Net.Out.onWrite, h]
  · simp [onWr, Silmaril.Wasm.Component.Streams.Net.Out.onWrite, h]

/-- A write event on an idle output: `DROPPED` makes it dead, anything else leaves it. -/
theorem relT_evW_idle {r w₀ w₁ s j p : Nat} (hj : j ≤ 1) {ms : MS} {x : NSt Unit} {o : NOut}
    (hlen : x.outs.length = 2) (hok : okT ms r w₀ w₁ s) (hI : IRel r ms x)
    (hOs : ∀ k, k ≤ 1 → ∃ o, x.outs[k]? = some o ∧ ORel ms k o) (ho : x.outs[j]? = some o)
    (hr : ORel ms j o) (h0 : ms.m (aO j) = 0) :
    RelT r w₀ w₁ s ⟨ms.g, if p % 16 = 0 then ms.m else upd ms.m (aO j) 2, ms.rp, .ready⟩
      { x with outs := x.outs.set j (onWr o p) } := by
  have hq : o.st = .idle (qOf ms j) := ORel_idle hr h0
  by_cases hs : p % 16 = 0
  · have ho2 : onWr o p = o := by
      simp [onWr, Silmaril.Wasm.Component.Streams.Net.Out.onWrite, hq, status, hs]
    have hm : (if p % 16 = 0 then ms.m else upd ms.m (aO j) 2) = ms.m := by simp [hs]
    rw [ho2, set_self_of ho, hm]
    exact relT_live hlen (.inl rfl) hok hI hOs
  · have ho2 : onWr o p = ⟨.dead, o.ack⟩ := by
      simp [onWr, Silmaril.Wasm.Component.Streams.Net.Out.onWrite, hq, status, hs]
    have hm : (if p % 16 = 0 then ms.m else upd ms.m (aO j) 2) = upd ms.m (aO j) 2 := by simp [hs]
    rw [ho2, hm]
    exact relT_set hj hlen (okT_out hj hok (fun _ _ => rfl) (okT_off hok hj)) hI rfl hOs
      (fun _ _ => rfl) (fun k hk => by simp [upd_apply, hk]) (.inr (.inr (.inl ⟨by simp [upd_apply], rfl⟩)))

/-- **A write event of output `j`**: the relation, by the output's state. -/
theorem relT_evW {r w₀ w₁ s j p : Nat} (hj : j ≤ 1) {ms : MS} {x : NSt Unit} {o : NOut} {g m : Nat → Nat}
    (hR : RelT r w₀ w₁ s ms x) (hne : ms.mode ≠ .exited) (ho : x.outs[j]? = some o)
    (hcase : (ms.m (aO j) = 1 ∧ g = (onWS j p ms.g ms.m).1 ∧ m = (onWS j p ms.g ms.m).2) ∨
      (ms.m (aO j) = 0 ∧ g = ms.g ∧ m = if p % 16 = 0 then ms.m else upd ms.m (aO j) 2) ∨
      (ms.m (aO j) ≠ 0 ∧ ms.m (aO j) ≠ 1 ∧ g = ms.g ∧ m = ms.m)) :
    RelT r w₀ w₁ s ⟨g, m, ms.rp, .ready⟩ { x with outs := x.outs.set j (onWr o p) } := by
  obtain ⟨hlen, -, hok, hI, hOs⟩ := relT_inv hR hne
  obtain ⟨o', ho', hr⟩ := hOs j hj
  have hoo : o' = o := Option.some.inj (ho'.symm.trans ho)
  rw [hoo] at hr
  rcases hcase with ⟨h1, rfl, rfl⟩ | ⟨h0, rfl, rfl⟩ | ⟨h0, h1, rfl, rfl⟩
  · exact relT_set hj hlen (okT_out hj hok (fun _ hk => onWS_g_other hk) (onWS_off_le (okT_off hok hj)))
      hI rfl hOs (fun _ hk => onWS_g_other hk) (fun _ hk => onWS_m_other hk)
      (ORel_onWS hj (ORel_busy hr h1) _ _)
  · exact relT_evW_idle hj hlen hok hI hOs ho hr h0
  · have ho2 : onWr o p = o := onWr_fixed hr h0 h1
    rw [ho2, set_self_of ho]
    exact relT_live hlen (.inl rfl) hok hI hOs

/-- **A write event of output `j`** is `NStep.waitOut`. -/
theorem sim_evW {a b c s j f v : Nat} (hj : j ≤ 1) {st st₁ : DStore} {ms : MS} {x : NSt Unit}
    {e : Event} {s' : DSt} (hR : RelT (rh a) (wh b) (wh c) s ms x) (hne : ms.mode ≠ .exited)
    (hw : DWait st s (wh (outC b c j)) st₁ e) (hwf : wfD e = true) (hc : e.code = .streamWrite)
    (hx : dexec (evW j) f (inv (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) = some (.ret v, s')) :
    v = 1 ∧ ∃ x', RelT (rh a) (wh b) (wh c) s ⟨s'.g, s'.m, s'.rp, .ready⟩ x' ∧
      NStep (teeNode a b c) s st x s'.st x' := by
  obtain ⟨-, -, hok, -, hOs⟩ := relT_inv hR hne
  have hpM : e.payload < M32 := (wfD_inv hwf).1
  have hdel : deliver e ms = ms := by simp [deliver, hc]
  have hx' : dexec (evW j) f (inv ms [e.code.toNat, e.index, e.payload] st₁) = some (.ret v, s') :=
    hdel ▸ hx
  obtain ⟨hv, hst, hrp, hcase⟩ := evW_ret hj hpM (okT_off hok hj) hok.2.2.2.2.1 hx'
  obtain ⟨o, ho, -⟩ := hOs j hj
  refine ⟨hv, { x with outs := x.outs.set j (onWr o e.payload) }, ?_,
    by rw [hst]; exact .waitOut (teeNode_out a b c j hj) ho hw⟩
  have hrp' : s'.rp = ms.rp := hrp
  rw [hrp']
  exact relT_evW hj hR hne ho (by
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact .inl ⟨h1, h2, h3⟩
    · exact .inr (.inl ⟨h1, h2, h3⟩)
    · exact .inr (.inr ⟨h1, h2, by rw [h3]; rfl, by rw [h3]; rfl⟩))

end Silmaril.Proofs.Wasm.JcoTool.KTee
