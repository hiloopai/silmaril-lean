module

public import Silmaril.Proofs.Wasm.JcoTool.KDrop.Events

/-!
# The writing cases of the callback: `WR` and `WTW`

* `after_write`: a write's result `p` (from `stream.write` or from the write's event) stands for
  the node's `Out.onWrite p` of its busy output: the offset advanced (to `WR`), or the output
  dead (to `DEAD`, or `CL` when the input is already dropped).
* `sim_wr` (`WR`): resume when the output is written (no built-in, the node unchanged), else
  `stream.write` of the pending output (`write`: blocked to `WTW`, or `after_write`).
* `sim_wtw` (`WTW`): the write's event (`waitOut`, `after_write`), or `DROPPED` on the idle input
  (`waitIn`: the input has ended, `NXT := 2`, wait again).
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

/-- The node's output after a write's result `p`. -/
abbrev NOut := Silmaril.Wasm.Component.Streams.Net.Out

theorem pending_len (ms : MS) : ms.pending.length = ms.g OLEN - ms.g OOFF := by
  simp [MS.pending, slice_length]

theorem nxtRel_of {ms ms' : MS} {x x' : NSt KSt} (h : NxtRel ms x) (hn : ms'.g NXT = ms.g NXT)
    (hk : ms'.kst = ms.kst) (hrd : x'.rd = x.rd) (hs : x'.s = x.s) : NxtRel ms' x' := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, b, h2⟩
  · exact .inl ⟨hn.trans h1, hrd.trans h2, hk.trans (h3.trans hs.symm)⟩
  · exact .inr (.inl ⟨hn.trans h1, hrd.trans h2, hk.trans (h3.trans hs.symm)⟩)
  · exact .inr (.inr ⟨hn.trans h1, b, hrd.trans h2⟩)

/-- After a completed write of `count p` items: `WR` with the rest pending. -/
theorem relD_completed {c c' s p : Nat} {ms : MS} {g m : Nat → Nat} {rp : Option (Nat × Nat)}
    {x : NSt KSt} {a : List Val} {md : Mode} (hok : okD ms (rh c) (wh c') s) (hnr : NxtRel ms x)
    (hm : md = .ready) (hc : p % 16 = 0)
    (hg : g = upd (upd ms.g OOFF (min (ms.g OOFF + p / 16) (ms.g OLEN))) PC pWR) (hmm : m = ms.m) :
    RelD (rh c) (wh c') s ⟨g, m, rp, md⟩
      { x with outs := [(⟨.busy ms.pending [], a⟩ : NOut).onWrite p] } := by
  subst hg hmm
  have e : ∀ j, j ≠ PC → j ≠ OOFF → upd (upd ms.g OOFF (min (ms.g OOFF + p / 16) (ms.g OLEN))) PC pWR j = ms.g j :=
    fun j h1 h2 => by simp [upd_apply, h1, h2]
  have hoff : upd (upd ms.g OOFF (min (ms.g OOFF + p / 16) (ms.g OLEN))) PC pWR OOFF =
      min (ms.g OOFF + p / 16) (ms.g OLEN) := by simp [upd_apply, PC, OOFF]
  have hok' : okD ⟨upd (upd ms.g OOFF (min (ms.g OOFF + p / 16) (ms.g OLEN))) PC pWR, ms.m, rp, md⟩
      (rh c) (wh c') s := by
    refine ⟨(e _ (by decide) (by decide)).trans hok.1, (e _ (by decide) (by decide)).trans hok.2.1,
      (e _ (by decide) (by decide)).trans hok.2.2.1, (e _ (by decide) (by decide)).le.trans hok.2.2.2.1,
      (e _ (by decide) (by decide)).le.trans hok.2.2.2.2.1, ?_⟩
    show upd (upd ms.g OOFF (min (ms.g OOFF + p / 16) (ms.g OLEN))) PC pWR OOFF ≤
      upd (upd ms.g OOFF (min (ms.g OOFF + p / 16) (ms.g OLEN))) PC pWR OLEN
    rw [hoff, e OLEN (by decide) (by decide)]
    exact Nat.min_le_right _ _
  refine relD_of (by simp [hm]) hok' (.inr (.inr (.inr (.inr (.inl ⟨hm, by simp [upd_apply], ⟨a ++ ms.pending.take (p / 16), ?_⟩, ?_⟩)))))
  · have hpend : MS.pending ⟨upd (upd ms.g OOFF (min (ms.g OOFF + p / 16) (ms.g OLEN))) PC pWR, ms.m, rp, md⟩ =
        ms.pending.drop (p / 16) := by
      simp only [MS.pending, hoff, e OLEN (by decide) (by decide)]
      exact pending_adv _ _ _ _
    simp [Silmaril.Wasm.Component.Streams.Net.Out.onWrite, status, count, hc, hpend]
  · exact nxtRel_of hnr (e NXT (by decide) (by decide))
      (kst_of (e GST (by decide) (by decide)) (e BLEN (by decide) (by decide)) rfl) rfl rfl

/-- After a write reporting `DROPPED`: the output is dead; `DEAD`, or `CL` if the input is
already dropped. -/
theorem relD_dropped {c c' s p : Nat} {ms : MS} {g : Nat → Nat} {m : Nat → Nat}
    {rp : Option (Nat × Nat)} {x : NSt KSt} {a : List Val} {md : Mode}
    (hok : okD ms (rh c) (wh c') s) (hnr : NxtRel ms x) (hm : md = .ready) (hc : ¬ p % 16 = 0)
    (hg : g = upd ms.g PC (if ms.g NXT ≠ 0 then pDEAD else pCL)) :
    RelD (rh c) (wh c') s ⟨g, m, rp, md⟩
      { x with outs := [(⟨.busy ms.pending [], a⟩ : NOut).onWrite p] } := by
  subst hg
  have hdead : ((⟨.busy ms.pending [], a⟩ : NOut).onWrite p).st = .dead := by
    simp [Silmaril.Wasm.Component.Streams.Net.Out.onWrite, status, hc]
  have hout : outIs { x with outs := [(⟨.busy ms.pending [], a⟩ : NOut).onWrite p] } .dead :=
    ⟨_, by rw [← hdead]⟩
  have hok' := okD_pc (m := m) (rp := rp) (md := md) (v := if ms.g NXT ≠ 0 then pDEAD else pCL) hok
  rcases hnr with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, b, h2⟩
  · refine relD_of (by simp [hm]) hok' (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hm, ?_, .inl h2, hout⟩)))))))
    simp [upd_apply, h1, pDEAD]
  · refine relD_of (by simp [hm]) hok' (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hm, ?_, .inr h2, hout⟩)))))))
    simp [upd_apply, h1, pDEAD]
  · refine relD_of (by simp [hm]) hok' (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hm, ?_, ⟨b, h2⟩, .inr hout⟩)))))))
    simp [upd_apply, h1, pCL]

/-- The relation after a write's result `p`, from the globals `onWriteD` leaves. -/
theorem after_write {c c' s i code p : Nat} {ms ms' : MS} {s₂ s' : DSt} {x : NSt KSt}
    {a : List Val} (hok : okD ms (rh c) (wh c') s) (hnr : NxtRel ms x)
    (hg : s₂.g = ms.g) (hmm : s₂.m = ms.m) (hp : s₂.l i = p)
    (h : dexec (.seq (onWriteD (.l i)) yield_) FUEL s₂ = some (.ret code, s'))
    (hmd : modeOf code = some ms'.mode) (hms : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩) :
    RelD (rh c) (wh c') s ms' { x with outs := [(⟨.busy ms.pending [], a⟩ : NOut).onWrite p] } := by
  rcases dexec_seq_ret h with hr | ⟨s₃, h3, hy⟩
  · by_cases hc : s₂.l i % 16 = 0
    · cases (onWriteD_completed hc (by rw [hg]; exact hok.2.2.2.2.2) (by rw [hg]; exact hok.2.2.2.2.1) hr).1
    · cases (onWriteD_dropped hc hr).1
  obtain ⟨rfl, rfl⟩ := yield_exec hy
  have hm : ms'.mode = .ready := by simpa [modeOf_yield] using hmd.symm
  have hne : ms'.mode ≠ .exited := by rw [hm]; decide
  have hle : s₂.g OOFF ≤ s₂.g OLEN := by rw [hg]; exact hok.2.2.2.2.2
  have hcap : s₂.g OLEN ≤ CAP := by rw [hg]; exact hok.2.2.2.2.1
  rw [hms]
  by_cases hc : p % 16 = 0
  · obtain ⟨-, hg3, hm3, -, -⟩ := onWriteD_completed (by rw [hp]; exact hc) hle hcap h3
    rw [hg, hp] at hg3
    rw [hmm] at hm3
    exact relD_completed hok hnr hm hc hg3 hm3
  · obtain ⟨-, rfl⟩ := onWriteD_dropped (by rw [hp]; exact hc) h3
    exact relD_dropped hok hnr hm hc (by simp [hg])

/-! ## `WR` -/

theorem geu_eval (t : St) (a b : E) : (E.bin .geu a b).eval t = if b.eval t ≤ a.eval t then 1 else 0 := rfl

/-- The output is written: reset the buffer, continue as `NXT` says. -/
theorem wr_reset {f code : Nat} {s s' : DSt}
    (h : dexec (seqs [.gset OOFF (.c 0), .gset OLEN (.c 0), nextPC, yield_]) f s = some (.ret code, s')) :
    code = 1 ∧ s'.st = s.st ∧ s'.m = s.m ∧ s'.rp = s.rp ∧
      s'.g = upd (upd (upd s.g OOFF 0) OLEN 0) PC
        (if s.g NXT = 1 then pRD else if s.g NXT = 2 then pEOI else pCL) := by
  have hn : upd (upd s.g OOFF 0) OLEN 0 NXT = s.g NXT := by simp [upd_apply, NXT, OOFF, OLEN]
  by_cases h1 : s.g NXT = 1
  · simp [seqs, nextPC, dexec, isE, E.eval, Bin.eval, yield_, dexec.dlab, hn, h1, M32, pRD] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [h1, pRD]
  by_cases h2 : s.g NXT = 2
  · simp [seqs, nextPC, dexec, isE, E.eval, Bin.eval, yield_, dexec.dlab, hn, h2, M32, pEOI] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [h2, pEOI]
  · simp [seqs, nextPC, dexec, isE, E.eval, Bin.eval, yield_, dexec.dlab, hn, h1, h2, M32, pCL] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [h1, h2, pCL]

theorem pending_nil {ms : MS} (h : ms.g OLEN ≤ ms.g OOFF) : ms.pending = [] := by
  have := pending_len ms
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- **`WR` with the output written**: no built-in; the node is unchanged. -/
theorem wr_resume {c c' s : Nat} {ms ms' : MS} {x : NSt KSt} {g : Nat → Nat}
    (hok : okD ms (rh c) (wh c') s) (hnr : NxtRel ms x) (hout : outIs x (.idle ms.pending))
    (hle : ms.g OLEN ≤ ms.g OOFF) (hm : ms'.mode = .ready) (hms : ms' = ⟨g, ms.m, ms.rp, ms'.mode⟩)
    (hg : g = upd (upd (upd ms.g OOFF 0) OLEN 0) PC
      (if ms.g NXT = 1 then pRD else if ms.g NXT = 2 then pEOI else pCL)) :
    RelD (rh c) (wh c') s ms' x := by
  rw [pending_nil hle] at hout
  rw [hms, hm]
  subst hg
  have e : ∀ v j, j ≠ PC → j ≠ OOFF → j ≠ OLEN → upd (upd (upd ms.g OOFF 0) OLEN 0) PC v j = ms.g j :=
    fun v j h1 h2 h3 => by simp [upd_apply, h1, h2, h3]
  have hok' : ∀ v, okD ⟨upd (upd (upd ms.g OOFF 0) OLEN 0) PC v, ms.m, ms.rp, .ready⟩ (rh c) (wh c') s :=
    fun v => ⟨(e v _ (by decide) (by decide) (by decide)).trans hok.1,
      (e v _ (by decide) (by decide) (by decide)).trans hok.2.1,
      (e v _ (by decide) (by decide) (by decide)).trans hok.2.2.1,
      (e v _ (by decide) (by decide) (by decide)).le.trans hok.2.2.2.1,
      by simp [upd_apply, PC, OLEN, CAP], by simp [upd_apply, PC, OLEN, OOFF]⟩
  have hk : ∀ v, MS.kst ⟨upd (upd (upd ms.g OOFF 0) OLEN 0) PC v, ms.m, ms.rp, .ready⟩ = ms.kst :=
    fun v => kst_of (e v GST (by decide) (by decide) (by decide)) (e v BLEN (by decide) (by decide) (by decide)) rfl
  have h0 : ∀ v, upd (upd (upd ms.g OOFF 0) OLEN 0) PC v OLEN = 0 ∧
      upd (upd (upd ms.g OOFF 0) OLEN 0) PC v OOFF = 0 := fun v => by simp [upd_apply, PC, OLEN, OOFF]
  generalize hV : (if ms.g NXT = 1 then pRD else if ms.g NXT = 2 then pEOI else pCL) = V
  rcases hnr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · refine relD_of (by simp) (hok' V) (.inl ⟨rfl, by simp [upd_apply, ← hV, h1, pRD], (hk V).trans h3,
      (h0 V).1, (h0 V).2, h2, hout⟩)
  · refine relD_of (by simp) (hok' V)
      (.inr (.inr (.inr (.inl ⟨rfl, by simp [upd_apply, ← hV, h1, pEOI], (hk V).trans h3, h2, hout⟩))))
  · refine relD_of (by simp) (hok' V)
      (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, by simp [upd_apply, ← hV, h1, pCL], h2, .inl hout⟩)))))))

theorem write_args {s : DSt} (hle : s.g OOFF ≤ s.g OLEN) (hcap : s.g OLEN ≤ CAP) :
    (E.bin .add (.c OUT) (.g OOFF)).eval s.down = OUT + s.g OOFF ∧
      (E.bin .sub (.g OLEN) (.g OOFF)).eval s.down = s.g OLEN - s.g OOFF := by
  simp only [E.eval, Bin.eval, DSt.down]
  simp only [CAP, M32, OLEN, OOFF, OUT] at hcap hle ⊢
  constructor <;> omega

/-- `stream.write` of the pending output. -/
theorem write_call {rest : S} {f w : Nat} {ms : MS} {s s' : DSt} {o : Out} (hw : s.g OUTSW = w)
    (hg : s.g = ms.g) (hm : s.m = ms.m) (hle : ms.g OOFF ≤ ms.g OLEN) (hcap : ms.g OLEN ≤ CAP)
    (h : dexec (.seq (.call .streamWrite [.g OUTSW, .bin .add (.c OUT) (.g OOFF),
      .bin .sub (.g OLEN) (.g OOFF)] [LR]) rest) f s = some (o, s')) :
    ∃ st₁ res, dstep s.st (.streamWrite w ms.pending) = some (st₁, .nat res) ∧
      dexec rest f { s with st := st₁, l := upd s.l LR res } = some (o, s') := by
  obtain ⟨ha, hb⟩ := write_args (s := s) (by rw [hg]; exact hle) (by rw [hg]; exact hcap)
  have hit : (slice s.m (OUT + s.g OOFF) (s.g OLEN - s.g OOFF)).map u8v = ms.pending := by
    rw [hg, hm]; exact write_items ms
  simp only [dexec, dcallBI, List.map] at h
  rw [show (E.g OUTSW).eval s.down = w from hw, ha, hb, hit] at h
  rcases hd : dstep s.st (.streamWrite w ms.pending) with _ | ⟨st₁, res⟩
  · rw [hd] at h; cases h
  · rw [hd] at h
    rcases res with _ | v | _ | _ | _ | _
    all_goals try (simp at h; done)
    by_cases hv : v < M32
    · simp only [hv, ↓reduceIte] at h
      exact ⟨st₁, v, rfl, h⟩
    · simp [hv] at h

theorem pending_pc (g m : Nat → Nat) (rp : Option (Nat × Nat)) (md md' : Mode) (v : Nat) :
    MS.pending ⟨upd g PC v, m, rp, md⟩ = MS.pending ⟨g, m, rp, md'⟩ := by
  simp only [MS.pending, upd_pc_ne (show OLEN ≠ PC by decide), upd_pc_ne (show OOFF ≠ PC by decide)]

theorem nxt_pc {ms : MS} {x : NSt KSt} {m : Nat → Nat} {rp : Option (Nat × Nat)} {md : Mode} {v : Nat}
    (hnr : NxtRel ms x) (hm : m = ms.m) : NxtRel ⟨upd ms.g PC v, m, rp, md⟩ x :=
  nxtRel_of hnr (upd_pc_ne (g := ms.g) (v := v) (show NXT ≠ PC by decide))
    (by subst hm; exact kst_of (ms' := ⟨upd ms.g PC v, ms.m, rp, md⟩) (ms := ms) (upd_pc_ne (g := ms.g) (v := v) (show GST ≠ PC by decide)) (upd_pc_ne (g := ms.g) (v := v) (show BLEN ≠ PC by decide)) rfl)
    rfl rfl

theorem isE_LR_upd (s : DSt) (st₁ : DStore) (v : Nat) :
    (isE (.l LR) blocked).eval (DSt.down { s with st := st₁, l := upd s.l LR v }) =
      if v = blocked then 1 else 0 := by
  rw [isE_eval _ _ _ blocked_lt]
  simp [E.eval, upd_apply, DSt.down]

theorem geu_iff (t : DSt) : (E.bin .geu (.g OOFF) (.g OLEN)).eval t.down ≠ 0 ↔ t.g OLEN ≤ t.g OOFF := by
  by_cases h : t.g OLEN ≤ t.g OOFF <;> simp [E.eval, Bin.eval, DSt.down, h]

/-- **`WR`**: resume (no built-in) or `stream.write` of the pending output. -/
theorem sim_wr {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hs : s < 2 ^ 28) (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pWR)
    (hout : outIs x (.idle ms.pending)) (hnr : NxtRel ms x) (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ (NStep (node k c c') s st x st' x' ∨ (st' = st ∧ x' = x)) := by
  obtain ⟨code, s', hx, hmd, hst, hms⟩ := ready_inv hm h
  have hc : dexec dWR FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pWR, pWTR, pWTW, pRD, pEOI, inv0] using cb_at hx
  rcases dexec_ite_ret hc with ⟨hge, hA⟩ | ⟨hlt, hB⟩
  · show ∃ x', _
    have hle : ms.g OLEN ≤ ms.g OOFF := by
      have e : (E.bin .geu (.g OOFF) (.g OLEN)).eval (inv0 ms [0, 0, 0] st).down =
          if ms.g OLEN ≤ ms.g OOFF then 1 else 0 := rfl
      rw [e] at hge
      by_contra hn
      exact hge (ite_eq_right hn)
    obtain ⟨rfl, hst', hm', hrp', hg'⟩ := wr_reset hA
    have hmode : ms'.mode = .ready := by simpa [modeOf_yield] using hmd.symm
    have hms₂ : ms' = ⟨s'.g, ms.m, ms.rp, ms'.mode⟩ := hms.trans (by rw [hm', hrp']; rfl)
    exact ⟨x, wr_resume hok hnr hout hle hmode hms₂ hg', .inr ⟨hst.trans hst', rfl⟩⟩
  have hlt' : ms.g OOFF < ms.g OLEN := Nat.lt_of_not_le (fun hn => ((geu_iff _).mpr hn) hlt)
  obtain ⟨st₁, res, hd, hR⟩ := write_call (ms := ms) hok.2.1 rfl rfl hok.2.2.2.2.2 hok.2.2.2.2.1 hB
  have hst₁ : s'.st = st₁ := noCall_st (by simp [noCall, noCall_onWriteD, yield_]) hR
  obtain ⟨a, ha⟩ := hout
  have hq : 0 < ms.pending.length := by rw [pending_len]; omega
  have hd' : dstep st (.streamWrite (wh c') (ms.pending.take ms.pending.length)) = some (st₁, .nat res) := by
    rw [List.take_length]; exact hd
  have hstep : NStep (node k c c') s st x st₁
      { x with outs := (x.outs.set 0 (Silmaril.Wasm.Component.Streams.Net.Out.afterWrite ms.pending [] a res)) } := by
    have h₀ := NStep.write (N := node k c c') (ws := s) (j := 0) (x := x) (q := ms.pending) (a := a)
      rfl (by simp [ha]) hq le_rfl hd'
    rwa [List.take_length, List.drop_length] at h₀
  by_cases hb : res = blocked
  · show ∃ x', _
    subst hb
    rw [dexec_ite, isE_LR_upd, ite_eq_left rfl, ite_eq_left (show (1 : Nat) ≠ 0 by decide)] at hR
    obtain ⟨hcd, rfl⟩ := wait_exec (by exact hok.2.2.1) hs (by decide) (dlab_ret hR)
    have hm' : ms'.mode = .waiting s := by
      rw [hcd, modeOf_wait] at hmd
      exact (Option.some.inj hmd).symm
    refine ⟨_, ?_, .inl (by rw [hst, hst₁]; exact hstep)⟩
    rw [hms]
    refine relD_of (not_wait_exited hm') (okD_pc hok)
      (.inr (.inr (.inr (.inr (.inr (.inl ⟨hm', by simp [upd_apply, pWTW], ⟨a, ?_⟩, ?_, ?_⟩))))))
    · simp [ha, Silmaril.Wasm.Component.Streams.Net.Out.afterWrite, pending_pc _ _ _ _ ms.mode, inv0]
    · exact nxt_pc hnr rfl
    · rw [pending_pc _ _ _ _ ms.mode]
      exact List.ne_nil_of_length_pos hq
  · rw [dexec_ite, isE_LR_upd, ite_eq_right hb, ite_eq_right (show ¬ (0 : Nat) ≠ 0 by decide)] at hR
    refine ⟨_, after_write (i := LR) (p := res) (a := a) hok hnr rfl rfl (by simp [upd_apply]) (dlab_ret hR) hmd hms, .inl ?_⟩
    rw [hst, hst₁]
    simp only [ha, Silmaril.Wasm.Component.Streams.Net.Out.afterWrite, hb, ite_false, List.set_cons_zero] at hstep
    exact hstep

/-! ## `WTW` -/

theorem deliver_m_nil {e : Event} {ms : MS} (h : e.items = []) : (deliver e ms).m = ms.m := by
  unfold deliver
  split
  · split
    · funext a; simp [writeBytes, h]
    · rfl
  · rfl

/-- `NXT := 2; return WAIT | s << 4`. -/
theorem nxtWait_exec {f code s : Nat} {t s' : DSt} (hws : t.g WS = s) (hs : s < 2 ^ 28)
    (h : dexec (.seq (.gset NXT (.c 2)) (.ret waitCode)) f t = some (.ret code, s')) :
    code = 2 + 16 * s ∧ s' = { t with g := upd t.g NXT 2 } := by
  simp only [dexec, Option.some.injEq, Prod.mk.injEq, Out.ret.injEq] at h
  obtain ⟨hcode, rfl⟩ := h
  refine ⟨?_, by simp [E.eval, M32]⟩
  rw [← hcode]
  apply waitCode_evalD _ _ hs
  have hk : ∀ v, upd t.g NXT v WS = t.g WS := fun v => by simp [upd_apply, NXT, WS]
  exact (hk ((E.c 2).eval t.down)).trans hws

/-- `DROPPED` on the idle input while a write is pending: `NXT := 2`, wait again. -/
theorem wtw_ended {k : KM} {c c' s p : Nat} {ms ms' : MS} {x : NSt KSt} {a : List Val}
    {items : List Val} (hok : okD ms (rh c) (wh c') s) (hnr : NxtRel ms x) (hpc : ms.g PC = pWTW)
    (hm' : ms'.mode = .waiting s) (hn1 : ms.g NXT = 1) (hdr : p % 16 ≠ 0) (hnil : items = [])
    (ha : x.outs = [⟨.busy ms.pending [], a⟩]) (hne : ms.pending ≠ [])
    (hg : ms'.g = upd ms.g NXT 2) (hmm : ms'.m = ms.m) :
    RelD (rh c) (wh c') s ms' (x.onRead (node k c c').T p items) := by
  subst hnil
  have e : ∀ j, j ≠ NXT → ms'.g j = ms.g j := fun j hj => by rw [hg]; simp [upd_apply, hj]
  have hok' : okD ms' (rh c) (wh c') s :=
    ⟨(e _ (by decide)).trans hok.1, (e _ (by decide)).trans hok.2.1, (e _ (by decide)).trans hok.2.2.1,
      (e _ (by decide)).le.trans hok.2.2.2.1, (e _ (by decide)).le.trans hok.2.2.2.2.1,
      by rw [e _ (by decide), e _ (by decide)]; exact hok.2.2.2.2.2⟩
  have hpend : ms'.pending = ms.pending := by
    simp only [MS.pending, e OLEN (by decide), e OOFF (by decide), hmm]
  have hkst : ms'.kst = x.s := by
    rcases hnr with ⟨-, -, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (kst_of (e GST (by decide)) (e BLEN (by decide)) hmm).trans h3
    · rw [hn1] at h1; cases h1
    · rw [hn1] at h1; cases h1
  refine relD_of (not_wait_exited hm') hok' (.inr (.inr (.inr (.inr (.inr (.inl
    ⟨hm', (e _ (by decide)).trans hpc, ⟨a, ?_⟩, .inr (.inl ⟨by rw [hg]; simp [upd_apply], ?_, ?_⟩), ?_⟩))))))
  · simp [NSt.onRead, ha, hpend, Silmaril.Wasm.Component.Streams.Net.Out.push, Tr.feed]
  · simp [NSt.onRead, status, hdr]
  · simp [NSt.onRead, hkst, Tr.feed]
  · rw [hpend]; exact hne

/-- **`WTW`**: the write's event, or `DROPPED` on the idle input (the input has ended). -/
theorem sim_wtw {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hs : s < 2 ^ 28) (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .waiting s)
    (hpc : ms.g PC = pWTW) (hout : outIs x (.busy ms.pending [])) (hnr : NxtRel ms x)
    (hne : ms.pending ≠ []) (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ NStep (node k c c') s st x st' x' := by
  obtain ⟨hd, st₁, e, hw, hwf, code, s', hx, hmd, hst, hms⟩ := event_inv hm h
  have hg1 : (deliver e ms).g = ms.g := deliver_g e ms
  have hc : dexec dWTW FUEL (inv0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.ret code, s') := by
    simpa [inv0, hg1, hpc, caseOf, pWTR, pWTW] using cb_at hx
  have hst₁ : s'.st = st₁ := noCall_st (by simp [dWTW, noCall, noCall_onWriteD, yield_]) hc
  obtain ⟨a, ha⟩ := hout
  have hidx := dwait_index hw
  rcases dexec_ite_ret hc with ⟨hev, hA⟩ | ⟨-, hB⟩
  · show ∃ x', _
    obtain ⟨h0', h1'⟩ := (evOut_iff _).mp hev
    have hcode : e.code = .streamWrite := code_three h0'
    have hie : e.index = wh c' := by rw [← hok.2.1, ← hg1]; exact h1'
    refine ⟨_, after_write (i := 2) (p := e.payload) (a := a) hok hnr hg1
      (by simp [deliver_write hcode, inv0]) rfl hA hmd hms, ?_⟩
    rw [hst, hst₁]
    have := NStep.waitOut (N := node k c c') (ws := s) (j := 0) (x := x) (o := ⟨.busy ms.pending [], a⟩)
      rfl (by simp [ha]) (by rw [← hidx, hie] at hw; exact hw)
    simp only [ha, List.set_cons_zero] at this
    exact this
  rcases dexec_ite_ret hB with ⟨hev, hC⟩ | ⟨-, hD⟩
  · show ∃ x', _
    obtain ⟨hev₁, hev₂⟩ := (andE_iff _ _ _).mp hev
    obtain ⟨hev₃, hev₄⟩ := (andE_iff _ _ _).mp hev₁
    obtain ⟨h0', h1'⟩ := (evIn_iff _).mp hev₃
    obtain ⟨hdr, hz⟩ := (evDropped0_iff _).mp hev₄
    have hn1 : ms.g NXT = 1 := by
      rw [isE_eval _ _ _ (by decide)] at hev₂
      by_contra hn; simp [E.eval, inv0, hg1, hn] at hev₂
    have hcode : e.code = .streamRead := code_two h0'
    have hie : e.index = rh c := by rw [← hok.1, ← hg1]; exact h1'
    have hnil : e.items = [] := by
      have := (wfD_inv hwf).2 hcode
      have hz' : e.payload / 16 = 0 := hz
      exact List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨hcd, rfl⟩ := nxtWait_exec (by simp only [inv0]; rw [hg1]; exact hok.2.2.1) hs hC
    rw [hcd, modeOf_wait] at hmd
    have hm' : ms'.mode = .waiting s := (Option.some.inj hmd).symm
    refine ⟨x.onRead (node k c c').T e.payload e.items, ?_, ?_⟩
    · refine wtw_ended hok hnr hpc hm' hn1 hdr hnil ha hne ?_ ?_
      · rw [hms]; simp [inv0, hg1]
      · rw [hms]; simp [inv0, deliver_m_nil hnil]
    · rw [hst, hst₁]
      exact NStep.waitIn rfl (by rw [← hidx, hie] at hw; exact hw)
  · simp [dexec] at hD

end Silmaril.Proofs.Wasm.JcoTool.KDrop
