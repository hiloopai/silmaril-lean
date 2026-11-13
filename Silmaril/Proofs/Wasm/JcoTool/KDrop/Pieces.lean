module

public import Silmaril.Proofs.Wasm.JcoTool.KDrop.Exec

/-!
# The pieces of the drop-aware callback

* `cb_case`: the callback runs the case of its `pc`.
* `onReadD_sound`: after a read's result (`COMPLETED` or `DROPPED`, with its count of bytes in
  the input buffer), the bytes were fed to the kernel, `NXT` records the status, `pc = WR`.
* `onWriteD_sound`: after a write's result, the offset advanced, or the dead output's next state.
* `flushD_sound`: `KCore.flushOut_sound` for `dexec`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KDrop

open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

/-! ## Dispatch -/

theorem pcIs_evalD (s : DSt) {n : Nat} (hn : n ≤ 8) :
    (pcIs n).eval s.down = if s.g PC = n then 1 else 0 := by
  have h : n % M32 = n := Nat.mod_eq_of_lt (by simp [M32]; omega)
  simp [pcIs, E.eval, Bin.eval, h, DSt.down]

theorem pc_of_eval {s : DSt} {n : Nat} (hn : n ≤ 8) (hc : (pcIs n).eval s.down ≠ 0) :
    s.g PC = n := by
  rw [pcIs_evalD s hn] at hc
  by_contra hne
  simp [hne] at hc

/-- **Dispatch**: a callback run that returned ran the case of `pc`. -/
theorem cb_case {k : KM} {N f : Nat} {s s' : DSt} {v : Nat}
    (h : dexec (callbackD k N) f s = some (.ret v, s')) :
    (s.g PC = pWTR ∧ dexec (dWTR k) f s = some (.ret v, s')) ∨
    (s.g PC = pWTW ∧ dexec dWTW f s = some (.ret v, s')) ∨
    (s.g PC = pRD ∧ dexec (dRD k N) f s = some (.ret v, s')) ∨
    (s.g PC = pEOI ∧ dexec (dEOI k) f s = some (.ret v, s')) ∨
    (s.g PC = pWR ∧ dexec dWR f s = some (.ret v, s')) ∨
    (s.g PC = pCL ∧ dexec dCL f s = some (.ret v, s')) ∨
    (s.g PC = pDEAD ∧ dexec dDEAD f s = some (.ret v, s')) ∨
    (s.g PC = pWTRD ∧ dexec dWTRD f s = some (.ret v, s')) := by
  have e : ∀ {n : Nat}, n ≤ 8 → (pcIs n).eval s.down ≠ 0 → s.g PC = n := pc_of_eval
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inl ⟨e (by decide) c, h⟩
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inl ⟨e (by decide) c, h⟩)
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inl ⟨e (by decide) c, h⟩))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inr (.inl ⟨e (by decide) c, h⟩)))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inr (.inr (.inl ⟨e (by decide) c, h⟩))))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨e (by decide) c, h⟩)))))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e (by decide) c, h⟩))))))
  rcases dexec_ite_ret h with ⟨c, h⟩ | ⟨-, h⟩
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨e (by decide) c, h⟩))))))
  · cases h

/-- What an invocation that returned tells about the run of its body. -/
theorem dinvoke_inv {body : S} {ps : List Nat} {st st' : DStore} {ms ms' : MS}
    (h : dinvoke body ps st ms = some (st', ms')) :
    ∃ code s', dexec body FUEL ⟨ms.g, ms.m, locals ps, st, ms.rp⟩ = some (.ret code, s') ∧
      modeOf code = some ms'.mode ∧ st' = s'.st ∧ ms'.g = s'.g ∧ ms'.m = s'.m ∧ ms'.rp = s'.rp := by
  unfold dinvoke at h
  split at h
  · rename_i code s' hx
    cases hm : modeOf code with
    | none => rw [hm] at h; cases h
    | some md =>
      rw [hm] at h
      cases h
      exact ⟨code, s', hx, hm, rfl, rfl, rfl, rfl⟩
  · cases h

/-! ## After a read -/

/-- The value of `nxtOf p`: `1` on `COMPLETED`, `2` otherwise. -/
theorem nxtOf_eval (p : E) (t : St) :
    (nxtOf p).eval t = if p.eval t % 16 = 0 then 1 else 2 := by
  by_cases h : p.eval t % 16 = 0 <;> simp [nxtOf, E.eval, Bin.eval, h, M32]

/-- The state before the feed loop. -/
def sN (t : St) (nx n : Nat) : St := { t with g := upd t.g NXT nx, l := upd (upd t.l LN n) LI 0 }

theorem onReadD_pre (k : KM) (f i : Nat) (t : St) :
    exec (onReadD k (.l i)) f t = exec (.seq (feedLoop k) (.gset PC (.c pWR))) f
      (sN t (if t.l i % 16 = 0 then 1 else 2) (t.l i / 16)) := by
  have h1 : (nxtOf (.l i)).eval t = if t.l i % 16 = 0 then 1 else 2 := nxtOf_eval _ t
  simp only [onReadD, seqs, exec, h1]
  simp [E.eval, Bin.eval, sN, M32]

/-- The feed loop's invariant at the start. -/
theorem linv_sN {t : St} {ks : KSt} {bs : List Nat} (nx : Nat) (hK : KS t.g t.m ks)
    (h0 : t.g OLEN = 0) (hin : slice t.m IN bs.length = bs) (hlen : bs.length ≤ 256) :
    LInv (sN t nx bs.length) ks [] bs 0 :=
  ⟨(hK.krep h0).upd_g nx (by decide) (by decide) (by decide), by simp [sN, upd_apply],
    by simp [sN, upd_apply, LN, LI], hin, Nat.zero_le _, hlen⟩

/-- What a read's result leaves: the bytes fed, the output pending from offset `0`, `NXT`. -/
structure RdPost (s s' : St) (ks : KSt) (out : List Nat) (nx : Nat) : Prop where
  pc : s'.g PC = pWR
  nxt : s'.g NXT = nx
  rep : KRep s'.g s'.m ks out
  g : ∀ j, j ≠ GST → j ≠ BLEN → j ≠ OLEN → j ≠ PC → j ≠ NXT → s'.g j = s.g j
  rp : s'.rp = s.rp

theorem rdPost_of {t t₂ : St} {ks : KSt} {out : List Nat} {nx n : Nat} (hR : KRep t₂.g t₂.m ks out)
    (hF : FrameL (sN t nx n) t₂) :
    RdPost t { t₂ with g := upd t₂.g PC pWR } ks out nx := by
  have hg : ∀ j, j ≠ GST → j ≠ BLEN → j ≠ OLEN → t₂.g j = upd t.g NXT nx j := hF.g
  refine ⟨by simp [upd_apply], ?_, hR.upd_g _ (by decide) (by decide) (by decide), ?_, hF.rp⟩
  · show upd t₂.g PC pWR NXT = nx
    rw [upd_apply, ite_eq_right (by decide), hg NXT (by decide) (by decide) (by decide)]
    simp [upd_apply]
  · intro j h1 h2 h3 h4 h5
    show upd t₂.g PC pWR j = t.g j
    rw [upd_apply, ite_eq_right h4, hg j h1 h2 h3]
    simp [upd_apply, h5]

/-- **After a read** whose result is in local `i`: the `count` bytes of the input buffer fed to
the kernel (stopping when it is done), `NXT` by the status. -/
theorem onRead_exec {k : KM} {f i : Nat} {t t' : St} {o : Out} {ks : KSt} {bs : List Nat}
    (hK : KS t.g t.m ks) (h0 : t.g OLEN = 0)
    (hin : slice t.m IN bs.length = bs) (hlen : bs.length ≤ 256) (hcnt : t.l i / 16 = bs.length)
    (h : exec (onReadD k (.l i)) f t = some (o, t')) :
    o = .norm ∧ RdPost t t' (k.tr.feed ks bs).1 (k.tr.feed ks bs).2
      (if t.l i % 16 = 0 then 1 else 2) := by
  rw [onReadD_pre k f i t, hcnt] at h
  generalize hnx : (if t.l i % 16 = 0 then 1 else 2) = nx at h
  have hI := linv_sN nx hK h0 hin hlen
  cases h₁ : exec (feedLoop k) f (sN t nx bs.length) with
  | none => rw [exec_seq, h₁] at h; cases h
  | some r =>
    obtain ⟨o₁, t₂⟩ := r
    obtain ⟨rfl, -, hR₂, hF₂⟩ := feed_sound hI h₁
    rw [exec_seq_norm h₁] at h
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hR : KRep t₂.g t₂.m (k.tr.feed ks bs).1 (k.tr.feed ks bs).2 := by simpa using hR₂
    exact ⟨rfl, by simpa [E.eval, M32, pWR] using rdPost_of hR hF₂⟩

/-- `onRead_exec` for `dexec`: the store is not touched. -/
theorem onReadD_sound {k : KM} {f i : Nat} {s s' : DSt} {o : Out} {ks : KSt} {bs : List Nat}
    (hK : KS s.g s.m ks) (h0 : s.g OLEN = 0)
    (hin : slice s.m IN bs.length = bs) (hlen : bs.length ≤ 256) (hcnt : s.l i / 16 = bs.length)
    (h : dexec (onReadD k (.l i)) f s = some (o, s')) :
    o = .norm ∧ s'.st = s.st ∧ RdPost s.down s'.down (k.tr.feed ks bs).1 (k.tr.feed ks bs).2
      (if s.l i % 16 = 0 then 1 else 2) := by
  rw [dexec_down (noCall_onReadD k _)] at h
  obtain ⟨⟨o', t'⟩, he, hx⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨ho, hP⟩ := onRead_exec (t := s.down) hK h0 hin hlen hcnt he
  exact ⟨ho, rfl, ⟨hP.pc, hP.nxt, hP.rep, hP.g, hP.rp⟩⟩

/-! ## After a write -/

/-- The globals after a write's result `v`: the offset advanced by the count (at most to the
end) and `pc = WR`; or, on `DROPPED`, `DEAD` (input still open, `NXT ≠ 0`) or `CL`. -/
def wrGD (g : Nat → Nat) (v : Nat) : Nat → Nat :=
  if v % 16 = 0 then upd (upd g OOFF (min (g OOFF + v / 16) (g OLEN))) PC pWR
  else upd g PC (if g NXT ≠ 0 then pDEAD else pCL)

@[simp] theorem down_g (s : DSt) : s.down.g = s.g := rfl
@[simp] theorem down_m (s : DSt) : s.down.m = s.m := rfl
@[simp] theorem down_l (s : DSt) : s.down.l = s.l := rfl
@[simp] theorem down_rp (s : DSt) : s.down.rp = s.rp := rfl

theorem onWriteD_dropped {f i : Nat} {s s' : DSt} {o : Out} (hc : s.l i % 16 ≠ 0)
    (h : dexec (onWriteD (.l i)) f s = some (o, s')) :
    o = .norm ∧ s' = { s with g := upd s.g PC (if s.g NXT ≠ 0 then pDEAD else pCL) } := by
  have hc' : (E.bin .remu (.l i) (.c 16)).eval s.down ≠ 0 := by simpa [E.eval, Bin.eval, M32] using hc
  rw [onWriteD, dexec_ite, ite_eq_left hc', dexec_ite] at h
  by_cases hn : s.g NXT = 0
  · have hn' : (E.g NXT).eval s.down = 0 := by simpa [E.eval] using hn
    rw [ite_eq_right (by simpa using hn')] at h
    simp only [dexec, dexec.dlab, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hn, pCL, E.eval, M32]
  · have hn' : (E.g NXT).eval s.down ≠ 0 := by simpa [E.eval] using hn
    rw [ite_eq_left hn'] at h
    simp only [dexec, dexec.dlab, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hn, pDEAD, E.eval, M32]

/-- The state after `LN := count`. -/
def sW (s : DSt) (i : Nat) : DSt := { s with l := upd s.l LN (s.l i / 16) }

theorem geu_evalW {s : DSt} {i : Nat} (hle : s.g OOFF ≤ s.g OLEN) (hcap : s.g OLEN ≤ CAP) :
    (E.bin .geu (.l LN) (.bin .sub (.g OLEN) (.g OOFF))).eval (sW s i).down =
      if s.g OLEN - s.g OOFF ≤ s.l i / 16 then 1 else 0 := by
  have hsub : (s.g OLEN + (M32 - s.g OOFF % M32)) % M32 = s.g OLEN - s.g OOFF := by
    simp only [CAP, M32, OLEN, OOFF] at hcap hle ⊢
    omega
  simp [E.eval, Bin.eval, sW, upd_apply, hsub]

/-- The offset after a completed write of `count` bytes. -/
theorem advance_exec {f i : Nat} {s : DSt} (hle : s.g OOFF ≤ s.g OLEN) (hcap : s.g OLEN ≤ CAP) :
    dexec (.ite (.bin .geu (.l LN) (.bin .sub (.g OLEN) (.g OOFF))) (.gset OOFF (.g OLEN))
        (.gset OOFF (.bin .add (.g OOFF) (.l LN)))) f (sW s i) =
      some (.norm, { sW s i with g := upd s.g OOFF (min (s.g OOFF + s.l i / 16) (s.g OLEN)) }) := by
  rw [dexec_ite, geu_evalW hle hcap]
  have hl : upd s.l LN (s.l i / 16) LN = s.l i / 16 := by simp [upd_apply]
  by_cases hge : s.g OLEN - s.g OOFF ≤ s.l i / 16
  · have hmin : min (s.g OOFF + s.l i / 16) (s.g OLEN) = s.g OLEN := by omega
    simp [hge, dexec, dexec.dlab, E.eval, sW, hmin]
  · have hmin : min (s.g OOFF + s.l i / 16) (s.g OLEN) = s.g OOFF + s.l i / 16 := by omega
    have hsm : (s.g OOFF + s.l i / 16) % M32 = s.g OOFF + s.l i / 16 := by
      simp only [CAP, M32, OLEN, OOFF] at hcap hle hmin ⊢
      omega
    simp [hge, dexec, dexec.dlab, E.eval, Bin.eval, sW, hl, hsm, hmin]

theorem onWriteD_completed {f i : Nat} {s s' : DSt} {o : Out} (hc : s.l i % 16 = 0)
    (hle : s.g OOFF ≤ s.g OLEN) (hcap : s.g OLEN ≤ CAP)
    (h : dexec (onWriteD (.l i)) f s = some (o, s')) :
    o = .norm ∧ s'.g = upd (upd s.g OOFF (min (s.g OOFF + s.l i / 16) (s.g OLEN))) PC pWR ∧
      s'.m = s.m ∧ s'.st = s.st ∧ s'.rp = s.rp := by
  have hc' : ¬ (E.bin .remu (.l i) (.c 16)).eval s.down ≠ 0 := by simpa [E.eval, Bin.eval, M32] using hc
  have hpre : dexec (.lset LN (.bin .divu (.l i) (.c 16))) f s = some (.norm, sW s i) := by
    simp [dexec, E.eval, Bin.eval, sW, M32]
  rw [onWriteD, dexec_ite, ite_eq_right hc'] at h
  simp only [seqs] at h
  rw [dexec_seq_norm hpre, dexec_seq_norm (advance_exec hle hcap)] at h
  simp only [dexec, dexec.dlab, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [E.eval, M32, pWR, sW]

/-! ## The flush -/

/-- `flushOut_sound` for `dexec`. -/
theorem flushD_sound {k : KM} {f : Nat} {s s' : DSt} {o : Out} {ks : KSt} (hK : KS s.g s.m ks)
    (h : dexec (flushOut k) f s = some (o, s')) :
    o = .norm ∧ s'.st = s.st ∧ WrPost s.down s'.down (k.flush.exec 0 ks).1 (k.flush.exec 0 ks).2 0 := by
  rw [dexec_down (noCall_flushOut k)] at h
  obtain ⟨⟨o', t'⟩, he, hx⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨ho, hW⟩ := flushOut_sound hK he
  exact ⟨ho, rfl, ⟨hW.pc, hW.nxt, hW.off, hW.rep, hW.hs, rfl, hW.rp⟩⟩

end Silmaril.Proofs.Wasm.JcoTool.KDrop
