module

public import Silmaril.Proofs.Wasm.JcoTool.KCore.Feed

/-!
# The callback simulates `Proc.tStep`: the toolkit and the pieces of the callback

(Restyled to the Isar conventions of `docs/projects/wasm-components.md` when moved out of `Silmaril/Raw`; the statements are
restated in `Silmaril.Wasm.JcoTool.KCore.Thms`.)

* Dispatch: the callback runs the case of the current `pc` (`exec_case_miss`, `exec_case_hit`).
* `invoke_inv`: what an invocation that returned tells about the body's run.
* `flushOut_sound`: the flush leaves the kernel's flush output in the empty output buffer.
* `onRead_sound`: after a read's result, the input ended (`EOI`) or the bytes were fed.
* `onWrite_sound`: after a write's result, the written prefix is dropped (or `FAULT`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCore

open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

/-! ## Dispatch -/

theorem pcIs_eval (s : St) {n : Nat} (hn : n ≤ 7) : (pcIs n).eval s = if s.g PC = n then 1 else 0 := by
  simp [pcIs, E.eval, Bin.eval, pc_mod hn]

theorem exec_case_miss {n : Nat} {A rest : S} {f : Nat} {s : St} (hn : n ≤ 7) (h : s.g PC ≠ n) :
    exec (.seq (case_ n A) rest) f s = exec rest f s := by
  simp [case_, exec, pcIs_eval s hn, h, lab]

/-- A case whose body returns: the callback returns what it returns. -/
theorem exec_case_ret {n : Nat} {A rest : S} {f : Nat} {s s' : St} {v : Nat} (hn : n ≤ 7)
    (h : s.g PC = n) (hA : exec A f s = some (.ret v, s')) :
    exec (.seq (case_ n A) rest) f s = some (.ret v, s') := by
  simp [case_, exec, pcIs_eval s hn, h, hA, lab]

theorem exec_case_none {n : Nat} {A rest : S} {f : Nat} {s : St} (hn : n ≤ 7)
    (h : s.g PC = n) (hA : exec A f s = none) : exec (.seq (case_ n A) rest) f s = none := by
  simp [case_, exec, pcIs_eval s hn, h, hA, lab]

theorem callback_eq (k : KM) (N : Nat) : callback k N =
    .seq (case_ pWTR (cbWTR k)) (.seq (case_ pWTW cbWTW) (.seq (case_ pRD (cbRD k N))
      (.seq (case_ pEOI (cbEOI k)) (.seq (case_ pWR cbWR) (.seq (case_ pCL cbCL) .unreachable))))) := rfl

/-- The case of `pc`, when its body can only return or trap, gives the callback's result. -/
theorem exec_case_hit {n : Nat} {A rest : S} {f : Nat} {s : St} (hn : n ≤ 7) (h : s.g PC = n)
    (hr : ∀ r, exec A f s = some r → ∃ v s', r = (.ret v, s')) :
    exec (.seq (case_ n A) rest) f s = exec A f s := by
  cases hx : exec A f s with
  | none => exact exec_case_none hn h hx
  | some r =>
    obtain ⟨v, s', hv⟩ := hr r hx
    have hx' : exec A f s = some (.ret v, s') := by rw [hx, hv]
    rw [exec_case_ret hn h hx', hv]

theorem miss {n m : Nat} {A rest : S} {f : Nat} {s : St} (hm : m ≤ 7) (h : s.g PC = n)
    (hne : n ≠ m) : exec (.seq (case_ m A) rest) f s = exec rest f s :=
  exec_case_miss hm (by rw [h]; exact hne)

/-- **Dispatch**: the callback runs the case of `pc`, when that case can only return or trap. -/
theorem exec_callback {k : KM} {N f : Nat} {s : St} {A : S} {n : Nat}
    (hA : (n = pWTR ∧ A = cbWTR k) ∨ (n = pWTW ∧ A = cbWTW) ∨ (n = pRD ∧ A = cbRD k N) ∨
      (n = pEOI ∧ A = cbEOI k) ∨ (n = pWR ∧ A = cbWR) ∨ (n = pCL ∧ A = cbCL))
    (h : s.g PC = n) (hr : ∀ r, exec A f s = some r → ∃ v s', r = (.ret v, s')) :
    exec (callback k N) f s = exec A f s := by
  rw [callback_eq]
  rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact exec_case_hit (by decide) h hr
  · rw [miss (by decide) h (by decide)]; exact exec_case_hit (by decide) h hr
  · rw [miss (by decide) h (by decide), miss (by decide) h (by decide)]
    exact exec_case_hit (by decide) h hr
  · rw [miss (by decide) h (by decide), miss (by decide) h (by decide), miss (by decide) h (by decide)]
    exact exec_case_hit (by decide) h hr
  · rw [miss (by decide) h (by decide), miss (by decide) h (by decide), miss (by decide) h (by decide),
      miss (by decide) h (by decide)]
    exact exec_case_hit (by decide) h hr
  · rw [miss (by decide) h (by decide), miss (by decide) h (by decide), miss (by decide) h (by decide),
      miss (by decide) h (by decide), miss (by decide) h (by decide)]
    exact exec_case_hit (by decide) h hr

/-- With `pc` none of the cases, the callback traps. -/
theorem exec_callback_other {k : KM} {N f : Nat} {s : St} (h : s.g PC = pFAULT) :
    exec (callback k N) f s = none := by
  rw [callback_eq]
  repeat rw [exec_case_miss (by decide) (by rw [h]; decide)]
  rfl

/-! ## Invocations -/

/-- The state of an invocation of a body with the parameters `ps`. -/
def st0 (ms : MS) (ps : List Nat) (st : Store) : St := ⟨ms.g, ms.m, locals ps, st, ms.rp, 0⟩

theorem invoke_inv {body : S} {ps : List Nat} {st st' : Store} {ms ms' : MS}
    (h : invoke body ps st ms = some (st', ms')) :
    ∃ code s', exec body FUEL (st0 ms ps st) = some (.ret code, s') ∧ modeOf code = some ms'.mode ∧
      st' = s'.st ∧ ms'.g = s'.g ∧ ms'.m = s'.m ∧ ms'.rp = s'.rp := by
  unfold invoke at h
  split at h
  · rename_i code s' hx
    cases hm : modeOf code with
    | none => rw [hm] at h; cases h
    | some md =>
      rw [hm] at h
      cases h
      exact ⟨code, s', hx, hm, rfl, rfl, rfl, rfl⟩
  · cases h

theorem modeOf_zero : modeOf 0 = some .exited := rfl
theorem modeOf_one : modeOf 1 = some .ready := rfl
theorem modeOf_wait : modeOf 82 = some (.waiting 5) := rfl

theorem waitCode_eval (s : St) (h : s.g WS = 5) : waitCode.eval s = 82 := by
  simp [waitCode, E.eval, Bin.eval, h, M32]

/-! ## The flush -/

attribute [local simp] PC GST BLEN OLEN OOFF NXT INSR OUTSW WS LI LB LR LN pRD pWTR pEOI pWR pWTW
  pCL pFIN pFAULT

/-- The kernel state `ks` in globals and memory. -/
structure KS (g m : Nat → Nat) (ks : KSt) : Prop where
  st : g GST = ks.st
  blen : g BLEN = ks.buf.length
  bufs : slice m KBUF ks.buf.length = ks.buf
  bcap : ks.buf.length ≤ CAP

theorem KS.krep {g m : Nat → Nat} {ks : KSt} (h : KS g m ks) (h0 : g OLEN = 0) : KRep g m ks [] :=
  ⟨h.st, h.blen, h.bufs, h0, rfl, h.bcap, by simp [CAP]⟩

theorem KRep.ks {g m : Nat → Nat} {ks : KSt} {out : List Nat} (h : KRep g m ks out) : KS g m ks :=
  ⟨h.st, h.blen, h.bufs, h.bcap⟩

/-- The globals `INSR`, `OUTSW`, `WS` and `NXT`, `PC`, `OOFF` are not the kernel's. -/
theorem frame_hs {s s' : St} (h : ∀ i, i ≠ GST → i ≠ BLEN → i ≠ OLEN → s'.g i = s.g i) :
    s'.g INSR = s.g INSR ∧ s'.g OUTSW = s.g OUTSW ∧ s'.g WS = s.g WS ∧ s'.g PC = s.g PC ∧
      s'.g NXT = s.g NXT ∧ s'.g OOFF = s.g OOFF :=
  ⟨h _ (by decide) (by decide) (by decide), h _ (by decide) (by decide) (by decide),
    h _ (by decide) (by decide) (by decide), h _ (by decide) (by decide) (by decide),
    h _ (by decide) (by decide) (by decide), h _ (by decide) (by decide) (by decide)⟩

/-- What a write-out step (`flushOut`, or the feed of `onRead`) establishes: the output `ys`
pending from offset `0`, the next state's flag, `pc = WR`, the handles and the store kept. -/
structure WrPost (s s' : St) (ks : KSt) (ys : List Nat) (nxt : Nat) : Prop where
  pc : s'.g PC = pWR
  nxt : s'.g NXT = nxt
  off : s'.g OOFF = 0
  rep : KRep s'.g s'.m ks ys
  hs : s'.g INSR = s.g INSR ∧ s'.g OUTSW = s.g OUTSW ∧ s'.g WS = s.g WS
  st : s'.st = s.st
  rp : s'.rp = s.rp

/-- The state after `OOFF := 0`, `OLEN := 0`, `LB := 0`. -/
def sF (s : St) : St := { s with g := upd (upd s.g OOFF 0) OLEN 0, l := upd s.l LB 0 }

theorem sF_rep {s : St} {ks : KSt} (hK : KS s.g s.m ks) : KRep (sF s).g (sF s).m ks [] := by
  refine KS.krep ⟨?_, ?_, hK.bufs, hK.bcap⟩ ?_
  · simpa [sF, upd_apply, GST, OOFF, OLEN] using hK.st
  · simpa [sF, upd_apply, BLEN, OOFF, OLEN] using hK.blen
  · simp [sF, upd_apply]

theorem flushOut_eq (k : KM) (f : Nat) (s : St) : exec (flushOut k) f s =
    exec (seqs [cS k.flush, .gset NXT (.c 0), .gset PC (.c pWR)]) f (sF s) := by
  simp [flushOut, seqs, exec, E.eval, sF]

/-- The two `global.set`s ending the flush keep what the flush established. -/
theorem wrPost_flush {s s₄ : St} {ks : KSt} {ys : List Nat} (hR : KRep s₄.g s₄.m ks ys)
    (hF : Frame (sF s) s₄) : WrPost s { s₄ with g := upd (upd s₄.g NXT 0) PC pWR } ks ys 0 := by
  have hk := frame_hs hF.g
  have hoff : s₄.g OOFF = 0 := by rw [hk.2.2.2.2.2]; simp [sF, upd_apply]
  have hs : s₄.g INSR = s.g INSR ∧ s₄.g OUTSW = s.g OUTSW ∧ s₄.g WS = s.g WS := by
    rw [hk.1, hk.2.1, hk.2.2.1]
    simp [sF, upd_apply]
  refine ⟨by simp [upd_apply], by simp [upd_apply], ?_, ?_, ?_, hF.st, hF.rp⟩
  · simpa [upd_apply] using hoff
  · exact (hR.upd_g _ (by decide) (by decide) (by decide)).upd_g _ (by decide) (by decide) (by decide)
  · simpa [upd_apply] using hs

/-- **The flush**: the kernel's flush output is pending, and the transformer closes after it. -/
theorem flushOut_sound {k : KM} {f : Nat} {s s' : St} {o : Out} {ks : KSt} (hK : KS s.g s.m ks)
    (h : exec (flushOut k) f s = some (o, s')) :
    o = .norm ∧ WrPost s s' (k.flush.exec 0 ks).1 (k.flush.exec 0 ks).2 0 := by
  have h₁ : exec (seqs [cS k.flush, .gset NXT (.c 0), .gset PC (.c pWR)]) f (sF s) = some (o, s') := by
    rw [← flushOut_eq]
    exact h
  obtain ⟨r, h₂⟩ : ∃ r, exec (cS k.flush) f (sF s) = some r := exec_seq_some h₁
  obtain ⟨-, ho₂, hR₄, hF₄⟩ : Post k.flush (sF s) ks [] r.1 r.2 := cS_sound k.flush (sF_rep hK) h₂
  have h₂' : exec (cS k.flush) f (sF s) = some (.norm, r.2) := by rw [h₂, ← ho₂]
  have hx : exec (seqs [cS k.flush, .gset NXT (.c 0), .gset PC (.c pWR)]) f (sF s) =
      some (.norm, { r.2 with g := upd (upd r.2.g NXT 0) PC pWR }) := by
    simp [seqs, exec_seq_norm h₂', exec, E.eval]
  have hos : o = .norm ∧ s' = { r.2 with g := upd (upd r.2.g NXT 0) PC pWR } := by
    have he : some (o, s') = some (Out.norm, { r.2 with g := upd (upd r.2.g NXT 0) PC pWR }) := by
      rw [← h₁, hx]
    simpa using he
  have hl : (sF s).l LB = 0 := by simp [sF, upd_apply]
  have hR : KRep r.2.g r.2.m (k.flush.exec 0 ks).1 (k.flush.exec 0 ks).2 := hl ▸ hR₄
  rw [hos.2]
  exact ⟨hos.1, wrPost_flush hR hF₄⟩

/-! ## After a read -/

/-- The state before the feed loop: the count and the counter set. -/
def sR (s : St) (n : Nat) : St := { s with l := upd (upd s.l LN n) LI 0 }

theorem remu16_eval (p : E) (s : St) : (E.bin .remu p (.c 16)).eval s = p.eval s % 16 := by
  simp [E.eval, Bin.eval]

theorem divu16_eval (p : E) (s : St) : (E.bin .divu p (.c 16)).eval s = p.eval s / 16 := by
  simp [E.eval, Bin.eval]

/-- What `onRead` establishes. -/
def ReadPost (k : KM) (s : St) (ks : KSt) (bs : List Nat) (v : Nat) (s' : St) : Prop :=
  (v % 16 ≠ 0 ∧ s' = { s with g := upd s.g PC pEOI }) ∨
    (v % 16 = 0 ∧ fitsF k ks bs 0 = true ∧ WrPost s s' (k.tr.feed ks bs).1 (k.tr.feed ks bs).2 1)

/-- The two `global.set`s ending a write-out keep what the feed established. -/
theorem wrPost_sets {s s₂ : St} {ks : KSt} {ys : List Nat} (hR : KRep s₂.g s₂.m ks ys)
    (hF : FrameL s s₂) (hoff : s.g OOFF = 0) :
    WrPost s { s₂ with g := upd (upd s₂.g NXT 1) PC pWR } ks ys 1 := by
  have hk := frame_hs hF.g
  refine ⟨by simp [upd_apply], by simp [upd_apply], ?_, ?_, ?_, hF.st, hF.rp⟩
  · simp only [OOFF, NXT, PC] at hk hoff ⊢
    simp [upd_apply, hk.2.2.2.2.2, hoff]
  · exact (hR.upd_g _ (by decide) (by decide) (by decide)).upd_g _ (by decide) (by decide) (by decide)
  · simp only [INSR, OUTSW, WS, NXT, PC] at hk ⊢
    simp [upd_apply, hk.1, hk.2.1, hk.2.2.1]

/-- The feed of a completed read: the bytes of the input buffer fed to the kernel. -/
theorem onRead_completed {k : KM} {f : Nat} {s s' : St} {o : Out} {ks : KSt} {bs : List Nat}
    (hK : KS s.g s.m ks) (h0 : s.g OLEN = 0) (hoff : s.g OOFF = 0)
    (hin : slice s.m IN bs.length = bs) (hlen : bs.length ≤ 256)
    (h : lab (exec (seqs [feedLoop k, .gset NXT (.c 1), .gset PC (.c pWR)]) f (sR s bs.length)) =
      some (o, s')) :
    o = .norm ∧ fitsF k ks bs 0 = true ∧ WrPost s s' (k.tr.feed ks bs).1 (k.tr.feed ks bs).2 1 := by
  have hI : LInv (sR s bs.length) ks [] bs 0 :=
    ⟨hK.krep h0, by simp [sR, upd_apply], by simp [sR, upd_apply], hin, Nat.zero_le _, hlen⟩
  obtain ⟨r, hr⟩ := lab_some h
  obtain ⟨r₁, hf⟩ : ∃ r₁, exec (feedLoop k) f (sR s bs.length) = some r₁ := exec_seq_some hr
  obtain ⟨ho₁, hfit, hR₂, hF₂⟩ : r₁.1 = .norm ∧ LPost k (sR s bs.length) ks [] bs 0 r₁.2 :=
    feed_sound hI hf
  have hf' : exec (feedLoop k) f (sR s bs.length) = some (.norm, r₁.2) := by rw [hf, ← ho₁]
  have hx : exec (seqs [feedLoop k, .gset NXT (.c 1), .gset PC (.c pWR)]) f (sR s bs.length) =
      some (.norm, { r₁.2 with g := upd (upd r₁.2.g NXT 1) PC pWR }) := by
    simp [seqs, exec_seq_norm hf', exec, E.eval]
  have hos : o = .norm ∧ s' = { r₁.2 with g := upd (upd r₁.2.g NXT 1) PC pWR } := by
    have he : some (o, s') = some (Out.norm, { r₁.2 with g := upd (upd r₁.2.g NXT 1) PC pWR }) := by
      rw [← h, hx, lab_norm]
    simpa using he
  have hFs : FrameL s r₁.2 := (frameL_l s _).trans hF₂
  rw [hos.2]
  exact ⟨hos.1, by simpa using hfit, wrPost_sets (by simpa using hR₂) hFs hoff⟩

/-- **After a read** with packed result `p` (its value `v`): on `DROPPED` the input has
ended; on `COMPLETED` the `v / 16` bytes of the input buffer were fed to the kernel. -/
theorem onRead_sound {k : KM} {f : Nat} {p : E} {s s' : St} {o : Out} {ks : KSt} {bs : List Nat}
    (hK : KS s.g s.m ks) (h0 : s.g OLEN = 0) (hoff : s.g OOFF = 0)
    (hin : slice s.m IN bs.length = bs) (hlen : bs.length ≤ 256)
    (hcnt : p.eval s % 16 = 0 → p.eval s / 16 = bs.length)
    (h : exec (onRead k p) f s = some (o, s')) : o = .norm ∧ ReadPost k s ks bs (p.eval s) s' := by
  have h' : lab (if (p.eval s % 16) ≠ 0 then exec (.gset PC (.c pEOI)) f s else
      exec (seqs [.lset LN (.bin .divu p (.c 16)), .lset LI (.c 0), feedLoop k,
        .gset NXT (.c 1), .gset PC (.c pWR)]) f s) = some (o, s') := by
    rw [← remu16_eval, ← exec_ite, ← onRead]
    exact h
  by_cases hc : p.eval s % 16 = 0
  · show o = .norm ∧ ReadPost k s ks bs (p.eval s) s'
    have hpre : exec (seqs [.lset LN (.bin .divu p (.c 16)), .lset LI (.c 0), feedLoop k,
        .gset NXT (.c 1), .gset PC (.c pWR)]) f s =
        exec (seqs [feedLoop k, .gset NXT (.c 1), .gset PC (.c pWR)]) f (sR s bs.length) := by
      rw [← hcnt hc]
      simp [seqs, exec, E.eval, Bin.eval, sR]
    have h₁ : lab (exec (seqs [feedLoop k, .gset NXT (.c 1), .gset PC (.c pWR)]) f
        (sR s bs.length)) = some (o, s') := by
      rw [← hpre]
      simpa [hc] using h'
    obtain ⟨ho, hfit, hW⟩ := onRead_completed hK h0 hoff hin hlen h₁
    exact ⟨ho, .inr ⟨hc, hfit, hW⟩⟩
  · have he : some (o, s') = some (Out.norm, { s with g := upd s.g PC pEOI }) := by
      rw [← h']
      simp [hc, exec_gset, lab_norm, E.eval]
    have hos : o = .norm ∧ s' = { s with g := upd s.g PC pEOI } := by simpa using he
    exact ⟨hos.1, .inl ⟨hc, hos.2⟩⟩

/-! ## After a write -/

/-- The globals after a write's result `v`: the offset advanced by the count (at most to the
end), or `FAULT`. -/
def wrG (g : Nat → Nat) (v : Nat) : Nat → Nat :=
  if v % 16 = 0 then upd (upd g OOFF (min (g OOFF + v / 16) (g OLEN))) PC pWR else upd g PC pFAULT

/-- The state after a completed write of `n` items, with the new offset `x`. -/
def wrSt (s : St) (n x : Nat) : St := { s with l := upd s.l LN n, g := upd (upd s.g OOFF x) PC pWR }

/-- The new offset computed by the code. -/
def wrOff (g : Nat → Nat) (n : Nat) : Nat := if g OLEN - g OOFF ≤ n then g OLEN else (g OOFF + n) % M32

/-- The new offset after a write of `n` items: at most the end of the buffer. -/
theorem onWrite_off {g : Nat → Nat} (hle : g OOFF ≤ g OLEN) (hcap : g OLEN ≤ CAP) (n : Nat) :
    wrOff g n = min (g OOFF + n) (g OLEN) := by
  unfold wrOff
  by_cases hge : g OLEN - g OOFF ≤ n
  · simp only [hge, ↓reduceIte]
    omega
  · have hlt : (g OOFF + n) % M32 = g OOFF + n := by
      simp only [CAP, M32] at hcap ⊢
      exact Nat.mod_eq_of_lt (by omega)
    simp only [hge, ↓reduceIte, hlt]
    omega

/-- The completed write: the offset advanced, `pc = WR`. -/
theorem onWrite_seq {f : Nat} {p : E} {s : St} (hle : s.g OOFF ≤ s.g OLEN) (hcap : s.g OLEN ≤ CAP) :
    exec (seqs [.lset LN (.bin .divu p (.c 16)),
      .ite (.bin .geu (.l LN) (.bin .sub (.g OLEN) (.g OOFF))) (.gset OOFF (.g OLEN))
        (.gset OOFF (.bin .add (.g OOFF) (.l LN))), .gset PC (.c pWR)]) f s =
      some (.norm, wrSt s (p.eval s / 16) (wrOff s.g (p.eval s / 16))) := by
  have hsub : (s.g OLEN + (M32 - s.g OOFF % M32)) % M32 = s.g OLEN - s.g OOFF := by
    simp only [CAP, M32] at hcap ⊢
    omega
  have hsub' : (s.g 3 + (M32 - s.g 4 % M32)) % M32 = s.g 3 - s.g 4 := hsub
  by_cases hge : s.g OLEN - s.g OOFF ≤ p.eval s / 16
  · have hge' : s.g 3 - s.g 4 ≤ p.eval s / 16 := hge
    simp [seqs, exec, E.eval, Bin.eval, upd_apply, hsub', hge', lab, wrSt, wrOff]
  · have hge' : ¬ s.g 3 - s.g 4 ≤ p.eval s / 16 := hge
    simp [seqs, exec, E.eval, Bin.eval, upd_apply, hsub', hge', lab, wrSt, wrOff]

/-- **After a write** with packed result `p`. -/
theorem onWrite_sound {f : Nat} {p : E} {s s' : St} {o : Out}
    (hle : s.g OOFF ≤ s.g OLEN) (hcap : s.g OLEN ≤ CAP)
    (h : exec (onWrite p) f s = some (o, s')) :
    o = .norm ∧ s'.g = wrG s.g (p.eval s) ∧ s'.m = s.m ∧ s'.st = s.st ∧ s'.rp = s.rp := by
  rw [onWrite, exec_ite, remu16_eval] at h
  by_cases hc : p.eval s % 16 = 0
  · show o = .norm ∧ s'.g = wrG s.g (p.eval s) ∧ s'.m = s.m ∧ s'.st = s.st ∧ s'.rp = s.rp
    have he : some (o, s') = some (Out.norm, wrSt s (p.eval s / 16) (wrOff s.g (p.eval s / 16))) := by
      rw [← h]
      simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte, onWrite_seq hle hcap, lab_norm]
    have hos : o = .norm ∧ s' = wrSt s (p.eval s / 16) (wrOff s.g (p.eval s / 16)) := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using he
    have hoff : wrOff s.g (p.eval s / 16) = min (s.g OOFF + p.eval s / 16) (s.g OLEN) :=
      onWrite_off hle hcap _
    rw [hos.2]
    exact ⟨hos.1, by simp [wrSt, wrG, hc, hoff], rfl, rfl, rfl⟩
  · show o = .norm ∧ s'.g = wrG s.g (p.eval s) ∧ s'.m = s.m ∧ s'.st = s.st ∧ s'.rp = s.rp
    have he : some (o, s') = some (Out.norm, { s with g := upd s.g PC pFAULT }) := by
      rw [← h]
      simp [hc, exec_gset, lab_norm, E.eval]
    have hos : o = .norm ∧ s' = { s with g := upd s.g PC pFAULT } := by simpa using he
    rw [hos.2]
    exact ⟨hos.1, by simp [wrG, hc], rfl, rfl, rfl⟩

end Silmaril.Proofs.Wasm.JcoTool.KCore
