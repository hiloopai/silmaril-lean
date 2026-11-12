module

public import Silmaril.Proofs.Wasm.JcoTool.KCore.Main

/-!
# The generated module does what `Proc.tStep` does (completeness, under the bounds)

(Restyled to the Isar conventions of `docs/projects/wasm-components.md` when moved out of `Silmaril/Raw`; the statements are
restated in `Silmaril.Wasm.JcoTool.KCore.Thms`.)

* `flushOut_complete`, `onRead_complete`, `onWrite_complete`: the pieces of the callback finish
  when the bounds checks of the kernel pass.
* `step_progress`: from a machine related to `t`, when `tStep` steps from `t` and the conditions
  `Cond` hold (the kernel's bounds for what it is fed or flushes, the events the runtime
  delivers at a wait are well formed and are the ones the module waits for), the runtime steps.
* `step_complete`: and then it steps to the same store and a state related to `tStep`'s.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCore

open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event EventCode blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Proc (TPc tStep)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

attribute [local simp] PC GST BLEN OLEN OOFF NXT INSR OUTSW WS LI LB LR LN pRD pWTR pEOI pWR pWTW
  pCL pFIN pFAULT

theorem flushOut_complete {k : KM} {f : Nat} {s : St} {ks : KSt} (hK : KS s.g s.m ks)
    (hfit : fitsS 0 k.flush ks 0 = true) : ∃ s', exec (flushOut k) f s = some (.norm, s') := by
  have hpre : ∀ rest : S, exec (.seq (.gset OOFF (.c 0)) (.seq (.gset OLEN (.c 0))
      (.seq (.lset LB (.c 0)) rest))) f s = exec rest f (sF s) := by
    intro rest
    simp [exec, E.eval, sF]
  have hR₃ : KRep (sF s).g (sF s).m ks [] := by
    refine KS.krep ⟨?_, ?_, hK.bufs, hK.bcap⟩ ?_
    · simpa [sF, upd_apply] using hK.st
    · simpa [sF, upd_apply] using hK.blen
    · simp [sF, upd_apply]
  have hl : (sF s).l LB = 0 := by simp [sF, upd_apply]
  obtain ⟨s₂, h₂⟩ := cS_complete k.flush (f := f) hR₃ (by rw [hl]; simpa using hfit)
  simp only [flushOut, seqs]
  rw [hpre, exec_seq_norm h₂, exec_seq_norm (exec_gset _ _ _ _), exec_gset]
  exact ⟨_, rfl⟩

theorem onWrite_complete {f : Nat} {p : E} {s : St} : ∃ s', exec (onWrite p) f s = some (.norm, s') := by
  rw [onWrite, exec_ite, remu16_eval]
  by_cases hc : p.eval s % 16 = 0
  · simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte, seqs]
    rw [exec_seq_norm (exec_lset _ _ _ _), exec_seq, exec_ite]
    by_cases hg : (E.bin .geu (.l LN) (.bin .sub (.g OLEN) (.g OOFF))).eval
        { s with l := upd s.l LN ((E.bin .divu p (.c 16)).eval s) } ≠ 0
    · simp only [hg, ne_eq, not_false_eq_true, ↓reduceIte, exec_gset, lab_norm]
      exact ⟨_, rfl⟩
    · simp only [hg, ↓reduceIte, exec_gset, lab_norm]
      exact ⟨_, rfl⟩
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte, exec_gset, lab_norm]
    exact ⟨_, rfl⟩

theorem onRead_complete {k : KM} {f : Nat} {p : E} {s : St} {ks : KSt} {bs : List Nat}
    (hK : KS s.g s.m ks) (h0 : s.g OLEN = 0)
    (hin : slice s.m IN bs.length = bs) (hlen : bs.length ≤ 256)
    (hcnt : p.eval s % 16 = 0 → p.eval s / 16 = bs.length)
    (hfit : p.eval s % 16 = 0 → fitsF k ks bs 0 = true) (hf : bs.length < f) :
    ∃ s', exec (onRead k p) f s = some (.norm, s') := by
  rw [onRead, exec_ite, remu16_eval]
  by_cases hc : p.eval s % 16 = 0
  · have hn : p.eval s / 16 = bs.length := hcnt hc
    have hpre : exec (seqs [.lset LN (.bin .divu p (.c 16)), .lset LI (.c 0), feedLoop k,
        .gset NXT (.c 1), .gset PC (.c pWR)]) f s =
        exec (seqs [feedLoop k, .gset NXT (.c 1), .gset PC (.c pWR)]) f (sR s bs.length) := by
      rw [← hn]
      simp [seqs, exec, E.eval, Bin.eval, sR]
    simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [hpre]
    have hI : LInv (sR s bs.length) ks [] bs 0 :=
      ⟨hK.krep h0, by simp [sR, upd_apply], by simp [sR, upd_apply], hin, Nat.zero_le _, hlen⟩
    obtain ⟨s₂, h₁⟩ := feed_complete hI (by simpa using hfit hc) hf
    simp only [seqs]
    rw [exec_seq_norm h₁, exec_seq_norm (exec_gset _ _ _ _), exec_gset, lab_norm]
    exact ⟨_, rfl⟩
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte, exec_gset, lab_norm]
    exact ⟨_, rfl⟩

/-! ## The machine steps -/

theorem invoke_some {body : S} {ps : List Nat} {st : Store} {ms : MS} {code : Nat} {s' : St}
    {md : Mode} (h : exec body FUEL (st0 ms ps st) = some (.ret code, s')) (hm : modeOf code = some md) :
    ∃ r, invoke body ps st ms = some r := by
  refine ⟨(s'.st, ⟨s'.g, s'.m, s'.rp, md⟩), ?_⟩
  simp only [invoke]
  rw [show (⟨ms.g, ms.m, locals ps, st, ms.rp, 0⟩ : St) = st0 ms ps st from rfl, h]
  simp [hm]

/-- The callback runs the case of `pc`, with the case's result given. -/
theorem cb_some {k : KM} {N : Nat} {st : Store} {ms : MS} {ps : List Nat} {A : S} {n : Nat}
    (hA : (n = pWTR ∧ A = cbWTR k) ∨ (n = pWTW ∧ A = cbWTW) ∨ (n = pRD ∧ A = cbRD k N) ∨
      (n = pEOI ∧ A = cbEOI k) ∨ (n = pWR ∧ A = cbWR) ∨ (n = pCL ∧ A = cbCL))
    (hpc : ms.g PC = n) {code : Nat} {s' : St} {md : Mode}
    (h : exec A FUEL (st0 ms ps st) = some (.ret code, s')) (hm : modeOf code = some md) :
    ∃ r, invoke (gen k N).cb ps st ms = some r := by
  have hx : exec (callback k N) FUEL (st0 ms ps st) = some (.ret code, s') := by
    rw [exec_cb hA hpc, h]
  exact invoke_some hx hm

/-- What a `stream.write` returns. -/
theorem streamWrite_res {st st' : Store} {w : Nat} {xs : List Val} {res : Res}
    (h : Silmaril.Wasm.Component.Async.step st (.streamWrite w xs) = some (st', res)) :
    ∃ r, res = .nat r ∧ (r = blocked ∨ r ≤ 16 * xs.length + 2) := by
  simp only [Silmaril.Wasm.Component.Async.step, Silmaril.Wasm.Component.Async.streamWrite] at h
  split at h
  · split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨_, rfl, .inr ?_⟩
      simp only [Silmaril.Wasm.Component.Async.packCopy, Silmaril.Wasm.Component.Async.CopyResult.toNat]
      omega
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨_, rfl, .inr (by simp [Silmaril.Wasm.Component.Async.packCopy,
          Silmaril.Wasm.Component.Async.CopyResult.toNat])⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨_, rfl, .inl rfl⟩
  · cases h

/-- What a `stream.read` returns, when not items. -/
theorem streamRead_nat {st st' : Store} {r n m : Nat}
    (h : Silmaril.Wasm.Component.Async.step st (.streamRead r n) = some (st', .nat m)) : m = blocked := by
  simp only [Silmaril.Wasm.Component.Async.step, Silmaril.Wasm.Component.Async.streamRead] at h
  split at h
  · split at h
    · cases h
    · cases h
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq, Res.nat.injEq] at h
        exact h.2.symm
  · cases h

theorem prog_cl {k : KM} {N : Nat} {st st' : Store} {ms : MS} {t' : TPc KSt} (hR : Rel ms .cl)
    (ht : tStep (trV k) N st .cl = some (st', t')) : ∃ r, rstep (gen k N) st ms = some r := by
  obtain ⟨hok, hmode, hpc⟩ := hR
  have hn := ok_num hok
  rw [rstep_ready hmode]
  cases hd : Silmaril.Wasm.Component.Async.step st (.streamDropW 4) with
  | none => simp [tStep, hd] at ht
  | some q =>
    have he : exec cbCL FUEL (st0 ms [0, 0, 0] st) = some (.ret 0,
        { st0 ms [0, 0, 0] st with st := q.1, g := upd ms.g PC pFIN }) := by
      simp [cbCL, seqs, exec, callBI, E.eval, st0, hn.2.1, hd]
    exact cb_some hcCL hpc he modeOf_zero

theorem dropFlush_some {k : KM} {s : St} {ks : KSt} (hK : KS s.g s.m ks) (hin : s.g INSR = 1)
    (hfit : fitsS 0 k.flush ks 0 = true) {q : Store × Res}
    (hd : Silmaril.Wasm.Component.Async.step s.st (.streamDropR 1) = some q) :
    ∃ s', exec (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) FUEL s = some (.ret 1, s') := by
  have hin' : s.g 6 = 1 := hin
  have e₁ : exec (.call .dropR [.g INSR] []) FUEL s = some (.norm, { s with st := q.1 }) := by
    simp [exec, callBI, E.eval, hin', hd]
  obtain ⟨s₂, h₂⟩ := flushOut_complete (k := k) (f := FUEL) (s := { s with st := q.1 }) hK hfit
  refine ⟨s₂, ?_⟩
  simp only [seqs]
  rw [exec_seq_norm e₁, exec_seq_norm h₂]
  rfl

theorem prog_eoi {k : KM} {N : Nat} {st st' : Store} {ms : MS} {ks : KSt} {t' : TPc KSt}
    (hR : Rel ms (.eoi ks)) (hc : Cond k N st (.eoi ks))
    (ht : tStep (trV k) N st (.eoi ks) = some (st', t')) : ∃ r, rstep (gen k N) st ms = some r := by
  obtain ⟨hok, hmode, hpc, hk⟩ := hR
  rw [rstep_ready hmode]
  cases hd : Silmaril.Wasm.Component.Async.step st (.streamDropR 1) with
  | none => simp [tStep, hd] at ht
  | some q =>
    obtain ⟨s', h⟩ := dropFlush_some (s := st0 ms [0, 0, 0] st) (ks_of hok hk) hok.1 hc hd
    exact cb_some hcEOI hpc h modeOf_one

/-- The rest of `WR` after a `stream.write` that returned `r` returns. -/
theorem wrRest_some {st st₁ : Store} {ms : MS} {r : Nat} (hok : ms.ok) :
    ∃ code s', exec wrRest FUEL (sW ms st st₁ r) = some (.ret code, s') ∧ ∃ md, modeOf code = some md := by
  have hn := ok_num hok
  have hc : (E.bin .eq (.l LR) (.c blocked)).eval (sW ms st st₁ r) = if r = blocked then 1 else 0 := by
    simp [E.eval, Bin.eval, sW, upd_apply]
  by_cases hb : r = blocked
  · have hbm : blocked % 4294967296 = blocked := by decide
    refine ⟨82, { sW ms st st₁ r with g := upd ms.g PC pWTW }, ?_, _, modeOf_wait⟩
    simp [hbm, hb, wrRest, seqs, exec, E.eval, lab, waitCode, Bin.eval, sW, st0, upd_apply, hn.2.2.1, M32]
  · obtain ⟨s₃, h₃⟩ := onWrite_complete (f := FUEL) (p := .l LR) (s := sW ms st st₁ r)
    have hi : exec (.ite (.bin .eq (.l LR) (.c blocked)) (.seq (.gset PC (.c pWTW)) (.ret waitCode)) .nop)
        FUEL (sW ms st st₁ r) = some (.norm, sW ms st st₁ r) := by
      simp [exec, E.eval, Bin.eval, sW, upd_apply, hb, lab]
    refine ⟨1, s₃, ?_, _, modeOf_one⟩
    simp only [wrRest, seqs]
    rw [exec_seq_norm hi, exec_seq_norm h₃]
    rfl

/-- `WR` with output pending: the write, then the rest. -/
theorem prog_wr_write {st st₁ : Store} {ms : MS} {r : Nat} (hok : ms.ok) (hlt : ms.g OOFF < ms.g OLEN)
    (hw : Silmaril.Wasm.Component.Async.step st (.streamWrite 4 ms.pending) = some (st₁, .nat r))
    (hrM : r < M32) :
    ∃ code s', exec cbWR FUEL (st0 ms [0, 0, 0] st) = some (.ret code, s') ∧ ∃ md, modeOf code = some md := by
  have hlt' : ¬ ms.g 3 ≤ ms.g 4 := by simp only [OLEN, OOFF] at hlt; omega
  have e₁ : exec (.ite (.bin .geu (.g OOFF) (.g OLEN)) (seqs [.gset OOFF (.c 0), .gset OLEN (.c 0),
      .ite (.g NXT) (.gset PC (.c pRD)) (.gset PC (.c pCL)), yield_]) .nop) FUEL (st0 ms [0, 0, 0] st) =
      some (.norm, st0 ms [0, 0, 0] st) := by
    simp [exec, E.eval, Bin.eval, st0, hlt', lab]
  have hitems : (slice ms.m (4096 + ms.g 4) (ms.g 3 - ms.g 4)).map u8v = ms.pending := write_items ms
  have e₂ : callBI .streamWrite [4, 4096 + ms.g 4, ms.g 3 - ms.g 4] [LR] (st0 ms [0, 0, 0] st) =
      some (.norm, sW ms st st₁ r) := by
    simp [callBI, st0, hitems, hw, hrM, sW]
  have hx₂ : exec (.call .streamWrite [.g OUTSW, .bin .add (.c OUT) (.g OOFF), .bin .sub (.g OLEN) (.g OOFF)]
      [LR]) FUEL (st0 ms [0, 0, 0] st) = some (.norm, sW ms st st₁ r) := by
    rw [exec, wr_args ms st hok, e₂]
  obtain ⟨code, s', hx, hmd⟩ := wrRest_some (st := st) (st₁ := st₁) (r := r) hok
  refine ⟨code, s', ?_, hmd⟩
  simp only [cbWR, seqs] at e₁ hx ⊢
  rw [exec_seq_norm e₁, exec_seq_norm hx₂]
  exact hx

theorem prog_wr {k : KM} {N : Nat} {st st' : Store} {ms : MS} {ys : List Val} {next : Option KSt}
    {t' : TPc KSt} (hR : Rel ms (.wr ys next)) (ht : tStep (trV k) N st (.wr ys next) = some (st', t')) :
    ∃ r, rstep (gen k N) st ms = some r := by
  obtain ⟨hok, hmode, hpc, hpend, hnext⟩ := hR
  rw [rstep_ready hmode]
  by_cases hge : ms.g OLEN ≤ ms.g OOFF
  · obtain ⟨g', hx, -⟩ := wr_done (st := st) hok hnext hge
    exact cb_some hcWR hpc hx modeOf_one
  · show ∃ r, invoke (gen k N).cb [0, 0, 0] st ms = some r
    have hlt : ms.g OOFF < ms.g OLEN := Nat.lt_of_not_le hge
    have hlen : ms.pending.length ≤ CAP := by
      have h3 : ms.g 3 ≤ 32768 := (ok_num hok).2.2.2.2.1
      simpa [MS.pending, slice_length, CAP] using by omega
    obtain ⟨y, ys', hys⟩ : ∃ y ys', ys = y :: ys' := List.exists_cons_of_ne_nil (by
      have hl4 : ms.g 4 < ms.g 3 := hlt
      rw [← hpend, MS.pending]
      simpa [slice_length] using hl4)
    obtain ⟨⟨st₁, res⟩, hw⟩ : ∃ q, Silmaril.Wasm.Component.Async.step st (.streamWrite 4 ms.pending) = some q := by
      cases hw : Silmaril.Wasm.Component.Async.step st (.streamWrite 4 ms.pending) with
      | none =>
        have hw' : Silmaril.Wasm.Component.Async.step st (.streamWrite 4 (y :: ys')) = none := by
          rw [← hys, ← hpend]; exact hw
        simp [tStep, hys, hw'] at ht
      | some q => exact ⟨q, rfl⟩
    obtain ⟨r, hres, hr⟩ := streamWrite_res hw
    have hrM : r < M32 := by
      rcases hr with hr | hr
      · rw [hr]; decide
      · simp only [M32, CAP] at hr hlen ⊢; omega
    obtain ⟨code, s', hx, md, hmd⟩ := prog_wr_write hok hlt (hres ▸ hw) hrM
    exact cb_some hcWR hpc hx hmd

theorem check_ok {a : Nat} {e : E} {f : Nat} {s : St} (ha : a < M32) (h₀ : s.l 0 = a)
    (h₁ : s.l 1 = e.eval s) :
    exec (.ite (.bin .eq (.l 0) (.c a)) (.ite (.bin .eq (.l 1) e) .nop .unreachable) .unreachable) f s =
      some (.norm, s) := by
  have ha' : a % M32 = a := Nat.mod_eq_of_lt ha
  simp [exec, E.eval, Bin.eval, ha', h₀, h₁, lab]

/-- A step of `tStep` from a waiting state takes an event. -/
theorem wait_event {k : KM} {N : Nat} {st st' : Store} {t t' : TPc KSt}
    (hwt : (∃ ys next, t = .wtW ys next) ∨ ∃ ks, t = .wtR ks)
    (ht : tStep (trV k) N st t = some (st', t')) :
    ∃ st₁ e, Silmaril.Wasm.Component.Async.step st (.wait 5) = some (st₁, .event e) := by
  cases hw : Silmaril.Wasm.Component.Async.step st (.wait 5) with
  | none =>
    rcases hwt with ⟨ys, next, rfl⟩ | ⟨ks, rfl⟩ <;> simp [tStep, hw] at ht
  | some q =>
    obtain ⟨st₁, res⟩ := q
    cases res with
    | event e => exact ⟨st₁, e, rfl⟩
    | _ => rcases hwt with ⟨ys, next, rfl⟩ | ⟨ks, rfl⟩ <;> simp [tStep, hw] at ht

theorem prog_wtW {k : KM} {N : Nat} {st st' : Store} {ms : MS} {ys : List Val} {next : Option KSt}
    {t' : TPc KSt} (hR : Rel ms (.wtW ys next)) (hcd : Cond k N st (.wtW ys next))
    (ht : tStep (trV k) N st (.wtW ys next) = some (st', t')) : ∃ r, rstep (gen k N) st ms = some r := by
  obtain ⟨hok, hmode, hpc, -, -⟩ := hR
  have hn := ok_num hok
  obtain ⟨st₁, e, hw⟩ := wait_event (.inl ⟨ys, next, rfl⟩) ht
  obtain ⟨hwf, hcode, hidx⟩ := hcd st₁ e hw
  have hdel : deliver e ms = ms := by simp [deliver, hcode]
  have hc : exec (.ite (.bin .eq (.l 0) (.c 3)) (.ite (.bin .eq (.l 1) (.g OUTSW)) .nop .unreachable)
      .unreachable) FUEL (st0 ms [e.code.toNat, e.index, e.payload] st₁) =
      some (.norm, st0 ms [e.code.toNat, e.index, e.payload] st₁) :=
    check_ok (by simp [M32]) (by simp [st0, locals, hcode, EventCode.toNat])
      (by simp [st0, locals, E.eval, hidx, hn.2.1])
  obtain ⟨s₂, h₂⟩ := onWrite_complete (f := FUEL) (p := .l 2)
    (s := st0 ms [e.code.toNat, e.index, e.payload] st₁)
  have hx : exec cbWTW FUEL (st0 ms [e.code.toNat, e.index, e.payload] st₁) = some (.ret 1, s₂) := by
    simp only [cbWTW, seqs]
    rw [exec_seq_norm hc, exec_seq_norm h₂]
    rfl
  obtain ⟨r, hr⟩ := cb_some (k := k) (N := N) hcWTW hpc hx modeOf_one
  refine ⟨r, ?_⟩
  simp only [rstep, hmode, hw, hwf, ↓reduceIte, hdel]
  exact hr

theorem exec_seq_ite_ret' {c : E} {A rest : S} {f : Nat} {s s' : St} {v : Nat} (hc : c.eval s ≠ 0)
    (hA : exec A f s = some (.ret v, s')) : exec (.seq (.ite c A .nop) rest) f s = some (.ret v, s') := by
  rw [exec_seq, exec_ite]
  simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte, hA]
  rfl

/-- The part of `RD` after `local.set LB 0`. -/
def rdTail (k : KM) (N : Nat) : S :=
  .seq (.ite (cE k.done) (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) .nop)
    (seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
      .ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTR), .ret waitCode]) .nop,
      onRead k (.l LR), yield_])

theorem cbRD_of_tail {k : KM} {N : Nat} {ms : MS} {st : Store} {code : Nat} {s' : St}
    (h : exec (rdTail k N) FUEL (sA ms st) = some (.ret code, s')) :
    exec (cbRD k N) FUEL (st0 ms [0, 0, 0] st) = some (.ret code, s') := by
  have e₀ : exec (.lset LB (.c 0)) FUEL (st0 ms [0, 0, 0] st) = some (.norm, sA ms st) := rfl
  rw [show cbRD k N = .seq (.lset LB (.c 0)) (rdTail k N) from rfl, exec_seq_norm e₀]
  exact h

theorem rd_call {N : Nat} {ms : MS} {st : Store} {r : Option (Out × St)} (hN : N ≤ 256)
    (hok : ms.ok) (hr : callBI .streamRead [1, IN, N] [LR] (sA ms st) = r) :
    exec (.call .streamRead [.g INSR, .c IN, .c N] [LR]) FUEL (sA ms st) = r := by
  have hn := ok_num hok
  have hargs : [E.g INSR, .c IN, .c N].map (·.eval (sA ms st)) = [1, IN, N] := by
    have hN' : N < 4294967296 := by omega
    simp [E.eval, sA, st0, hn.1, hN', IN, M32]
  rw [exec, hargs, hr]

/-- `RD` when done: drop the input, flush, `YIELD`. -/
theorem prog_rd_done {k : KM} {N : Nat} {st : Store} {ms : MS} {ks : KSt} (hok : ms.ok)
    (hK : KS ms.g ms.m ks) (hd : k.tr.done ks = true) (hfit : fitsS 0 k.flush ks 0 = true)
    {q : Store × Res} (hdr : Silmaril.Wasm.Component.Async.step st (.streamDropR 1) = some q) :
    ∃ s', exec (rdTail k N) FUEL (sA ms st) = some (.ret 1, s') := by
  have hc : (cE k.done).eval (sA ms st) ≠ 0 :=
    (done_eval k (s := sA ms st) hK.st hK.blen (by simp [sA, upd_apply])).mpr hd
  obtain ⟨s', h⟩ := dropFlush_some (s := sA ms st) hK hok.1 hfit hdr
  exact ⟨s', exec_seq_ite_ret' hc h⟩

/-- `RD`, not done, the read delivered `xs`: `onRead`, `YIELD`. -/
theorem prog_rd_read {k : KM} {N : Nat} {st st₁ : Store} {ms : MS} {ks : KSt} {p : Nat}
    {xs : List Val} (hN : N ≤ 256) (hok : ms.ok) (hK : KS ms.g ms.m ks) (h0 : ms.g OLEN = 0)
    (hc : (cE k.done).eval (sA ms st) = 0)
    (hr : Silmaril.Wasm.Component.Async.step st (.streamRead 1 N) = some (st₁, .read p xs))
    (hfit : p % 16 = 0 → fitsF k ks (xs.map byteOf) 0 = true) :
    ∃ s', exec (rdTail k N) FUEL (sA ms st) = some (.ret 1, s') := by
  obtain ⟨hlen, hp, hcnt⟩ := streamRead_res hr
  have hpM : p < M32 := by simp [M32]; omega
  have hpb : p ≠ blocked := by simp [blocked]; omega
  have e₁ : callBI .streamRead [1, IN, N] [LR] (sA ms st) = some (.norm, sB ms st₁ p xs st) := by
    simp [callBI, show (sA ms st).st = st from rfl, hr, hpM, sB]
  have hcb' : (E.bin .eq (.l LR) (.c blocked)).eval (sB ms st₁ p xs st) = 0 := by
    simp [E.eval, Bin.eval, sB, upd_apply, hpb]
  have hKb : KS (sB ms st₁ p xs st).g (sB ms st₁ p xs st).m ks := by
    simpa [sB, sA, st0] using KS.writeIn hK (bs := xs.map byteOf) (by simp; omega)
  have hpl : (E.l LR).eval (sB ms st₁ p xs st) = p := by simp [E.eval, sB, upd_apply]
  obtain ⟨s₂, h₂⟩ := onRead_complete (k := k) (f := FUEL) (p := .l LR) hKb
    (by simpa [sB, sA, st0] using h0)
    (show slice (sB ms st₁ p xs st).m IN (xs.map byteOf).length = xs.map byteOf from slice_writeBytes _ _ _)
    (by simp; omega) (by rw [hpl]; intro h; simpa using hcnt h)
    (by rw [hpl]; exact hfit) (by simp [FUEL, M32]; omega)
  refine ⟨s₂, ?_⟩
  rw [rdTail, exec_seq_ite_skip hc]
  simp only [seqs]
  rw [exec_seq_norm (rd_call hN hok e₁), exec_seq_ite_skip hcb', exec_seq_norm h₂]
  rfl

/-- `RD`, not done, the read blocked: `pc = WTR`, wait. -/
theorem prog_rd_blocked {k : KM} {N : Nat} {st st₁ : Store} {ms : MS} (hN : N ≤ 256) (hok : ms.ok)
    (hc : (cE k.done).eval (sA ms st) = 0)
    (hr : Silmaril.Wasm.Component.Async.step st (.streamRead 1 N) = some (st₁, .nat blocked)) :
    ∃ s', exec (rdTail k N) FUEL (sA ms st) = some (.ret 82, s') := by
  have hn := ok_num hok
  have e₁ : callBI .streamRead [1, IN, N] [LR] (sA ms st) = some (.norm, sBl ms st st₁) := by
    simp [callBI, show (sA ms st).st = st from rfl, hr, sBl]
  have hcb' : (E.bin .eq (.l LR) (.c blocked)).eval (sBl ms st st₁) ≠ 0 := by
    simp [E.eval, Bin.eval, upd_apply, sBl]
  have hW : exec (.seq (.gset PC (.c pWTR)) (.ret waitCode)) FUEL (sBl ms st st₁) =
      some (.ret 82, { sBl ms st st₁ with g := upd ms.g PC pWTR }) := by
    simp [exec, E.eval, waitCode, Bin.eval, sBl, sA, st0, upd_apply, hn.2.2.1, M32]
  refine ⟨{ sBl ms st st₁ with g := upd ms.g PC pWTR }, ?_⟩
  rw [rdTail, exec_seq_ite_skip hc]
  simp only [seqs]
  rw [exec_seq_norm (rd_call hN hok e₁), exec_seq_ite_ret' hcb' hW]

theorem prog_rd {k : KM} {N : Nat} {st st' : Store} {ms : MS} {ks : KSt} {t' : TPc KSt}
    (hN : N ≤ 256) (hR : Rel ms (.rd ks)) (hcd : Cond k N st (.rd ks))
    (ht : tStep (trV k) N st (.rd ks) = some (st', t')) : ∃ r, rstep (gen k N) st ms = some r := by
  obtain ⟨hok, hmode, hpc, hk, h0, -⟩ := hR
  have hK : KS ms.g ms.m ks := ks_of hok hk
  rw [rstep_ready hmode]
  by_cases hd : k.tr.done ks = true
  · have hdone : (trV k).done ks = true := hd
    obtain ⟨q, hdr⟩ : ∃ q, Silmaril.Wasm.Component.Async.step st (.streamDropR 1) = some q :=
      Option.ne_none_iff_exists'.mp fun hn => by simp [tStep, hdone, hn] at ht
    obtain ⟨s', h⟩ := prog_rd_done (N := N) hok hK hd (hcd.1 hd) hdr
    exact cb_some hcRD hpc (cbRD_of_tail h) modeOf_one
  · show ∃ r, invoke (gen k N).cb [0, 0, 0] st ms = some r
    have hdf : k.tr.done ks = false := by simpa using hd
    have hdone : (trV k).done ks = false := hdf
    have hc : (cE k.done).eval (sA ms st) = 0 :=
      Classical.not_not.mp fun hne => hd ((done_eval k (s := sA ms st) hK.st hK.blen
        (by simp [sA, upd_apply])).mp hne)
    obtain ⟨⟨st₁, res⟩, hr⟩ : ∃ q, Silmaril.Wasm.Component.Async.step st (.streamRead 1 N) = some q :=
      Option.ne_none_iff_exists'.mp fun hn => by simp [tStep, hdone, hn] at ht
    cases res with
    | read p xs =>
      obtain ⟨s', h⟩ := prog_rd_read hN hok hK h0 hc hr (hcd.2 st₁ p xs hr)
      exact cb_some hcRD hpc (cbRD_of_tail h) modeOf_one
    | nat m =>
      obtain ⟨s', h⟩ := prog_rd_blocked (k := k) hN hok hc (streamRead_nat hr ▸ hr)
      exact cb_some hcRD hpc (cbRD_of_tail h) modeOf_wait
    | _ => simp [tStep, hdone, hr] at ht

theorem prog_wtR {k : KM} {N : Nat} {st st' : Store} {ms : MS} {ks : KSt} {t' : TPc KSt}
    (hR : Rel ms (.wtR ks)) (hcd : Cond k N st (.wtR ks))
    (ht : tStep (trV k) N st (.wtR ks) = some (st', t')) : ∃ r, rstep (gen k N) st ms = some r := by
  obtain ⟨hok, hmode, hpc, hk, h0, -, hrp0⟩ := hR
  have hn := ok_num hok
  have hK : KS ms.g ms.m ks := ks_of hok hk
  obtain ⟨st₁, e, hw⟩ := wait_event (.inr ⟨ks, rfl⟩) ht
  obtain ⟨hwf, hcode, hidx, hfit⟩ := hcd st₁ e hw
  obtain ⟨-, -, hlen, hcnt⟩ := wellFormed_inv hwf
  have hdel : deliver e ms = { ms with m := writeBytes ms.m IN (e.items.map byteOf), rp := none } := by
    simp [deliver, hcode, hrp0, hidx, IN]
  generalize hsb : st0 { ms with m := writeBytes ms.m IN (e.items.map byteOf), rp := none }
    [e.code.toNat, e.index, e.payload] st₁ = sb
  have hc : exec (.ite (.bin .eq (.l 0) (.c 2)) (.ite (.bin .eq (.l 1) (.g INSR)) .nop .unreachable)
      .unreachable) FUEL sb = some (.norm, sb) := by
    rw [← hsb]
    exact check_ok (by simp [M32]) (by simp [st0, locals, hcode, EventCode.toNat])
      (by simp [st0, locals, E.eval, hidx, hn.1])
  have hKb : KS sb.g sb.m ks := by
    rw [← hsb]
    exact KS.writeIn hK (by simpa using hlen)
  have hpl : (E.l 2).eval sb = e.payload := by rw [← hsb]; rfl
  have hin : slice sb.m IN (e.items.map byteOf).length = e.items.map byteOf := by
    rw [← hsb]; exact slice_writeBytes _ _ _
  obtain ⟨s₂, h₂⟩ := onRead_complete (k := k) (f := FUEL) (p := .l 2) hKb
    (by rw [← hsb]; exact h0) hin (by simpa using hlen)
    (by rw [hpl]; intro hz; simpa using hcnt hcode hz) (by rw [hpl]; exact hfit)
    (by simp [FUEL, M32]; omega)
  have hx : exec (cbWTR k) FUEL sb = some (.ret 1, s₂) := by
    simp only [cbWTR, seqs]
    rw [exec_seq_norm hc, exec_seq_norm h₂]
    rfl
  have hpc' : ({ ms with m := writeBytes ms.m IN (e.items.map byteOf), rp := none } : MS).g PC = pWTR := hpc
  rw [← hsb] at hx
  obtain ⟨r, hr⟩ := cb_some (k := k) (N := N) hcWTR hpc' hx modeOf_one
  refine ⟨r, ?_⟩
  simp only [rstep, hmode, hw, hwf, ↓reduceIte, hdel]
  exact hr

/-- **Progress**: when `tStep` steps from `t` and the conditions hold, the runtime steps. -/
theorem step_progress {k : KM} {N : Nat} (hN : N ≤ 256) {st st' : Store} {ms : MS} {t t' : TPc KSt}
    (hR : Rel ms t) (hcd : Cond k N st t) (ht : tStep (trV k) N st t = some (st', t')) :
    ∃ r, rstep (gen k N) st ms = some r := by
  cases t with
  | rd ks => exact prog_rd hN hR hcd ht
  | wtR ks => exact prog_wtR hR hcd ht
  | eoi ks => exact prog_eoi hR hcd ht
  | wr ys next => exact prog_wr hR ht
  | wtW ys next => exact prog_wtW hR hcd ht
  | cl => exact prog_cl hR ht
  | fin => simp [tStep] at ht
  | fault => simp [tStep] at ht

/-- **Completeness**: when `tStep` steps from `t` and the conditions hold, the runtime steps to
the same store and a state related to `tStep`'s. -/
theorem step_complete {k : KM} {N : Nat} (hN : N ≤ 256) {st st' : Store} {ms : MS} {t t' : TPc KSt}
    (hR : Rel ms t) (hcd : Cond k N st t) (ht : tStep (trV k) N st t = some (st', t')) :
    ∃ ms', rstep (gen k N) st ms = some (st', ms') ∧ Rel ms' t' := by
  obtain ⟨⟨st'', ms'⟩, h⟩ := step_progress hN hR hcd ht
  obtain ⟨t'', ht'', hR'⟩ := step_sound hN hR h
  rw [ht] at ht''
  simp only [Option.some.injEq, Prod.mk.injEq] at ht''
  obtain ⟨rfl, rfl⟩ := ht''
  exact ⟨ms', h, hR'⟩

end Silmaril.Proofs.Wasm.JcoTool.KCore
