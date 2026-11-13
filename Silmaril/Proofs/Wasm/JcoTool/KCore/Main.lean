module

public import Silmaril.Proofs.Wasm.JcoTool.KCore.Sim
public import Silmaril.Proofs.Wasm.JcoTool.KCore.Ret

/-!
# The generated module simulates `Proc.tStep`

(Restyled to the Isar conventions of `docs/projects/wasm-components.md` when moved out of `Silmaril/Raw`; the statements are
restated in `Silmaril.Wasm.JcoTool.KCore.Thms`.)

`step_sound`: every step of the callback runtime on the generated module, from a machine
related to a transformer state `t` (`Rel`), is a step of `Proc.tStep (trV k) N` from `t` with
the same store, to a state related to the machine's new state.
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

/-- The callback runs the case of `pc`. -/
theorem exec_cb {k : KM} {N f : Nat} {s : St} {A : S} {n : Nat}
    (hA : (n = pWTR ∧ A = cbWTR k) ∨ (n = pWTW ∧ A = cbWTW) ∨ (n = pRD ∧ A = cbRD k N) ∨
      (n = pEOI ∧ A = cbEOI k) ∨ (n = pWR ∧ A = cbWR) ∨ (n = pCL ∧ A = cbCL))
    (h : s.g PC = n) : exec (callback k N) f s = exec A f s := by
  have hr : OutIn IsRet A := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := retOnly k N
    rcases hA with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  exact exec_callback hA h fun r hx => by
    obtain ⟨o, s'⟩ := r
    obtain ⟨v, rfl⟩ := hr f s o s' hx
    exact ⟨v, s', rfl⟩

theorem rstep_ready {P : Prog} {st : Store} {ms : MS} (h : ms.mode = .ready) :
    rstep P st ms = invoke P.cb [0, 0, 0] st ms := by
  simp [rstep, h]

/-- The handles and bounds, numerically. -/
theorem ok_num {ms : MS} (h : ms.ok) :
    ms.g 6 = 1 ∧ ms.g 7 = 4 ∧ ms.g 8 = 5 ∧ ms.g 2 ≤ 32768 ∧ ms.g 3 ≤ 32768 ∧ ms.g 4 ≤ ms.g 3 := h

theorem cb_eq (k : KM) (N : Nat) : (gen k N).cb = callback k N := rfl

theorem hcCL {k : KM} {N : Nat} : (pCL = pWTR ∧ cbCL = cbWTR k) ∨ (pCL = pWTW ∧ cbCL = cbWTW) ∨
    (pCL = pRD ∧ cbCL = cbRD k N) ∨ (pCL = pEOI ∧ cbCL = cbEOI k) ∨ (pCL = pWR ∧ cbCL = cbWR) ∨
    (pCL = pCL ∧ cbCL = cbCL) := .inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))

/-! ## `CL` and `FAULT` -/

/-- The entry of a `ready` step: the callback runs the case of `pc`, which returns `code`. -/
theorem entry {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} {A : S} {n : Nat}
    (hmode : ms.mode = .ready)
    (hA : (n = pWTR ∧ A = cbWTR k) ∨ (n = pWTW ∧ A = cbWTW) ∨ (n = pRD ∧ A = cbRD k N) ∨
      (n = pEOI ∧ A = cbEOI k) ∨ (n = pWR ∧ A = cbWR) ∨ (n = pCL ∧ A = cbCL))
    (hpc : ms.g PC = n) (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ code s', exec A FUEL (st0 ms [0, 0, 0] st) = some (.ret code, s') ∧
      modeOf code = some ms'.mode ∧ st' = s'.st ∧ ms'.g = s'.g ∧ ms'.m = s'.m ∧ ms'.rp = s'.rp := by
  have h' : invoke (gen k N).cb [0, 0, 0] st ms = some (st', ms') := by
    rw [← rstep_ready hmode]
    exact h
  obtain ⟨code, s', hx, hrest⟩ := invoke_inv h'
  have hx' : exec A FUEL (st0 ms [0, 0, 0] st) = some (.ret code, s') := by
    rw [← exec_cb hA hpc, ← cb_eq]
    exact hx
  exact ⟨code, s', hx', hrest⟩

theorem sim_cl {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} (hR : Rel ms .cl)
    (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ t', tStep (trV k) N st .cl = some (st', t') ∧ Rel ms' t' := by
  obtain ⟨hok, hmode, hpc⟩ := hR
  have hn : ms.g 7 = 4 := (ok_num hok).2.1
  obtain ⟨code, s', hx, hmd, hst, -⟩ := entry hmode hcCL hpc h
  obtain ⟨r, hd⟩ : ∃ r, Silmaril.Wasm.Component.Async.step st (.streamDropW 4) = some r := by
    cases hd : Silmaril.Wasm.Component.Async.step st (.streamDropW 4) with
    | none => simp [cbCL, seqs, exec, callBI, E.eval, st0, hn, hd] at hx
    | some r => exact ⟨r, rfl⟩
  have he : some (Out.ret code, s') =
      some (.ret 0, { st0 ms [0, 0, 0] st with st := r.1, g := upd ms.g PC pFIN }) := by
    rw [← hx]
    simp [cbCL, seqs, exec, callBI, E.eval, st0, hn, hd]
  have hcs : code = 0 ∧ s' = { st0 ms [0, 0, 0] st with st := r.1, g := upd ms.g PC pFIN } := by
    simpa using he
  have hex : ms'.mode = .exited := by simpa [modeOf, hcs.1] using hmd.symm
  refine ⟨.fin, ?_, hex⟩
  rw [hst, hcs.2]
  simp [tStep, hd]

/-! ## The machine's view -/

theorem kst_eq {g m : Nat → Nat} {ks : KSt} {out : List Nat} (hR : KRep g m ks out)
    (rp : Option (Nat × Nat)) (md : Mode) : MS.kst ⟨g, m, rp, md⟩ = ks := by
  have hb : slice m KBUF (g BLEN) = ks.buf := by rw [hR.blen]; exact hR.bufs
  simp only [MS.kst, hR.st, hb]

/-- The kernel state held by a machine, in its globals and memory. -/
theorem ks_of {ms : MS} {ks : KSt} (hok : ms.ok) (hk : ms.kst = ks) : KS ms.g ms.m ks := by
  subst hk
  have hl : (slice ms.m KBUF (ms.g BLEN)).length = ms.g BLEN := slice_length _ _ _
  refine ⟨rfl, hl.symm, ?_, ?_⟩
  · show slice ms.m KBUF (slice ms.m KBUF (ms.g BLEN)).length = slice ms.m KBUF (ms.g BLEN)
    rw [hl]
  · show (slice ms.m KBUF (ms.g BLEN)).length ≤ CAP
    rw [hl]; exact hok.2.2.2.1

theorem pending_eq {g m : Nat → Nat} {ks : KSt} {ys : List Nat} (hR : KRep g m ks ys) (h0 : g OOFF = 0)
    (rp : Option (Nat × Nat)) (md : Mode) : MS.pending ⟨g, m, rp, md⟩ = ys.map u8v := by
  have hs : slice m OUT (g OLEN) = ys := by rw [hR.olen]; exact hR.outs
  simp only [MS.pending, hs, h0, List.drop_zero]

theorem feed_trV (k : KM) : ∀ (s : KSt) (xs : List Val),
    (trV k).feed s xs = ((k.tr.feed s (xs.map byteOf)).1, (k.tr.feed s (xs.map byteOf)).2.map u8v) := by
  intro s xs
  induction xs generalizing s with
  | nil => simp [Tr.feed]
  | cons x xs ih =>
    by_cases hd : k.tr.done s = true
    · simp [Tr.feed, trV, hd]
    · have hdf : k.tr.done s = false := by simpa using hd
      have e1 : (trV k).feed s (x :: xs) = (((trV k).feed ((trV k).step s x).1 xs).1,
          ((trV k).step s x).2 ++ ((trV k).feed ((trV k).step s x).1 xs).2) := by
        simp only [Tr.feed]
        rw [show (trV k).done s = false from hdf]
        rfl
      have e2 : k.tr.feed s (byteOf x :: xs.map byteOf) = ((k.tr.feed (k.tr.step s (byteOf x)).1
          (xs.map byteOf)).1, (k.tr.step s (byteOf x)).2 ++ (k.tr.feed (k.tr.step s (byteOf x)).1
          (xs.map byteOf)).2) := by
        simp only [Tr.feed, hdf, Bool.false_eq_true, ↓reduceIte]
      rw [e1, List.map_cons, e2, ih]
      simp [trV]

theorem flush_trV (k : KM) (s : KSt) : (trV k).flush s = (k.flush.exec 0 s).2.map u8v := rfl

/-- After a write-out step, the machine writes `ys`, then continues as `next` says. -/
theorem rel_wr {s₀ s₂ : St} {ks : KSt} {ys : List Nat} {nxt : Nat} {next : Option KSt}
    (hW : WrPost s₀ s₂ ks ys nxt) (hh : s₀.g INSR = 1 ∧ s₀.g OUTSW = 4 ∧ s₀.g WS = 5)
    (hnext : NextRel ⟨s₂.g, s₂.m, s₂.rp, .ready⟩ next) :
    Rel ⟨s₂.g, s₂.m, s₂.rp, .ready⟩ (.wr (ys.map u8v) next) := by
  have hb : s₂.g BLEN ≤ CAP := by rw [hW.rep.blen]; exact hW.rep.bcap
  have ho : s₂.g OLEN ≤ CAP := by rw [hW.rep.olen]; exact hW.rep.ocap
  refine ⟨⟨?_, ?_, ?_, hb, ho, ?_⟩, rfl, hW.pc, pending_eq hW.rep hW.off _ _, hnext⟩
  · exact hW.hs.1.trans hh.1
  · exact hW.hs.2.1.trans hh.2.1
  · exact hW.hs.2.2.trans hh.2.2
  · show s₂.g OOFF ≤ s₂.g OLEN
    rw [hW.off]; exact Nat.zero_le _

/-! ## `EOI`, and the done branch of `RD` -/

theorem hcEOI {k : KM} {N : Nat} : (pEOI = pWTR ∧ cbEOI k = cbWTR k) ∨ (pEOI = pWTW ∧ cbEOI k = cbWTW) ∨
    (pEOI = pRD ∧ cbEOI k = cbRD k N) ∨ (pEOI = pEOI ∧ cbEOI k = cbEOI k) ∨ (pEOI = pWR ∧ cbEOI k = cbWR) ∨
    (pEOI = pCL ∧ cbEOI k = cbCL) := .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))

/-- `drop-readable`, then the flush, then `YIELD`: the transformer's `eoi` (and `rd` when
done). -/
theorem dropFlush_sound {k : KM} {s s' : St} {ks : KSt} {code : Nat} (hK : KS s.g s.m ks)
    (hin : s.g INSR = 1)
    (h : exec (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) FUEL s = some (.ret code, s')) :
    code = 1 ∧ ∃ r, Silmaril.Wasm.Component.Async.step s.st (.streamDropR 1) = some r ∧ s'.st = r.1 ∧
      WrPost { s with st := r.1 } s' (k.flush.exec 0 ks).1 (k.flush.exec 0 ks).2 0 := by
  have hin' : s.g 6 = 1 := hin
  cases hd : Silmaril.Wasm.Component.Async.step s.st (.streamDropR 1) with
  | none =>
    have hn : exec (.call .dropR [.g INSR] []) FUEL s = none := by
      simp [exec, callBI, E.eval, hin', hd]
    simp only [seqs] at h
    rw [exec_seq, hn] at h
    cases h
  | some r =>
    have e₁ : exec (.call .dropR [.g INSR] []) FUEL s = some (.norm, { s with st := r.1 }) := by
      simp [exec, callBI, E.eval, hin', hd]
    simp only [seqs] at h
    rw [exec_seq_norm e₁] at h
    cases hf : exec (flushOut k) FUEL { s with st := r.1 } with
    | none => rw [exec_seq, hf] at h; cases h
    | some q =>
      obtain ⟨o₂, s₂⟩ := q
      obtain ⟨rfl, hW⟩ := flushOut_sound (s := { s with st := r.1 }) hK hf
      rw [exec_seq_norm hf] at h
      simp only [yield_, exec, Option.some.injEq, Prod.mk.injEq, Out.ret.injEq] at h
      obtain ⟨hc, rfl⟩ := h
      exact ⟨by simpa [E.eval] using hc.symm, r, rfl, hW.st, hW⟩

theorem sim_eoi {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} {ks : KSt} (hR : Rel ms (.eoi ks))
    (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ t', tStep (trV k) N st (.eoi ks) = some (st', t') ∧ Rel ms' t' := by
  obtain ⟨hok, hmode, hpc, hk⟩ := hR
  rw [rstep_ready hmode] at h
  obtain ⟨code, s', hx, hmd, rfl, hg, hm, hrp⟩ := invoke_inv h
  rw [cb_eq, exec_cb hcEOI hpc] at hx
  obtain ⟨rfl, r, hd, hst, hW⟩ := dropFlush_sound (s := st0 ms [0, 0, 0] st) (ks_of hok hk) hok.1 hx
  have hms : ms' = ⟨s'.g, s'.m, s'.rp, .ready⟩ := by
    have hmo : ms'.mode = .ready := by simpa [modeOf] using hmd.symm
    cases ms'; simp_all
  refine ⟨.wr ((trV k).flush ks) none, ?_, ?_⟩
  · show (Silmaril.Wasm.Component.Async.step st (.streamDropR 1)).map
      (fun p => (p.1, TPc.wr ((trV k).flush ks) none)) = some (s'.st, _)
    simp only [st0] at hd
    rw [hd, hst]
    rfl
  · rw [hms, flush_trV]
    exact rel_wr hW ⟨hok.1, hok.2.1, hok.2.2.1⟩ hW.nxt

/-! ## `WR` -/

theorem hcWR {k : KM} {N : Nat} : (pWR = pWTR ∧ cbWR = cbWTR k) ∨ (pWR = pWTW ∧ cbWR = cbWTW) ∨
    (pWR = pRD ∧ cbWR = cbRD k N) ∨ (pWR = pEOI ∧ cbWR = cbEOI k) ∨ (pWR = pWR ∧ cbWR = cbWR) ∨
    (pWR = pCL ∧ cbWR = cbCL) := .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))

/-- The kernel state and the continuation only depend on `GST`, `BLEN`, `NXT` and memory. -/
theorem nextRel_of {ms ms' : MS} {next : Option KSt} (h : NextRel ms next) (h₁ : ms'.g NXT = ms.g NXT)
    (h₂ : ms'.g GST = ms.g GST) (h₃ : ms'.g BLEN = ms.g BLEN) (h₄ : ms'.m = ms.m) : NextRel ms' next := by
  have hk : ms'.kst = ms.kst := by simp only [MS.kst, h₂, h₃, h₄]
  cases next with
  | none => exact h₁.trans h
  | some ks => exact ⟨h₁.trans h.1, hk.trans h.2⟩

theorem kst_of {ms ms' : MS} (h₂ : ms'.g GST = ms.g GST) (h₃ : ms'.g BLEN = ms.g BLEN)
    (h₄ : ms'.m = ms.m) : ms'.kst = ms.kst := by
  simp only [MS.kst, h₂, h₃, h₄]

/-- The pending output after `c` more bytes were written. -/
theorem pending_adv (m : Nat → Nat) (off len c : Nat) :
    (((slice m OUT len).drop (min (off + c) len)).map u8v) = (((slice m OUT len).drop off).map u8v).drop c := by
  rw [← List.map_drop, List.drop_drop]
  by_cases h : off + c ≤ len
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_eq_nil_of_le (by simp [slice_length]),
      List.drop_eq_nil_of_le (by simp [slice_length]; omega)]

/-- The bytes `stream.write` lifts are the pending output. -/
theorem write_items (ms : MS) :
    (slice ms.m (OUT + ms.g OOFF) (ms.g OLEN - ms.g OOFF)).map u8v = ms.pending := by
  simp only [MS.pending, slice_drop]

/-- The resumption after the output is written. -/
theorem wr_done {st : Store} {ms : MS} {next : Option KSt}
    (hok : ms.ok) (hnext : NextRel ms next) (hge : ms.g OLEN ≤ ms.g OOFF) :
    ∃ g', exec cbWR FUEL (st0 ms [0, 0, 0] st) = some (.ret 1, { st0 ms [0, 0, 0] st with g := g' }) ∧
      Rel ⟨g', ms.m, ms.rp, .ready⟩ (TPc.resume next) := by
  have hn := ok_num hok
  have hge' : ms.g 3 ≤ ms.g 4 := hge
  cases next with
  | some ks =>
    have hx : ms.g 5 = 1 := hnext.1
    refine ⟨upd (upd (upd ms.g 4 0) 3 0) 0 0, ?_, ?_⟩
    · simp [cbWR, seqs, exec, E.eval, Bin.eval, st0, hge', hx, lab, yield_, upd_apply]
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, (kst_of (ms := ms) (by simp) (by simp) rfl).trans hnext.2,
        ?_, ?_⟩ <;> simp [upd_apply, hn, CAP]
  | none =>
    have hx : ms.g 5 = 0 := hnext
    refine ⟨upd (upd (upd ms.g 4 0) 3 0) 0 5, ?_, ?_⟩
    · simp [cbWR, seqs, exec, E.eval, Bin.eval, st0, hge', hx, lab, yield_, upd_apply]
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩ <;> simp [upd_apply, hn, CAP]

theorem wr_args (ms : MS) (st : Store) (hok : ms.ok) :
    [E.g OUTSW, .bin .add (.c OUT) (.g OOFF), .bin .sub (.g OLEN) (.g OOFF)].map
      (·.eval (st0 ms [0, 0, 0] st)) = [4, 4096 + ms.g 4, ms.g 3 - ms.g 4] := by
  have hn := ok_num hok
  have h3 : ms.g 3 ≤ 32768 := hn.2.2.2.2.1
  have h4 : ms.g 4 ≤ ms.g 3 := hn.2.2.2.2.2
  have e₄ : (4096 + ms.g 4) % 4294967296 = 4096 + ms.g 4 := Nat.mod_eq_of_lt (by omega)
  have e₃ : (ms.g 3 + (4294967296 - ms.g 4 % 4294967296)) % 4294967296 = ms.g 3 - ms.g 4 := by omega
  simp [E.eval, Bin.eval, st0, hn.2.1, OUT, M32, e₄, e₃]

/-- The rest of the `WR` case after the `stream.write`. -/
def wrRest : S :=
  seqs [.ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTW), .ret waitCode]) .nop,
    onWrite (.l LR), yield_]

/-- `WR` with output pending: the check falls through to the `stream.write`. -/
theorem wr_pre {st : Store} {ms : MS} {o : Out} {s' : St} (hok : ms.ok)
    (hlt : ms.g OOFF < ms.g OLEN) (h : exec cbWR FUEL (st0 ms [0, 0, 0] st) = some (o, s')) :
    (match callBI .streamWrite [4, 4096 + ms.g 4, ms.g 3 - ms.g 4] [LR] (st0 ms [0, 0, 0] st) with
      | some (.norm, s₁) => exec wrRest FUEL s₁
      | r => r) = some (o, s') := by
  have hlt' : ¬ ms.g 3 ≤ ms.g 4 := by simp only [OLEN, OOFF] at hlt; omega
  have e₁ : exec (.ite (.bin .geu (.g OOFF) (.g OLEN)) (seqs [.gset OOFF (.c 0), .gset OLEN (.c 0),
      .ite (.g NXT) (.gset PC (.c pRD)) (.gset PC (.c pCL)), yield_]) .nop) FUEL (st0 ms [0, 0, 0] st) =
      some (.norm, st0 ms [0, 0, 0] st) := by
    simp [exec, E.eval, Bin.eval, st0, hlt', lab]
  simp only [cbWR, seqs] at e₁ h ⊢
  rw [← h, exec_seq_norm e₁, exec_seq, exec, wr_args ms st hok]
  rfl

/-- The state after `stream.write` returned `r`. -/
def sW (ms : MS) (st st₁ : Store) (r : Nat) : St :=
  { st0 ms [0, 0, 0] st with st := st₁, l := upd (st0 ms [0, 0, 0] st).l LR r }

/-- A blocked write: `pc = WTW`, wait. -/
theorem wr_blocked {st st₁ : Store} {ms : MS} {o : Out} {s' : St} (hok : ms.ok)
    (h : exec wrRest FUEL (sW ms st st₁ blocked) = some (o, s')) :
    o = .ret 82 ∧ s'.g = upd ms.g PC pWTW ∧ s'.st = st₁ ∧ s'.m = ms.m ∧ s'.rp = ms.rp := by
  have hn := ok_num hok
  have hbm : blocked % 4294967296 = blocked := by decide
  have he : some (o, s') = some (.ret 82, { sW ms st st₁ blocked with g := upd ms.g PC pWTW }) := by
    rw [← h]
    simp [hbm, wrRest, seqs, exec, E.eval, lab, waitCode, Bin.eval, sW, st0, upd_apply, hn.2.2.1, M32]
  have hos : o = .ret 82 ∧ s' = { sW ms st st₁ blocked with g := upd ms.g PC pWTW } := by simpa using he
  rw [hos.2]
  exact ⟨hos.1, rfl, rfl, rfl, rfl⟩

/-- A write that completed (or failed): the offset advanced by `onWrite`, `YIELD`. -/
theorem wr_done' {st st₁ : Store} {ms : MS} {o : Out} {s' : St} {r : Nat} (hok : ms.ok)
    (hb : r ≠ blocked) (h : exec wrRest FUEL (sW ms st st₁ r) = some (o, s')) :
    o = .ret 1 ∧ s'.g = wrG ms.g r ∧ s'.st = st₁ ∧ s'.m = ms.m ∧ s'.rp = ms.rp := by
  have hc : exec (.ite (.bin .eq (.l LR) (.c blocked)) (.seq (.gset PC (.c pWTW)) (.ret waitCode)) .nop)
      FUEL (sW ms st st₁ r) = some (.norm, sW ms st st₁ r) := by
    simp [exec, E.eval, Bin.eval, sW, upd_apply, hb, lab]
  have h₁ : exec (.seq (onWrite (.l LR)) yield_) FUEL (sW ms st st₁ r) = some (o, s') := by
    rw [← h]
    simp only [wrRest, seqs]
    rw [exec_seq_norm hc]
  obtain ⟨q, hq⟩ : ∃ q, exec (onWrite (.l LR)) FUEL (sW ms st st₁ r) = some q := exec_seq_some h₁
  obtain ⟨hq1, hg₂, hm₂, hst₂, hrp₂⟩ := onWrite_sound (s := sW ms st st₁ r) hok.2.2.2.2.2
    hok.2.2.2.2.1 hq
  have hq' : exec (onWrite (.l LR)) FUEL (sW ms st st₁ r) = some (.norm, q.2) := by rw [hq, ← hq1]
  have he : some (o, s') = some (.ret 1, q.2) := by
    rw [← h₁, exec_seq_norm hq']
    simp [yield_, exec, E.eval, M32]
  have hos : o = .ret 1 ∧ s' = q.2 := by simpa using he
  have hl : (E.l LR).eval (sW ms st st₁ r) = r := by simp [E.eval, sW, upd_apply]
  rw [hos.2, hg₂, hm₂, hst₂, hrp₂, hl]
  exact ⟨hos.1, rfl, rfl, rfl, rfl⟩

/-- The write of the pending output. -/
theorem wr_write {st : Store} {ms : MS} {o : Out} {s' : St} (hok : ms.ok)
    (hlt : ms.g OOFF < ms.g OLEN) (h : exec cbWR FUEL (st0 ms [0, 0, 0] st) = some (o, s')) :
    ∃ st₁ r, Silmaril.Wasm.Component.Async.step st (.streamWrite 4 ms.pending) = some (st₁, .nat r) ∧
      s'.st = st₁ ∧ s'.m = ms.m ∧ s'.rp = ms.rp ∧
      ((r = blocked ∧ o = .ret 82 ∧ s'.g = upd ms.g PC pWTW) ∨ (r ≠ blocked ∧ o = .ret 1 ∧ s'.g = wrG ms.g r)) := by
  have h₁ := wr_pre hok hlt h
  have hitems : (slice ms.m (4096 + ms.g 4) (ms.g 3 - ms.g 4)).map u8v = ms.pending :=
    write_items ms
  obtain ⟨st₁, r, hw, hr⟩ : ∃ st₁ r, Silmaril.Wasm.Component.Async.step st (.streamWrite 4 ms.pending) =
      some (st₁, .nat r) ∧ r < M32 := by
    cases hw : Silmaril.Wasm.Component.Async.step st (.streamWrite 4 ms.pending) with
    | none => simp [callBI, st0, hitems, hw] at h₁
    | some q =>
      obtain ⟨st₁, res⟩ := q
      cases res with
      | nat r => exact if hr : r < M32 then ⟨st₁, r, rfl, hr⟩ else by simp [callBI, st0, hitems, hw, hr] at h₁
      | _ => simp [callBI, st0, hitems, hw] at h₁
  have e₂ : callBI .streamWrite [4, 4096 + ms.g 4, ms.g 3 - ms.g 4] [LR] (st0 ms [0, 0, 0] st) =
      some (.norm, sW ms st st₁ r) := by
    simp [callBI, st0, hitems, hw, hr, sW]
  have h₂ : exec wrRest FUEL (sW ms st st₁ r) = some (o, s') := by simpa only [e₂] using h₁
  by_cases hb : r = blocked
  · obtain ⟨ho, hg, hst, hm, hrp⟩ := wr_blocked hok (hb ▸ h₂)
    exact ⟨st₁, r, hw, hst, hm, hrp, .inl ⟨hb, ho, hg⟩⟩
  · obtain ⟨ho, hg, hst, hm, hrp⟩ := wr_done' hok hb h₂
    exact ⟨st₁, r, hw, hst, hm, hrp, .inr ⟨hb, ho, hg⟩⟩

/-- The machine after an invocation that returned `code` with the state `s'`. -/
theorem ms_eq {ms' : MS} {s' : St} {md : Mode} (hmd : ms'.mode = md) (hg : ms'.g = s'.g)
    (hm : ms'.m = s'.m) (hrp : ms'.rp = s'.rp) : ms' = ⟨s'.g, s'.m, s'.rp, md⟩ := by
  cases ms'
  simp only at hmd hg hm hrp
  rw [hmd, hg, hm, hrp]

theorem mode_of {code : Nat} {md : Mode} (h : modeOf code = some md) (c : Nat) (hc : code = c) :
    modeOf c = some md := hc ▸ h

/-- After a write's result `r`: the transformer's `onWrite`. -/
theorem rel_onWrite {ms : MS} {ys : List Val} {next : Option KSt} (hok : ms.ok) (hpend : ms.pending = ys)
    (hnext : NextRel ms next) (r : Nat) (rp : Option (Nat × Nat)) :
    Rel ⟨wrG ms.g r, ms.m, rp, .ready⟩ (TPc.onWrite ys next r) := by
  have hn := ok_num hok
  have hk : NextRel ⟨wrG ms.g r, ms.m, rp, .ready⟩ next := by
    refine nextRel_of hnext ?_ ?_ ?_ rfl <;> by_cases hc : r % 16 = 0 <;> simp [wrG, hc, upd_apply]
  by_cases hc : r % 16 = 0
  · show Rel ⟨wrG ms.g r, ms.m, rp, .ready⟩ (TPc.onWrite ys next r)
    have hon : TPc.onWrite ys next r = .wr (ys.drop (r / 16)) next := by
      simp [TPc.onWrite, Silmaril.Wasm.Component.Streams.Proc.copyStatus,
        Silmaril.Wasm.Component.Streams.Proc.copyCount, hc]
    have hp : MS.pending ⟨wrG ms.g r, ms.m, rp, .ready⟩ = ys.drop (r / 16) := by
      show ((slice ms.m OUT (wrG ms.g r OLEN)).drop (wrG ms.g r OOFF)).map u8v = ys.drop (r / 16)
      have e₁ : wrG ms.g r OLEN = ms.g OLEN := by simp [wrG, hc, upd_apply]
      have e₂ : wrG ms.g r OOFF = min (ms.g OOFF + r / 16) (ms.g OLEN) := by simp [wrG, hc, upd_apply]
      rw [e₁, e₂, pending_adv]
      exact congrArg (List.drop (r / 16)) hpend
    rw [hon]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, by simp [wrG, hc, upd_apply], hp, hk⟩ <;>
      simp [wrG, hc, upd_apply, hn, CAP]
  · have hon : TPc.onWrite ys next r = .fault := by
      simp [TPc.onWrite, Silmaril.Wasm.Component.Streams.Proc.copyStatus, hc]
    rw [hon]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩ <;> simp [wrG, hc, upd_apply, hn, CAP]

/-- `WR` with the output written: resume. -/
theorem sim_wr_done {k : KM} {N : Nat} {st : Store} {ms ms' : MS} {ys : List Val} {next : Option KSt} {code : Nat}
    {s' : St} (hok : ms.ok) (hpend : ms.pending = ys) (hnext : NextRel ms next)
    (hge : ms.g OLEN ≤ ms.g OOFF) (hx : exec cbWR FUEL (st0 ms [0, 0, 0] st) = some (.ret code, s'))
    (hmd : modeOf code = some ms'.mode) (hg : ms'.g = s'.g) (hm : ms'.m = s'.m) (hrp : ms'.rp = s'.rp) :
    ∃ t', tStep (trV k) N st (.wr ys next) = some (s'.st, t') ∧ Rel ms' t' := by
  have hys : ys = [] := by
    rw [← hpend, MS.pending, List.drop_eq_nil_of_le (by simpa [slice_length] using hge), List.map_nil]
  obtain ⟨g', hx', hR'⟩ := wr_done (st := st) hok hnext hge
  have he : some (Out.ret code, s') = some (.ret 1, { st0 ms [0, 0, 0] st with g := g' }) := by
    rw [← hx, hx']
  have hcs : code = 1 ∧ s' = { st0 ms [0, 0, 0] st with g := g' } := by simpa using he
  have hms : ms' = ⟨g', ms.m, ms.rp, .ready⟩ := by
    rw [ms_eq (by simpa [modeOf, hcs.1] using hmd.symm) hg hm hrp, hcs.2]
    rfl
  refine ⟨TPc.resume next, by rw [hys, hcs.2]; rfl, ?_⟩
  rw [hms]
  exact hR'

theorem nextRel_g {ms : MS} {next : Option KSt} (hnext : NextRel ms next) (g' : Nat → Nat)
    (h₁ : g' GST = ms.g GST) (h₂ : g' BLEN = ms.g BLEN) (h₃ : g' NXT = ms.g NXT) (md : Mode) :
    NextRel ⟨g', ms.m, ms.rp, md⟩ next :=
  nextRel_of hnext h₃ h₁ h₂ rfl

/-- `WR`, the write blocked: wait for it. -/
theorem sim_wr_blocked {k : KM} {N : Nat} {st st₁ : Store} {ms : MS} {y : Val} {ys' : List Val} {next : Option KSt}
    (hok : ms.ok) (hpend : ms.pending = y :: ys') (hnext : NextRel ms next)
    (hw : Silmaril.Wasm.Component.Async.step st (.streamWrite 4 (y :: ys')) = some (st₁, .nat blocked)) :
    tStep (trV k) N st (.wr (y :: ys') next) = some (st₁, .wtW (y :: ys') next) ∧
      Rel ⟨upd ms.g PC pWTW, ms.m, ms.rp, .waiting 5⟩ (.wtW (y :: ys') next) := by
  have hn := ok_num hok
  have hp : MS.pending ⟨upd ms.g PC pWTW, ms.m, ms.rp, .waiting 5⟩ = y :: ys' := by
    simpa [MS.pending, upd_apply] using hpend
  refine ⟨by simp [tStep, hw], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, by simp [upd_apply], hp, nextRel_g hnext _ ?_ ?_ ?_ _⟩ <;>
    simp [upd_apply, hn, CAP]

/-- `WR`, the write returned `r`: the transformer's `onWrite`. -/
theorem sim_wr_ret {k : KM} {N : Nat} {st st₁ : Store} {ms : MS} {y : Val} {ys' : List Val} {next : Option KSt} {r : Nat}
    (hok : ms.ok) (hpend : ms.pending = y :: ys') (hnext : NextRel ms next) (hb : r ≠ blocked)
    (hw : Silmaril.Wasm.Component.Async.step st (.streamWrite 4 (y :: ys')) = some (st₁, .nat r)) :
    tStep (trV k) N st (.wr (y :: ys') next) = some (st₁, TPc.onWrite (y :: ys') next r) ∧
      Rel ⟨wrG ms.g r, ms.m, ms.rp, .ready⟩ (TPc.onWrite (y :: ys') next r) :=
  ⟨by simp [tStep, hw, hb], rel_onWrite hok hpend hnext r ms.rp⟩

theorem sim_wr {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} {ys : List Val} {next : Option KSt}
    (hR : Rel ms (.wr ys next)) (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ t', tStep (trV k) N st (.wr ys next) = some (st', t') ∧ Rel ms' t' := by
  obtain ⟨hok, hmode, hpc, hpend, hnext⟩ := hR
  obtain ⟨code, s', hx, hmd, hst, hg, hm, hrp⟩ := entry hmode hcWR hpc h
  rw [hst]
  by_cases hge : ms.g OLEN ≤ ms.g OOFF
  · exact sim_wr_done hok hpend hnext hge hx hmd hg hm hrp
  · show ∃ t', tStep (trV k) N st (.wr ys next) = some (s'.st, t') ∧ Rel ms' t'
    have hlt : ms.g OOFF < ms.g OLEN := Nat.lt_of_not_le hge
    obtain ⟨st₁, r, hw, hst', hm', hrp', hcase⟩ := wr_write hok hlt hx
    obtain ⟨y, ys', hys⟩ : ∃ y ys', ys = y :: ys' := List.exists_cons_of_ne_nil (by
      have hlt' : ms.g 4 < ms.g 3 := hlt
      rw [← hpend, MS.pending]
      simpa [slice_length] using hlt')
    rw [hys] at hpend ⊢
    rw [hpend] at hw
    rcases hcase with ⟨hb, ho, hg'⟩ | ⟨hb, ho, hg'⟩
    · have hc : code = 82 := by injection ho
      have hms : ms' = ⟨upd ms.g PC pWTW, ms.m, ms.rp, .waiting 5⟩ := by
        rw [ms_eq (by simpa [modeOf, hc] using hmd.symm) hg hm hrp, hg', hm', hrp']
      rw [hms, hst']
      exact ⟨_, sim_wr_blocked hok hpend hnext (hb ▸ hw)⟩
    · have hc : code = 1 := by injection ho
      have hms : ms' = ⟨wrG ms.g r, ms.m, ms.rp, .ready⟩ := by
        rw [ms_eq (by simpa [modeOf, hc] using hmd.symm) hg hm hrp, hg', hm', hrp']
      rw [hms, hst']
      exact ⟨_, sim_wr_ret hok hpend hnext hb hw⟩

/-! ## `WTW` -/

theorem hcWTW {k : KM} {N : Nat} : (pWTW = pWTR ∧ cbWTW = cbWTR k) ∨ (pWTW = pWTW ∧ cbWTW = cbWTW) ∨
    (pWTW = pRD ∧ cbWTW = cbRD k N) ∨ (pWTW = pEOI ∧ cbWTW = cbEOI k) ∨ (pWTW = pWR ∧ cbWTW = cbWR) ∨
    (pWTW = pCL ∧ cbWTW = cbCL) := .inr (.inl ⟨rfl, rfl⟩)

theorem deliver_g (e : Event) (ms : MS) : (deliver e ms).g = ms.g := by
  unfold deliver
  split
  · split <;> rfl
  · rfl

/-- The check of the event: its code is `a` and its index `e`. -/
theorem check_inv {a : Nat} {e : E} {f : Nat} {s s₁ : St} {o : Out} (ha : a < M32)
    (h : exec (.ite (.bin .eq (.l 0) (.c a)) (.ite (.bin .eq (.l 1) e) .nop .unreachable) .unreachable) f s =
      some (o, s₁)) : s.l 0 = a ∧ s.l 1 = e.eval s ∧ o = .norm ∧ s₁ = s := by
  have ha' : a % M32 = a := Nat.mod_eq_of_lt ha
  by_cases h₁ : s.l 0 = a
  · by_cases h₂ : s.l 1 = e.eval s
    · simp [exec, E.eval, Bin.eval, ha', h₁, h₂, lab] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨h₁, h₂, rfl, rfl⟩
    · simp [exec, E.eval, Bin.eval, ha', h₁, h₂, lab] at h
  · simp [exec, E.eval, Bin.eval, ha', h₁, lab] at h

/-- The entry of a `waiting 5` step: a well-formed event, then the case of `pc`. -/
theorem entry_wait {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} {A : S} {n : Nat}
    (hmode : ms.mode = .waiting 5)
    (hA : (n = pWTR ∧ A = cbWTR k) ∨ (n = pWTW ∧ A = cbWTW) ∨ (n = pRD ∧ A = cbRD k N) ∨
      (n = pEOI ∧ A = cbEOI k) ∨ (n = pWR ∧ A = cbWR) ∨ (n = pCL ∧ A = cbCL))
    (hpc : ms.g PC = n) (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ st₁ e, Silmaril.Wasm.Component.Async.step st (.wait 5) = some (st₁, .event e) ∧
      wellFormed e = true ∧ ∃ code s',
        exec A FUEL (st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) = some (.ret code, s') ∧
        modeOf code = some ms'.mode ∧ st' = s'.st ∧ ms'.g = s'.g ∧ ms'.m = s'.m ∧ ms'.rp = s'.rp := by
  obtain ⟨⟨st₁, res⟩, hw⟩ : ∃ q, Silmaril.Wasm.Component.Async.step st (.wait 5) = some q := by
    cases hw : Silmaril.Wasm.Component.Async.step st (.wait 5) with
    | none => simp [rstep, hmode, hw] at h
    | some q => exact ⟨q, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, res = .event e := by
    cases res with
    | event e => exact ⟨e, rfl⟩
    | _ => simp [rstep, hmode, hw] at h
  have hw' : Silmaril.Wasm.Component.Async.step st (.wait 5) = some (st₁, .event e) := by rw [hw, he]
  have hwf : wellFormed e = true := by
    by_contra hn
    simp [rstep, hmode, hw', hn] at h
  have hi : invoke (gen k N).cb [e.code.toNat, e.index, e.payload] st₁ (deliver e ms) =
      some (st', ms') := by simpa [rstep, hmode, hw', hwf] using h
  obtain ⟨code, s', hx, hrest⟩ := invoke_inv hi
  have hdpc : (deliver e ms).g PC = n := by rw [deliver_g]; exact hpc
  have hx' : exec A FUEL (st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.ret code, s') := by
    rw [← exec_cb hA hdpc, ← cb_eq]
    exact hx
  exact ⟨st₁, e, hw', hwf, code, s', hx', hrest⟩

/-- The check at the start of `WTW`: the event is the write's completion. -/
theorem wtw_check {ms : MS} {e : Event} {st₁ : Store} {code : Nat} {s' : St}
    (h : exec cbWTW FUEL (st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.ret code, s')) :
    e.code = .streamWrite ∧
      exec (.seq (onWrite (.l 2)) yield_) FUEL (st0 ms [e.code.toNat, e.index, e.payload] st₁) =
        some (.ret code, s') := by
  simp only [cbWTW, seqs] at h
  obtain ⟨⟨o₁, s₁⟩, hc⟩ := exec_seq_some h
  obtain ⟨hl0, -, ho, hs⟩ := check_inv (by simp [M32]) hc
  have hcode : e.code = .streamWrite := by
    have h3 : e.code.toNat = 3 := hl0
    cases hec : e.code <;> simp_all [EventCode.toNat]
  have hdel : deliver e ms = ms := by simp [deliver, hcode]
  have hc' : exec (.ite (.bin .eq (.l 0) (.c 3)) (.ite (.bin .eq (.l 1) (.g OUTSW)) .nop .unreachable)
      .unreachable) FUEL (st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.norm, st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) := by rw [hc, ho, hs]
  have h' : exec (.seq (onWrite (.l 2)) yield_) FUEL
      (st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) = some (.ret code, s') := by
    rw [← h, exec_seq_norm hc']
  exact ⟨hcode, hdel ▸ h'⟩

/-- `onWrite` then `YIELD` from an invocation state. -/
theorem onWrite_yield {ms : MS} {ps : List Nat} {st₁ : Store} {code : Nat} {s' : St} (hok : ms.ok)
    (h : exec (.seq (onWrite (.l 2)) yield_) FUEL (st0 ms ps st₁) = some (.ret code, s')) :
    code = 1 ∧ s'.g = wrG ms.g ((E.l 2).eval (st0 ms ps st₁)) ∧ s'.st = st₁ ∧ s'.m = ms.m ∧
      s'.rp = ms.rp := by
  obtain ⟨q, hq⟩ := exec_seq_some h
  obtain ⟨hq1, hg₂, hm₂, hst₂, hrp₂⟩ := onWrite_sound (s := st0 ms ps st₁) hok.2.2.2.2.2
    hok.2.2.2.2.1 hq
  have hq' : exec (onWrite (.l 2)) FUEL (st0 ms ps st₁) = some (.norm, q.2) := by rw [hq, ← hq1]
  have he : some (Out.ret code, s') = some (.ret 1, q.2) := by
    rw [← h, exec_seq_norm hq']
    simp [yield_, exec, E.eval, M32]
  have hos : code = 1 ∧ s' = q.2 := by simpa using he
  rw [hos.2]
  exact ⟨hos.1, hg₂, hst₂, hm₂, hrp₂⟩

theorem sim_wtW {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} {ys : List Val} {next : Option KSt}
    (hR : Rel ms (.wtW ys next)) (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ t', tStep (trV k) N st (.wtW ys next) = some (st', t') ∧ Rel ms' t' := by
  obtain ⟨hok, hmode, hpc, hpend, hnext⟩ := hR
  obtain ⟨st₁, e, hw, -, code, s', hx, hmd, hst, hg, hm, hrp⟩ := entry_wait hmode hcWTW hpc h
  obtain ⟨-, hx₁⟩ := wtw_check hx
  obtain ⟨hc1, hg₂, hst₂, hm₂, hrp₂⟩ := onWrite_yield hok hx₁
  have hpl : (E.l 2).eval (st0 ms [e.code.toNat, e.index, e.payload] st₁) = e.payload := rfl
  have hms : ms' = ⟨wrG ms.g e.payload, ms.m, ms.rp, .ready⟩ := by
    rw [ms_eq (by simpa [modeOf, hc1] using hmd.symm) hg hm hrp, hg₂, hm₂, hrp₂, hpl]
  refine ⟨TPc.onWrite ys next e.payload, ?_, ?_⟩
  · rw [hst, hst₂]
    simp [tStep, hw]
  · rw [hms]
    exact rel_onWrite hok hpend hnext e.payload ms.rp

/-! ## Reads -/

theorem kst_of_KS {g m : Nat → Nat} {ks : KSt} (h : KS g m ks) (rp : Option (Nat × Nat)) (md : Mode) :
    MS.kst ⟨g, m, rp, md⟩ = ks := by
  have hb : slice m KBUF (g BLEN) = ks.buf := by rw [h.blen]; exact h.bufs
  simp only [MS.kst, h.st, hb]

/-- After `onRead`: the transformer's `onRead` over values. -/
theorem rel_onRead {k : KM} {s s₂ : St} {ks : KSt} {xs : List Val} {v : Nat}
    (hK : KS s.g s.m ks) (hok : MS.ok ⟨s.g, s.m, s.rp, .ready⟩)
    (hP : ReadPost k s ks (xs.map byteOf) v s₂) :
    Rel ⟨s₂.g, s₂.m, s₂.rp, .ready⟩ (TPc.onRead (trV k) ks v xs) := by
  rcases hP with ⟨hc, rfl⟩ | ⟨hc, -, hW⟩
  · have hon : TPc.onRead (trV k) ks v xs = .eoi ks := by
      simp [TPc.onRead, Silmaril.Wasm.Component.Streams.Proc.copyStatus, hc]
    rw [hon]
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hok
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, by simp [upd_apply], ?_⟩
    · simpa [upd_apply] using h₁
    · simpa [upd_apply] using h₂
    · simpa [upd_apply] using h₃
    · simpa [upd_apply] using h₄
    · simpa [upd_apply] using h₅
    · simpa [upd_apply] using h₆
    · exact (kst_of (ms := ⟨s.g, s.m, s.rp, .ready⟩) (by simp) (by simp) rfl).trans
        (kst_of_KS hK _ _)
  · have hon : TPc.onRead (trV k) ks v xs =
        .wr ((k.tr.feed ks (xs.map byteOf)).2.map u8v) (some (k.tr.feed ks (xs.map byteOf)).1) := by
      simp [TPc.onRead, Silmaril.Wasm.Component.Streams.Proc.copyStatus, hc, feed_trV]
    rw [hon]
    exact rel_wr hW ⟨hok.1, hok.2.1, hok.2.2.1⟩ ⟨hW.nxt, kst_eq hW.rep _ _⟩

/-- What a `stream.read` delivers at once. -/
theorem streamRead_res {st st' : Store} {r n p : Nat} {xs : List Val}
    (h : Silmaril.Wasm.Component.Async.step st (.streamRead r n) = some (st', .read p xs)) :
    xs.length ≤ n ∧ p ≤ 16 * n + 2 ∧ (p % 16 = 0 → p / 16 = xs.length) := by
  simp only [Silmaril.Wasm.Component.Async.step, Silmaril.Wasm.Component.Async.streamRead] at h
  split at h
  · split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq, Res.read.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      simp only [Silmaril.Wasm.Component.Async.packCopy, Silmaril.Wasm.Component.Async.CopyResult.toNat,
        List.length_take]
      omega
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq, Res.read.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        simp [Silmaril.Wasm.Component.Async.packCopy, Silmaril.Wasm.Component.Async.CopyResult.toNat]
      · cases h
  · cases h

theorem wellFormed_inv {e : Event} (h : wellFormed e = true) :
    e.payload < M32 ∧ e.index < M32 ∧ e.items.length ≤ 256 ∧
      (e.code = .streamRead → e.payload % 16 = 0 → e.payload / 16 = e.items.length) := by
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  refine ⟨h₁, h₂, h₃, fun hc hp => ?_⟩
  rcases h₄ with (h₄ | h₄) | h₄
  · exact absurd hc h₄
  · exact absurd hp h₄
  · exact h₄

/-! ## `RD` -/

theorem hcRD {k : KM} {N : Nat} : (pRD = pWTR ∧ cbRD k N = cbWTR k) ∨ (pRD = pWTW ∧ cbRD k N = cbWTW) ∨
    (pRD = pRD ∧ cbRD k N = cbRD k N) ∨ (pRD = pEOI ∧ cbRD k N = cbEOI k) ∨
    (pRD = pWR ∧ cbRD k N = cbWR) ∨ (pRD = pCL ∧ cbRD k N = cbCL) := .inr (.inr (.inl ⟨rfl, rfl⟩))

/-- A case that returns: the sequence returns what it returns. -/
theorem exec_seq_ite_ret {c : E} {A rest : S} {f : Nat} {s s' : St} {code : Nat} (hc : c.eval s ≠ 0)
    (hA : OutIn IsRet A) (h : exec (.seq (.ite c A .nop) rest) f s = some (.ret code, s')) :
    exec A f s = some (.ret code, s') := by
  rw [exec_seq, exec_ite] at h
  simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte] at h
  cases hx : exec A f s with
  | none => rw [hx] at h; cases h
  | some q =>
    obtain ⟨o, s₁⟩ := q
    obtain ⟨v, rfl⟩ := hA f s o s₁ hx
    rw [hx] at h
    exact h

theorem exec_seq_ite_skip {c : E} {A rest : S} {f : Nat} {s : St} (hc : c.eval s = 0) :
    exec (.seq (.ite c A .nop) rest) f s = exec rest f s := by
  rw [exec_seq, exec_ite]
  simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte]
  rfl

/-- The state after `local.set LB 0` at the start of `RD`. -/
def sA (ms : MS) (st : Store) : St := { st0 ms [0, 0, 0] st with l := upd (locals [0, 0, 0]) LB 0 }

theorem rd_done {k : KM} {N : Nat} {st : Store} {ms : MS} {ks : KSt} {code : Nat} {s' : St}
    (hok : ms.ok) (hK : KS ms.g ms.m ks) (hd : k.tr.done ks = true)
    (hx : exec (.seq (.ite (cE k.done) (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) .nop)
      (seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
        .ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTR), .ret waitCode]) .nop,
        onRead k (.l LR), yield_])) FUEL (sA ms st) = some (.ret code, s')) :
    ∃ t', tStep (trV k) N st (.rd ks) = some (s'.st, t') ∧ code = 1 ∧ Rel ⟨s'.g, s'.m, s'.rp, .ready⟩ t' := by
  have hc : (cE k.done).eval (sA ms st) ≠ 0 :=
    (done_eval k (s := sA ms st) hK.st hK.blen (by simp [sA, upd_apply])).mpr hd
  have hret : OutIn IsRet (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) :=
    outIn_seqs_ret (as := [_, _]) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact nr_of_norm (outIn_call _ _ _)
      · exact outIn_flushOut k) outIn_yield
  obtain ⟨rfl, r, hdr, hst, hW⟩ := dropFlush_sound (s := sA ms st) hK hok.1 (exec_seq_ite_ret hc hret hx)
  refine ⟨.wr ((trV k).flush ks) none, ?_, rfl, ?_⟩
  · have hdone : (trV k).done ks = true := hd
    simp only [tStep, hdone, ↓reduceIte]
    rw [show (sA ms st).st = st from rfl] at hdr
    rw [hdr, hst]
    rfl
  · rw [flush_trV]
    exact rel_wr hW ⟨hok.1, hok.2.1, hok.2.2.1⟩ hW.nxt

/-- The input bytes written at `IN` leave the kernel's buffer alone. -/
theorem KS.writeIn {g m : Nat → Nat} {ks : KSt} (h : KS g m ks) {bs : List Nat} (hb : bs.length ≤ 256) :
    KS g (writeBytes m IN bs) ks :=
  ⟨h.st, h.blen, by
    rw [slice_writeBytes_out (.inl (by simp [IN, KBUF]; omega))]
    exact h.bufs, h.bcap⟩

/-- The state after a read that delivered `xs` at once. -/
def sB (ms : MS) (st₁ : Store) (p : Nat) (xs : List Val) (st : Store) : St :=
  { sA ms st with st := st₁, m := writeBytes (sA ms st).m IN (xs.map byteOf), l := upd (sA ms st).l LR p }

/-- A statement that finished normally, then `YIELD`. -/
theorem yield_after {X : S} {f : Nat} {s s₂ s' : St} {code : Nat} (hX : exec X f s = some (.norm, s₂))
    (h : exec (.seq X yield_) f s = some (.ret code, s')) : code = 1 ∧ s' = s₂ := by
  have he : some (Out.ret code, s') = some (.ret 1, s₂) := by
    rw [← h, exec_seq_norm hX]
    simp [yield_, exec, E.eval, M32]
  simpa using he

/-- The rest of `RD` after the `stream.read`. -/
def rdRest (k : KM) : S :=
  seqs [.ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTR), .ret waitCode]) .nop,
    onRead k (.l LR), yield_]

/-- `RD`, not done: the `stream.read` of up to `N` bytes into `IN`. -/
theorem rd_pre {k : KM} {N : Nat} {st : Store} {ms : MS} {code : Nat} {s' : St} (hN : N ≤ 256)
    (hok : ms.ok)
    (hx : exec (seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
        .ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTR), .ret waitCode]) .nop,
        onRead k (.l LR), yield_]) FUEL (sA ms st) = some (.ret code, s')) :
    (match callBI .streamRead [1, IN, N] [LR] (sA ms st) with
      | some (.norm, s₁) => exec (rdRest k) FUEL s₁
      | r => r) = some (.ret code, s') := by
  have hn := ok_num hok
  have hargs : [E.g INSR, .c IN, .c N].map (·.eval (sA ms st)) = [1, IN, N] := by
    have hN' : N < 4294967296 := by omega
    simp [E.eval, sA, st0, hn.1, hN', IN, M32]
  simp only [seqs] at hx
  rw [exec_seq, exec, hargs] at hx
  exact hx

/-- A read that delivered `xs` at once: the transformer's `onRead`. -/
theorem rd_completed {k : KM} {N : Nat} {st st₁ : Store} {ms : MS} {ks : KSt} {code p : Nat}
    {xs : List Val} {s' : St} (hN : N ≤ 256) (hok : ms.ok) (hK : KS ms.g ms.m ks) (h0 : ms.g OLEN = 0)
    (hoff : ms.g OOFF = 0) (hd : k.tr.done ks = false)
    (hr : Silmaril.Wasm.Component.Async.step st (.streamRead 1 N) = some (st₁, .read p xs))
    (hx : exec (rdRest k) FUEL (sB ms st₁ p xs st) = some (.ret code, s')) :
    tStep (trV k) N st (.rd ks) = some (s'.st, TPc.onRead (trV k) ks p xs) ∧ code = 1 ∧
      Rel ⟨s'.g, s'.m, s'.rp, .ready⟩ (TPc.onRead (trV k) ks p xs) := by
  obtain ⟨hlen, hp, hcnt⟩ := streamRead_res hr
  have hpb : p ≠ blocked := by simp [blocked]; omega
  have hcb : (E.bin .eq (.l LR) (.c blocked)).eval (sB ms st₁ p xs st) = 0 := by
    simp [E.eval, Bin.eval, sB, upd_apply, hpb]
  have hx₁ : exec (.seq (onRead k (.l LR)) yield_) FUEL (sB ms st₁ p xs st) = some (.ret code, s') := by
    have e := exec_seq_ite_skip (A := seqs [.gset PC (.c pWTR), .ret waitCode])
      (rest := .seq (onRead k (.l LR)) yield_) (f := FUEL) hcb
    rw [← e]
    simpa only [rdRest, seqs] using hx
  have hKb : KS (sB ms st₁ p xs st).g (sB ms st₁ p xs st).m ks := by
    simpa [sB, sA, st0] using KS.writeIn hK (bs := xs.map byteOf) (by simp; omega)
  have hpl : (E.l LR).eval (sB ms st₁ p xs st) = p := by simp [E.eval, sB, upd_apply]
  obtain ⟨⟨o₂, s₂⟩, ho⟩ := exec_seq_some hx₁
  obtain ⟨ho₂, hP⟩ := onRead_sound hKb (by simpa [sB, sA, st0] using h0) (by simpa [sB, sA, st0] using hoff)
    (show slice (sB ms st₁ p xs st).m IN (xs.map byteOf).length = xs.map byteOf from slice_writeBytes _ _ _)
    (by simp; omega) (by rw [hpl]; intro h; simpa using hcnt h) ho
  have hP' : ReadPost k (sB ms st₁ p xs st) ks (xs.map byteOf) p s₂ := hpl ▸ hP
  have hos := yield_after (ho₂ ▸ ho) hx₁
  have hst₂ : s₂.st = st₁ := by
    rcases hP' with ⟨-, hs⟩ | ⟨-, -, hW⟩
    · rw [hs]; rfl
    · exact hW.st
  rw [hos.2]
  exact ⟨by simp [tStep, show (trV k).done ks = false from hd, hr, hst₂], hos.1,
    rel_onRead hKb (show MS.ok ⟨ms.g, _, _, _⟩ from hok) hP'⟩

/-- The state after a blocked read. -/
def sBl (ms : MS) (st st₁ : Store) : St := { sA ms st with st := st₁, rp := some (1, IN), l := upd (sA ms st).l LR blocked }

/-- A blocked read: `pc = WTR`, wait. -/
theorem rd_blocked {k : KM} {st st₁ : Store} {ms : MS} {ks : KSt} {code : Nat} {s' : St}
    (hok : ms.ok) (hK : KS ms.g ms.m ks) (h0 : ms.g OLEN = 0) (hoff : ms.g OOFF = 0)
    (hx : exec (rdRest k) FUEL (sBl ms st st₁) = some (.ret code, s')) :
    code = 82 ∧ Rel ⟨s'.g, s'.m, s'.rp, .waiting 5⟩ (.wtR ks) ∧ s'.st = st₁ := by
  have hn := ok_num hok
  have hbm : blocked % 4294967296 = blocked := by decide
  have he : some (Out.ret code, s') = some (.ret 82, { sBl ms st st₁ with g := upd ms.g PC pWTR }) := by
    rw [← hx]
    simp [hbm, rdRest, seqs, exec, E.eval, lab, waitCode, Bin.eval, sBl, sA, st0, upd_apply, hn.2.2.1, M32]
  have hos : code = 82 ∧ s' = { sBl ms st st₁ with g := upd ms.g PC pWTR } := by simpa using he
  have hk' : MS.kst ⟨upd ms.g 0 1, ms.m, some (1, IN), .waiting 5⟩ = ks :=
    (kst_of (ms := ⟨ms.g, ms.m, ms.rp, .ready⟩) (by simp) (by simp) rfl).trans (kst_of_KS hK _ _)
  refine ⟨hos.1, ?_, by rw [hos.2]; rfl⟩
  rw [hos.2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, by simp [upd_apply], hk',
    by simpa [upd_apply] using h0, by simpa [upd_apply] using hoff, rfl⟩ <;>
    simp [upd_apply, hn, CAP]

theorem rd_read {k : KM} {N : Nat} {st : Store} {ms : MS} {ks : KSt} {code : Nat} {s' : St}
    (hN : N ≤ 256) (hok : ms.ok) (hK : KS ms.g ms.m ks) (h0 : ms.g OLEN = 0) (hoff : ms.g OOFF = 0)
    (hd : k.tr.done ks = false)
    (hx : exec (seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
        .ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTR), .ret waitCode]) .nop,
        onRead k (.l LR), yield_]) FUEL (sA ms st) = some (.ret code, s')) :
    ∃ t' md, tStep (trV k) N st (.rd ks) = some (s'.st, t') ∧ modeOf code = some md ∧
      Rel ⟨s'.g, s'.m, s'.rp, md⟩ t' := by
  have hx₁ := rd_pre hN hok hx
  have hsA : (sA ms st).st = st := rfl
  have hdone : (trV k).done ks = false := hd
  cases hr : Silmaril.Wasm.Component.Async.step st (.streamRead 1 N) with
  | none => simp [callBI, hsA, hr] at hx₁
  | some q =>
    show ∃ t' md, tStep (trV k) N st (.rd ks) = some (s'.st, t') ∧ modeOf code = some md ∧
      Rel ⟨s'.g, s'.m, s'.rp, md⟩ t'
    obtain ⟨st₁, res⟩ := q
    cases res with
    | read p xs =>
      have hpM : p < M32 := by have := (streamRead_res hr).2.1; simp [M32]; omega
      have h₂ : exec (rdRest k) FUEL (sB ms st₁ p xs st) = some (.ret code, s') := by
        simpa [callBI, hsA, hr, hpM, sB] using hx₁
      obtain ⟨ht, hc, hR⟩ := rd_completed hN hok hK h0 hoff hd hr h₂
      exact ⟨_, .ready, ht, by rw [hc]; rfl, hR⟩
    | nat r =>
      by_cases hb : r = blocked
      · have h₂ : exec (rdRest k) FUEL (sBl ms st st₁) = some (.ret code, s') := by
          simpa [callBI, hsA, hr, hb, sBl] using hx₁
        obtain ⟨hc, hR, hst⟩ := rd_blocked hok hK h0 hoff h₂
        exact ⟨.wtR ks, .waiting 5, by simp [tStep, hdone, hr, hb, hst], by rw [hc]; rfl, hR⟩
      · simp [callBI, hsA, hr, hb] at hx₁
    | _ => simp [callBI, hsA, hr] at hx₁

theorem sim_rd {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} {ks : KSt} (hN : N ≤ 256)
    (hR : Rel ms (.rd ks)) (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ t', tStep (trV k) N st (.rd ks) = some (st', t') ∧ Rel ms' t' := by
  obtain ⟨hok, hmode, hpc, hk, h0, hoff⟩ := hR
  have hK : KS ms.g ms.m ks := ks_of hok hk
  obtain ⟨code, s', hx, hmd, hst, hg, hm, hrp⟩ := entry hmode hcRD hpc h
  have e₀ : exec (.lset LB (.c 0)) FUEL (st0 ms [0, 0, 0] st) = some (.norm, sA ms st) := rfl
  have hx₁ : exec (.seq (.ite (cE k.done) (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) .nop)
      (seqs [.call .streamRead [.g INSR, .c IN, .c N] [LR],
        .ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTR), .ret waitCode]) .nop,
        onRead k (.l LR), yield_])) FUEL (sA ms st) = some (.ret code, s') := by
    rw [← hx, ← exec_seq_norm e₀]
    rfl
  rw [hst]
  by_cases hd : k.tr.done ks = true
  · obtain ⟨t', ht, hc, hR'⟩ := rd_done (N := N) hok hK hd hx₁
    exact ⟨t', ht, by rw [ms_eq (by simpa [modeOf, hc] using hmd.symm) hg hm hrp]; exact hR'⟩
  · have hc : (cE k.done).eval (sA ms st) = 0 :=
      Classical.not_not.mp fun hne => hd ((done_eval k (s := sA ms st) hK.st hK.blen
        (by simp [sA, upd_apply])).mp hne)
    obtain ⟨t', md, ht, hmd', hR'⟩ :=
      rd_read hN hok hK h0 hoff (by simpa using hd) (by rw [← exec_seq_ite_skip hc]; exact hx₁)
    have hmo : ms'.mode = md := Option.some.inj (hmd.symm.trans hmd')
    exact ⟨t', ht, by rw [ms_eq hmo hg hm hrp]; exact hR'⟩

/-! ## `WTR` -/

theorem hcWTR {k : KM} {N : Nat} : (pWTR = pWTR ∧ cbWTR k = cbWTR k) ∨ (pWTR = pWTW ∧ cbWTR k = cbWTW) ∨
    (pWTR = pRD ∧ cbWTR k = cbRD k N) ∨ (pWTR = pEOI ∧ cbWTR k = cbEOI k) ∨
    (pWTR = pWR ∧ cbWTR k = cbWR) ∨ (pWTR = pCL ∧ cbWTR k = cbCL) := .inl ⟨rfl, rfl⟩

/-- The memory and the pending read after the read's completion is delivered. -/
def dms (e : Event) (ms : MS) : MS := { ms with m := writeBytes ms.m IN (e.items.map byteOf), rp := none }

/-- The check at the start of `WTR`: the event is the read's completion, which `deliver` copied
into the input buffer. -/
theorem wtr_check {k : KM} {ms : MS} {e : Event} {st₁ : Store} {code : Nat} {s' : St} (hok : ms.ok)
    (hrp0 : ms.rp = some (1, IN))
    (h : exec (cbWTR k) FUEL (st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.ret code, s')) :
    e.code = .streamRead ∧
      exec (.seq (onRead k (.l 2)) yield_) FUEL (st0 (dms e ms) [e.code.toNat, e.index, e.payload] st₁) =
        some (.ret code, s') := by
  simp only [cbWTR, seqs] at h
  obtain ⟨⟨o₁, s₁⟩, hc⟩ := exec_seq_some h
  obtain ⟨hl0, hl1, ho, hs⟩ := check_inv (by simp [M32]) hc
  have hcode : e.code = .streamRead := by
    have h2 : e.code.toNat = 2 := hl0
    cases hec : e.code <;> simp_all [EventCode.toNat]
  have hidx : e.index = 1 := by
    have h1 : e.index = (deliver e ms).g INSR := hl1
    rw [h1, deliver_g]
    exact hok.1
  have hdel : deliver e ms = dms e ms := by simp [deliver, dms, hcode, hrp0, hidx, IN]
  have hc' : exec (.ite (.bin .eq (.l 0) (.c 2)) (.ite (.bin .eq (.l 1) (.g INSR)) .nop .unreachable)
      .unreachable) FUEL (st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.norm, st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) := by rw [hc, ho, hs]
  have h' : exec (.seq (onRead k (.l 2)) yield_) FUEL
      (st0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) = some (.ret code, s') := by
    rw [← h, exec_seq_norm hc']
  exact ⟨hcode, hdel ▸ h'⟩

/-- `onRead` of the delivered items, then `YIELD`. -/
theorem wtr_read {k : KM} {ms : MS} {ks : KSt} {e : Event} {st₁ : Store} {code : Nat} {s' : St}
    (hK : KS ms.g ms.m ks) (h0 : ms.g OLEN = 0) (hoff : ms.g OOFF = 0) (hlen : e.items.length ≤ 256)
    (hcnt : e.payload % 16 = 0 → e.payload / 16 = e.items.length)
    (h : exec (.seq (onRead k (.l 2)) yield_) FUEL (st0 (dms e ms) [e.code.toNat, e.index, e.payload] st₁) =
      some (.ret code, s')) :
    code = 1 ∧ s'.st = st₁ ∧
      ReadPost k (st0 (dms e ms) [e.code.toNat, e.index, e.payload] st₁) ks (e.items.map byteOf) e.payload s' := by
  have hKb : KS (dms e ms).g (dms e ms).m ks := KS.writeIn hK (by simpa using hlen)
  have hin : slice (dms e ms).m IN (e.items.map byteOf).length = e.items.map byteOf :=
    slice_writeBytes _ _ _
  have hpl : (E.l 2).eval (st0 (dms e ms) [e.code.toNat, e.index, e.payload] st₁) = e.payload := rfl
  obtain ⟨⟨o₂, s₂⟩, ho⟩ := exec_seq_some h
  obtain ⟨ho₂, hP⟩ := onRead_sound (s := st0 (dms e ms) _ st₁) hKb h0 hoff hin (by simpa using hlen)
    (by rw [hpl]; intro hz; simpa using hcnt hz) ho
  have hP' : ReadPost k (st0 (dms e ms) [e.code.toNat, e.index, e.payload] st₁) ks
      (e.items.map byteOf) e.payload s₂ := hpl ▸ hP
  have hos := yield_after (ho₂ ▸ ho) h
  have hst₂ : s₂.st = st₁ := by
    rcases hP' with ⟨-, hs⟩ | ⟨-, -, hW⟩
    · rw [hs]; rfl
    · exact hW.st
  rw [hos.2]
  exact ⟨hos.1, hst₂, hP'⟩

theorem sim_wtR {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} {ks : KSt}
    (hR : Rel ms (.wtR ks)) (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ t', tStep (trV k) N st (.wtR ks) = some (st', t') ∧ Rel ms' t' := by
  obtain ⟨hok, hmode, hpc, hk, h0, hoff, hrp0⟩ := hR
  have hK : KS ms.g ms.m ks := ks_of hok hk
  obtain ⟨st₁, e, hw, hwf, code, s', hx, hmd, hst, hg, hm, hrp⟩ := entry_wait hmode hcWTR hpc h
  obtain ⟨-, -, hlen, hcnt⟩ := wellFormed_inv hwf
  obtain ⟨hcode, hx₁⟩ := wtr_check hok hrp0 hx
  obtain ⟨hc1, hst₂, hP⟩ := wtr_read hK h0 hoff hlen (hcnt hcode) hx₁
  refine ⟨TPc.onRead (trV k) ks e.payload e.items, by rw [hst, hst₂]; simp [tStep, hw], ?_⟩
  rw [ms_eq (by simpa [modeOf, hc1] using hmd.symm) hg hm hrp]
  have hKb : KS (st0 (dms e ms) [e.code.toNat, e.index, e.payload] st₁).g
      (st0 (dms e ms) [e.code.toNat, e.index, e.payload] st₁).m ks := KS.writeIn hK (by simpa using hlen)
  exact rel_onRead hKb (show MS.ok ⟨ms.g, _, _, _⟩ from hok) hP

/-! ## The other states -/

theorem sim_fault {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} (hR : Rel ms .fault)
    (h : rstep (gen k N) st ms = some (st', ms')) : False := by
  obtain ⟨-, hmode, hpc⟩ := hR
  rw [rstep_ready hmode] at h
  obtain ⟨code, s', hx, -⟩ := invoke_inv h
  rw [cb_eq, exec_callback_other hpc] at hx
  cases hx

theorem sim_fin {k : KM} {N : Nat} {st st' : Store} {ms ms' : MS} (hR : Rel ms .fin)
    (h : rstep (gen k N) st ms = some (st', ms')) : False := by
  have hm : ms.mode = .exited := hR
  simp [rstep, hm] at h

/-- **The simulation**: every step of the callback runtime on the generated module, from a
machine related to `t`, is a step of `tStep (trV k) N` from `t` with the same store. -/
theorem step_sound {k : KM} {N : Nat} (hN : N ≤ 256) {st st' : Store} {ms ms' : MS} {t : TPc KSt}
    (hR : Rel ms t) (h : rstep (gen k N) st ms = some (st', ms')) :
    ∃ t', tStep (trV k) N st t = some (st', t') ∧ Rel ms' t' := by
  cases t with
  | rd ks => exact sim_rd hN hR h
  | wtR ks => exact sim_wtR hR h
  | eoi ks => exact sim_eoi hR h
  | wr ys next => exact sim_wr hR h
  | wtW ys next => exact sim_wtW hR h
  | cl => exact sim_cl hR h
  | fin => exact (sim_fin hR h).elim
  | fault => exact (sim_fault hR h).elim

end Silmaril.Proofs.Wasm.JcoTool.KCore
