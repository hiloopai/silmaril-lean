module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Quiet

/-!
# The resting state of the open pipe

**`term_got`**: in an open run that cannot step, the sink holds `(trV k).runP xs`. See
`KLive.Quiet` for the argument. `Rest` collects what the network's invariants say about the final
state (`rest_mk`); one lemma per state of the module's output reads it (`rest_closed`, `rest_idle`,
`rest_dead`, `rest_busy`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (Network NSt RV OS rh wh NStep Node Sys)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Wasm.JcoTool.KRead (PSys PStep PSteps m₀ Closed FlushNil)
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Proofs.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.JcoTool.KNet
open Silmaril.Proofs.Wasm.Component.Streams.Net (Coh Inv RInv WInv ChanInv wOut NodeInv OInv)
open Silmaril.Proofs.Wasm.Component.Streams.Live (StPos chan_in chan_out busy_open write_ok
  dstep_write_eq wait_wh_ok)

variable {xs : List Val} {k : KM} {N : Nat}

theorem view_closed {o : OS} {d : Bool} (h : o.view = .closed d) : o = .closed d := by
  cases o <;> simp_all [OS.view]

/-- Silmaril.Wasm.Component.Streams.Net.Out of an output: its view is `closed` only if it is closed. -/
theorem out_closed {o : Silmaril.Wasm.Component.Streams.Net.Out} {d : Bool} (h : o.st.view = .closed d) : o.st = .closed d :=
  view_closed h

/-- **What the invariants say about a resting open pipe**, with the source's output `o0` and the
module's output `o1`. -/
structure Rest (xs : List Val) (k : KM) (N : Nat) (s : Sys (pM xs k N).net) (o0 o1 : Silmaril.Wasm.Component.Streams.Net.Out) : Prop where
  ch0 : ChanInv o0.st.view o0.ack (s.ns (i1 xs k N)).rd (s.ns (i1 xs k N)).got (s.st.chans (rh 0))
  ch1 : ChanInv o1.st.view o1.ack (s.ns (i2 xs k N)).rd (s.ns (i2 xs k N)).got (s.st.chans (rh 1))
  O0 : OInv xs (s.ns (i0 xs k N)).rd.flushed o0
  O1 : OInv ((s.ns (i1 xs k N)).outSoFar (trV k)) (s.ns (i1 xs k N)).rd.flushed o1
  hs1 : (s.ns (i1 xs k N)).s = ((trV k).feed (trV k).init (s.ns (i1 xs k N)).got).1
  stop1 : (s.ns (i1 xs k N)).rd = .gone false → (trV k).done (s.ns (i1 xs k N)).s = true ∨
    ((s.ns (i1 xs k N)).outs ≠ [] ∧ ∀ o ∈ (s.ns (i1 xs k N)).outs, o.isDead)
  ho1 : (s.ns (i1 xs k N)).outs = [o1]
  snk : ((s.ns (i2 xs k N)).rd = .busy ∧ (s.st.chans (rh 1)).r.ev = none) ∨
    (s.ns (i2 xs k N)).rd = .gone true
  ngf : (s.ns (i2 xs k N)).rd ≠ .gone false
  nclosed : ∀ d, o0.st ≠ .closed d
  srcIdle : ∀ q a, o0 = ⟨.idle q, a⟩ → q = []
  srcBusy : ∀ ys q a, o0 = ⟨.busy ys q, a⟩ → (s.st.chans (rh 0)).w.ev = none
  pos : StPos s.st

section
variable {s : Sys (pM xs k N).net} {o0 : Silmaril.Wasm.Component.Streams.Net.Out}

/-- With the module's output dead, the sink would have gone before the end: impossible. -/
theorem rest_dead {a : List Val} (R : Rest xs k N s o0 ⟨.dead, a⟩) : False :=
  R.ngf (R.ch1.2.2.1 (.inl rfl))

theorem rest_closed_true {a : List Val} (R : Rest xs k N s o0 ⟨.closed true, a⟩) : False :=
  R.ngf (R.ch1.2.2.1 (.inr rfl))

/-- With the module writing and the sink reading, nothing pending: impossible (`busy_open`). -/
theorem rest_busy {p q a : List Val} (R : Rest xs k N s o0 ⟨.busy p q, a⟩)
    (hq : (s.st.chans (rh 1)).w.ev = none) : False := by
  have hW1 : WInv (.busy p) a (s.st.chans (rh 1)) := R.ch1.1
  rcases R.snk with ⟨hr, hev⟩ | hgone
  · obtain ⟨-, hrc⟩ := busy_open hW1 (R.pos (rh 1)) (by rw [hq]; rfl)
    have hR1 : RInv .busy (s.ns (i2 xs k N)).got (s.st.chans (rh 1)) := hr ▸ R.ch1.2.1
    have hsome : (s.st.chans (rh 1)).r.ev.isSome := hR1.2.2.2.2.2.2.1 hW1.1 hrc
    simp [hev] at hsome
  · have h : (OS.busy p q).view = .closed false := R.ch1.2.2.2 (.inr hgone)
    simp [OS.view] at h

/-- The module's input took everything the source offered. -/
theorem rest_src_all {o1 : Silmaril.Wasm.Component.Streams.Net.Out} (R : Rest xs k N s o0 o1) (hbusy : (s.ns (i1 xs k N)).rd = .busy)
    (hq : (s.st.chans (rh 0)).r.ev = none) : (s.st.chans (rh 0)).sent = xs := by
  have hR0 : RInv .busy (s.ns (i1 xs k N)).got (s.st.chans (rh 0)) := hbusy ▸ R.ch0.2.1
  obtain ⟨st0, a0⟩ := o0
  cases st0 with
  | idle q0 =>
    have hq0 : q0 = [] := R.srcIdle q0 a0 rfl
    have hO : a0 ++ q0 = xs := R.O0
    have hs : (s.st.chans (rh 0)).sent = a0 := R.ch0.1.2.2.2.1
    rw [hs, ← hO, hq0, List.append_nil]
  | busy ys q0 =>
    have hW0 : WInv (.busy ys) a0 (s.st.chans (rh 0)) := R.ch0.1
    obtain ⟨-, hrc⟩ := busy_open hW0 (R.pos (rh 0)) (by rw [R.srcBusy ys q0 a0 rfl]; rfl)
    have hsome : (s.st.chans (rh 0)).r.ev.isSome := hR0.2.2.2.2.2.2.1 hW0.1 hrc
    simp [hq] at hsome
  | dead =>
    have h : (s.ns (i1 xs k N)).rd = .gone false := R.ch0.2.2.1 (.inl rfl)
    cases hbusy.symm.trans h
  | closed d => exact absurd rfl (R.nclosed d)

/-- **The module waits for its read, its output written**: the sink holds `runP xs`. -/
theorem rest_idle {a : List Val} (R : Rest xs k N s o0 ⟨.idle [], a⟩)
    (hbusy : (s.ns (i1 xs k N)).rd = .busy) (hq : (s.st.chans (rh 0)).r.ev = none) :
    (s.ns (i2 xs k N)).got = (trV k).runP xs := by
  have hW1 : WInv .idle a (s.st.chans (rh 1)) := R.ch1.1
  have hr2 : (s.ns (i2 xs k N)).rd = .busy ∧ (s.st.chans (rh 1)).r.ev = none :=
    R.snk.resolve_right fun hgone => by
      have h : (OS.idle []).view = .closed false := R.ch1.2.2.2 (.inr hgone)
      simp [OS.view] at h
  have hR1 : RInv .busy (s.ns (i2 xs k N)).got (s.st.chans (rh 1)) := hr2.1 ▸ R.ch1.2.1
  have hgot : (s.ns (i2 xs k N)).got = a := by
    have h1 : (s.st.chans (rh 1)).sent = (s.ns (i2 xs k N)).got := by
      rw [hR1.1, hR1.2.2.2.1 hr2.2, List.append_nil]
    exact h1.symm.trans hW1.2.2.2.1
  have hack : a = (trV k).runP (s.ns (i1 xs k N)).got := by
    have h : a ++ [] = (s.ns (i1 xs k N)).outSoFar (trV k) := R.O1
    simpa [NSt.outSoFar, NSt.flushedP, hbusy, Tr.runP] using h
  have hR0 : RInv .busy (s.ns (i1 xs k N)).got (s.st.chans (rh 0)) := hbusy ▸ R.ch0.2.1
  have hg0 : (s.st.chans (rh 0)).sent = (s.ns (i1 xs k N)).got := by
    rw [hR0.1, hR0.2.2.2.1 hq, List.append_nil]
  rw [hgot, hack, ← hg0, rest_src_all R hbusy hq]

/-- With the writable end gone, the sink has seen the end. -/
theorem rest_snk_gone {o1 : Silmaril.Wasm.Component.Streams.Net.Out} (R : Rest xs k N s o0 o1)
    (hw : (s.st.chans (rh 1)).w.gone = true) : (s.ns (i2 xs k N)).rd = .gone true :=
  R.snk.resolve_left fun ⟨hr, hev⟩ => by
    have hR1 : RInv .busy (s.ns (i2 xs k N)).got (s.st.chans (rh 1)) := hr ▸ R.ch1.2.1
    have hsome : (s.st.chans (rh 1)).r.ev.isSome := hR1.2.2.2.2.2.2.2 hw
    simp [hev] at hsome

/-- **The module has exited, its output closed at the end**: the kernel was done, and the sink
holds `runP xs`. -/
theorem rest_closed {a : List Val} (R : Rest xs k N s o0 ⟨.closed false, a⟩) (hfl : FlushNil k)
    {b : Bool} (hb : (s.ns (i1 xs k N)).rd = .gone b) :
    (s.ns (i2 xs k N)).got = (trV k).runP xs := by
  have hW1 : WInv (.closed false) a (s.st.chans (rh 1)) := R.ch1.1
  have hR1 : RInv (.gone true) (s.ns (i2 xs k N)).got (s.st.chans (rh 1)) :=
    rest_snk_gone R hW1.1 ▸ R.ch1.2.1
  have hgot : (s.ns (i2 xs k N)).got = a := hR1.1.symm.trans hW1.2.2.1
  have hack : a = (s.ns (i1 xs k N)).outSoFar (trV k) := R.O1.1
  have hb' : (s.ns (i1 xs k N)).rd = .gone false := by
    cases b with
    | false => exact hb
    | true => exact absurd (view_closed (R.ch0.2.2.2 (.inr hb))) (R.nclosed false)
  have hdone : (trV k).done (s.ns (i1 xs k N)).s = true := by
    rcases R.stop1 hb' with h | ⟨-, hdead⟩
    · exact h
    · have h : (⟨.closed false, a⟩ : Silmaril.Wasm.Component.Streams.Net.Out).isDead := hdead _ (by rw [R.ho1]; exact List.mem_singleton_self _)
      simp [Silmaril.Wasm.Component.Streams.Net.Out.isDead] at h
  have hso : (s.ns (i1 xs k N)).outSoFar (trV k) = (trV k).runP (s.ns (i1 xs k N)).got := by
    simp only [NSt.outSoFar, NSt.flushedP, hb', Bool.false_or, hdone, ↓reduceIte, hfl _ hdone,
      List.append_nil]
    rfl
  have hR0 : RInv (.gone false) (s.ns (i1 xs k N)).got (s.st.chans (rh 0)) := hb' ▸ R.ch0.2.1
  have hpre : (s.ns (i1 xs k N)).got <+: xs := hR0.1 ▸ sent_prefix R.O0 R.ch0
  calc (s.ns (i2 xs k N)).got = (trV k).runP (s.ns (i1 xs k N)).got := hgot.trans (hack.trans hso)
    _ = (trV k).runP xs := (runP_done (trV k) hpre (R.hs1 ▸ hdone)).symm

end

/-! ## The final state's invariants -/

section
variable {T : PSys MS} {s : Sys (pM xs k N).net}

/-- The sink of a resting pipe reads with nothing pending, or has gone at the end. -/
theorem snk_rest (hC : Ctx (pM xs k N) (toM T) s) (nosnk : ¬ NEn (pM xs k N) s (i2 xs k N))
    {o1 : Silmaril.Wasm.Component.Streams.Net.Out}
    (hCh1 : ChanInv o1.st.view o1.ack (s.ns (i2 xs k N)).rd (s.ns (i2 xs k N)).got (s.st.chans (rh 1)))
    (ngf : (s.ns (i2 xs k N)).rd ≠ .gone false) :
    ((s.ns (i2 xs k N)).rd = .busy ∧ (s.st.chans (rh 1)).r.ev = none) ∨
      (s.ns (i2 xs k N)).rd = .gone true := by
  rcases hr : (s.ns (i2 xs k N)).rd with _ | _ | _ | b
  · exact absurd (nen_input_idle hC.inv hC.ok.wf _ rfl hr) nosnk
  · cases hev : (s.st.chans (rh 1)).r.ev with
    | none => exact .inl ⟨rfl, rfl⟩
    | some q =>
      have hR1 : RInv .busy (s.ns (i2 xs k N)).got (s.st.chans (rh 1)) := hr ▸ hCh1.2.1
      exact absurd (nen_waitIn hC.inv hC.ok.wf _ rfl hR1.2.1 (by rw [hev]; rfl)) nosnk
  · exact absurd (nen_ended hC.inv hC.ok.wf _ rfl hr) nosnk
  · cases b with
    | false => exact absurd hr ngf
    | true => exact .inr rfl

/-- The sink never drops its input before the end (it is never done and has no output). -/
theorem snk_ngf (hC : Ctx (pM xs k N) (toM T) s) : (s.ns (i2 xs k N)).rd ≠ .gone false := fun h => by
  have hout : (s.ns (i2 xs k N)).outs = [] :=
    List.eq_nil_of_length_eq_zero (hC.inv.node (i2 xs k N)).len
  rcases (hC.inv.node (i2 xs k N)).stop h with hd | ⟨hne, -⟩
  · exact Bool.false_ne_true hd
  · exact hne hout

/-- A source that cannot step has written everything it queued. -/
theorem src_idle (hC : Ctx (pM xs k N) (toM T) s) {o0 : Silmaril.Wasm.Component.Streams.Net.Out}
    (ho0 : (s.ns (i0 xs k N)).outs = [o0])
    (nosrc : ∀ {st' x'}, NStep ((pM xs k N).net.node (i0 xs k N)) ((pM xs k N).net.ws (i0 xs k N))
      s.st (s.ns (i0 xs k N)) st' x' → ¬ Closed x' → False) :
    ∀ q a, o0 = ⟨.idle q, a⟩ → q = [] := by
  rintro q a rfl
  cases q with
  | nil => rfl
  | cons v q0 =>
    have ho0' : (s.ns (i0 xs k N)).outs[0]? = some ⟨.idle (v :: q0), a⟩ := by rw [ho0]; rfl
    obtain ⟨hm0, hinv⟩ := chan_out hC.ok.wf hC.inv (i := i0 xs k N) (j := 0) (c := 0) rfl ho0'
    obtain ⟨hw, hst', -, -, hev0⟩ := hinv.1
    have hev' : (s.st.chans (rh 0)).r.gone = true → (s.st.chans (rh 0)).w.ev.isSome := by
      intro h; rw [hev0, h]; rfl
    have hx : (v :: q0).take (v :: q0).length ≠ [] := by simp
    obtain ⟨c₁, r, hwr⟩ := write_ok hw hst' hev' hx
    refine (nosrc (NStep.write (j := 0) rfl ho0' (by simp) (le_refl _)
      (dstep_write_eq hC.inv.coh hm0 hw hwr)) ?_).elim
    rintro ⟨d, a', h⟩
    have h' : Silmaril.Wasm.Component.Streams.Net.Out.afterWrite ((v :: q0).take (v :: q0).length) ((v :: q0).drop (v :: q0).length) a r =
        ⟨.closed d, a'⟩ := by
      simpa only [ho0, List.set_cons_zero, List.cons.injEq, and_true] using h
    exact afterWrite_not_closed _ _ _ _ _ _ h'

/-- A source that cannot step, writing, has no pending event. -/
theorem src_busy (hC : Ctx (pM xs k N) (toM T) s) {o0 : Silmaril.Wasm.Component.Streams.Net.Out}
    (ho0 : (s.ns (i0 xs k N)).outs = [o0])
    (nosrc : ∀ {st' x'}, NStep ((pM xs k N).net.node (i0 xs k N)) ((pM xs k N).net.ws (i0 xs k N))
      s.st (s.ns (i0 xs k N)) st' x' → ¬ Closed x' → False) :
    ∀ ys q a, o0 = ⟨.busy ys q, a⟩ → (s.st.chans (rh 0)).w.ev = none := by
  rintro ys q a rfl
  have ho0' : (s.ns (i0 xs k N)).outs[0]? = some ⟨.busy ys q, a⟩ := by rw [ho0]; rfl
  obtain ⟨-, hinv⟩ := chan_out hC.ok.wf hC.inv (i := i0 xs k N) (j := 0) (c := 0) rfl ho0'
  have hW0 : WInv (.busy ys) a (s.st.chans (rh 0)) := hinv.1
  cases hw0 : (s.st.chans (rh 0)).w.ev with
  | none => rfl
  | some p =>
    obtain ⟨hm0, hwr⟩ := hC.ok.wf.out_wr (i0 xs k N) 0 0 rfl
    obtain ⟨st', e, hwt⟩ := wait_wh_ok hC.inv.coh hm0 hW0.1 (by rw [hw0]; rfl)
    refine (nosrc (NStep.waitOut (j := 0) rfl ho0' (hwr ▸ hwt)) ?_).elim
    rintro ⟨d, a', h⟩
    have h' : Silmaril.Wasm.Component.Streams.Net.Out.onWrite ⟨.busy ys q, a⟩ e.payload = ⟨.closed d, a'⟩ := by
      simpa only [ho0, List.set_cons_zero, List.cons.injEq, and_true] using h
    exact onWrite_busy_not_closed _ _ _ _ _ _ h'

/-- **The invariants of a resting open pipe.** -/
theorem rest_mk (hC : Ctx (pM xs k N) (toM T) s)
    (hT : PSteps xs k true (DRStep (genD k N)) (PSys.init xs k (m₀ k)) T)
    (hsrc : s.ns (i0 xs k N) = T.src) (nosnk : ¬ NEn (pM xs k N) s (i2 xs k N))
    (nosrc : ∀ {st' x'}, NStep ((pM xs k N).net.node (i0 xs k N)) ((pM xs k N).net.ws (i0 xs k N))
      s.st (s.ns (i0 xs k N)) st' x' → ¬ Closed x' → False) :
    ∃ o0 o1, Rest xs k N s o0 o1 := by
  have hI := hC.inv
  obtain ⟨o0, ho0⟩ : ∃ o0, (s.ns (i0 xs k N)).outs = [o0] :=
    List.length_eq_one_iff.1 (hI.node (i0 xs k N)).len
  obtain ⟨o1, ho1⟩ : ∃ o1, (s.ns (i1 xs k N)).outs = [o1] :=
    List.length_eq_one_iff.1 (hI.node (i1 xs k N)).len
  have ho0' : (s.ns (i0 xs k N)).outs[0]? = some o0 := by rw [ho0]; rfl
  have ho1' : (s.ns (i1 xs k N)).outs[0]? = some o1 := by rw [ho1]; rfl
  obtain ⟨-, hCh0⟩ := chan_out hC.ok.wf hI (i := i0 xs k N) (j := 0) (c := 0) rfl ho0'
  obtain ⟨-, hCh1⟩ := chan_out hC.ok.wf hI (i := i1 xs k N) (j := 0) (c := 1) rfl ho1'
  have hsrcI : (s.ns (i0 xs k N)).rd = .gone true ∧ (s.ns (i0 xs k N)).got = [] :=
    (hI.node (i0 xs k N)).src rfl
  have hso : (s.ns (i0 xs k N)).outSoFar ((pM xs k N).net.node (i0 xs k N)).T = xs := by
    simp only [NSt.outSoFar, NSt.flushedP, hsrcI.1, hsrcI.2]
    rfl
  have hO0 : OInv xs (s.ns (i0 xs k N)).rd.flushed o0 :=
    cast (congrArg (fun O => OInv O (s.ns (i0 xs k N)).rd.flushed o0) hso)
      ((hI.node (i0 xs k N)).outs o0 (by rw [ho0]; exact List.mem_singleton_self _))
  have nclosed : ∀ d, o0.st ≠ .closed d := fun d hd => open_src hT ⟨d, o0.ack, by
    rw [← hsrc, ho0, show o0 = ⟨.closed d, o0.ack⟩ from by cases o0; cases hd; rfl]⟩
  exact ⟨o0, o1, hCh0, hCh1, hO0, (hI.node (i1 xs k N)).outs o1 (by rw [ho1]; exact List.mem_singleton_self _),
    (hI.node (i1 xs k N)).hs, (hI.node (i1 xs k N)).stop, ho1, snk_rest hC nosnk hCh1 (snk_ngf hC),
    snk_ngf hC, nclosed, src_idle hC ho0 nosrc, src_busy hC ho0 nosrc, hC.pos⟩

end

theorem relD_exited {r w ws : Nat} {ms : MS} {x : NSt KSt} (hR : RelD r w ws ms x)
    (hex : ms.mode = .exited) : ∃ b, x.rd = .gone b ∧ ∃ d, outIs x (.closed d) := by
  unfold RelD at hR
  rwa [ite_eq_left hex] at hR

/-- The module's output, read off its node. -/
theorem out_of {s : Sys (pM xs k N).net} {o0 o1 : Silmaril.Wasm.Component.Streams.Net.Out} (R : Rest xs k N s o0 o1) {y : NSt KSt}
    (hy : y.outs = (s.ns (i1 xs k N)).outs) {st : OS} {a : List Val} (ha : y.outs = [⟨st, a⟩]) :
    o1 = ⟨st, a⟩ := by
  have h : [o1] = [⟨st, a⟩] := R.ho1.symm.trans (hy.symm.trans ha)
  simpa using h

/-- **The sink of a resting open pipe holds the kernel's output so far.** -/
theorem term_got (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) (hfl : FlushNil k) {T : PSys MS}
    (hT : PSteps xs k true (DRStep (genD k N)) (PSys.init xs k (m₀ k)) T)
    (hterm : ∀ T', ¬ PStep xs k true (DRStep (genD k N)) T T') :
    T.snk.got = (trV k).runP xs := by
  obtain ⟨s, -, hC⟩ := mctx (pM_live (xs := xs) hN hfit) (psteps_mreach hT)
  have hst : s.st = T.st := hC.abs.1
  have hsrc : s.ns (i0 xs k N) = T.src := (hC.abs.2 _).1 rfl
  have hsnk : s.ns (i2 xs k N) = T.snk := (hC.abs.2 _).1 rfl
  obtain ⟨c, c', hn, hR⟩ := (hC.abs.2 (i1 xs k N)).2 k N rfl
  obtain ⟨hc0, hc1⟩ : c = 0 ∧ c' = 1 := by
    have h1 : (Silmaril.Wasm.JcoTool.KDrop.node k c c').inp = some 0 := congrArg Node.inp hn.symm
    have h2 : (Silmaril.Wasm.JcoTool.KDrop.node k c c').outs = [1] := congrArg Node.outs hn.symm
    simp only [Silmaril.Wasm.JcoTool.KDrop.node, Option.some.injEq, List.cons.injEq, and_true] at h1 h2
    exact ⟨h1, h2⟩
  subst hc0 hc1
  obtain ⟨hy1, -, hy3, -⟩ := cast_fields hn (s.ns (i1 xs k N))
  have hE := mod_env hC (i := i1 xs k N) rfl hn ⟨hy1, cast_fields hn _ |>.2.1, hy3⟩
  have hF := fit_of (hC.fits (i1 xs k N) k N rfl) ((cast_fields hn _).2.2.2 (hC.inv.node _).hs)
  have nomod : ¬ CanStep k N T.st T.m := fun ⟨_, _, hd⟩ => hterm _ (.mod hd)
  obtain ⟨o0, o1, R⟩ := rest_mk hC hT hsrc (fun ⟨_, _, hs'⟩ =>
    hterm _ (.snk (by rw [← hst, ← hsnk]; exact hs'))) (fun hs' hnc =>
    hterm _ (.src (by rw [← hst, ← hsrc]; exact hs') (fun _ => hnc)))
  rw [← hsnk]
  by_cases hex : T.m.mode = .exited
  · have hex' : ((toM (xs := xs) (k := k) (N := N) T).ms (i1 xs k N)).mode = .exited := hex
    obtain ⟨b, hb, d, a, ha⟩ := relD_exited hR hex'
    have ho : o1 = ⟨.closed d, a⟩ := out_of R hy3 ha
    subst ho
    cases d with
    | false => exact rest_closed R hfl (hy1.symm.trans hb)
    | true => exact (rest_closed_true R).elim
  obtain ⟨hok, hL⟩ := relD_live hR hex
  rcases hL with ⟨hm, hpc, hk, h0, -, hrd, -⟩ | ⟨hm, hpc, hk, h0, -, hrp, hrd, ⟨a, ha⟩⟩ |
    ⟨hm, hpc, hrp, hrd, ⟨a, ha⟩⟩ | ⟨hm, hpc, hk, hrd, -⟩ | ⟨hm, hpc, hout, -⟩ |
    ⟨hm, hpc, hout, -, -⟩ | ⟨hm, hpc, -, hout⟩ | ⟨hm, hpc, hrd, -⟩
  · exact absurd (mp_rd hN hE hF hok hm hpc hk h0 hrd) nomod
  · cases hq : (s.st.chans (rh 0)).r.ev with
    | some q => exact absurd (mp_wtr hN hE hF hok hm hpc hk h0 hrp hrd (hst ▸ hq)) nomod
    | none => exact rest_idle (out_of R hy3 ha ▸ R) (hy1.symm.trans hrd) hq
  · exact (rest_dead (out_of R hy3 ha ▸ R)).elim
  · exact absurd (mp_eoi hE hF hok hm hpc hk hrd) nomod
  · exact absurd (mp_wr hE hok hm hpc hout) nomod
  · obtain ⟨a, ha⟩ := hout
    cases hq : (s.st.chans (rh 1)).w.ev with
    | some q => exact absurd (mp_wtw hE hok hm hpc ⟨a, ha⟩ (hst ▸ hq)) nomod
    | none => exact (rest_busy (out_of R hy3 ha ▸ R) hq).elim
  · exact absurd (mp_cl hE hok hm hpc hout) nomod
  · exact absurd (mp_dead hE hok hm hpc hrd) nomod

/-- **The outputs so far of the open pipe are exactly the kernel's output so far.** -/
theorem pipe_part (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) (hfl : FlushNil k) (ys : List Val) :
    (Silmaril.Wasm.JcoTool.KRead.dropObs k N).part xs ys ↔ ys = (trV k).runP xs := by
  constructor
  · rintro ⟨c, hc, hstab, rfl⟩
    obtain ⟨T, hcT, hTt⟩ := open_term hN hfit hc
    rw [← hstab T hcT]
    exact term_got hN hfit hfl (hc.trans hcT) hTt
  · rintro rfl
    obtain ⟨T, hT, hTt⟩ := open_term (xs := xs) hN hfit Relation.ReflTransGen.refl
    refine ⟨T, hT, fun c' hc' => ?_, term_got hN hfit hfl hT hTt⟩
    rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c'', h1, -⟩
    · rfl
    · exact absurd h1 (hTt _)

/-- **The pipe model of a generated module reads as its kernel's transformer.** -/
theorem pipe_reads (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) (hfl : FlushNil k) :
    (Silmaril.Wasm.JcoTool.KRead.dropObs k N).Reads (trV k) := fun _ ys =>
  ⟨pipe_whole hN hfit ys, pipe_part hN hfit hfl ys⟩

end Silmaril.Proofs.Wasm.JcoTool.KLive
