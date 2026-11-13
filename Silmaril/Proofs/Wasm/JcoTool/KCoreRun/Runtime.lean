module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Invoke

/-!
# The callback runtime on Core 3.0

`deliver_core`: the runtime's delivery of a completed read on the Core store (`deliverC`) keeps
the instance relation with `KCore.deliver`'s memory. `rstep_core`: **every step of the drop
runtime `KDrop.DRStep` of a module is a step `CRStep` of the runtime on Core 3.0** (the Core
invocations of the callback of `toModule`, with the built-ins as host calls), when the callback
is `CbSafe` at the machine's globals; the store after it holds the machine's globals and memory.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd locals FUEL Prog MS Mode deliver modeOf writeBytes byteOf)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec dinvoke DRStep wfD)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)
open Silmaril.Wasm.Component.Streams.Drop (DStore)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma : Nat}

theorem dinvoke_inv {body : S} {ps : List Nat} {st st' : DStore} {ms ms' : MS}
    (h : dinvoke body ps st ms = some (st', ms')) :
    ∃ code s', dexec body FUEL ⟨ms.g, ms.m, locals ps, st, ms.rp⟩ = some (.ret code, s') ∧
      modeOf code = some ms'.mode ∧ st' = s'.st ∧ ms'.g = s'.g ∧ ms'.m = s'.m ∧ ms'.rp = s'.rp := by
  unfold dinvoke at h
  split at h
  · rename_i code s' hx
    obtain ⟨md, hmd, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨code, s', hx, hmd, rfl, rfl, rfl, rfl⟩
  · cases h

theorem inst_mem {cs cs' : Store H} {mi : ModuleInst} {g m m' : Nat → Nat}
    (hI : InstR hb ma cs mi g m) (hm : MemR cs' ⟨[], mi⟩ ma m') (hg : cs'.globals = cs.globals)
    (hf : cs'.funcs = cs.funcs) : InstR hb ma cs' mi g m' := by
  refine ⟨?_, hI.glt, hm, fun b => ?_⟩
  · have e : ∀ x, cs'.global? ⟨[], mi⟩ x = cs.global? ⟨[], mi⟩ x := global?_of_globals hg _
    obtain ⟨h1, h2, h3⟩ := hI.glob
    exact ⟨h1, fun g' hg' => by rw [e]; exact h2 g' hg',
      fun g₁ g₂ a a' gi gi' ha ha' => by rw [e] at ha ha'; exact h3 g₁ g₂ a a' gi gi' ha ha'⟩
  · obtain ⟨a', fi, ps, rs, h1, h2, h3, h4, h5⟩ := hI.imp b
    exact ⟨a', fi, ps, rs, h1, by rw [hf]; exact h2, h3, h4, h5⟩

/-- **The delivery of a completed read on Core** keeps the instance relation. -/
theorem deliver_core {cs : Store H} {mi : ModuleInst} {ms : MS} (hI : InstR hb ma cs mi ms.g ms.m)
    (e : Silmaril.Wasm.Component.Async.Event) :
    InstR hb ma (deliverC ma cs e ms.rp).1 mi (deliver e ms).g (deliver e ms).m ∧
      (deliverC ma cs e ms.rp).2 = (deliver e ms).rp ∧ (deliverC ma cs e ms.rp).1.funcs = cs.funcs := by
  rcases e with ⟨c, idx, pay, items⟩
  cases hrp : ms.rp with
  | none =>
    cases c <;> (simp only [deliver, deliverC, hrp]; exact ⟨hI, trivial, trivial⟩)
  | some hp =>
    obtain ⟨h, p⟩ := hp
    cases c
    case streamRead =>
      by_cases hh : h = idx
      · obtain ⟨x, h0, h1, hs, hbx⟩ := hI.mem
        have hm : MemR cs ⟨[], mi⟩ ma ms.m := ⟨x, h0, h1, hs, hbx⟩
        have hag := memOf_agree hs hbx
        have hm' := memR_enc hm (writeBytes_bytes (fun a ha => hm.byte_lt ha) p items)
          (writeBytes_congr (fun a ha => (hag a ha).symm) p _) h1
        simp only [deliver, deliverC, hrp, hh, ↓reduceIte, h1]
        exact ⟨inst_mem hI hm' rfl rfl, trivial, rfl⟩
      · simp only [deliver, deliverC, hrp, hh, ↓reduceIte]
        exact ⟨hI, trivial, trivial⟩
    all_goals (simp only [deliver, deliverC, hrp]; exact ⟨hI, trivial, trivial⟩)

theorem cbAt_funcs {cs cs' : Store H} {mi : ModuleInst} {P : Prog} {a : Nat} (hcb : CbAt cs mi P a)
    (hf : cs'.funcs = cs.funcs) : CbAt cs' mi P a := by
  obtain ⟨fi, ty, ps, rs, h1, h2⟩ := hcb
  exact ⟨fi, ty, ps, rs, by rw [hf]; exact h1, h2⟩

theorem wfD_bounds {e : Silmaril.Wasm.Component.Async.Event} (h : wfD e = true) :
    e.payload < M32 ∧ e.index < M32 := by
  simp only [wfD, Silmaril.Wasm.JcoTool.KCore.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2⟩

theorem code_lt (c : Silmaril.Wasm.Component.Async.EventCode) : c.toNat < M32 := by
  cases c <;> decide

theorem deliver_g (e : Silmaril.Wasm.Component.Async.Event) (ms : MS) : (deliver e ms).g = ms.g := by
  unfold deliver
  split
  · split <;> rfl
  · rfl

/-- A step after `YIELD`. -/
theorem rstep_ready (Pf : Profile) {P : Prog} {mi : ModuleInst} {a : Nat} {st st' : DStore}
    {ms ms' : MS} {cs : Store H} (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi P a)
    (hsafe : CbSafe P ms.g) (hm : ms.mode = .ready)
    (hinv : dinvoke P.cb [0, 0, 0] st ms = some (st', ms')) :
    ∃ cs', CRStep Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi P a := by
  obtain ⟨code, s', hx, hmd, rfl, hg, hmm, hrp⟩ := dinvoke_inv hinv
  have hb' : bexec CBL P.cb FUEL ⟨ms.g, ms.m, locals [0, 0, 0], st, ms.rp⟩ = some (.ret code, s') :=
    hsafe [0, 0, 0] ms.m st ms.rp _ (.inl rfl) hx
  obtain ⟨-, cs', hI', hf, hrun⟩ := invoke_run Pf hI hcb (by decide) (by decide) (by decide) hb'
  refine ⟨cs', ?_, by rw [hg, hmm]; exact hI', cbAt_funcs hcb hf⟩
  rw [hm, hrp]
  exact .ready hrun hmd

/-- A step after `WAIT`: an event, its delivery, the invocation. -/
theorem rstep_event (Pf : Profile) {P : Prog} {mi : ModuleInst} {a : Nat} {st st₁ st' : DStore}
    {ms ms' : MS} {cs : Store H} {s h : Nat} {e : Silmaril.Wasm.Component.Async.Event}
    (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi P a) (hsafe : CbSafe P ms.g)
    (hm : ms.mode = .waiting s) (hw : Silmaril.Wasm.Component.Streams.Drop.DWait st s h st₁ e)
    (hwf : wfD e = true)
    (hinv : dinvoke P.cb [e.code.toNat, e.index, e.payload] st₁ (deliver e ms) = some (st', ms')) :
    ∃ cs', CRStep Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi P a := by
  obtain ⟨hI₁, hrp₁, hf₁⟩ := deliver_core hI e
  obtain ⟨code, s', hx, hmd, rfl, hg, hmm, hrp⟩ := dinvoke_inv hinv
  obtain ⟨hpl, hil⟩ := wfD_bounds hwf
  have hx' : dexec P.cb FUEL ⟨ms.g, (deliver e ms).m, locals [e.code.toNat, e.index, e.payload], st₁,
      (deliver e ms).rp⟩ = some (.ret code, s') := by rw [← deliver_g e ms]; exact hx
  have hb' : bexec CBL P.cb FUEL ⟨ms.g, (deliver e ms).m, locals [e.code.toNat, e.index, e.payload],
      st₁, (deliverC ma cs e ms.rp).2⟩ = some (.ret code, s') := by
    rw [hrp₁]; exact hsafe _ _ _ _ _ (.inr ⟨e, hwf, rfl⟩) hx'
  have hI₂ : InstR hb ma (deliverC ma cs e ms.rp).1 mi ms.g (deliver e ms).m := by
    rw [← deliver_g e ms]; exact hI₁
  obtain ⟨-, cs', hI', hf, hrun⟩ := invoke_run Pf hI₂ (cbAt_funcs hcb hf₁) (code_lt e.code) hil hpl hb'
  refine ⟨cs', ?_, by rw [hg, hmm]; exact hI', cbAt_funcs (cbAt_funcs hcb hf₁) hf⟩
  rw [hm, hrp]
  exact .event hw hwf rfl hrun hmd

/-- **Every step of the drop runtime is a step of the runtime on Core 3.0.** -/
theorem rstep_core (Pf : Profile) {P : Prog} {mi : ModuleInst} {a : Nat} {st st' : DStore}
    {ms ms' : MS} {cs : Store H} (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi P a)
    (hsafe : CbSafe P ms.g) (h : DRStep P st ms st' ms') :
    ∃ cs', CRStep Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi P a := by
  cases h with
  | ready hm hinv => exact rstep_ready Pf hI hcb hsafe hm hinv
  | event hm hw hwf hinv => exact rstep_event Pf hI hcb hsafe hm hw hwf hinv

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
