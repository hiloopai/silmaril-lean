module

public import Silmaril.Wasm.JcoTool.KRead.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Vals

/-!
# One step of the runtime on Core, both ways

* `fwd_step`: every step of the drop runtime `DRStep P` from a machine whose callback is
  `CbSafe` is a step `CRStepU` of the runtime on Core 3.0 (with the result read unsigned), the
  store after it holding the machine's globals and memory (as `KCoreRun.rstep_core`, keeping the
  bound `code < 2 ^ 32` that `invoke_run` gives).
* `bwd_step`: **conversely**, in the deterministic profile and given `UniqueVal` (unique
  value results of Core with the built-ins), every step `CRStepU` from a Core store related to a
  machine whose callback is `CbSafe` and does not trap there (`NoTrap`) is the image of a step
  of the drop runtime: the Core runtime has no behaviour the model lacks.
-/

public section

namespace Silmaril.Proofs.Wasm.JcoTool.KRead

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.JcoTool.KRead
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (BI M32 Prog MS Mode deliver modeOf FUEL locals)
open Silmaril.Wasm.JcoTool.KDrop (DRStep dinvoke wfD dexec)
open Silmaril.Wasm.Component.Streams.Drop (DStore DWait)
open Silmaril.Proofs.Wasm.JcoTool.KCoreRun (dinvoke_inv deliver_core wfD_bounds code_lt cbAt_funcs deliver_g)

variable {H : Type} {hb : BI → H} {ma : Nat}

/-- A drop-runtime step after `YIELD` on Core. -/
theorem fwd_ready (Pf : Profile) {P : Prog} {mi : ModuleInst} {a : Nat} {st st' : DStore}
    {ms ms' : MS} {cs : Store H} (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi P a)
    (hsafe : CbSafe P ms.g) (hm : ms.mode = .ready)
    (hinv : dinvoke P.cb [0, 0, 0] st ms = some (st', ms')) :
    ∃ cs', CRStepU Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi P a := by
  obtain ⟨code, s', hx, hmd, rfl, hg, hmm, hrp⟩ := dinvoke_inv hinv
  have hb' : bexec CBL P.cb FUEL ⟨ms.g, ms.m, locals [0, 0, 0], st, ms.rp⟩ = some (.ret code, s') :=
    hsafe [0, 0, 0] ms.m st ms.rp _ (.inl rfl) hx
  obtain ⟨hc, cs', hI', hf, hrun⟩ := invoke_run Pf hI hcb (by decide) (by decide) (by decide) hb'
  refine ⟨cs', ?_, by rw [hg, hmm]; exact hI', cbAt_funcs hcb hf⟩
  rw [hm, hrp]
  exact .ready hc hrun hmd

/-- A drop-runtime step after `WAIT` on Core. -/
theorem fwd_event (Pf : Profile) {P : Prog} {mi : ModuleInst} {a : Nat} {st st₁ st' : DStore}
    {ms ms' : MS} {cs : Store H} {s h : Nat} {e : Silmaril.Wasm.Component.Async.Event}
    (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi P a) (hsafe : CbSafe P ms.g)
    (hm : ms.mode = .waiting s) (hw : DWait st s h st₁ e) (hwf : wfD e = true)
    (hinv : dinvoke P.cb [e.code.toNat, e.index, e.payload] st₁ (deliver e ms) = some (st', ms')) :
    ∃ cs', CRStepU Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi P a := by
  obtain ⟨hI₁, hrp₁, hf₁⟩ := deliver_core hI e
  obtain ⟨code, s', hx, hmd, rfl, hg, hmm, hrp⟩ := dinvoke_inv hinv
  obtain ⟨hpl, hil⟩ := wfD_bounds hwf
  have hx' : dexec P.cb FUEL ⟨ms.g, (deliver e ms).m, locals [e.code.toNat, e.index, e.payload],
      st₁, (deliver e ms).rp⟩ = some (.ret code, s') := by rw [← deliver_g e ms]; exact hx
  have hb' : bexec CBL P.cb FUEL ⟨ms.g, (deliver e ms).m, locals [e.code.toNat, e.index, e.payload],
      st₁, (deliverC ma cs e ms.rp).2⟩ = some (.ret code, s') := by
    rw [hrp₁]; exact hsafe _ _ _ _ _ (.inr ⟨e, hwf, rfl⟩) hx'
  have hI₂ : InstR hb ma (deliverC ma cs e ms.rp).1 mi ms.g (deliver e ms).m := by
    rw [← deliver_g e ms]; exact hI₁
  obtain ⟨hc, cs', hI', hf, hrun⟩ :=
    invoke_run Pf hI₂ (cbAt_funcs hcb hf₁) (code_lt e.code) hil hpl hb'
  refine ⟨cs', ?_, by rw [hg, hmm]; exact hI', cbAt_funcs (cbAt_funcs hcb hf₁) hf⟩
  rw [hm, hrp]
  exact .event hw hwf rfl hc hrun hmd

/-- **A step of the drop runtime is a step of the runtime on Core**, reading the result unsigned. -/
theorem fwd_step (Pf : Profile) {P : Prog} {mi : ModuleInst} {a : Nat} {st st' : DStore}
    {ms ms' : MS} {cs : Store H} (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi P a)
    (hsafe : CbSafe P ms.g) (h : DRStep P st ms st' ms') :
    ∃ cs', CRStepU Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi P a := by
  cases h with
  | ready hm hinv => exact fwd_ready Pf hI hcb hsafe hm hinv
  | event hm hw hwf hinv => exact fwd_event Pf hI hcb hsafe hm hw hwf hinv

theorem w_inj {x y : Nat} (hx : x < M32) (hy : y < M32) (h : Val.i32 (w x) = Val.i32 (w y)) :
    x = y := by
  have h1 : (w x).toNat = (w y).toNat := by
    have : w x = w y := by simp only [Val.i32, Val.num.injEq] at h; injection h
    rw [this]
  simp only [w, BitVec.toNat_ofNat] at h1
  rwa [Nat.mod_eq_of_lt (by simpa [M32] using hx), Nat.mod_eq_of_lt (by simpa [M32] using hy)] at h1

/-- Two Core runs of one invocation to value results agree (`Task.hstep_unf`). -/
theorem runs_agree {o : GrowKind → Nat → Nat → Nat → Bool} (hu : UniqueVal o hb ma) {a : Nat}
    {st₁ st₂ : DStore} {rp rp₁ rp₂ : Option (Nat × Nat)} {cs cs₁ cs₂ : Store H} {st : DStore}
    {args : List Val} {c₁ c₂ : Nat} (hc₁ : c₁ < M32) (hc₂ : c₂ < M32)
    (h₁ : HSteps (Profile.deterministic o) hb ma ((st, rp), invoke cs a args)
      ((st₁, rp₁), ⟨cs₁, {}, vals [Val.i32 (w c₁)]⟩))
    (h₂ : HSteps (Profile.deterministic o) hb ma ((st, rp), invoke cs a args)
      ((st₂, rp₂), ⟨cs₂, {}, vals [Val.i32 (w c₂)]⟩)) :
    st₁ = st₂ ∧ rp₁ = rp₂ ∧ cs₁ = cs₂ ∧ c₁ = c₂ := by
  have e := hu _ _ _ h₁ h₂ ⟨_, _, rfl⟩ ⟨_, _, rfl⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, e2⟩ := e
  have e3 : cs₁ = cs₂ := congrArg Config.store e2
  have e4 := congrArg Config.code e2
  simp only [vals, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Silmaril.Wasm.SingleThreaded.Det.toAdmin_inj] at e4
  exact ⟨rfl, rfl, e3, w_inj hc₁ hc₂ e4⟩

/-- **One Core invocation run against the checked run**: with unique value results, a Core run of
the callback to a value ends where the checked run `bexec` says. -/
theorem bwd_core {o : GrowKind → Nat → Nat → Nat → Bool} (hu : UniqueVal o hb ma) {P : Prog}
    {mi : ModuleInst} {a : Nat} {g m : Nat → Nat} {cs₀ cs' : Store H} {st₀ st' : DStore}
    {rp₀ rp' : Option (Nat × Nat)} {x y z code code' : Nat} {s' : Silmaril.Wasm.JcoTool.KDrop.DSt}
    (hx : x < M32) (hy : y < M32) (hz : z < M32) (hI : InstR hb ma cs₀ mi g m)
    (hcb : CbAt cs₀ mi P a)
    (hb' : bexec CBL P.cb FUEL ⟨g, m, locals [x, y, z], st₀, rp₀⟩ = some (.ret code', s'))
    (hc : code < M32)
    (hrun : HSteps (Profile.deterministic o) hb ma ((st₀, rp₀), invoke cs₀ a ([x, y, z].map (Val.i32 ∘ w)))
      ((st', rp'), ⟨cs', {}, vals [Val.i32 (w code)]⟩)) :
    st' = s'.st ∧ rp' = s'.rp ∧ code = code' ∧ InstR hb ma cs' mi s'.g s'.m ∧ cs'.funcs = cs₀.funcs := by
  obtain ⟨hc', cs'', hI', hf, hrun'⟩ := invoke_run (Profile.deterministic o) hI hcb hx hy hz hb'
  obtain ⟨e1, e2, e3, e4⟩ := runs_agree hu hc hc' hrun hrun'
  have hI'' : InstR hb ma cs' mi s'.g s'.m := e3 ▸ hI'
  have hf' : cs'.funcs = cs₀.funcs := e3 ▸ hf
  exact ⟨e1, e2, e4, hI'', hf'⟩

/-- A Core runtime step after `YIELD` is a drop-runtime step. -/
theorem bwd_ready {o : GrowKind → Nat → Nat → Nat → Bool} (hu : UniqueVal o hb ma) {P : Prog}
    {mi : ModuleInst} {a : Nat} {st st' : DStore} {ms : MS} {cs cs' : Store H}
    {rp' : Option (Nat × Nat)} {md : Mode} {code : Nat} (hI : InstR hb ma cs mi ms.g ms.m)
    (hcb : CbAt cs mi P a) (hsafe : CbSafe P ms.g) (hnt : NoTrap P st ms) (hm : ms.mode = .ready)
    (hc : code < M32)
    (hrun : HSteps (Profile.deterministic o) hb ma ((st, ms.rp), invoke cs a ([0, 0, 0].map (Val.i32 ∘ w)))
      ((st', rp'), ⟨cs', {}, vals [Val.i32 (w code)]⟩)) (hmd : modeOf code = some md) :
    ∃ ms', DRStep P st ms st' ms' ∧ ms'.rp = rp' ∧ ms'.mode = md ∧ InstR hb ma cs' mi ms'.g ms'.m ∧
      CbAt cs' mi P a := by
  obtain ⟨⟨st'', ms''⟩, hinv⟩ := hnt.1 hm
  obtain ⟨code', s', hxd, hmd', hst, hg, hmm, hrp'⟩ := dinvoke_inv hinv
  have hb' : bexec CBL P.cb FUEL ⟨ms.g, ms.m, locals [0, 0, 0], st, ms.rp⟩ = some (.ret code', s') :=
    hsafe [0, 0, 0] ms.m st ms.rp _ (.inl rfl) hxd
  obtain ⟨e1, e2, e3, hI', hf⟩ := bwd_core hu (by decide) (by decide) (by decide) hI hcb hb' hc hrun
  have hinv' : dinvoke P.cb [0, 0, 0] st ms = some (st', ms'') := by rw [e1, ← hst]; exact hinv
  have hD : DRStep P st ms st' ms'' := .ready hm hinv'
  have hmd'' : ms''.mode = md := Option.some.inj (hmd'.symm.trans (e3 ▸ hmd))
  have hI'' : InstR hb ma cs' mi ms''.g ms''.m := by rw [hg, hmm]; exact hI'
  exact ⟨ms'', hD, by rw [hrp', e2], hmd'', hI'', cbAt_funcs hcb hf⟩

/-- A Core runtime step after `WAIT` is a drop-runtime step. -/
theorem bwd_event {o : GrowKind → Nat → Nat → Nat → Bool} (hu : UniqueVal o hb ma) {P : Prog}
    {mi : ModuleInst} {a : Nat} {st st₁ st' : DStore} {ms : MS} {cs cs₁ cs' : Store H}
    {rp₁ rp' : Option (Nat × Nat)} {md : Mode} {code s h : Nat} {e : Silmaril.Wasm.Component.Async.Event}
    (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi P a) (hsafe : CbSafe P ms.g)
    (hnt : NoTrap P st ms) (hm : ms.mode = .waiting s) (hw : DWait st s h st₁ e) (hwf : wfD e = true)
    (hd : deliverC ma cs e ms.rp = (cs₁, rp₁)) (hc : code < M32)
    (hrun : HSteps (Profile.deterministic o) hb ma
      ((st₁, rp₁), invoke cs₁ a ([e.code.toNat, e.index, e.payload].map (Val.i32 ∘ w)))
      ((st', rp'), ⟨cs', {}, vals [Val.i32 (w code)]⟩)) (hmd : modeOf code = some md) :
    ∃ ms', DRStep P st ms st' ms' ∧ ms'.rp = rp' ∧ ms'.mode = md ∧ InstR hb ma cs' mi ms'.g ms'.m ∧
      CbAt cs' mi P a := by
  obtain ⟨⟨st'', ms''⟩, hinv⟩ := hnt.2 s h st₁ e hm hw hwf
  obtain ⟨hI₁, hrp₁, hf₁⟩ := deliver_core hI e
  obtain ⟨code', s', hxd, hmd', hst, hg, hmm, hrp'⟩ := dinvoke_inv hinv
  obtain ⟨hpl, hil⟩ := wfD_bounds hwf
  have hcs : (deliverC ma cs e ms.rp).1 = cs₁ := congrArg Prod.fst hd
  have hrpd : (deliver e ms).rp = rp₁ := hrp₁.symm.trans (congrArg Prod.snd hd)
  have hx' : dexec P.cb FUEL ⟨ms.g, (deliver e ms).m, locals [e.code.toNat, e.index, e.payload],
      st₁, (deliver e ms).rp⟩ = some (.ret code', s') := by rw [← deliver_g e ms]; exact hxd
  have hb' : bexec CBL P.cb FUEL ⟨ms.g, (deliver e ms).m, locals [e.code.toNat, e.index, e.payload],
      st₁, rp₁⟩ = some (.ret code', s') := hrpd ▸ hsafe _ _ _ _ _ (.inr ⟨e, hwf, rfl⟩) hx'
  have hI₂ : InstR hb ma cs₁ mi ms.g (deliver e ms).m := by rw [← hcs, ← deliver_g e ms]; exact hI₁
  have hcb₁ : CbAt cs₁ mi P a := cbAt_funcs hcb (hcs ▸ hf₁)
  obtain ⟨e1, e2, e3, hI', hf⟩ := bwd_core hu (code_lt e.code) hil hpl hI₂ hcb₁ hb' hc hrun
  have hinv' : dinvoke P.cb [e.code.toNat, e.index, e.payload] st₁ (deliver e ms) = some (st', ms'') := by
    rw [e1, ← hst]; exact hinv
  have hD : DRStep P st ms st' ms'' := .event hm hw hwf hinv'
  have hmd'' : ms''.mode = md := Option.some.inj (hmd'.symm.trans (e3 ▸ hmd))
  have hI'' : InstR hb ma cs' mi ms''.g ms''.m := by rw [hg, hmm]; exact hI'
  exact ⟨ms'', hD, by rw [hrp', e2], hmd'', hI'', cbAt_funcs hcb₁ hf⟩

/-- **A step of the runtime on Core is a step of the drop runtime**, from a machine whose callback
is `CbSafe` and does not trap, given unique value results of Core (`UniqueVal`). -/
theorem bwd_step (o : GrowKind → Nat → Nat → Nat → Bool) (hu : UniqueVal o hb ma) {P : Prog}
    {mi : ModuleInst} {a : Nat} {st st' : DStore} {ms : MS} {cs cs' : Store H}
    {rp' : Option (Nat × Nat)} {md : Mode} (hI : InstR hb ma cs mi ms.g ms.m)
    (hcb : CbAt cs mi P a) (hsafe : CbSafe P ms.g) (hnt : NoTrap P st ms)
    (h : CRStepU (Profile.deterministic o) hb ma a (st, cs, ms.rp, ms.mode) (st', cs', rp', md)) :
    ∃ ms', DRStep P st ms st' ms' ∧ ms'.rp = rp' ∧ ms'.mode = md ∧ InstR hb ma cs' mi ms'.g ms'.m ∧
      CbAt cs' mi P a := by
  generalize hx : (st, cs, ms.rp, ms.mode) = x at h
  generalize hy : (st', cs', rp', md) = y at h
  cases h with
  | ready hc hrun hmd =>
    simp only [Prod.mk.injEq] at hx hy
    obtain ⟨rfl, rfl, rfl, hm⟩ := hx
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hy
    exact bwd_ready hu hI hcb hsafe hnt hm hc hrun hmd
  | event hw hwf hd hc hrun hmd =>
    simp only [Prod.mk.injEq] at hx hy
    obtain ⟨rfl, rfl, rfl, hm⟩ := hx
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hy
    exact bwd_event hu hI hcb hsafe hnt hm hw hwf hd hc hrun hmd

end Silmaril.Proofs.Wasm.JcoTool.KRead
