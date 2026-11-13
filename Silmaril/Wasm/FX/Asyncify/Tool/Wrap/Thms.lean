module

public import Silmaril.Wasm.FX.Asyncify.Tool.Wrap.Defs
public import Silmaril.Wasm.FX.Asyncify.Tool.Fits.Thms
public import Silmaril.Wasm.FX.Asyncify.Tool.Thms
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Wrap.Beh
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Wrap.ShapeEnv

/-!
# The asyncified program stays in bounds when `sp` wraps: results

The header of `Defs`. Follow-up 4 proved `Task.fits` within `DepthBound` (every record ends below
`2 ^ 32`) and for memories of at least `2 ^ 32 + 4 · max F R` bytes, and froze the rest as
`Task.fits_wrap` and `Task.fits_window`. Both are proved here, so `Task.fits` holds outright.

* **Small memories, `cap < 2 ^ 32 + 4 F`** (`Wrap/Unwind`, `Wrap/Rewind`, `Wrap/Normal`,
  `Wrap/Main`): `FitsIn` gives `DepthBoundW`, `SB + 4 F · depth < 2 ^ 32 + 4 F`, so every
  record *starts* below `2 ^ 32` and only the `sp` after the last record of an unwinding wraps.
  Saving and restoring a record at `a` only read `sp` as the natural number `a`, and the pop
  `sp - 4 F` works modulo `2 ^ 32`, so the in-bounds simulation of `Fits` goes through with
  the weaker bound (`asyncify_fits_safeW`). It is also a full simulation: `asyncify_behW` is
  `asyncify_beh` under `DepthBoundW`.
* **Large memories, `2 ^ 32 + 4 F ≤ cap + 1`** (`Wrap/Shape`, `Wrap/ShapeEnv`): every access with
  an offset of `4 F` or more is a request access whose address operand is the constant `0`
  pushed right before it (`c32 0, local.get a, st o`, `c32 0, ld o`, `o + 4 ≤ 4 R`), an
  invariant of every target run (`cfgOK_runN`). Every other access is a 32-bit operand plus an
  offset below `4 F`. So no access ends past `cap` whatever the run does (`safe_shape`, needing
  only `4 R ≤ cap` besides). This is the fact about the shape of the code that the case
  `R > F` needed: there records can wrap onto the request area and the simulation fails, but
  the bounds do not.

Results:

* **`fits_proved : Task.fits`**, `fits_wrap_proved : Task.fits_wrap`,
  `fits_window_proved : Task.fits_window`.
* `fits_shape`: no `FitsIn` hypothesis is needed once `2 ^ 32 + 4 F ≤ cap + 1` and `SB ≤ cap`
  (sharpening `fits_wide`, which needs `2 ^ 32 + 4 · max F R ≤ cap`).
* `asyncify_beh_fitsW`: for `cap < 2 ^ 32 + 4 F`, the bounded target has the source's behaviours
  when the source fits (sharpening `asyncify_beh_fits_lt`, which needs `cap < 2 ^ 32`).
* `asyncifyBytes_correctW`: `asyncifyBytes_correct` (the tool on bytes, end to end) under
  `DepthBoundW` instead of `DepthBound`.
* `asyncify_beh_fits'`, `asyncify_fits_core'`: `asyncify_beh_fits` and `asyncify_fits_core`
  without their `Task.fits` hypothesis.

Not claimed: the behaviours for memories of `2 ^ 32 + 4 F` bytes or more with source runs that
leave `DepthBoundW` (only reachable when `R > F`): records then overwrite the request area, and
the target need not have the source's behaviours. Only safety is proved there.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

variable {σ : Type}

/-- **No access past `cap` once `2 ^ 32 + 4 F ≤ cap + 1` and `SB ≤ cap`**, by any run. -/
theorem fits_shape (P : Prog) (hP : P.WF) (H : Host σ) {cap : Nat}
    (hF : 2 ^ 32 + 4 * P.frameWords ≤ cap + 1) (hR : P.sb ≤ cap) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (s : σ) :
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg) (tgtSt P e fn args s) :=
  safe_shape P hP H hF hR hfn args s

/-- **`Task.fits`, proved.** -/
theorem fits_proved : Task.fits := by
  intro P hP σ H cap e fn args s hge hget hargs hfit
  have hfn : P.fnAt e = some fn := by simp [Prog.fnAt, hge, hget]
  by_cases hc : cap < 2 ^ 32 + 4 * P.frameWords
  · exact asyncify_fits_safeW P hP H cap hfn args hargs s (boundW_of_fitsIn hc hfit) hfit
  · have h0 : P.sb + 4 * P.frameWords * 1 ≤ cap := hfit 0 _ rfl
    exact safe_shape P hP H (by omega) (by omega) hfn args s

/-- **`Task.fits_wrap`, proved.** -/
theorem fits_wrap_proved : Task.fits_wrap :=
  fun P hP _ H cap e fn args s hge hget hargs _ hfit =>
    fits_proved P hP H cap e fn args s hge hget hargs hfit

/-- **`Task.fits_window`, proved.** -/
theorem fits_window_proved : Task.fits_window :=
  fun P hP _ H cap e fn args s hge hget hargs _ _ hfit =>
    fits_proved P hP H cap e fn args s hge hget hargs hfit

/-- **The bounded target has the source's behaviours** for a memory below `2 ^ 32 + 4 F` bytes
into which every source state fits. -/
theorem asyncify_beh_fitsW (P : Prog) (hP : P.WF) (H : Host σ) (cap : Nat)
    (hcap : cap < 2 ^ 32 + 4 * P.frameWords) {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn)
    (args : List W) (hargs : args.length = fn.nparams) (s : σ)
    (hfit : FitsIn cap P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStepB cap (asyncifyProg P) H) (tgtSt P e fn args s) := by
  have hb : DepthBoundW P H (srcCfg e fn args, s) := boundW_of_fitsIn hcap hfit
  rw [bounded_eq_of_safe cap _ H (asyncify_fits_safeW P hP H cap hfn args hargs s hb hfit)]
  exact asyncify_behW P hP H hfn args hargs s hb

/-- **End to end on bytes, within `DepthBoundW`** (`asyncifyBytes_correct` with the weaker
bound: the last record of a suspension may end above `2 ^ 32`). -/
theorem asyncifyBytes_correctW {b b' : ByteArray} {pages : Nat}
    (h : asyncifyBytes b pages = .ok b') :
    ∃ m P m', Silmaril.Wasm.Binary.Core.decode? b = some m ∧
      Silmaril.Wasm.Binary.Core.Encodes b'.data.toList m' ∧
      envOf m = some P.env ∧ envOfLax m' = some (asyncifyProg P) ∧
      globalsOfLax m' = some P.tGlobals ∧ (∀ name, exportFunc m' name = exportFunc m name) ∧
      ∀ {σ : Type} (H : Host σ) {e : Nat} {fn : FnSrc} (args : List W) (s : σ),
        P.fnAt e = some fn → args.length = fn.nparams → DepthBoundW P H (srcCfg e fn args, s) →
        beh (srcStep P.env H) (srcCfg e fn args, s) =
          beh (tgtStep (asyncifyProg P) H) (tgtSt P e fn args s) := by
  obtain ⟨m, P, m', hd, -, hwf, henv, -, he, hlax, hgl, hex⟩ := asyncifyBytes_spec h
  exact ⟨m, P, m', hd, he, henv, hlax, hgl, hex, fun {_} H {_} {_} args s hfn hargs hb =>
    asyncify_behW P hwf H hfn args hargs s hb⟩

/-- `asyncify_beh_fits` without its `Task.fits` hypothesis. -/
theorem asyncify_beh_fits' (P : Prog) (hP : P.WF) (H : Host σ) (cap : Nat) {e : Nat}
    {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams)
    (s : σ) (hbound : DepthBound P H (srcCfg e fn args, s))
    (hfit : FitsIn cap P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStepB cap (asyncifyProg P) H) (tgtSt P e fn args s) :=
  asyncify_beh_fits fits_proved P hP H cap hfn args hargs s hbound hfit

open Silmaril.Wasm.Execution.Core in
open Silmaril.Wasm.Numerics (Profile) in
/-- `asyncify_fits_core` without its `Task.fits` hypothesis. -/
theorem asyncify_fits_core' {Hc : Type} (Pf : Profile) (host : HostSemantics Hc) (P : Prog)
    (hP : P.WF) (Hh : Host σ) {cap : Nat} (hcap : P.sb ≤ cap) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (h : σ)
    (hbound : DepthBound P Hh (srcCfg e fn args, h)) (hfit : FitsIn cap P Hh (srcCfg e fn args, h))
    (s : Store Hc) (mi : ModuleInst) (hH : HoldsProg s mi (asyncifyProg P))
    (hg : GlobalsAre s ⟨[], mi⟩ P.tGlobals) (hm : MemAre s ⟨[], mi⟩ (fun _ => 0) cap)
    {o : Obs σ} (ho : o ∈ beh (srcStep P.env Hh) (srcCfg e fn args, h)) (hd : o ≠ .diverges) :
    CoreObs Pf host cap (asyncifyProg P) Hh mi e args s h o :=
  asyncify_fits_core fits_proved Pf host P hP Hh hcap hfn args hargs h hbound hfit s mi hH hg hm
    ho hd

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.fits_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fits_proved

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.fits_window_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fits_window_proved

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.asyncify_beh_fitsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asyncify_beh_fitsW

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.asyncify_fits_core'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asyncify_fits_core'

end Silmaril.Wasm.FX.Asyncify.Tool
