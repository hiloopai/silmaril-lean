module

public import Silmaril.Wasm.FX.Asyncify.Tool.Bounded.Thms
public import Silmaril.Wasm.FX.Asyncify.Tool.CoreSys.Thms
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.WideEnv

/-!
# The asyncified program stays in bounds: results

The header of `Defs`. The open target `Task.fits` of `Silmaril.Wasm.FX.Asyncify.Tool.Bounded` asks
that the asyncified program never accesses memory past `cap` when every source state fits its
frames, `4 F` bytes each, above the request area (`FitsIn cap`).

* **`asyncify_fits_safe`**: proved for every source run within `DepthBound` (the shadow stack
  stays below `2 ^ 32`). The proof is the simulation of `asyncify_beh` with every target state in
  bounds (`SimSafe`, `safe_of_rel`): the macro steps of a suspension (`unwind`, `rewinds_chain`)
  are redone as in-bounds chains (`StepsS`), saving and restoring one record per source frame at
  `SB, SB + 4 F, …, SB + 4 F · (depth - 1)`; normal mode never loads or stores.
* **`fits_of_depth`**: `Task.fits` with the extra hypothesis `DepthBound`.
* **`fits_lt`**: `Task.fits` for `cap < 2 ^ 32` (there `FitsIn` implies `DepthBound`): every Wasm
  32 memory, in particular every output of the tool (fewer than `65536` pages, `fits_pages`).
* **`fits_of_wrap`**: `Task.fits` follows from the frozen remainder `Task.fits_wrap` (source runs
  outside `DepthBound`, so `cap ≥ 2 ^ 32`).
* **`fits_wide`**: a memory of at least `2 ^ 32 + 4 · max F R` bytes is never overrun, by any run
  (every access is a 32-bit operand plus an offset of the generated code: `safe_wide`). So
  `Task.fits_wrap` reduces to the window below that size, frozen as `Task.fits_window`
  (`fits_wrap_of_window`, `fits_of_window`).
* **`asyncify_beh_fits_lt`**, **`asyncify_beh_fits_dep`**: the bounded target has the source's
  behaviours, unconditionally (`asyncify_beh_fits` of `Bounded` was conditional on `Task.fits`).
* **`asyncify_fits_core_lt`**: every terminating source behaviour is a Core 3.0 observation of
  the output with a memory below `2 ^ 32` bytes into which the source fits (`asyncify_fits_core`
  of `CoreSys` was conditional on `Task.fits`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

variable {σ : Type}

/-- `FitsIn` below `2 ^ 32` bytes gives `DepthBound`. -/
theorem depthBound_of_fits {P : Prog} {H : Host σ} {cap : Nat} {x : Cfg × σ}
    (hcap : cap < 2 ^ 32) (hfit : FitsIn cap P H x) : DepthBound P H x :=
  fun n y hy => Nat.lt_of_le_of_lt (hfit n y hy) hcap

/-- **`Task.fits` within `DepthBound`.** -/
theorem fits_of_depth (P : Prog) (hP : P.WF) {σ : Type} (H : Host σ) (cap : Nat) (e : Nat)
    (fn : FnSrc) (args : List W) (s : σ) (hge : P.imps.length ≤ e)
    (hget : P.fns[e - P.imps.length]? = some fn) (hargs : args.length = fn.nparams)
    (hbound : DepthBound P H (srcCfg e fn args, s)) (hfit : FitsIn cap P H (srcCfg e fn args, s)) :
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg) (tgtSt P e fn args s) := by
  have hfn : P.fnAt e = some fn := by simp [Prog.fnAt, hge, hget]
  exact asyncify_fits_safe P hP H cap hfn args hargs s hbound hfit

/-- **`Task.fits` for memories below `2 ^ 32` bytes.** -/
theorem fits_lt (P : Prog) (hP : P.WF) {σ : Type} (H : Host σ) (cap : Nat) (hcap : cap < 2 ^ 32)
    (e : Nat) (fn : FnSrc) (args : List W) (s : σ) (hge : P.imps.length ≤ e)
    (hget : P.fns[e - P.imps.length]? = some fn) (hargs : args.length = fn.nparams)
    (hfit : FitsIn cap P H (srcCfg e fn args, s)) :
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg) (tgtSt P e fn args s) :=
  fits_of_depth P hP H cap e fn args s hge hget hargs (depthBound_of_fits hcap hfit) hfit

/-- The memory of the tool's output (fewer than `65536` pages) has fewer than `2 ^ 32` bytes. -/
theorem fits_pages {pages : Nat} (h : pages < 65536) : capOf pages < 2 ^ 32 := by
  unfold capOf; omega

/-- **`Task.fits` follows from its remainder outside `DepthBound`.** -/
theorem fits_of_wrap (h : Task.fits_wrap) : Task.fits := by
  intro P hP σ H cap e fn args s hge hget hargs hfit
  by_cases hb : DepthBound P H (srcCfg e fn args, s)
  · exact fits_of_depth P hP H cap e fn args s hge hget hargs hb hfit
  · exact h P hP H cap e fn args s hge hget hargs hb hfit

/-- **`Task.fits` for memories of at least `2 ^ 32 + 4 · max F R` bytes**, without `FitsIn`. -/
theorem fits_wide (P : Prog) (hP : P.WF) {σ : Type} (H : Host σ) (cap : Nat)
    (hcap : 2 ^ 32 + 4 * max P.frameWords P.reqWords ≤ cap) (e : Nat) (fn : FnSrc) (args : List W)
    (s : σ) (hge : P.imps.length ≤ e) (hget : P.fns[e - P.imps.length]? = some fn) :
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg) (tgtSt P e fn args s) := by
  have hfn : P.fnAt e = some fn := by simp [Prog.fnAt, hge, hget]
  exact safe_wide P hP H hcap hfn args s

/-- **`Task.fits_wrap` reduces to the window below `2 ^ 32 + 4 · max F R` bytes.** -/
theorem fits_wrap_of_window (h : Task.fits_window) : Task.fits_wrap := by
  intro P hP σ H cap e fn args s hge hget hargs hb hfit
  by_cases hc : cap < 2 ^ 32 + 4 * max P.frameWords P.reqWords
  · exact h P hP H cap e fn args s hge hget hargs hc hb hfit
  · exact fits_wide P hP H cap (by omega) e fn args s hge hget

theorem fits_of_window (h : Task.fits_window) : Task.fits := fits_of_wrap (fits_wrap_of_window h)

/-- **The bounded target has the source's behaviours** within `DepthBound`, when every source
state fits its frames into `cap` bytes (`asyncify_beh_fits` without `Task.fits`). -/
theorem asyncify_beh_fits_dep (P : Prog) (hP : P.WF) (H : Host σ) (cap : Nat) {e : Nat}
    {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams)
    (s : σ) (hbound : DepthBound P H (srcCfg e fn args, s))
    (hfit : FitsIn cap P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStepB cap (asyncifyProg P) H) (tgtSt P e fn args s) :=
  asyncify_beh_safe P hP H cap hfn args hargs s hbound
    (asyncify_fits_safe P hP H cap hfn args hargs s hbound hfit)

/-- **The bounded target has the source's behaviours** for a memory below `2 ^ 32` bytes, when
every source state fits its frames into it. -/
theorem asyncify_beh_fits_lt (P : Prog) (hP : P.WF) (H : Host σ) (cap : Nat)
    (hcap : cap < 2 ^ 32) {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W)
    (hargs : args.length = fn.nparams) (s : σ) (hfit : FitsIn cap P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStepB cap (asyncifyProg P) H) (tgtSt P e fn args s) :=
  asyncify_beh_fits_dep P hP H cap hfn args hargs s (depthBound_of_fits hcap hfit) hfit

open Silmaril.Wasm.Execution.Core in
open Silmaril.Wasm.Numerics (Profile) in
/-- **Every terminating source behaviour is a Core 3.0 observation** of the output, for a memory
below `2 ^ 32` bytes holding the request area and into which every source state fits. -/
theorem asyncify_fits_core_lt {Hc : Type} (Pf : Profile) (host : HostSemantics Hc) (P : Prog)
    (hP : P.WF) (Hh : Host σ) {cap : Nat} (hcap : P.sb ≤ cap) (hcap' : cap < 2 ^ 32) {e : Nat}
    {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams)
    (h : σ) (hfit : FitsIn cap P Hh (srcCfg e fn args, h))
    (s : Store Hc) (mi : ModuleInst) (hH : HoldsProg s mi (asyncifyProg P))
    (hg : GlobalsAre s ⟨[], mi⟩ P.tGlobals) (hm : MemAre s ⟨[], mi⟩ (fun _ => 0) cap)
    {o : Obs σ} (ho : o ∈ beh (srcStep P.env Hh) (srcCfg e fn args, h)) (hd : o ≠ .diverges) :
    CoreObs Pf host cap (asyncifyProg P) Hh mi e args s h o :=
  asyncify_src_core Pf host P hP Hh hcap hfn args hargs h (depthBound_of_fits hcap' hfit)
    (asyncify_fits_safe P hP Hh cap hfn args hargs h (depthBound_of_fits hcap' hfit) hfit)
    s mi hH hg hm ho hd

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.asyncify_fits_core_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asyncify_fits_core_lt

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.fits_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fits_lt

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.fits_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fits_of_window

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.fits_of_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fits_of_wrap

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.asyncify_beh_fits_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asyncify_beh_fits_lt

end Silmaril.Wasm.FX.Asyncify.Tool
