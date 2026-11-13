module

public import Silmaril.Wasm.FX.Asyncify.Tool.CoreSim.Thms
public import Silmaril.Wasm.FX.Asyncify.Tool.Thms
public import Silmaril.Wasm.FX.Asyncify.Tool.Bounded.Thms
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSys.Run
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSys.Upd

/-!
# The asyncify host protocol on Core 3.0: results

The header of `Defs`; proofs in `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSys.*`. **Proved**, for
every profile and host of silmaril-lean's Core 3.0 `Step`, every deterministic host `Hh` of the
protocol and a memory of `cap ≥ SB` bytes:

* `asyncify_core`: every behaviour of the bounded target system (`tgtStepB`, the asyncified
  program under the host protocol) other than divergence is an observation of the protocol on
  Core (`CoreObs`), from a store that holds the asyncified program, the initial globals
  `Prog.tGlobals` and a zero memory: the same results with the same final host state, the same
  traps, through the same rounds of export calls, each a Core 3.0 run;
* `asyncify_src_core`: with `asyncify_beh_safe`, when the target stays in bounds (`Safe`), every
  terminating source behaviour (results with the final host state, or a trap) is such a Core
  observation; `asyncify_fits_core` the same conditional on `Task.fits`;
* `hostUpd_exists`: a store realizing the host's update between two rounds exists, so the
  `round` case of `CoreObs` (which quantifies over every such store) is not vacuous.

Not proved: divergence on Core (a diverging target need not be matched by an infinite Core run
here, since a machine step can be zero Core steps: constants are values in Core), and the
converse direction (every Core observation is a target behaviour), which would need determinism
of Core `Step`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSys

variable {H σ : Type}

theorem ginv_tGlobals (P : Prog) (hP : P.WF) : GInv P.tGlobals := by
  have hb := (Prog.wf_bounds hP).2
  refine ⟨rfl, fun v hv => ?_⟩
  have hv' : BitVec.ofNat 32 P.sb = v := Option.some.inj hv
  rw [← hv', BitVec.toNat_ofNat]
  simp only [Prog.sb]
  omega

theorem reqFits (P : Prog) {cap : Nat} (hcap : P.sb ≤ cap) : ReqFits cap (asyncifyProg P) := by
  have h1 := Prog.reqWords_pos P
  refine ⟨by simp only [Prog.sb] at hcap; omega, fun n m hm => ?_⟩
  have h2 := Prog.imp_le hm
  simp only [Prog.sb] at hcap
  omega

/-- **Every terminating behaviour of the bounded target is a Core 3.0 observation.** -/
theorem asyncify_core (Pf : Profile) (host : HostSemantics H) (P : Prog) (hP : P.WF)
    (Hh : Host σ) {cap : Nat} (hcap : P.sb ≤ cap) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (h : σ)
    (s : Store H) (mi : ModuleInst) (hH : HoldsProg s mi (asyncifyProg P))
    (hg : GlobalsAre s ⟨[], mi⟩ P.tGlobals) (hm : MemAre s ⟨[], mi⟩ (fun _ => 0) cap)
    {o : Obs σ} (ho : o ∈ beh (tgtStepB cap (asyncifyProg P) Hh) (tgtSt P e fn args h))
    (hd : o ≠ .diverges) : CoreObs Pf host cap (asyncifyProg P) Hh mi e args s h o := by
  have hge := Prog.fnAt_ge hfn
  have hfd := Prog.tgt_fn hfn
  have hEn : EntryOk (asyncifyProg P) e args := ⟨hge, fid_lt hP hge hfd, _, hfd, hargs⟩
  obtain ⟨hsteps, hR⟩ := crel_init (Pf := Pf) (host := host) (cap := cap) (envOk_asyncify hP)
    hH hge (fid_lt hP hge hfd) hfd hargs hg hm (ginv_tGlobals P hP)
  rcases ho with ⟨k, hk⟩ | ⟨hdv, -⟩
  · exact obs_of_runN (envOk_asyncify hP) (reqFits P hcap) k (tgtSt P e fn args h) s s _ o
      hsteps hR hEn hk
  · exact absurd hdv hd

/-- **In bounds, every terminating source behaviour is a Core 3.0 observation.** -/
theorem asyncify_src_core (Pf : Profile) (host : HostSemantics H) (P : Prog) (hP : P.WF)
    (Hh : Host σ) {cap : Nat} (hcap : P.sb ≤ cap) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (h : σ)
    (hbound : DepthBound P Hh (srcCfg e fn args, h))
    (hsafe : Safe (tgtStep (asyncifyProg P) Hh) (fun t => OOB cap t.cfg) (tgtSt P e fn args h))
    (s : Store H) (mi : ModuleInst) (hH : HoldsProg s mi (asyncifyProg P))
    (hg : GlobalsAre s ⟨[], mi⟩ P.tGlobals) (hm : MemAre s ⟨[], mi⟩ (fun _ => 0) cap)
    {o : Obs σ} (ho : o ∈ beh (srcStep P.env Hh) (srcCfg e fn args, h)) (hd : o ≠ .diverges) :
    CoreObs Pf host cap (asyncifyProg P) Hh mi e args s h o := by
  rw [asyncify_beh_safe P hP Hh cap hfn args hargs h hbound hsafe] at ho
  exact asyncify_core Pf host P hP Hh hcap hfn args hargs h s mi hH hg hm ho hd

/-- **Conditional on `Task.fits`**: when every source state fits its frames in `cap` bytes, every
terminating source behaviour is a Core 3.0 observation. -/
theorem asyncify_fits_core (ht : Task.fits) (Pf : Profile) (host : HostSemantics H) (P : Prog)
    (hP : P.WF) (Hh : Host σ) {cap : Nat} (hcap : P.sb ≤ cap) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (h : σ)
    (hbound : DepthBound P Hh (srcCfg e fn args, h)) (hfit : FitsIn cap P Hh (srcCfg e fn args, h))
    (s : Store H) (mi : ModuleInst) (hH : HoldsProg s mi (asyncifyProg P))
    (hg : GlobalsAre s ⟨[], mi⟩ P.tGlobals) (hm : MemAre s ⟨[], mi⟩ (fun _ => 0) cap)
    {o : Obs σ} (ho : o ∈ beh (srcStep P.env Hh) (srcCfg e fn args, h)) (hd : o ≠ .diverges) :
    CoreObs Pf host cap (asyncifyProg P) Hh mi e args s h o := by
  rw [asyncify_beh_fits ht P hP Hh cap hfn args hargs h hbound hfit] at ho
  exact asyncify_core Pf host P hP Hh hcap hfn args hargs h s mi hH hg hm ho hd

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.asyncify_src_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asyncify_src_core

end Silmaril.Wasm.FX.Asyncify.Tool
