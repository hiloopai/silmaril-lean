module

public import Silmaril.Wasm.FX.Asyncify.Tool.SelSim.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.SelSim.Inst

/-!
# The selective mode is correct: results

* **`asyncify_beh_selOk`** (proved in `Silmaril/Proofs/Wasm/FX/Asyncify/Tool/SelSim`): the
  simulation of `asyncify_beh` for every program `Q` with `SelOk Q C`, i.e. well formed except
  that a pure statement may hold the code of a call statement to a function of `C`, every
  function of `C` being a defined function with pure statements only. The relation `RelS` adds to
  `Rel` the frames of a calm call in progress, which source and target run in lockstep (the
  target's calm functions run in normal mode: their prologue and guards pass, and they never
  unwind).
* `selProg_selOk`: `selProg P` satisfies `SelOk` with `C = SelCalm P` for every well-formed `P`
  (via `calm_calls`, `calm_defined` of `Tool/Calm`).
* **`selective_beh : SelectiveBeh`**: the statement of `Tool/Selective` is proved, so
  `asyncify_beh_sel` is `asyncify_beh_selective` without its hypothesis.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

variable {σ : Type}

theorem srcCfg_selFn (P : Prog) (e : Nat) (fn : FnSrc) (args : List W) :
    srcCfg e (selFn P fn) args = srcCfg e fn args := by
  simp only [srcCfg, selFn_body]
  rfl

theorem depthBound_selProg {P : Prog} {H : Host σ} {x : Cfg × σ} :
    DepthBound (selProg P) H x ↔ DepthBound P H x := by
  unfold DepthBound
  rw [selProg_env, selProg_sb, selProg_frameWords]

/-- **`SelectiveBeh` holds**: the selective output asyncifies its source correctly. -/
theorem selective_beh : SelectiveBeh := by
  intro σ P hP H e fn fn' args s hfn hfn' hargs hb
  have hfn'' : fn' = selFn P fn := by
    rw [selProg_fnAt, hfn] at hfn'
    exact (Option.some.inj hfn').symm
  subst hfn''
  have h := asyncify_beh_selOk (selProg P) (SelCalm P) (selProg_selOk hP) H hfn' args
    (by simpa [selFn] using hargs) s (depthBound_selProg.2 (by rwa [srcCfg_selFn]))
  rwa [selProg_env, srcCfg_selFn] at h

/-- **The selective mode is correct** (`asyncify_beh_selective` without its hypothesis). -/
theorem asyncify_beh_sel (P : Prog) (hP : P.WF) (H : Host σ) {e : Nat} {fn fn' : FnSrc}
    (hfn : P.fnAt e = some fn) (hfn' : (selProg P).fnAt e = some fn') (args : List W)
    (hargs : args.length = fn.nparams) (s : σ) (hb : DepthBound P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStep (asyncifyProg (selProg P)) H) (tgtSt (selProg P) e fn' args s) :=
  asyncify_beh_selective selective_beh P hP H hfn hfn' args hargs s hb

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.selective_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selective_beh

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.asyncify_beh_selOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asyncify_beh_selOk

end Silmaril.Wasm.FX.Asyncify.Tool
