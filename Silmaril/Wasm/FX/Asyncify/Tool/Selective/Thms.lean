module

public import Silmaril.Wasm.FX.Asyncify.Tool.Selective.Defs
public import Silmaril.Wasm.FX.Asyncify.Tool.Thms

/-!
# The asyncify tool, selective mode: results

* `selProg_env`: the selective program has the same machine program as the source (same
  imports, same bodies), so `--selective` asyncifies the same source.
* `selProg_frameWords`, `selProg_reqWords`, `selProg_sb`: the same frame size, request area and
  shadow-stack base.
* `SelectiveBeh`: `asyncify_beh` for the selective program (the target of `selProg P` under the
  host protocol has the source's behaviours); `asyncify_beh_selective` is stated from it. It is
  proved as `selective_beh` in `Silmaril.Wasm.FX.Asyncify.Tool.SelSim.Thms`, which also states the
  unconditional `asyncify_beh_sel`. (It is a separate statement because its proof needs the
  simulation with calm calls in progress, which imports this module.)

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

theorem selStmt_code (P : Prog) (st : Stmt) : (selStmt P st).code = st.code := by
  cases st with
  | pure is => rfl
  | call f as rs =>
    by_cases h : P.imps.length ≤ f.value.val ∧ mayS P f.value.val = false
    · simp only [selStmt, h, and_self, ↓reduceIte]
      rfl
    · simp only [selStmt, h, ↓reduceIte]

theorem flatS_selStmt (P : Prog) : ∀ ss : List Stmt, flatS (ss.map (selStmt P)) = flatS ss
  | [] => rfl
  | st :: ss => by
    simp only [List.map_cons, flatS, selStmt_code, flatS_selStmt P ss]

/-- **The selective program asyncifies the same source program.** -/
theorem selProg_env (P : Prog) : (selProg P).env = P.env := by
  simp only [selProg, Prog.env, List.map_map, Function.comp_def, FnSrc.body, flatS_selStmt]

theorem selProg_frameWords (P : Prog) : (selProg P).frameWords = P.frameWords := by
  simp only [selProg, Prog.frameWords, List.map_map, Function.comp_def]
  rfl

theorem selProg_reqWords (P : Prog) : (selProg P).reqWords = P.reqWords := rfl

theorem selProg_sb (P : Prog) : (selProg P).sb = P.sb := rfl

/-- The selective program is correct on the frame machine (`asyncify_beh` for `selProg P`, with
the same source). Proved as `selective_beh` (`Silmaril.Wasm.FX.Asyncify.Tool.SelSim.Thms`). -/
def SelectiveBeh : Prop :=
  ∀ (σ : Type) (P : Prog), P.WF → ∀ (H : Host σ) (e : Nat) (fn fn' : FnSrc) (args : List W)
    (s : σ), P.fnAt e = some fn → (selProg P).fnAt e = some fn' → args.length = fn.nparams →
    DepthBound P H (srcCfg e fn args, s) →
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStep (asyncifyProg (selProg P)) H) (tgtSt (selProg P) e fn' args s)

/-- The selective mode is correct, given `SelectiveBeh` (proved: `asyncify_beh_sel`). -/
theorem asyncify_beh_selective (hT : SelectiveBeh) {σ : Type} (P : Prog) (hP : P.WF)
    (H : Host σ) {e : Nat} {fn fn' : FnSrc} (hfn : P.fnAt e = some fn)
    (hfn' : (selProg P).fnAt e = some fn') (args : List W) (hargs : args.length = fn.nparams)
    (s : σ) (hb : DepthBound P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStep (asyncifyProg (selProg P)) H) (tgtSt (selProg P) e fn' args s) :=
  hT σ P hP H e fn fn' args s hfn hfn' hargs hb

end Silmaril.Wasm.FX.Asyncify.Tool
