module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Wrap.Main

/-!
# The pass is correct when the records start below `2 ^ 32`

`SimSafeW` carries the full one-step obligation of the simulation, not only the bounds. Under
`DepthBoundW` every source state fits into `2 ^ 32 + 4 F` bytes, so `simSafeW_of_rel` gives a
stuttering simulation `isSimW` with `RelW`, and `asyncify_behW` is `asyncify_beh` with
`DepthBoundW` in place of `DepthBound`: the shadow stack's last record may end above
`2 ^ 32`, so the `sp` of a suspended run may wrap around.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- `DepthBoundW` is `FitsIn (2 ^ 32 + 4 F)`. -/
theorem fitsIn_of_boundW {P : Prog} {H : Host σ} {x : Cfg × σ} (h : DepthBoundW P H x) :
    FitsIn (2 ^ 32 + 4 * P.frameWords) P H x := fun n y hy => Nat.le_of_lt (h n y hy)

theorem boundW_of_fitsIn {P : Prog} {H : Host σ} {x : Cfg × σ} {cap : Nat}
    (hcap : cap < 2 ^ 32 + 4 * P.frameWords) (h : FitsIn cap P H x) : DepthBoundW P H x :=
  fun n y hy => Nat.lt_of_le_of_lt (h n y hy) hcap

/-- **The stuttering simulation with `RelW`.** -/
theorem isSimW (P : Prog) (H : Host σ) :
    IsSim (srcStep P.env H) (tgtStep (asyncifyProg P) H) (RelW P H) mu where
  stop := fun _ _ o hR h =>
    have hok := simSafeW_of_rel (cap := 2 ^ 32 + 4 * P.frameWords) hR (fitsIn_of_boundW hR.bound)
    have ⟨n, hn, _⟩ := hok.1 o h
    ⟨n, hn⟩
  next := fun _ _ x' hR h =>
    have hok := simSafeW_of_rel (cap := 2 ^ 32 + 4 * P.frameWords) hR (fitsIn_of_boundW hR.bound)
    have ⟨n, t', hn, hR', hd, _⟩ := hok.2 x' h
    ⟨n, t', hn, hR', hd⟩

/-- **Correctness of the asyncify pass within `DepthBoundW`** (`asyncify_beh` with the weaker
bound: every record starts below `2 ^ 32`). -/
theorem asyncify_behW (P : Prog) (hP : P.WF) (H : Host σ) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (s : σ)
    (hbound : DepthBoundW P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStep (asyncifyProg P) H) (tgtSt P e fn args s) := by
  have e1 : Steps (asyncifyProg P) (3 + 1) ⟨[entry e (tdef P fn) args], P.tGlobals, fun _ => 0⟩
      ⟨[⟨e, args ++ List.replicate (P.frameWords - fn.nparams) 0, [],
        trS (P.ctx fn) 0 fn.stmts ++ fn.tail, fn.nres⟩], P.tGlobals, fun _ => 0⟩ := by
    have h := steps_ite (E := asyncifyProg P) (fr := ⟨e, args ++
      List.replicate (P.frameWords - fn.nparams) 0, [], [], fn.nres⟩) (rest := [])
      (t := restoreCode P.frameWords) (e := []) (K := trS (P.ctx fn) 0 fn.stmts ++ fn.tail)
      (seg_prologue_normal P _ (fun _ => 0))
    simpa [entry, tdef, Prog.tBody, prologue, ifThen, List.append_assoc] using h
  rw [beh_shift (e1.tgt_of (H := H) (t := tgtSt P e fn args s) rfl)]
  exact beh_eq_of_sim (isSimW P H) ⟨hP, rfl, ⟨_, _, [], [], [], rfl, rfl,
    TopR.ofEntry hP hfn rfl hargs, .nil e⟩, rfl, ⟨fn, hfn, hargs⟩, hbound⟩

end Silmaril.Wasm.FX.Asyncify.Tool
