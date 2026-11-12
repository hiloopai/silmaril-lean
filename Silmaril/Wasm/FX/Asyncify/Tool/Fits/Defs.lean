module

public import Silmaril.Wasm.FX.Asyncify.Tool.Bounded.Defs

/-!
# The asyncified program stays in bounds: what is left open

`Silmaril.Wasm.FX.Asyncify.Tool.Fits.Thms` proves `Task.fits` (`Silmaril.Wasm.FX.Asyncify.Tool.Bounded`)
for every source run within `DepthBound` (the shadow stack stays below `2 ^ 32`), in particular
whenever `cap < 2 ^ 32` (every Wasm 32 memory, and every output of the tool, which has fewer than
`65536` pages). What is left is the case where a reachable source state needs a shadow stack of
`2 ^ 32` bytes or more: then `FitsIn` forces `cap ≥ 2 ^ 32`, `sp` wraps around, and the
simulation of `asyncify_beh` (which reads `sp` as a natural number below `2 ^ 32`) does not
apply. That case is frozen here as `Task.fits_wrap`; `Task.fits` follows from it
(`fits_of_wrap`). A memory of at least `2 ^ 32 + 4 · max F R` bytes is never overrun at all
(`fits_wide`), so what is left is the window `Task.fits_window` below that size
(`fits_wrap_of_window`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

/-- **Open target** (frozen, not proved): `Task.fits` for source runs that leave `DepthBound`, i.e.
that reach a state whose frames need `2 ^ 32` bytes or more of shadow stack. -/
def Task.fits_wrap : Prop :=
  ∀ (P : Prog) (_ : P.WF) {σ : Type} (H : Host σ) (cap : Nat) (e : Nat) (fn : FnSrc)
    (args : List W) (s : σ), P.imps.length ≤ e → P.fns[e - P.imps.length]? = some fn →
    args.length = fn.nparams →
    ¬ DepthBound P H (⟨[entry e ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ args], [],
      fun _ => 0⟩, s) →
    FitsIn cap P H (⟨[entry e ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ args], [], fun _ => 0⟩, s) →
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg)
      ⟨⟨[entry e ⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ args],
        P.tGlobals, fun _ => 0⟩, s, e, args⟩

/-- **Open target** (frozen, not proved): `Task.fits_wrap` for memories of fewer than
`2 ^ 32 + 4 · max F R` bytes (`F` the frame size, `R` the request area in words). -/
def Task.fits_window : Prop :=
  ∀ (P : Prog) (_ : P.WF) {σ : Type} (H : Host σ) (cap : Nat) (e : Nat) (fn : FnSrc)
    (args : List W) (s : σ), P.imps.length ≤ e → P.fns[e - P.imps.length]? = some fn →
    args.length = fn.nparams → cap < 2 ^ 32 + 4 * max P.frameWords P.reqWords →
    ¬ DepthBound P H (⟨[entry e ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ args], [],
      fun _ => 0⟩, s) →
    FitsIn cap P H (⟨[entry e ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ args], [], fun _ => 0⟩, s) →
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg)
      ⟨⟨[entry e ⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ args],
        P.tGlobals, fun _ => 0⟩, s, e, args⟩

end Silmaril.Wasm.FX.Asyncify.Tool
