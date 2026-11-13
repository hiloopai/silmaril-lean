module

public import Silmaril.Wasm.Jco.Wrap.Defs
public import Silmaril.Proofs.Wasm.Jco.Wrap.Basic

/-!
# The monadic construction: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Wrap.Basic`.

* `wrap_world`: the wrapper component exports exactly the world's functions, in order.
* **`wrap_correct`**: for every core instance `M` and metadata `md` such that `M`'s exports have
  the C convention's core result types (`Meta.Conforms`), calling export `name` of `wrap md`
  (canonical-ABI lowering into `M`'s memory through the adaptor's `cabi_realloc`, the adaptor's
  export shim, canonical lifting) **is** calling world function `name` of `M` under the C
  convention: the two relations between start states and terminating outcomes (results with
  final states, or traps) are equal. In particular the component traps exactly when the
  convention traps, and both are deterministic exactly when `M` is.
* `wrap_correct_seq`: the same for sequences of calls (the component keeps no state besides
  `M`'s).
* the ingredients, for reuse: `canonCall_wrap` (one lift), `lowerParams_wrap` (lowering through
  `cabi_realloc` is copying through `alloc`), `run_plain`/`run_out` (the export shims).

Divergence is not covered: `RM` relates states to terminating outcomes only.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

theorem wrap_world (md : Meta) : (wrap md).world = md.world := by
  suffices h : ∀ k ws, (liftsFrom k ws).map (·.sig) = ws from h 0 md.world
  intro k ws
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih => simp [liftsFrom, ih]

/-- **The behaviour theorem of the monadic construction.** -/
theorem wrap_correct (M : CoreInst) (md : Meta) (hC : md.Conforms M) (name : String)
    (vs : List PVal) : (wrap md).callExport M name vs = md.spec M name vs :=
  Silmaril.Proofs.Wasm.Jco.wrap_callExport M md hC name vs

/-- A sequence of export calls; the results in order. -/
def runCalls {σ : Type} (f : String → List PVal → RM σ (Option PVal)) :
    List (String × List PVal) → RM σ (List (Option PVal))
  | [] => pure []
  | (n, vs) :: cs => do
    let r ← f n vs
    let rs ← runCalls f cs
    pure (r :: rs)

theorem wrap_correct_seq (M : CoreInst) (md : Meta) (hC : md.Conforms M)
    (calls : List (String × List PVal)) :
    runCalls ((wrap md).callExport M) calls = runCalls (md.spec M) calls := by
  have h : (wrap md).callExport M = md.spec M := by
    funext name vs
    exact wrap_correct M md hC name vs
  rw [h]

/-- One lift of the wrapper behaves as the convention's call of its world function. -/
theorem canonCall_wrap (M : CoreInst) (md : Meta) (hC : md.Conforms M) (i : Nat) (s : Sig)
    (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCall M ((wrap md).callRef M (.adapt 0)) ((wrap md).callRef M (.adapt (i + 1))) s vs =
      md.specCall M s vs :=
  Silmaril.Proofs.Wasm.Jco.canonCall_wrap M md hC i s hi vs

/-- Canonical lowering through the adaptor's `cabi_realloc` is the convention's copy through
`alloc`. -/
theorem lowerParams_wrap (M : CoreInst) (md : Meta) (ps : List PTy) (vs : List PVal) :
    lowerParams M ((wrap md).callRef M (.adapt 0)) ps vs = md.specParams M ps vs :=
  Silmaril.Proofs.Wasm.Jco.lowerParams_wrap M md ps vs

end Silmaril.Wasm.Jco
