module

public import Silmaril.Wasm.SSA.Translate.Defs
public import Silmaril.Wasm.SSA.Contract.Defs
import Silmaril.Proofs.Wasm.SSA.Translate.BackRun

/-!
# From the fragment into SSA: correctness

`compileFunc_sound`: every terminating run of a fragment function (return
value or trap) is a run of its SSA translation with the same outcome. The
proof is a continuation-passing simulation by induction on the fragment's
big-step derivations (`Silmaril.Proofs.Wasm.SSA.Translate`), with a separate
invariant for loop headers.

`compileFunc_complete` is the converse: every terminating run of the
translation is a run of the source (`Silmaril.Proofs.Wasm.SSA.Translate.BackRun`,
a structural induction that inverts SSA evaluations, with an induction on
the loop header's CFG execution). Together (`compileFunc_iff`) the source and
its translation have the same terminating outcomes; in particular the source
diverges or is stuck on an input exactly when the translation has no
terminating outcome on it. The typed-block check (`select r r 1` in
`joinBlock`) is what makes the converse hold for blocks whose body produces no
value.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Compile.PassAPI

/-- **Correctness of the translation into SSA** (terminating runs). -/
theorem compileFunc_sound {f : FragFunc} {args : List WVal} {o : FOut} (h : f.Run args o) :
    (compileFunc f).Run args o :=
  Silmaril.Proofs.Wasm.SSA.Translate.compileFunc_sound h

/-- The translation as a verified translation in silmaril's IR category. -/
def toSSA : Translation fragIR ssaIR where
  run := compileFunc
  inv_run _ := trivial
  sound _ _ _ h := compileFunc_sound h

@[simp] theorem toSSA_run (f : FragFunc) : toSSA.run f = compileFunc f := rfl

/-- **The translation reflects terminating runs.** -/
theorem compileFunc_complete {f : FragFunc} {args : List WVal} {o : FOut}
    (h : (compileFunc f).Run args o) : f.Run args o :=
  Silmaril.Proofs.Wasm.SSA.Translate.compileFunc_complete h

/-- The source and its translation have the same terminating outcomes. -/
theorem compileFunc_iff {f : FragFunc} {args : List WVal} {o : FOut} :
    (compileFunc f).Run args o ↔ f.Run args o :=
  ⟨compileFunc_complete, compileFunc_sound⟩

end Silmaril.Wasm.SSA
