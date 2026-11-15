module

public import Silmaril.Wasm.Abstract.DivO.Defs
public import Silmaril.Wasm.Interp.Diverge.Thms
import Silmaril.Proofs.Wasm.Abstract.DivO.Basic
import Silmaril.Proofs.Wasm.Abstract.DivO.Decomp

/-!
# Coinductive divergence of the open native semantics: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.DivO`.

* `evalDivO_iff_step`, `localDivO_iff_step`: unfolding; `evalDivO_of_coind`,
  `localDivO_of_coind`: coinduction;
* **the closure** (`divStepO_closed_iff`, `evalDivO_closed`, `localDivO_closed`): at
  `C = closedCall`, `DivStepO` is `Interp.DivStep`, and `EvalDivO`/`LocalDivO` are
  `Interp.EvalDiv`/`LocalDiv`. So the oracle form generalizes the existing divergence.

**Decomposition**, any oracle `C` (the oracle form of `Abstract.Decomp`, #322):

* `evalDivO_decomp`: a diverging problem diverges within its function (`LocalDivO C`), or
  reaches (`ReachO C`) a call whose body diverges (`CallDivO C`);
* `callDivO_path_or_chain`: a diverging call reaches a locally diverging call
  (`LocalCallDivO C`) by finitely many descents (`z = x ∨ PendO C x z`), or starts an
  infinite chain of descents (`BodyReachO C`);
* the converses: `reachO_evalDivO`, `callDivO_of_local`, `callDivO_of_bodyReach`,
  `callDivO_of_pendO`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (Problem DivStep)

variable {H : Type} {C : CallRel H}

theorem DivStepO.mono' {X X' Y Y' : Problem H} (hX : X ≤ X') (hY : Y ≤ Y') :
    DivStepO C X Y ≤ DivStepO C X' Y' :=
  fun _ _ _ _ h => h.mono hX hY

/-- Unfolding open divergence once. -/
theorem evalDivO_iff_step {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    EvalDivO C s f stk es ↔ DivStepO C (EvalDivO C) (EvalDivO C) s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.DivO.evalDivO_iff_step

/-- Unfolding local divergence once. -/
theorem localDivO_iff_step {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    LocalDivO C s f stk es ↔ DivStepO C (LocalDivO C) ⊥ s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.DivO.localDivO_iff_step

/-- Coinduction for open divergence. -/
theorem evalDivO_of_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStepO C X X s f stk es) : X ≤ EvalDivO C :=
  Silmaril.Proofs.Wasm.Abstract.DivO.evalDivO_of_coind h

/-- Coinduction for local divergence. -/
theorem localDivO_of_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStepO C X ⊥ s f stk es) : X ≤ LocalDivO C :=
  Silmaril.Proofs.Wasm.Abstract.DivO.localDivO_of_coind h

/-- At the closure, the open unfolding is `Interp.DivStep`. -/
theorem divStepO_closed_iff {X Y : Problem H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} : DivStepO closedCall X Y s f stk es ↔ DivStep X Y s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.DivO.divStepO_closed_iff

/-- **At the closure, open divergence is `Interp.EvalDiv`.** -/
theorem evalDivO_closed : EvalDivO (closedCall : CallRel H) = Interp.EvalDiv :=
  Silmaril.Proofs.Wasm.Abstract.DivO.evalDivO_closed

/-- **At the closure, local divergence is `Interp.LocalDiv`.** -/
theorem localDivO_closed : LocalDivO (closedCall : CallRel H) = Interp.LocalDiv :=
  Silmaril.Proofs.Wasm.Abstract.DivO.localDivO_closed

/-- Reaching a diverging call diverges. -/
theorem reachO_evalDivO {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : ReachO C s f stk es y) (hy : CallDivO C y) :
    EvalDivO C s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.DivO.reachO_evalDivO h hy

/-- **A diverging problem diverges within its function or reaches a diverging call.** -/
theorem evalDivO_decomp {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : EvalDivO C s f stk es) :
    LocalDivO C s f stk es ∨ ∃ y, ReachO C s f stk es y ∧ CallDivO C y :=
  Silmaril.Proofs.Wasm.Abstract.DivO.evalDivO_decomp h

/-- Local divergence is divergence. -/
theorem localDivO_le_evalDivO : LocalDivO C ≤ EvalDivO C :=
  Silmaril.Proofs.Wasm.Abstract.DivO.localDivO_le_evalDivO

/-- Local divergence of a call is divergence. -/
theorem callDivO_of_local {x : (wasmOShape H).self.Op} (h : LocalCallDivO C x) : CallDivO C x :=
  Silmaril.Proofs.Wasm.Abstract.DivO.callDivO_of_local h

/-- Descending into a diverging call diverges. -/
theorem callDivO_of_bodyReach {x y : (wasmOShape H).self.Op} (h : BodyReachO C x y)
    (hy : CallDivO C y) : CallDivO C x :=
  Silmaril.Proofs.Wasm.Abstract.DivO.callDivO_of_bodyReach h hy

/-- A descent (`PendO`) to a diverging call diverges. -/
theorem callDivO_of_pendO {x z : (wasmOShape H).self.Op} (h : PendO C x z)
    (hz : CallDivO C z) : CallDivO C x :=
  Silmaril.Proofs.Wasm.Abstract.DivO.callDivO_of_pendO h hz

/-- **A diverging call reaches a locally diverging call by finitely many descents, or starts
an infinite chain of descents into diverging calls.** -/
theorem callDivO_path_or_chain {x : (wasmOShape H).self.Op} (h : CallDivO C x) :
    (∃ z, (z = x ∨ PendO C x z) ∧ LocalCallDivO C z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = x ∧ ∀ n, BodyReachO C (g n) (g (n + 1)) :=
  Silmaril.Proofs.Wasm.Abstract.DivO.callDivO_path_or_chain h

end Silmaril.Wasm.Abstract
