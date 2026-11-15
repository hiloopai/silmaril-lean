module

public import Silmaril.Wasm.Abstract.DivO.Defs
public import Silmaril.Wasm.Interp.Diverge.Thms
import Silmaril.Proofs.Wasm.Abstract.DivO.Basic

/-!
# Coinductive divergence of the open native semantics: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.DivO`.

* `evalDivO_iff_step`, `localDivO_iff_step`: unfolding; `evalDivO_of_coind`,
  `localDivO_of_coind`: coinduction;
* **the closure** (`divStepO_closed_iff`, `evalDivO_closed`, `localDivO_closed`): at
  `C = closedCall`, `DivStepO` is `Interp.DivStep`, and `EvalDivO`/`LocalDivO` are
  `Interp.EvalDiv`/`LocalDiv`. So the oracle form generalizes the existing divergence.
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
    EvalDivO C s f stk es ↔ DivStepO C (EvalDivO C) (EvalDivO C) s f stk es := by
  unfold EvalDivO; conv_lhs => rw [← OrderHom.map_gfp (divOpO C)]
  rfl

/-- Unfolding local divergence once. -/
theorem localDivO_iff_step {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    LocalDivO C s f stk es ↔ DivStepO C (LocalDivO C) ⊥ s f stk es := by
  unfold LocalDivO; conv_lhs => rw [← OrderHom.map_gfp (localDivOpO C)]
  rfl

/-- Coinduction for open divergence. -/
theorem evalDivO_of_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStepO C X X s f stk es) : X ≤ EvalDivO C :=
  OrderHom.le_gfp (divOpO C) fun s f stk es hx => h s f stk es hx

/-- Coinduction for local divergence. -/
theorem localDivO_of_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStepO C X ⊥ s f stk es) : X ≤ LocalDivO C :=
  OrderHom.le_gfp (localDivOpO C) fun s f stk es hx => h s f stk es hx

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

end Silmaril.Wasm.Abstract
