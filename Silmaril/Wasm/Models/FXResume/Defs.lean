module

public import Silmaril.Wasm.Models.FXBindT.Defs

/-!
# Untyped `resume` beyond fresh continuations

The WasmFX lowering (`Silmaril.Wasm.Models.FXLower`) resumes only a **fresh** continuation of a
Core function, which never suspends, and the typed relation `StepFXT`
(`Silmaril.Wasm.Models.FXBindT`) types `cont.bind` but leaves `resume` untyped. This topic studies
the untyped `resume` rule of `StepFX'` on continuations that were **captured by `suspend`** or
**partially applied by `cont.bind`**:

* `echoSrc m ct hs₀ hs E vs x`: the *echo handler*. A label of arity `m` whose continuation is
  `resume $ct hs₀`, around a handler frame `hs` whose body suspends with payload `vs` in the
  context `E`. The `(on $x 0)` clause branches to the label with the payload and the captured
  continuation, and the label's code resumes it at once, with the payload as arguments;
* `bindResumeSrc ws vs k ct ct' hs`: `ws; vs; ref.cont k; cont.bind $ct $ct'; resume $ct' hs`,
  partial application followed by a resume with the remaining arguments;
* `ResumeArity m ct n`: the typed proposal's side condition that `resume $ct` takes `n`
  arguments (`$ct` resolves to a function type with `n` parameters, read as for `BindArity`).
  `StepFX'` never checks it.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXResume

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT

/-- **The echo handler**: a handler `hs` whose body suspends with payload `vs` in context `E`,
inside a label of arity `m` that resumes the captured continuation with what it receives. -/
def echoSrc (m : Nat) (ct : TypeIdx) (hs₀ : List OnClause) (hs : List HClause) (E : CtxV)
    (vs : List FVal) (x : TagIdx) : List AdminFX :=
  [.label m [.fx (.resume ct hs₀)] [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))]]

/-- **Partial application, then resume**: bind `vs` to the continuation `k`, then resume the
result with `ws` (pushed first). -/
def bindResumeSrc (ws vs : List FVal) (k : Nat) (ct ct' : TypeIdx) (hs : List OnClause) :
    List AdminFX :=
  fvals ws ++ fvals vs ++ [.contRef k, .fx (.contBind ct ct'), .fx (.resume ct' hs)]

/-- `resume $ct` takes exactly `n` arguments in module instance `m` (the typed proposal). -/
def ResumeArity (m : ModuleInst) (ct : TypeIdx) (n : Nat) : Prop :=
  ∃ ps, contParams? m ct = some ps ∧ ps.length = n

end Silmaril.Wasm.Models.FXResume
