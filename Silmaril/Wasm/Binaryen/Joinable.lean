module

public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Execution.Core.Typing.Config

@[expose] public section

/-! # The one hard bridge: joinability implies contextual equivalence

Local rewrites are justified by a small-step fact about the lowered code alone:
from every configuration that fits the typing, both sides reach a **common**
configuration (`Joinable`), or both reach the **same control transfer** up to
dead trailing code (`JoinableBot`). Steps are taken under `closedHost`, so they
include no host call; a run under any other host contains them.

`joinable_seqEquiv` turns that into `SeqEquiv Eq` (both directions). Proof plan:
use a code simulation with the store relation
"function bodies related by `K.plug es` / `K.plug es'`". Under a deterministic
profile (`Profile.deterministic o`; `SingleThreaded/Determinism.lean`) the
source run from the plugged configuration passes through the join point, which
gives the backward direction and transfers divergence. The statement is first
proved for `closedHost`, then for any `HostRespectsCode` host (hosts must
respect typing).

**Scope.** This module does not establish the legacy general results the bridge theorems
`joinable_seqEquiv`, `joinableBot_seqEquiv` and `joinableTrap_seqRefines`. The toolkit contracts are supplied by separate proof modules.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

/-- A configuration fits `C ⊢ _ : it`: a valid store, a frame typed by `C` (without
labels or return), and operand values of the parameter types. -/
def Fits {H : Type} (C : Context) (it : InstrType) (s : Store H) (f : Frame) (vs : List Val) :
    Prop :=
  StoreOk s ∧ FrameOk s f { C with labels := [], return_ := none } ∧
    List.Forall₂ (ValOk s) vs it.params

/-- The configuration running `es` from `s, f` on operand stack `vs`. -/
def codeConfig {H : Type} (s : Store H) (f : Frame) (vs : List Val) (es : List BExpr) : Config H :=
  ⟨s, f, vals vs ++ expression (BExpr.lowerList es)⟩

/-- **Joinability.** From every fitting configuration, both sides reach a common
configuration without host calls. -/
def Joinable (P : Profile) (C : Context) (it : InstrType) (es es' : List BExpr) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (vs : List Val), Fits C it s f vs →
    ∃ c, Steps P closedHost (codeConfig s f vs es) c ∧ Steps P closedHost (codeConfig s f vs es') c

/-- An administrative instruction that transfers control out of a bare sequence. -/
def Admin.IsTransfer : Admin → Prop
  | .trap => True
  | .plain (.br _) => True
  | .plain .return_ => True
  | .plain .throwRef => True
  | _ => False

/-- **Joinability up to a control transfer.** Either `Joinable`, or the source
reaches a transfer (trap, `br`, `return`, throw) that the target also reaches with
the same values, store and frame, differing only in dead trailing code; or both
diverge. This is what dead-code elimination needs. -/
def JoinableBot (P : Profile) (C : Context) (it : InstrType) (es es' : List BExpr) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (vs : List Val), Fits C it s f vs →
    (∃ c, Steps P closedHost (codeConfig s f vs es) c ∧
      Steps P closedHost (codeConfig s f vs es') c) ∨
    (∃ (s' : Store H) (f' : Frame) (ws : List Val) (k : Admin) (junk junk' : List Admin),
      Admin.IsTransfer k ∧
      Steps P closedHost (codeConfig s f vs es) ⟨s', f', vals ws ++ k :: junk⟩ ∧
      Steps P closedHost (codeConfig s f vs es') ⟨s', f', vals ws ++ k :: junk'⟩) ∨
    (Diverges P closedHost (codeConfig s f vs es) ∧ Diverges P closedHost (codeConfig s f vs es'))

theorem Joinable.symm {P : Profile} {C : Context} {it : InstrType} {es es' : List BExpr}
    (h : Joinable P C it es es') : Joinable P C it es' es :=
  fun s f vs hf => let ⟨c, h₁, h₂⟩ := h s f vs hf; ⟨c, h₂, h₁⟩

theorem Joinable.refl (P : Profile) (C : Context) (it : InstrType) (es : List BExpr) :
    Joinable P C it es es :=
  fun _ _ _ _ => ⟨_, .refl, .refl⟩

theorem Joinable.joinableBot {P : Profile} {C : Context} {it : InstrType} {es es' : List BExpr}
    (h : Joinable P C it es es') : JoinableBot P C it es es' :=
  fun s f vs hf => Or.inl (h s f vs hf)

end Silmaril.Wasm.Binaryen
