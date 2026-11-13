module

public import Silmaril.Wasm.Game.ULink.Runs.Defs
public import Silmaril.Wasm.Game.ULink.Thms
import Silmaril.Proofs.Wasm.Game.ULink.Runs

/-!
# A linked run splits into a consumer run answered by provider runs

For a link `L : ULink` over one store, at **every** profile:

* `ULink.linked_oruns`: a host-free run of the linked module from `⟨s, f, code⟩` (real store
  `s` with the link's layout) to a result is an `ORuns` run of the consumer from
  `⟨L.stubS s, f, code⟩` to the stubbed final configuration, whose calls are stub calls
  answered by host-free runs of the provider's invocations in the real store at the call
  (`ULink.provAns`). No typing hypothesis: it reuses the backward step lemmas of the untyped
  link (`linked_step`, `step_fill_inv`).
* `ULink.layout_of_funcs`, `ULink.invoke_stubS`: the layout depends on the functions only;
  invocations in the stubbed store have the same code.

Proofs: `Silmaril.Proofs.Wasm.Game.ULink.Runs`. New theorems.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.ULink

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {L : ULink}

/-- The layout depends on the functions only. -/
theorem layout_of_funcs {s s' : Store Nat} (h : L.Layout s) (hf : s'.funcs = s.funcs) :
    L.Layout s' :=
  Silmaril.Proofs.Wasm.Game.ULink.Layout.of_funcs h hf

/-- An invocation in the stubbed store has the code of the invocation in the real store. -/
theorem invoke_stubS (s : Store Nat) (a : Nat) (vs : List Val) :
    invoke (L.stubS s) a vs = ⟨L.stubS s, {}, (invoke s a vs).code⟩ :=
  Silmaril.Proofs.Wasm.Game.ULink.config_stub (L := L) s (.pending a vs)

/-- **A linked run to a result is a consumer run answered by provider runs**, every
profile. -/
theorem linked_oruns {P : Profile} {s : Store Nat} {f : Frame} {code : List Admin}
    {d : Config Nat} {r : Result} (hl : L.Layout s)
    (h : Steps P (Det.noHost (H := Nat)) ⟨s, f, code⟩ d) (hfin : d.code = r.toAdmin) :
    ∃ tr, ORuns P (L.provAns P) ⟨L.stubS s, f, code⟩ tr ⟨L.stubS d.store, d.frame, d.code⟩ :=
  Silmaril.Proofs.Wasm.Game.ULink.linked_oruns hl h hfin

end Silmaril.Wasm.Game.ULink
