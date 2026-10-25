module

public import Silmaril.Wasm.Execution.Core.Soundness.PresWireExn

@[expose] public section

/-! # Preservation for the divergent-sequence rules `trap-instrs` / `throw_ref-instrs`

`vals vs ++ [trap] ++ rest ↪ [trap]` and `vals vs ++ throwing a ++ rest ↪ throwing a`.
The discarded `rest` may initialise locals (e.g. `local.set x` of a non-defaultable
local), so the reduct must be typable at an instruction type with initialised locals
that are *not* set in the context. This uses the typing deviation of
`Typing/Config.lean` (`AdminOk.trap` with arbitrary in-bounds initialised locals and
`AdminOk.throwRefInits`): both reducts are typed at every valid instruction type
(`AdminsOk.trap_it`, `AdminsOk.throwing_it`).

Both lemmas have the shape of the cases of `Step.preservation_gen`
(`exact pres_throwRefInstrs hne` / `exact pres_trapInstrs hne`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- `Step_read/throw_ref-instrs`. -/
theorem pres_throwRefInstrs {s : Store H} {f : Frame} {vs : List Val} {a : Nat}
    {rest : List Admin} (_hne : vs ≠ [] ∨ rest ≠ []) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct (vals vs ++ throwing a ++ rest) it →
      PresConcl ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  have hp := hty.params_ok hwf
  exact PresConcl.same hs hf hu
    (AdminsOk.throwing_it (hty.exn_existsExn (a := a) (by simp))
      ⟨hp.1, hty.results_wire hs hts hwf, hp.2⟩)

/-- `Step_pure/trap-instrs`. -/
theorem pres_trapInstrs {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    (_hne : vs ≠ [] ∨ rest ≠ []) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct (vals vs ++ [.trap] ++ rest) it →
      PresConcl ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  have hp := hty.params_ok hwf
  exact PresConcl.same hs hf hu
    (AdminsOk.trap_it ⟨hp.1, hty.results_wire hs hts hwf, hp.2⟩)

end Silmaril.Wasm.Execution.Core
