module

public import Silmaril.Wasm.Behaviour.Semantics.V3.Defs
import Silmaril.Proofs.Wasm.Behaviour.Semantics.V3

/-!
# The behaviours of Core 3.0

Observable outcomes of the Core 3.0 reduction relation, indexed by a numerics
profile `P`. A finite run ends at `c'.code = r.toAdmin`; an infinite reduction
trace observes divergence. `terminal_of_mem` relates the finite case to
`Config.Terminal`.

Unlike 1.0 and 2.0, 3.0 supports escaping exceptions, represented by
`Behaviour.throws`. `Result.exists_toBehaviour` covers every terminating
behaviour constructor; it does not assert that arbitrary behaviour sets are
realizable by a module.

The versioned import is `Semantics.V3`; the declarations retain the existing
`Silmaril.Wasm.Execution.Core` namespace. `Semantics.Core` re-exports this file
for compatibility. See `docs/projects/wasm-semantics.md` for the version map.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- Divergence is observed exactly when the configuration has an infinite
trace. -/
@[simp] theorem diverges_mem_behavioursOf_iff {P : Profile} {host : HostSemantics H}
    {c : Config H} :
    (Behaviour.diverges : Behaviour Val) ∈ behavioursOf P host c ↔ Diverges P host c :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V3.diverges_mem_behavioursOf_iff

/-! ## Elimination -/

/-- Every terminating observed behaviour comes from a finite run to a terminal
configuration. -/
theorem exists_result_of_mem {P : Profile} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Val} (mem : b ∈ behavioursOf P host c) (ne : b ≠ .diverges) :
    ∃ (c' : Config H) (r : Result),
      Steps P host c c' ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V3.exists_result_of_mem mem ne

/-- The `Behaviour.Terminates` phrasing of `exists_result_of_mem`. -/
theorem terminates_of_mem {P : Profile} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Val} (mem : b ∈ behavioursOf P host c) (term : b.Terminates) :
    ∃ (c' : Config H) (r : Result),
      Steps P host c c' ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour :=
  exists_result_of_mem mem (by rintro rfl; exact absurd term (by simp))

/-- The `Config.Terminal` phrasing: a terminating behaviour is reached at a
terminal configuration. -/
theorem terminal_of_mem {P : Profile} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Val} (mem : b ∈ behavioursOf P host c) (term : b.Terminates) :
    ∃ c' : Config H, Steps P host c c' ∧ c'.Terminal := by
  obtain ⟨c', r, steps, final, _⟩ := terminates_of_mem mem term
  exact ⟨c', steps, r, final⟩

/-! ## Monotonicity along a run -/

/-- Divergence is preserved backwards along a finite run. -/
theorem diverges_of_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps P host c c') (div : Diverges P host c') : Diverges P host c :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V3.diverges_of_steps steps div

/-- Behaviours accumulate backwards along a run. -/
theorem behavioursOf_mono_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps P host c c') : behavioursOf P host c' ⊆ behavioursOf P host c :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V3.behavioursOf_mono_steps steps

end Silmaril.Wasm.Execution.Core
