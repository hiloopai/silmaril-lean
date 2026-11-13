module

public import Silmaril.Wasm.Tools.Gen.Cmd.Mutate.Defs
public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Execution.Core.Soundness.Defs

/-!
# Observational equivalence of `--preserve-semantics`

The notion of "same semantics" that `wasm-tools mutate --preserve-semantics` is proved to keep
(`Thms.mutate_preserve_equiv`): **export equivalence** (silmaril's `ExportEquiv` with equal
behaviours, `Silmaril.Wasm.Binaryen.Equiv`): on every valid store and every list of imports,
the two modules instantiate together, and every session of calls to their exports (the
instantiation run, then any script of invocations by export name) has the same behaviours,
traps and divergence included. It is required at every deterministic numerical profile (any
oracle deciding `memory.grow`/`table.grow` failures) and under every host that respects code
(`HostRespectsCode`) and is sound (`HostOk`), silmaril's closed host among them.

Names, not indices, are observed, so this is the equivalence of wasm-mutate's
"semantics-preserving" mutations as a client of the module sees them.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Equiv

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- **Observational equivalence** of Core 3.0 modules: export equivalence with equal behaviours
at every deterministic profile, under every code-respecting, sound host. -/
def ObsEquiv (m m' : Module) : Prop :=
  ∀ (oracle : GrowKind → Nat → Nat → Nat → Bool) (H : Type) (host : HostSemantics H),
    HostRespectsCode host → HostOk host →
      ExportEquiv (· = ·) (Profile.deterministic oracle) host m m'

end Silmaril.Wasm.Tools.Gen.Cmd.Equiv
