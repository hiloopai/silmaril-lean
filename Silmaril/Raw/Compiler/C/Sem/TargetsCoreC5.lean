module

public import Silmaril.Compiler.C.Sem.Validator.Defs
@[expose] public section

/-!
# Checked realisation of C5 through Cerberus Core

The universal clause has the shape of `Targets.c4_core_realises`, using
`elabC5` and C5 (the heap: `malloc`, `calloc`, `realloc`, `free`). The existence
clause explicitly excludes the always-declining stub. Scoring should additionally
require an accepted corpus program, counting each program once across the Core
elaborators.

As with C0 through C4, `elabC5` is worker-written: this theorem shows that C5
is faithfully realisable in Core, not that C5 matches Cerberus's own
elaboration. A bridge to Cerberus-generated Core is a separate obligation.

Acceptance is partial: an undefined source execution (a use after `free`, a
double `free`, an access past a block), unsupported syntax, exhausted checking
fuel, or differing Core behaviours must decline. Frozen Core enables the `alloc`
action (an untyped, aligned dynamic region that typed loads and stores may
access within its bounds), static `kill` of an allocation base, and in-bounds
pointer shifts. It does not enable the dynamic `kill` that Cerberus elaborates
`free` to, so `free` needs an explicit encoding (for instance a static kill of
the block base, which cannot kill a zero-sized block) or a separately approved
change to Core. Core has no allocation-size query, `memcpy` or zero-filled
region: `calloc` and `realloc` need an explicit encoding of the zeroing, the old
block size and the copy (preserving C5's initialisation of copied bytes), or must
decline. Core reports exhaustion as unsupported rather than returning `NULL`.
Core's pointer equality across distinct allocations is not decided, and C5's
block addresses are not Core's: programs observing addresses must decline unless
the translator preserves the observation. C4's function-pointer, variadic and
floating restrictions, and the current structural elaborator's unsupported
syntax, also remain relevant.

The acceptance witness need not itself call an allocation function; broader
coverage remains an implementation and corpus-measurement goal. No implementation
or proof of this target is supplied by this statement.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem

/-- At least one program elaborates, and every accepted program is in C5 with
exactly the behaviours of its structurally elaborated Core program. -/
def c5_core_realises : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program), elabC5 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC5 p = some q → C5.InFragment p ∧ Core.beh q = C5.beh p)

end Silmaril.Compile.Targets
