module

public import Silmaril.X86.RelIsa.Defs

/-!
# Loosening a deterministic machine into a relational one

`loosen I P` is the relational machine that, where `P` holds and `I` takes a step, takes
exactly that step, and everywhere else (`I` fails, or `P` fails) allows every outcome, `stop`
included, subject only to the machine invariant: a successor of a loose step is `live`.

It is the demonic counterpart of a run predicate: a `Must` proof on `loosen I P` constrains
only the states where `P` holds, and every machine `C` with `Le C (loosen I P)` inherits it
(`Must.of_le`). The theorems are in `Loosen/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.RelIsa

open Silmaril.X86.SegVC (Isa)

variable {σ : Type}

/-- **Loosening**: where `P` holds and `I` takes a step, exactly that step. Everywhere else
(`I` fails, or `P` fails) every outcome is allowed, `stop` included, subject only to the
machine invariant: a successor of a loose step is `live`. (`live` is part of the views, so
every `C` with `Le C (loosen I P)` keeps it anyway; for `Open.isa`, `Open9.isa` and
`Str9.isa` it is `True`.) -/
def loosen (I : Isa σ) (P : σ → Prop) : RelIsa σ where
  toViews := Views.ofIsa I
  step s r := (∀ t, P s → I.step s = some t → r = .ok t) ∧ ∀ t, r = .ok t → I.live t
  live_step {_ t} _ h := h.2 t rfl

end Silmaril.X86.RelIsa
