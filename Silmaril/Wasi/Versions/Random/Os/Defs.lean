module

public import Silmaril.Wasi.Versions.Random.Over.Defs

@[expose] public section

/-!
# `wasi:random` 0.3 over 0.2: the OS image (definitions)

The control states that `p3OverP2R` reaches (`RShape`): idle, starting an export call, waiting
for the 0.2 answer, returning it. `pendR ch c` is the OS image of the answer held in the control
state `c` and not yet returned: nonempty only when a secure byte answer is about to be returned.
`Silmaril.Wasi.Versions.Random.Os.Thms` proves that the image of the 0.2 answers is the image of
the 0.3 returns followed by `pendR`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Random

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-- The control states of `p3OverP2R`. -/
inductive RShape : SCSt Unit rand2Fns rand3Fns → Prop
  /-- No export call runs. -/
  | idle : RShape (.idle ())
  /-- An export call starts. -/
  | start (q : (nsig rand3Fns).Op) : RShape (.run q (p3OverP2R () q))
  /-- The 0.2 call is pending. -/
  | wait (q : (nsig rand3Fns).Op) : RShape (.wait q (op2 q) fun n => .pure ((), n))
  /-- The answer `n` is about to be returned. -/
  | done (q : (nsig rand3Fns).Op) (n : Option (List Val)) : RShape (.run q (.pure ((), n)))

/-- The OS image of the answer held in a control state. -/
def pendR (ch : Silmaril.Process.LPS.Word) : SCSt Unit rand2Fns rand3Fns →
    List Silmaril.Process.LPS.Event
  | .run q (.pure (_, n)) => osEvR ch (.imp q.1.1 q.2 n)
  | _ => []

end Silmaril.Wasi.Versions.Random
