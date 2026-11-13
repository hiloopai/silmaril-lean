module

public import Silmaril.Wasm.FX.Asyncify.Defs

/-!
# Asyncify with a host: blocking calls as unhandled suspensions

The tool `wasm-asyncify` (`Silmaril.Wasm.FX.Asyncify.Tool`) works on programs whose import calls
**block**: the host answers them, and the asyncified program returns to the host with its frames
saved, then the host calls the export again, which rewinds. The family `scheme` of
`Silmaril.Wasm.FX.Asyncify` has no host: its source is the handler kernel `FXAsync.sstep`, where a
`suspend` without an enclosing handler traps. This module closes both machines of the family's
`unwind` strategy with a host, in the way the tool does:

* **Source** (`hsstep`): a `suspend t n` that no frame below handles (`blockedOn`) is a
  *blocking call* of import `t` with the `n` operands as arguments; the host answers it in one
  step, its answers are pushed on the suspending frame and the frame continues. Every other step
  is the kernel's.
* **Target** (`htstep`): the compiled program unwinds as for a handled `suspend`, but no frame
  handles `t`: unwinding passes every frame, down to the empty stack (`atRoot`). There (where the
  kernel's asyncify machine traps) the host reads the request (tag `t`, payload), answers, and
  the saved frames are rewound with the answers as arguments. This is the tool's host protocol:
  the export returns unwound (`state = 1`), the host reads the import index and arguments, writes
  the results, sets `state = 2` and re-enters the export, which rewinds.

`hostScheme V σ o` is the instance: the same compiler `compPO o` as `scheme V .unwind o`, the
host-closed machines, and the same fragment (`Opt.Dom`: a sound suspension analysis). A host is
deterministic (`KHost`); host states are not observed (an observation is a result, a trap or
divergence), so a host that records its calls is visible only through the results it returns.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Host

open Silmaril.Wasm.Models.FXAsync

variable {V σ : Type}

/-- A deterministic host with state `σ`: answers to an import (tag) and its arguments. -/
structure KHost (V σ : Type) where
  answer : σ → Nat → List (SV V) → σ × List (SV V)

/-- **The blocking call at the top of a stack**, if any: the top frame runs `suspend t n` on at
least `n` operands and no frame below handles `t`. Returns the tag, the payload and the top frame
after the instruction (payload removed). -/
def blockedOn : List (SFrame V) → Option (Nat × List (SV V) × SFrame V)
  | ⟨.suspend t n :: c, ops, w⟩ :: rest =>
    match popN n ops, split t rest with
    | some (p, o), none => some (t, p, ⟨c, o, w⟩)
    | _, _ => none
  | _ => none

/-- **The source closed by a host**: blocking calls are answered, all else is the kernel. -/
def hsstep (P : Prog (Ins V)) (test : V → Bool) (H : KHost V σ) (x : SCfg V × σ) :
    Res (SCfg V × σ) V :=
  match blockedOn x.1.stack with
  | some (t, p, fr) =>
    let r := H.answer x.2 t p
    .next (⟨x.1.conts, { fr with ops := r.2 ++ fr.ops } :: x.1.stack.tail⟩, r.1)
  | none => (sstep P test x.1).map (·, x.2)

/-- The target has unwound every frame: the request (tag, payload) and the saved frames. -/
def atRoot : TCfg V → Option (Nat × List (SV V) × List (TFrame V))
  | ⟨_, .unwind t p buf, []⟩ => some (t, p, buf)
  | _ => none

/-- **The target closed by the host protocol**: at the root the host answers and the saved
frames are rewound with the answers; all else is the asyncify machine. -/
def htstep (Q : Prog (TIns V)) (test : V → Bool) (H : KHost V σ) (y : TCfg V × σ) :
    Res (TCfg V × σ) V :=
  match atRoot y.1 with
  | some (t, p, buf) =>
    let r := H.answer y.2 t p
    .next (⟨y.1.heap, .rewind buf.reverse r.2, []⟩, r.1)
  | none => (tstep Q test y.1).map (·, y.2)

/-- The source behaviours of a call of `f` with `args` from host state `s`. -/
def hSrcRun (P : Prog (Ins V)) (test : V → Bool) (H : KHost V σ) (s : σ) (f : Nat)
    (args : List (SV V)) : Set (Obs V) :=
  beh (hsstep P test H) (sInit f args, s)

/-- An asyncify instance closed by a host: target, compiler, target behaviours, fragment. -/
structure HScheme (V σ : Type) where
  TP : Type
  compile : Prog (Ins V) → TP
  run : TP → (V → Bool) → KHost V σ → σ → Nat → List (SV V) → Set (Obs V)
  dom : Prog (Ins V) → Prop

/-- Correctness: on the fragment, every call under every host has the same behaviours. -/
def HScheme.Correct (A : HScheme V σ) : Prop :=
  ∀ P, A.dom P → ∀ test H s f args, A.run (A.compile P) test H s f args = hSrcRun P test H s f args

/-- **The host instance of the `unwind` strategy**, for an optimization `o`. -/
def hostScheme (V σ : Type) (o : Opt) : HScheme V σ where
  TP := Prog (TIns V)
  compile := compPO o
  run := fun Q test H s f args => beh (htstep Q test H) (tInit f args, s)
  dom := o.Dom

end Silmaril.Wasm.FX.Asyncify.Host
