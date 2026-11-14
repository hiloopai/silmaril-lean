module

public import Silmaril.Games.Abstract.SigBridge.Defs
public import Silmaril.Wasm.Game.Strategy.Defs

/-!
# Scalar Wasm instances as abstract machines

A scalar Core 3.0 instance `I` (`Silmaril.Wasm.Game`) at store `s` and
numerics profile `P` is an abstract state machine over the game `I.E ↠ I.F`.
Its states are the hidden states of `I.lts P s`: idle with a store, running an
export call, or waiting on an import call. Its steps are the transitions of
that system. There are no silent steps, because host-free runs are folded into
the visible moves.

`Silmaril.Wasm.Abstract.Instance.Thms` shows that state erasure of this
machine is the existing strategy `I.strategy P s` (read as a trace model). It
also transports `Silmaril.Wasm.Det.Game.DetMod` (determinism modulo traps) to
the generic `TraceModel.DetUpTo`.

**What determinism means here.** Imports are Opponent moves: two plays are
compared only after the same import answers. A deterministic module
(`Silmaril.Wasm.Det.Core.DetModule`) gives a deterministic trace model *modulo
traps*: after a trap-free play, the next Proponent move is unique unless one
candidate is a trap. Traps are exempt because the existing determinism
results are stated modulo traps (`Silmaril.Wasm.Det.Game`), so that a run
that traps on one branch, for example when `memory.grow` fails or resources
run out, need not match a branch that succeeds. Profiles with
nondeterministic NaN payloads or relaxed-SIMD choices give machines that
need not be deterministic at all.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)

/-- A scalar instance at store `s` as an abstract machine. -/
def machine (I : ScalarInstance) (P : Profile) (s : Silmaril.Wasm.Execution.Core.Store Nat) :
    Machine (sigGame I.E I.F) :=
  Machine.ofLTS (I.lts P s)

end Silmaril.Wasm.Abstract
