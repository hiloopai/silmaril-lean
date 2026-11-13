module

public import Silmaril.Wasm.FX.Asyncify.Host.Defs

/-!
# Asyncify with a host: behaviours that observe the host state

`Silmaril.Wasm.FX.Asyncify.Host` compares the host-closed kernel `hsstep` and the host-closed
asyncify machine `htstep` by `FXAsync.beh`, whose observations are results, traps and divergence:
the host state is not observed, so a host that records its calls is visible only through the
answers it gives. The tool `wasm-asyncify` observes the final host state (`Tool.Obs σ`).

This module adds that observation to the kernel side. `observe step` is the closed machine
`step` whose stop at `(c, s)` reports the outcome **with the host state `s`** (`HOut`). It is a
machine over the value type `HOut V σ`: a stop is `done [val h]`, so `FXAsync.beh` and the
simulation theorems of the family apply unchanged. A step that stops never changes the host
state (stops of `hsstep` and `htstep` come from the kernel and the asyncify machine), so `s` is
the final host state.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Host

open Silmaril.Wasm.Models.FXAsync

variable {V σ : Type}

/-- An outcome with the final host state. -/
inductive HOut (V σ : Type) where
  | done (vs : List (SV V)) (s : σ)
  | trap (s : σ)

/-- An outcome at host state `s`. -/
def HOut.ofOutcome (s : σ) : Outcome V → HOut V σ
  | .done vs => .done vs s
  | .trap => .trap s

/-- **A host-closed machine observing the host state**: a stop `o` at `(c, s)` becomes the
result `[val (o, s)]`. -/
def observe {C : Type} (step : C × σ → Res (C × σ) V) (x : C × σ) : Res (C × σ) (HOut V σ) :=
  match step x with
  | .next y => .next y
  | .stop o => .stop (.done [.val (HOut.ofOutcome x.2 o)])

/-- The source behaviours of a call, host state observed. -/
def hSrcObs (P : Prog (Ins V)) (test : V → Bool) (H : KHost V σ) (s : σ) (f : Nat)
    (args : List (SV V)) : Set (Obs (HOut V σ)) :=
  beh (observe (hsstep P test H)) (sInit f args, s)

/-- The target behaviours of a call under the host protocol, host state observed. -/
def hTgtObs (Q : Prog (TIns V)) (test : V → Bool) (H : KHost V σ) (s : σ) (f : Nat)
    (args : List (SV V)) : Set (Obs (HOut V σ)) :=
  beh (observe (htstep Q test H)) (tInit f args, s)

end Silmaril.Wasm.FX.Asyncify.Host
