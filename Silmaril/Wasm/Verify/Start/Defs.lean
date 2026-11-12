module

public import Silmaril.Wasm.Verify.Reach.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs

@[expose] public section

/-!
# Reachability with an instantiation phase

The invariant of `Silmaril.Wasm.Verify.Reach` lifted to the instantiable system
`I.instSysT P s t₀` of `Silmaril.Wasm.Game.Start` (an instantiation thread `t₀` run from the store
`s`, then export calls against the persisted store). For the specification's instantiation
(`Silmaril.Wasm.Game.SpecInst`), `s = c₀.store` and `t₀ = configThread c₀`, with `c₀` the
configuration of `$instantiate`: segment initialisation followed by `call start`.

* `StartIn I s t₀ G fs i`: what the checker establishes: the functions of `G` are closed
  (`FuncsClosed`), the invariant `CfgIn` holds of the instantiation configuration
  `t₀.config s` (so the store's references, the start function and the segment-initialisation
  code are in `G`), every export is in `G`, and `G` avoids import `i`.
* `ThInv G fs base x`: a thread `x = (store, thread)` satisfies `CfgIn` and its store has the
  function instances `base` (steps never change them).
* `SInv`: the invariant of the states of `(I.instSysT P s t₀).toLTS`: threads (instantiating or
  running an export call) satisfy `ThInv`, waiting continuations satisfy it for every answer,
  ready stores hold only references in `G`.

The results (`Silmaril.Wasm.Verify.Start.Thms`): no play of `I.instStrategyT P s t₀`, in particular
of the strategy `I.specStrategy P c₀` with the specification's instantiation, asks import `i`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- What the checker establishes about an instance whose instantiation runs `t₀` from `s`. -/
structure StartIn (I : ScalarInstance) (s : Store Nat) (t₀ : Thread) (G : Nat → Prop)
    (fs : List Nat) (i : Nat) : Prop where
  closed : FuncsClosed G fs (InstrIn G fs) s.funcs
  cfg : CfgIn G fs (InstrIn G fs) (t₀.config s)
  exports : ∀ j, G (I.addr j)
  avoids : Avoids G s.funcs i

/-- A thread satisfies the reachability invariant and keeps the function instances `base`. -/
def ThInv (G : Nat → Prop) (fs : List Nat) (base : List (FuncInst Nat)) (x : Store Nat × Thread) :
    Prop :=
  CfgIn G fs (InstrIn G fs) (x.2.config x.1) ∧ x.1.funcs = base

/-- The invariant of the states of the instantiable system. -/
def SInv (I : ScalarInstance) (P : Profile) (s : Store Nat) (t₀ : Thread) (G : Nat → Prop)
    (fs : List Nat) : (I.instSysT P s t₀).St → Prop
  | .fresh => True
  | .inst c => ThInv G fs s.funcs c
  | .iwait _ k => ∀ n, ThInv G fs s.funcs (k n)
  | .ready st => StoreIn G st ∧ st.funcs = s.funcs
  | .run _ c => ThInv G fs s.funcs c
  | .wait _ _ k => ∀ n, ThInv G fs s.funcs (k n)
  | .dead => True
  | .pstart => True
  | .pwait => True
  | .pfail _ => True

end Silmaril.Wasm.Verify
