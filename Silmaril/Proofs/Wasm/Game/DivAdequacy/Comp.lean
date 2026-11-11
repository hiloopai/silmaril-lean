module

public import Silmaril.Proofs.Wasm.Game.DivAdequacy.Traces
public import Silmaril.Games.DivLTSComp.Thms

/-!
# The divergence-observing closed program is a composite of strategies

The environment's and the instance's transition systems with silent steps take
silent steps only in running positions (`Env.silentRunning_dlts`,
`ScalarInstance.silentRunning_dlts`: the environment loops only on a pending
question, the instance steps only while its thread has control). With
`DStrategy.ofLTS_comp` this makes the closed program `I.closedD P s K` the
composite `K.dstrategy.comp (I.dstrategy P s)` of the two divergence-observing
strategies (`closedD_eq_comp`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace Env

variable {E : Sig.{0}}

/-- The game position of a state of the environment's system. -/
def dpos : Option E.Op → Pos Sig.empty E
  | none => .idle
  | some e => .run e

/-- The environment's system with silent loops takes silent steps only when running. -/
theorem silentRunning_dlts (K : Silmaril.Wasm.Game.Env E) : K.dlts.SilentRunning := by
  refine LTS.silentRunning_of_pos (L := K.dlts) dpos rfl ?_ ?_ ?_
  · intro x y o h
    cases h with
    | ask e => exact .ask e
    | ans hw => exact .ret _ _
  · intro x y h
    cases h
    rfl
  · intro x y h
    cases h with
    | loop _ => exact ⟨_, rfl⟩

end Env

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance}

open Silmaril.Wasm.Game.ScalarInstance

/-- The instance's system with silent host-free steps takes silent steps only when running. -/
theorem silentRunning_dlts (P : Profile) (s : Store Nat) : (I.dlts P s).SilentRunning := by
  refine LTS.silentRunning_of_pos (L := I.dlts P s) HState.pos rfl ?_ ?_ ?_
  · intro x y o h
    cases h with
    | call s f => exact .ask f
    | ucall => exact .call _ _
    | uret v => exact .reply _ _ v
    | oret => exact .ret _ _
  · intro x y h
    cases h
    rfl
  · intro x y h
    cases h
    exact ⟨_, rfl⟩

/-- **The closed program is the composite of the divergence-observing strategies.** -/
theorem closedD_eq_comp (P : Profile) (s : Store Nat) (K : Silmaril.Wasm.Game.Env I.E) :
    I.closedD P s K = K.dstrategy.comp (I.dstrategy P s) :=
  DStrategy.ofLTS_comp (Env.denotes_dlts K) (denotes_dlts P s)
    (LTS.SilentRunning.divRunning (Env.silentRunning_dlts K))
    (LTS.SilentRunning.divRunning (silentRunning_dlts P s))

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
