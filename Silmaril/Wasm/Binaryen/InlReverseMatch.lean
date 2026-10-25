module

public import Silmaril.Wasm.Binaryen.InlReverseContexts
public import Silmaril.Wasm.Binaryen.InlProfileInit
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext

@[expose] public section

/-! # Reverse inlining matches with explicit initialization prefixes

Inlining checkpoints need not be closed under one selected target step: entry
into an inline block precedes its parameter stores and local initialization.
`ReverseMatch` retains that finite write chain instead of requiring an artificial
checkpoint at every intermediate write. The chain is stable under runtime
contexts. The resulting checkpoint simulation reuses `ForwardSim` for finite
runs and divergence; its only stutters are actual pending writes, whose code
rank strictly decreases.

The driver requires a chosen reverse step law. Supplying that law for the full
inlining relation remains a separate obligation; this module does not assert
that the complete inliner already supports arbitrary-profile equivalence.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

/-- A nonempty actual original run matches a selected target step, after only
the target's uniquely forced pending local writes have been completed. -/
def ReverseMatch (p : Prm) (P : Profile) (mode : Mode)
    (original next : Config H) : Prop :=
  ∃ originalNext normalized : Config H,
    Relation.TransGen (Step P Det.noHost) original originalNext ∧
    Initialization next normalized ∧ MR p mode originalNext normalized ∧
    SR p originalNext.store normalized.store

/-- Dead target suffixes can take an administrative reduction after the
original has already discarded its corresponding suffix. Such a step may
stutter only when the actual target code rank strictly decreases. -/
def ReverseProgress (p : Prm) (P : Profile) (mode : Mode)
    (original target next : Config H) : Prop :=
  ReverseMatch p P mode original next ∨
    ∃ normalized : Config H, Initialization next normalized ∧
      MR p mode original normalized ∧ SR p original.store normalized.store ∧
      aszs next.code < aszs target.code

namespace ReverseMatch

theorem of_steps {mode : Mode} {original originalNext next : Config H}
    (steps : Relation.TransGen (Step P Det.noHost) original originalNext)
    (runtime : MR p mode originalNext next) (stores : SR p originalNext.store next.store) :
    ReverseMatch p P mode original next :=
  ⟨originalNext, next, steps, .done _, runtime, stores⟩

/-- Lift a generic match through related suffixes and the same value prefix. -/
theorem context {original next : Config H} (matched : ReverseMatch p P .gen original next)
    (vs : List Val) {oldRest newRest : List Admin} (rest : LN p oldRest newRest) :
    ReverseMatch p P .gen
      ⟨original.store, original.frame, vals vs ++ original.code ++ oldRest⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ newRest⟩ := by
  obtain ⟨oldNext, normalized, steps, initializes, ⟨frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, vals vs ++ oldNext.code ++ oldRest⟩,
    ⟨normalized.store, normalized.frame, vals vs ++ normalized.code ++ newRest⟩,
    tg_instrs steps vs oldRest, initializes.context vs newRest,
    ⟨frames, LN.append (LN.append (LN.of_vals vs) code) rest⟩, stores⟩

theorem label {original next : Config H} (matched : ReverseMatch p P .gen original next)
    (n : Nat) (cont : List Instr) :
    ReverseMatch p P .gen
      ⟨original.store, original.frame, [.label n cont original.code]⟩
      ⟨next.store, next.frame, [.label n cont next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, initializes, ⟨frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, [.label n cont oldNext.code]⟩,
    ⟨normalized.store, normalized.frame, [.label n cont normalized.code]⟩,
    tg_label steps n cont, initializes.label n cont,
    ⟨frames, .cons (.label code) .nil⟩, stores⟩

theorem handler {original next : Config H} (matched : ReverseMatch p P .gen original next)
    (n : Nat) (catches : List Catch) :
    ReverseMatch p P .gen
      ⟨original.store, original.frame, [.handler n catches original.code]⟩
      ⟨next.store, next.frame, [.handler n catches next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, initializes, ⟨frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, [.handler n catches oldNext.code]⟩,
    ⟨normalized.store, normalized.frame, [.handler n catches normalized.code]⟩,
    tg_handler steps n catches, initializes.handler n catches,
    ⟨frames, .cons (.handler code) .nil⟩, stores⟩

/-- Nested activations can change their own locals; the outer frame is retained. -/
theorem frame_gen {original next : Config H} (matched : ReverseMatch p P .gen original next)
    (n : Nat) (outer : Frame) :
    ReverseMatch p P .gen
      ⟨original.store, outer, [.frame n original.frame original.code]⟩
      ⟨next.store, outer, [.frame n next.frame next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, initializes, ⟨frames, code⟩, stores⟩ := matched
  refine ⟨⟨oldNext.store, outer, [.frame n oldNext.frame oldNext.code]⟩,
    ⟨normalized.store, outer, [.frame n normalized.frame normalized.code]⟩,
    tg_frame steps n outer, initializes.frame n outer, ⟨rfl, ?_⟩, stores⟩
  rw [frames]
  exact .cons (.frame (.gen code)) .nil

/-- A recursive call to the changed caller retains its added-local slice. -/
theorem frame_caller {original next : Config H} (matched : ReverseMatch p P .g original next)
    (n : Nat) (outer : Frame) :
    ReverseMatch p P .gen
      ⟨original.store, outer, [.frame n original.frame original.code]⟩
      ⟨next.store, outer, [.frame n next.frame next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, initializes,
    ⟨moduleEq, locals, E, extra, frames, code⟩, stores⟩ := matched
  refine ⟨⟨oldNext.store, outer, [.frame n oldNext.frame oldNext.code]⟩,
    ⟨normalized.store, outer, [.frame n normalized.frame normalized.code]⟩,
    tg_frame steps n outer, initializes.frame n outer, ⟨rfl, ?_⟩, stores⟩
  rw [frames]
  exact .cons (.frame (.g moduleEq locals extra code)) .nil

end ReverseMatch

/-- A selected target may still have pending writes before the checkpoint.
Original typing is retained in its actual surrounding runtime context. -/
def ReverseCheckpoint (p : Prm) (target original : Config H) : Prop :=
  ∃ normalized : Config H, Initialization target normalized ∧
    MR p .gen original normalized ∧ SR p original.store normalized.store ∧ ContextTyped original

theorem ReverseCheckpoint.of_related {original target : Config H}
    (runtime : MR p .gen original target) (stores : SR p original.store target.store)
    (typed : ContextTyped original) : ReverseCheckpoint p target original :=
  ⟨target, .done _, runtime, stores, typed⟩

/-- At a terminal target there cannot be any pending write. The original has
the same result and its store relates to the target's actual final store. -/
theorem ReverseCheckpoint.terminal {original target : Config H} {r : Result}
    (checkpoint : ReverseCheckpoint p target original) (finished : target.code = r.toAdmin) :
    original.code = r.toAdmin ∧ SR p original.store target.store := by
  obtain ⟨normalized, initializes, runtime, stores, _⟩ := checkpoint
  cases initializes with
  | done =>
    refine ⟨?_, stores⟩
    have code := runtime.2
    rw [finished] at code
    cases r with
    | values vs => exact LN.vals_inv_right code
    | trap => exact LN.trap_inv_right code
    | throw a => exact LN.throwing_inv_right code
  | step write _ =>
    exact (SingleThreaded.Exec.BehaviourRefinement.not_step_of_terminal ⟨r, finished⟩
      (write.step (P := Profile.spec false {}) (host := Det.noHost))).elim

/-- The remaining local obligation: replay the selected checkpoint step, with
its actual outcome and context-stable normalization prefix. -/
def ChosenReverseStep (p : Prm) (P : Profile) (H : Type) : Prop :=
  ∀ {original target next : Config H}, ContextTyped original →
    MR p .gen original target → SR p original.store target.store →
    Step P Det.noHost target next → ReverseProgress p P .gen original target next

/-- Pending writes supply exactly the decreasing stutters needed by the shared
simulation kit. All other selected target steps make actual source progress. -/
def reverseCheckpointSim (replay : ChosenReverseStep p P H) :
    ConfigSim P Det.noHost (ReverseCheckpoint (H := H) p) where
  toForwardSim := {
    measure := fun target => aszs target.code
    step := by
      intro target next original selected checkpoint
      obtain ⟨normalized, initializes, runtime, stores, typed⟩ := checkpoint
      cases initializes with
      | done =>
        rcases replay typed runtime stores selected with matched | stutter
        · obtain ⟨oldNext, newNormalized, steps, init, newRuntime, newStores⟩ := matched
          exact ⟨oldNext, .inl steps, newNormalized, init, newRuntime, newStores,
            typed.steps steps.to_reflTransGen⟩
        · obtain ⟨newNormalized, init, newRuntime, newStores, rank⟩ := stutter
          exact ⟨original, .inr ⟨rfl, rank⟩,
            newNormalized, init, newRuntime, newStores, typed⟩
      | step write tail =>
        obtain rfl := write.unique next selected
        exact ⟨original, .inr ⟨rfl, write.rank⟩, normalized, tail, runtime, stores, typed⟩ }
  terminal := by
    intro target original r checkpoint finished
    exact ⟨original, .refl, (checkpoint.terminal finished).1⟩

/-- A chosen terminating target run is reproduced in the original with the
same result and the actual final mutable-store relation. -/
theorem reverse_checkpoint_run (replay : ChosenReverseStep p P H)
    {original target final : Config H} {r : Result}
    (checkpoint : ReverseCheckpoint p target original)
    (run : Steps P Det.noHost target final) (finished : final.code = r.toAdmin) :
    ∃ originalFinal : Config H, Steps P Det.noHost original originalFinal ∧
      originalFinal.code = r.toAdmin ∧ SR p originalFinal.store final.store := by
  obtain ⟨originalFinal, steps, related⟩ :=
    (reverseCheckpointSim replay).toForwardSim.steps run checkpoint
  exact ⟨originalFinal, steps, related.terminal finished⟩

/-- Nondeterministic divergence is transported without choosing a normal form
or appealing to termination excluding a different diverging execution. -/
theorem reverse_checkpoint_diverges (replay : ChosenReverseStep p P H)
    {original target : Config H} (checkpoint : ReverseCheckpoint p target original)
    (diverges : Diverges P Det.noHost target) : Diverges P Det.noHost original :=
  (reverseCheckpointSim replay).toForwardSim.diverges diverges checkpoint

end Silmaril.Wasm.Binaryen.InlR
