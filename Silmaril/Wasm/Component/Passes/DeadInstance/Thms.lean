module

public import Silmaril.Wasm.Component.Passes.DeadInstance.Defs
public import Silmaril.Wasm.Component.Contract.Defs
public import Silmaril.Wasm.Component.Laws.Defs
import Silmaril.Proofs.Wasm.Component.Laws.Dead

/-!
# Dead instance elimination: soundness

* `denU_removeNode`, `denU_deadInstances`: removing dead core instances
  preserves the denotation of a flat component, for every core semantics,
  *assuming* `PairLaws` (only `hdist`, `psum` and `pproj` are used), which
  holds (`pairLaws`); unconditional: `denU_removeNode'`. Proofs:
  `Silmaril.Proofs.Wasm.Component.Laws.Dead`.
* `deadInstancePass L C : Pass (linkedIR C).contract`;
  `deadInstancePass' C := deadInstancePass pairLaws C`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Compile.PassAPI

variable {M : Type} [CoreModule M]

/-- Removing a dead instance preserves the denotation (assuming `PairLaws`). -/
theorem denU_removeNode (L : PairLaws) (C : CoreSem M) {l l' : Linked M} {k : Nat}
    (h : removeNode l k = some l') : l'.denU C = l.denU C :=
  Silmaril.Proofs.Wasm.Component.Laws.denU_removeNode L C h

theorem removeNode_sizes {l l' : Linked M} {k : Nat} (h : removeNode l k = some l') :
    l'.imports = l.imports ∧ l'.exports.length = l.exports.length := by
  obtain ⟨I, ns, xs⟩ := l
  simp only [removeNode] at h
  split at h
  · simp at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp
    · simp at h

/-- One step of `deadInstances`. -/
def removeNodeStep (l : Linked M) (k : Nat) : Linked M := (removeNode l k).getD l

theorem removeNodeStep_sound (L : PairLaws) (C : CoreSem M) (l : Linked M) (k : Nat) :
    (linkedIR C).Inv (removeNodeStep l k) ∧ (linkedIR C).contract.Rel l (removeNodeStep l k) := by
  refine ⟨trivial, ?_⟩
  unfold removeNodeStep
  cases h : removeNode l k with
  | none => exact DenT.rel_refl _
  | some l' =>
    obtain ⟨h₁, h₂⟩ := removeNode_sizes h
    exact ⟨congrArg List.length h₁, h₂, (denU_removeNode L C h).le⟩

/-- The dead instance elimination pass (assuming `PairLaws`). -/
def deadInstancePass (L : PairLaws) (C : CoreSem M) : Pass (linkedIR C).contract :=
  Pass.foldSteps (fun l => (List.range l.nodes.length).reverse) removeNodeStep
    (fun l k _ => removeNodeStep_sound L C l k)

theorem deadInstancePass_run (L : PairLaws) (C : CoreSem M) (l : Linked M) :
    (deadInstancePass L C).run l = deadInstances l := rfl

/-- Removing a dead instance preserves the denotation (unconditional). -/
theorem denU_removeNode' (C : CoreSem M) {l l' : Linked M} {k : Nat}
    (h : removeNode l k = some l') : l'.denU C = l.denU C :=
  denU_removeNode pairLaws C h

/-- The dead instance elimination pass (unconditional). -/
def deadInstancePass' (C : CoreSem M) : Pass (linkedIR C).contract := deadInstancePass pairLaws C

theorem deadInstancePass'_run (C : CoreSem M) (l : Linked M) :
    (deadInstancePass' C).run l = deadInstances l := rfl

end Silmaril.Wasm.Component
