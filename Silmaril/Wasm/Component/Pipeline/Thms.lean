module

public import Silmaril.Wasm.Component.Pipeline.Defs
public import Silmaril.Wasm.Component.Passes.Fusion.Thms
public import Silmaril.Wasm.Component.Passes.Flatten.Thms
public import Silmaril.Wasm.Component.Passes.DeadInstance.Thms
public import Silmaril.Wasm.Component.Passes.DeadExport.Thms

/-!
# The component pipeline and its soundness

Passes are elements of the monoid `Pass C` of `Silmaril.Compile.PassAPI`
(product = sequencing); translations between IRs compose in the category of
IRs over `compDomain`.

Unconditional (proved for every core semantics):

* `fusionPipeline C : Pass (contract C)` — adapter fusion on the nested IR;
* `linkedFusionPipeline C : Pass (linkedIR C).contract`;
* `programFusionPipeline C : Pass (programIR C).contract` — dead export
  elimination, then adapter fusion;
* `programFusionPipeline_sound`.

Stated for an explicit `L : PairLaws` (the five laws of pairing), and
unconditionally (primed names, applying them to `pairLaws`):

* `linkedPipeline L C = fuseLinkedPass C * deadInstancePass L C`;
* `componentPipeline L C : Pass (contract C)` — flatten, `linkedPipeline`,
  embed back; its run function is `optimizeComponent`
  (`componentPipeline_run`);
* `programPipeline L C : Pass (programIR C).contract` — dead export
  elimination, then `componentPipeline`; its run function is
  `optimizeProgram`;
* **`optimizeComponent_sound`**: `(optimizeComponent c).denU C = c.denU C`
  (same interface sizes), hence the typed denotations agree
  (`optimizeComponent_den`);
* unconditional versions: `linkedPipeline'`, `componentPipeline'`,
  `programPipeline'` (with `componentPipeline'_run`, `programPipeline'_run`),
  `denU_optimizeLinked'`, **`optimizeComponent_sound'`**,
  `optimizeComponent_den'`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Compile.PassAPI
open CategoryTheory

variable {M : Type} [CoreModule M]

/-! ## Lifting component passes to programs -/

/-- A component pass, applied to the component of a program. -/
def liftProgram {C : CoreSem M} (p : Pass (contract C)) : Pass (programIR C).contract where
  run q := { q with comp := p.run q.comp }
  inv_run _ := trivial
  sound {q} _ := by
    obtain ⟨h₁, h₂, h₃⟩ := p.sound (x := q.comp) trivial
    obtain ⟨c, obs⟩ := q
    cases obs with
    | none => exact ⟨h₁, h₂, h₃⟩
    | some obs => exact ⟨h₁, rfl, Strategy.comp_mono h₃ le_rfl⟩

/-! ## Unconditional pipelines -/

/-- Adapter fusion on the nested IR. -/
def fusionPipeline (C : CoreSem M) : Pass (contract C) := Pass.pipeline [fusePass C]

/-- Adapter fusion on the flat IR. -/
def linkedFusionPipeline (C : CoreSem M) : Pass (linkedIR C).contract :=
  Pass.pipeline [fuseLinkedPass C]

/-- Dead export elimination, then adapter fusion. -/
def programFusionPipeline (C : CoreSem M) : Pass (programIR C).contract :=
  deadExportPass C * liftProgram (fusionPipeline C)

/-- Soundness of the unconditional program pipeline: equal interface sizes and
refinement (in fact equality, see `denU_deadExports`, `denU_fuseComponent`). -/
theorem programFusionPipeline_sound (C : CoreSem M) (p : Program M) :
    (programIR C).contract.Rel p ((programFusionPipeline C).run p) :=
  (programFusionPipeline C).sound trivial

/-! ## The full pipeline (conditional on the pairing laws) -/

/-- Adapter fusion, then dead instance elimination, on the flat IR. -/
def linkedPipeline (L : PairLaws) (C : CoreSem M) : Pass (linkedIR C).contract :=
  fuseLinkedPass C * deadInstancePass L C

/-- Flatten, optimise the flat component, embed back. -/
def componentPipeline (L : PairLaws) (C : CoreSem M) : Pass (contract C) :=
  endEquiv (nestedIR C)
    (flattenT L C ≫ (endEquiv (linkedIR C)).symm (linkedPipeline L C) ≫ toComponentT C)

/-- The run function of the component pipeline is `optimizeComponent`. -/
theorem componentPipeline_run (L : PairLaws) (C : CoreSem M) :
    (componentPipeline L C).run = optimizeComponent := rfl

/-- Dead export elimination, then the component pipeline. -/
def programPipeline (L : PairLaws) (C : CoreSem M) : Pass (programIR C).contract :=
  deadExportPass C * liftProgram (componentPipeline L C)

/-- The run function of the program pipeline is `optimizeProgram`. -/
theorem programPipeline_run (L : PairLaws) (C : CoreSem M) :
    (programPipeline L C).run = optimizeProgram := rfl

theorem denU_optimizeLinked (L : PairLaws) (C : CoreSem M) (l : Linked M) :
    (optimizeLinked l).denU C = l.denU C := by
  unfold optimizeLinked deadInstances
  rw [← denU_fuseLinked C l]
  generalize fuseLinked l = l'
  generalize (List.range l'.nodes.length).reverse = ks
  induction ks generalizing l' with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases h : removeNode l' k with
    | none => rfl
    | some l'' => exact denU_removeNode L C h

/-- **Soundness of the component optimiser** (assuming `PairLaws`): for every
core semantics, the optimised component has the same strategy and the same
interface sizes. -/
theorem optimizeComponent_sound (L : PairLaws) (C : CoreSem M) (c : Comp M) :
    (optimizeComponent c).denU C = c.denU C ∧
      (optimizeComponent c).imports.length = c.imports.length ∧
      (optimizeComponent c).exports.length = c.exports.length := by
  obtain ⟨h₁, h₂, -⟩ := (componentPipeline L C).sound (x := c) trivial
  refine ⟨?_, h₁, h₂⟩
  simp only [optimizeComponent]
  rw [Linked.denU_toComponent, denU_optimizeLinked L C, denU_flatten L C]

/-- The typed denotation of the optimised component (at the common interface
sizes). -/
theorem optimizeComponent_den (L : PairLaws) (C : CoreSem M) (c : Comp M) (n k : Nat) :
    atSizes n k ((optimizeComponent c).denU C) = atSizes n k (c.denU C) := by
  rw [(optimizeComponent_sound L C c).1]

/-! ## Unconditional versions -/

/-- Adapter fusion, then dead instance elimination, on the flat IR. -/
def linkedPipeline' (C : CoreSem M) : Pass (linkedIR C).contract := linkedPipeline pairLaws C

/-- Flatten, optimise the flat component, embed back. -/
def componentPipeline' (C : CoreSem M) : Pass (contract C) := componentPipeline pairLaws C

/-- The run function of the component pipeline is `optimizeComponent`. -/
theorem componentPipeline'_run (C : CoreSem M) : (componentPipeline' C).run = optimizeComponent :=
  rfl

/-- Dead export elimination, then the component pipeline. -/
def programPipeline' (C : CoreSem M) : Pass (programIR C).contract := programPipeline pairLaws C

/-- The run function of the program pipeline is `optimizeProgram`. -/
theorem programPipeline'_run (C : CoreSem M) : (programPipeline' C).run = optimizeProgram := rfl

/-- Optimising a flat component preserves its denotation. -/
theorem denU_optimizeLinked' (C : CoreSem M) (l : Linked M) :
    (optimizeLinked l).denU C = l.denU C :=
  denU_optimizeLinked pairLaws C l

/-- **Soundness of the component optimiser**: for every core semantics, the
optimised component has the same strategy and the same interface sizes. -/
theorem optimizeComponent_sound' (C : CoreSem M) (c : Comp M) :
    (optimizeComponent c).denU C = c.denU C ∧
      (optimizeComponent c).imports.length = c.imports.length ∧
      (optimizeComponent c).exports.length = c.exports.length :=
  optimizeComponent_sound pairLaws C c

/-- The typed denotation of the optimised component (at the common interface
sizes). -/
theorem optimizeComponent_den' (C : CoreSem M) (c : Comp M) (n k : Nat) :
    atSizes n k ((optimizeComponent c).denU C) = atSizes n k (c.denU C) :=
  optimizeComponent_den pairLaws C c n k

end Silmaril.Wasm.Component
