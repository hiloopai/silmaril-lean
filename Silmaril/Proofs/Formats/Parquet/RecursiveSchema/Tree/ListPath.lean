module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema hiding Compiled Context
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Boundary Context Step)
open Silmaril.Formats.Parquet.RecursiveSchema.Tree

private theorem wrap_steps (ancestors : List Ancestor) (ctx : Context) (site : Site) (kind : Kind) :
    (ancestors.foldr (fun (ancestor : Ancestor) child => ancestor.wrap child) (.signed site kind)).steps ctx =
      ((ancestors.foldl Ancestor.enter ctx).enter site).steps := by
  induction ancestors generalizing ctx with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | struct site => exact ih (ctx.enter site)
    | list site wrapper => exact ih (ctx.enterList site wrapper)

private theorem plan_leaf (ancestors : List Ancestor) (site : Site) (kind : Kind) :
    (ancestors.foldr (fun (ancestor : Ancestor) child => ancestor.wrap child) (.signed site kind)).leaf = (site, kind) := by
  induction ancestors with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> exact ih

private theorem wrapper_count (shape : ListPath.Shape) (ctx : Context) :
    ((shape.steps ctx).filterMap Step.wrapper?).length =
      (ctx.steps.filterMap Step.wrapper?).length + shape.repetitions := by
  induction shape generalizing ctx with
  | signed site _ =>
    cases nullable : site.nullable <;>
      simp [ListPath.Shape.steps, ListPath.Shape.repetitions, Repeated.Context.enter,
        List.filterMap_append, Step.wrapper?, nullable]
  | struct site _ ih =>
    simp only [ListPath.Shape.steps, ListPath.Shape.repetitions, ih]
    cases nullable : site.nullable <;> simp [Repeated.Context.enter, List.filterMap_append, Step.wrapper?, nullable]
  | list node _ ih =>
    simp only [ListPath.Shape.steps, ListPath.Shape.repetitions, ih]
    cases nullable : node.site.nullable <;>
      simp [Silmaril.Formats.Parquet.RecursiveSchema.TwoList.ListSite.enter, Repeated.Context.enterList,
        List.filterMap_append, List.filterMap_cons, Step.wrapper?, Nat.add_assoc, nullable]

private def boundaryAt (step : Step × Nat) : Option Boundary :=
  match step with
  | (.emptyList outer wrapper, level) => some ⟨outer, wrapper, level⟩
  | (.optional .., _) => none

private theorem boundary_indices (steps : List (Step × Nat)) :
    (steps.filterMap boundaryAt).map (·.emptyLevel) =
      steps.filterMap (fun (step, level) => if step.wrapper?.isSome then some level else none) := by
  induction steps with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨step, level⟩
    cases step <;> simp [List.filterMap_cons, boundaryAt, Step.wrapper?, ih]

private theorem boundary_count (steps : List (Step × Nat)) :
    (steps.filterMap boundaryAt).length = (steps.filterMap (fun pair => pair.1.wrapper?)).length := by
  induction steps with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨step, level⟩
    cases step <;> simp [List.filterMap_cons, boundaryAt, Step.wrapper?, ih]

private theorem path_levels {P : Type} [ListPath.Chunk.ScanShape P] {path : LeafPath} {plan : P}
    (shape : ListPath.Chunk.ScanShape.shape plan = path.shape) :
    let original := ListPath.Chunk.ScanShape.shape plan
    original.leaf = (path.site, path.kind) ∧ original.steps {} = path.steps ∧
      original.definitions = path.maxDefinition ∧ original.repetitions = path.maxRepetition ∧
      ListPath.Chunk.wrappers plan = path.repeated.map (·.emptyLevel) := by
  have steps : (ListPath.Chunk.ScanShape.shape plan).steps {} = path.steps :=
    shape.symm ▸ wrap_steps path.ancestors {} path.site path.kind
  have leaf : (ListPath.Chunk.ScanShape.shape plan).leaf = (path.site, path.kind) :=
    shape.symm ▸ plan_leaf path.ancestors path.site path.kind
  have defn := ListPath.Shape.steps_length (ListPath.Chunk.ScanShape.shape plan) {}
  rw [steps] at defn
  have repeated := boundary_count path.steps.zipIdx
  change _ = (path.steps.zipIdx.filterMap (Step.wrapper? ∘ Prod.fst)).length at repeated
  rw [← List.filterMap_map, List.zipIdx_map_fst] at repeated
  change path.maxRepetition = _ at repeated
  have reps := wrapper_count (ListPath.Chunk.ScanShape.shape plan) {}
  rw [steps] at reps
  refine ⟨leaf, steps, ?_, ?_, ?_⟩
  · simpa [LeafPath.maxDefinition] using defn.symm
  · change _ = 0 + _ at reps
    rw [Nat.zero_add] at reps
    exact reps.symm.trans repeated.symm
  · unfold ListPath.Chunk.wrappers
    rw [steps]
    exact (boundary_indices path.steps.zipIdx).symm

public theorem projected_levels {path : LeafPath} {plan : ListPath.Plan} (projected : path.listPlan = some plan) :
    plan.shape.leaf = (path.site, path.kind) ∧ plan.shape.steps {} = path.steps ∧
      plan.shape.definitions = path.maxDefinition ∧ plan.shape.repetitions = path.maxRepetition ∧
      ListPath.Chunk.wrappers plan = path.repeated.map (·.emptyLevel) := by
  have shape : plan.shape = path.shape := by
    unfold LeafPath.listPlan at projected
    cases seen : path.shape with
    | signed _ _ => simp [seen] at projected
    | struct _ _ => simp [seen] at projected
    | list outer child =>
      simp only [seen, Option.some.injEq] at projected
      cases projected
      rfl
  exact path_levels (path := path) (plan := plan) shape

public theorem scan_levels {path : LeafPath} {plan : ListPath.Chunk.RepeatedPath}
    (projected : path.scanPlan = some plan) :
    plan.shape = path.shape ∧ plan.shape.leaf = (path.site, path.kind) ∧ plan.shape.steps {} = path.steps ∧
      plan.shape.definitions = path.maxDefinition ∧ plan.shape.repetitions = path.maxRepetition ∧
      ListPath.Chunk.wrappers plan = path.repeated.map (·.emptyLevel) := by
  have shape : plan.shape = path.shape := by
    dsimp only [LeafPath.scanPlan] at projected
    split at projected
    · cases projected
      rfl
    · contradiction
  exact ⟨shape, path_levels (path := path) (plan := plan) shape⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree
