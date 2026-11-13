module

public import Silmaril.Wasm.Wit.Project.IR.Defs

/-!
# The world of an IR component under composition and optimisation

* flattening (`flatten`: composing nested component instances into one flat
  component), adapter fusion, dead instance elimination and the whole optimiser
  keep the world;
* specialisation (`specialise J σ₀ c`: composing providers `σ₀` over new imports
  `J` into the imports of `c`) keeps the exports and replaces the imports by `J`;
* dead export elimination keeps the imports.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component

variable {M : Type}

theorem exportIface_mapImpl (f : Export → Impl) (xs : List Export) :
    exportIface (xs.map fun x => { x with impl := f x }) = exportIface xs := by
  simp [exportIface, Function.comp_def]

theorem world_toComponent (l : Linked M) : compWorld (Linked.toComponent l) = linkedWorld l := rfl

theorem world_mapImpls (f : Impl → Impl) (c : Comp M) :
    compWorld (c.mapImpls f) = compWorld c := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [compWorld, Comp.mapImpls, Comp.imports_mk, Comp.exports_mk]
  rw [exportIface_mapImpl (fun x => f x.impl)]

/-- Adapter fusion keeps the world. -/
theorem world_fuseComponent (c : Comp M) : compWorld (fuseComponent c) = compWorld c :=
  world_mapImpls _ c

/-- Adapter fusion keeps the world (flat components). -/
theorem world_fuseLinked (l : Linked M) : linkedWorld (fuseLinked l) = linkedWorld l := by
  simp only [linkedWorld, fuseLinked]
  rw [exportIface_mapImpl (fun x => x.impl.fuse)]

variable [CoreModule M]

/-- **Flattening keeps the world**: composing the nested instances of a
component into one flat component does not change its imports and exports. -/
theorem world_flatten (c : Comp M) : linkedWorld (flatten c) = compWorld c := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [flatten, linkedWorld, compWorld, Comp.imports_mk, Comp.exports_mk]
  rw [exportIface_mapImpl]

/-- **Specialisation** composes providers into the imports: the exports are kept
and the imports become the providers' imports `J`. -/
theorem world_specialise (J : Iface) (σ₀ : List Impl) (c : Comp M) :
    linkedWorld (specialise J σ₀ c) = ⟨J, (compWorld c).exports⟩ := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [specialise, linkedWorld, compWorld, Comp.exports_mk]
  rw [exportIface_mapImpl]

theorem world_removeNode {l l' : Linked M} {k : Nat} (h : removeNode l k = some l') :
    linkedWorld l' = linkedWorld l := by
  unfold removeNode at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
      simp only [linkedWorld]
      rw [exportIface_mapImpl]
    · cases h

/-- Dead instance elimination keeps the world. -/
theorem world_deadInstances (l : Linked M) : linkedWorld (deadInstances l) = linkedWorld l := by
  unfold deadInstances
  generalize (List.range l.nodes.length).reverse = ks
  induction ks generalizing l with
  | nil => rfl
  | cons k ks ih =>
    rw [List.foldl_cons, ih]
    cases h : removeNode l k with
    | none => rfl
    | some l' => exact world_removeNode h

/-- **The optimiser keeps the world.** -/
theorem world_optimizeComponent (c : Comp M) :
    compWorld (optimizeComponent c) = compWorld c := by
  unfold optimizeComponent optimizeLinked
  rw [world_toComponent, world_deadInstances, world_fuseLinked, world_flatten]

omit [CoreModule M] in
/-- Dead export elimination keeps the imports. -/
theorem world_deadExports_imports (p : Program M) :
    (compWorld (deadExports p).comp).imports = (compWorld p.comp).imports := by
  obtain ⟨⟨I, ns, xs⟩, obs⟩ := p
  cases obs <;> rfl

end Silmaril.Wasm.Wit.Project
