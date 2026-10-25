module

public import Silmaril.Wasm.Link.Initializers

/-! # Scoped control annotations in linked module views

Successful source lookups preserve allocated type tags. Scoping is also needed
for inline annotations: an unavailable source type index must not acquire a
meaning merely because the linked module has a larger type table.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.ControlViews

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

theorem value_free_indices {n : Nat} {v : ValType} (scope : v.Scoped n) :
    ∀ x ∈ (liftVal v).freeIdx, x < n := by
  cases v with
  | num t => simp [liftVal, Ty.freeIdx]
  | vec t => simp [liftVal, Ty.freeIdx]
  | ref rt =>
    rcases rt with ⟨nullable, heap⟩
    cases heap with
    | abstract a => cases a <;> simp [liftVal, liftRef, liftHeap, Ty.freeIdx]
    | typeIdx x =>
      simpa [liftVal, liftRef, liftHeap, liftTypeIdx, Ty.freeIdx,
        ValType.Scoped, RefType.Scoped, HeapType.Scoped] using scope

/-- Type checking a closed annotation excludes every unavailable source
index, including indices left un-substituted by a failed lookup. -/
theorem scope_of_closed_type {C : Context} {kind : TKind} {t : Ty kind}
    (valid : TyOk C.toTypeCtx (t.substAll (C.types.map .dt))) :
    ∀ x ∈ t.freeIdx, x < C.types.length := by
  intro x hx
  by_contra hn
  have hg : C.types[x]? = none := List.getElem?_eq_none (by omega)
  have hs : Subst.all (C.types.map .dt) (.idx x) = none := by
    simp only [Subst.all, List.getElem?_map, hg, Option.map_none]
  exact hn (TyOk.freeIdx_lt valid x (Ty.freeIdx_subst_of_none _ _ x hx hs))

theorem ref_scope_of_typing {C : Context} {rt : RefType}
    (valid : TyOk C.toTypeCtx (C.closeRef rt)) : rt.Scoped C.types.length := by
  rcases rt with ⟨nullable, heap⟩
  cases heap with
  | abstract a => trivial
  | typeIdx x =>
    exact scope_of_closed_type valid x.toNat
      (by simp only [liftRef, liftHeap, liftTypeIdx, Ty.freeIdx, List.mem_singleton])

theorem value_scope_of_typing {C : Context} {v : ValType}
    (valid : TyOk C.toTypeCtx (C.closeVal v)) : v.Scoped C.types.length := by
  cases v with
  | num t => trivial
  | vec t => trivial
  | ref rt =>
    rcases rt with ⟨nullable, heap⟩
    cases heap with
    | abstract a => trivial
    | typeIdx x =>
      exact scope_of_closed_type valid x.toNat
        (by simp only [liftVal, liftRef, liftHeap, liftTypeIdx, Ty.freeIdx, List.mem_singleton])

theorem closed_value_type {left right : ModuleInst} {r : Relocation} {v v' : ValType}
    (views : Views.Successful r left right) (rewrite : valType? r.types v = some v')
    (scope : v.Scoped left.types.length) : right.instVal v' = left.instVal v :=
  Initializers.closed_value_type views rewrite (value_free_indices scope)

theorem closed_ref_type {left right : ModuleInst} {r : Relocation} {rt rt' : RefType}
    (views : Views.Successful r left right) (rewrite : refType? r.types rt = some rt')
    (scope : rt.Scoped left.types.length) : right.instRef rt' = left.instRef rt := by
  rcases rt with ⟨nullable, heap⟩
  cases heap with
  | abstract a =>
    simp only [refType?, heap?, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at rewrite
    subst rt'
    cases a <;> rfl
  | typeIdx x =>
    simp only [refType?, heap?, Option.map_eq_map, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.pure_def,
      Option.some.injEq] at rewrite
    obtain ⟨heap', ⟨y, hy, rfl⟩, rfl⟩ := rewrite
    have hx : x.toNat < left.types.length := scope
    have hd := List.getElem?_eq_getElem hx
    exact LinkExecution.instRef_type_of_lookup nullable (views.types hy hd) hd

def BlockScoped (n : Nat) : BlockType → Prop
  | .empty => True
  | .value t => t.Scoped n
  | .typeIdx x => x.toNat < n

theorem block_scope_of_typing {C : Context} {bt : BlockType} {params results : List CValType}
    (valid : BlockTypeOk C bt params results) : BlockScoped C.types.length bt := by
  cases valid with
  | empty => trivial
  | value hv => exact value_scope_of_typing hv
  | typeIdx hd _ => exact (List.getElem?_eq_some_iff.mp hd).1

/-- Relocated blocks and loops see the same closed parameter/result types.
The type-index case uses its successful operational lookup; the inline case
uses source scoping. -/
theorem block_lookup {left right : ModuleInst} {r : Relocation} {bt bt' : BlockType}
    {params results : List CValType}
    (views : Views.Successful r left right) (rewrite : blockType? r.types bt = some bt')
    (scope : BlockScoped left.types.length bt)
    (lookup : left.blockType? bt = some (params, results)) :
    right.blockType? bt' = some (params, results) := by
  cases bt with
  | empty =>
    simp only [blockType?, Option.some.injEq] at rewrite
    subst bt'
    exact lookup
  | value v =>
    simp only [blockType?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
    obtain ⟨v', hv, rfl⟩ := rewrite
    simpa only [ModuleInst.blockType?, closed_value_type views hv scope] using lookup
  | typeIdx x =>
    simp only [blockType?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
    obtain ⟨y, hy, rfl⟩ := rewrite
    simp only [ModuleInst.blockType?, Option.bind_eq_bind, Option.bind_eq_some_iff] at lookup
    obtain ⟨d, hd, result⟩ := lookup
    simp only [ModuleInst.blockType?, views.types hy hd, Option.bind_eq_bind, Option.bind_some]
    exact result

end Silmaril.Wasm.Link.GC.ControlViews
