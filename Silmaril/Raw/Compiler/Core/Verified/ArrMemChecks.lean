module

public import Silmaril.Compiler.Core.Verified.ArrInit.Defs
public import Silmaril.Compiler.Core.Verified.SubobjectChecks.Defs
/-! # Array invariants on an actual two-element allocation

These witnesses ensure the invariant admits adjacent elements with the same
provenance, rejects one-past definitions, and retains the untouched value across
an overwrite. The loads use the canonical typed-memory operations.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrMemChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open ArrMem

def array (x : Sym) : Array := ⟨⟨x, 0, 4096⟩, 2⟩

theorem initial (x : Sym) : Inv SubobjectChecks.memory [array x] (fun _ => none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain rfl := List.mem_singleton.mp ha
    refine ⟨by simp [SubobjectChecks.memory, array], ⟨{base := 4096, size := 8}, ?_, rfl,
      by norm_num [array], rfl, rfl⟩⟩
    simp [SubobjectChecks.memory, array]
  · intro a ha
    obtain rfl := List.mem_singleton.mp ha
    norm_num [array]
  · intro a ha b hb _
    exact (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm
  · intro a ha b hb ne
    obtain rfl := List.mem_singleton.mp ha
    obtain rfl := List.mem_singleton.mp hb
    exact False.elim (ne rfl)
  · intro q d hd
    cases hd

def definitions (x : Sym) : Defs :=
  update (update (fun _ => none) (x.key, 0) (some (.lit 17))) (x.key, 1) (some (.lit (-23)))

def memory : Mem.Concrete.State :=
  Locals.stored (Locals.stored SubobjectChecks.memory 0 4096 17) 0 4100 (-23)

/-- Two element definitions coexist in a single eight-byte allocation. -/
theorem initialized (x : Sym) : Inv memory [array x] (definitions x) := by
  have first := (initial x).store (a := array x) (by simp) (i := 0) (by norm_num [array])
    (.lit 17) (by constructor <;> decide)
  have second := first.store (a := array x) (by simp) (i := 1) (by norm_num [array])
    (.lit (-23)) (by constructor <;> decide)
  exact second

/-- An overwrite changes element zero and keeps the signed value in element one. -/
theorem overwrite (x : Sym) (tags : Mem.Concrete.Tags) (ann : List Annot) :
    let m := Locals.stored memory 0 4096 99
    Mem.Concrete.loadTyped tags m (Mem.Concrete.intType ann) (.allocated 0 4096) =
      .ok (.integer (.signed .int) 99, {m with lastUsed := some 0}) ∧
    Mem.Concrete.loadTyped tags m (Mem.Concrete.intType ann) (.allocated 0 4100) =
      .ok (.integer (.signed .int) (-23), {m with lastUsed := some 0}) := by
  have inv := (initialized x).store (a := array x) (by simp) (i := 0) (by norm_num [array])
    (.lit 99) (by constructor <;> decide)
  have first := (inv.element (a := array x) (by simp) (i := 0)
    (d := .lit 99) (by simp [update])).2.2
  have second := (inv.element (a := array x) (by simp) (i := 1)
    (d := .lit (-23)) (by simp [update, definitions, array])).2.2
  exact ⟨IntSubobject.load tags ann first.live first.plain (by constructor <;> decide) first.bytes,
    IntSubobject.load tags ann second.live second.plain (by constructor <;> decide) second.bytes⟩

/-- The invariant cannot claim an initialized one-past element, regardless of its bytes. -/
theorem one_past_rejected (x : Sym) (m : Mem.Concrete.State) (ds : Defs) (d : IntExpr.Term)
    (h : Inv m [array x] ds) : ds (x.key, 2) ≠ some d := by
  intro hd
  have bound := (h.element (a := array x) (by simp) hd).2.1
  change 2 < 2 at bound
  omega

/-- Whole-array unspecified initialization forgets both old definitions. -/
theorem uninitialized (x : Sym) :
    Inv (ArrInit.stored memory 0 4096 2) [array x]
      (ArrInit.forget (definitions x) x.key) ∧
    ArrInit.forget (definitions x) x.key (x.key, 0) = none ∧
    ArrInit.forget (definitions x) x.key (x.key, 1) = none :=
  ⟨ArrInit.inv_stored (initialized x) (a := array x) (by simp), by simp [ArrInit.forget],
    by simp [ArrInit.forget]⟩

end Silmaril.Compile.Core.Verified.ArrMemChecks
