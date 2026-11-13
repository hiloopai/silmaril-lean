module

public import Silmaril.Proofs.Wasm.LimeCompile.Select.Fam

/-!
# Erasing `select` annotations: redexes of the families are rigid

The left-hand side of every rule of the numeric, vector and state families consists of values
and flat plain instructions, so its only erasure-preimage is itself. Also: inversions of erased
code against a rigid prefix, a plain instruction after values, and a `label`, `handler` or
`frame`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Select

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.LimeCompile.Select

variable {H : Type} {P : Profile}

theorem rig_constI32 (c : BitVec 32) : Rig (constI32 c) := rig_val _

theorem numeric_rig {L R : List Admin} (h : NumericStep P L R) : AllRig L := by
  cases h <;> repeat' first
    | with_reducible apply allRig_cons
    | with_reducible exact allRig_nil
    | with_reducible exact rig_val _
    | with_reducible apply rig_plain
    | exact flat_mk rfl fun _ h => nomatch h

theorem vector_rig {L R : List Admin} (h : VectorStep P L R) : AllRig L := by
  cases h <;> repeat' first
    | with_reducible apply allRig_cons
    | with_reducible exact allRig_nil
    | with_reducible exact rig_val _
    | with_reducible exact rig_constI32 _
    | with_reducible apply rig_plain
    | exact flat_mk rfl fun _ h => nomatch h

theorem variable_rig {c c' : Config H} (h : VariableStep c c') : AllRig c.code := by
  cases h <;> repeat' first
    | with_reducible apply allRig_cons
    | with_reducible exact allRig_nil
    | with_reducible exact rig_val _
    | with_reducible apply rig_plain
    | exact flat_mk rfl fun _ h => nomatch h

theorem table_rig {c c' : Config H} (h : TableStep P c c') : AllRig c.code := by
  cases h <;> repeat' first
    | with_reducible apply allRig_cons
    | with_reducible exact allRig_nil
    | with_reducible exact rig_val _
    | with_reducible exact rig_constI32 _
    | with_reducible exact rig_ref _
    | with_reducible apply rig_plain
    | exact flat_mk rfl fun _ h => nomatch h

theorem memory_rig {c c' : Config H} (h : MemoryStep P c c') : AllRig c.code := by
  cases h <;> repeat' first
    | with_reducible apply allRig_cons
    | with_reducible exact allRig_nil
    | with_reducible exact rig_val _
    | with_reducible exact rig_constI32 _
    | with_reducible apply rig_plain
    | exact flat_mk rfl fun _ h => nomatch h

theorem reference_rig {c c' : Config H} (h : RefStep c c') : AllRig c.code := by
  cases h <;> repeat' first
    | with_reducible apply allRig_cons
    | with_reducible exact allRig_nil
    | with_reducible exact rig_constI32 _
    | with_reducible exact rig_ref _
    | with_reducible apply rig_plain
    | exact flat_mk rfl fun _ h => nomatch h

theorem aggregate_rig {c c' : Config H} (h : AggregateStep c c') : AllRig c.code := by
  cases h <;> repeat' first
    | with_reducible apply allRig_cons
    | with_reducible exact allRig_nil
    | with_reducible apply allRig_append
    | with_reducible exact allRig_vals _
    | with_reducible exact rig_val _
    | with_reducible exact rig_constI32 _
    | with_reducible exact rig_ref _
    | with_reducible apply rig_plain
    | exact flat_mk rfl fun _ h => nomatch h

/-! ## Inversions -/

theorem rigid_prefix {X A R : List Admin} (hA : AllRig A) (h : selAs X = selAs (A ++ R)) :
    ∃ R', X = A ++ R' ∧ selAs R' = selAs R := by
  obtain ⟨A', R', rfl, hA', hR⟩ := selAs_eq_append h
  exact ⟨R', by rw [eq_of_selAs_rig hA hA'], hR⟩

theorem plain_inv {D : List Admin} {vs : List Val} {i : Instr}
    (h : selAs D = selAs (vals vs ++ [.plain i])) :
    ∃ j, D = vals vs ++ [.plain j] ∧ selI j = selI i := by
  obtain ⟨B, rfl, hB⟩ := selAs_eq_vals_append h
  obtain ⟨a, rfl, ha⟩ := selAs_eq_singleton hB
  obtain ⟨j, rfl, hj⟩ := selA_eq_plain ha
  exact ⟨j, rfl, hj⟩

theorem label_inv {D : List Admin} {n : Nat} {cont : List Instr} {B : List Admin}
    (h : selAs D = selAs [.label n cont B]) :
    ∃ cont' B', D = [.label n cont' B'] ∧ selL cont' = selL cont ∧ selAs B' = selAs B := by
  obtain ⟨a, rfl, ha⟩ := selAs_eq_singleton h
  obtain ⟨cont', B', rfl, hc, hB⟩ := selA_eq_label ha
  exact ⟨cont', B', rfl, hc, hB⟩

theorem handler_inv {D : List Admin} {n : Nat} {cs : List Catch} {B : List Admin}
    (h : selAs D = selAs [.handler n cs B]) :
    ∃ B', D = [.handler n cs B'] ∧ selAs B' = selAs B := by
  obtain ⟨a, rfl, ha⟩ := selAs_eq_singleton h
  obtain ⟨B', rfl, hB⟩ := selA_eq_handler ha
  exact ⟨B', rfl, hB⟩

theorem frame_inv {D : List Admin} {n : Nat} {f : Frame} {B : List Admin}
    (h : selAs D = selAs [.frame n f B]) :
    ∃ B', D = [.frame n f B'] ∧ selAs B' = selAs B := by
  obtain ⟨a, rfl, ha⟩ := selAs_eq_singleton h
  obtain ⟨B', rfl, hB⟩ := selA_eq_frame ha
  exact ⟨B', rfl, hB⟩

theorem selAs_ne_nil {X Y : List Admin} (h : selAs X = selAs Y) (hY : Y ≠ []) : X ≠ [] := by
  rintro rfl
  exact hY (selAs_eq_nil.mp h.symm)

end Silmaril.Proofs.Wasm.LimeCompile.Select
