module

public import Mathlib.Data.List.Basic

/-!
# Partial environments for operational semantics

Functional partial maps and their pointwise update laws, shared by local
environments and heaps. No allocation policy or language syntax is imposed.
-/

@[expose] public section

namespace Silmaril.Semantics.Operational

universe u v

abbrev Environment (Key : Type u) (Value : Type v) := Key → Option Value

namespace Environment

variable {Key : Type u} {Value : Type v}

def empty : Environment Key Value := fun _ => none

def set [DecidableEq Key] (env : Environment Key Value) (key : Key) (value : Value) :
    Environment Key Value := fun other => if other = key then some value else env other

def erase [DecidableEq Key] (env : Environment Key Value) (key : Key) :
    Environment Key Value := fun other => if other = key then none else env other

/-- Use the default only when the queried key is absent. -/
def lookup (env : Environment Key Value) (key : Key) (default : Option Value) : Option Value :=
  (env key).or default

/-- A finite list witnesses that an environment has no bindings outside its support. -/
def SupportedBy (env : Environment Key Value) (support : List Key) : Prop :=
  ∀ key value, env key = some value → key ∈ support

theorem empty_supported : SupportedBy (empty : Environment Key Value) [] := by
  intro key value present
  cases present

theorem set_supported [DecidableEq Key] (env : Environment Key Value) (support : List Key)
    (supported : SupportedBy env support) (key : Key) (value : Value) :
    SupportedBy (set env key value) (key :: support) := by
  intro other found present
  by_cases equal : other = key
  · simp [equal]
  · simp only [set, ite_eq_right equal] at present
    exact List.mem_cons_of_mem _ (supported other found present)

theorem erase_supported [DecidableEq Key] (env : Environment Key Value) (support : List Key)
    (supported : SupportedBy env support) (key : Key) :
    SupportedBy (erase env key) support := by
  intro other found present
  by_cases equal : other = key
  · simp [erase, equal] at present
  · simp only [erase, ite_eq_right equal] at present
    exact supported other found present

theorem absent_outside_support (env : Environment Key Value) (support : List Key)
    (supported : SupportedBy env support) (key : Key) (outside : key ∉ support) :
    env key = none := by
  cases present : env key with
  | none => rfl
  | some value => exact False.elim (outside (supported key value present))

@[simp] theorem empty_apply (key : Key) : (empty : Environment Key Value) key = none := rfl

@[simp] theorem set_same [DecidableEq Key] (env : Environment Key Value) (key : Key)
    (value : Value) : set env key value key = some value := by simp [set]

@[simp] theorem set_other [DecidableEq Key] (env : Environment Key Value) (key other : Key)
    (value : Value) (h : other ≠ key) : set env key value other = env other := by simp [set, h]

@[simp] theorem erase_same [DecidableEq Key] (env : Environment Key Value) (key : Key) :
    erase env key key = none := by simp [erase]

@[simp] theorem erase_other [DecidableEq Key] (env : Environment Key Value) (key other : Key)
    (h : other ≠ key) : erase env key other = env other := by simp [erase, h]

@[simp] theorem lookup_some (env : Environment Key Value) (key : Key) (value : Value)
    (default : Option Value) (h : env key = some value) :
    lookup env key default = some value := by simp [lookup, h]

@[simp] theorem lookup_none (env : Environment Key Value) (key : Key)
    (default : Option Value) (h : env key = none) :
    lookup env key default = default := by simp [lookup, h]

theorem set_set [DecidableEq Key] (env : Environment Key Value) (key : Key)
    (first second : Value) : set (set env key first) key second = set env key second := by
  funext other
  by_cases h : other = key <;> simp [set, h]

theorem set_comm [DecidableEq Key] (env : Environment Key Value) (left right : Key)
    (first second : Value) (h : left ≠ right) :
    set (set env left first) right second = set (set env right second) left first := by
  funext other
  by_cases hl : other = left
  · subst other; simp [set, h]
  · by_cases hr : other = right <;> simp [set, hl, hr, Ne.symm h]

theorem erase_set_of_absent [DecidableEq Key] (env : Environment Key Value) (key : Key)
    (value : Value) (h : env key = none) : erase (set env key value) key = env := by
  funext other
  by_cases heq : other = key
  · subst other; simp [h]
  · simp [heq]

end Environment

end Silmaril.Semantics.Operational
