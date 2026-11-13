module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Dedup

/-!
# Snoc contexts

Anonymous entries retain their position and type but cannot be looked up.
Normalization preserves the full context shape while replacing older shadowed
names by anonymous entries.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope

variable {ν : Type u} {τ : Type v}

/-- A snoc context of optional names and types. -/
inductive Ctx (ν : Type u) (τ : Type v) : Type (max u v) where
  | nil
  | snoc (Γ : Ctx ν τ) (name : Option ν) (ty : τ)
  deriving Repr, DecidableEq

namespace Ctx

/-- Number of entries, including anonymous entries. -/
def length : Ctx ν τ → Nat
  | .nil => 0
  | .snoc Γ _ _ => Γ.length + 1

/-- Types in oldest-to-newest order. -/
def types : Ctx ν τ → List τ
  | .nil => []
  | .snoc Γ _ A => Γ.types ++ [A]

/-- Lookup the newest visible binding of a name. -/
def lookup [DecidableEq ν] : Ctx ν τ → ν → Option τ
  | .nil, _ => none
  | .snoc Γ none _, x => Γ.lookup x
  | .snoc Γ (some y) A, x => if x = y then some A else Γ.lookup x

/-- Replace every occurrence of `x` by an anonymous entry. -/
def mask [DecidableEq ν] (x : ν) : Ctx ν τ → Ctx ν τ
  | .nil => .nil
  | .snoc Γ none A => .snoc (mask x Γ) none A
  | .snoc Γ (some y) A =>
      .snoc (mask x Γ) (if x = y then none else some y) A

/-- Remove shadowing without removing entries, scanning newest-to-oldest. -/
def normalize [DecidableEq ν] : Ctx ν τ → Ctx ν τ
  | .nil => .nil
  | .snoc Γ none A => .snoc (normalize Γ) none A
  | .snoc Γ (some x) A => .snoc (mask x (normalize Γ)) (some x) A

@[simp] theorem length_mask [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) :
    (mask x Γ).length = Γ.length := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => cases n <;> simp [mask, length, ih]

@[simp] theorem types_mask [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) :
    (mask x Γ).types = Γ.types := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => cases n <;> simp [mask, types, ih]

@[simp] theorem length_normalize [DecidableEq ν] (Γ : Ctx ν τ) :
    (normalize Γ).length = Γ.length := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => cases n <;> simp [normalize, length, ih]

@[simp] theorem types_normalize [DecidableEq ν] (Γ : Ctx ν τ) :
    (normalize Γ).types = Γ.types := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => cases n <;> simp [normalize, types, ih]

@[simp] theorem lookup_mask_self [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) :
    (mask x Γ).lookup x = none := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simpa [mask, lookup] using ih
      | some y =>
          by_cases h : x = y
          · subst y
            simp [mask, lookup, ih]
          · simp [mask, lookup, h, ih]

theorem lookup_mask_of_ne [DecidableEq ν] {x y : ν} (h : y ≠ x) (Γ : Ctx ν τ) :
    (mask x Γ).lookup y = Γ.lookup y := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simpa [mask, lookup] using ih
      | some z => by_cases hx : x = z <;> by_cases hy : y = z <;>
        simp_all [mask, lookup]

@[simp] theorem lookup_normalize [DecidableEq ν] (Γ : Ctx ν τ) (x : ν) :
    (normalize Γ).lookup x = Γ.lookup x := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simpa [normalize, lookup] using ih
      | some y =>
          by_cases h : x = y
          · subst x
            simp [normalize, lookup]
          · simp [normalize, lookup, h, lookup_mask_of_ne h, ih]

/-- Contexts in which each visible name occurs at most once. -/
inductive ShadowFree [DecidableEq ν] : Ctx ν τ → Prop where
  | nil : ShadowFree .nil
  | snoc_none {Γ : Ctx ν τ} {A : τ} : ShadowFree Γ → ShadowFree (.snoc Γ none A)
  | snoc_some {Γ : Ctx ν τ} {x : ν} {A : τ} :
      ShadowFree Γ → Γ.lookup x = none → ShadowFree (.snoc Γ (some x) A)

theorem ShadowFree.mask [DecidableEq ν] {Γ : Ctx ν τ} (hΓ : ShadowFree Γ) (z : ν) :
    ShadowFree (mask z Γ) := by
  induction hΓ with
  | nil => exact .nil
  | snoc_none _ ih => exact .snoc_none ih
  | @snoc_some Γ x A _ hx ih =>
      by_cases hzx : z = x
      · rw [Ctx.mask, ite_eq_left hzx]
        exact ShadowFree.snoc_none ih
      · rw [Ctx.mask, ite_eq_right hzx]
        exact ShadowFree.snoc_some ih (lookup_mask_of_ne (Ne.symm hzx) Γ ▸ hx)

theorem shadowFree_normalize [DecidableEq ν] (Γ : Ctx ν τ) : ShadowFree (normalize Γ) := by
  induction Γ with
  | nil => exact .nil
  | snoc Γ n A ih =>
      cases n with
      | none => exact .snoc_none ih
      | some x => exact .snoc_some (ih.mask x) (lookup_mask_self x _)

theorem mask_eq_self_of_lookup_eq_none [DecidableEq ν] {Γ : Ctx ν τ} {x : ν}
    (h : Γ.lookup x = none) : mask x Γ = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simp [mask, ih h]
      | some y =>
          by_cases hxy : x = y
          · simp [lookup, hxy] at h
          · simp [mask, hxy, ih (by simpa [lookup, hxy] using h)]

theorem ShadowFree.normalize_eq [DecidableEq ν] {Γ : Ctx ν τ} (hΓ : ShadowFree Γ) :
    normalize Γ = Γ := by
  induction hΓ with
  | nil => rfl
  | snoc_none _ ih => simp [normalize, ih]
  | @snoc_some Γ x A _ hx ih => simp [normalize, ih, mask_eq_self_of_lookup_eq_none hx]

@[simp] theorem normalize_idem [DecidableEq ν] (Γ : Ctx ν τ) :
    normalize (normalize Γ) = normalize Γ :=
  (shadowFree_normalize Γ).normalize_eq

theorem normalize_eq_self_iff [DecidableEq ν] {Γ : Ctx ν τ} :
    normalize Γ = Γ ↔ ShadowFree Γ := by
  constructor
  · intro h
    rw [← h]
    exact shadowFree_normalize Γ
  · exact ShadowFree.normalize_eq

/-- Named slots in oldest-to-newest order, retaining repeated names and skipping
anonymous slots. -/
def names : Ctx ν τ → List ν
  | .nil => []
  | .snoc Γ none _ => Γ.names
  | .snoc Γ (some x) _ => Γ.names ++ [x]

/-- Names of the latest bindings, in their context order. -/
def uniqueNames [DecidableEq ν] (Γ : Ctx ν τ) : List ν := Γ.names.dedup

/-- The finite set of names occurring in the context. -/
def vars [DecidableEq ν] (Γ : Ctx ν τ) : Finset ν := Γ.names.toFinset

@[simp] theorem names_nil : (.nil : Ctx ν τ).names = [] := rfl

@[simp] theorem names_snoc_none (Γ : Ctx ν τ) (A : τ) :
    (snoc Γ none A).names = Γ.names := rfl

@[simp] theorem names_snoc_some (Γ : Ctx ν τ) (x : ν) (A : τ) :
    (snoc Γ (some x) A).names = Γ.names ++ [x] := rfl

theorem names_length_le (Γ : Ctx ν τ) : Γ.names.length ≤ Γ.length := by
  induction Γ with
  | nil => exact Nat.le_refl 0
  | snoc Γ name A ih =>
      cases name with
      | none => exact Nat.le_succ_of_le ih
      | some x => simpa [names, length] using Nat.succ_le_succ ih

variable [DecidableEq ν]

theorem names_toFinset (Γ : Ctx ν τ) : Γ.names.toFinset = Γ.vars := rfl

@[simp] theorem uniqueNames_toFinset (Γ : Ctx ν τ) : Γ.uniqueNames.toFinset = Γ.vars := by
  exact List.toFinset_dedup

@[simp] theorem mem_vars {Γ : Ctx ν τ} {x : ν} : x ∈ Γ.vars ↔ x ∈ Γ.names :=
  List.mem_toFinset

@[simp] theorem mem_uniqueNames {Γ : Ctx ν τ} {x : ν} :
    x ∈ Γ.uniqueNames ↔ x ∈ Γ.names := List.mem_dedup

@[simp] theorem uniqueNames_nodup (Γ : Ctx ν τ) : Γ.uniqueNames.Nodup :=
  List.nodup_dedup _

theorem uniqueNames_sublist (Γ : Ctx ν τ) : List.Sublist Γ.uniqueNames Γ.names :=
  List.dedup_sublist _

theorem uniqueNames_length (Γ : Ctx ν τ) : Γ.uniqueNames.length = Γ.vars.card :=
  (List.card_toFinset Γ.names).symm

theorem vars_card_le (Γ : Ctx ν τ) : Γ.vars.card ≤ Γ.length :=
  (List.toFinset_card_le Γ.names).trans Γ.names_length_le

@[simp] theorem vars_nil : (.nil : Ctx ν τ).vars = ∅ := rfl

@[simp] theorem vars_snoc_none (Γ : Ctx ν τ) (A : τ) :
    (snoc Γ none A).vars = Γ.vars := rfl

@[simp] theorem vars_snoc_some (Γ : Ctx ν τ) (x : ν) (A : τ) :
    (snoc Γ (some x) A).vars = insert x Γ.vars := by
  ext y
  simp [or_comm]

/-- A name occurs exactly when its newest binding can be looked up. -/
theorem mem_names_iff_lookup {Γ : Ctx ν τ} {x : ν} :
    x ∈ Γ.names ↔ Γ.lookup x ≠ none := by
  induction Γ with
  | nil => simp [lookup]
  | snoc Γ name A ih =>
      cases name with
      | none => exact ih
      | some y => by_cases h : x = y <;> simp [lookup, h, ih]

theorem mem_vars_iff_lookup {Γ : Ctx ν τ} {x : ν} :
    x ∈ Γ.vars ↔ Γ.lookup x ≠ none := mem_vars.trans mem_names_iff_lookup

theorem mem_uniqueNames_iff_lookup {Γ : Ctx ν τ} {x : ν} :
    x ∈ Γ.uniqueNames ↔ Γ.lookup x ≠ none := mem_uniqueNames.trans mem_names_iff_lookup

theorem mem_vars_iff_exists {Γ : Ctx ν τ} {x : ν} :
    x ∈ Γ.vars ↔ ∃ A, Γ.lookup x = some A :=
  mem_vars_iff_lookup.trans Option.ne_none_iff_exists'

theorem lookup_eq_none_iff {Γ : Ctx ν τ} {x : ν} :
    Γ.lookup x = none ↔ x ∉ Γ.names := by
  simp [mem_names_iff_lookup]

@[simp] theorem names_mask (Γ : Ctx ν τ) (x : ν) :
    (Γ.mask x).names = Γ.names.filter (fun y => decide (x ≠ y)) := by
  induction Γ with
  | nil => rfl
  | snoc Γ name A ih =>
      cases name with
      | none => exact ih
      | some y => by_cases h : x = y <;> simp_all [mask, names]

@[simp] theorem vars_mask (Γ : Ctx ν τ) (x : ν) :
    (Γ.mask x).vars = Γ.vars.erase x := by
  ext y
  simp [and_comm, ne_comm]

@[simp] theorem vars_normalize (Γ : Ctx ν τ) : Γ.normalize.vars = Γ.vars := by
  ext x
  simp only [mem_vars_iff_lookup, lookup_normalize]

private theorem dedup_snoc (xs : List ν) (x : ν) :
    (xs ++ [x]).dedup = xs.dedup.filter (fun y => decide (x ≠ y)) ++ [x] := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      by_cases hxy : x = y
      · subst y
        by_cases hx : x ∈ ys <;> simp [hx, ih]
      · by_cases hy : y ∈ ys <;> simp [hy, ih, Ne.symm hxy, hxy]

/-- Removing shadowed bindings produces precisely the duplicate-free name list. -/
@[simp] theorem names_normalize (Γ : Ctx ν τ) : Γ.normalize.names = Γ.uniqueNames := by
  change Γ.normalize.names = Γ.names.dedup
  induction Γ with
  | nil => rfl
  | snoc Γ name A ih =>
      cases name with
      | none => exact ih
      | some x => simp only [normalize, names, names_mask, ih, dedup_snoc]

@[simp] theorem uniqueNames_normalize (Γ : Ctx ν τ) :
    Γ.normalize.uniqueNames = Γ.uniqueNames := by
  simp [uniqueNames, names_normalize]

theorem shadowFree_iff_names_nodup (Γ : Ctx ν τ) : Γ.ShadowFree ↔ Γ.names.Nodup := by
  induction Γ with
  | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
  | snoc Γ name A ih =>
      cases name with
      | none =>
          constructor
          · intro h; cases h with | snoc_none h => exact ih.mp h
          · intro h; exact .snoc_none (ih.mpr h)
      | some x =>
          have hn : (Γ.names ++ [x]).Nodup ↔ Γ.names.Nodup ∧ x ∉ Γ.names := by
            simp [List.nodup_append, List.forall_mem_ne']
          rw [names, hn]
          constructor
          · intro h
            cases h with
            | snoc_some h hx => exact ⟨ih.mp h, lookup_eq_none_iff.mp hx⟩
          · rintro ⟨h, hx⟩
            exact .snoc_some (ih.mpr h) (lookup_eq_none_iff.mpr hx)

theorem ShadowFree.uniqueNames_eq {Γ : Ctx ν τ} (h : Γ.ShadowFree) :
    Γ.uniqueNames = Γ.names := (shadowFree_iff_names_nodup Γ).mp h |>.dedup

end Ctx

end Silmaril.Isotope
