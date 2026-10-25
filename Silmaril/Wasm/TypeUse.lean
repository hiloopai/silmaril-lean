module

public import Silmaril.Wasm.Types
public import Mathlib.Data.List.Basic

/-! # Checked type uses

Explicit declarations are appended without deduplication. Inline signatures are
interned after those declarations have been collected, so existing type indices
remain stable. This resolves source references; it does not validate a signature.
-/

@[expose] public section
namespace Silmaril.Wasm

inductive BuildError where
  | indexOverflow (kind : IndexKind)
  | unknownType (index : TypeIdx)
  | typeMismatch (index : TypeIdx)
  | lateImport
  | duplicateExport (name : String)
  | unknownExport (kind : IndexKind) (index : Nat)
  | invalidStart (index : FuncIdx)
  deriving DecidableEq, Repr

/-- The `index` form optionally checks a repeated inline signature. -/
inductive TypeUse (Signature : Type) where
  | index (index : TypeIdx) (annotation : Option Signature := none)
  | inline (signature : Signature)
  deriving DecidableEq, Repr

namespace IndexSpace

variable {A : Type} {kind : IndexKind}

/-- Append to a declaration space, accounting for its imported prefix. -/
def append (kind : IndexKind) (offset : Nat) (xs : List A) (x : A) :
    Except BuildError (Idx kind × List A) :=
  match Idx.ofNat? (offset + xs.length) with
  | none => .error (.indexOverflow kind)
  | some i => .ok (i, xs ++ [x])

theorem append_eq_ok_iff (offset : Nat) (xs : List A) (x : A)
    (i : Idx kind) (ys : List A) :
    append kind offset xs x = .ok (i, ys) ↔
      i.toNat = offset + xs.length ∧ ys = xs ++ [x] := by
  unfold append
  split <;> rename_i h
  · constructor
    · simp
    · rintro ⟨hi, _⟩
      have := (Idx.ofNat?_eq_some_iff _ i).mpr hi.symm
      simp_all
  · constructor
    · intro e
      cases e
      exact ⟨((Idx.ofNat?_eq_some_iff _ _).mp h).symm, rfl⟩
    · rintro ⟨hi, rfl⟩
      have := (Idx.ofNat?_eq_some_iff _ i).mpr hi.symm
      simp_all

end IndexSpace

namespace TypeTable

variable {S : Type}

/-- Preserve every explicit type declaration, including duplicate signatures. -/
def append (types : List S) (signature : S) : Except BuildError (TypeIdx × List S) :=
  IndexSpace.append .type_ 0 types signature

/-- Use the first equal signature, or append a fresh declaration. -/
def intern [DecidableEq S] (types : List S) (signature : S) :
    Except BuildError (TypeIdx × List S) :=
  if signature ∈ types then
    match Idx.ofNat? (types.idxOf signature) with
    | none => .error (.indexOverflow .type_)
    | some i => .ok (i, types)
  else append types signature

theorem append_spec {types types' : List S} {signature : S} {i : TypeIdx}
    (h : append types signature = .ok (i, types')) :
    i.toNat = types.length ∧ types' = types ++ [signature] := by
  simpa [append] using (IndexSpace.append_eq_ok_iff 0 types signature i types').mp h

theorem append_lookup {types types' : List S} {signature : S} {i : TypeIdx}
    (h : append types signature = .ok (i, types')) :
    types'[i.toNat]? = some signature := by
  obtain ⟨hi, rfl⟩ := append_spec h
  simp [hi]

theorem intern_lookup [DecidableEq S] {types types' : List S} {signature : S} {i : TypeIdx}
    (h : intern types signature = .ok (i, types')) :
    types'[i.toNat]? = some signature := by
  unfold intern at h
  split at h
  · rename_i mem
    split at h <;> rename_i eq
    · contradiction
    · cases h
      rw [← (Idx.ofNat?_eq_some_iff _ _).mp eq]
      exact List.getElem?_idxOf mem
  · exact append_lookup h

/-- Interning never shifts an existing type declaration. -/
theorem intern_prefix [DecidableEq S] {types types' : List S} {signature : S} {i : TypeIdx}
    (h : intern types signature = .ok (i, types')) : types <+: types' := by
  unfold intern at h
  split at h
  · split at h
    · contradiction
    · cases h
      exact List.prefix_refl _
  · obtain ⟨_, rfl⟩ := append_spec h
    exact List.prefix_append _ _

end TypeTable

namespace TypeUse

variable {S : Type} [DecidableEq S]

def resolve (use : TypeUse S) (types : List S) : Except BuildError (TypeIdx × List S) :=
  match use with
  | .inline signature => TypeTable.intern types signature
  | .index i annotation =>
    match types[i.toNat]? with
    | none => .error (.unknownType i)
    | some signature =>
      if annotation.all (· = signature) then .ok (i, types)
      else .error (.typeMismatch i)

@[simp] theorem resolve_index {types : List S} {i : TypeIdx} {signature : S}
    (h : types[i.toNat]? = some signature) :
    resolve (.index i) types = .ok (i, types) := by simp [resolve, h]

@[simp] theorem resolve_annotated {types : List S} {i : TypeIdx} {signature : S}
    (h : types[i.toNat]? = some signature) :
    resolve (.index i (some signature)) types = .ok (i, types) := by simp [resolve, h]

/-- Successful resolution always produces a declared signature. -/
theorem resolve_exists {use : TypeUse S} {types types' : List S} {i : TypeIdx}
    (h : resolve use types = .ok (i, types')) : ∃ signature, types'[i.toNat]? = some signature := by
  cases use with
  | inline signature => exact ⟨signature, TypeTable.intern_lookup h⟩
  | index j annotation =>
    simp only [resolve] at h
    split at h
    · contradiction
    · rename_i signature lookup
      split at h
      · cases h
        exact ⟨signature, lookup⟩
      · contradiction

theorem resolve_prefix {use : TypeUse S} {types types' : List S} {i : TypeIdx}
    (h : resolve use types = .ok (i, types')) : types <+: types' := by
  cases use with
  | inline signature => exact TypeTable.intern_prefix h
  | index j annotation =>
    simp only [resolve] at h
    split at h
    · contradiction
    · split at h
      · cases h
        exact List.prefix_refl _
      · contradiction

end TypeUse
end Silmaril.Wasm
