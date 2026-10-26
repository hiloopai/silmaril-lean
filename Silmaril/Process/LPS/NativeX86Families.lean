module

public import Silmaril.Process.LPS.NativeX86

/-! # Installing explicitly reviewed native syscall families

Family translations export native `SpecArm` lists alongside their reference
lists. Native specifications with a different structure layout must receive the
original x86 input, rather than being passed through `rekey`. This opt-in
builder installs those specifications in the existing ninety slots. It preserves
the slot's number and name and rejects duplicate or unknown override keys.

The checks certify table wiring only. Supplying a family here is an explicit ABI
review decision, not a proof of correspondence with Linux. Architecture-only
extensions (including legacy aliases) are composed separately, outside the
reference denominator. Clients must also select a matching refusal filter.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86

/-- Replace only semantics and status, after matching both native number and name.
No input renumbering or register permutation is applied to a native family. -/
def installArm (overrides : List SpecArm) (source : SpecArm) : SpecArm :=
  match lookupArm overrides source.no with
  | some native =>
    if native.name = source.name then
      { source with status := native.status, spec := native.spec }
    else source
  | none => source

def tableWithFamilies (reference overrides : List SpecArm) : List SpecArm :=
  (table reference).map (installArm overrides)

/-- Every supplied key is a reference-family native key, with no duplicate
numbers. This does not inspect or certify the supplied specification. -/
def FamiliesWf (overrides : List SpecArm) : Prop :=
  (armNumbers overrides).Nodup ∧
    ∀ native ∈ overrides,
      (native.no, native.name) ∈ numbers.map (fun row => (row.nativeNo, row.name))

instance (overrides : List SpecArm) : Decidable (FamiliesWf overrides) := by
  unfold FamiliesWf
  infer_instance

/-- Every override must also have an actual slot in the supplied reference
table. A catalogue-valid family cannot silently disappear when using a subset. -/
def FamiliesWfFor (reference overrides : List SpecArm) : Prop :=
  FamiliesWf overrides ∧ ∀ native ∈ overrides,
    ∃ source ∈ table reference, source.no = native.no ∧ source.name = native.name

instance (reference overrides : List SpecArm) : Decidable (FamiliesWfFor reference overrides) := by
  unfold FamiliesWfFor
  infer_instance

def checkedTableWithFamilies (reference overrides : List SpecArm) : Option (List SpecArm) :=
  if FamiliesWfFor reference overrides then some (tableWithFamilies reference overrides) else none

@[simp] theorem installArm_number (overrides : List SpecArm) (source : SpecArm) :
    (installArm overrides source).no = source.no := by
  unfold installArm
  split <;> first | rfl | split <;> rfl

@[simp] theorem installArm_name (overrides : List SpecArm) (source : SpecArm) :
    (installArm overrides source).name = source.name := by
  unfold installArm
  split <;> first | rfl | split <;> rfl

theorem tableWithFamilies_surface (reference overrides : List SpecArm) :
    (tableWithFamilies reference overrides).map (fun a => (a.no, a.name)) =
      (table reference).map (fun a => (a.no, a.name)) := by
  simp [tableWithFamilies, List.map_map, Function.comp_def]

theorem tableWithFamilies_numbers (reference overrides : List SpecArm) :
    armNumbers (tableWithFamilies reference overrides) = armNumbers (table reference) := by
  simp [armNumbers, tableWithFamilies, List.map_map, Function.comp_def]

theorem tableWithFamilies_length (reference overrides : List SpecArm) :
    (tableWithFamilies reference overrides).length = (table reference).length := by
  simp [tableWithFamilies]

theorem nativeFamilies_length (overrides : List SpecArm) :
    (tableWithFamilies specTable overrides).length = 90 := by
  rw [tableWithFamilies_length, table_length]

theorem nativeFamilies_numbers_nodup (overrides : List SpecArm) :
    (armNumbers (tableWithFamilies specTable overrides)).Nodup := by
  rw [tableWithFamilies_numbers]
  exact table_numbers_nodup

/-- A successfully checked table has exactly the original native surface. -/
theorem checkedTableWithFamilies_surface (reference overrides result : List SpecArm)
    (checked : checkedTableWithFamilies reference overrides = some result) :
    result.map (fun a => (a.no, a.name)) =
      (table reference).map (fun a => (a.no, a.name)) := by
  unfold checkedTableWithFamilies at checked
  split at checked
  · cases Option.some.inj checked
    exact tableWithFamilies_surface reference overrides
  · cases checked

/-- In particular, a native structure-aware spec sees native sysno and arguments.
Only the caller's supplied spec, not the reference arm, determines its outcomes. -/
theorem installArm_spec (overrides : List SpecArm) (source native : SpecArm)
    (found : lookupArm overrides source.no = some native) (named : native.name = source.name)
    (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect) :
    (installArm overrides source).spec input model outcome ↔
      native.spec input model outcome := by
  simp [installArm, found, named]

theorem installArm_wrong_name (overrides : List SpecArm) (source native : SpecArm)
    (found : lookupArm overrides source.no = some native) (named : native.name ≠ source.name) :
    installArm overrides source = source := by
  simp [installArm, found, named]

theorem installArm_absent (overrides : List SpecArm) (source : SpecArm)
    (absent : lookupArm overrides source.no = none) : installArm overrides source = source := by
  simp [installArm, absent]

end Silmaril.Process.LPS.NativeX86
