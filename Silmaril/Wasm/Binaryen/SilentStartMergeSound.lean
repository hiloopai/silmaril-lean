module

public import Silmaril.Wasm.Link.SilentStartSound
public import Silmaril.Wasm.Binaryen.MergeProfileEquivalence

@[expose] public section

/-! # Original-program semantics for checked silent-start merging

The erased modules are intermediate inputs to the existing checked merger.
This bridge restores each original start in separate instantiation, retaining
its exact final store and named instances. It proves target-to-original
behavioral inclusion at every numerical profile. It does not claim the
opposite inclusion or silently identify the originals with the intermediate
modules.
-/

namespace Silmaril.Wasm.Binaryen.SilentStartMerge

open Execution.Core Validation Numerics

variable {H : Type} {P : Profile}

/-- Pointwise provenance of a named original and its prepared linker input.
The original is validated before the checker erases its start. -/
def Prepared (source target : String × Module) : Prop :=
  source.1 = target.1 ∧ Link.SilentStart.erase? source.2 = some target.2 ∧ ModuleValid source.2

private theorem original_sections {source target : Module}
    (accepted : Link.SilentStart.erase? source = some target)
    (profile : Link.GC.inProfile target = true) : source.data = [] ∧ source.elems = [] := by
  have output := Link.SilentStart.erase?_output accepted
  rw [output] at profile
  simp only [Link.GC.inProfile, Bool.and_eq_true, List.isEmpty_iff,
    Option.isNone_iff_eq_none] at profile
  exact ⟨profile.1.1.1.2, profile.1.1.2⟩

/-- Restore every original start in the actual in-order instantiation run.
The store and all named module instances are unchanged. -/
theorem separateReady_restore {source prepared : List (String × Module)}
    (provenance : List.Forall₂ Prepared source prepared)
    (profiles : ∀ p ∈ prepared, Link.GC.inProfile p.2 = true)
    {s t : Store H} {initial final : List (String × ModuleInst)}
    (ready : SeparateReady P SingleThreaded.Det.noHost s initial prepared t final) :
    SeparateReady P SingleThreaded.Det.noHost s initial source t final := by
  induction provenance generalizing s initial with
  | nil => exact ready
  | @cons source target sources targets head rest ih =>
    rcases source with ⟨sourceName, sourceModule⟩
    rcases target with ⟨targetName, targetModule⟩
    obtain ⟨nameEq, accepted, valid⟩ := head
    cases nameEq
    obtain ⟨noData, noElems⟩ := original_sections accepted
      (profiles (sourceName, targetModule) (by simp))
    have output := Link.SilentStart.erase?_output accepted
    have importsEq := congrArg (fun m : Module => m.imports) output
    change targetModule.imports = sourceModule.imports at importsEq
    cases ready with
    | cons imports headReady tailReady =>
      exact .cons (by simpa only [importsEq] using imports)
        (Link.SilentStart.ready_restore accepted valid noData noElems headReady)
        (ih (fun p hp => profiles p (by simp [hp])) tailReady)

/-- Every behavior after separately preparing the intermediate modules is
an actual behavior after separately preparing the original modules. -/
theorem program_beh_subset {source prepared : List (String × Module)}
    (provenance : List.Forall₂ Prepared source prepared)
    (profiles : ∀ p ∈ prepared, Link.GC.inProfile p.2 = true)
    (n x : String) (vs : List Val) :
    Program.beh P (SingleThreaded.Det.noHost (H := H)) prepared n x vs ⊆
      Program.beh P (SingleThreaded.Det.noHost (H := H)) source n x vs := by
  rintro behavior ⟨s, instances, mi, address, ready, lookup, exported, observation⟩
  exact ⟨s, instances, mi, address, separateReady_restore provenance profiles ready,
    lookup, exported, observation⟩

/-- The existing executable merger, composed with checked silent-start
preparation, refines the original program at every numerical profile. The
export witness refers to the retained named intermediate interfaces. -/
theorem checkedMerge_refines_original {source prepared : List (String × Module)}
    {result : Module} (provenance : List.Forall₂ Prepared source prepared)
    (merged : checkedMerge? prepared = some result) (P : Profile)
    {n x : String} {vs : List Val}
    (exported : ∃ p ∈ prepared, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    (moduleEntryPoints P (SingleThreaded.Det.noHost (H := H)) closedEnv).beh result x vs ⊆
      Program.beh P (SingleThreaded.Det.noHost (H := H)) source n x vs := by
  rw [← checkedMerge?_sound_profile merged P exported]
  obtain ⟨_, _, _, profiles, _⟩ := checkedMerge?_conditions merged
  exact program_beh_subset provenance profiles n x vs

end Silmaril.Wasm.Binaryen.SilentStartMerge
