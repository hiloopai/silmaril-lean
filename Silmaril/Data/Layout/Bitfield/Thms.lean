module

public import Silmaril.Data.Layout.Bitfield.Defs
public import Silmaril.Data.Layout.Thms
import Silmaril.Proofs.Data.Layout.Bitfield

/-! # Bit-field layouts are well formed

PROVED (standard axioms), proofs in `Silmaril.Proofs.Data.Layout.Bitfield`:

* `bitStruct_wf`: under either policy, a struct's slots are pairwise disjoint, in increasing
  order, and inside the record;
* `bitUnion_wf`: a union's slots start at bit 0 and lie inside the record;
* `bitLayout_wf`: the same for a declaration. These are **structural** facts about the placement
  function; they say nothing about what a compiler does (agreement with gcc and clang's MSVC
  emulation on 25 measured aggregates is `Examples.cases_agree`, a finite comparison);
* `msX64_wf`: the Microsoft x64 data model (LLP64) is well formed (a data model, not a calling
  convention);
* `bitfieldLayout`: **`Task.bitfieldLayout` holds** (`Silmaril.Data.Layout.Thms`), with
  `bitfieldPlace` and GCC's x86-64 placements of its two examples.
-/

@[expose] public section

namespace Silmaril.Data.Layout

theorem bitStruct_wf {pol : BitPolicy} {ms : List BMember} {ss : List BitSlot} {sh : Shape}
    (h : bitStruct pol ms = .ok (ss, sh)) :
    (ss.Pairwise fun a b => a.off + a.width ≤ b.off) ∧ ∀ s ∈ ss, s.off + s.width ≤ 8 * sh.size :=
  Silmaril.Proofs.Data.Layout.Bitfield.bitStruct_wf h

theorem bitUnion_wf {pol : BitPolicy} {ms : List BMember} {ss : List BitSlot} {sh : Shape}
    (h : bitUnion pol ms = .ok (ss, sh)) : ∀ s ∈ ss, s.off = 0 ∧ s.width ≤ 8 * sh.size :=
  Silmaril.Proofs.Data.Layout.Bitfield.bitUnion_wf h

/-- **Every slot of a declaration's layout lies inside the record**, and a struct's slots are
pairwise disjoint. -/
theorem bitLayout_wf {pol : BitPolicy} {dm : DataModel} {env : Env} {d : Decl}
    {ss : List BitSlot} {sh : Shape} (h : bitLayout pol dm env d = .ok (ss, sh)) :
    (∀ s ∈ ss, s.off + s.width ≤ 8 * sh.size) ∧
      (d.kind = .struct → ss.Pairwise fun a b => a.off + a.width ≤ b.off) := by
  unfold bitLayout at h
  split at h
  · cases h
  cases hk : d.kind <;> simp only [hk, bitKind] at h
  · exact ⟨(bitStruct_wf h).2, fun _ => (bitStruct_wf h).1⟩
  · exact ⟨fun s hs => by have := bitUnion_wf h s hs; omega, fun h' => nomatch h'⟩

/-- The Microsoft x64 data model is well formed. -/
theorem msX64_wf : msX64.WF := Silmaril.Proofs.Data.Layout.Bitfield.msX64_wf

/-- **`Task.bitfieldLayout` holds.** -/
theorem bitfieldLayout : Task.bitfieldLayout := by
  refine ⟨bitfieldPlace, ?_, by decide, by decide⟩
  intro dm env fs r h
  unfold bitfieldPlace at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i ss sh hs
  cases h
  obtain ⟨h1, h2⟩ := bitStruct_wf hs
  refine ⟨?_, ?_⟩
  · exact List.pairwise_map.mpr h1
  · intro x hx
    obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hx
    exact h2 s hs'

end Silmaril.Data.Layout
