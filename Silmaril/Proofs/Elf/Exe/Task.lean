module

public import Silmaril.Proofs.Elf.Exe.RoLoaded

/-! # `Task.roLoaded_of_exeLoaded` from the reader bridges (proofs for `Silmaril.Elf.Exe.Thms`)

The API's `NoTextRel A` (and `NoLazyGotRo A` under lazy binding) gives the loader-level
`NoTextRelD F lazy` once the loader's header and relocation reads agree with the AST
(`Task.dynInfo_rd`, `Task.relas_rd`). -/

@[expose] public section

namespace Silmaril.Elf.Exe

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Bridge

/-- The loader's `DT_` lookup is the AST's. -/
theorem dynInfoOf_tag (A : File) (t : Nat) : (dynInfoOf A).tag t = A.dynTag t := by
  simp only [Elf.DynInfo.tag, dynInfoOf, File.dynTag, List.find?_map]
  cases h : A.dynamic.find? (·.tag == t) with
  | none => simp [Function.comp_def, h]
  | some e => simp [Function.comp_def, h]

/-- `avoidsRo` on the loader's view of the AST's program headers. -/
theorem avoidsRo_of {A : File} {p : Nat}
    (h : ∀ ph ∈ A.loads, ph.flags / 2 % 2 = 0 → p + 8 ≤ ph.virtualAddress ∨ ph.virtualAddress + ph.memorySize ≤ p) :
    avoidsRo (dynInfoOf A).phs p = true := by
  simp only [avoidsRo, dynInfoOf, List.all_map, List.all_eq_true, Function.comp_apply]
  intro ph hph
  simp only [Silmaril.Elf.Link.ElfBind.isLoad, Silmaril.Elf.Link.ElfBind.isRo, phdrToDyn,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp, beq_iff_eq]
  by_cases hk : ph.kind = 1
  · by_cases hr : ph.flags / 2 % 2 = 0
    · right
      exact decide_eq_true <| h ph (List.mem_filter.2 ⟨hph, by simp [PT_LOAD, hk]⟩) hr
    · left; intro _; simpa using hr
  · left; intro hk'; exact absurd hk' hk

/-- **`NoTextRelD` from the API's `NoTextRel`**, through the reader bridges. -/
theorem noTextRelD_of_api (hd : Task.dynInfo_rd) (hr : Task.relas_rd) {F : Blob} {A : File} {lazy : Bool}
    (hA : Parses F A) (hx : A.header.machine = 62) (hdyn : A.isDynamic) (hc : A.DynConsistent)
    (hnt : NoTextRel A) (hgot : lazy = true → NoLazyGotRo A) : NoTextRelD F lazy := by
  intro i hi ps hps p hp
  have hi' : finfo F = some (dynInfoOf A) := hd F A hA hx hdyn
  rw [hi, Option.some.injEq] at hi'
  subst hi'
  unfold slotPositions at hps
  cases hrd : frun F (Elf.relas (dynInfoOf A)) with
  | none => rw [hrd] at hps; cases hps
  | some aj =>
    obtain ⟨a, j⟩ := aj
    rw [hrd] at hps
    dsimp only at hps
    have hk := hr F A a j hA hx hc hrd
    -- a relocation offset
    have hrel : ∀ q ∈ a.map (·.off) ++ j.map (·.off), avoidsRo (dynInfoOf A).phs q = true := by
      intro q hq
      have hq' : q ∈ (a ++ j).map (·.off) := by simpa [List.map_append] using hq
      obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hq'
      have hm : (r.off, r.kind, r.sym, some r.addend) ∈ (A.relocs .dynamic).map relocKey := by
        rw [hk]; exact List.mem_map.2 ⟨r, hr', rfl⟩
      obtain ⟨r', hr'', he⟩ := List.mem_map.1 hm
      simp only [relocKey, Prod.mk.injEq] at he
      rw [← he.1]
      exact avoidsRo_of (hnt r' hr'')
    by_cases hl : lazy = true ∧ j ≠ []
    · simp only [hl, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hps
      cases ht : (dynInfoOf A).tag 3 with
      | none => rw [ht] at hps; cases hps
      | some g =>
        rw [ht] at hps
        simp only [Option.map_some, Option.some.injEq] at hps
        subst hps
        rcases List.mem_append.1 (List.append_assoc _ _ _ ▸ hp) with hp | hp
        · rw [dynInfoOf_tag] at ht
          exact avoidsRo_of fun ph hph hro => hgot hl.1 g ht p hp ph hph hro
        · exact hrel p hp
    · simp only [hl, ↓reduceIte, Option.map_some, Option.some.injEq] at hps
      subst hps
      simp only [List.nil_append] at hp
      exact hrel p hp

/-- **`Task.roLoaded_of_exeLoaded`, from the reader bridges.** -/
theorem roLoaded_task (hd : Task.dynInfo_rd) (hr : Task.relas_rd) : Task.roLoaded_of_exeLoaded :=
  fun _ _ _ _ _ _ _ _ _ hA hx hdyn hc hnt hgot hp hl =>
    roLoaded_of_exeLoaded hp (noTextRelD_of_api hd hr hA hx hdyn hc hnt hgot) hl

end Silmaril.Elf.Exe
