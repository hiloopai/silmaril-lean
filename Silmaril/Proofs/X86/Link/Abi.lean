module

public import Silmaril.X86.Link.Abi.Defs

/-! # Soundness of the link-time ABI check -/

@[expose] public section

namespace Silmaril.Proofs.X86.Link.Abi

open Silmaril.X86.Link Silmaril.X86.Link.Abi

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link

variable {Tag : Type} [DecidableEq Tag]

omit [DecidableEq Tag] in
theorem tags_mem {names : List NameBytes} {entries : List (NameBytes × Tag)}
    (h : tags names entries = true) {name : NameBytes} (hn : name ∈ names) :
    ∃ tag, (name, tag) ∈ entries := by
  simp only [tags, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hall, -⟩, -⟩ := h
  obtain ⟨⟨name', tag⟩, hmem, rfl⟩ := hall name hn
  exact ⟨tag, hmem⟩

omit [DecidableEq Tag] in
theorem mem_candidates_export {policy : Policy Tag} {ifaces : List (Interface Tag)}
    {iface : Interface Tag} (hi : iface ∈ ifaces) {name : NameBytes} {tag : Tag}
    (he : (name, tag) ∈ iface.exports) : tag ∈ candidates policy ifaces name := by
  simp only [candidates, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    beq_iff_eq]
  exact Or.inl ⟨iface, hi, (name, tag), ⟨he, rfl⟩, rfl⟩

omit [DecidableEq Tag] in
theorem mem_candidates_external {policy : Policy Tag} {ifaces : List (Interface Tag)}
    {name : NameBytes} {tag : Tag} (he : (name, tag) ∈ policy.externals) :
    tag ∈ candidates policy ifaces name := by
  simp only [candidates, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
  exact Or.inr ⟨(name, tag), ⟨he, rfl⟩, rfl⟩

theorem annotates_of_check {policy : Policy Tag} {objects : List ObjectFile}
    {ifaces : List (Interface Tag)} (h : checkAbi policy objects ifaces = true) {i : Nat}
    {object : ObjectFile} {iface : Interface Tag} (ho : objects[i]? = some object)
    (hi : ifaces[i]? = some iface) : iface.annotates object = true := by
  simp only [checkAbi, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨-, hzip⟩, -⟩ := h
  have hmem : (object, iface) ∈ objects.zip ifaces :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨ho, hi⟩)
  exact hzip _ hmem

/-- **`checkAbi` is sound**: every cross-object binding the static linker can
make (an undefined global to a strong definition of the same name in any
object, or to an absolute symbol) is between tags the policy accepts. -/
theorem checkAbi_sound {policy : Policy Tag} {objects : List ObjectFile}
    {ifaces : List (Interface Tag)} (h : checkAbi policy objects ifaces = true) :
    AbiSound policy objects ifaces := by
  intro i object iface ho hi name hn
  have hann := annotates_of_check h ho hi
  simp only [Interface.annotates, Bool.and_eq_true] at hann
  obtain ⟨importTag, himport⟩ := tags_mem hann.2 hn
  have hok : importOk policy ifaces name importTag = true := by
    have h' := h
    simp only [checkAbi, Bool.and_eq_true, List.all_eq_true] at h'
    exact h'.2 iface (List.mem_of_getElem? hi) (name, importTag) himport
  simp only [importOk, List.all_eq_true] at hok
  refine ⟨importTag, himport, ?_, ?_⟩
  · intro j object' iface' ho' hi' hdef
    have hann' := annotates_of_check h ho' hi'
    simp only [Interface.annotates, Bool.and_eq_true] at hann'
    obtain ⟨exportTag, hexport⟩ := tags_mem hann'.1 hdef
    exact ⟨exportTag, hexport,
      hok _ (mem_candidates_export (List.mem_of_getElem? hi') hexport)⟩
  · intro exportTag hext
    exact hok _ (mem_candidates_external hext)

theorem linkAbi_some {accepts : Header → Bool} {relocate : Relocator} {policy : Policy Tag}
    {objects : List ObjectFile} {ifaces : List (Interface Tag)} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : linkAbi accepts relocate policy objects ifaces layout absolute = some out) :
    checkAbi policy objects ifaces = true ∧ externalsTag policy absolute = true ∧
      link accepts relocate objects layout absolute = some out := by
  unfold linkAbi at h
  by_cases hc : (checkAbi policy objects ifaces && externalsTag policy absolute) = true
  · simp only [hc, guard_true, Option.bind_eq_bind, Option.pure_def, Option.bind_some] at h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hc.1, hc.2, by simpa using h⟩
  · simp [hc] at h

omit [DecidableEq Tag] in
theorem externalsTag_mem {policy : Policy Tag} {absolute : AbsoluteSymbols}
    (h : externalsTag policy absolute = true) {entry : NameBytes × Nat} (he : entry ∈ absolute) :
    ∃ tag, (entry.1, tag) ∈ policy.externals := by
  simp only [externalsTag, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨name, tag⟩, hmem, rfl⟩ := h entry he
  exact ⟨tag, hmem⟩

/-- **ABI soundness of a successful tagged link**: `AbiSound` holds, and every
absolute symbol the linker may bind has a tag in `policy.externals` (which
`AbiSound` checks against every import of that name). -/
theorem linkAbi_sound {accepts : Header → Bool} {relocate : Relocator} {policy : Policy Tag}
    {objects : List ObjectFile} {ifaces : List (Interface Tag)} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : linkAbi accepts relocate policy objects ifaces layout absolute = some out) :
    AbiSound policy objects ifaces ∧ ∀ entry ∈ absolute, ∃ tag, (entry.1, tag) ∈ policy.externals := by
  obtain ⟨hc, he, -⟩ := linkAbi_some h
  exact ⟨checkAbi_sound hc, fun _ hm => externalsTag_mem he hm⟩

/-- ABI-tagged links are exactly the imported links that pass the ABI checks. -/
theorem linkAbi_eq {accepts : Header → Bool} {relocate : Relocator} {policy : Policy Tag}
    {objects : List ObjectFile} {ifaces : List (Interface Tag)} {layout : Layout}
    {absolute : AbsoluteSymbols} (h : checkAbi policy objects ifaces = true)
    (he : externalsTag policy absolute = true) :
    linkAbi accepts relocate policy objects ifaces layout absolute =
      link accepts relocate objects layout absolute := by
  simp [linkAbi, h, he]

/-- A failed ABI check rejects the link whatever the layout. -/
theorem linkAbi_rejects {accepts : Header → Bool} {relocate : Relocator} {policy : Policy Tag}
    {objects : List ObjectFile} {ifaces : List (Interface Tag)} {layout : Layout}
    {absolute : AbsoluteSymbols} (h : checkAbi policy objects ifaces = false) :
    linkAbi accepts relocate policy objects ifaces layout absolute = none := by
  simp [linkAbi, h]

/-- An absolute symbol without an external tag rejects the link. -/
theorem linkAbi_rejects_untagged {accepts : Header → Bool} {relocate : Relocator}
    {policy : Policy Tag} {objects : List ObjectFile} {ifaces : List (Interface Tag)}
    {layout : Layout} {absolute : AbsoluteSymbols} (h : externalsTag policy absolute = false) :
    linkAbi accepts relocate policy objects ifaces layout absolute = none := by
  simp [linkAbi, h]

end Silmaril.Proofs.X86.Link.Abi
