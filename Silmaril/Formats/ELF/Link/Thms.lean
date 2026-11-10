module

public import Silmaril.Formats.ELF.Link.Defs
import Silmaril.Proofs.Formats.ELF.Link

/-! # Static ELF section linking: theorems

* `applyPatch_size`, `applyPatch_get`: one patch keeps the section size and overwrites
  exactly the offsets it covers;
* `foldl_patches_get`, `foldl_patches_get_mem`, `foldl_patches_size`: pairwise-disjoint
  patches, applied in order, leave uncovered bytes alone and leave each patch's own bytes in
  place;
* `linkSection_some`, `link_some`, `addressAt_of_mem`, `resolveRelocations_mem`: what a
  successful `linkSection`, `link` or `resolveRelocations` exposes;
* `drop_eq_of_getElem?`, `mapM_some_mem`, `mapM_some_mem'`: list facts used by clients.

Architecture-specific relocation profiles supply the `Relocator`; the x86-64 one is
`Silmaril.X86.Linking`.
-/

@[expose] public section

namespace Silmaril.Formats.ELF.Link

open Silmaril.Formats.ELF

theorem applyPatch_size {before after : Bytes} {patch : Patch}
    (applied : applyPatch before patch = some after) : after.size = before.size :=
  Proofs.Formats.ELF.Link.applyPatch_size applied

/-- One patch overwrites exactly the offsets it covers. -/
theorem applyPatch_get {d d' : Bytes} {p : Patch} (h : applyPatch d p = some d') (i : Nat) :
    d'[i]? = if Covers p i then p.bytes[i - p.offset]? else d[i]? :=
  Proofs.Formats.ELF.Link.applyPatch_get h i

/-- Bytes covered by no patch keep their section value. -/
theorem foldl_patches_get {patches : List Patch} {d d' : Bytes}
    (hpw : patches.Pairwise Patch.Disjoint) (h : patches.foldlM applyPatch d = some d') (i : Nat)
    (hn : ∀ q ∈ patches, ¬ Covers q i) : d'[i]? = d[i]? :=
  Proofs.Formats.ELF.Link.foldl_patches_get hpw h i hn

/-- Each patch's bytes survive the other (disjoint) patches. -/
theorem foldl_patches_get_mem {patches : List Patch} {d d' : Bytes}
    (hpw : patches.Pairwise Patch.Disjoint) (h : patches.foldlM applyPatch d = some d')
    (q : Patch) (hq : q ∈ patches) (i : Nat) (hc : Covers q i) :
    d'[i]? = q.bytes[i - q.offset]? :=
  Proofs.Formats.ELF.Link.foldl_patches_get_mem hpw h q hq i hc

theorem foldl_patches_size {patches : List Patch} {d d' : Bytes}
    (h : patches.foldlM applyPatch d = some d') : d'.size = d.size :=
  Proofs.Formats.ELF.Link.foldl_patches_size h

/-- Reassemble a suffix from pointwise facts about its first bytes. -/
theorem drop_eq_of_getElem? {α} {l pre : List α} {o : Nat}
    (h : ∀ j < pre.length, l[o + j]? = pre[j]?) :
    l.drop o = pre ++ l.drop (o + pre.length) :=
  Proofs.Formats.ELF.Link.drop_eq_of_getElem? h

theorem mapM_some_mem {α β} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') (a : α) (ha : a ∈ l) : ∃ b ∈ l', f a = some b :=
  Proofs.Formats.ELF.Link.mapM_some_mem h a ha

theorem mapM_some_mem' {α β} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') (b : β) (hb : b ∈ l') : ∃ a ∈ l, f a = some b :=
  Proofs.Formats.ELF.Link.mapM_some_mem' h b hb

/-- A successful section link applied the patches of exactly the relocations
aimed at that section, disjointly, to the input section bytes. -/
theorem linkSection_some {objects : List ObjectFile} {rels : List ResolvedRelocation}
    {relocate : Relocator} {placement : Placement} {out : LinkedSection}
    (h : linkSection objects rels relocate placement = some out) :
    ∃ part patches, sectionAt objects placement.key = some part ∧
      (rels.filter (fun r => r.key == placement.key)).mapM (fun r => do
        let patch ← relocate rels r part.data
        guard (patch.offset = r.offset ∧ 0 < patch.bytes.size)
        pure patch) = some patches ∧
      patches.Pairwise Patch.Disjoint ∧ patches.foldlM applyPatch part.data = some out.data ∧
      out.address = placement.address ∧ out.key = placement.key :=
  Proofs.Formats.ELF.Link.linkSection_some h

/-- The structure exposed by a successful `link`. -/
theorem link_some {accepts : Header → Bool} {relocate : Relocator} {objects : List ObjectFile}
    {layout : Layout} {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) :
    (layout.map Placement.key).Nodup ∧
    ∃ rels, resolveRelocations objects layout absolute = some rels ∧
      layout.mapM (linkSection objects rels relocate) = some out ∧
      out.Pairwise LinkedSection.Disjoint :=
  Proofs.Formats.ELF.Link.link_some h

theorem addressAt_of_mem {layout : Layout} {placement : Placement} (h : placement ∈ layout)
    (hnd : (layout.map Placement.key).Nodup) :
    addressAt layout placement.key = some placement.address :=
  Proofs.Formats.ELF.Link.addressAt_of_mem h hnd

/-- A resolved relocation's place is its target section's base plus its offset. -/
theorem resolveRelocations_mem {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {rels : List ResolvedRelocation}
    (h : resolveRelocations objects layout absolute = some rels) {r : ResolvedRelocation}
    (hr : r ∈ rels) :
    ∃ base, addressAt layout r.key = some base ∧ r.place = base + r.offset :=
  Proofs.Formats.ELF.Link.resolveRelocations_mem h hr

end Silmaril.Formats.ELF.Link
