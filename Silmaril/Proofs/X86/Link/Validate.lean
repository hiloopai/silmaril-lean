module

public import Silmaril.X86.Link.Validate.Defs
public import Silmaril.Proofs.X86.Link.Blob
public import Silmaril.Formats.ELF.Link.Thms

/-! # Soundness of the link validator

* `sectionIn_of_check`: the arithmetic check `sectionInN` against a parsed
  `PT_LOAD` header gives `SectionIn` for the image `ELFImage` loads;
* `validateN_sound`: an accepted blob link is `Validated`, a statement about
  `readObject`, `ELFImage.parse` and `Relocation.link` alone;
* `validate_sound`: the same for byte arrays.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Link.Validate

open Silmaril.X86.Link Silmaril.X86.Link.Validate

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link
open Silmaril.Process.LPS
open Silmaril.X86.Linking Silmaril.Proofs.X86.Link.Blob

theorem permissions_bits {f : Nat} (h : f < 8) :
    (ELFImage.permissions f).contains 'r' = (f / 4 % 2 == 1) ∧
      (ELFImage.permissions f).contains 'w' = (f / 2 % 2 == 1) ∧
      (ELFImage.permissions f).contains 'x' = (f % 2 == 1) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 := by omega
  all_goals simp [ELFImage.permissions]

theorem permsOk_of_check {ph : ProgramHeader} {flags : Nat} (hf : ph.flags < 8)
    (h : permsOkN ph.flags flags = true) (file : Bytes) :
    PermsOk (ELFImage.segment file ph) flags := by
  obtain ⟨hr, hw, hx⟩ := permissions_bits hf
  simp only [PermsOk, Segment.readable, Segment.writable, Segment.executable, ELFImage.segment,
    hr, hw, hx]
  simp only [permsOkN, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by simpa using h1, ?_, ?_⟩
  · constructor
    · intro hw'
      have : (ph.flags / 2 % 2 == 1) = true := hw'
      rw [this] at h2
      simpa using h2.symm
    · intro hne
      have : (flags &&& 1 != 0) = true := by simpa using hne
      rw [this] at h2
      exact h2
  · intro hne
    rcases h3 with h3 | h3
    · exact absurd h3 hne
    · simpa using h3

/-- The bytewise meaning of `bytesInN`. -/
theorem bytesInN_spec {n : Nat} {ph : ProgramHeader} {s : LinkedSection}
    (h : bytesInN n ph s = true) (i : Nat) (hi : i < s.memorySize) :
    (expected s)[i]? = some (segByteN n ph (s.address - ph.virtualAddress + i)) := by
  simp only [bytesInN, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hle, hdata⟩, htail⟩ := h
  unfold expected
  by_cases hid : i < s.data.size
  · rw [List.getElem?_append_left (by simpa using hid)]
    have := congrArg (fun l => l[i]?) hdata
    simp only [List.getElem?_map, List.getElem?_range hid, Option.map_some] at this
    exact this.symm
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [Array.length_toList, List.getElem?_replicate]
    rw [ite_eq_left (by omega)]
    congr 1
    rcases htail with hfs | hall
    · unfold segByteN
      rw [ite_eq_right (by omega)]
    · have := hall (i - s.data.size) (by omega)
      have e : s.address - ph.virtualAddress + s.data.size + (i - s.data.size) =
          s.address - ph.virtualAddress + i := by omega
      rw [e] at this
      exact this.symm

/-- One arithmetic check against a parsed `PT_LOAD` header places a linked
section byte-exactly in the loaded image. -/
theorem sectionIn_of_check {policy : ELFImage.Policy} {n len : Nat}
    {records : ELFImage.Records} {ph : ProgramHeader} {s : LinkedSection}
    (hp : ELFImage.parse policy (Blob.bytesOf n len) = some records)
    (hph : ph ∈ records.programHeaders) (hc : sectionInN n ph s = true) :
    SectionIn (records.image (Blob.bytesOf n len)) s := by
  simp only [sectionInN, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hk, hlo⟩, hhi⟩, hperm⟩, hbytes⟩ := hc
  have hload : ph ∈ ELFImage.loadHeaders records.programHeaders :=
    List.mem_filter.mpr ⟨hph, by simp [hk]⟩
  have hvalid : ELFImage.ValidLoad policy (Blob.bytesOf n len) ph :=
    (ELFImage.parse_sound hp).2.2.2.2.2.2.1 ph hload
  have hinside := hvalid.2.2.2.1
  have hfit := hvalid.2.2.1
  refine ⟨ELFImage.segment (Blob.bytesOf n len) ph, List.mem_map.mpr ⟨ph, hload, rfl⟩,
    hlo, hhi, permsOk_of_check hvalid.2.1 hperm _, ?_⟩
  intro i hi
  rw [bytesInN_spec hbytes i hi]
  show (ELFImage.segment (Blob.bytesOf n len) ph).bytes[s.address - ph.virtualAddress + i]? = _
  have hin : s.address - ph.virtualAddress + i < ph.memorySize := by omega
  unfold segByteN
  split
  · rename_i hlt
    rw [ELFImage.segment_file_byte hinside hlt, Blob.getElem?_bytesOf]
    have : ph.offset + (s.address - ph.virtualAddress + i) < len := by
      simp only [Blob.size_bytesOf] at hinside
      omega
    simp [this]
  · rename_i hge
    rw [ELFImage.segment_bss_byte hinside (by omega) hin]

theorem mapM_readObject_bytes (objects : List Blob) :
    (objects.map Blob.bytes).mapM readObject =
      objects.mapM (fun b => Blob.readObjectN b.n b.len) := by
  induction objects with
  | nil => rfl
  | cons b rest ih => simp [List.mapM_cons, ih, Blob.bytes, Blob.readObject_bytesOf]

/-! ## Facts about the default preparation -/

/-- Dropping no section changes nothing. -/
theorem dropSections_nil (i : Nat) (object : ObjectFile) : dropSections [] i object = object := by
  cases object with
  | mk header sections symbols relocations =>
    simp only [dropSections, List.contains_nil, Bool.false_eq_true, ite_false, Bool.not_false,
      List.filter_true]
    congr 1
    exact List.zipIdx_map_fst 0 sections

/-- With no discarded sections, `prepare` is the shared profile rewrite. -/
theorem prepare_nil (objects : List ObjectFile) : prepare objects [] = Profile.normalize objects := by
  simp only [prepare, dropSections_nil]
  exact List.zipIdx_map_fst 0 _

/-- Every linked section has one of the three flag sets of the profile. -/
theorem linkSection_flags {objects : List ObjectFile} {rels : List ResolvedRelocation}
    {relocate : Relocator} {pl : Placement} {s : LinkedSection}
    (h : linkSection objects rels relocate pl = some s) :
    s.flags = 2 ∨ s.flags = 3 ∨ s.flags = 6 := by
  unfold linkSection at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨part, -, _, -, _, -, _, hfl, _, -, _, -, patches, -, _, -, data, -, _, -, rfl⟩ := h
  by_contra hn
  simp only at hn
  simp [guard, hn] at hfl

theorem link_flags {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : Relocation.link objects layout absolute = some out)
    {s : LinkedSection} (hs : s ∈ out) : s.flags = 2 ∨ s.flags = 3 ∨ s.flags = 6 := by
  have h' : Silmaril.Formats.ELF.Link.link Relocation.accepts Relocation.relocate objects layout
      absolute = some out := by
    unfold Relocation.link at h
    by_cases hs : (objects.all Relocation.staticObject) = true
    · simpa [hs] using h
    · simp [hs] at h
  obtain ⟨-, rels, -, hmap, -⟩ := Silmaril.Formats.ELF.Link.link_some h'
  obtain ⟨pl, -, hpl⟩ := Silmaril.Formats.ELF.Link.mapM_some_mem' hmap s hs
  exact linkSection_flags hpl

/-! ## Kernel-fast patching is `foldlM applyPatch` -/

theorem foldlM_bounds : ∀ {patches : List Patch} {d d' : Bytes},
    patches.foldlM applyPatch d = some d' → ∀ p ∈ patches, p.offset + p.bytes.size ≤ d.size
  | [], _, _, _, p, hp => by simp at hp
  | q :: qs, d, d', h, p, hp => by
    simp only [List.foldlM_cons] at h
    cases he : applyPatch d q with
    | none => simp [he] at h
    | some e =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      rcases List.mem_cons.mp hp with rfl | hmem
      · unfold applyPatch at he
        by_contra hn
        simp [hn] at he
      · rw [← applyPatch_size he]; exact foldlM_bounds h p hmem

theorem foldlM_some : ∀ {patches : List Patch} {d : Bytes},
    (∀ p ∈ patches, p.offset + p.bytes.size ≤ d.size) → ∃ d', patches.foldlM applyPatch d = some d'
  | [], d, _ => ⟨d, rfl⟩
  | q :: qs, d, h => by
    have hq := h q List.mem_cons_self
    have he : applyPatch d q = some ⟨d.toList.take q.offset ++ q.bytes.toList ++
        d.toList.drop (q.offset + q.bytes.size)⟩ := by simp [applyPatch, hq]
    obtain ⟨d', hd'⟩ := foldlM_some (patches := qs)
      (d := ⟨d.toList.take q.offset ++ q.bytes.toList ++ d.toList.drop (q.offset + q.bytes.size)⟩)
      (fun p hp => by rw [applyPatch_size he]; exact h p (List.mem_cons_of_mem _ hp))
    exact ⟨d', by simp only [List.foldlM_cons, he, Option.bind_eq_bind, Option.bind_some]; exact hd'⟩

theorem applyAll_getElem? (d : Bytes) (patches : List Patch) (i : Nat) :
    (applyAll d patches)[i]? = d[i]?.map (patchedByte patches i) := by
  simp only [applyAll, List.getElem?_toArray, List.getElem?_map, List.getElem?_zipIdx,
    Array.getElem?_toList]
  cases d[i]? <;> simp

theorem sortedFrom_le : ∀ {ps : List Patch} {pos : Nat}, sortedFrom pos ps = true →
    ∀ q ∈ ps, pos ≤ q.offset
  | [], _, _, q, hq => by simp at hq
  | p :: ps, pos, h, q, hq => by
    simp only [sortedFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · have := sortedFrom_le h.2 q hq; omega

theorem sortedFrom_pairwise : ∀ {ps : List Patch} {pos : Nat}, sortedFrom pos ps = true →
    ps.Pairwise Patch.Disjoint
  | [], _, _ => .nil
  | p :: ps, pos, h => by
    simp only [sortedFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    refine List.Pairwise.cons (fun q hq => ?_) (sortedFrom_pairwise h.2)
    exact Or.inl (sortedFrom_le h.2 q hq)

theorem mergePatches_spec : ∀ {ps : List Patch} {l : List (BitVec 8)} {pos : Nat},
    sortedFrom pos ps = true → (∀ q ∈ ps, q.offset + q.bytes.size ≤ pos + l.length) →
    (mergePatches l pos ps).length = l.length ∧
    ∀ j, (mergePatches l pos ps)[j]? =
      match ps.find? (fun q => decide (Covers q (pos + j))) with
      | some q => q.bytes[pos + j - q.offset]?
      | none => l[j]?
  | [], l, pos, _, _ => by simp [mergePatches]
  | p :: ps, l, pos, hs, hb => by
    have hp := hb p List.mem_cons_self
    simp only [sortedFrom, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hpos, hs'⟩ := hs
    have hall := sortedFrom_le hs'
    obtain ⟨ih1, ih2⟩ := mergePatches_spec (ps := ps)
      (l := l.drop (p.offset - pos + p.bytes.size)) (pos := p.offset + p.bytes.size) hs' (by
        intro q hq
        have h1 := hall q hq
        have h2 := hb q (List.mem_cons_of_mem _ hq)
        simp only [List.length_drop]
        omega)
    have hlen : (mergePatches l pos (p :: ps)).length = l.length := by
      simp only [mergePatches, List.length_append, List.length_take, Array.length_toList, ih1,
        List.length_drop]
      omega
    refine ⟨hlen, fun j => ?_⟩
    simp only [mergePatches, List.append_assoc]
    have htake : (l.take (p.offset - pos)).length = p.offset - pos := by
      simp only [List.length_take]; omega
    by_cases h1 : j < p.offset - pos
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h1]
      have hnc : ∀ q ∈ p :: ps, ¬ Covers q (pos + j) := by
        intro q hq hcq
        rcases List.mem_cons.mp hq with rfl | hq
        · simp only [Covers] at hcq; omega
        · have := hall q hq; simp only [Covers] at hcq; omega
      have : (p :: ps).find? (fun q => decide (Covers q (pos + j))) = none := by
        rw [List.find?_eq_none]; intro q hq; simpa using hnc q hq
      rw [this]
    · rw [List.getElem?_append_right (by omega), htake]
      by_cases h2 : j < p.offset - pos + p.bytes.size
      · rw [List.getElem?_append_left (by simp; omega)]
        have hcp : Covers p (pos + j) := by simp only [Covers]; omega
        have : (p :: ps).find? (fun q => decide (Covers q (pos + j))) = some p := by
          simp [hcp]
        rw [this, Array.getElem?_toList]
        congr 1; omega
      · rw [List.getElem?_append_right (by simp; omega), ih2]
        have hnp : ¬ Covers p (pos + j) := by simp only [Covers]; omega
        have hidx : p.offset + p.bytes.size + (j - (p.offset - pos) - p.bytes.toList.length) =
            pos + j := by
          simp only [Array.length_toList]; omega
        simp only [hidx, List.find?_cons, hnp, decide_false]
        cases ps.find? (fun q => decide (Covers q (pos + j))) with
        | some q => rfl
        | none =>
          rw [List.getElem?_drop]
          simp only [Array.length_toList]
          rw [show p.offset - pos + p.bytes.size + (j - (p.offset - pos) - p.bytes.size) = j by omega]

theorem pairwiseFast_iff (patches : List Patch) :
    pairwiseFast patches = true ↔ patches.Pairwise Patch.Disjoint := by
  unfold pairwiseFast
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact sortedFrom_pairwise h
    · exact h
  · intro h; simp [h]

/-- The merge is `applyAll` on sorted, in-bounds patches. -/
theorem merge_eq_applyAll {patches : List Patch} {d : Bytes} (hs : sortedFrom 0 patches = true)
    (hb : ∀ p ∈ patches, p.offset + p.bytes.size ≤ d.size) :
    (⟨mergePatches d.toList 0 patches⟩ : Bytes) = applyAll d patches := by
  obtain ⟨h1, h2⟩ := mergePatches_spec (l := d.toList) hs (by simpa using hb)
  apply Array.ext_getElem?
  intro i
  rw [applyAll_getElem?, List.getElem?_toArray, h2 i, Nat.zero_add]
  simp only [Array.getElem?_toList]
  cases hf : patches.find? (fun q => decide (Covers q i)) with
  | none => cases d[i]? <;> simp [patchedByte, hf]
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have hc : Covers q i := by simpa using List.find?_some hf
    have hi : i < d.size := by have := hb q hq; simp only [Covers] at hc; omega
    have hj : i - q.offset < q.bytes.size := by simp only [Covers] at hc; omega
    simp [Array.getElem?_eq_getElem hi, patchedByte, hf, Array.getElem?_eq_getElem hj]

/-- **One-pass patching is `foldlM applyPatch`** for pairwise disjoint patches. -/
theorem foldlM_applyPatch_eq {patches : List Patch} {d : Bytes}
    (hpw : patches.Pairwise Patch.Disjoint) :
    patches.foldlM applyPatch d = applyPatches d patches := by
  unfold applyPatches
  split
  · rename_i hall
    have hb : ∀ p ∈ patches, p.offset + p.bytes.size ≤ d.size := by
      intro p hp; simpa using List.all_eq_true.mp hall p hp
    obtain ⟨d', hd'⟩ := foldlM_some hb
    rw [hd']
    congr 1
    have hsplit : (if sortedFrom 0 patches = true then (⟨mergePatches d.toList 0 patches⟩ : Bytes)
        else applyAll d patches) = applyAll d patches := by
      split
      · exact merge_eq_applyAll (by assumption) hb
      · rfl
    rw [hsplit]
    apply Array.ext_getElem?
    intro i
    rw [applyAll_getElem?]
    by_cases hc : ∃ q ∈ patches, Covers q i
    · obtain ⟨q, hq, hcq⟩ := hc
      obtain ⟨p, hp⟩ : ∃ p, patches.find? (fun p => decide (Covers p i)) = some p := by
        cases h : patches.find? (fun p => decide (Covers p i)) with
        | some p => exact ⟨p, rfl⟩
        | none =>
          rw [List.find?_eq_none] at h
          exact absurd (by simpa using hcq) (h q hq)
      have hpm := List.mem_of_find?_eq_some hp
      have hpc : Covers p i := by simpa using List.find?_some hp
      rw [foldl_patches_get_mem hpw hd' p hpm i hpc]
      have hi : i < d.size := by
        have := hb p hpm; simp only [Covers] at hpc; omega
      have hj : i - p.offset < p.bytes.size := by simp only [Covers] at hpc; omega
      simp only [Array.getElem?_eq_getElem hi, Option.map_some, patchedByte, hp,
        Array.getElem?_eq_getElem hj, Option.getD_some]
    · have hn : ∀ q ∈ patches, ¬ Covers q i := fun q hq hcq => hc ⟨q, hq, hcq⟩
      rw [foldl_patches_get hpw hd' i hn]
      have hf : patches.find? (fun p => decide (Covers p i)) = none := by
        rw [List.find?_eq_none]; intro q hq; simpa using hn q hq
      cases d[i]? <;> simp [patchedByte, hf]
  · rename_i hall
    cases h : patches.foldlM applyPatch d with
    | none => rfl
    | some d' =>
      exact absurd (List.all_eq_true.mpr fun p hp => by simpa using foldlM_bounds h p hp) hall

theorem guard_bind_congr {p : Prop} [Decidable p] {α : Type} {x y : Option α}
    (h : p → x = y) : ((guard p : Option Unit) >>= fun _ => x) = (guard p >>= fun _ => y) := by
  by_cases hp : p
  · simp [hp, h hp]
  · simp [hp]

theorem linkSectionFast_eq (objects : List ObjectFile) (relocations : List ResolvedRelocation)
    (relocate : Relocator) (placement : Placement) :
    linkSectionFast objects relocations relocate placement =
      linkSection objects relocations relocate placement := by
  unfold linkSectionFast linkSection
  congr 1; funext part
  congr 1; funext _; congr 1; funext _; congr 1; funext _; congr 1; funext _
  congr 1; funext _; congr 1; funext patches
  have hg : (guard (pairwiseFast patches = true) : Option Unit) =
      guard (patches.Pairwise Patch.Disjoint) := by
    by_cases h : patches.Pairwise Patch.Disjoint
    · simp [h, (pairwiseFast_iff patches).mpr h]
    · have : ¬ pairwiseFast patches = true := fun h' => h ((pairwiseFast_iff patches).mp h')
      simp [h, this]
  rw [hg]
  refine guard_bind_congr fun hpw => ?_
  rw [foldlM_applyPatch_eq hpw]


theorem linkSectionFast_eq' : linkSectionFast = linkSection := by
  funext o r f p; exact linkSectionFast_eq o r f p

/-! ## Section-wise linking -/

theorem linkSection_shape {objects : List ObjectFile} {rels : List ResolvedRelocation}
    {relocate : Relocator} {pl : Placement} {s : LinkedSection}
    (h : linkSection objects rels relocate pl = some s) :
    s.address = (shapeOf objects pl).1 ∧ s.memorySize = (shapeOf objects pl).2 := by
  unfold linkSection at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨part, hpart, _, -, _, -, _, -, _, -, _, -, patches, -, _, -, data, -, _, -, rfl⟩ := h
  simp [shapeOf, hpart]

theorem mapM_pairwise {α β : Type} {f : α → Option β} {R : α → α → Prop} {S : β → β → Prop}
    (hS : ∀ x y a b, f x = some a → f y = some b → R x y → S a b) :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l.Pairwise R → l'.Pairwise S
  | [], l', h, _ => by simp at h; subst h; exact .nil
  | x :: xs, l', h, hp => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hp
    refine List.Pairwise.cons (fun b' hb' => ?_) (mapM_pairwise hS hbs hxs)
    obtain ⟨y, hy, hfy⟩ := Silmaril.Formats.ELF.Link.mapM_some_mem' hbs b' hb'
    exact hS x y b b' hb hfy (hx y hy)

theorem mapM_of_forall {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, ∃ y, f x = some y) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := mapM_of_forall (l := xs) fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- **Section-wise linking.** The global guards, the resolved relocations, one successful
`linkSection` per placement and disjoint placements give a successful `Relocation.link`,
each of whose sections is the `linkSection` of a placement. -/
theorem link_of_sections {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {rels : List ResolvedRelocation}
    (hg : linkGuards objects layout absolute = true)
    (hr : resolveRelocations objects layout absolute = some rels)
    (hs : ∀ pl ∈ layout, ∃ s, linkSection objects rels Relocation.relocate pl = some s)
    (hd : shapesDisjoint objects layout = true) :
    ∃ out, Relocation.link objects layout absolute = some out ∧
      ∀ s ∈ out, ∃ pl ∈ layout, linkSection objects rels Relocation.relocate pl = some s := by
  obtain ⟨out, hout⟩ := mapM_of_forall hs
  have hpw : out.Pairwise LinkedSection.Disjoint := by
    refine mapM_pairwise (R := fun p q => ShapeDisjoint (shapeOf objects p) (shapeOf objects q))
      (fun x y a b ha hb hxy => ?_) hout ?_
    · obtain ⟨ha1, ha2⟩ := linkSection_shape ha
      obtain ⟨hb1, hb2⟩ := linkSection_shape hb
      simp only [LinkedSection.Disjoint, ha1, ha2, hb1, hb2]
      exact hxy
    · have := of_decide_eq_true hd
      exact List.pairwise_map.mp this
  refine ⟨out, ?_, fun s hs' => Silmaril.Formats.ELF.Link.mapM_some_mem' hout s hs'⟩
  simp only [linkGuards, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
  unfold Relocation.link Silmaril.Formats.ELF.Link.link
  simp only [h1, h2, h3, h4, h5, h6, h7, hr, hout, hpw, guard_true, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]

/-! ## The validator is sound -/

/-- **Composition of section-wise checks**, for any preparation `prep`. Parsed inputs,
resolved relocations, the global checks, and the per-section check for every placement give
`ValidatedBy prep`. -/
theorem validatedBy_of_parts {prep : List ObjectFile → List ObjectFile}
    {objects : List Blob} {exe : Blob} {W : Witness}
    {parsed : List ObjectFile} {records : ELFImage.Records} {rels : List ResolvedRelocation}
    (hobj : objects.mapM (fun b => Blob.readObjectN b.n b.len) = some parsed)
    (hexe : Blob.parseN ELFImage.x86Policy exe.n exe.len = some records)
    (hrels : resolveRelocations (prep parsed) W.layout W.absolute = some rels)
    (hg : globalOk (prep parsed) records W = true)
    (hs : ∀ pl ∈ W.layout, checkSection exe.n records (prep parsed) rels pl = true) :
    ValidatedBy prep (objects.map Blob.bytes) exe.bytes W := by
  simp only [globalOk, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨hguards, hdisj⟩, hentry⟩ := hg
  have hsec : ∀ pl ∈ W.layout, ∃ s, linkSection (prep parsed) rels
      Relocation.relocate pl = some s ∧
      ∃ ph ∈ records.programHeaders, sectionInN exe.n ph s = true := by
    intro pl hpl
    have h := hs pl hpl
    unfold checkSection at h
    rw [linkSectionFast_eq] at h
    split at h
    · rename_i s hls
      exact ⟨s, hls, by simpa using h⟩
    · cases h
  obtain ⟨out, hlink, hout⟩ := link_of_sections hguards hrels
    (fun pl hpl => (hsec pl hpl).imp fun _ h => h.1) hdisj
  have hp : ELFImage.parse ELFImage.x86Policy exe.bytes = some records := by
    rw [Blob.bytes, Blob.parse_bytesOf]
    exact hexe
  refine ⟨parsed, records, out, by rw [mapM_readObject_bytes]; exact hobj, hp, hlink, ?_, hentry⟩
  intro s hs'
  obtain ⟨pl, hpl, hls⟩ := hout s hs'
  obtain ⟨s', hls', ph, hph, hc⟩ := hsec pl hpl
  rw [hls] at hls'
  cases hls'
  exact sectionIn_of_check hp hph hc

/-- **Composition of section-wise checks.** Parsed inputs, resolved relocations, the
global checks, and the per-section check for every placement give `Validated`. -/
theorem validated_of_parts {objects : List Blob} {exe : Blob} {W : Witness}
    {parsed : List ObjectFile} {records : ELFImage.Records} {rels : List ResolvedRelocation}
    (hobj : objects.mapM (fun b => Blob.readObjectN b.n b.len) = some parsed)
    (hexe : Blob.parseN ELFImage.x86Policy exe.n exe.len = some records)
    (hrels : resolveRelocations (prepare parsed W.dropped) W.layout W.absolute = some rels)
    (hg : globalOk (prepare parsed W.dropped) records W = true)
    (hs : ∀ pl ∈ W.layout, checkSection exe.n records (prepare parsed W.dropped) rels pl = true) :
    Validated (objects.map Blob.bytes) exe.bytes W :=
  validatedBy_of_parts (prep := fun p => prepare p W.dropped) hobj hexe hrels hg hs

/-- The checks after parsing give `ValidatedBy`. -/
theorem validatedBy_of_checkAll {prep : List ObjectFile → List ObjectFile}
    {objects : List Blob} {exe : Blob} {W : Witness}
    {parsed : List ObjectFile} {records : ELFImage.Records}
    (hobj : objects.mapM (fun b => Blob.readObjectN b.n b.len) = some parsed)
    (hexe : Blob.parseN ELFImage.x86Policy exe.n exe.len = some records)
    (h : checkAllBy prep exe.n records parsed W = true) :
    ValidatedBy prep (objects.map Blob.bytes) exe.bytes W := by
  unfold checkAllBy at h
  dsimp only at h
  split at h
  · rename_i rels hrels
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact validatedBy_of_parts hobj hexe hrels h.1 h.2
  · cases h

/-- Soundness of the blob validator, for any preparation. -/
theorem validateByN_sound {prep : List ObjectFile → List ObjectFile}
    {objects : List Blob} {exe : Blob} {W : Witness}
    (h : validateByN prep objects exe W = true) :
    ValidatedBy prep (objects.map Blob.bytes) exe.bytes W := by
  unfold validateByN at h
  split at h
  · rename_i parsed records hobj hexe
    exact validatedBy_of_checkAll hobj hexe h
  · cases h

/-- Soundness of the blob validator. -/
theorem validateN_sound {objects : List Blob} {exe : Blob} {W : Witness}
    (h : validateN objects exe W = true) :
    Validated (objects.map Blob.bytes) exe.bytes W :=
  validateByN_sound (prep := fun p => prepare p W.dropped) h

/-- Section-wise validation for any preparation. -/
theorem validatedBy_of_chunks {prep : List ObjectFile → List ObjectFile}
    {objects : List Blob} {exe : Blob} {W : Witness}
    (chunks : List (List Placement)) (hg : validateGlobalByN prep objects exe W = true)
    (hc : ∀ c ∈ chunks, validateChunkByN prep objects exe W c = true)
    (hcover : ∀ pl ∈ W.layout, ∃ c ∈ chunks, pl ∈ c) :
    ValidatedBy prep (objects.map Blob.bytes) exe.bytes W := by
  unfold validateGlobalByN at hg
  dsimp only at hg
  split at hg
  · rename_i parsed records hobj hexe
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hg
    obtain ⟨⟨rels, hrels⟩, hglob⟩ := hg
    refine validatedBy_of_parts hobj hexe hrels hglob fun pl hpl => ?_
    obtain ⟨c, hcm, hplc⟩ := hcover pl hpl
    have h := hc c hcm
    unfold validateChunkByN at h
    dsimp only at h
    rw [hobj, hexe] at h
    simp only [hrels, List.all_eq_true] at h
    exact h pl hplc
  · cases hg

/-- **Section-wise validation**: a global check and per-chunk section checks
whose chunks cover the layout give `Validated`. Each chunk is a separate kernel
evaluation, so no single `decide` has to link the whole image. -/
theorem validated_of_chunks {objects : List Blob} {exe : Blob} {W : Witness}
    (chunks : List (List Placement)) (hg : validateGlobalN objects exe W = true)
    (hc : ∀ c ∈ chunks, validateChunkN objects exe W c = true)
    (hcover : ∀ pl ∈ W.layout, ∃ c ∈ chunks, pl ∈ c) :
    Validated (objects.map Blob.bytes) exe.bytes W :=
  validatedBy_of_chunks (prep := fun p => prepare p W.dropped) chunks hg hc hcover

/-- Soundness of the validator on byte arrays. -/
theorem validate_sound {objects : List Bytes} {exe : Bytes} {W : Witness}
    (h : validate objects exe W = true) : Validated objects exe W := by
  have := validateN_sound h
  simpa [List.map_map, Function.comp_def, Blob.bytes_ofBytes] using this

/-! ## The profile-aware validator -/

/-- The piece check gives `PiecesIn`. -/
theorem piecesIn_of_check {objects : List Blob} {exe : Blob} {W : Witness}
    {parsed : List ObjectFile} {records : ELFImage.Records}
    (hobj : objects.mapM (fun b => Blob.readObjectN b.n b.len) = some parsed)
    (hexe : Blob.parseN ELFImage.x86Policy exe.n exe.len = some records)
    (h : piecesOk exe.n records parsed W.pieces = true) :
    PiecesIn (objects.map Blob.bytes) exe.bytes W := by
  have hp : ELFImage.parse ELFImage.x86Policy exe.bytes = some records := by
    rw [Blob.bytes, Blob.parse_bytesOf]
    exact hexe
  refine ⟨parsed, records, by rw [mapM_readObject_bytes]; exact hobj, hp, fun p hpm => ?_⟩
  unfold piecesOk at h
  rw [List.all_eq_true] at h
  have hq := h p hpm
  split at hq
  · rename_i s hs
    obtain ⟨ph, hph, hc⟩ := List.any_eq_true.mp hq
    exact ⟨s, hs, sectionIn_of_check hp hph hc⟩
  · cases hq

/-- Soundness of the profile-aware validator. -/
theorem validateProfileN_sound {objects : List Blob} {exe : Blob} {W : Witness}
    (h : validateProfileN objects exe W = true) :
    ValidatedProfile (objects.map Blob.bytes) exe.bytes W := by
  unfold validateProfileN at h
  split at h
  · rename_i parsed records hobj hexe
    rw [Bool.and_eq_true] at h
    exact ⟨validatedBy_of_checkAll hobj hexe h.1, piecesIn_of_check hobj hexe h.2⟩
  · cases h

/-- Section-wise validation with the profile-aware validator. -/
theorem validatedProfile_of_chunks {objects : List Blob} {exe : Blob} {W : Witness}
    (chunks : List (List Placement)) (hg : validateProfileGlobalN objects exe W = true)
    (hc : ∀ c ∈ chunks, validateProfileChunkN objects exe W c = true)
    (hcover : ∀ pl ∈ W.layout, ∃ c ∈ chunks, pl ∈ c) :
    ValidatedProfile (objects.map Blob.bytes) exe.bytes W := by
  have hg' := hg
  unfold validateProfileGlobalN at hg'
  dsimp only at hg'
  split at hg'
  · rename_i parsed records hobj hexe
    simp only [Bool.and_eq_true] at hg'
    refine ⟨validatedBy_of_chunks chunks ?_ hc hcover, piecesIn_of_check hobj hexe hg'.2⟩
    unfold validateGlobalByN
    rw [hobj, hexe]
    simp only [Bool.and_eq_true]
    exact hg'.1
  · cases hg'

/-- A chunk of the layout passes when the whole profile-aware validation does. -/
theorem validateProfileChunkN_of {objects : List Blob} {exe : Blob} {W : Witness}
    {chunk : List Placement} (h : validateProfileN objects exe W = true)
    (hsub : ∀ pl ∈ chunk, pl ∈ W.layout) : validateProfileChunkN objects exe W chunk = true := by
  unfold validateProfileN at h
  unfold validateProfileChunkN validateChunkByN
  split at h
  · simp only [Bool.and_eq_true] at h
    have h1 := h.1
    unfold checkAllBy at h1
    dsimp only at h1 ⊢
    split at h1
    · simp only [Bool.and_eq_true, List.all_eq_true] at h1 ⊢
      exact fun pl hpl => h1.2 pl (hsub pl hpl)
    · cases h1
  · cases h

/-- **Rejection from one chunk**: if a chunk of the layout fails, the whole profile-aware
validation fails. -/
theorem validateProfileN_false_of_chunk {objects : List Blob} {exe : Blob} {W : Witness}
    {chunk : List Placement} (hsub : ∀ pl ∈ chunk, pl ∈ W.layout)
    (h : validateProfileChunkN objects exe W chunk = false) :
    validateProfileN objects exe W = false := by
  cases hv : validateProfileN objects exe W
  · rfl
  · rw [validateProfileChunkN_of hv hsub] at h
    cases h

/-- The default options change no symbol. -/
theorem extendSymbol_default (provided : List NameBytes) (symbol : ObjectSymbol) :
    Profile.extendSymbol {} provided symbol = symbol := rfl

/-- The default options change no object. -/
theorem extendObject_default (provided : List NameBytes) (object : ObjectFile) :
    Profile.extendObject {} provided object = object := by
  have hid : Profile.extendSymbol {} provided = id := funext fun _ => rfl
  cases object
  simp only [Profile.extendObject, hid, List.map_id]

/-- With the default profile, `prepareProfile` is `prepare`. -/
theorem prepareProfile_default {W : Witness} (h : W.profile = {}) (objects : List ObjectFile) :
    prepareProfile W objects = prepare objects W.dropped := by
  have hid : Profile.extendObject {} (W.absolute.map Prod.fst) = id :=
    funext (extendObject_default _)
  simp only [prepareProfile, h, hid, List.map_id, Bool.false_eq_true, ite_false]

/-- With the default profile, the profile-aware meaning is `Validated`. -/
theorem validated_of_profile_default {objects : List Bytes} {exe : Bytes} {W : Witness}
    (h : W.profile = {}) (hv : ValidatedProfile objects exe W) : Validated objects exe W := by
  obtain ⟨⟨parsed, records, out, h1, h2, h3, h4, h5⟩, -⟩ := hv
  rw [prepareProfile_default h] at h3 h5
  exact ⟨parsed, records, out, h1, h2, h3, h4, h5⟩

end Silmaril.Proofs.X86.Link.Validate
