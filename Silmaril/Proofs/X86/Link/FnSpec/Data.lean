module

public import Silmaril.Proofs.X86.Link.FnSpec.Load

/-!
# Proofs: data sections in a loaded executable

* `region_split_byte`, `region_split`: splitting consecutive bytes off a `Region`, weakening
  their permission (`Code` is a `Region` with `need = EX`; `DataPt` one with `DataNeed`).
* `data_loaded`: on a machine that holds the loader image with its permissions
  (`ImageLoaded`, `ImagePerms`), the fragment off the code bytes owns every data byte of the
  linked image (`DataPt out (byteOf m) ∗ ⊤`), and the machine's bytes are the linked bytes.
* `not_dom_of_data`: in a successful link, a byte of a non-executable section is not a code
  byte (sections are pairwise disjoint).
* `data_section_ro`, `data_section_rw`: **what a `FnSpec` precondition uses**: every
  non-executable section `s` of a validated link is `bytesPtRO s.address (expected s) ∗ ⊤`
  (its data, then its zero fill up to `memorySize`, so `.bss` is covered)
  in the frame of a loaded machine, and `bytesPt …` when `s` is writable.
-/

@[expose] public section

open Silmaril.X86 (MState Word Byte)
open Silmaril.Process (addressLimit Permissions)
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (LinkedSection)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint)
open Silmaril.X86.Link.Contract (ContainsF)
open Silmaril.X86.Link.FnSpec
open Silmaril.X86.Safe
open Silmaril.X86.Link.Validate (SectionIn PermsOk expected)

namespace Silmaril.Proofs.X86.Link.FnSpec

open Silmaril.X86.Link.FnSpec

variable {need : Nat → Permissions → Prop} {D : Nat → Prop} {bs : Nat → Byte}

theorem region_congr {D' : Nat → Prop} (h : ∀ x, D x ↔ D' x) :
    Region need D bs = Region need D' bs := by
  funext f
  simp only [Region, h]

/-- **Splitting one byte off a region**, weakening its permission to `N`. -/
theorem region_split_byte {N : Permissions → Prop} {a : Nat} (hD : D a)
    (hN : ∀ p, need a p → N p) :
    Region need D bs ⊢ₛ (byteAt N a (bs a) ∗ Region need (fun x => D x ∧ x ≠ a) bs) := by
  rintro f ⟨hin, hout⟩
  obtain ⟨hlim, p, hp, hfa⟩ := hin a hD
  refine ⟨Frag.single (.mem a) (.cell ⟨some (bs a), p⟩), _, single_disjoint_erase _ _ f,
    union_single_erase hfa, ⟨hlim, p, hN p hp, rfl⟩, ?_, ?_⟩
  · intro x ⟨hx, hxa⟩
    refine ⟨(hin x hx).1, ?_⟩
    obtain ⟨_, q, hq, hfx⟩ := hin x hx
    exact ⟨q, hq, by simp [hxa, hfx]⟩
  · intro l hl
    by_cases e : l = .mem a
    · simp [e]
    · simp only [e, ite_false]
      refine hout l fun x hx he => ?_
      subst he
      exact hl x ⟨hx, fun h => e (h ▸ rfl)⟩ rfl

/-- **Splitting consecutive bytes off a region**, weakening their permissions to `N`. -/
theorem region_split {N : Permissions → Prop} : ∀ (code : List Byte) {D : Nat → Prop} (a : Nat),
    (∀ i (hi : i < code.length), D (a + i) ∧ bs (a + i) = code[i] ∧ ∀ p, need (a + i) p → N p) →
    Region need D bs ⊢ₛ
      (bytesAt N a code ∗ Region need (fun x => D x ∧ ¬ (a ≤ x ∧ x < a + code.length)) bs)
  | [], D, a, _ => by
    rw [show bytesAt N a [] = emp from rfl, emp_sep]
    exact entails_of_eq (region_congr fun x => by simp)
  | c :: cs, D, a, hD => by
    have h0 := hD 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have h1 := region_split_byte (N := N) (bs := bs) (need := need) h0.1 h0.2.2
    rw [h0.2.1] at h1
    have hD' : ∀ i (hi : i < cs.length), (D (a + 1 + i) ∧ a + 1 + i ≠ a) ∧
        bs (a + 1 + i) = cs[i] ∧ ∀ p, need (a + 1 + i) p → N p := by
      intro i hi
      have := hD (i + 1) (by simp; omega)
      rw [show a + (i + 1) = a + 1 + i by omega] at this
      exact ⟨⟨this.1, by omega⟩, by simpa using this.2.1, this.2.2⟩
    have h2 := region_split (N := N) cs (D := fun x => D x ∧ x ≠ a) (a + 1) hD'
    have hc : Region need (fun x => (D x ∧ x ≠ a) ∧ ¬ (a + 1 ≤ x ∧ x < a + 1 + cs.length)) bs =
        Region need (fun x => D x ∧ ¬ (a ≤ x ∧ x < a + (c :: cs).length)) bs :=
      region_congr fun x => by
        simp only [List.length_cons]
        constructor
        · rintro ⟨⟨hx, h1⟩, h2⟩; exact ⟨hx, by omega⟩
        · rintro ⟨hx, h1⟩; exact ⟨⟨hx, by omega⟩, by omega⟩
    refine entails_trans h1 (entails_trans (sep_mono_right _ h2) ?_)
    rw [hc, ← sep_assoc]
    exact entails_refl _


open Silmaril.X86.Link.Unit (Contains x86_link_some)
open Silmaril.X86.Linking (Relocation.link)

theorem expected_length {s : LinkedSection} (h : s.data.size ≤ s.memorySize) :
    (expected s).length = s.memorySize := by
  simp only [expected, List.length_append, Array.length_toList, List.length_replicate]; omega

/-- **Every in-memory byte of a linked section (data or zero fill) is in a machine that holds
the loader image**, with the permissions of its segment. -/
theorem containsM_loaded {image : Silmaril.Process.LPS.Image} {out : List LinkedSection}
    {m : MState} (hin : ∀ s ∈ out, SectionIn image s)
    (hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64)
    (hl : ImageLoaded image m) {a : Nat} {b : Byte} {f : Nat}
    (hc : ContainsM out a b f) :
    a < 2 ^ 64 ∧ m.memory.bytes.get? a = some b ∧
      ∃ seg ∈ image.segments, ∃ i < seg.size, seg.base + i = a ∧ PermsOk seg f ∧
        seg.bytes[i]? = some b := by
  obtain ⟨s, hs, hf, hle, hd⟩ := hc
  obtain ⟨hsz, hlim⟩ := hb s hs
  have hlen := expected_length hsz
  have hi : a - s.address < s.memorySize := by
    rcases Nat.lt_or_ge (a - s.address) s.memorySize with h | h
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hd; cases hd
  obtain ⟨seg, hseg, hbase, hend, hperm, hbytes⟩ := hin s hs
  have hj := hbytes (a - s.address) hi
  rw [hd] at hj
  obtain ⟨hget, -⟩ := hl seg hseg (s.address - seg.base + (a - s.address)) (by omega) b hj
  rw [show seg.base + (s.address - seg.base + (a - s.address)) = a by omega] at hget
  exact ⟨by omega, hget, seg, hseg, s.address - seg.base + (a - s.address), by omega, by omega,
    hf ▸ hperm, hj⟩

/-- **The data sections are in the frame of a loaded machine**: on a machine that holds the
loader image with its permissions, the fragment off the code bytes owns every data byte of
the linked image (`DataPt`), with the machine's bytes, which are the linked bytes. -/
theorem data_loaded {image : Silmaril.Process.LPS.Image} {out : List LinkedSection}
    {m : MState} (hin : ∀ s ∈ out, SectionIn image s)
    (hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64)
    (hl : ImageLoaded image m) (hp : ImagePerms image m) :
    (DataPt out (byteOf m) ∗ fun _ => True) (offBytes (Dom out) (toFrag m)) ∧
      ∀ a b f, ContainsM out a b f → byteOf m a = b := by
  have hbyte : ∀ a b f, ContainsM out a b f → byteOf m a = b := by
    intro a b f hc
    obtain ⟨-, hget, -⟩ := containsM_loaded hin hb hl hc
    show (m.memory.bytes.get? a).getD 0 = b
    rw [hget]; rfl
  refine ⟨sep_onBytes (D := DataDom out) ⟨fun a ha => ?_, fun l hl' => ?_⟩ trivial, hbyte⟩
  · obtain ⟨⟨b, f, hf, hc⟩, hnd⟩ := ha
    obtain ⟨hlim, hget, seg, hseg, i, hi, hia, hperm, -⟩ := containsM_loaded hin hb hl hc
    refine ⟨hlim, permsAt m.memory a, ⟨?_, fun b' f' hc' hw => ?_⟩, ?_⟩
    · have := (hp seg hseg i hi).1 hperm.1
      rw [hia] at this
      exact this
    · obtain ⟨-, -, seg', hseg', i', hi', hia', hperm', -⟩ := containsM_loaded hin hb hl hc'
      have hr := (hp seg' hseg' i' hi').1 hperm'.1
      have hw' := (hp seg' hseg' i' hi').2 (hperm'.2.1.mpr hw)
      rw [hia'] at hr hw'
      exact ⟨hr, hw'⟩
    · have hdd : DataDom out a := ⟨⟨b, f, hf, hc⟩, hnd⟩
      simp only [onBytes, offBytes, toFrag, hnd, ite_false]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hdd), show byteOf m a = b from hbyte a b f hc, hget]
  · cases l with
    | mem a =>
      have : ¬ DataDom out a := fun ha => hl' a ha rfl
      simp [onBytes, this]
    | _ => rfl

theorem pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x) :
    ∀ {l : List α}, l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: as, h, x, hx, y, hy, hxy => by
    obtain ⟨ha, has⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hx with hx' | hx'
    · rcases List.mem_cons.mp hy with hy' | hy'
      · exact absurd (hx'.trans hy'.symm) hxy
      · subst hx'; exact ha y hy'
    · rcases List.mem_cons.mp hy with hy' | hy'
      · subst hy'; exact hR _ _ (ha x hx')
      · exact pairwise_ne hR has x hx' y hy' hxy

/-- In a successful link, a byte of a non-executable section is not a code byte. -/
theorem not_dom_of_data {objects : List ObjectFile} {layout : Silmaril.Formats.ELF.Link.Layout}
    {absolute : Silmaril.Formats.ELF.Link.AbsoluteSymbols} {out : List LinkedSection}
    (h : Relocation.link objects layout absolute = some out) {s : LinkedSection} (hs : s ∈ out)
    (hx : s.flags &&& 4 = 0) {i : Nat} (hi : i < s.memorySize) : ¬ Dom out (s.address + i) := by
  rintro ⟨b, f, hf, t, ht, htf, hle, hb⟩
  have hts : t ≠ s := by
    rintro rfl; rw [htf] at hx; exact hf hx
  obtain ⟨-, rels, -, -, hpw⟩ := Silmaril.Formats.ELF.Link.link_some (x86_link_some h)
  have hdis := pairwise_ne (fun x y (hxy : Silmaril.Formats.ELF.Link.LinkedSection.Disjoint x y) => by
    unfold Silmaril.Formats.ELF.Link.LinkedSection.Disjoint at hxy ⊢; omega) hpw t ht s hs hts
  obtain ⟨_, _, _, _, hsz, -⟩ := link_meta h ht
  have hti : s.address + i - t.address < t.data.size := by
    rcases Nat.lt_or_ge (s.address + i - t.address) t.data.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hb; cases hb
  unfold Silmaril.Formats.ELF.Link.LinkedSection.Disjoint at hdis
  omega

/-- **A loaded data section, as a precondition can use it**: in a validated link, every
non-executable section's linked bytes are owned, readable, by the frame of a loaded machine
(`bytesPtRO`); writable ones are also owned writable (`data_section_rw`). -/
theorem data_section_ro {objects : List ObjectFile} {layout : Silmaril.Formats.ELF.Link.Layout}
    {absolute : Silmaril.Formats.ELF.Link.AbsoluteSymbols} {out : List LinkedSection}
    {image : Silmaril.Process.LPS.Image} {m : MState}
    (h : Relocation.link objects layout absolute = some out)
    (hin : ∀ s ∈ out, SectionIn image s) (hl : ImageLoaded image m) (hp : ImagePerms image m)
    {s : LinkedSection} (hs : s ∈ out) (hx : s.flags &&& 4 = 0) :
    (bytesPtRO s.address (expected s) ∗ fun _ => True) (offBytes (Dom out) (toFrag m)) := by
  have hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64 :=
    fun s hs => by obtain ⟨_, _, _, _, hsz, hlim⟩ := link_meta h hs; exact ⟨hsz, hlim⟩
  obtain ⟨hdata, hbyte⟩ := data_loaded hin hb hl hp
  have hsz := (hb s hs).1
  have hlen := expected_length hsz
  have hD : ∀ i (hi : i < (expected s).length), DataDom out (s.address + i) ∧
      byteOf m (s.address + i) = (expected s)[i] ∧
      ∀ p, DataNeed out (s.address + i) p → RO p := by
    intro i hi
    have hc : ContainsM out (s.address + i) (expected s)[i] s.flags :=
      ⟨s, hs, rfl, by omega, by simp⟩
    exact ⟨⟨⟨_, _, hx, hc⟩, not_dom_of_data h hs hx (by omega)⟩, hbyte _ _ _ hc,
      fun p hp => hp.1⟩
  have e1 : (DataPt out (byteOf m) ∗ fun _ => True) ⊢ₛ
      (bytesPtRO s.address (expected s) ∗ fun _ => True) :=
    entails_trans (sep_mono_left _ (region_split (N := RO) _ _ hD))
      (by rw [sep_assoc]; exact sep_mono_right _ (fun _ _ => trivial))
  exact e1 _ hdata

/-- **A loaded writable data section** (`.data`, `.bss`): owned readable and writable
(`bytesPt`) by the frame of a loaded machine. -/
theorem data_section_rw {objects : List ObjectFile} {layout : Silmaril.Formats.ELF.Link.Layout}
    {absolute : Silmaril.Formats.ELF.Link.AbsoluteSymbols} {out : List LinkedSection}
    {image : Silmaril.Process.LPS.Image} {m : MState}
    (h : Relocation.link objects layout absolute = some out)
    (hin : ∀ s ∈ out, SectionIn image s) (hl : ImageLoaded image m) (hp : ImagePerms image m)
    {s : LinkedSection} (hs : s ∈ out) (hx : s.flags &&& 4 = 0) (hw : s.flags &&& 1 ≠ 0) :
    (bytesPt s.address (expected s) ∗ fun _ => True) (offBytes (Dom out) (toFrag m)) := by
  have hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64 :=
    fun s hs => by obtain ⟨_, _, _, _, hsz, hlim⟩ := link_meta h hs; exact ⟨hsz, hlim⟩
  obtain ⟨hdata, hbyte⟩ := data_loaded hin hb hl hp
  have hsz := (hb s hs).1
  have hlen := expected_length hsz
  have hD : ∀ i (hi : i < (expected s).length), DataDom out (s.address + i) ∧
      byteOf m (s.address + i) = (expected s)[i] ∧
      ∀ p, DataNeed out (s.address + i) p → RW p := by
    intro i hi
    have hc : ContainsM out (s.address + i) (expected s)[i] s.flags :=
      ⟨s, hs, rfl, by omega, by simp⟩
    exact ⟨⟨⟨_, _, hx, hc⟩, not_dom_of_data h hs hx (by omega)⟩, hbyte _ _ _ hc,
      fun p hp => hp.2 _ _ hc hw⟩
  have e1 : (DataPt out (byteOf m) ∗ fun _ => True) ⊢ₛ
      (bytesPt s.address (expected s) ∗ fun _ => True) :=
    entails_trans (sep_mono_left _ (region_split (N := RW) _ _ hD))
      (by rw [sep_assoc]; exact sep_mono_right _ (fun _ _ => trivial))
  exact e1 _ hdata


/-! ## Non-vacuity of `ImageLoaded ∧ ImagePerms`

`data_section_ro`/`data_section_rw` assume a machine that holds the loader image with its
permissions. Any image whose segments' byte spans are pairwise disjoint and below `2 ^ 64` has
such a machine: one region mapping everything `rwx`, with the segments' bytes installed. -/

theorem installSegs_get : ∀ {segs : List Silmaril.Process.LPS.Segment},
    segs.Pairwise SegDisjoint → ∀ {seg}, seg ∈ segs → ∀ {i} (hi : i < seg.bytes.length),
      (installSegs segs).get? (seg.base + i) = some seg.bytes[i]
  | [], _, _, h, _, _ => by simp at h
  | t :: ts, hp, seg, hseg, i, hi => by
    obtain ⟨ht, hts⟩ := List.pairwise_cons.mp hp
    by_cases e : seg = t
    · subst e; exact Silmaril.Process.Memory.install_get _ _ _ _ hi
    · have hm : seg ∈ ts := by
        rcases List.mem_cons.mp hseg with h | h
        · exact absurd h e
        · exact h
      have hd := ht seg hm
      unfold SegDisjoint at hd
      show (Silmaril.Process.Memory.install _ _ _).get? _ = _
      rw [Silmaril.Process.Memory.install_outside _ _ _ _ (by omega)]
      exact installSegs_get hts hm hi

theorem allRwx_permits (bytes : Silmaril.Process.ByteMemory) (acc : Silmaril.Process.Access)
    {a : Nat} (ha : a < 2 ^ 64) :
    (Silmaril.Process.Memory.mk [allRwx] bytes).permits acc a = true := by
  have ha' : a < 18446744073709551616 := ha
  cases acc <;>
    simp [Silmaril.Process.Memory.permits, allRwx, Silmaril.Process.Region.Contains,
      Silmaril.Process.Permissions.allows, ha']

/-- **Non-vacuity**: an image with pairwise disjoint segment bytes below `2 ^ 64` is held, with
its permissions, by `loadedMachine image core`. -/
theorem loadedMachine_spec (image : Silmaril.Process.LPS.Image) (core : Silmaril.X86.State)
    (hd : image.segments.Pairwise SegDisjoint)
    (hlim : ∀ seg ∈ image.segments, seg.base + seg.size ≤ 2 ^ 64) :
    ImageLoaded image (loadedMachine image core) ∧ ImagePerms image (loadedMachine image core) := by
  refine ⟨fun seg hseg i hi b hb => ?_, fun seg hseg i hi => ?_⟩
  · have hl := hlim seg hseg
    have hi' : i < seg.bytes.length := by
      rcases Nat.lt_or_ge i seg.bytes.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hb; cases hb
    rw [List.getElem?_eq_getElem hi', Option.some.injEq] at hb
    refine ⟨?_, fun _ => allRwx_permits _ _ (by omega)⟩
    show (installSegs image.segments).get? _ = _
    rw [installSegs_get hd hseg hi', hb]
  · have hl := hlim seg hseg
    exact ⟨fun _ => allRwx_permits _ _ (by omega), fun _ => allRwx_permits _ _ (by omega)⟩

end Silmaril.Proofs.X86.Link.FnSpec
