module

public import Silmaril.Machine.Link.Unit.Defs
public import Silmaril.Proofs.Machine.Link.Patch

/-! # The linked image is the disjoint union of the TU images

PROVED here (standard axioms): `link_eq_units`, `images_disjoint`,
`link_covered`, `contains_of_unit`, `globalValuation_owner`, and the agreement
lemmas they need (`addr_restrict`, `localValue_eq`, `resolveIn_eq`,
`resolveRelocations_slot`, `linkSection_eq`, `linkPart_congr`,
`mapM_filter_slot`). The relocator must be `SectionLocal`: the imported
`Relocator` sees every relocation of the link, while a unit alone sees only its
own.
-/

@[expose] public section

namespace Silmaril.Machine.Link.Unit

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (SectionKey Layout AbsoluteSymbols ResolvedRelocation Relocator
  LinkedSection Patch applyPatch allocated definitionValue globalDefinitions addressAt sectionAt
  resolveSymbol resolveRelocations linkSection link allocatedSections)

/-! ## Placement and resolution agree with the global link -/

theorem addr_restrict (layout : Layout) (slot index : Nat) :
    (restrict layout slot).addr index = addressAt layout ⟨slot, index⟩ := by
  induction layout with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨⟨o, i⟩, a⟩ := q
    by_cases ho : o = slot
    · subst ho
      by_cases hi : i = index
      · subst hi
        simp [restrict, Placement.addr, addressAt]
      · have : (i == index) = false := by simpa using hi
        simp only [restrict, List.filterMap_cons, ite_true] at ih ⊢
        simp [Placement.addr, addressAt, hi] at ih ⊢
        exact ih
    · simp only [restrict, List.filterMap_cons, ho, ite_false] at ih ⊢
      rw [ih]
      simp [addressAt, ho]

theorem sectionAt_of {objects : List ObjectFile} {slot : Nat} {object : ObjectFile}
    (h : objects[slot]? = some object) (index : Nat) :
    sectionAt objects ⟨slot, index⟩ = object.sections[index]? := by
  simp [sectionAt, h]

theorem localValue_eq {objects : List ObjectFile} {slot : Nat} {object : ObjectFile}
    (h : objects[slot]? = some object) (layout : Layout) (symbol : ObjectSymbol) :
    localValue object (restrict layout slot) symbol = definitionValue objects layout slot symbol := by
  simp only [localValue, definitionValue, sectionAt_of h, addr_restrict]

theorem resolveIn_eq {objects : List ObjectFile} {slot : Nat} {object : ObjectFile}
    (h : objects[slot]? = some object) (layout : Layout) (absolute : AbsoluteSymbols)
    (symbolIndex : Nat) :
    resolveIn object (restrict layout slot) (globalValuation objects layout absolute) symbolIndex =
      resolveSymbol objects layout absolute slot symbolIndex := by
  simp only [resolveIn, resolveSymbol, h, localValue_eq h, globalValuation, Option.bind_eq_bind,
    Option.bind_some]
  rfl

/-! ## Generic list facts -/

theorem mapM_getElem? {α β} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → ∀ i : Nat, l'[i]? = l[i]?.bind f
  | [], l', h, i => by simp at h; subst h; simp
  | x :: xs, l', h, i => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some bs =>
        simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases i with
        | zero => simp [hx]
        | succ i => simpa using mapM_getElem? hxs i

theorem filter_flatten_single {α} (P : α → Bool) : ∀ (gs : List (List α)) (i : Nat)
    (g : List α), gs[i]? = some g →
    (∀ j g', gs[j]? = some g' → j ≠ i → ∀ r ∈ g', P r = false) →
    gs.flatten.filter P = g.filter P
  | [], i, g, h, _ => by simp at h
  | h0 :: t, 0, g, h, hn => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have : t.flatten.filter P = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      obtain ⟨g', hg', hr'⟩ := List.mem_flatten.mp hr
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
      have := hn (j + 1) t[j] (by simp [hj]) (by omega) r hr'
      simp [this]
    simp [List.flatten_cons, List.filter_append, this]
  | h0 :: t, i + 1, g, h, hn => by
    simp only [List.getElem?_cons_succ] at h
    have h0f : h0.filter P = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      simp [hn 0 h0 rfl (by omega) r hr]
    rw [List.flatten_cons, List.filter_append, h0f, List.nil_append]
    exact filter_flatten_single P t i g h fun j g' hj hne => hn (j + 1) g' (by simpa using hj)
      (by omega)

theorem mapM_congr_mem {α β} {f g : α → Option β} : ∀ {l : List α},
    (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, List.mapM_cons, h x List.mem_cons_self,
      mapM_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-! ## Relocations of one unit -/

/-- The `slot` group of a successful `resolveRelocations` is the unit's
relocation list under `restrict` and `globalValuation`, and it is all the
relocations aimed at that unit's sections. -/
theorem resolveRelocations_slot {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {rels : List ResolvedRelocation}
    (h : resolveRelocations objects layout absolute = some rels) {slot : Nat}
    {object : ObjectFile} (ho : objects[slot]? = some object) :
    ∃ g, relocations object slot (restrict layout slot)
        (globalValuation objects layout absolute) = some g ∧
      ∀ k : SectionKey, k.object = slot → rels.filter (·.key == k) = g.filter (·.key == k) := by
  unfold resolveRelocations at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨groups, hgroups, rfl⟩ := h
  have hslot := mapM_getElem? hgroups slot
  rw [List.getElem?_zipIdx, ho] at hslot
  simp only [Option.map_some, Nat.zero_add, Option.bind_some] at hslot
  have hrel : relocations object slot (restrict layout slot)
      (globalValuation objects layout absolute) = groups[slot]? := by
    rw [hslot]
    unfold relocations
    apply mapM_congr_mem
    intro rel _
    simp only [sectionAt_of ho, addr_restrict, resolveIn_eq ho]
    rfl
  obtain ⟨g, -, hg⟩ := mapM_some_mem hgroups (object, slot)
    (List.mem_zipIdx_iff_getElem?.mpr (by simpa using ho))
  refine ⟨g, hrel.trans (hslot.trans hg), fun k hk => ?_⟩
  apply filter_flatten_single _ groups slot g (hslot.trans hg)
  intro j g' hj hne r hr
  have hjj := mapM_getElem? hgroups j
  rw [hj, List.getElem?_zipIdx] at hjj
  cases hoj : objects[j]? with
  | none => simp [hoj] at hjj
  | some oj =>
    simp only [hoj, Option.map_some, Nat.zero_add, Option.bind_some] at hjj
    obtain ⟨rel, -, hrel'⟩ := mapM_some_mem' hjj.symm r hr
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hrel'
    obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl⟩ := hrel'
    simp only [beq_eq_false_iff_ne]
    intro he
    exact hne (by rw [← hk, ← he])

/-! ## Sections of one unit -/

theorem linkSection_eq (objects : List ObjectFile) (rels : List ResolvedRelocation)
    (relocate : Relocator) (placement : Silmaril.Formats.ELF.Link.Placement) :
    linkSection objects rels relocate placement =
      (sectionAt objects placement.key).bind fun part => linkPart part rels relocate placement :=
  rfl

/-- A section-local relocator links a section the same way from any relocation
list that agrees on that section. -/
theorem linkPart_congr {relocate : Relocator} (hloc : SectionLocal relocate)
    {rels rels' : List ResolvedRelocation} {placement : Silmaril.Formats.ELF.Link.Placement}
    (h : rels.filter (·.key == placement.key) = rels'.filter (·.key == placement.key))
    (part : ObjectSection) :
    linkPart part rels relocate placement = linkPart part rels' relocate placement := by
  unfold linkPart
  rw [h, mapM_congr_mem (g := fun relocation => do
      let patch ← relocate rels' relocation part.data
      guard (patch.offset = relocation.offset ∧ 0 < patch.bytes.size)
      pure patch)]
  intro r hr
  have hk : r.key = placement.key := by simpa using (List.mem_filter.mp hr).2
  rw [hloc rels rels' r part.data (by rw [hk]; exact h)]

/-- `mapM` commutes with selecting the entries of one slot. -/
theorem mapM_filter_slot {F : Silmaril.Formats.ELF.Link.Placement → Option LinkedSection}
    {G : Nat × Nat → Option LinkedSection} {slot : Nat}
    (hkey : ∀ pl s, F pl = some s → s.key = pl.key) :
    ∀ {layout : Layout} {out : List LinkedSection},
    (∀ pl ∈ layout, pl.key.object = slot → F pl = G (pl.key.index, pl.address)) →
    layout.mapM F = some out →
    (restrict layout slot).mapM G = some (out.filter (·.key.object == slot))
  | [], out, _, h => by simp at h; subst h; rfl
  | pl :: rest, out, hFG, h => by
    rw [List.mapM_cons] at h
    cases hx : F pl with
    | none => simp [hx] at h
    | some s =>
      cases hxs : rest.mapM F with
      | none => simp [hx, hxs] at h
      | some ss =>
        simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        have ih := mapM_filter_slot hkey (fun q hq => hFG q (List.mem_cons_of_mem _ hq)) hxs
        have hs := hkey pl s hx
        by_cases ho : pl.key.object = slot
        · have hG : G (pl.key.index, pl.address) = some s := by
            rw [← hFG pl List.mem_cons_self ho, hx]
          simp only [restrict, List.filterMap_cons, ho, ite_true, List.mapM_cons] at ih ⊢
          simp [hG, ih, hs, ho]
        · simp only [restrict, List.filterMap_cons, ho, ite_false] at ih ⊢
          simp [ih, hs, ho]

/-! ## The commutation theorem -/

/-- **`link_eq_units`.** A successful link, restricted to the sections of object
`slot`, is exactly that object's TU-alone image under the placement and the
valuation the link induces. -/
theorem link_eq_units {accepts : Header → Bool} {relocate : Relocator}
    (hloc : SectionLocal relocate) {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) {slot : Nat}
    {object : ObjectFile} (ho : objects[slot]? = some object) :
    image object slot (restrict layout slot) (globalValuation objects layout absolute) relocate =
      some (out.filter (·.key.object == slot)) := by
  obtain ⟨-, rels, hrels, hsec, hpw⟩ := link_some h
  obtain ⟨g, hg, hfilt⟩ := resolveRelocations_slot hrels ho
  have hmap := mapM_filter_slot (F := linkSection objects rels relocate) (G := fun entry => do
      let part ← object.sections[entry.1]?
      linkPart part g relocate ⟨⟨slot, entry.1⟩, entry.2⟩)
    (fun pl s hs => by
      obtain ⟨_, _, -, -, -, -, -, hk⟩ := linkSection_some hs
      exact hk)
    (fun pl _ hpl => by
      obtain ⟨⟨o, i⟩, a⟩ := pl
      simp only at hpl
      rw [hpl, linkSection_eq, sectionAt_of ho]
      simp only
      congr 1
      funext part
      exact linkPart_congr hloc (hfilt _ rfl) part)
    hsec
  simp only [image, hg, Option.bind_eq_bind, Option.bind_some]
  simp only [bind, pure] at hmap ⊢
  rw [hmap]
  simp [List.Pairwise.filter _ hpw]

/-! ## Disjointness and coverage -/

theorem pairwise_mem_ne {α} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b
  | [], _, a, ha, _, _, _ => by simp at ha
  | x :: xs, h, a, ha, b, hb, hne => by
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact hx b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact hs _ _ (hx a ha')
      · exact pairwise_mem_ne hs hxs a ha' b hb' hne

theorem LinkedSection.disjoint_symm (s t : LinkedSection) (h : s.Disjoint t) : t.Disjoint s :=
  h.symm

/-- **`images_disjoint`.** The images of two different units of one link are
pairwise disjoint as address ranges. -/
theorem images_disjoint {accepts : Header → Bool} {relocate : Relocator}
    (hloc : SectionLocal relocate) {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) {i j : Nat}
    {oi oj : ObjectFile} (hi : objects[i]? = some oi) (hj : objects[j]? = some oj) (hij : i ≠ j) :
    ∃ imgI imgJ,
      image oi i (restrict layout i) (globalValuation objects layout absolute) relocate =
        some imgI ∧
      image oj j (restrict layout j) (globalValuation objects layout absolute) relocate =
        some imgJ ∧
      ∀ s ∈ imgI, ∀ t ∈ imgJ, s.Disjoint t := by
  refine ⟨_, _, link_eq_units hloc h hi, link_eq_units hloc h hj, fun s hs t ht => ?_⟩
  obtain ⟨-, -, -, -, hpw⟩ := link_some h
  simp only [List.mem_filter, beq_iff_eq] at hs ht
  exact pairwise_mem_ne LinkedSection.disjoint_symm hpw s hs.1 t ht.1
    (fun he => hij (by rw [← hs.2, ← ht.2, he]))

/-- Every linked section has an object behind it. -/
theorem link_key_object {accepts : Header → Bool} {relocate : Relocator}
    {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : link accepts relocate objects layout absolute = some out)
    {s : LinkedSection} (hs : s ∈ out) : ∃ object, objects[s.key.object]? = some object := by
  have hperm : (layout.map Silmaril.Formats.ELF.Link.Placement.key).Perm
      (allocatedSections objects) := by
    unfold link at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, hp, -⟩ := h
    by_contra hn
    simp [hn] at hp
  obtain ⟨-, rels, -, hsec, -⟩ := link_some h
  obtain ⟨pl, hpl, hls⟩ := mapM_some_mem' hsec s hs
  obtain ⟨_, _, -, -, -, -, -, hk⟩ := linkSection_some hls
  have hmem : s.key ∈ allocatedSections objects :=
    hperm.mem_iff.mp (List.mem_map.mpr ⟨pl, hpl, hk.symm⟩)
  simp only [allocatedSections, List.mem_flatMap, List.mem_filterMap] at hmem
  obtain ⟨⟨object, idx⟩, hz, part, -, hkey⟩ := hmem
  split at hkey
  · simp only [Option.some.injEq] at hkey
    rw [← hkey]
    exact ⟨object, List.mem_zipIdx_iff_getElem?.mp hz⟩
  · simp at hkey

/-- The linked image is covered by the unit images: every section of a
successful link belongs to the image of its own object. -/
theorem link_covered {accepts : Header → Bool} {relocate : Relocator}
    (hloc : SectionLocal relocate) {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) {s : LinkedSection}
    (hs : s ∈ out) : ∃ object img, objects[s.key.object]? = some object ∧
      image object s.key.object (restrict layout s.key.object)
        (globalValuation objects layout absolute) relocate = some img ∧ s ∈ img := by
  obtain ⟨object, ho⟩ := link_key_object h hs
  exact ⟨object, _, ho, link_eq_units hloc h ho, List.mem_filter.mpr ⟨hs, by simp⟩⟩

/-- Image inclusion at the byte level: what a unit's image holds at an address,
the linked image holds there too. -/
theorem contains_of_unit {accepts : Header → Bool} {relocate : Relocator}
    (hloc : SectionLocal relocate) {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) {slot : Nat}
    {object : ObjectFile} (ho : objects[slot]? = some object) {img : List LinkedSection}
    (himg : image object slot (restrict layout slot)
      (globalValuation objects layout absolute) relocate = some img)
    {a : Nat} {b : BitVec 8} (hc : Contains img a b) : Contains out a b := by
  rw [link_eq_units hloc h ho, Option.some.injEq] at himg
  subst himg
  obtain ⟨s, hs, hle, hb⟩ := hc
  exact ⟨s, (List.mem_filter.mp hs).1, hle, hb⟩

/-- The valuation sends a uniquely defined global to its owner's local address. -/
theorem globalValuation_owner {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {name : NameBytes} {slot : Nat} {object : ObjectFile}
    {symbol : ObjectSymbol} (ho : objects[slot]? = some object)
    (hd : globalDefinitions objects name = [(slot, symbol)])
    (ha : absolute.filter (fun entry => entry.1 == name) = []) :
    globalValuation objects layout absolute name =
      localValue object (restrict layout slot) symbol := by
  simp [globalValuation, hd, ha, localValue_eq ho]

end Silmaril.Machine.Link.Unit
