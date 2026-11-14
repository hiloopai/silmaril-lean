module

public import Silmaril.Machine.Link.Contract.Defs
public import Silmaril.Proofs.Machine.Link.Unit
public import Silmaril.Proofs.Machine.Link.Abi

/-! # Composition of TU contracts across a link

PROVED here (standard axioms):

* `restrict_wellPlaced`: after a successful link, the placement `restrict layout
  slot` places every allocated section of object `slot` exactly once;
* `globalValuation_export`: after a successful link, the valuation of a name
  that object `slot` defines is that unit's own address for it
  (`TU.exportAddr` under `restrict layout slot`), connecting L3's
  `globalValuation_owner` to `TU.exportAddr`;
* `image_congr_valuation`: a unit's image depends on `σ` only through the
  names the unit leaves undefined;
* `link_compose`: per-unit `TU.Sat`, a successful link, ABI compatibility and
  closed imports give every export spec, for every step index, in every context
  extending the linked image. Cyclic imports are allowed: the proof is induction
  on the step index, so there is no acyclicity hypothesis;
* `ownershipDisjoint_of_link`.
-/

@[expose] public section

namespace Silmaril.Machine.Link.Contract

universe u

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (SectionKey Layout AbsoluteSymbols ResolvedRelocation Relocator
  LinkedSection allocated definitionValue globalDefinitions addressAt sectionAt link
  allocatedSections)
open Silmaril.Machine.Link.Unit

/-! ## Well-placedness of `restrict` -/

/-- The section-index projection of `restrict`. -/
def slotIndex (slot : Nat) (key : SectionKey) : Option Nat :=
  if key.object = slot then some key.index else none

theorem restrict_map_fst (layout : Layout) (slot : Nat) :
    (restrict layout slot).map Prod.fst =
      (layout.map Silmaril.Formats.ELF.Link.Placement.key).filterMap (slotIndex slot) := by
  induction layout with
  | nil => rfl
  | cons q qs ih =>
    by_cases h : q.key.object = slot
    · simp [restrict, slotIndex, h] at ih ⊢; exact ih
    · simp [restrict, slotIndex, h] at ih ⊢; exact ih

theorem flatMap_zipIdx_single {α β} (H : α → List β) :
    ∀ (l : List α) (k slot : Nat) (x : α), k ≤ slot → l[slot - k]? = some x →
      (l.zipIdx k).flatMap (fun q => if q.2 = slot then H q.1 else []) = H x
  | [], _, _, _, _, h => by simp at h
  | y :: ys, k, slot, x, hk, h => by
    rw [List.zipIdx_cons, List.flatMap_cons]
    by_cases hs : k = slot
    · subst hs
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [ite_true]
      suffices hz : (ys.zipIdx (k + 1)).flatMap
          (fun q => if q.2 = k then H q.1 else []) = [] by rw [hz, List.append_nil]
      rw [List.flatMap_eq_nil_iff]
      intro q hq
      have := (List.mem_zipIdx hq).1
      simp only [ite_eq_right_iff]; omega
    · simp only [hs, ite_false, List.nil_append]
      apply flatMap_zipIdx_single H ys (k + 1) slot x (by omega)
      rw [show slot - k = (slot - (k + 1)) + 1 by omega] at h
      simpa using h

theorem allocatedSections_slot {objects : List ObjectFile} {slot : Nat} {object : ObjectFile}
    (ho : objects[slot]? = some object) :
    (allocatedSections objects).filterMap (slotIndex slot) = allocatedIndices object := by
  unfold allocatedSections
  rw [List.filterMap_flatMap]
  have : ∀ q : ObjectFile × Nat,
      (q.1.sections.zipIdx.filterMap fun (part, sectionIndex) =>
        if allocated part then some (⟨q.2, sectionIndex⟩ : SectionKey) else none).filterMap
          (slotIndex slot) =
      if q.2 = slot then allocatedIndices q.1 else [] := by
    intro q
    rw [List.filterMap_filterMap]
    by_cases hq : q.2 = slot
    · simp only [hq, ite_true, allocatedIndices]
      congr 1; funext r
      by_cases ha : allocated r.1 <;> simp [ha, slotIndex]
    · simp only [hq, ite_false, List.filterMap_eq_nil_iff]
      intro r _
      by_cases ha : allocated r.1 <;> simp [ha, slotIndex, hq]
  simp only [this]
  exact flatMap_zipIdx_single allocatedIndices objects 0 slot object (Nat.zero_le _)
    (by simpa using ho)

/-- The layout facts a successful `link` checks. -/
theorem link_layout {accepts : Header → Bool} {relocate : Relocator} {objects : List ObjectFile}
    {layout : Layout} {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) :
    (layout.map Silmaril.Formats.ELF.Link.Placement.key).Perm (allocatedSections objects) := by
  unfold link at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, hp, -⟩ := h
  by_contra hn
  simp [hn] at hp

/-- **`restrict_wellPlaced`.** -/
theorem restrict_wellPlaced {accepts : Header → Bool} {relocate : Relocator}
    {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : link accepts relocate objects layout absolute = some out)
    {slot : Nat} {object : ObjectFile} (ho : objects[slot]? = some object) :
    WellPlaced object (restrict layout slot) := by
  rw [WellPlaced, restrict_map_fst]
  refine ⟨?_, ?_⟩
  · refine List.Nodup.filterMap ?_ (link_some h).1
    intro a a' b ha ha'
    simp only [slotIndex, Option.mem_def] at ha ha'
    split at ha <;> split at ha' <;> simp_all
    cases a; cases a'; simp_all
  · rw [← allocatedSections_slot ho]
    exact (link_layout h).filterMap _

/-! ## The valuation of an exported name is the exporter's own address -/

/-- The strong global definitions `link` checks for duplicates. -/
def definedSymbols (objects : List ObjectFile) : List ObjectSymbol :=
  objects.flatMap (fun object => object.symbols.filter fun symbol =>
    symbol.binding == 1 && symbol.raw.sectionIndex != 0)

/-- The symbol facts a successful `link` checks: unique strong global names, none
of them also an absolute symbol. -/
theorem link_defined {accepts : Header → Bool} {relocate : Relocator}
    {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : link accepts relocate objects layout absolute = some out) :
    ((definedSymbols objects).map ObjectSymbol.name).Nodup ∧
    (definedSymbols objects).all
      (fun symbol => !(absolute.any fun pair => pair.1 == symbol.name)) = true := by
  unfold link at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, h5, _, h6, -⟩ := h
  refine ⟨?_, ?_⟩
  · by_contra hn; simp only [definedSymbols] at hn; simp [hn] at h5
  · by_contra hn; simp only [definedSymbols] at hn; simp [hn] at h6

theorem map_snd_flatMap_zipIdx {α β} (F : α → List β) :
    ∀ (l : List α) (k : Nat),
      ((l.zipIdx k).flatMap (fun q => (F q.1).map ((q.2, ·) : β → Nat × β))).map Prod.snd =
        l.flatMap F := by
  intro l
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    rw [List.zipIdx_cons, List.flatMap_cons, List.map_append, ih, List.flatMap_cons]
    simp

theorem length_le_one_of_nodup {α} {c : α} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, x = c) → l.length ≤ 1
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: _, hn, hc => by
    exfalso
    have ha := hc a (by simp)
    have hb := hc b (by simp)
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    exact hn.1.1 (ha.trans hb.symm)

theorem globalDefinitions_single {accepts : Header → Bool} {relocate : Relocator}
    {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : link accepts relocate objects layout absolute = some out)
    {name : NameBytes} {slot : Nat} {symbol : ObjectSymbol}
    (hmem : (slot, symbol) ∈ globalDefinitions objects name) :
    globalDefinitions objects name = [(slot, symbol)] := by
  have hsnd : (globalDefinitions objects name).map Prod.snd =
      (definedSymbols objects).filter (fun s => s.name == name) := by
    unfold globalDefinitions definedSymbols
    rw [List.filter_flatMap]
    have := map_snd_flatMap_zipIdx (fun object : ObjectFile =>
      object.symbols.filter fun symbol =>
        symbol.binding == 1 && symbol.raw.sectionIndex != 0 && symbol.name == name) objects 0
    rw [this]
    congr 1; funext object
    rw [List.filter_filter]
    congr 1; funext s
    simp [Bool.and_comm]
  have hlen : (globalDefinitions objects name).length ≤ 1 := by
    rw [← List.length_map (f := Prod.snd), hsnd, ← List.length_map (f := ObjectSymbol.name)]
    apply length_le_one_of_nodup (c := name)
    · exact (link_defined h).1.sublist (List.filter_sublist.map _)
    · intro x hx
      simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hx
      obtain ⟨s, ⟨-, hs⟩, rfl⟩ := hx
      exact hs
  generalize globalDefinitions objects name = L at hmem hlen ⊢
  match L, hlen with
  | [], _ => simp at hmem
  | [x], _ => simp only [List.mem_singleton] at hmem; rw [hmem]

/-- **`globalValuation_export`.** In a successful link, the one valuation sends a
global that unit `u` (at `slot`) defines to `u`'s own unit-local address for it. -/
theorem globalValuation_export {Tag : Type} {Spec : Type u} {accepts : Header → Bool}
    {relocate : Relocator} {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) {slot : Nat}
    {u : TU Tag Spec} (ho : objects[slot]? = some u.object) {name : NameBytes}
    (hd : name ∈ Abi.definedGlobals u.object) :
    globalValuation objects layout absolute name = u.exportAddr (restrict layout slot) name := by
  simp only [Abi.definedGlobals, List.mem_map, List.mem_filter] at hd
  obtain ⟨sym, ⟨hsym, hp⟩, rfl⟩ := hd
  obtain ⟨sym0, hfind⟩ : ∃ sym0, u.object.symbols.find? (fun symbol =>
      symbol.binding == 1 && symbol.raw.sectionIndex != 0 && symbol.name == sym.name) =
      some sym0 := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    exact ⟨sym, hsym, by simp only [Bool.and_eq_true] at hp ⊢; simp [hp]⟩
  have hmem0 := List.mem_of_find?_eq_some hfind
  have hp0 := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hp0
  have hgd : (slot, sym0) ∈ globalDefinitions objects sym.name := by
    simp only [globalDefinitions, List.mem_flatMap, List.mem_map, List.mem_filter]
    refine ⟨(u.object, slot), List.mem_zipIdx_iff_getElem?.mpr ho, sym0, ⟨hmem0, ?_⟩, rfl⟩
    simp [hp0]
  have hobj : u.object ∈ objects := List.mem_of_getElem? ho
  have hdef : sym0 ∈ definedSymbols objects := by
    simp only [definedSymbols, List.mem_flatMap, List.mem_filter]
    exact ⟨u.object, hobj, hmem0, by simp [hp0.1.1, hp0.1.2]⟩
  have habs : absolute.filter (fun entry => entry.1 == sym.name) = [] := by
    have := List.all_eq_true.mp (link_defined h).2 sym0 hdef
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at this
    rw [List.filter_eq_nil_iff]
    intro e he; simpa [hp0.2] using this e he
  rw [globalValuation_owner ho (globalDefinitions_single h hgd) habs]
  simp [TU.exportAddr, hfind]

/-! ## Locality in the valuation -/

/-- A unit's image depends on `σ` only through the names it leaves undefined. -/
theorem image_congr_valuation {object : ObjectFile} {slot : Nat} {p : Placement}
    {σ σ' : Valuation} {relocate : Relocator}
    (hσ : ∀ name ∈ Abi.undefinedGlobals object, σ name = σ' name) :
    image object slot p σ relocate = image object slot p σ' relocate := by
  have hres : ∀ k, resolveIn object p σ k = resolveIn object p σ' k := by
    intro k
    unfold resolveIn
    cases hs : object.symbols[k]? with
    | none => rfl
    | some symbol =>
      by_cases hund : symbol.raw.sectionIndex = 0 ∧ symbol.binding = 1 ∧ symbol.name ≠ []
      · have he : σ symbol.name = σ' symbol.name := by
          apply hσ
          simp only [Abi.undefinedGlobals, List.mem_map, List.mem_filter]
          refine ⟨symbol, ⟨List.mem_of_getElem? hs, ?_⟩, rfl⟩
          simp [hund.1, hund.2.1, hund.2.2]
        simp [he]
      · by_cases hi : symbol.raw.sectionIndex ≠ 0
        · simp [hi]
        · have hg' : ¬ (symbol.binding = 1 ∧ symbol.name ≠ []) := fun hb =>
            hund ⟨by simpa using hi, hb⟩
          simp [hg']
  have hrel : relocations object slot p σ = relocations object slot p σ' := by
    unfold relocations
    congr 1; funext r
    simp only [hres]
  unfold image
  rw [hrel]

/-! ## Flag-aware image inclusion -/

theorem Extends.refl (img : Image) : Extends img img := fun _ _ _ h => h

theorem Extends.trans {a b c : Image} (h₁ : Extends a b) (h₂ : Extends b c) : Extends a c :=
  fun x y f h => h₂ x y f (h₁ x y f h)

/-- Sublists extend: every section of `small` is a section of `big`. -/
theorem Extends.of_subset {small big : Image} (h : ∀ s ∈ small, s ∈ big) : Extends small big := by
  rintro a b f ⟨s, hs, hf, hle, hb⟩
  exact ⟨s, h s hs, hf, hle, hb⟩

/-- A unit's image is included, flags and all, in the linked image. -/
theorem extends_of_unit {accepts : Header → Bool} {relocate : Relocator}
    (hloc : SectionLocal relocate) {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) {slot : Nat}
    {object : ObjectFile} (ho : objects[slot]? = some object) {img : List LinkedSection}
    (himg : image object slot (restrict layout slot)
      (globalValuation objects layout absolute) relocate = some img) : Extends img out := by
  rw [link_eq_units hloc h ho, Option.some.injEq] at himg
  subst himg
  exact Extends.of_subset fun s hs => (List.mem_filter.mp hs).1

/-! ## Composition -/

variable {Tag : Type} {Spec : Type u}

/-- Under the ABI check, every export a unit declares is a global it defines. -/
theorem exports_defined [DecidableEq Tag] {policy : Abi.Policy Tag} {units : List (TU Tag Spec)}
    (habi : AbiCompatible policy units) {slot : Nat} {u : TU Tag Spec}
    (hu : units[slot]? = some u) {e : Entry Tag Spec} (he : e ∈ u.exports) :
    e.name ∈ Abi.definedGlobals u.object := by
  have hann := Abi.annotates_of_check habi (i := slot) (object := u.object) (iface := u.iface)
    (by simp [hu]) (by simp [hu])
  simp only [Abi.Interface.annotates, Abi.tags, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem] at hann
  exact hann.1.1.2 (e.name, e.tag) (by simp [TU.iface]; exact ⟨e, he, rfl, rfl⟩)

/-- **`link_compose`.** Per-unit relocation-parametric contracts, a successful
link of the units' objects, ABI compatibility and closed imports give every
export's spec at its address in the linked layout, for every step index, in
every context that extends the linked image and in which the assumed externals
are safe. Imports may be cyclic (mutual recursion across units): the proof is
induction on the step index and `TU.Sat` relies on imports one step later. -/
theorem link_compose [DecidableEq Tag] {L : Logic Spec} {accepts : Header → Bool}
    {relocate : Relocator} (hloc : SectionLocal relocate) {policy : Abi.Policy Tag}
    {units : List (TU Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection}
    (hlink : link accepts relocate (units.map TU.object) layout absolute = some out)
    (habi : AbiCompatible policy units) (hsat : ∀ u ∈ units, u.Sat L relocate)
    {ext : List (Entry Tag Spec)} (hclosed : ImportsClosed L units ext) {ctx : Image}
    (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a,
      globalValuation (units.map TU.object) layout absolute x.name = some a →
        L.Safe n a x.spec ctx) :
    ∀ (n slot : Nat) (u : TU Tag Spec), units[slot]? = some u → ∀ e ∈ u.exports, ∀ a,
      u.exportAddr (restrict layout slot) e.name = some a → L.Safe n a e.spec ctx := by
  intro n
  induction n with
  | zero => intros; exact L.zero _ _ _
  | succ n ih =>
    intro slot u hu e he a ha
    have ho : (units.map TU.object)[slot]? = some u.object := by simp [hu]
    have himg := link_eq_units hloc hlink ho
    refine hsat u (List.mem_of_getElem? hu) slot _ _ _ (restrict_wellPlaced hlink ho) himg n ctx
      ((extends_of_unit hloc hlink ho himg).trans hctx) ?_ e he a ha
    intro i hi a' hσ
    rcases hclosed u (List.mem_of_getElem? hu) i hi with
      ⟨slot', v, hv, e', he', hname, hsub⟩ | ⟨x, hx, hname, hsub⟩
    · have hov : (units.map TU.object)[slot']? = some v.object := by simp [hv]
      rw [← hname, globalValuation_export hlink hov (exports_defined habi hv he')] at hσ
      exact L.sub hsub (ih slot' v hv e' he' a' hσ)
    · rw [← hname] at hσ
      exact L.sub hsub (hext x hx n a' hσ)

/-- `link_compose` stated at the link's one valuation `σ*`: every export spec
holds at `σ* e.name`. -/
theorem link_compose_valuation [DecidableEq Tag] {L : Logic Spec} {accepts : Header → Bool}
    {relocate : Relocator} (hloc : SectionLocal relocate) {policy : Abi.Policy Tag}
    {units : List (TU Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection}
    (hlink : link accepts relocate (units.map TU.object) layout absolute = some out)
    (habi : AbiCompatible policy units) (hsat : ∀ u ∈ units, u.Sat L relocate)
    {ext : List (Entry Tag Spec)} (hclosed : ImportsClosed L units ext) {ctx : Image}
    (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a,
      globalValuation (units.map TU.object) layout absolute x.name = some a →
        L.Safe n a x.spec ctx) :
    ∀ (n slot : Nat) (u : TU Tag Spec), units[slot]? = some u → ∀ e ∈ u.exports, ∀ a,
      globalValuation (units.map TU.object) layout absolute e.name = some a →
        L.Safe n a e.spec ctx := by
  intro n slot u hu e he a ha
  have ho : (units.map TU.object)[slot]? = some u.object := by simp [hu]
  rw [globalValuation_export hlink ho (exports_defined habi hu he)] at ha
  exact link_compose hloc hlink habi hsat hclosed hctx hext n slot u hu e he a ha

/-- The ABI-checked unit link (`Unit.linkUnits`) supplies both the link and
`AbiCompatible`. -/
theorem linkUnits_compose [DecidableEq Tag] {L : Logic Spec} {accepts : Header → Bool}
    {relocate : Relocator} (hloc : SectionLocal relocate) {policy : Abi.Policy Tag}
    {units : List (TU Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection}
    (hlink : linkUnits accepts relocate policy units layout absolute = some out)
    (hsat : ∀ u ∈ units, u.Sat L relocate)
    {ext : List (Entry Tag Spec)} (hclosed : ImportsClosed L units ext) {ctx : Image}
    (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a,
      globalValuation (units.map TU.object) layout absolute x.name = some a →
        L.Safe n a x.spec ctx) :
    ∀ (n slot : Nat) (u : TU Tag Spec), units[slot]? = some u → ∀ e ∈ u.exports, ∀ a,
      globalValuation (units.map TU.object) layout absolute e.name = some a →
        L.Safe n a e.spec ctx := by
  obtain ⟨hc, -, hl⟩ := Abi.linkAbi_some hlink
  exact link_compose_valuation hloc hl hc hsat hclosed hctx hext

/-- Ownership disjointness is a consequence of a successful link. -/
theorem ownershipDisjoint_of_link {accepts : Header → Bool} {relocate : Relocator}
    {units : List (TU Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection}
    (hlink : link accepts relocate (units.map TU.object) layout absolute = some out) :
    OwnershipDisjoint units out := by
  intro slot u _ s hs hso _ t ht hto
  obtain ⟨-, -, -, -, hpw⟩ := link_some hlink
  exact pairwise_mem_ne LinkedSection.disjoint_symm hpw s hs t ht
    (fun he => hto (by rw [← he, hso]))

/-- A unit whose exports are safe in its own image, without relying on its
imports, satisfies its contract (by `Logic.frame`). -/
theorem _root_.Silmaril.Machine.Link.Unit.TU.Sat.of_frame {L : Logic Spec} {relocate : Relocator}
    {u : TU Tag Spec}
    (h : ∀ slot p σ img, WellPlaced u.object p → u.image slot p σ relocate = some img →
      ∀ n, ∀ e ∈ u.exports, ∀ a, u.exportAddr p e.name = some a → L.Safe (n + 1) a e.spec img) :
    u.Sat L relocate := by
  intro slot p σ img hp himg n ctx hctx _ e he a ha
  exact L.frame hctx (h slot p σ img hp himg n e he a ha)

end Silmaril.Machine.Link.Contract
