module

public import Silmaril.X86.Link.Contract.Defs
public import Silmaril.X86.Link.Unit.Thms
import Silmaril.Proofs.X86.Link.Compose

/-! # Contracts of translation units: theorems (header)

PROVED (`Silmaril.Proofs.X86.Link.Compose`, standard axioms), for any program
logic `L : Logic Spec`, any `SectionLocal` relocator and any successful link of
the imported linker:

* `link_compose`: if every unit satisfies `TU.Sat`, the units are
  `AbiCompatible`, and `ImportsClosed` holds (every import served, up to
  `L.Sub`, by some unit's export or by an assumed external that is safe in the
  context), then every export of every unit is `L.Safe n` at its address in the
  linked layout, for **every** `n`, in every context extending the linked image.
  Cyclic imports (mutual recursion across units) are covered: the proof is
  induction on the step index, there is no acyclicity hypothesis, and so no
  `Task.link_compose_cyclic` is needed. The acyclic case is a special case;
* `link_compose_valuation`, `linkUnits_compose`: the same conclusion at the
  link's one valuation `σ*`, and for the ABI-checked `Unit.linkUnits`;
* `restrict_wellPlaced`: after a successful link, `restrict layout slot` is
  `WellPlaced` (closes the gap `image_not_wellPlaced` for the placements
  `link_compose` uses);
* `globalValuation_export`: the valuation of a name a unit defines is that
  unit's `TU.exportAddr` under `restrict` (connects `TU.exportAddr` to
  `globalValuation_owner`);
* `exports_defined`: under `AbiCompatible`, every declared export is a defined
  global of its object;
* `image_congr_valuation`: an image depends on `σ` only on the unit's undefined
  globals (locality in the valuation);
* `ownershipDisjoint_of_link`: `OwnershipDisjoint` follows from a successful
  link, so it is not a hypothesis of `link_compose`;
* `TU.Sat.of_frame`: a unit whose exports are safe in its own image satisfies
  its contract (by `Logic.frame`);
* flag-aware inclusion: `Extends` keeps section flags (`ContainsF`);
  `Extends.contains` (byte-level inclusion), `Extends.refl`, `Extends.trans`,
  `Extends.of_subset`, `extends_of_unit`.

Assumed: nothing beyond the hypotheses stated. Not covered here: a validator of
`ld` output (`validate_sound`), relocatable partial links (`ld -r`), and the
semantic content of ownership (other units not writing owned memory), which
belongs to the instantiated logic.
-/

@[expose] public section

namespace Silmaril.X86.Link.Contract

open Silmaril.Formats.ELF.Link (link_some)
universe u
open Silmaril.Formats.ELF hiding Image
open Silmaril.Formats.ELF.Link (SectionKey Layout AbsoluteSymbols ResolvedRelocation Relocator
  LinkedSection allocated definitionValue globalDefinitions addressAt sectionAt link
  allocatedSections)
open Silmaril.X86.Link.Unit

/-- **`restrict_wellPlaced`.** -/
theorem restrict_wellPlaced {accepts : Header → Bool} {relocate : Relocator}
    {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : link accepts relocate objects layout absolute = some out)
    {slot : Nat} {object : ObjectFile} (ho : objects[slot]? = some object) :
    WellPlaced object (restrict layout slot) :=
  Proofs.X86.Link.Compose.restrict_wellPlaced h ho

/-- **`globalValuation_export`.** In a successful link, the one valuation sends a
global that unit `u` (at `slot`) defines to `u`'s own unit-local address for it. -/
theorem globalValuation_export {Tag : Type} {Spec : Type u} {accepts : Header → Bool}
    {relocate : Relocator} {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) {slot : Nat}
    {u : TU Tag Spec} (ho : objects[slot]? = some u.object) {name : NameBytes}
    (hd : name ∈ Abi.definedGlobals u.object) :
    globalValuation objects layout absolute name = u.exportAddr (restrict layout slot) name :=
  Proofs.X86.Link.Compose.globalValuation_export h ho hd

/-- A unit's image depends on `σ` only through the names it leaves undefined. -/
theorem image_congr_valuation {object : ObjectFile} {slot : Nat} {p : Placement}
    {σ σ' : Valuation} {relocate : Relocator}
    (hσ : ∀ name ∈ Abi.undefinedGlobals object, σ name = σ' name) :
    image object slot p σ relocate = image object slot p σ' relocate :=
  Proofs.X86.Link.Compose.image_congr_valuation hσ

theorem Extends.refl (img : Image) : Extends img img :=
  Proofs.X86.Link.Compose.Extends.refl img

theorem Extends.trans {a b c : Image} (h₁ : Extends a b) (h₂ : Extends b c) : Extends a c :=
  Proofs.X86.Link.Compose.Extends.trans h₁ h₂

/-- Sublists extend: every section of `small` is a section of `big`. -/
theorem Extends.of_subset {small big : Image} (h : ∀ s ∈ small, s ∈ big) : Extends small big :=
  Proofs.X86.Link.Compose.Extends.of_subset h

/-- A unit's image is included, flags and all, in the linked image. -/
theorem extends_of_unit {accepts : Header → Bool} {relocate : Relocator}
    (hloc : SectionLocal relocate) {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) {slot : Nat}
    {object : ObjectFile} (ho : objects[slot]? = some object) {img : List LinkedSection}
    (himg : image object slot (restrict layout slot)
      (globalValuation objects layout absolute) relocate = some img) : Extends img out :=
  Proofs.X86.Link.Compose.extends_of_unit hloc h ho himg

variable {Tag : Type} {Spec : Type u}

/-- Under the ABI check, every export a unit declares is a global it defines. -/
theorem exports_defined [DecidableEq Tag] {policy : Abi.Policy Tag} {units : List (TU Tag Spec)}
    (habi : AbiCompatible policy units) {slot : Nat} {u : TU Tag Spec}
    (hu : units[slot]? = some u) {e : Entry Tag Spec} (he : e ∈ u.exports) :
    e.name ∈ Abi.definedGlobals u.object :=
  Proofs.X86.Link.Compose.exports_defined habi hu he

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
      u.exportAddr (restrict layout slot) e.name = some a → L.Safe n a e.spec ctx :=
  Proofs.X86.Link.Compose.link_compose hloc hlink habi hsat hclosed hctx hext

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
        L.Safe n a e.spec ctx :=
  Proofs.X86.Link.Compose.link_compose_valuation hloc hlink habi hsat hclosed hctx hext

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
        L.Safe n a e.spec ctx :=
  Proofs.X86.Link.Compose.linkUnits_compose hloc hlink hsat hclosed hctx hext

/-- Ownership disjointness is a consequence of a successful link. -/
theorem ownershipDisjoint_of_link {accepts : Header → Bool} {relocate : Relocator}
    {units : List (TU Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection}
    (hlink : link accepts relocate (units.map TU.object) layout absolute = some out) :
    OwnershipDisjoint units out :=
  Proofs.X86.Link.Compose.ownershipDisjoint_of_link hlink

/-- A unit whose exports are safe in its own image, without relying on its
imports, satisfies its contract (by `Logic.frame`). -/
theorem TU.Sat.of_frame {L : Logic Spec} {relocate : Relocator}
    {u : TU Tag Spec}
    (h : ∀ slot p σ img, WellPlaced u.object p → u.image slot p σ relocate = some img →
      ∀ n, ∀ e ∈ u.exports, ∀ a, u.exportAddr p e.name = some a → L.Safe (n + 1) a e.spec img) :
    u.Sat L relocate :=
  Proofs.X86.Link.Compose.TU.Sat.of_frame h

end Silmaril.X86.Link.Contract
