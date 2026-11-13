module

public import Silmaril.Machine.Link.Unit.Defs
public import Silmaril.Proofs.Machine.Link.Unit
public import Silmaril.Machine.Link.Abi.Thms

/-! # Translation units: theorems (header)

PROVED (`Silmaril.Proofs.Machine.Link.Unit`, standard axioms), for any
`SectionLocal` relocator and any successful imported `link`:

* `link_eq_units`: the linked sections of object `slot` are exactly
  `image object slot (restrict layout slot) (globalValuation objects layout absolute)`;
* `images_disjoint`: images of two different units are disjoint address ranges;
* `link_covered`: every linked section lies in the image of its own unit;
* `contains_of_unit`: a byte in a unit's image is in the linked image;
* `globalValuation_owner`: the valuation sends a uniquely defined global to its
  owner's unit-local address; plus the agreement lemmas `addr_restrict`,
  `localValue_eq`, `resolveIn_eq`, `resolveRelocations_slot`, `linkPart_congr`.

Here: the x86-64 relocator is `SectionLocal` (`x86_sectionLocal`); the
corollaries for the x86-64 profile (`x86_link_eq_units`, `x86_images_disjoint`)
and for ABI-checked unit lists (`linkUnits_eq_units`, which also returns
`Abi.AbiSound`); closed instances on the `Checks` ASTs (with the valuation
computed), negative tests (cross-ABI and untagged unit links rejected; the
image is `none` when `σ` leaves an import unvalued; `image_not_wellPlaced`
records that `image` does not yet reject empty or duplicated placements), and
on the real gcc fixture of `Silmaril.X86.Linking.Fixture`
(`fixture_units`, `fixture_images_disjoint`), which reuse its `linked` theorem
instead of re-running the ten-minute elaboration.
-/

@[expose] public section

namespace Silmaril.Machine.Link.Unit

universe u

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (Layout AbsoluteSymbols Relocator LinkedSection link)
open Silmaril.X86.Linking.Relocation (accepts relocate staticObject)

/-- The x86-64 profile computes each patch from the relocation alone. -/
theorem x86_sectionLocal : SectionLocal relocate := fun _ _ _ _ _ => rfl

theorem x86_link_some {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link objects layout absolute = some out) :
    link accepts relocate objects layout absolute = some out := by
  unfold Silmaril.X86.Linking.Relocation.link at h
  by_cases hs : (objects.all staticObject) = true
  · simpa [hs] using h
  · simp [hs] at h

theorem x86_link_eq_units {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link objects layout absolute = some out) {slot : Nat}
    {object : ObjectFile} (ho : objects[slot]? = some object) :
    image object slot (restrict layout slot) (globalValuation objects layout absolute) relocate =
      some (out.filter (·.key.object == slot)) :=
  link_eq_units x86_sectionLocal (x86_link_some h) ho

theorem x86_images_disjoint {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link objects layout absolute = some out) {i j : Nat}
    {oi oj : ObjectFile} (hi : objects[i]? = some oi) (hj : objects[j]? = some oj) (hij : i ≠ j) :
    ∃ imgI imgJ,
      image oi i (restrict layout i) (globalValuation objects layout absolute) relocate =
        some imgI ∧
      image oj j (restrict layout j) (globalValuation objects layout absolute) relocate =
        some imgJ ∧
      ∀ s ∈ imgI, ∀ t ∈ imgJ, s.Disjoint t :=
  images_disjoint x86_sectionLocal (x86_link_some h) hi hj hij

/-- `link_eq_units` for an ABI-checked link of units, together with the ABI
soundness of every binding. -/
theorem linkUnits_eq_units {Tag : Type} {Spec : Type u} [DecidableEq Tag] {accepts : Header → Bool}
    {relocate : Relocator} (hloc : SectionLocal relocate) {policy : Abi.Policy Tag}
    {units : List (TU Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection}
    (h : linkUnits accepts relocate policy units layout absolute = some out) :
    Abi.AbiSound policy (units.map TU.object) (units.map TU.iface) ∧
    ∀ slot (u : TU Tag Spec), units[slot]? = some u →
      u.image slot (restrict layout slot)
          (globalValuation (units.map TU.object) layout absolute) relocate =
        some (out.filter (·.key.object == slot)) := by
  obtain ⟨hc, -, hl⟩ := Abi.linkAbi_some h
  refine ⟨Abi.checkAbi_sound hc, fun slot u hu => ?_⟩
  exact link_eq_units hloc hl (by simp [hu])

/-! ## Closed instance: the `Checks` ASTs (valuation computed) -/

section Checks

open Silmaril.X86.Linking.Checks (caller callee)

/-- The placement the `Checks` layout gives each object. -/
theorem checks_restrict :
    restrict Silmaril.X86.Linking.Checks.layout 0 = [(1, 0x1000)] ∧
    restrict Silmaril.X86.Linking.Checks.layout 1 = [(1, 0x1020)] := ⟨rfl, rfl⟩

/-- The one valuation of that link sends `f` to the callee's section. -/
theorem checks_valuation :
    globalValuation [caller, callee] Silmaril.X86.Linking.Checks.layout [] [102] =
      some 0x1020 := rfl

/-- The caller alone, placed at `0x1000` with `f ↦ 0x1020`, already has its final
bytes (`call` displacement `0x20 + A - P`, A = 0). -/
theorem checks_caller_image :
    image caller 0 [(1, 0x1000)] (fun name => if name = [102] then some 0x1020 else none)
      relocate = some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩] := by decide

/-- Under another valuation the same unit gets other bytes: the image really
depends on `σ`. -/
theorem checks_caller_image' :
    image caller 0 [(1, 0x1000)] (fun name => if name = [102] then some 0x1100 else none)
      relocate = some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x00, 1, 0, 0]⟩] := by decide

theorem checks_link_eq_units :
    image caller 0 [(1, 0x1000)]
        (globalValuation [caller, callee] Silmaril.X86.Linking.Checks.layout []) relocate =
      some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩] ∧
    image callee 1 [(1, 0x1020)]
        (globalValuation [caller, callee] Silmaril.X86.Linking.Checks.layout []) relocate =
      some [⟨⟨1, 1⟩, 0x1020, 6, 1, #[0x90]⟩] :=
  ⟨(x86_link_eq_units Silmaril.X86.Linking.Checks.succeeds (slot := 0) rfl).trans rfl,
   (x86_link_eq_units Silmaril.X86.Linking.Checks.succeeds (slot := 1) rfl).trans rfl⟩

/-- The same link as ABI-tagged units (`sysv64` on both sides of `f`). -/
def callerTU : TU Abi.Conv String :=
  { object := caller, config := { defines := ["CALLER"] },
    imports := [⟨[102], .sysv64, "f returns"⟩] }

def calleeTU : TU Abi.Conv String :=
  { object := callee, exports := [⟨[102], .sysv64, "f returns"⟩] }

theorem checks_linkUnits :
    linkUnits accepts relocate Abi.Policy.exact [callerTU, calleeTU]
      Silmaril.X86.Linking.Checks.layout =
    some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩, ⟨⟨1, 1⟩, 0x1020, 6, 1, #[0x90]⟩] := by
  rfl

theorem checks_units_images :
    callerTU.image 0 [(1, 0x1000)]
        (globalValuation [caller, callee] Silmaril.X86.Linking.Checks.layout []) relocate =
      some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩] :=
  ((linkUnits_eq_units x86_sectionLocal checks_linkUnits).2 0 callerTU rfl).trans rfl

/-! ### Negative tests -/

/-- A cross-ABI unit link is rejected: the caller imports `f` as `sysv64`, the
callee exports it as `ms64`. -/
theorem checks_linkUnits_rejects_ms64 :
    linkUnits accepts relocate Abi.Policy.exact
      [callerTU, { calleeTU with exports := [⟨[102], .ms64, "f returns"⟩] }]
      Silmaril.X86.Linking.Checks.layout = none := by
  rfl

/-- An import with no tagged export is rejected. -/
theorem checks_linkUnits_rejects_untagged :
    linkUnits accepts relocate Abi.Policy.exact [callerTU, { calleeTU with exports := [] }]
      Silmaril.X86.Linking.Checks.layout = none := by
  rfl

/-- The image is partial in `σ`: with `f` unvalued the caller has no image. -/
theorem checks_caller_image_unvalued :
    image caller 0 [(1, 0x1000)] (fun _ => none) relocate = none := by decide

/-- **Known gap (no `WellPlaced` yet).** `image` does not check that `p` places
each allocated section exactly once. An empty placement of the callee is
accepted with an empty image, and a duplicated placement of the caller's `.text`
yields a second copy at `0x2000` whose `call` displacement was computed for the
first copy at `0x1000` (so it is not the bytes a link at `0x2000` would give,
compare `checks_caller_image'`). Statements quantified over all `p` (WP-L4
`Unit.Sat`) must assume a well-placedness predicate. -/
theorem image_not_wellPlaced :
    image callee 1 [] (fun _ => none) relocate = some [] ∧
    image caller 0 [(1, 0x1000), (1, 0x2000)]
        (fun name => if name = [102] then some 0x1020 else none) relocate =
      some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩, ⟨⟨0, 1⟩, 0x2000, 6, 4, #[0x20, 0, 0, 0]⟩] := by
  decide

end Checks

/-! ## Instance on the real gcc fixture -/

section Fixture

open Silmaril.X86.Linking.Fixture (object0 object1 expected)

/-- The two real gcc objects of the L1 fixture, parsed by the certified reader:
each one's TU-alone image, under the placement and valuation induced by the
link that `Fixture.linked` checks against GNU `ld`, is exactly its part of the
linked output. -/
theorem fixture_units :
    ∃ o0 o1, [object0, object1].mapM readObject = some [o0, o1] ∧
      image o0 0 [(3, 4096), (5, 4192)]
          (globalValuation [o0, o1] Silmaril.X86.Linking.Fixture.layout []) relocate =
        some (expected.take 2) ∧
      image o1 1 [(3, 4128), (4, 4160), (5, 4224)]
          (globalValuation [o0, o1] Silmaril.X86.Linking.Fixture.layout []) relocate =
        some (expected.drop 2) := by
  have h := Silmaril.X86.Linking.Fixture.linked
  unfold Silmaril.X86.Linking.Relocation.linkBytes at h
  cases h0 : readObject object0 with
  | none => simp [h0] at h
  | some o0 =>
    cases h1 : readObject object1 with
    | none => simp [h0, h1] at h
    | some o1 =>
      simp only [List.mapM_cons, List.mapM_nil, h0, h1, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def] at h
      refine ⟨o0, o1, by simp [h0, h1], ?_, ?_⟩
      · exact (x86_link_eq_units h (slot := 0) rfl).trans rfl
      · exact (x86_link_eq_units h (slot := 1) rfl).trans rfl

theorem fixture_images_disjoint :
    ∃ o0 o1, [object0, object1].mapM readObject = some [o0, o1] ∧
      ∀ s ∈ expected.take 2, ∀ t ∈ expected.drop 2, s.Disjoint t := by
  obtain ⟨o0, o1, hp, h0, h1⟩ := fixture_units
  refine ⟨o0, o1, hp, ?_⟩
  have h := Silmaril.X86.Linking.Fixture.linked
  unfold Silmaril.X86.Linking.Relocation.linkBytes at h
  simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
  obtain ⟨imgI, imgJ, hI, hJ, hd⟩ :=
    x86_images_disjoint h (i := 0) (j := 1) (oi := o0) (oj := o1) rfl rfl (by decide)
  rw [show restrict Silmaril.X86.Linking.Fixture.layout 0 = [(3, 4096), (5, 4192)] from rfl,
    h0, Option.some.injEq] at hI
  rw [show restrict Silmaril.X86.Linking.Fixture.layout 1 = [(3, 4128), (4, 4160), (5, 4224)]
    from rfl, h1, Option.some.injEq] at hJ
  subst hI hJ
  exact hd

end Fixture

end Silmaril.Machine.Link.Unit
