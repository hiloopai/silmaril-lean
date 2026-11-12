module
public import Silmaril.Formats.PER.Defs

public section
namespace Silmaril.Formats.PER
variable {α β : Type}

@[ext] theorem ext {R S : PER α} (h : ∀ x y, R.rel x y ↔ S.rel x y) : R = S := by
  cases R with
  | mk rel laws =>
    cases S with
    | mk rel' laws' =>
      have hr : rel = rel' := funext fun x => funext fun y => propext (h x y)
      cases hr
      rfl

instance : LE (PER α) := ⟨Sub⟩

instance : PartialOrder (PER α) where
  le_refl _ := by intro x y h; exact h
  le_trans _ _ _ h k := by intro x y hx; exact k (h hx)
  le_antisymm _ _ h k := ext fun _ _ => ⟨fun hx => h hx, fun hx => k hx⟩

theorem ofDecoder_eq_ofRelation (decode : α → Option β) :
    ofDecoder decode = ofRelation (Silmaril.EncRel.ofDecoder decode) := by
  apply ext
  intro x y
  change (Silmaril.EncRel.ofDecoder decode).same x y ↔
    (Silmaril.EncRel.ofDecoder decode).per x y
  rw [(Silmaril.EncRel.ofDecoder_functional decode).per_eq_same]

theorem dom_left (R : PER α) {x y : α} (h : R.rel x y) : R.Dom x :=
  R.laws.trans h (R.laws.symm h)

theorem dom_right (R : PER α) {x y : α} (h : R.rel x y) : R.Dom y :=
  R.dom_left (R.laws.symm h)

@[simp] theorem ofDecoder_dom (decode : α → Option β) (x : α) :
    (ofDecoder decode).Dom x ↔ ∃ a, decode x = some a := by
  constructor
  · rintro ⟨a, h, _⟩; exact ⟨a, h⟩
  · rintro ⟨a, h⟩; exact ⟨a, h, h⟩

theorem list_length {R : PER α} {xs ys : List α} (h : R.list.rel xs ys) :
    xs.length = ys.length := h.length_eq

theorem restrict_sub (R : PER α) (selected : α → Prop) : (R.restrict selected).Sub R := by
  intro x y h
  exact h.2.2

theorem Canonical.rel_iff {R : PER α} (C : Canonical R) (x y : α) :
    C.per.rel x y ↔ C.selected x ∧ x = y := by
  constructor
  · rintro ⟨hx, hy, hr⟩
    obtain ⟨z, _, unique⟩ := C.representative x (C.supported x hx)
    exact ⟨hx, (unique x ⟨hx, C.supported x hx⟩).trans (unique y ⟨hy, hr⟩).symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, hx, C.supported x hx⟩

/-- A correct total encoder is a section of a partial decoder; its image is
therefore a transversal of the decoder PER. This theorem is conditional on
the actual roundtrip law, rather than treating an encoding option as proof. -/
def Canonical.ofCodec (decode : α → Option β) (encode : β → α)
    (roundtrip : ∀ a, decode (encode a) = some a) : Canonical (ofDecoder decode) where
  selected x := ∃ a, encode a = x
  supported := by
    rintro x ⟨a, rfl⟩
    exact ⟨a, roundtrip a, roundtrip a⟩
  representative := by
    intro x hx
    obtain ⟨a, ha⟩ := (ofDecoder_dom decode x).mp hx
    refine ⟨encode a, ⟨⟨a, rfl⟩, a, ha, roundtrip a⟩, ?_⟩
    rintro y ⟨⟨b, rfl⟩, c, hc, hc'⟩
    have hca : c = a := Option.some.inj (hc.symm.trans ha)
    have hbc : b = c := Option.some.inj ((roundtrip b).symm.trans hc')
    exact congrArg encode (hbc.trans hca)

/-- Sections likewise select canonical CSTs or event streams of an AST
projection. No injectivity of that projection is required. -/
def Canonical.ofSection (project : α → β) (section_ : β → α)
    (roundtrip : ∀ b, project (section_ b) = b) : Canonical (kernel project) where
  selected x := ∃ b, section_ b = x
  supported _ _ := rfl
  representative := by
    intro x _
    refine ⟨section_ (project x), ⟨⟨project x, rfl⟩, (roundtrip _).symm⟩, ?_⟩
    rintro y ⟨⟨b, rfl⟩, h⟩
    change project x = project (section_ b) at h
    rw [roundtrip] at h
    exact congrArg section_ h.symm

/-- The representative exists mathematically; this uses choice and does not
claim that canonicalization is computable. -/
noncomputable def Canonical.normalize {R : PER α} (C : Canonical R)
    (x : {x // R.Dom x}) : {x // C.selected x} :=
  ⟨(C.representative x.val x.property).choose,
    (C.representative x.val x.property).choose_spec.1.1⟩

theorem Canonical.normalize_related {R : PER α} (C : Canonical R)
    (x : {x // R.Dom x}) : R.rel x.val (C.normalize x).val :=
  (C.representative x.val x.property).choose_spec.1.2

theorem Canonical.normalize_eq_iff {R : PER α} (C : Canonical R)
    (x y : {x // R.Dom x}) : C.normalize x = C.normalize y ↔ R.rel x.val y.val := by
  constructor
  · intro h
    have hx := C.normalize_related x
    have hy := C.normalize_related y
    rw [h] at hx
    exact R.laws.trans hx (R.laws.symm hy)
  · intro h
    apply Subtype.ext
    obtain ⟨z, _, unique⟩ := C.representative x.val x.property
    exact (unique _ ⟨(C.normalize x).property, C.normalize_related x⟩).trans
      (unique _ ⟨(C.normalize y).property, R.laws.trans h (C.normalize_related y)⟩).symm

/-- The selected representatives are exactly the original equivalence classes. -/
noncomputable def Canonical.classEquiv {R : PER α} (C : Canonical R) :
    R.Quotient ≃ {x // C.selected x} where
  toFun := _root_.Quotient.lift C.normalize (fun x y h =>
    (C.normalize_eq_iff x y).mpr h)
  invFun x := _root_.Quotient.mk _ ⟨x.val, C.supported x.val x.property⟩
  left_inv := by
    intro q
    induction q using _root_.Quotient.inductionOn with
    | _ x => exact _root_.Quotient.sound (R.laws.symm (C.normalize_related x))
  right_inv := by
    intro x
    apply Subtype.ext
    obtain ⟨z, _, unique⟩ := C.representative x.val (C.supported x.val x.property)
    exact (unique _ ⟨(C.normalize ⟨x.val, C.supported x.val x.property⟩).property,
      C.normalize_related ⟨x.val, C.supported x.val x.property⟩⟩).trans
      (unique _ ⟨x.property, C.supported x.val x.property⟩).symm
end Silmaril.Formats.PER
