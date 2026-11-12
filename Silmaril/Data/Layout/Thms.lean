module

public import Silmaril.Data.Layout.Defs

/-!
# Layouts are well-formed

* `alignUp`: the next multiple (`dvd_alignUp`, `le_alignUp`).
* `place`: sequential placement is a `Chain` (members in order, disjoint), every member is
  aligned, and every member ends by `placeEnd` (`chain_place`, `place_aligned`,
  `place_end_le`); `Chain.pairwise` turns a chain into pairwise disjointness.
* `layoutTy_wf`: every computed shape of a well-formed data model (`DataModel.WF`) is
  well-formed (power-of-two alignment dividing the size).
* `declLayout_wf`: every computed struct or union layout is `DeclLayout.WF`: members in bounds,
  aligned, disjoint (structs), at offset zero (unions).
* The five data models are well-formed (`sysvX86_64_wf`, ...).

Open goals:
* `Task.bitfieldLayout`: bit-fields (`Field.bits`) are rejected by `layoutTy`; their psABI
  allocation (storage units of the declared type, no straddling, unnamed bit-fields do not
  affect alignment) and its well-formedness at bit granularity are pending.
-/

@[expose] public section

namespace Silmaril.Data.Layout

/-! ## `alignUp` and powers of two -/

theorem dvd_alignUp (n : Nat) {a : Nat} (ha : 0 < a) : a ∣ alignUp n a := by
  simp [alignUp, Nat.pos_iff_ne_zero.mp ha, Nat.dvd_mul_left]

theorem le_alignUp (n : Nat) {a : Nat} (ha : 0 < a) : n ≤ alignUp n a := by
  simp only [alignUp, Nat.pos_iff_ne_zero.mp ha, ite_false]
  have h1 := Nat.div_add_mod (n + a - 1) a
  have h2 := Nat.mod_lt (n + a - 1) ha
  rw [Nat.mul_comm] at h1
  generalize (n + a - 1) / a * a = q at *
  omega

theorem alignUp_one (n : Nat) : alignUp n 1 = n := by
  simp [alignUp]

theorem Pow2.pos {n : Nat} (h : Pow2 n) : 0 < n := by
  obtain ⟨k, rfl⟩ := h; exact Nat.two_pow_pos k

theorem Pow2.one : Pow2 1 := ⟨0, rfl⟩

theorem Pow2.dvd_of_le {a b : Nat} (ha : Pow2 a) (hb : Pow2 b) (h : a ≤ b) : a ∣ b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide)).mp h)

theorem Pow2.max {a b : Nat} (ha : Pow2 a) (hb : Pow2 b) : Pow2 (max a b) := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h]; exact hb
  · rw [Nat.max_eq_left h]; exact ha

theorem pow2_of_isPow2 {n : Nat} (h : isPow2 n = true) : Pow2 n := by
  simp only [isPow2, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨k, -, hk⟩ := h
  exact ⟨k, hk.symm⟩

/-! ## Sequential placement -/

theorem place_length (off : Nat) (ms : List Shape) : (place off ms).length = ms.length := by
  induction ms generalizing off with
  | nil => rfl
  | cons s ss ih => simp [place, ih]

theorem le_placeEnd (off : Nat) {ms : List Shape} (h : ∀ s ∈ ms, 0 < s.align) :
    off ≤ placeEnd off ms := by
  induction ms generalizing off with
  | nil => exact Nat.le_refl _
  | cons s ss ih =>
    simp only [placeEnd]
    have := le_alignUp off (h s (by simp))
    have := ih (alignUp off s.align + s.size) (fun t ht => h t (by simp [ht]))
    omega

theorem chain_place (off : Nat) {ms : List Shape} (h : ∀ s ∈ ms, 0 < s.align) :
    Chain off (place off ms) := by
  induction ms generalizing off with
  | nil => trivial
  | cons s ss ih =>
    exact ⟨le_alignUp off (h s (by simp)), ih _ (fun t ht => h t (by simp [ht]))⟩

theorem place_aligned (off : Nat) {ms : List Shape} (h : ∀ s ∈ ms, 0 < s.align) :
    ∀ t ∈ place off ms, t.align ∣ t.off := by
  induction ms generalizing off with
  | nil => simp [place]
  | cons s ss ih =>
    intro t ht
    simp only [place, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact dvd_alignUp off (h s (by simp))
    · exact ih _ (fun u hu => h u (by simp [hu])) t ht

theorem place_end_le (off : Nat) {ms : List Shape} (h : ∀ s ∈ ms, 0 < s.align) :
    ∀ t ∈ place off ms, t.off + t.size ≤ placeEnd off ms := by
  induction ms generalizing off with
  | nil => simp [place]
  | cons s ss ih =>
    intro t ht
    simp only [place, List.mem_cons] at ht
    have hs : ∀ u ∈ ss, 0 < u.align := fun u hu => h u (by simp [hu])
    rcases ht with rfl | ht
    · exact le_placeEnd _ hs
    · exact ih _ hs t ht

theorem place_shape (off : Nat) (ms : List Shape) :
    (place off ms).map (fun t => (t.size, t.align)) = ms.map (fun s => (s.size, s.align)) := by
  induction ms generalizing off with
  | nil => rfl
  | cons s ss ih => simp [place, ih]

theorem Chain.le_off {lo : Nat} {ss : List Slot} (h : Chain lo ss) : ∀ t ∈ ss, lo ≤ t.off := by
  induction ss generalizing lo with
  | nil => simp
  | cons s ss ih =>
    intro t ht
    obtain ⟨h1, h2⟩ := h
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact h1
    · have := ih h2 t ht; omega

theorem Chain.pairwise {lo : Nat} {ss : List Slot} (h : Chain lo ss) :
    ss.Pairwise fun s t => s.off + s.size ≤ t.off := by
  induction ss generalizing lo with
  | nil => exact .nil
  | cons s ss ih => exact .cons (fun t ht => h.2.le_off t ht) (ih h.2)

/-! ## Maximum alignment and size -/

theorem le_maxAlign {ms : List Shape} : ∀ s ∈ ms, s.align ≤ maxAlign ms := by
  induction ms with
  | nil => simp
  | cons s ss ih =>
    intro t ht
    simp only [List.mem_cons] at ht
    simp only [maxAlign]
    rcases ht with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih t ht) (Nat.le_max_right _ _)

theorem le_maxSize {ms : List Shape} : ∀ s ∈ ms, s.size ≤ maxSize ms := by
  induction ms with
  | nil => simp
  | cons s ss ih =>
    intro t ht
    simp only [List.mem_cons] at ht
    simp only [maxSize]
    rcases ht with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih t ht) (Nat.le_max_right _ _)

theorem pow2_maxAlign {ms : List Shape} (h : ∀ s ∈ ms, Pow2 s.align) : Pow2 (maxAlign ms) := by
  induction ms with
  | nil => exact Pow2.one
  | cons s ss ih => exact Pow2.max (h s (by simp)) (ih fun t ht => h t (by simp [ht]))

/-! ## Struct and union placement -/

/-- The record shape of a placement, and the facts about its slots. -/
structure PlaceWF (k : Kind) (r : Shape × List Slot) : Prop where
  shape : r.1.WF
  inBounds : ∀ t ∈ r.2, t.off + t.size ≤ r.1.size
  aligned : ∀ t ∈ r.2, t.align ∣ t.off
  alignDvd : ∀ t ∈ r.2, t.align ∣ r.1.align
  pow2 : ∀ t ∈ r.2, Pow2 t.align
  disjoint : k = .struct → r.2.Pairwise fun s t => s.off + s.size ≤ t.off
  unionZero : k = .union → ∀ t ∈ r.2, t.off = 0

theorem mem_place_align {off : Nat} {ms : List Shape} {t : Slot} (ht : t ∈ place off ms) :
    ∃ s ∈ ms, t.align = s.align ∧ t.size = s.size := by
  induction ms generalizing off with
  | nil => simp [place] at ht
  | cons s ss ih =>
    simp only [place, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨s, by simp, rfl, rfl⟩
    · obtain ⟨u, hu, h1, h2⟩ := ih ht
      exact ⟨u, by simp [hu], h1, h2⟩

theorem kindPlace_wf (k : Kind) {ms : List Shape} (h : ∀ s ∈ ms, Pow2 s.align) :
    PlaceWF k (kindPlace k ms) := by
  have hpos : ∀ s ∈ ms, 0 < s.align := fun s hs => (h s hs).pos
  have hmax := pow2_maxAlign h
  cases k with
  | struct =>
    simp only [kindPlace, structPlace]
    refine ⟨⟨hmax, dvd_alignUp _ hmax.pos⟩, ?_, place_aligned 0 hpos, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact Nat.le_trans (place_end_le 0 hpos t ht) (le_alignUp _ hmax.pos)
    · intro t ht
      obtain ⟨s, hs, ha, -⟩ := mem_place_align ht
      rw [ha]; exact Pow2.dvd_of_le (h s hs) hmax (le_maxAlign s hs)
    · intro t ht
      obtain ⟨s, hs, ha, -⟩ := mem_place_align ht
      rw [ha]; exact h s hs
    · intro _; exact (chain_place 0 hpos).pairwise
    · intro h; cases h
  | union =>
    simp only [kindPlace, unionPlace]
    refine ⟨⟨hmax, dvd_alignUp _ hmax.pos⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      simpa using Nat.le_trans (le_maxSize s hs) (le_alignUp _ hmax.pos)
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact Nat.dvd_zero _
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact Pow2.dvd_of_le (h s hs) hmax (le_maxAlign s hs)
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact h s hs
    · intro h; cases h
    · intro _ t ht
      simp only [List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      rfl

/-! ## Computed shapes -/

theorem memberAlign_pow2 {natural : Nat} {al : Option Nat} {a : Nat} (hn : Pow2 natural)
    (h : memberAlign natural al = .ok a) : Pow2 a := by
  cases al with
  | none => cases h; exact hn
  | some b =>
    simp only [memberAlign] at h
    split at h
    · cases h; exact Pow2.max hn (pow2_of_isPow2 (by assumption))
    · cases h

theorem fieldShapes_length {g : CTy → Except String Shape} {fs : List Field} {ms : List Shape}
    (h : fieldShapes g fs = .ok ms) : ms.length = fs.length := by
  induction fs generalizing ms with
  | nil => cases h; rfl
  | cons f fs ih =>
    simp only [fieldShapes] at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    cases h; simp [ih (by assumption)]

theorem fieldShapes_pow2 {g : CTy → Except String Shape}
    (hg : ∀ t s, g t = .ok s → Pow2 s.align) {fs : List Field} {ms : List Shape}
    (h : fieldShapes g fs = .ok ms) : ∀ m ∈ ms, Pow2 m.align := by
  induction fs generalizing ms with
  | nil => cases h; simp
  | cons f fs ih =>
    simp only [fieldShapes] at h
    split at h; · cases h
    split at h; · cases h
    rename_i s hs
    split at h; · cases h
    rename_i a ha
    split at h; · cases h
    rename_i ss hss
    cases h
    intro m hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact memberAlign_pow2 (hg _ _ hs) ha
    · exact ih hss m hm

theorem DataModel.WF.intOf {dm : DataModel} (hdm : dm.WF) {k : IntKind} {s : Shape}
    (h : dm.intOf k = .ok s) : s.WF := by
  simp only [DataModel.intOf] at h
  split at h
  · cases h; exact hdm.int _ _ (by assumption)
  · cases h

theorem DataModel.WF.floatOf {dm : DataModel} (hdm : dm.WF) {k : FloatKind} {s : Shape}
    (h : dm.floatOf k = .ok s) : s.WF := by
  simp only [DataModel.floatOf] at h
  split at h
  · cases h; exact hdm.float _ _ (by assumption)
  · cases h

/-- Every shape computed under a well-formed data model is well-formed. -/
theorem layoutTy_wf {dm : DataModel} (hdm : dm.WF) (env : Env) :
    ∀ (fuel : Nat) (t : CTy) (s : Shape), layoutTy dm env fuel t = .ok s → s.WF := by
  intro fuel
  induction fuel with
  | zero => intro t s h; simp [layoutTy] at h
  | succ fuel ih =>
    intro t s h
    have hg : ∀ t s, layoutTy dm env fuel t = .ok s → Pow2 s.align :=
      fun t s h => (ih t s h).pow2
    cases t with
    | void => simp [layoutTy] at h
    | bool => simp only [layoutTy] at h; cases h; exact hdm.bool
    | int k _ => exact hdm.intOf h
    | float k => exact hdm.floatOf h
    | ptr _ => simp only [layoutTy] at h; cases h; exact hdm.ptr
    | enum _ u =>
      cases u with
      | none => exact hdm.intOf h
      | some p => exact hdm.intOf h
    | array e n =>
      simp only [layoutTy] at h
      split at h
      · cases h
        rename_i s' hs'
        have := ih e s' hs'
        exact ⟨this.pow2, Nat.dvd_trans this.dvd (Nat.dvd_mul_left _ _)⟩
      · cases h
    | typedef _ t => exact ih t s h
    | struct tag =>
      simp only [layoutTy] at h
      split at h; · cases h
      split at h
      · cases h; exact (kindPlace_wf .struct (fieldShapes_pow2 hg (by assumption))).shape
      · cases h
    | union tag =>
      simp only [layoutTy] at h
      split at h; · cases h
      split at h
      · cases h; exact (kindPlace_wf .union (fieldShapes_pow2 hg (by assumption))).shape
      · cases h

/-! ## Computed declaration layouts -/

theorem declLayout_fields_slot {dm : DataModel} {env : Env} {d : Decl} {L : DeclLayout}
    (h : declLayout dm env d = .ok L) :
    ∃ ms, fieldShapes (layoutTy dm env defaultFuel) d.fields = .ok ms ∧
      L.kind = d.kind ∧ L.shape = (kindPlace d.kind ms).1 ∧
      L.fields.map PlacedField.slot = (kindPlace d.kind ms).2 := by
  simp only [declLayout] at h
  split at h
  · cases h
  · rename_i ms hms
    cases h
    refine ⟨ms, hms, rfl, rfl, ?_⟩
    have hlen : (kindPlace d.kind ms).2.length = d.fields.length := by
      rw [← fieldShapes_length hms]
      cases d.kind <;> simp [kindPlace, structPlace, unionPlace, place_length]
    rw [List.map_map]
    have : (PlacedField.slot ∘ fun (x : Field × Slot) =>
        ({ name := x.1.name, ty := x.1.ty, off := x.2.off, size := x.2.size,
           align := x.2.align } : PlacedField)) = Prod.snd := by
      funext x; rfl
    rw [this, List.map_snd_zip]
    omega

theorem mem_fields_slot {L : DeclLayout} {f : PlacedField} (hf : f ∈ L.fields) :
    f.slot ∈ L.fields.map PlacedField.slot := List.mem_map_of_mem hf

/-- Computed struct and union layouts are well-formed. -/
theorem declLayout_wf {dm : DataModel} (hdm : dm.WF) {env : Env} {d : Decl} {L : DeclLayout}
    (h : declLayout dm env d = .ok L) : L.WF := by
  obtain ⟨ms, hms, hk, hshape, hslots⟩ := declLayout_fields_slot h
  have hp := kindPlace_wf d.kind
    (fieldShapes_pow2 (fun t s h => (layoutTy_wf hdm env _ t s h).pow2) hms)
  generalize kindPlace d.kind ms = r at hp hshape hslots
  obtain ⟨sh, sl⟩ := r
  simp only at hshape hslots
  have mem : ∀ f ∈ L.fields, f.slot ∈ sl := fun f hf => hslots ▸ mem_fields_slot hf
  refine ⟨hshape ▸ hp.shape, fun f hf => hshape ▸ hp.inBounds _ (mem f hf),
    fun f hf => hp.aligned _ (mem f hf), fun f hf => hshape ▸ hp.alignDvd _ (mem f hf),
    fun f hf => hp.pow2 _ (mem f hf), ?_, ?_⟩
  · intro hs
    have := hp.disjoint (hk ▸ hs)
    rw [← hslots] at this
    exact List.pairwise_map.mp this
  · intro hu f hf
    exact hp.unionZero (hk ▸ hu) _ (mem f hf)

theorem pairwise_disjoint_of_ne {l : List PlacedField}
    (hp : l.Pairwise fun f g => f.off + f.size ≤ g.off)
    {f g : PlacedField} (hf : f ∈ l) (hg : g ∈ l) (hne : f ≠ g) :
    f.off + f.size ≤ g.off ∨ g.off + g.size ≤ f.off := by
  induction l with
  | nil => simp at hf
  | cons x xs ih =>
    rw [List.pairwise_cons] at hp
    simp only [List.mem_cons] at hf hg
    rcases hf with rfl | hf <;> rcases hg with rfl | hg
    · exact absurd rfl hne
    · exact .inl (hp.1 g hg)
    · exact .inr (hp.1 f hf)
    · exact ih hp.2 hf hg

/-- Distinct members of a well-formed struct layout occupy disjoint byte ranges. -/
theorem DeclLayout.WF.disjoint_of_ne {L : DeclLayout} (hL : L.WF) (hk : L.kind = .struct)
    {f g : PlacedField} (hf : f ∈ L.fields) (hg : g ∈ L.fields) (hne : f ≠ g) :
    f.off + f.size ≤ g.off ∨ g.off + g.size ≤ f.off :=
  pairwise_disjoint_of_ne (hL.disjoint hk) hf hg hne

theorem DeclLayout.mem_of_field? {L : DeclLayout} {name : String} {f : PlacedField}
    (h : L.field? name = some f) :
    f ∈ L.fields ∧ f.name = name := by
  simp only [DeclLayout.field?] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-! ## The data models are well-formed -/

theorem exactShape_wf {n : Nat} {s : Shape} (h : exactShape n = some s) : s.WF := by
  simp only [exactShape] at h
  split at h
  · cases h
    rename_i hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨⟨0, rfl⟩, Nat.dvd_refl _⟩
    · exact ⟨⟨1, rfl⟩, Nat.dvd_refl _⟩
    · exact ⟨⟨2, rfl⟩, Nat.dvd_refl _⟩
    · exact ⟨⟨3, rfl⟩, Nat.dvd_refl _⟩
  · cases h

private theorem wf_of (a k size : Nat) (h : a = 2 ^ k) (hd : a ∣ size) :
    (Shape.mk size a).WF := ⟨⟨k, h⟩, hd⟩

theorem sysvX86_64_wf : sysvX86_64.WF where
  int k s h := by
    cases k <;> simp only [sysvX86_64, Option.some.injEq] at h <;> (try subst h) <;>
      first
      | exact exactShape_wf h
      | exact wf_of 1 0 _ rfl (by decide) | exact wf_of 2 1 _ rfl (by decide)
      | exact wf_of 4 2 _ rfl (by decide) | exact wf_of 8 3 _ rfl (by decide)
      | exact wf_of 16 4 _ rfl (by decide)
  float k s h := by
    cases k <;> simp only [sysvX86_64, Option.some.injEq] at h <;> subst h <;>
      first
      | exact wf_of 4 2 _ rfl (by decide) | exact wf_of 8 3 _ rfl (by decide)
      | exact wf_of 16 4 _ rfl (by decide)
  ptr := wf_of 8 3 _ rfl (by decide)
  bool := wf_of 1 0 _ rfl (by decide)

theorem aapcs64_wf : aapcs64.WF :=
  ⟨sysvX86_64_wf.int, sysvX86_64_wf.float, sysvX86_64_wf.ptr, sysvX86_64_wf.bool⟩
theorem rv64Lp64_wf : rv64Lp64.WF :=
  ⟨sysvX86_64_wf.int, sysvX86_64_wf.float, sysvX86_64_wf.ptr, sysvX86_64_wf.bool⟩

theorem i386Ilp32_wf : i386Ilp32.WF where
  int k s h := by
    cases k with
    | exact n =>
      simp only [i386Ilp32] at h
      split at h
      · cases h; exact wf_of 4 2 _ rfl (by decide)
      · exact exactShape_wf h
    | _ =>
      simp only [i386Ilp32, Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;>
      first
      | exact wf_of 1 0 _ rfl (by decide) | exact wf_of 2 1 _ rfl (by decide)
      | exact wf_of 4 2 _ rfl (by decide)
  float k s h := by
    cases k <;> simp only [i386Ilp32, Option.some.injEq] at h <;> subst h <;>
      first
      | exact wf_of 4 2 _ rfl (by decide) | exact wf_of 16 4 _ rfl (by decide)
  ptr := wf_of 4 2 _ rfl (by decide)
  bool := wf_of 1 0 _ rfl (by decide)

theorem wasm32_wf : wasm32.WF where
  int k s h := by
    cases k <;> simp only [wasm32, Option.some.injEq] at h <;> (try subst h) <;>
      first
      | exact exactShape_wf h
      | exact wf_of 1 0 _ rfl (by decide) | exact wf_of 2 1 _ rfl (by decide)
      | exact wf_of 4 2 _ rfl (by decide) | exact wf_of 8 3 _ rfl (by decide)
      | exact wf_of 16 4 _ rfl (by decide)
  float k s h := by
    cases k <;> simp only [wasm32, Option.some.injEq] at h <;> subst h <;>
      first
      | exact wf_of 4 2 _ rfl (by decide) | exact wf_of 8 3 _ rfl (by decide)
      | exact wf_of 16 4 _ rfl (by decide)
  ptr := wf_of 4 2 _ rfl (by decide)
  bool := wf_of 1 0 _ rfl (by decide)

/-! ## Data models with the same layout -/

section Congr
variable {dm dm' : DataModel} (h : dm.SameLayout dm') (env : Env)
include h

theorem intOf_congr : dm.intOf = dm'.intOf := by
  funext k; simp [DataModel.intOf, h.int]

theorem floatOf_congr : dm.floatOf = dm'.floatOf := by
  funext k; simp [DataModel.floatOf, h.float]

theorem layoutTy_congr : layoutTy dm env = layoutTy dm' env := by
  funext fuel
  induction fuel with
  | zero => funext t; rfl
  | succ fuel ih =>
    funext t
    cases t with
    | enum tag u => cases u <;> simp only [layoutTy, intOf_congr h, h.enumRepr]
    | _ => first | rfl | simp only [layoutTy, ih, intOf_congr h, floatOf_congr h, h.ptr, h.bool]

theorem declLayout_congr : declLayout dm env = declLayout dm' env := by
  funext d; simp only [declLayout, layoutTy_congr h]

theorem tagLayout_congr : tagLayout dm env = tagLayout dm' env := by
  funext k tag; simp only [tagLayout, declLayout_congr h]

theorem resolve_congr : resolve dm env = resolve dm' env := by
  funext t p
  induction p generalizing t with
  | nil => simp only [resolve, layoutTy_congr h]
  | cons st p ih =>
    cases st <;> simp only [resolve, layoutTy_congr h, tagLayout_congr h, ih]

end Congr

theorem aapcs64_sameLayout : aapcs64.SameLayout sysvX86_64 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem rv64Lp64_sameLayout : rv64Lp64.SameLayout sysvX86_64 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- AAPCS64 and the RISC-V LP64 psABI lay out every C declaration exactly as System V x86-64
(the formats of `long double` differ, its size and alignment do not). -/
theorem declLayout_aapcs64 (env : Env) : declLayout aapcs64 env = declLayout sysvX86_64 env :=
  declLayout_congr aapcs64_sameLayout env

theorem declLayout_rv64Lp64 (env : Env) : declLayout rv64Lp64 env = declLayout sysvX86_64 env :=
  declLayout_congr rv64Lp64_sameLayout env

/-! ## Open goals -/

/-- Bit-fields: psABI allocation of `Field.bits` members (System V x86-64 §3.1.2, AAPCS64
§10.1.8, RISC-V psABI: storage units of the declared type, no straddling of a unit,
zero-width fields align to the next unit, unnamed bit-fields do not affect alignment) and
its well-formedness at bit granularity. `layoutTy` currently rejects bit-fields.
The examples are GCC's x86-64 placements (bit offset, width) and record shapes. -/
def Task.bitfieldLayout : Prop :=
  ∃ place : DataModel → Env → List Field → Option (List (Nat × Nat) × Shape),
    (∀ dm env fs r, place dm env fs = some r →
      (r.1.Pairwise fun a b => a.1 + a.2 ≤ b.1) ∧ ∀ x ∈ r.1, x.1 + x.2 ≤ 8 * r.2.size) ∧
    place sysvX86_64 [] [⟨"a", .int .int .unsigned, none, some 3⟩,
      ⟨"b", .int .int .unsigned, none, some 30⟩] = some ([(0, 3), (32, 30)], ⟨8, 4⟩) ∧
    place sysvX86_64 [] [⟨"a", .int .char .plain, none, none⟩,
      ⟨"b", .int .int .signed, none, some 4⟩] = some ([(0, 8), (8, 4)], ⟨4, 4⟩)

end Silmaril.Data.Layout
