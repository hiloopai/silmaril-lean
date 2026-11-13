module

public import Silmaril.Cerberus.Mem.IntSlots.Defs

/-! # Integer objects of every width in the concrete memory

`IntSlots` for every integer type `ity` with a fixed layout (`integerLayout ity = some (w, sg)`:
every integer type but enumerations, whose width comes from the tags): a C local of type
`ity` is a `w`-byte, `w`-aligned object (`layout_tyType`). Allocation (`allocate_ty`),
access, store of a value in the type's representation range (`store_ty`), load (`load_ty`)
and kill (`kill_ty`) of a live, writable, non-atomic `w`-byte object, for every annotation of
the type and every tag environment. With `ity = int` these are the lemmas of `IntSlots`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Mem.Concrete

/-- The integer type `ity`, with any annotations. -/
def tyType (ann : List Annot) (ity : IntegerType) : Ctype := .mk ann (.basic (.integer ity))

/-- A fixed layout is not an enumeration's, so the tags do not change it. -/
theorem registeredIntegerLayout_of {ity : IntegerType} {w : Nat} {sg : Bool}
    (h : integerLayout ity = some (w, sg)) (tags : Tags) :
    registeredIntegerLayout tags ity = some (w, sg) := by
  cases ity <;> simp_all [registeredIntegerLayout, registeredInteger, integerLayout]

theorem registeredInteger_of {ity : IntegerType} {w : Nat} {sg : Bool}
    (h : integerLayout ity = some (w, sg)) (tags : Tags) :
    registeredInteger tags ity = some ity := by
  cases ity <;> simp_all [registeredInteger, integerLayout]

theorem layout_tyType {ity : IntegerType} {w : Nat} {sg : Bool}
    (h : integerLayout ity = some (w, sg)) (tags : Tags) (ann : List Annot) :
    typeLayout 64 tags (tyType ann ity) = .ok ⟨w, w, []⟩ := by
  simp [typeLayout, tyType, registeredIntegerLayout_of h tags]
  rfl

/-- The address of the next allocation of a `w`-byte, `w`-aligned object. -/
def nextAddress (s : State) (w : Nat) : Int :=
  (s.lastAddress - w) - (s.lastAddress - w) % w

/-- A fresh `ity` object is allocated below every earlier one, with unspecified bytes. -/
theorem allocate_ty {ity : IntegerType} {w : Nat} {sg : Bool} (h : integerLayout ity = some (w, sg))
    (hw : 0 < w) (tags : Tags) (ann : List Annot) (s : State) (hpos : 0 < nextAddress s w) :
    allocateTyped tags s w (tyType ann ity) = .ok (.allocated s.nextId (nextAddress s w),
      { writeRepresentation (nextAddress s w) (plainBytes (List.replicate w none)) s with
        nextId := s.nextId + 1
        lastAddress := nextAddress s w
        allocations := s.allocations.insert s.nextId
          ({base := nextAddress s w, size := w, objectType := some (tyType ann ity)} : Allocation)
        lastUsed := some s.nextId }) := by
  unfold nextAddress at hpos ⊢
  have hn : ¬ (s.lastAddress - w - (s.lastAddress - w) % w ≤ 0) := by omega
  have hw' : ¬ ((w : Int) ≤ 0) := by omega
  simp only [allocateTyped, layout_tyType h tags ann, bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right_of_eq_false _ _ (by simpa using hw'), ite_eq_right_of_eq_false _ _ (by simpa using hn)]
  rw [show ((w : Int)).toNat = w from by simp]
  obtain ⟨b, pb, hs⟩ := writeRepresentation_shape (s.lastAddress - w - (s.lastAddress - w) % w)
    (plainBytes (List.replicate w none)) s
  simp only [hs]
  simp [tyType]

/-- A live, non-atomic, writable `w`-byte object at `addr`. -/
structure LiveSz (s : State) (id addr : Int) (w : Nat) : Prop where
  alive : id ∉ s.dead
  found : ∃ a, s.allocations.lookup id = some a ∧ a.base = addr ∧ a.size = w ∧ a.atomic = false ∧
    a.readonly = none

theorem LiveSz.of_int {s : State} {id addr : Int} (h : LiveInt s id addr) : LiveSz s id addr 4 :=
  ⟨h.alive, h.found⟩

theorem LiveSz.int {s : State} {id addr : Int} (h : LiveSz s id addr 4) : LiveInt s id addr :=
  ⟨h.alive, h.found⟩

theorem access_ty {ity : IntegerType} {w : Nat} {sg : Bool} (hl : integerLayout ity = some (w, sg))
    (tags : Tags) (ann : List Annot) {s : State} {id addr : Int} (h : LiveSz s id addr w) :
    accessTyped tags s (tyType ann ity) (.allocated id addr) = .ok (id, addr, w) := by
  obtain ⟨alive, a, look, base, size, atomic, _⟩ := h
  simp [accessTyped, layout_tyType hl tags ann, alive, look, base, size, checkAtomic, atomic, bind,
    Except.bind, pure, Except.pure]

/-- A value is representable in the `w` bytes of a type of signedness `sg`. -/
def InRange (w : Nat) (sg : Bool) (n : Int) : Prop :=
  (representationBounds w sg).1 ≤ n ∧ n ≤ (representationBounds w sg).2

theorem store_ty {ity : IntegerType} {w : Nat} {sg : Bool} (hl : integerLayout ity = some (w, sg))
    (tags : Tags) (ann : List Annot) {s : State} {id addr : Int} (h : LiveSz s id addr w) {n : Int}
    (hn : InRange w sg n) :
    storeTyped tags s (tyType ann ity) (.allocated id addr) (.integer ity n) =
      .ok ((addr, w), {writeRepresentation addr (plainBytes (encodeInteger w n)) s with
        lastUsed := some id}) := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := h
  obtain ⟨lo, hi⟩ := hn
  have hr : represent 64 tags (.integer ity n) s = .ok (plainBytes (encodeInteger w n), s) := by
    simp only [represent, registeredIntegerLayout_of hl tags]
    simp [lo, hi, pure, Except.pure]
  simp [storeTyped, access_ty hl tags ann ⟨alive, a, look, base, size, atomic, ro⟩, checkWritable,
    look, ro, hr, bind, Except.bind, pure, Except.pure, plainBytes, encodeInteger_length]

theorem kill_ty {ity : IntegerType} {w : Nat} {sg : Bool} (hl : integerLayout ity = some (w, sg))
    (tags : Tags) (ann : List Annot) {s : State} {id addr : Int} (h : LiveSz s id addr w) :
    killTyped tags s (tyType ann ity) (.allocated id addr) =
      .ok ((), { s with
        allocations := s.allocations.erase id
        dead := id :: s.dead
        lastUsed := some id }) := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := h
  simp [killTyped, access_ty hl tags ann ⟨alive, a, look, base, size, atomic, ro⟩, look, base,
    bind, Except.bind, pure, Except.pure]

/-- No pointer-copy metadata on the object's `w` bytes. -/
def PlainSz (s : State) (addr : Int) (w : Nat) : Prop :=
  ∀ i : Nat, i < w → s.pointerBytes.lookup (addr + i) = none

theorem exposeReadBytes_plain {s : State} {addr : Int} {w : Nat} (h : PlainSz s addr w) :
    exposeReadBytes s addr w = s := by
  unfold exposeReadBytes
  suffices ∀ (l : List Int), (∀ i ∈ l, s.pointerBytes.lookup (addr + i) = none) →
      ∀ s' : State, s'.pointerBytes = s.pointerBytes →
      l.foldl (fun (s : State) (i : Int) => match (s.pointerBytes.lookup (addr+i)).bind (·.1) with
        | none => s
        | some id => match s.allocations.lookup id with
          | none => s
          | some a => {s with allocations := s.allocations.insert id {a with exposed := true}}) s' = s' by
    refine this _ (fun i hi => ?_) s rfl
    simp at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact h j hj
  intro l
  induction l with
  | nil => intro _ s' _; rfl
  | cons i l ih =>
    intro hl s' hs'
    rw [List.foldl_cons]
    have hi : s'.pointerBytes.lookup (addr + i) = none := by
      rw [hs']; exact hl i (by simp)
    rw [hi]
    exact ih (fun j hj => hl j (by simp [hj])) s' hs'

/-- The signed reading of the unsigned decoding of an in-range value is the value. -/
theorem signed_decode {w : Nat} {sg : Bool} {n : Int} (hn : InRange w sg n) :
    (if sg && n % 256 ^ w ≥ 256 ^ w / 2 then n % 256 ^ w - 256 ^ w else n % 256 ^ w) = n := by
  obtain ⟨lo, hi⟩ := hn
  have pos : (0 : Int) < 256 ^ w := by positivity
  have even : (256 : Int) ^ w / 2 * 2 = 256 ^ w ∨ w = 0 := by
    cases w with
    | zero => right; rfl
    | succ w => left; rw [pow_succ]; omega
  cases sg
  · simp only [representationBounds, Bool.false_eq_true, ↓reduceIte] at lo hi
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact Int.emod_eq_of_lt lo (by omega)
  · simp only [representationBounds, ↓reduceIte] at lo hi
    simp only [Bool.true_and, ge_iff_le, decide_eq_true_eq]
    rcases even with even | rfl
    · generalize (256 : Int) ^ w = M at *
      by_cases hneg : n < 0
      · have e : n % M = n + M := by
          rw [Int.emod_eq_add_self_emod]
          exact Int.emod_eq_of_lt (by omega) (by omega)
        rw [e, ite_eq_left (by omega)]
        ring
      · have e : n % M = n := Int.emod_eq_of_lt (by omega) (by omega)
        rw [e, ite_eq_right (by omega)]
    · simp at lo hi ⊢
      omega

theorem load_ty {ity : IntegerType} {w : Nat} {sg : Bool} (hl : integerLayout ity = some (w, sg))
    (tags : Tags) (ann : List Annot) {s : State} {id addr : Int} (h : LiveSz s id addr w)
    (plain : PlainSz s addr w) {n : Int} (hn : InRange w sg n)
    (bytes : fetchBytes w addr s.bytes = encodeInteger w n) :
    loadTyped tags s (tyType ann ity) (.allocated id addr) =
      .ok (.integer ity n, {s with lastUsed := some id}) := by
  have hdec : decodeInteger (fetchBytes w addr s.bytes) = some (n % 256 ^ w) := by
    rw [bytes]; exact decode_encode w n
  have hexp : exposeRead 64 tags s (tyType ann ity) addr = s := by
    simp only [exposeRead, tyType, registeredIntegerLayout_of hl tags]
    exact exposeReadBytes_plain plain
  have habs : abstractValue 64 tags s (tyType ann ity) addr = .ok (.integer ity n) := by
    have hlay := layout_tyType hl tags ann
    unfold tyType at hlay ⊢
    simp only [abstractValue, hlay, bind, Except.bind, pure, Except.pure,
      registeredIntegerLayout_of hl tags]
    simp only [show ((w : Int)).toNat = w from by simp, hdec]
    rw [signed_decode hn]
  unfold loadTyped
  rw [access_ty hl tags ann h]
  simp only [bind, Except.bind, habs, hexp, pure, Except.pure]

end Silmaril.Cerberus.Mem.Concrete
