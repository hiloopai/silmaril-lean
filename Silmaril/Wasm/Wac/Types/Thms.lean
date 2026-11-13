module

public import Silmaril.Wasm.Wac.Types.Defs

/-!
# WAC subtyping: the checker decides the relation; a preorder; merging

* `sub_iff : sub a b = true ↔ Sub a b`: the checker is sound and complete.
* `Sub.refl`, `Sub.trans`: subtyping is a preorder.
* `merge_lower`: for instances whose exports are all flat (functions, values,
  resources and their type definitions, which is every WIT interface), the merge of
  two implicit-import kinds is a common subtype of both, so the merged import is a
  valid argument of every instantiation that asked for it.
* `merge_not_lower`: without flatness this fails: wac keeps the *larger* of two
  comparable nested instance exports, which is not a subtype of the smaller one.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

/-! ## Size bounds -/

theorem sizeOf_lt_of_mem {k : String} {a : Kind} {as : Externs} (h : (k, a) ∈ as) :
    sizeOf a < sizeOf as := by
  have h1 : sizeOf (k, a) < sizeOf as := List.sizeOf_lt_of_mem h
  have h2 : sizeOf a < sizeOf (k, a) := by simp; omega
  omega

/-! ## Lists of named items -/

theorem anyMatch_iff (as : Externs) (k : String) (b : Kind) :
    anyMatch as k b = true ↔ ∃ a, (k, a) ∈ as ∧ sub a b = true := by
  induction as with
  | nil => simp [anyMatch]
  | cons p as ih =>
    obtain ⟨k', a⟩ := p
    by_cases hk : k' = k
    · subst hk; simp [anyMatch, ih]
    · simp [anyMatch, ih, hk, Ne.symm hk]

theorem subEx_iff (as bs : Externs) :
    subEx as bs = true ↔ ∀ p ∈ bs, ∃ a, (p.1, a) ∈ as ∧ sub a p.2 = true := by
  induction bs with
  | nil => simp [subEx]
  | cons p bs ih =>
    obtain ⟨k, b⟩ := p
    simp [subEx, ih, anyMatch_iff]

theorem SubEx_iff (as bs : Externs) :
    SubEx as bs ↔ ∀ p ∈ bs, ∃ a, (p.1, a) ∈ as ∧ Sub a p.2 := by
  induction bs with
  | nil => exact ⟨fun _ => by simp, fun _ => .nil as⟩
  | cons p bs ih =>
    obtain ⟨k, b⟩ := p
    constructor
    · intro h
      cases h with
      | cons hm hs hr =>
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨_, hm, hs⟩
        · exact ih.1 hr p hp
    · intro h
      have h0 : ∃ a, (k, a) ∈ as ∧ Sub a b := h (k, b) (by simp)
      have h1 : SubEx as bs := ih.2 fun p hp => h p (by simp [hp])
      obtain ⟨a, hm, hs⟩ := h0
      exact .cons hm hs h1

/-! ## Inversion -/

theorem Sub.inst_iff {i j : Option String} {as bs : Externs} :
    Sub (.inst i as) (.inst j bs) ↔ SubEx as bs :=
  ⟨fun h => by cases h; assumption, .inst⟩

theorem Sub.comp_iff {i j : Option String} {ai ae bi be : Externs} :
    Sub (.comp i ai ae) (.comp j bi be) ↔ SubEx bi ai ∧ SubEx ae be :=
  ⟨fun h => by cases h; exact ⟨by assumption, by assumption⟩, fun h => .comp h.1 h.2⟩

theorem Sub.type_iff {a b : Kind} : Sub (.type a) (.type b) ↔ Sub a b :=
  ⟨fun h => by cases h; assumption, .type⟩

/-- Pointwise transport of an equivalence of `sub` and `Sub` to named items. -/
theorem subEx_iff_SubEx {as bs : Externs}
    (h : ∀ k k' a b, (k, a) ∈ as → (k', b) ∈ bs → (sub a b = true ↔ Sub a b)) :
    subEx as bs = true ↔ SubEx as bs := by
  rw [subEx_iff, SubEx_iff]
  refine forall_congr' fun p => forall_congr' fun hp => exists_congr fun a => ?_
  exact and_congr_right fun ha => h _ _ _ _ ha hp

/-! ## The checker decides the relation -/

theorem sub_func_iff (s s' : Wit.Binary.Sig) : sub (.func s) (.func s') = true ↔ Sub (.func s) (.func s') :=
  ⟨fun h => by rw [show s' = s by simpa [sub, eq_comm] using h]; exact .func s,
    fun h => by cases h; simp [sub]⟩

theorem sub_value_iff (t t' : Wit.Binary.Ty) : sub (.value t) (.value t') = true ↔ Sub (.value t) (.value t') :=
  ⟨fun h => by rw [show t' = t by simpa [sub, eq_comm] using h]; exact .value t,
    fun h => by cases h; simp [sub]⟩

theorem sub_resource_iff (r r' : String) :
    sub (.resource r) (.resource r') = true ↔ Sub (.resource r) (.resource r') :=
  ⟨fun h => by rw [show r' = r by simpa [sub, eq_comm] using h]; exact .resource r,
    fun h => by cases h; simp [sub]⟩

/-- The named-items step of the size induction. -/
theorem subEx_iff_sized (n : Nat) (ih : ∀ a b : Kind, sizeOf a + sizeOf b ≤ n → (sub a b = true ↔ Sub a b))
    (as bs : Externs) (h : sizeOf as + sizeOf bs < n) : subEx as bs = true ↔ SubEx as bs :=
  subEx_iff_SubEx fun _ _ x y hx hy => ih x y (by
    have := sizeOf_lt_of_mem hx; have := sizeOf_lt_of_mem hy; omega)

theorem sub_iff_le (n : Nat) : ∀ a b : Kind, sizeOf a + sizeOf b ≤ n → (sub a b = true ↔ Sub a b) := by
  induction n with
  | zero => intro a b h; cases a <;> simp at h
  | succ n ih =>
    intro a b hab
    cases a <;> cases b
    case func.func s s' => exact sub_func_iff s s'
    case value.value t t' => exact sub_value_iff t t'
    case resource.resource r r' => exact sub_resource_iff r r'
    case type.type a b =>
      rw [Sub.type_iff, ← ih a b (by simp at hab; omega), sub]
    case inst.inst i as j bs =>
      rw [Sub.inst_iff, sub]; exact subEx_iff_sized n ih as bs (by simp at hab; omega)
    case comp.comp i ai ae j bi be =>
      rw [Sub.comp_iff, sub, Bool.and_eq_true]
      exact and_congr (subEx_iff_sized n ih bi ai (by simp at hab; omega))
        (subEx_iff_sized n ih ae be (by simp at hab; omega))
    all_goals exact ⟨fun h => by simp [sub] at h, fun h => by cases h⟩

/-- **The subtype checker decides subtyping.** -/
theorem sub_iff (a b : Kind) : sub a b = true ↔ Sub a b := sub_iff_le _ a b (Nat.le_refl _)

instance (a b : Kind) : Decidable (Sub a b) := decidable_of_iff _ (sub_iff a b)

/-! ## A preorder -/

theorem Sub.refl_le (n : Nat) : ∀ a : Kind, sizeOf a ≤ n → Sub a a := by
  induction n with
  | zero => intro a h; cases a <;> simp at h
  | succ n ih =>
    intro a ha
    have hex : ∀ es : Externs, sizeOf es < n + 1 → SubEx es es := fun es hes =>
      (SubEx_iff es es).2 fun p hp =>
        ⟨p.2, hp, ih p.2 (by have := sizeOf_lt_of_mem (k := p.1) (a := p.2) hp; omega)⟩
    cases a with
    | func s => exact .func s
    | value t => exact .value t
    | resource r => exact .resource r
    | type a => exact .type (ih a (by simp at ha; omega))
    | inst i es => exact .inst (hex es (by simp at ha; omega))
    | comp i is es => exact .comp (hex is (by simp at ha; omega)) (hex es (by simp at ha; omega))

theorem Sub.refl (a : Kind) : Sub a a := Sub.refl_le _ a (Nat.le_refl _)

/-- Composition of `SubEx`, given transitivity on the items involved. -/
theorem SubEx.trans_of {as bs cs : Externs}
    (h : ∀ k x y z, (k, x) ∈ as → (k, y) ∈ bs → (k, z) ∈ cs → Sub x y → Sub y z → Sub x z)
    (h1 : SubEx as bs) (h2 : SubEx bs cs) : SubEx as cs := by
  have e1 := (SubEx_iff as bs).1 h1
  have e2 := (SubEx_iff bs cs).1 h2
  refine (SubEx_iff as cs).2 fun p hp => ?_
  obtain ⟨y, hy, hyz⟩ := e2 p hp
  obtain ⟨x, hx, hxy⟩ := e1 (p.1, y) hy
  exact ⟨x, hx, h p.1 x y p.2 hx hy hp hxy hyz⟩

/-- The named-items step of the size induction for transitivity. -/
theorem SubEx.trans_sized (n : Nat)
    (ih : ∀ a b c : Kind, sizeOf a + sizeOf b + sizeOf c ≤ n → Sub a b → Sub b c → Sub a c)
    {as bs cs : Externs} (h : sizeOf as + sizeOf bs + sizeOf cs < n)
    (h1 : SubEx as bs) (h2 : SubEx bs cs) : SubEx as cs :=
  SubEx.trans_of (fun _ x y z hx hy hz => ih x y z (by
    have := sizeOf_lt_of_mem hx; have := sizeOf_lt_of_mem hy; have := sizeOf_lt_of_mem hz
    omega)) h1 h2

theorem Sub.trans_le (n : Nat) :
    ∀ a b c : Kind, sizeOf a + sizeOf b + sizeOf c ≤ n → Sub a b → Sub b c → Sub a c := by
  induction n with
  | zero => intro a b c h; cases a <;> simp at h
  | succ n ih =>
    intro a b c hs hab hbc
    cases hab with
    | func s => exact hbc
    | value t => exact hbc
    | resource r => exact hbc
    | type h1 => cases hbc with
      | type h2 => exact .type (ih _ _ _ (by simp at hs; omega) h1 h2)
    | inst h1 => cases hbc with
      | inst h2 => exact .inst (SubEx.trans_sized n ih (by simp at hs; omega) h1 h2)
    | comp i1 e1 => cases hbc with
      | comp i2 e2 =>
        exact .comp (SubEx.trans_sized n ih (by simp at hs; omega) i2 i1)
          (SubEx.trans_sized n ih (by simp at hs; omega) e1 e2)

theorem Sub.trans {a b c : Kind} (h1 : Sub a b) (h2 : Sub b c) : Sub a c :=
  Sub.trans_le _ a b c (Nat.le_refl _) h1 h2

/-! ## Flat kinds and merging -/

/-- A flat kind is a subtype only of itself. -/
theorem flat_sub : ∀ {a b : Kind}, a.flat = true → Sub a b → b = a
  | .func _, _, _, h => by cases h; rfl
  | .value _, _, _, h => by cases h; rfl
  | .resource _, _, _, h => by cases h; rfl
  | .type a, _, hf, h => by
    cases h with
    | type h' => rw [flat_sub (a := a) (by simpa [Kind.flat] using hf) h']
  | .inst _ _, _, hf, _ => by simp [Kind.flat] at hf
  | .comp _ _ _, _, hf, _ => by simp [Kind.flat] at hf

/-- On flat kinds the checker is equality. -/
theorem sub_flat {a b : Kind} (ha : a.flat = true) :
    sub a b = true ↔ a = b := by
  rw [sub_iff]
  exact ⟨fun h => (flat_sub ha h).symm, fun h => h ▸ Sub.refl a⟩

theorem Externs.find_mem {es : Externs} {n : String} {k : Kind} (h : es.find n = some k) :
    (n, k) ∈ es := by
  induction es with
  | nil => simp [Externs.find] at h
  | cons p es ih =>
    obtain ⟨m, x⟩ := p
    by_cases hm : n = m
    · subst hm; simp [Externs.find] at h; simp [h]
    · simp [Externs.find, List.lookup, beq_false_of_ne hm] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Every item is flat. -/
def FlatEx (es : Externs) : Prop := ∀ p ∈ es, p.2.flat = true

/-- A merge step at a known name `n` of flat items: the merge goes on unchanged when
the two items are equal, and fails otherwise. -/
theorem mergeEx_known (contra : Bool) {es ns : Externs} {n : String} {src tgt : Kind}
    (hf : es.find n = some tgt) (fs : src.flat = true) (ft : tgt.flat = true) :
    mergeEx contra es ((n, src) :: ns) = if tgt = src then mergeEx contra es ns else none := by
  by_cases he : tgt = src
  · have hs : sub tgt tgt = true := (sub_flat ft).2 rfl
    subst he; rw [mergeEx, hf]; cases contra <;> simp [hs]
  · have h1 : sub src tgt = false :=
      Bool.eq_false_iff.2 fun e => he ((sub_flat fs).1 e).symm
    have h2 : sub tgt src = false := Bool.eq_false_iff.2 fun e => he ((sub_flat ft).1 e)
    rw [mergeEx, hf]; cases contra <;> simp [h1, h2, he]

theorem mem_drop_dup {α : Type} {x p : α} {es ns : List α} (hx : x ∈ es) (hp : p ∈ es ++ x :: ns) :
    p ∈ es ++ ns := by
  rcases List.mem_append.1 hp with hp | hp
  · exact List.mem_append_left _ hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ hp

theorem FlatEx.snoc {es : Externs} {n : String} {k : Kind} (fe : FlatEx es) (fk : k.flat = true) :
    FlatEx (es ++ [(n, k)]) := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · exact fe p hp
  · rw [List.mem_singleton.1 hp]; exact fk

/-- Merging flat named items keeps every item of both sides. -/
theorem mergeEx_flat (contra : Bool) :
    ∀ (ns es ms : Externs), FlatEx es → FlatEx ns → mergeEx contra es ns = some ms →
      ∀ p ∈ es ++ ns, p ∈ ms := by
  intro ns
  induction ns with
  | nil => intro es ms _ _ h; simp only [mergeEx, Option.some.injEq] at h; simp [h]
  | cons q ns ih =>
    obtain ⟨n, src⟩ := q
    intro es ms fe fn h
    have fsrc : src.flat = true := fn (n, src) (by simp)
    have fns : FlatEx ns := fun p hp => fn p (by simp [hp])
    cases hf : es.find n with
    | none =>
      have h' : mergeEx contra (es ++ [(n, src)]) ns = some ms := by rw [mergeEx, hf] at h; exact h
      exact fun p hp => ih _ _ (fe.snoc fsrc) fns h' p (by simpa using hp)
    | some tgt =>
      have hmem : (n, tgt) ∈ es := Externs.find_mem hf
      have he : tgt = src ∧ mergeEx contra es ns = some ms := by
        rw [mergeEx_known contra hf fsrc (fe _ hmem)] at h; split at h <;> simp_all
      have hall : ∀ p ∈ es ++ ns, p ∈ ms := ih es ms fe fns he.2
      exact fun p hp => hall p (mem_drop_dup (he.1 ▸ hmem) hp)

/-- **Merging implicit imports of flat instances gives a common subtype**: the merged
instance can be passed to every instantiation that asked for either. -/
theorem merge_lower {i j : Option String} {es ns : Externs} {c : Kind}
    (fe : FlatEx es) (fn : FlatEx ns) (h : merge (.inst i es) (.inst j ns) = some c) :
    Sub c (.inst i es) ∧ Sub c (.inst j ns) := by
  simp only [merge, Option.map_eq_some_iff] at h
  obtain ⟨ms, hm, rfl⟩ := h
  have hall := mergeEx_flat false ns es ms fe fn hm
  have lift : ∀ xs : Externs, (∀ p ∈ xs, p ∈ ms) → SubEx ms xs := fun xs hx =>
    (SubEx_iff ms xs).2 fun p hp => ⟨p.2, hx p hp, Sub.refl _⟩
  exact ⟨.inst (lift es fun p hp => hall p (List.mem_append_left _ hp)),
    .inst (lift ns fun p hp => hall p (List.mem_append_right _ hp))⟩

/-- An instance with a nested instance export `f` exporting `xs`. -/
def nestedEx (xs : List String) : Kind :=
  .inst none [("f", .inst none (xs.map fun x => (x, .value (.prim .u32))))]

/-- **Merging is not a lower bound in general**: merging `{f: {x}}` into `{f: {x, y}}`
keeps the larger `{f: {x}}`, which is not a subtype of `{f: {x, y}}`. wac accepts this
merge (`merge_interface`), and the merged implicit import is then not a valid argument
of the instantiation that asked for `{f: {x, y}}`. -/
theorem merge_not_lower :
    merge (nestedEx ["x", "y"]) (nestedEx ["x"]) = some (nestedEx ["x"]) ∧
    ¬ Sub (nestedEx ["x"]) (nestedEx ["x", "y"]) := by
  refine ⟨by decide +kernel, ?_⟩
  rw [← sub_iff]
  decide +kernel

/-- Merging flat named items only appends: every item comes from one of the sides. -/
theorem mergeEx_flat_out (contra : Bool) :
    ∀ (ns es ms : Externs), FlatEx es → FlatEx ns → mergeEx contra es ns = some ms →
      ∀ p ∈ ms, p ∈ es ++ ns := by
  intro ns
  induction ns with
  | nil => intro es ms _ _ h; simp only [mergeEx, Option.some.injEq] at h; simp [h]
  | cons q ns ih =>
    obtain ⟨n, src⟩ := q
    intro es ms fe fn h
    have fsrc : src.flat = true := fn (n, src) (by simp)
    have fns : FlatEx ns := fun p hp => fn p (by simp [hp])
    cases hf : es.find n with
    | none =>
      have h' : mergeEx contra (es ++ [(n, src)]) ns = some ms := by rw [mergeEx, hf] at h; exact h
      exact fun p hp => by simpa using ih _ _ (fe.snoc fsrc) fns h' p hp
    | some tgt =>
      have hmem : (n, tgt) ∈ es := Externs.find_mem hf
      have he : tgt = src ∧ mergeEx contra es ns = some ms := by
        rw [mergeEx_known contra hf fsrc (fe _ hmem)] at h; split at h <;> simp_all
      have hall : ∀ p ∈ ms, p ∈ es ++ ns := ih es ms fe fns he.2
      exact fun p hp => by
        rcases List.mem_append.1 (hall p hp) with h1 | h1 <;> simp [h1]

/-- Merging a flat kind succeeds only with itself. -/
theorem merge_flat : ∀ {a b c : Kind}, a.flat = true → merge a b = some c → c = a ∧ b = a
  | .func _, .func _, _, _, h | .value _, .value _, _, _, h | .resource _, .resource _, _, _, h => by
    simp only [merge] at h; split at h <;> simp_all
  | .type a, .type b, c, hf, h => by
    simp only [merge, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    obtain ⟨e1, e2⟩ := merge_flat (a := a) (by simpa [Kind.flat] using hf) hc'
    exact ⟨by rw [e1], by rw [e2]⟩
  | .inst _ _, _, _, hf, _ | .comp _ _ _, _, _, hf, _ => by simp [Kind.flat] at hf
  | .func _, .value _, _, _, h | .func _, .resource _, _, _, h | .func _, .type _, _, _, h
  | .func _, .inst _ _, _, _, h | .func _, .comp _ _ _, _, _, h
  | .value _, .func _, _, _, h | .value _, .resource _, _, _, h | .value _, .type _, _, _, h
  | .value _, .inst _ _, _, _, h | .value _, .comp _ _ _, _, _, h
  | .resource _, .func _, _, _, h | .resource _, .value _, _, _, h | .resource _, .type _, _, _, h
  | .resource _, .inst _ _, _, _, h | .resource _, .comp _ _ _, _, _, h
  | .type _, .func _, _, _, h | .type _, .value _, _, _, h | .type _, .resource _, _, _, h
  | .type _, .inst _ _, _, _, h | .type _, .comp _ _ _, _, _, h => by simp [merge] at h

theorem flatEx_of_all {es : Externs} (h : es.all (·.2.flat) = true) : FlatEx es :=
  fun p hp => by simpa using List.all_eq_true.1 h p hp

theorem merge_wit_inst {i j : Option String} {es ns : Externs} {c : Kind}
    (fe : FlatEx es) (fn : FlatEx ns) (h : merge (.inst i es) (.inst j ns) = some c) : c.wit = true := by
  have h' : ∃ ms, mergeEx false es ns = some ms ∧ Kind.inst i ms = c := by
    simpa only [merge, Option.map_eq_some_iff] using h
  obtain ⟨ms, hm, rfl⟩ := h'
  have hout : ∀ p ∈ ms, p ∈ es ++ ns := mergeEx_flat_out false ns es ms fe fn hm
  refine List.all_eq_true.2 fun p hp => ?_
  rcases List.mem_append.1 (hout p hp) with h1 | h1
  · exact fe p h1
  · exact fn p h1

/-- **Merging WIT-shaped kinds gives a WIT-shaped common subtype.** -/
theorem merge_wit {a b c : Kind} (ha : a.wit = true) (hb : b.wit = true) (h : merge a b = some c) :
    c.wit = true ∧ Sub c a ∧ Sub c b := by
  cases a with
  | inst i es =>
    cases b with
    | inst j ns =>
      have fe : FlatEx es := flatEx_of_all (by simpa [Kind.wit] using ha)
      have fn : FlatEx ns := flatEx_of_all (by simpa [Kind.wit] using hb)
      exact ⟨merge_wit_inst fe fn h, merge_lower fe fn h⟩
    | _ => simp [merge] at h
  | _ =>
    have hf := ha
    simp only [Kind.wit] at hf
    obtain ⟨rfl, rfl⟩ := merge_flat hf h
    exact ⟨ha, Sub.refl _, Sub.refl _⟩

end Silmaril.Wasm.Wac
