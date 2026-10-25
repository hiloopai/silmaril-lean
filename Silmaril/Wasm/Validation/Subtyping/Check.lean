module

public import Silmaril.Wasm.Validation.Subtyping.Properties
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # A computable subtyping checker (§2.2)

`Sub.check Δ a b` decides `Sub Δ a b` rule by rule:

* numeric, vector, packed types: equality;
* reference types: nullability `n₁ → n₂` and heap subtyping;
* storage, field, composite types: the structural rules (`STRUCT` by prefix);
* sequences: pointwise;
* heap types: the abstract hierarchy (`absSub`), `BOT`, the three
  `deftype <: struct/array/func` rules on the expansion, and between defined
  types the reachability of a declared supertype (unrolling `SUB … typeuse* …`
  and resolving `_IDX` through `TYPES`) that is equal after closure
  (`Deftype_sub/refl`, `Deftype_sub/super`). The search is bounded by a fuel
  `TypeCtx.fuel` that strictly bounds every supertype chain of a valid type.

**Soundness** (`Sub.check_sound`) is unconditional. **Completeness**
(`Sub.check_complete`) holds in a well-formed closed context (`Δ.Ok`) with no
`RECS` (every context after the type section) for valid types; the premise of
`Heaptype_sub/trans` is what makes validity necessary. The proof goes through the
declarative reachability relation `TypeCtx.Reach` and its invariance under
closure (`unrolldt_clos`).
-/

namespace Silmaril.Wasm.Validation

/-! ## Definitions -/

/-- Structural size of a semantic type. -/
def Ty.size : {k : TKind} → Ty k → Nat
  | _, .nil => 1
  | _, .cons a l => a.size + l.size + 1
  | _, .idx _ => 1
  | _, .recv _ => 1
  | _, .dt d => d.size + 1
  | _, .defn g _ => g.size + 1
  | _, .abs _ => 1
  | _, .bot => 1
  | _, .use u => u.size + 1
  | _, .ref _ h => h.size + 1
  | _, .num _ => 1
  | _, .vec _ => 1
  | _, .refv r => r.size + 1
  | _, .botv => 1
  | _, .val t => t.size + 1
  | _, .pack _ => 1
  | _, .field _ s => s.size + 1
  | _, .struct fs => fs.size + 1
  | _, .array f => f.size + 1
  | _, .func ps rs => ps.size + rs.size + 1
  | _, .sub _ sups b => sups.size + b.size + 1
  | _, .group subs => subs.size + 1

/-- The defined type a type use denotes (`_IDX x` through `TYPES`); `REC i` has none. -/
def TypeCtx.resolve (Δ : TypeCtx) : CTypeUse → Option DefType
  | .dt d => some d
  | .idx x => Δ.types[x]?
  | .recv _ => none

/-- The abstract heap type a composite type is directly below. -/
def compAbs : CCompType → AbsHeapType
  | .struct _ => .struct
  | .array _ => .array
  | .func _ _ => .func

/-- The kind (`struct`/`array`/`func`) of a defined type's expansion. -/
def defKind (d : DefType) : Option AbsHeapType := (unrolldt d).map (fun st => compAbs st.body)

/-- Declared supertypes of a defined type (after unrolling). -/
def supersOf (d : DefType) : List CTypeUse :=
  match unrolldt d with
  | some st => st.supers
  | none => []

/-- The abstract heap-type order, including the four bottoms. -/
def absSub : AbsHeapType → AbsHeapType → Bool
  | .any, .any | .eq, .eq | .i31, .i31 | .struct, .struct | .array, .array
  | .none, .none | .func, .func | .nofunc, .nofunc | .exn, .exn | .noexn, .noexn
  | .extern, .extern | .noextern, .noextern => true
  | .eq, .any | .i31, .eq | .i31, .any | .struct, .eq | .struct, .any
  | .array, .eq | .array, .any => true
  | .none, .any | .none, .eq | .none, .i31 | .none, .struct | .none, .array => true
  | .nofunc, .func | .noexn, .exn | .noextern, .extern => true
  | _, _ => false

/-- The top a bottom abstract heap type is the bottom of. -/
def botTop : AbsHeapType → Option AbsHeapType
  | .none => some .any
  | .nofunc => some .func
  | .noexn => some .exn
  | .noextern => some .extern
  | _ => none

/-- Bounded search along declared supertypes for a defined type satisfying `P`. -/
def TypeCtx.reach (Δ : TypeCtx) (P : DefType → Bool) : Nat → DefType → Bool
  | 0, d => P d
  | n + 1, d => P d || (supersOf d).any fun u =>
      match Δ.resolve u with
      | some d' => Δ.reach P n d'
      | none => false

/-- Measure of a defined type: strictly decreases along supertypes of valid types. -/
def mu0 : DefType → Nat
  | .defn g i => g.size * g.size + i

/-- Fuel for the supertype search from `d`. -/
def TypeCtx.fuel (Δ : TypeCtx) (d : DefType) : Nat :=
  mu0 d + (if d.freeIdx = [] then 0 else 1 + (Δ.types.map mu0).sum)

/-- `Deftype_sub`. -/
def TypeCtx.checkDef (Δ : TypeCtx) (d₁ d₂ : DefType) : Bool :=
  Δ.reach (fun e => decide (e.clos Δ.types = d₂.clos Δ.types)) (Δ.fuel d₁) d₁

/-- `deftype <: absheaptype` through the expansion of the resolved type use. -/
def TypeCtx.checkUseAbs (Δ : TypeCtx) (u : CTypeUse) (b : AbsHeapType) : Bool :=
  match Δ.resolve u >>= defKind with
  | some k => absSub k b
  | none => false

/-- `Heaptype_sub`. -/
def TypeCtx.checkHeap (Δ : TypeCtx) : CHeapType → CHeapType → Bool
  | .bot, _ => true
  | .abs a, .abs b => absSub a b
  | .abs a, .use u =>
    match botTop a with
    | some t => Δ.checkUseAbs u t
    | none => false
  | .use u, .abs b => Δ.checkUseAbs u b
  | .use u₁, .use u₂ =>
    match Δ.resolve u₁, Δ.resolve u₂ with
    | some d₁, some d₂ => Δ.checkDef d₁ d₂
    | none, none => decide (u₁ = u₂)
    | _, _ => false
  | .abs _, .bot => false
  | .use _, .bot => false

/-- Pointwise Boolean relation on lists. -/
def forall2B {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: l, b :: l' => f a b && forall2B f l l'
  | _, _ => false

/-- `Reftype_sub`. -/
def TypeCtx.checkRef (Δ : TypeCtx) : CRefType → CRefType → Bool
  | .ref n₁ h₁, .ref n₂ h₂ => (!n₁ || n₂) && Δ.checkHeap h₁ h₂

/-- `Valtype_sub`. -/
def TypeCtx.checkVal (Δ : TypeCtx) : CValType → CValType → Bool
  | .num t₁, .num t₂ => decide (t₁ = t₂)
  | .vec t₁, .vec t₂ => decide (t₁ = t₂)
  | .refv r₁, .refv r₂ => Δ.checkRef r₁ r₂
  | .botv, _ => true
  | _, _ => false

/-- `Storagetype_sub`. -/
def TypeCtx.checkStorage (Δ : TypeCtx) : CStorageType → CStorageType → Bool
  | .val t₁, .val t₂ => Δ.checkVal t₁ t₂
  | .pack p₁, .pack p₂ => decide (p₁ = p₂)
  | _, _ => false

/-- `Fieldtype_sub`. -/
def TypeCtx.checkField (Δ : TypeCtx) : CFieldType → CFieldType → Bool
  | .field .const z₁, .field .const z₂ => Δ.checkStorage z₁ z₂
  | .field .var z₁, .field .var z₂ => Δ.checkStorage z₁ z₂ && Δ.checkStorage z₂ z₁
  | _, _ => false

/-- `Comptype_sub`. -/
def TypeCtx.checkComp (Δ : TypeCtx) : CCompType → CCompType → Bool
  | .struct fs₁, .struct fs₂ =>
    decide (fs₂.toList.length ≤ fs₁.toList.length) &&
      forall2B Δ.checkField (fs₁.toList.take fs₂.toList.length) fs₂.toList
  | .array f₁, .array f₂ => Δ.checkField f₁ f₂
  | .func ps₁ rs₁, .func ps₂ rs₂ =>
    forall2B Δ.checkVal ps₂.toList ps₁.toList && forall2B Δ.checkVal rs₁.toList rs₂.toList
  | _, _ => false

/-- The checker at every sort. -/
def Sub.checkK (Δ : TypeCtx) : (k : TKind) → Ty k → Ty k → Bool
  | .heap, a, b => Δ.checkHeap a b
  | .ref, a, b => Δ.checkRef a b
  | .val, a, b => Δ.checkVal a b
  | .storage, a, b => Δ.checkStorage a b
  | .field, a, b => Δ.checkField a b
  | .comp, a, b => Δ.checkComp a b
  | .def, a, b => Δ.checkDef a b
  | .list k, a, b => forall2B (Sub.checkK Δ k) a.toList b.toList
  | .use, _, _ => false
  | .sub, _, _ => false
  | .group, _, _ => false

/-- The subtyping checker. -/
def Sub.check (Δ : TypeCtx) {k : TKind} (a b : Ty k) : Bool := Sub.checkK Δ k a b

/-! ## Reachability along declared supertypes -/

/-- `d` reaches `e` by following declared supertypes (unrolled, `_IDX` resolved). -/
inductive TypeCtx.Reach (Δ : TypeCtx) : DefType → DefType → Prop where
  | refl (d : DefType) : Δ.Reach d d
  | step {d d' e : DefType} {u : CTypeUse} (hu : u ∈ supersOf d)
      (hr : Δ.resolve u = some d') (h : Δ.Reach d' e) : Δ.Reach d e

theorem TypeCtx.Reach.trans {Δ : TypeCtx} {a b c : DefType} (h₁ : Δ.Reach a b)
    (h₂ : Δ.Reach b c) : Δ.Reach a c := by
  induction h₁ with
  | refl => exact h₂
  | step hu hr _ ih => exact .step hu hr (ih h₂)

theorem TypeCtx.reach_of {Δ : TypeCtx} {P : DefType → Bool} {d : DefType} (h : P d = true) :
    ∀ n, Δ.reach P n d = true
  | 0 => h
  | _ + 1 => by simp [TypeCtx.reach, h]

theorem TypeCtx.reach_sound {Δ : TypeCtx} {P : DefType → Bool} :
    ∀ {n : Nat} {d : DefType}, Δ.reach P n d = true → ∃ e, Δ.Reach d e ∧ P e = true
  | 0, d, h => ⟨d, .refl d, h⟩
  | n + 1, d, h => by
    simp only [TypeCtx.reach, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with h | ⟨u, hu, h⟩
    · exact ⟨d, .refl d, h⟩
    · split at h
      · next d' hr =>
        obtain ⟨e, he, hP⟩ := reach_sound h
        exact ⟨e, .step hu hr he, hP⟩
      · simp at h

/-! ## Soundness -/

theorem Sub.use_left {Δ : TypeCtx} {u : CTypeUse} {d : DefType} {h : CHeapType}
    (hr : Δ.resolve u = some d) (hs : Sub Δ (.use (.dt d)) h) : Sub Δ (.use u) h := by
  cases u with
  | dt d' => cases hr; exact hs
  | idx x => exact .idxL hr hs
  | recv i => cases hr

theorem Sub.use_right {Δ : TypeCtx} {u : CTypeUse} {d : DefType} {h : CHeapType}
    (hr : Δ.resolve u = some d) (hs : Sub Δ h (.use (.dt d))) : Sub Δ h (.use u) := by
  cases u with
  | dt d' => cases hr; exact hs
  | idx x => exact .idxR hr hs
  | recv i => cases hr

theorem supersOf_mem {d : DefType} {u : CTypeUse} (hu : u ∈ supersOf d) :
    ∃ (fin : Bool) (sups : Ty (.list .use)) (ct : CCompType) (j : Nat),
      unrolldt d = some (.sub fin sups ct) ∧ sups.toList[j]? = some u := by
  unfold supersOf at hu
  split at hu
  · next st hst =>
    cases st with
    | sub fin sups ct =>
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      exact ⟨fin, sups, ct, j, hst, by simp [Ty.supers]⟩
  · simp at hu

theorem TypeCtx.Reach.sub {Δ : TypeCtx} {d e d₂ : DefType} (h : Δ.Reach d e)
    (hc : e.clos Δ.types = d₂.clos Δ.types) : Sub Δ d d₂ := by
  induction h with
  | refl => exact .defRefl hc
  | step hu hr _ ih =>
    obtain ⟨fin, sups, ct, j, hun, hj⟩ := supersOf_mem hu
    exact .defSuper hun hj (Sub.use_left hr (.defDef (ih hc)))

theorem absSub_sound {Δ : TypeCtx} {a b : AbsHeapType} (h : absSub a b = true) :
    Sub Δ (.abs a) (.abs b) := by
  have eqAny' : Sub Δ (.abs .eq) (.abs .any) := .eqAny
  have i31Any : Sub Δ (.abs .i31) (.abs .any) := .heapTrans (.abs .eq) .i31Eq .eqAny
  have structAny : Sub Δ (.abs .struct) (.abs .any) := .heapTrans (.abs .eq) .structEq .eqAny
  have arrayAny : Sub Δ (.abs .array) (.abs .any) := .heapTrans (.abs .eq) .arrayEq .eqAny
  cases a <;> cases b <;> simp [absSub] at h
  all_goals first
    | exact .heapRefl
    | exact .eqAny | exact .i31Eq | exact .structEq | exact .arrayEq
    | exact i31Any | exact structAny | exact arrayAny
    | exact .none .heapRefl nofun | exact .none eqAny' nofun | exact .none i31Any nofun
    | exact .none structAny nofun | exact .none arrayAny nofun
    | exact .nofunc .heapRefl nofun | exact .noexn .heapRefl nofun
    | exact .noextern .heapRefl nofun

theorem defKind_sub {Δ : TypeCtx} {d : DefType} {k : AbsHeapType} (hk : defKind d = some k) :
    Sub Δ (.use (.dt d)) (.abs k) := by
  unfold defKind at hk
  cases hun : unrolldt d with
  | none => simp [hun] at hk
  | some st =>
    rw [hun] at hk
    cases st with
    | sub fin sups ct =>
      simp only [Option.map_some, Option.some.injEq, Ty.body] at hk
      subst hk
      cases ct with
      | struct fs => exact .defStruct (.mk hun)
      | array f => exact .defArray (.mk hun)
      | func ps rs => exact .defFunc (.mk hun)

theorem useAbs_sound {Δ : TypeCtx} {u : CTypeUse} {k b : AbsHeapType}
    (hk : (Δ.resolve u >>= defKind) = some k) (h : absSub k b = true) :
    Sub Δ (.use u) (.abs b) := by
  cases hr : Δ.resolve u with
  | none => simp [hr] at hk
  | some d =>
    rw [hr] at hk
    exact Sub.use_left hr (.heapTrans (.abs k) (defKind_sub hk) (absSub_sound h))

theorem TypeCtx.checkDef_sound {Δ : TypeCtx} {d₁ d₂ : DefType} (h : Δ.checkDef d₁ d₂ = true) :
    Sub Δ d₁ d₂ := by
  obtain ⟨e, he, hP⟩ := reach_sound h
  exact he.sub (by simpa using hP)

theorem TypeCtx.checkUseAbs_sound {Δ : TypeCtx} {u : CTypeUse} {b : AbsHeapType}
    (h : Δ.checkUseAbs u b = true) : Sub Δ (.use u) (.abs b) := by
  unfold TypeCtx.checkUseAbs at h
  split at h
  · next k hk => exact useAbs_sound hk h
  · simp at h

theorem TypeCtx.checkHeap_sound {Δ : TypeCtx} :
    ∀ {h₁ h₂ : CHeapType}, Δ.checkHeap h₁ h₂ = true → Sub Δ h₁ h₂
  | .bot, _, _ => .bot
  | .abs a, .abs b, h => absSub_sound h
  | .abs a, .use u, h => by
    simp only [TypeCtx.checkHeap] at h
    split at h
    · next t ht =>
      have hs := Δ.checkUseAbs_sound h
      cases a <;> simp [botTop] at ht <;> subst ht
      · exact .none hs nofun
      · exact .nofunc hs nofun
      · exact .noexn hs nofun
      · exact .noextern hs nofun
    · simp at h
  | .use u, .abs b, h => Δ.checkUseAbs_sound h
  | .use u₁, .use u₂, h => by
    simp only [TypeCtx.checkHeap] at h
    split at h
    · next d₁ d₂ hr₁ hr₂ =>
      exact Sub.use_left hr₁ (Sub.use_right hr₂ (.defDef (TypeCtx.checkDef_sound h)))
    · simp at h; subst h; exact .heapRefl
    · simp at h
  | .abs _, .bot, h => by simp [TypeCtx.checkHeap] at h
  | .use _, .bot, h => by simp [TypeCtx.checkHeap] at h

theorem forall2B_sound {Δ : TypeCtx} {k : TKind} {f : Ty k → Ty k → Bool}
    (hf : ∀ a b, f a b = true → Sub Δ a b) :
    ∀ {l₁ l₂ : List (Ty k)}, forall2B f l₁ l₂ = true → Sub Δ (Ty.ofList l₁) (Ty.ofList l₂)
  | [], [], _ => .nil
  | a :: l, b :: l', h => by
    simp only [forall2B, Bool.and_eq_true] at h
    exact .cons (hf a b h.1) (forall2B_sound hf h.2)
  | [], _ :: _, h => by simp [forall2B] at h
  | _ :: _, [], h => by simp [forall2B] at h

theorem forall2B_sound' {Δ : TypeCtx} {k : TKind} {f : Ty k → Ty k → Bool}
    (hf : ∀ a b, f a b = true → Sub Δ a b) {l₁ l₂ : Ty (.list k)}
    (h : forall2B f l₁.toList l₂.toList = true) : Sub Δ l₁ l₂ := by
  have := forall2B_sound hf h
  rwa [Ty.ofList_toList, Ty.ofList_toList] at this

theorem TypeCtx.checkRef_sound {Δ : TypeCtx} {a b : CRefType} (h : Δ.checkRef a b = true) :
    Sub Δ a b := by
  cases a with
  | ref n₁ h₁ =>
    cases b with
    | ref n₂ h₂ =>
      simp only [TypeCtx.checkRef, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hn, hh⟩ := h
      have hs := Δ.checkHeap_sound hh
      cases n₂ with
      | true => exact .refNull hs
      | false =>
        rcases hn with rfl | hn
        · exact .refNonNull hs
        · cases hn

theorem TypeCtx.checkVal_sound {Δ : TypeCtx} :
    ∀ {a b : CValType}, Δ.checkVal a b = true → Sub Δ a b
  | .num t₁, .num t₂, h => by simp [TypeCtx.checkVal] at h; subst h; exact .num
  | .vec .v128, .vec .v128, _ => .vec
  | .refv _, .refv _, h => .refv (Δ.checkRef_sound h)
  | .botv, _, _ => .botv
  | .num _, .vec _, h | .num _, .refv _, h | .num _, .botv, h
  | .vec _, .num _, h | .vec _, .refv _, h | .vec _, .botv, h
  | .refv _, .num _, h | .refv _, .vec _, h | .refv _, .botv, h => by
    simp [TypeCtx.checkVal] at h

theorem TypeCtx.checkStorage_sound {Δ : TypeCtx} {a b : CStorageType}
    (h : Δ.checkStorage a b = true) : Sub Δ a b := by
  cases a <;> cases b <;> simp [TypeCtx.checkStorage] at h
  · exact .val (Δ.checkVal_sound h)
  · subst h; exact .pack

theorem TypeCtx.checkField_sound {Δ : TypeCtx} :
    ∀ {a b : CFieldType}, Δ.checkField a b = true → Sub Δ a b
  | .field .const _, .field .const _, h => .fieldConst (Δ.checkStorage_sound h)
  | .field .var _, .field .var _, h => by
    simp only [TypeCtx.checkField, Bool.and_eq_true] at h
    exact .fieldVar (Δ.checkStorage_sound h.1) (Δ.checkStorage_sound h.2)
  | .field .const _, .field .var _, h | .field .var _, .field .const _, h => by
    simp [TypeCtx.checkField] at h

theorem TypeCtx.checkComp_sound {Δ : TypeCtx} {a b : CCompType}
    (h : Δ.checkComp a b = true) : Sub Δ a b := by
  cases a <;> cases b <;> simp only [TypeCtx.checkComp, Bool.false_eq_true] at h
  · next fs₁ fs₂ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hs := forall2B_sound (fun _ _ => Δ.checkField_sound) h.2
    rw [Ty.ofList_toList] at hs
    have := Sub.struct (extra := Ty.ofList (fs₁.toList.drop fs₂.toList.length)) hs
    have e : (Ty.ofList (fs₁.toList.take fs₂.toList.length)).app
        (Ty.ofList (fs₁.toList.drop fs₂.toList.length)) = fs₁ := by
      simp [Ty.app]
    rwa [e] at this
  · exact .array (Δ.checkField_sound h)
  · simp only [Bool.and_eq_true] at h
    exact .func (forall2B_sound' (fun _ _ => Δ.checkVal_sound) h.1)
      (forall2B_sound' (fun _ _ => Δ.checkVal_sound) h.2)

theorem Sub.checkK_sound (Δ : TypeCtx) :
    ∀ (k : TKind) (a b : Ty k), Sub.checkK Δ k a b = true → Sub Δ a b
  | .heap, _, _, h => Δ.checkHeap_sound h
  | .ref, _, _, h => Δ.checkRef_sound h
  | .val, _, _, h => Δ.checkVal_sound h
  | .storage, _, _, h => Δ.checkStorage_sound h
  | .field, _, _, h => Δ.checkField_sound h
  | .comp, _, _, h => Δ.checkComp_sound h
  | .def, _, _, h => Δ.checkDef_sound h
  | .list k, _, _, h => forall2B_sound' (Sub.checkK_sound Δ k) h
  | .use, _, _, h => by simp [Sub.checkK] at h
  | .sub, _, _, h => by simp [Sub.checkK] at h
  | .group, _, _, h => by simp [Sub.checkK] at h

/-- **Soundness** of the checker (unconditional). -/
theorem Sub.check_sound {Δ : TypeCtx} {k : TKind} {a b : Ty k} (h : Sub.check Δ a b = true) :
    Sub Δ a b :=
  Sub.checkK_sound Δ k a b h


/-! ## Completeness: auxiliary facts -/

theorem absSub_refl : ∀ a : AbsHeapType, absSub a a = true := by
  intro a; cases a <;> rfl

theorem absSub_trans : ∀ {a b c : AbsHeapType}, absSub a b = true → absSub b c = true →
    absSub a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

theorem absSub_eq_of_botTop : ∀ {a a' t : AbsHeapType}, absSub a a' = true →
    botTop a' = some t → a = a' := by
  intro a a' t h1 h2
  cases a' <;> simp [botTop] at h2 <;> cases a <;> simp_all [absSub]

theorem absSub_of_botTop : ∀ {a t x : AbsHeapType}, botTop a = some t → absSub x t = true →
    absSub a x = true := by
  intro a t x h1 h2
  cases a <;> simp [botTop] at h1 <;> subst h1 <;> cases x <;> simp_all [absSub]

theorem absSub_botTop_trans : ∀ {a t k b : AbsHeapType}, botTop a = some t →
    absSub k t = true → absSub k b = true → absSub a b = true := by
  intro a t k b h1 h2 h3
  cases a <;> simp [botTop] at h1 <;> subst h1 <;> cases k <;> simp [absSub] at h2 <;>
    cases b <;> simp_all [absSub]

theorem compAbs_not_bot (c : CCompType) : ∀ {a t : AbsHeapType},
    absSub (compAbs c) a = true → botTop a = some t → False := by
  intro a t h1 h2
  cases a <;> simp [botTop] at h2 <;> cases c <;> simp [compAbs, absSub] at h1

theorem compAbs_subst (σ : Subst) (c : CCompType) : compAbs (c.subst σ) = compAbs c := by
  cases c <;> rfl

theorem Sub.compAbs_eq {Δ : TypeCtx} {c c' : CCompType} (h : Sub Δ c c') :
    compAbs c = compAbs c' := by
  cases h <;> rfl

theorem defKind_of_unroll {d : DefType} {fin : Bool} {sups : Ty (.list .use)} {c : CCompType}
    (h : unrolldt d = some (.sub fin sups c)) : defKind d = some (compAbs c) := by
  simp [defKind, h, Ty.body]

theorem defKind_compAbs {d : DefType} {k : AbsHeapType} (h : defKind d = some k) :
    ∃ c, k = compAbs c := by
  unfold defKind at h
  cases hu : unrolldt d with
  | none => simp [hu] at h
  | some st =>
    rw [hu] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨_, h.symm⟩

theorem Ty.size_lt_of_mem {k : TKind} : ∀ {l : Ty (.list k)} {a : Ty k},
    a ∈ l.toList → a.size < l.size
  | .nil, _, h => by simp at h
  | .cons b l, a, h => by
    simp only [Ty.toList_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp only [Ty.size]; omega
    · have := Ty.size_lt_of_mem h; simp only [Ty.size]; omega

theorem Ty.length_le_size {k : TKind} : ∀ (l : Ty (.list k)), l.toList.length ≤ l.size
  | .nil => by simp [Ty.size]
  | .cons b l => by have := Ty.length_le_size l; simp only [Ty.toList_cons, Ty.size]; simp; omega

theorem Ty.freeIdx_of_mem {k : TKind} : ∀ {l : Ty (.list k)} {a : Ty k} {x : Nat},
    a ∈ l.toList → x ∈ a.freeIdx → x ∈ l.freeIdx
  | .nil, _, _, h, _ => by simp at h
  | .cons b l, a, x, h, hx => by
    simp only [Ty.toList_cons, List.mem_cons] at h
    simp only [Ty.freeIdx, List.mem_append]
    rcases h with rfl | h
    · exact .inl hx
    · exact .inr (Ty.freeIdx_of_mem h hx)

theorem TyOk.of_mem {Δ : TypeCtx} {k : TKind} : ∀ {l : Ty (.list k)}, TyOk Δ l →
    ∀ a ∈ l.toList, TyOk Δ a
  | .nil, _, a, h => by simp at h
  | .cons b l, hl, a, h => by
    cases hl with
    | cons hb hl' =>
      simp only [Ty.toList_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact hb
      · exact TyOk.of_mem hl' a h

theorem TyOk.of_forall {Δ : TypeCtx} {k : TKind} : ∀ {l : Ty (.list k)},
    (∀ a ∈ l.toList, TyOk Δ a) → TyOk Δ l
  | .nil, _ => .nil
  | .cons b l, h => .cons (h b (by simp)) (TyOk.of_forall fun a ha => h a (by simp [ha]))

theorem TyOk.app_left {Δ : TypeCtx} {k : TKind} {l e : Ty (.list k)} (h : TyOk Δ (l.app e)) :
    TyOk Δ l :=
  TyOk.of_forall fun a ha => TyOk.of_mem h a (by simp [Ty.app, ha])

theorem TypeCtx.resolve_ok {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {u : CTypeUse}
    (h : TyOk Δ u) : ∃ d, Δ.resolve u = some d ∧ TyOk Δ d := by
  cases h with
  | idx hx => exact ⟨_, hx, (hΔ _ (List.mem_of_getElem? hx)).2⟩
  | recv hi => simp [hr] at hi
  | dt hd => exact ⟨_, rfl, hd⟩

theorem TyOk.use_inv {Δ : TypeCtx} {u : CTypeUse} (h : TyOk Δ (.use u)) : TyOk Δ u := by
  cases h with
  | use h => exact h

theorem TyOk.dt_inv {Δ : TypeCtx} {d : DefType} (h : TyOk Δ (.dt d)) : TyOk Δ d := by
  cases h with
  | dt h => exact h

/-- The substitution `unrollrt` performs on a group's members. -/
def unrollSubst (subs : Ty (.list .sub)) : Subst
  | .recv j => if j < subs.length then some (.dt (.defn (.group subs) j)) else none
  | .idx _ => none

theorem unrolldt_defn (subs : Ty (.list .sub)) (i : Nat) :
    unrolldt (.defn (.group subs) i) = (subs.toList[i]?).map (·.subst (unrollSubst subs)) := by
  simp only [unrolldt, unrollrt, Ty.subs]
  rw [Ty.toList_subst, List.getElem?_map]
  congr 2

theorem supersOf_of_unroll {d : DefType} {st : CSubType} (h : unrolldt d = some st) :
    supersOf d = st.supers := by
  simp [supersOf, h]

theorem mu0_lt_sq {Δ : TypeCtx} {e : DefType} (he : TyOk Δ e) : mu0 e < e.size * e.size := by
  cases he with
  | @defn _ subs i _ hi =>
    have h1 := Ty.length_le_size subs
    simp only [Ty.length] at hi
    have : i < subs.size := by omega
    simp only [mu0, Ty.size]
    nlinarith

theorem le_sum_of_mem' {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- One step along a declared supertype of a valid defined type: the target is
valid, the fuel strictly decreases, and the kind is preserved. -/
theorem TypeCtx.super_step {Δ : TypeCtx} (hΔ : Δ.Ok) {d d' : DefType} {u : CTypeUse}
    (hd : TyOk Δ d) (hu : u ∈ supersOf d) (hr : Δ.resolve u = some d') :
    TyOk Δ d' ∧ Δ.fuel d' < Δ.fuel d ∧ defKind d' = defKind d := by
  cases hd with
  | @defn _ subs i hg hi =>
    have hi' : i < subs.toList.length := by simpa [Ty.length] using hi
    have hst : subs.toList[i]? = some subs.toList[i] := List.getElem?_eq_getElem hi'
    generalize subs.toList[i] = st at hst
    have hso := GroupOk2.get subs hg hst
    rw [Nat.zero_add] at hso
    have hun := unrolldt_defn subs i
    rw [hst, Option.map_some] at hun
    rw [supersOf_of_unroll hun] at hu
    have hmemst : st ∈ subs.toList := List.mem_of_getElem? hst
    have hsz : st.size < subs.size := Ty.size_lt_of_mem hmemst
    cases hso with
    | noSuper hct => simp [Ty.subst, Ty.supers] at hu
    | @oneSuper _ fin u0 ct _ sups' ct' hu0 hb hunroll hct hsub =>
      simp only [Ty.subst, Ty.supers, Ty.toList_cons, Ty.toList_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hu
      have hkd : defKind (.defn (.group subs) i) = some (compAbs ct') := by
        rw [defKind_of_unroll hun, compAbs_subst, hsub.compAbs_eq]
      have hfree : ∀ y, y ∈ u0.freeIdx → y ∈ (Ty.defn (.group subs) i).freeIdx := by
        intro y hy
        simp only [Ty.freeIdx]
        exact Ty.freeIdx_of_mem hmemst (by simp [Ty.freeIdx, hy])
      subst hu
      cases u0 with
      | idx x =>
        simp only [Ty.subst, unrollSubst, Option.getD_none, TypeCtx.resolve] at hr
        have hmem : d' ∈ Δ.types := List.mem_of_getElem? hr
        have hcl : d'.freeIdx = [] := (hΔ d' hmem).1
        simp only [TypeCtx.unrollUse, TypeCtx.withRecs, hr] at hunroll
        refine ⟨(hΔ d' hmem).2, ?_, by rw [defKind_of_unroll hunroll, hkd]⟩
        have hx : x ∈ (Ty.defn (.group subs) i).freeIdx := hfree x (by simp [Ty.freeIdx])
        have hne : (Ty.defn (.group subs) i).freeIdx ≠ [] := List.ne_nil_of_mem hx
        have hle : mu0 d' ≤ (Δ.types.map mu0).sum :=
          le_sum_of_mem' (List.mem_map_of_mem hmem)
        simp only [TypeCtx.fuel, hcl, hne, ↓reduceIte]
        omega
      | recv j =>
        cases hu0 with
        | recv hj =>
          have hj' : j < subs.toList.length := by
            have := (List.getElem?_eq_some_iff.1 hj).1
            simpa [TypeCtx.withRecs] using this
          have hji : j < i := by simpa [before] using hb
          have hjl : j < subs.length := by simpa [Ty.length] using hj'
          simp only [Ty.subst, unrollSubst, hjl, ↓reduceIte, Option.getD_some,
            TypeCtx.resolve, Option.some.injEq] at hr
          subst hr
          refine ⟨.defn hg hjl, ?_, ?_⟩
          · simp only [TypeCtx.fuel, mu0, Ty.freeIdx]
            by_cases hf : subs.freeIdx = [] <;> simp [hf] <;> omega
          · simp only [TypeCtx.unrollUse, TypeCtx.withRecs] at hunroll
            have h2 := unrolldt_defn subs j
            rw [hunroll, Option.map_some] at h2
            rw [defKind_of_unroll h2, compAbs_subst, hkd]
      | dt e =>
        rw [Ty.recFree_dt e _ (fun _ => rfl)] at hr
        simp only [TypeCtx.resolve, Option.some.injEq] at hr
        subst hr
        have he : TyOk Δ e :=
          TyOk.def_congr (Δ₁ := Δ.withRecs subs.toList) (Δ₂ := Δ) rfl hu0.dt_inv
        simp only [TypeCtx.unrollUse] at hunroll
        refine ⟨he, ?_, by rw [defKind_of_unroll hunroll, hkd]⟩
        have hlt := mu0_lt_sq he
        simp only [Ty.size] at hsz
        have hmu : mu0 e < mu0 (.defn (.group subs) i) := by
          have h2 : e.size * e.size ≤ (subs.size + 1) * (subs.size + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          have : mu0 (.defn (.group subs) i) = (subs.size + 1) * (subs.size + 1) + i := rfl
          rw [this]
          omega
        have hfe : e.freeIdx ≠ [] → (Ty.defn (.group subs) i).freeIdx ≠ [] := by
          intro hne
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
          exact List.ne_nil_of_mem (hfree y (by simpa [Ty.freeIdx] using hy))
        unfold TypeCtx.fuel
        by_cases h1 : e.freeIdx = []
        · simp only [h1, ↓reduceIte]; split <;> omega
        · simp only [h1, hfe h1, ↓reduceIte]; omega


/-! ## Completeness: the bounded search and closure -/

@[simp] theorem TypeCtx.resolve_dt (Δ : TypeCtx) (d : DefType) : Δ.resolve (.dt d) = some d := rfl

theorem TypeCtx.reach_succ_iff {Δ : TypeCtx} {P : DefType → Bool} {n : Nat} {d : DefType} :
    Δ.reach P (n + 1) d = true ↔
      P d = true ∨ ∃ u ∈ supersOf d, ∃ d', Δ.resolve u = some d' ∧ Δ.reach P n d' = true := by
  simp only [TypeCtx.reach, Bool.or_eq_true, List.any_eq_true]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, ?_⟩
    revert h
    cases Δ.resolve u <;> simp
  · rintro ⟨u, hu, d', hr, h⟩
    refine ⟨u, hu, ?_⟩
    rw [hr]
    exact h

theorem TypeCtx.reach_mono {Δ : TypeCtx} {P : DefType → Bool} :
    ∀ {n m : Nat} {d : DefType}, Δ.reach P n d = true → n ≤ m → Δ.reach P m d = true
  | 0, m, _, h, _ => reach_of h m
  | _ + 1, 0, _, _, hle => by omega
  | n + 1, m + 1, d, h, hle => by
    rw [TypeCtx.reach_succ_iff] at h ⊢
    rcases h with h | ⟨u, hu, d', hr, h⟩
    · exact .inl h
    · exact .inr ⟨u, hu, d', hr, reach_mono h (by omega)⟩

theorem TypeCtx.reach_complete {Δ : TypeCtx} (hΔ : Δ.Ok) {P : DefType → Bool} {d e : DefType}
    (h : Δ.Reach d e) : TyOk Δ d → P e = true → Δ.reach P (Δ.fuel d) d = true := by
  induction h with
  | refl => intro _ hP; exact reach_of hP _
  | @step d d' e u hu hr _ ih =>
    intro hd hP
    obtain ⟨hok, hlt, -⟩ := Δ.super_step hΔ hd hu hr
    have ih' := ih hok hP
    obtain ⟨m, hm⟩ : ∃ m, Δ.fuel d = m + 1 := ⟨Δ.fuel d - 1, by omega⟩
    rw [hm, TypeCtx.reach_succ_iff]
    exact .inr ⟨u, hu, d', hr, reach_mono ih' (by omega)⟩

theorem TypeCtx.Reach.ok_kind {Δ : TypeCtx} (hΔ : Δ.Ok) {d e : DefType} (h : Δ.Reach d e) :
    TyOk Δ d → TyOk Δ e ∧ defKind e = defKind d := by
  induction h with
  | refl => intro hd; exact ⟨hd, rfl⟩
  | step hu hr _ ih =>
    intro hd
    obtain ⟨hok, -, hk⟩ := Δ.super_step hΔ hd hu hr
    obtain ⟨h1, h2⟩ := ih hok
    exact ⟨h1, h2.trans hk⟩

theorem TypeCtx.Ok.clos_types {Δ : TypeCtx} (hΔ : Δ.Ok) {x : Nat} {d : DefType}
    (hx : Δ.types[x]? = some d) : d.clos Δ.types = d := by
  rw [hΔ.clos_eq]
  exact Ty.subst_closed d _ (fun _ => rfl) (hΔ d (List.mem_of_getElem? hx)).1

theorem TypeCtx.resolve_subst_eq {Δ : TypeCtx} (hΔ : Δ.Ok) {u' u : CTypeUse}
    (h : u'.subst Δ.closSubst = u.subst Δ.closSubst) {b : DefType}
    (hb : Δ.resolve u = some b) :
    ∃ a, Δ.resolve u' = some a ∧ a.clos Δ.types = b.clos Δ.types := by
  have key : ∀ {w : CTypeUse} {c : DefType}, Δ.resolve w = some c →
      w.subst Δ.closSubst = .dt (c.clos Δ.types) := by
    intro w c hw
    cases w with
    | idx x =>
      simp only [TypeCtx.resolve] at hw
      rw [TypeCtx.subst_idx, hw, hΔ.clos_types hw]
      rfl
    | recv i => simp [TypeCtx.resolve] at hw
    | dt e =>
      simp only [TypeCtx.resolve, Option.some.injEq] at hw
      subst hw
      simp only [Ty.subst, hΔ.clos_eq]
  rw [key hb] at h
  cases u' with
  | idx y =>
    cases hy : Δ.types[y]? with
    | none => rw [TypeCtx.subst_idx, hy] at h; simp at h
    | some c =>
      refine ⟨c, hy, ?_⟩
      rw [key (show Δ.resolve (.idx y) = some c from hy)] at h
      simpa using h
  | recv i => simp [Ty.subst, TypeCtx.closSubst_recv] at h
  | dt c =>
    refine ⟨c, rfl, ?_⟩
    rw [key (show Δ.resolve (.dt c) = some c from rfl)] at h
    simpa using h

theorem TypeCtx.super_sim {Δ : TypeCtx} (hΔ : Δ.Ok) {a b b' : DefType} {u : CTypeUse}
    (hc : a.clos Δ.types = b.clos Δ.types) (hu : u ∈ supersOf b)
    (hr : Δ.resolve u = some b') :
    ∃ u' a', u' ∈ supersOf a ∧ Δ.resolve u' = some a' ∧ a'.clos Δ.types = b'.clos Δ.types := by
  obtain ⟨fin, sups, ct, j, hub, hj⟩ := supersOf_mem hu
  rw [hΔ.clos_eq, hΔ.clos_eq] at hc
  have e1 := unrolldt_subst Δ.closSubst Δ.closSubst_recv Δ.closSubst_recFree a
  have e2 := unrolldt_subst Δ.closSubst Δ.closSubst_recv Δ.closSubst_recFree b
  rw [hc, e2, hub] at e1
  cases hua : unrolldt a with
  | none => rw [hua] at e1; simp at e1
  | some st' =>
    rw [hua] at e1
    cases st' with
    | sub fin' sups' ct' =>
      simp only [Option.map_some, Option.some.injEq, Ty.subst, Ty.sub.injEq] at e1
      have hl := congrArg Ty.toList e1.2.1
      rw [Ty.toList_subst, Ty.toList_subst] at hl
      have hj' : (sups'.toList.map (·.subst Δ.closSubst))[j]? =
          some (u.subst Δ.closSubst) := by
        rw [← hl, List.getElem?_map, hj]; rfl
      rw [List.getElem?_map] at hj'
      cases hu' : sups'.toList[j]? with
      | none => rw [hu'] at hj'; simp at hj'
      | some u' =>
        rw [hu'] at hj'
        simp only [Option.map_some, Option.some.injEq] at hj'
        obtain ⟨a', hra, hca⟩ := TypeCtx.resolve_subst_eq hΔ hj' hr
        refine ⟨u', a', ?_, hra, hca⟩
        rw [supersOf_of_unroll hua]
        simpa [Ty.supers] using List.mem_of_getElem? hu'

theorem TypeCtx.Reach.sim {Δ : TypeCtx} (hΔ : Δ.Ok) {b b' : DefType} (h : Δ.Reach b b') :
    ∀ {a : DefType}, a.clos Δ.types = b.clos Δ.types →
      ∃ a', Δ.Reach a a' ∧ a'.clos Δ.types = b'.clos Δ.types := by
  induction h with
  | refl => intro a hc; exact ⟨a, .refl a, hc⟩
  | step hu hr _ ih =>
    intro a hc
    obtain ⟨u', a1, hu', hr', hc'⟩ := TypeCtx.super_sim hΔ hc hu hr
    obtain ⟨a', ha', hc''⟩ := ih hc'
    exact ⟨a', .step hu' hr' ha', hc''⟩

theorem defKind_clos {Δ : TypeCtx} (hΔ : Δ.Ok) {a b : DefType}
    (hc : a.clos Δ.types = b.clos Δ.types) : defKind a = defKind b := by
  have k : ∀ d : DefType, defKind (d.clos Δ.types) = defKind d := by
    intro d
    rw [hΔ.clos_eq]
    unfold defKind
    rw [unrolldt_subst Δ.closSubst Δ.closSubst_recv Δ.closSubst_recFree, Option.map_map]
    congr 1
    funext st
    cases st
    simp [Ty.subst, Ty.body, compAbs_subst]
  rw [← k a, hc, k b]

theorem TypeCtx.checkDef_exists {Δ : TypeCtx} {d₁ d₂ : DefType} (h : Δ.checkDef d₁ d₂ = true) :
    ∃ e, Δ.Reach d₁ e ∧ e.clos Δ.types = d₂.clos Δ.types := by
  obtain ⟨e, he, hP⟩ := reach_sound h
  exact ⟨e, he, by simpa using hP⟩

theorem TypeCtx.checkDef_of_reach {Δ : TypeCtx} (hΔ : Δ.Ok) {d₁ e d₂ : DefType}
    (hd : TyOk Δ d₁) (h : Δ.Reach d₁ e) (hc : e.clos Δ.types = d₂.clos Δ.types) :
    Δ.checkDef d₁ d₂ = true :=
  Δ.reach_complete hΔ h hd (by simp [hc])

theorem TypeCtx.checkDef_trans {Δ : TypeCtx} (hΔ : Δ.Ok) {d₁ d₂ d₃ : DefType}
    (hd : TyOk Δ d₁) (h₁ : Δ.checkDef d₁ d₂ = true) (h₂ : Δ.checkDef d₂ d₃ = true) :
    Δ.checkDef d₁ d₃ = true := by
  obtain ⟨e1, he1, hc1⟩ := TypeCtx.checkDef_exists h₁
  obtain ⟨e2, he2, hc2⟩ := TypeCtx.checkDef_exists h₂
  obtain ⟨e', he', hc'⟩ := he2.sim hΔ hc1
  exact TypeCtx.checkDef_of_reach hΔ hd (he1.trans he') (hc'.trans hc2)

theorem TypeCtx.checkDef_kind {Δ : TypeCtx} (hΔ : Δ.Ok) {d₁ d₂ : DefType}
    (hd : TyOk Δ d₁) (h : Δ.checkDef d₁ d₂ = true) : defKind d₂ = defKind d₁ := by
  obtain ⟨e, he, hc⟩ := TypeCtx.checkDef_exists h
  rw [← defKind_clos hΔ hc]
  exact (he.ok_kind hΔ hd).2

/-! ## Completeness: heap types -/

theorem TypeCtx.checkUseAbs_iff {Δ : TypeCtx} {u : CTypeUse} {d : DefType} {b : AbsHeapType}
    (hr : Δ.resolve u = some d) :
    Δ.checkUseAbs u b = true ↔ ∃ k, defKind d = some k ∧ absSub k b = true := by
  unfold TypeCtx.checkUseAbs
  rw [hr]
  change (match defKind d with | some k => absSub k b | none => false) = true ↔ _
  cases defKind d <;> simp

theorem TypeCtx.checkHeap_use_left {Δ : TypeCtx} {u : CTypeUse} {d : DefType}
    (hr : Δ.resolve u = some d) (h : CHeapType) :
    Δ.checkHeap (.use u) h = Δ.checkHeap (.use (.dt d)) h := by
  cases h with
  | bot => rfl
  | abs b => simp only [TypeCtx.checkHeap, TypeCtx.checkUseAbs, hr, TypeCtx.resolve_dt]
  | use v =>
    cases hv : Δ.resolve v <;> simp [TypeCtx.checkHeap, hr, hv]

theorem TypeCtx.checkHeap_use_right {Δ : TypeCtx} {u : CTypeUse} {d : DefType}
    (hr : Δ.resolve u = some d) (h : CHeapType) :
    Δ.checkHeap h (.use u) = Δ.checkHeap h (.use (.dt d)) := by
  cases h with
  | bot => rfl
  | abs a => simp only [TypeCtx.checkHeap, TypeCtx.checkUseAbs, hr, TypeCtx.resolve_dt]
  | use v =>
    cases hv : Δ.resolve v <;> simp [TypeCtx.checkHeap, hr, hv]

theorem TypeCtx.checkHeap_refl (Δ : TypeCtx) : ∀ h : CHeapType, Δ.checkHeap h h = true
  | .bot => rfl
  | .abs a => absSub_refl a
  | .use u => by
    cases hu : Δ.resolve u with
    | none => simp [TypeCtx.checkHeap, hu]
    | some d =>
      simp only [TypeCtx.checkHeap, hu, TypeCtx.checkDef]
      exact reach_of (by simp) _

theorem TypeCtx.checkHeap_bottom {Δ : TypeCtx} {a t : AbsHeapType} (ht : botTop a = some t)
    {h : CHeapType} (hb : h ≠ .bot) (hs : Δ.checkHeap h (.abs t) = true) :
    Δ.checkHeap (.abs a) h = true := by
  cases h with
  | bot => exact absurd rfl hb
  | abs x => exact absSub_of_botTop ht hs
  | use u => simp only [TypeCtx.checkHeap, ht]; exact hs

theorem TypeCtx.checkHeap_trans {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {h₁ h' h₂ : CHeapType} (ok₁ : TyOk Δ h₁) (ok' : TyOk Δ h')
    (c₁ : Δ.checkHeap h₁ h' = true) (c₂ : Δ.checkHeap h' h₂ = true) :
    Δ.checkHeap h₁ h₂ = true := by
  cases h₁ with
  | bot => rfl
  | abs a =>
    cases h' with
    | bot => simp [TypeCtx.checkHeap] at c₁
    | abs a' =>
      cases h₂ with
      | bot => simp [TypeCtx.checkHeap] at c₂
      | abs b => exact absSub_trans c₁ c₂
      | use w =>
        simp only [TypeCtx.checkHeap] at c₁ c₂ ⊢
        cases ht : botTop a' with
        | none => simp [ht] at c₂
        | some t => rw [absSub_eq_of_botTop c₁ ht]; simpa [ht] using c₂
    | use v =>
      obtain ⟨dv, hv, okv⟩ := TypeCtx.resolve_ok hΔ hr ok'.use_inv
      simp only [TypeCtx.checkHeap] at c₁
      cases ht : botTop a with
      | none => simp [ht] at c₁
      | some t =>
        simp only [ht] at c₁
        obtain ⟨k, hk, hkt⟩ := (TypeCtx.checkUseAbs_iff hv).1 c₁
        cases h₂ with
        | bot => simp [TypeCtx.checkHeap] at c₂
        | abs b =>
          simp only [TypeCtx.checkHeap] at c₂
          obtain ⟨k', hk', hkb⟩ := (TypeCtx.checkUseAbs_iff hv).1 c₂
          rw [hk] at hk'
          cases hk'
          exact absSub_botTop_trans ht hkt hkb
        | use w =>
          rw [TypeCtx.checkHeap_use_left hv] at c₂
          cases hw : Δ.resolve w with
          | none => simp [TypeCtx.checkHeap, hw] at c₂
          | some dw =>
            simp only [TypeCtx.checkHeap, hw] at c₂
            have := TypeCtx.checkDef_kind hΔ okv c₂
            simp only [TypeCtx.checkHeap, ht]
            exact (TypeCtx.checkUseAbs_iff hw).2 ⟨k, by rw [this, hk], hkt⟩
  | use u =>
    obtain ⟨du, hu, oku⟩ := TypeCtx.resolve_ok hΔ hr ok₁.use_inv
    rw [TypeCtx.checkHeap_use_left hu] at c₁ ⊢
    cases h' with
    | bot => simp [TypeCtx.checkHeap] at c₁
    | abs a' =>
      simp only [TypeCtx.checkHeap] at c₁
      obtain ⟨k, hk, hka⟩ := (TypeCtx.checkUseAbs_iff (u := .dt du) rfl).1 c₁
      cases h₂ with
      | bot => simp [TypeCtx.checkHeap] at c₂
      | abs b =>
        simp only [TypeCtx.checkHeap] at c₂ ⊢
        exact (TypeCtx.checkUseAbs_iff rfl).2 ⟨k, hk, absSub_trans hka c₂⟩
      | use w =>
        simp only [TypeCtx.checkHeap] at c₂
        cases ht : botTop a' with
        | none => simp [ht] at c₂
        | some t =>
          obtain ⟨c, rfl⟩ := defKind_compAbs hk
          exact (compAbs_not_bot c hka ht).elim
    | use v =>
      obtain ⟨dv, hv, okv⟩ := TypeCtx.resolve_ok hΔ hr ok'.use_inv
      rw [TypeCtx.checkHeap_use_right hv] at c₁
      rw [TypeCtx.checkHeap_use_left hv] at c₂
      simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt] at c₁
      cases h₂ with
      | bot => simp [TypeCtx.checkHeap] at c₂
      | abs b =>
        simp only [TypeCtx.checkHeap] at c₂ ⊢
        obtain ⟨k, hk, hkb⟩ := (TypeCtx.checkUseAbs_iff rfl).1 c₂
        refine (TypeCtx.checkUseAbs_iff rfl).2 ⟨k, ?_, hkb⟩
        rw [← TypeCtx.checkDef_kind hΔ oku c₁]
        exact hk
      | use w =>
        cases hw : Δ.resolve w with
        | none => simp [TypeCtx.checkHeap, hw] at c₂
        | some dw =>
          rw [TypeCtx.checkHeap_use_right hw] at c₂ ⊢
          simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt] at c₂ ⊢
          exact TypeCtx.checkDef_trans hΔ oku c₁ c₂


/-! ## Completeness -/

theorem TyOk.ref_inv {Δ : TypeCtx} {n : Bool} {h : CHeapType} (hk : TyOk Δ (.ref n h)) :
    TyOk Δ h := by
  cases hk with
  | ref h => exact h

theorem TyOk.refv_inv {Δ : TypeCtx} {r : CRefType} (hk : TyOk Δ (.refv r)) : TyOk Δ r := by
  cases hk with
  | refv h => exact h

theorem TyOk.val_inv {Δ : TypeCtx} {t : CValType} (hk : TyOk Δ (.val t)) : TyOk Δ t := by
  cases hk with
  | val h => exact h

theorem TyOk.field_inv {Δ : TypeCtx} {m : Mutability} {s : CStorageType}
    (hk : TyOk Δ (.field m s)) : TyOk Δ s := by
  cases hk with
  | field h => exact h

theorem TyOk.struct_inv {Δ : TypeCtx} {fs : Ty (.list .field)} (hk : TyOk Δ (.struct fs)) :
    TyOk Δ fs := by
  cases hk with
  | struct h => exact h

theorem TyOk.array_inv {Δ : TypeCtx} {f : CFieldType} (hk : TyOk Δ (.array f)) : TyOk Δ f := by
  cases hk with
  | array h => exact h

theorem TyOk.func_inv {Δ : TypeCtx} {ps rs : Ty (.list .val)} (hk : TyOk Δ (.func ps rs)) :
    TyOk Δ ps ∧ TyOk Δ rs := by
  cases hk with
  | func hp hr => exact ⟨hp, hr⟩

theorem TyOk.cons_inv {Δ : TypeCtx} {k : TKind} {a : Ty k} {l : Ty (.list k)}
    (hk : TyOk Δ (.cons a l)) : TyOk Δ a ∧ TyOk Δ l := by
  cases hk with
  | cons ha hl => exact ⟨ha, hl⟩

theorem forall2B_length {α : Type} {f : α → α → Bool} :
    ∀ {l₁ l₂ : List α}, forall2B f l₁ l₂ = true → l₁.length = l₂.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [forall2B, Bool.and_eq_true] at h
    simp [forall2B_length h.2]
  | [], _ :: _, h => by simp [forall2B] at h
  | _ :: _, [], h => by simp [forall2B] at h

theorem TypeCtx.checkVal_botv (Δ : TypeCtx) : ∀ t : CValType, Δ.checkVal .botv t = true
  | .num _ => rfl
  | .vec _ => rfl
  | .refv _ => rfl
  | .botv => rfl

/-- **Completeness** of the checker on valid types in a well-formed context with
no `RECS`. -/
theorem Sub.complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) :
    ∀ {k : TKind} {a b : Ty k}, Sub Δ a b → TyOk Δ a → TyOk Δ b → Sub.checkK Δ k a b = true
  | _, _, _, .heapRefl, _, _ => Δ.checkHeap_refl _
  | _, _, _, .heapTrans hok h₁ h₂, ha, hb =>
    TypeCtx.checkHeap_trans hΔ hr ha hok (Sub.complete hΔ hr h₁ ha hok)
      (Sub.complete hΔ hr h₂ hok hb)
  | _, _, _, .eqAny, _, _ => rfl
  | _, _, _, .i31Eq, _, _ => rfl
  | _, _, _, .structEq, _, _ => rfl
  | _, _, _, .arrayEq, _, _ => rfl
  | _, _, _, .defStruct (.mk hu), _, _ =>
    (TypeCtx.checkUseAbs_iff (TypeCtx.resolve_dt Δ _)).2 ⟨_, defKind_of_unroll hu, rfl⟩
  | _, _, _, .defArray (.mk hu), _, _ =>
    (TypeCtx.checkUseAbs_iff (TypeCtx.resolve_dt Δ _)).2 ⟨_, defKind_of_unroll hu, rfl⟩
  | _, _, _, .defFunc (.mk hu), _, _ =>
    (TypeCtx.checkUseAbs_iff (TypeCtx.resolve_dt Δ _)).2 ⟨_, defKind_of_unroll hu, rfl⟩
  | _, _, _, .defDef h, ha, hb => by
    show Δ.checkHeap _ _ = true
    simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt]
    exact Sub.complete hΔ hr h ha.use_inv.dt_inv hb.use_inv.dt_inv
  | _, _, _, .idxL (x := x) (d := d) hx hs, _, hb => by
    show Δ.checkHeap _ _ = true
    rw [TypeCtx.checkHeap_use_left (show Δ.resolve (.idx x) = some d from hx)]
    exact Sub.complete hΔ hr hs (.use (.dt (hΔ _ (List.mem_of_getElem? hx)).2)) hb
  | _, _, _, .idxR (x := x) (d := d) hx hs, ha, _ => by
    show Δ.checkHeap _ _ = true
    rw [TypeCtx.checkHeap_use_right (show Δ.resolve (.idx x) = some d from hx)]
    exact Sub.complete hΔ hr hs ha (.use (.dt (hΔ _ (List.mem_of_getElem? hx)).2))
  | _, _, _, .recStruct h, _, _ => by simp [hr] at h
  | _, _, _, .recArray h, _, _ => by simp [hr] at h
  | _, _, _, .recFunc h, _, _ => by simp [hr] at h
  | _, _, _, .recSub h _, _, _ => by simp [hr] at h
  | _, _, _, .none hs hne, _, hb =>
    TypeCtx.checkHeap_bottom (a := .none) rfl hne (Sub.complete hΔ hr hs hb (.abs _))
  | _, _, _, .nofunc hs hne, _, hb =>
    TypeCtx.checkHeap_bottom (a := .nofunc) rfl hne (Sub.complete hΔ hr hs hb (.abs _))
  | _, _, _, .noexn hs hne, _, hb =>
    TypeCtx.checkHeap_bottom (a := .noexn) rfl hne (Sub.complete hΔ hr hs hb (.abs _))
  | _, _, _, .noextern hs hne, _, hb =>
    TypeCtx.checkHeap_bottom (a := .noextern) rfl hne (Sub.complete hΔ hr hs hb (.abs _))
  | _, _, _, .bot, _, _ => rfl
  | _, _, _, .refNonNull h, ha, hb => by
    show Δ.checkRef _ _ = true
    simp only [TypeCtx.checkRef, Bool.not_false, Bool.true_or, Bool.true_and]
    exact Sub.complete hΔ hr h ha.ref_inv hb.ref_inv
  | _, _, _, .refNull h, ha, hb => by
    show Δ.checkRef _ _ = true
    simp only [TypeCtx.checkRef, Bool.or_true, Bool.true_and]
    exact Sub.complete hΔ hr h ha.ref_inv hb.ref_inv
  | _, _, _, .num, _, _ => by simp [Sub.checkK, TypeCtx.checkVal]
  | _, _, _, .vec, _, _ => by simp [Sub.checkK, TypeCtx.checkVal]
  | _, _, _, .refv h, ha, hb => by
    have := Sub.complete hΔ hr h ha.refv_inv hb.refv_inv
    exact this
  | _, _, _, .botv, _, _ => Δ.checkVal_botv _
  | _, _, _, .val h, ha, hb => by
    have := Sub.complete hΔ hr h ha.val_inv hb.val_inv
    exact this
  | _, _, _, .pack, _, _ => by simp [Sub.checkK, TypeCtx.checkStorage]
  | _, _, _, .fieldConst h, ha, hb => by
    have := Sub.complete hΔ hr h ha.field_inv hb.field_inv
    exact this
  | _, _, _, .fieldVar h₁ h₂, ha, hb => by
    show Δ.checkField _ _ = true
    simp only [TypeCtx.checkField, Bool.and_eq_true]
    exact ⟨Sub.complete hΔ hr h₁ ha.field_inv hb.field_inv,
      Sub.complete hΔ hr h₂ hb.field_inv ha.field_inv⟩
  | _, _, _, @Sub.struct _ fs₁ extra fs₂ h, ha, hb => by
    have hc := Sub.complete hΔ hr h (TyOk.app_left ha.struct_inv) hb.struct_inv
    change forall2B (Sub.checkK Δ .field) fs₁.toList fs₂.toList = true at hc
    have hlen := forall2B_length hc
    show Δ.checkComp _ _ = true
    simp only [TypeCtx.checkComp, Ty.app, Ty.toList_ofList, List.length_append,
      Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [List.take_left' hlen]
    exact hc
  | _, _, _, .array h, ha, hb => by
    have := Sub.complete hΔ hr h ha.array_inv hb.array_inv
    exact this
  | _, _, _, .func hp hr', ha, hb => by
    show Δ.checkComp _ _ = true
    simp only [TypeCtx.checkComp, Bool.and_eq_true]
    exact ⟨Sub.complete hΔ hr hp hb.func_inv.1 ha.func_inv.1,
      Sub.complete hΔ hr hr' ha.func_inv.2 hb.func_inv.2⟩
  | _, _, _, .defRefl h, _, _ => by
    show Δ.checkDef _ _ = true
    exact TypeCtx.reach_of (by simp [h]) _
  | _, _, _, .defSuper hu hj hs, ha, hb => by
    show Δ.checkDef _ _ = true
    have hok := ha.unroll_super hu (List.mem_of_getElem? hj)
    have hc := Sub.complete hΔ hr hs hok (.use (.dt hb))
    obtain ⟨d', hd', -⟩ := TypeCtx.resolve_ok hΔ hr hok.use_inv
    change Δ.checkHeap _ _ = true at hc
    rw [TypeCtx.checkHeap_use_left hd'] at hc
    simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt] at hc
    obtain ⟨e, he, hce⟩ := TypeCtx.checkDef_exists hc
    refine TypeCtx.checkDef_of_reach hΔ ha (.step ?_ hd' he) hce
    rw [supersOf_of_unroll hu]
    simpa [Ty.supers] using List.mem_of_getElem? hj
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons h hl, ha, hb => by
    show forall2B _ (_ :: _) (_ :: _) = true
    simp only [forall2B, Bool.and_eq_true]
    exact ⟨Sub.complete hΔ hr h ha.cons_inv.1 hb.cons_inv.1,
      Sub.complete hΔ hr hl ha.cons_inv.2 hb.cons_inv.2⟩

theorem Sub.check_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {k : TKind}
    {a b : Ty k} (h : Sub Δ a b) (ha : TyOk Δ a) (hb : TyOk Δ b) : Sub.check Δ a b = true :=
  Sub.complete hΔ hr h ha hb

/-- The checker decides subtyping between valid types in a well-formed context
without `RECS` (every context after the type section). -/
theorem Sub.check_iff {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {k : TKind}
    {a b : Ty k} (ha : TyOk Δ a) (hb : TyOk Δ b) : Sub.check Δ a b = true ↔ Sub Δ a b :=
  ⟨Sub.check_sound, fun h => Sub.check_complete hΔ hr h ha hb⟩

/-! ## External types -/

/-- `Externtype_sub`, as a Boolean check. -/
def ExternSub.check (Δ : TypeCtx) : CExternType → CExternType → Bool
  | .tag d₁, .tag d₂ => Δ.checkDef d₁ d₂ && Δ.checkDef d₂ d₁
  | .global ⟨.const, t₁⟩, .global ⟨.const, t₂⟩ => Δ.checkVal t₁ t₂
  | .global ⟨.var, t₁⟩, .global ⟨.var, t₂⟩ => Δ.checkVal t₁ t₂ && Δ.checkVal t₂ t₁
  | .mem ⟨a₁, l₁⟩, .mem ⟨a₂, l₂⟩ => decide (a₁ = a₂) && decide (LimitsSub l₁ l₂)
  | .table ⟨a₁, l₁, r₁⟩, .table ⟨a₂, l₂, r₂⟩ =>
    decide (a₁ = a₂) && decide (LimitsSub l₁ l₂) && Δ.checkRef r₁ r₂ && Δ.checkRef r₂ r₁
  | .func d₁, .func d₂ => Δ.checkDef d₁ d₂
  | _, _ => false

theorem ExternSub.check_sound {Δ : TypeCtx} {a b : CExternType}
    (h : ExternSub.check Δ a b = true) : ExternSub Δ a b := by
  rcases a with d₁ | ⟨m₁, t₁⟩ | ⟨a₁, l₁⟩ | ⟨a₁, l₁, r₁⟩ | d₁ <;>
    rcases b with d₂ | ⟨m₂, t₂⟩ | ⟨a₂, l₂⟩ | ⟨a₂, l₂, r₂⟩ | d₂ <;>
    try (simp [ExternSub.check] at h; done)
  · simp only [ExternSub.check, Bool.and_eq_true] at h
    exact .tag ⟨Δ.checkDef_sound h.1, Δ.checkDef_sound h.2⟩
  · cases m₁ <;> cases m₂ <;> simp only [ExternSub.check, Bool.and_eq_true] at h
    · exact .global (.const (Δ.checkVal_sound h))
    · simp at h
    · simp at h
    · exact .global (.var (Δ.checkVal_sound h.1) (Δ.checkVal_sound h.2))
  · simp only [ExternSub.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hl⟩ := h
    exact .mem (.mk hl)
  · simp only [ExternSub.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, hl⟩, h₁⟩, h₂⟩ := h
    exact .table (.mk hl (Δ.checkRef_sound h₁) (Δ.checkRef_sound h₂))
  · exact .func (Δ.checkDef_sound h)

theorem ExternSub.check_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {a b : CExternType} (ha : ExternTypeOk Δ a) (hb : ExternTypeOk Δ b)
    (h : ExternSub Δ a b) : ExternSub.check Δ a b = true := by
  cases h with
  | tag h =>
    cases ha with
    | tag ha =>
      cases hb with
      | tag hb =>
        simp only [ExternSub.check, Bool.and_eq_true]
        exact ⟨Sub.complete hΔ hr h.1 ha.1 hb.1, Sub.complete hΔ hr h.2 hb.1 ha.1⟩
  | global h =>
    cases ha with
    | global ha =>
      cases hb with
      | global hb =>
        cases h with
        | const h => exact Sub.complete hΔ hr h ha hb
        | var h₁ h₂ =>
          simp only [ExternSub.check, Bool.and_eq_true]
          exact ⟨Sub.complete hΔ hr h₁ ha hb, Sub.complete hΔ hr h₂ hb ha⟩
  | mem h =>
    cases h with
    | mk hl => simp [ExternSub.check, hl]
  | table h =>
    cases ha with
    | table ha =>
      cases hb with
      | table hb =>
        cases h with
        | mk hl h₁ h₂ =>
          simp only [ExternSub.check, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨by trivial, hl⟩, Sub.complete hΔ hr h₁ ha.2 hb.2⟩, Sub.complete hΔ hr h₂ hb.2 ha.2⟩
  | func h =>
    cases ha with
    | func ha _ =>
      cases hb with
      | func hb _ => exact Sub.complete hΔ hr h ha hb

/-- The extern checker decides `ExternSub` between valid extern types in a
well-formed context without `RECS`. -/
theorem ExternSub.check_iff {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {a b : CExternType} (ha : ExternTypeOk Δ a) (hb : ExternTypeOk Δ b) :
    ExternSub.check Δ a b = true ↔ ExternSub Δ a b :=
  ⟨ExternSub.check_sound, ExternSub.check_complete hΔ hr ha hb⟩

end Silmaril.Wasm.Validation
