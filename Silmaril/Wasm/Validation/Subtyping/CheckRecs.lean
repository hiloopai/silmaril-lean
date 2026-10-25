module

public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # A subtyping checker under non-empty `RECS` (§2.2)

`Sub.check` (`Subtyping/Check.lean`) is complete only when `Δ.recs = []`. Inside
`Deftype_ok` a recursive group is checked under `C, RECS subtype*`, where the
rules `Heaptype_sub/rec-struct`, `rec-array`, `rec-func` and `rec-sub` apply to
`REC i` heap types. This file extends the checker with those rules:

* `REC i <: REC i` (reflexivity);
* `REC i <: absheaptype` via the kind of `C.RECS[i]` (`rec-struct/array/func`);
* `REC i <: ht` via a declared supertype `u` of `C.RECS[i]` and `u <: ht`
  (`rec-sub` and `trans`), searched with fuel `|C.RECS|` (supertypes of a valid
  group point strictly backwards, `before`).

**The validity oracle.** The step `REC i <: u <: ht` goes through
`Heaptype_sub/trans`, whose premise is `C ⊢ u : OK`. For `u = REC j` and
`u = _IDX x` this is decidable from the context; for `u = _DEF d` it is the full
`Deftype_ok`, which in turn depends on this checker (a later unit closes the
knot). So the checker is parameterised by an oracle `okD : DefType → Bool` for
the validity of `_DEF` supertypes of `RECS` entries (`Sub.checkRWith okD`):

* `Sub.checkRWith_sound`: sound whenever `okD` is sound;
* `Sub.checkRWith_complete`: complete for valid types in a well-formed context
  (`Δ.Ok`) whose `RECS` are a valid group (`Δ.RecsOk`), provided `okD` accepts
  the `_DEF` supertypes of `RECS` entries (`Δ.OracleOk okD`).

`Sub.checkR` (a separate recursive-type checker justification (not included in this package)) instantiates `okD` with the sound
`TyOk.check`.
-/

namespace Silmaril.Wasm.Validation

/-! ## Definitions -/

/-- Decidable validity of a type use as the middle of `Heaptype_sub/trans`
(`_DEF` through the oracle). -/
def TypeCtx.midOk (Δ : TypeCtx) (okD : DefType → Bool) : CTypeUse → Bool
  | .recv j => (Δ.recs[j]?).isSome
  | .idx x => (Δ.types[x]?).isSome
  | .dt d => okD d

/-- The direct rules for `REC i <: ht`: reflexivity and `rec-struct/array/func`. -/
def TypeCtx.recDirect (Δ : TypeCtx) (i : Nat) : CHeapType → Bool
  | .abs b =>
    match Δ.recs[i]? with
    | some st => absSub (compAbs st.body) b
    | none => false
  | .use (.recv j) => decide (i = j)
  | .use (.idx _) => false
  | .use (.dt _) => false
  | .bot => false

/-- Search from `REC i` along declared supertypes (fuel `n`). -/
def TypeCtx.recUp (Δ : TypeCtx) (okD : DefType → Bool) : Nat → Nat → CHeapType → Bool
  | 0, i, h => Δ.recDirect i h
  | n + 1, i, h => Δ.recDirect i h ||
      match Δ.recs[i]? with
      | some st => st.supers.any fun u => Δ.midOk okD u &&
          match u with
          | .recv j => Δ.recUp okD n j h
          | .idx x => Δ.checkHeap (.use (.idx x)) h
          | .dt d => Δ.checkHeap (.use (.dt d)) h
      | none => false

/-- `typeuse <: heaptype` with fuel `n` for `REC` chains. -/
def TypeCtx.checkUseR (Δ : TypeCtx) (okD : DefType → Bool) (n : Nat) : CTypeUse → CHeapType → Bool
  | .recv i, h => Δ.recUp okD n i h
  | .idx x, h => Δ.checkHeap (.use (.idx x)) h
  | .dt d, h => Δ.checkHeap (.use (.dt d)) h

/-- `Heaptype_sub` with the `REC` rules. -/
def TypeCtx.checkHeapR (Δ : TypeCtx) (okD : DefType → Bool) : CHeapType → CHeapType → Bool
  | .bot, _ => true
  | .abs a, .abs b => absSub a b
  | .abs a, .use u =>
    match botTop a with
    | some t => Δ.checkUseR okD Δ.recs.length u (.abs t)
    | none => false
  | .use u, h => Δ.checkUseR okD Δ.recs.length u h
  | .abs _, .bot => false

/-- `Reftype_sub`. -/
def TypeCtx.checkRefR (Δ : TypeCtx) (okD : DefType → Bool) : CRefType → CRefType → Bool
  | .ref n₁ h₁, .ref n₂ h₂ => (!n₁ || n₂) && Δ.checkHeapR okD h₁ h₂

/-- `Valtype_sub`. -/
def TypeCtx.checkValR (Δ : TypeCtx) (okD : DefType → Bool) : CValType → CValType → Bool
  | .num t₁, .num t₂ => decide (t₁ = t₂)
  | .vec t₁, .vec t₂ => decide (t₁ = t₂)
  | .refv r₁, .refv r₂ => Δ.checkRefR okD r₁ r₂
  | .botv, _ => true
  | _, _ => false

/-- `Storagetype_sub`. -/
def TypeCtx.checkStorageR (Δ : TypeCtx) (okD : DefType → Bool) :
    CStorageType → CStorageType → Bool
  | .val t₁, .val t₂ => Δ.checkValR okD t₁ t₂
  | .pack p₁, .pack p₂ => decide (p₁ = p₂)
  | _, _ => false

/-- `Fieldtype_sub`. -/
def TypeCtx.checkFieldR (Δ : TypeCtx) (okD : DefType → Bool) : CFieldType → CFieldType → Bool
  | .field .const z₁, .field .const z₂ => Δ.checkStorageR okD z₁ z₂
  | .field .var z₁, .field .var z₂ =>
    Δ.checkStorageR okD z₁ z₂ && Δ.checkStorageR okD z₂ z₁
  | _, _ => false

/-- `Comptype_sub`. -/
def TypeCtx.checkCompR (Δ : TypeCtx) (okD : DefType → Bool) : CCompType → CCompType → Bool
  | .struct fs₁, .struct fs₂ =>
    decide (fs₂.toList.length ≤ fs₁.toList.length) &&
      forall2B (Δ.checkFieldR okD) (fs₁.toList.take fs₂.toList.length) fs₂.toList
  | .array f₁, .array f₂ => Δ.checkFieldR okD f₁ f₂
  | .func ps₁ rs₁, .func ps₂ rs₂ =>
    forall2B (Δ.checkValR okD) ps₂.toList ps₁.toList &&
      forall2B (Δ.checkValR okD) rs₁.toList rs₂.toList
  | _, _ => false

/-- The checker at every sort. -/
def Sub.checkKR (okD : DefType → Bool) (Δ : TypeCtx) : (k : TKind) → Ty k → Ty k → Bool
  | .heap, a, b => Δ.checkHeapR okD a b
  | .ref, a, b => Δ.checkRefR okD a b
  | .val, a, b => Δ.checkValR okD a b
  | .storage, a, b => Δ.checkStorageR okD a b
  | .field, a, b => Δ.checkFieldR okD a b
  | .comp, a, b => Δ.checkCompR okD a b
  | .def, a, b => Δ.checkDef a b
  | .list k, a, b => forall2B (Sub.checkKR okD Δ k) a.toList b.toList
  | .use, _, _ => false
  | .sub, _, _ => false
  | .group, _, _ => false

/-- The subtyping checker with the `REC` rules, parameterised by a validity
oracle for `_DEF` supertypes of `RECS` entries. -/
def Sub.checkRWith (okD : DefType → Bool) (Δ : TypeCtx) {k : TKind} (a b : Ty k) : Bool :=
  Sub.checkKR okD Δ k a b

/-! ## Unfolding -/

section
variable {Δ : TypeCtx} {okD : DefType → Bool}

@[simp] theorem Sub.checkKR_heap {a b : CHeapType} :
    Sub.checkKR okD Δ .heap a b = Δ.checkHeapR okD a b := rfl

theorem TypeCtx.checkHeapR_use {u : CTypeUse} {h : CHeapType} :
    Δ.checkHeapR okD (.use u) h = Δ.checkUseR okD Δ.recs.length u h := by
  cases h <;> rfl

theorem TypeCtx.checkUseR_idx {n x : Nat} {h : CHeapType} :
    Δ.checkUseR okD n (.idx x) h = Δ.checkHeap (.use (.idx x)) h := rfl

theorem TypeCtx.checkUseR_dt {n : Nat} {d : DefType} {h : CHeapType} :
    Δ.checkUseR okD n (.dt d) h = Δ.checkHeap (.use (.dt d)) h := rfl

theorem TypeCtx.recUp_succ_some {n i : Nat} {h : CHeapType} {st : CSubType}
    (hi : Δ.recs[i]? = some st) :
    Δ.recUp okD (n + 1) i h =
      (Δ.recDirect i h || st.supers.any fun u => Δ.midOk okD u && Δ.checkUseR okD n u h) := by
  simp only [TypeCtx.recUp, hi]
  congr 2
  funext u
  cases u <;> rfl

theorem TypeCtx.recUp_succ_none {n i : Nat} {h : CHeapType} (hi : Δ.recs[i]? = none) :
    Δ.recUp okD (n + 1) i h = Δ.recDirect i h := by
  simp [TypeCtx.recUp, hi]

theorem TypeCtx.recUp_of_direct {i : Nat} {h : CHeapType} (H : Δ.recDirect i h = true) :
    ∀ n, Δ.recUp okD n i h = true
  | 0 => H
  | n + 1 => by
    cases hi : Δ.recs[i]? with
    | none => rw [TypeCtx.recUp_succ_none hi]; exact H
    | some st => rw [TypeCtx.recUp_succ_some hi]; simp [H]

theorem TypeCtx.checkUseR_of_resolve {n : Nat} {w : CTypeUse} {d : DefType} {h : CHeapType}
    (hr : Δ.resolve w = some d) : Δ.checkUseR okD n w h = Δ.checkHeap (.use w) h := by
  cases w with
  | recv i => simp [TypeCtx.resolve] at hr
  | idx x => rfl
  | dt e => rfl

theorem TypeCtx.checkUseR_use_left {n : Nat} {v : CTypeUse} {d : DefType} {h : CHeapType}
    (hv : Δ.resolve v = some d) : Δ.checkUseR okD n v h = Δ.checkUseR okD n (.dt d) h := by
  rw [TypeCtx.checkUseR_of_resolve hv, TypeCtx.checkHeap_use_left hv]
  rfl

theorem TypeCtx.recDirect_use_resolved {i : Nat} {v : CTypeUse} {d : DefType}
    (hv : Δ.resolve v = some d) : Δ.recDirect i (.use v) = false := by
  cases v <;> simp_all [TypeCtx.recDirect, TypeCtx.resolve]

theorem TypeCtx.recUp_use_right {v : CTypeUse} {d : DefType} (hv : Δ.resolve v = some d) :
    ∀ n i, Δ.recUp okD n i (.use v) = Δ.recUp okD n i (.use (.dt d))
  | 0, i => by
    show Δ.recDirect i _ = Δ.recDirect i _
    rw [TypeCtx.recDirect_use_resolved hv]; rfl
  | n + 1, i => by
    cases hi : Δ.recs[i]? with
    | none =>
      rw [TypeCtx.recUp_succ_none hi, TypeCtx.recUp_succ_none hi,
        TypeCtx.recDirect_use_resolved hv]; rfl
    | some st =>
      rw [TypeCtx.recUp_succ_some hi, TypeCtx.recUp_succ_some hi,
        TypeCtx.recDirect_use_resolved hv]
      have e : ∀ u, Δ.checkUseR okD n u (.use v) = Δ.checkUseR okD n u (.use (.dt d)) := by
        intro u
        cases u with
        | recv j => exact TypeCtx.recUp_use_right hv n j
        | idx x => exact TypeCtx.checkHeap_use_right hv (.use (.idx x))
        | dt e => exact TypeCtx.checkHeap_use_right hv (.use (.dt e))
      simp only [e]
      rfl

theorem TypeCtx.checkUseR_use_right {v : CTypeUse} {d : DefType} (hv : Δ.resolve v = some d)
    (n : Nat) (u : CTypeUse) :
    Δ.checkUseR okD n u (.use v) = Δ.checkUseR okD n u (.use (.dt d)) := by
  cases u with
  | recv j => exact TypeCtx.recUp_use_right hv n j
  | idx x => exact TypeCtx.checkHeap_use_right hv (.use (.idx x))
  | dt e => exact TypeCtx.checkHeap_use_right hv (.use (.dt e))

theorem TypeCtx.checkHeapR_use_right {v : CTypeUse} {d : DefType} (hv : Δ.resolve v = some d)
    (h : CHeapType) : Δ.checkHeapR okD h (.use v) = Δ.checkHeapR okD h (.use (.dt d)) := by
  cases h with
  | bot => rfl
  | abs a =>
    cases ht : botTop a <;> simp only [TypeCtx.checkHeapR, ht, TypeCtx.checkUseR_use_left hv]
  | use u => exact TypeCtx.checkUseR_use_right hv _ u

end

/-! ## Soundness -/

section
variable {Δ : TypeCtx} {okD : DefType → Bool}

theorem TypeCtx.midOk_sound (hok : ∀ d, okD d = true → TyOk Δ d) :
    ∀ {u : CTypeUse}, Δ.midOk okD u = true → TyOk Δ (.use u)
  | .recv j, h => by
    simp only [TypeCtx.midOk, Option.isSome_iff_exists] at h
    obtain ⟨_, h⟩ := h
    exact .use (.recv h)
  | .idx x, h => by
    simp only [TypeCtx.midOk, Option.isSome_iff_exists] at h
    obtain ⟨_, h⟩ := h
    exact .use (.idx h)
  | .dt d, h => .use (.dt (hok d h))

theorem TypeCtx.recDirect_sound {i : Nat} :
    ∀ {h : CHeapType}, Δ.recDirect i h = true → Sub Δ (.use (.recv i)) h
  | .abs b, H => by
    simp only [TypeCtx.recDirect] at H
    split at H
    · next st hst =>
      cases st with
      | sub fin sups ct =>
        have hs : Sub Δ (.use (.recv i)) (.abs (compAbs ct)) := by
          cases ct with
          | struct fs => exact .recStruct hst
          | array f => exact .recArray hst
          | func ps rs => exact .recFunc hst
        exact .heapTrans (.abs _) hs (absSub_sound H)
    · simp at H
  | .use (.recv j), H => by
    simp only [TypeCtx.recDirect, decide_eq_true_eq] at H
    subst H
    exact .heapRefl
  | .use (.idx _), H => by simp [TypeCtx.recDirect] at H
  | .use (.dt _), H => by simp [TypeCtx.recDirect] at H
  | .bot, H => by simp [TypeCtx.recDirect] at H

theorem mem_supers_getElem {st : CSubType} {u : CTypeUse} (hu : u ∈ st.supers) :
    ∃ (fin : Bool) (sups : Ty (.list .use)) (ct : CCompType) (j : Nat),
      st = .sub fin sups ct ∧ sups.toList[j]? = some u := by
  cases st with
  | sub fin sups ct =>
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem (by simpa [Ty.supers] using hu)
    exact ⟨fin, sups, ct, j, rfl, by rw [List.getElem?_eq_getElem hj, e]⟩

theorem TypeCtx.recUp_sound (hok : ∀ d, okD d = true → TyOk Δ d) :
    ∀ {n i : Nat} {h : CHeapType}, Δ.recUp okD n i h = true → Sub Δ (.use (.recv i)) h
  | 0, i, h, H => TypeCtx.recDirect_sound H
  | n + 1, i, h, H => by
    cases hi : Δ.recs[i]? with
    | none => rw [TypeCtx.recUp_succ_none hi] at H; exact TypeCtx.recDirect_sound H
    | some st =>
      rw [TypeCtx.recUp_succ_some hi] at H
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at H
      rcases H with H | ⟨u, hu, hm, hc⟩
      · exact TypeCtx.recDirect_sound H
      · obtain ⟨fin, sups, ct, j, rfl, hj⟩ := mem_supers_getElem hu
        have hc' : Sub Δ (.use u) h := by
          cases u with
          | recv j' => exact TypeCtx.recUp_sound hok hc
          | idx x => exact TypeCtx.checkHeap_sound hc
          | dt e => exact TypeCtx.checkHeap_sound hc
        exact .heapTrans (TypeCtx.midOk_sound hok hm) (.recSub hi hj) hc'

theorem TypeCtx.checkUseR_sound (hok : ∀ d, okD d = true → TyOk Δ d) {n : Nat} :
    ∀ {u : CTypeUse} {h : CHeapType}, Δ.checkUseR okD n u h = true → Sub Δ (.use u) h
  | .recv _, _, H => TypeCtx.recUp_sound hok H
  | .idx _, _, H => TypeCtx.checkHeap_sound H
  | .dt _, _, H => TypeCtx.checkHeap_sound H

theorem TypeCtx.checkHeapR_sound (hok : ∀ d, okD d = true → TyOk Δ d) :
    ∀ {h₁ h₂ : CHeapType}, Δ.checkHeapR okD h₁ h₂ = true → Sub Δ h₁ h₂
  | .bot, _, _ => .bot
  | .abs a, .abs b, h => absSub_sound h
  | .abs a, .use u, h => by
    simp only [TypeCtx.checkHeapR] at h
    split at h
    · next t ht =>
      have hs := TypeCtx.checkUseR_sound hok h
      cases a <;> simp [botTop] at ht <;> subst ht
      · exact .none hs nofun
      · exact .nofunc hs nofun
      · exact .noexn hs nofun
      · exact .noextern hs nofun
    · simp at h
  | .use u, _, h => TypeCtx.checkUseR_sound hok h
  | .abs _, .bot, h => by simp [TypeCtx.checkHeapR] at h

theorem TypeCtx.checkRefR_sound (hok : ∀ d, okD d = true → TyOk Δ d) {a b : CRefType}
    (h : Δ.checkRefR okD a b = true) : Sub Δ a b := by
  cases a with
  | ref n₁ h₁ =>
    cases b with
    | ref n₂ h₂ =>
      simp only [TypeCtx.checkRefR, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hn, hh⟩ := h
      have hs := TypeCtx.checkHeapR_sound hok hh
      cases n₂ with
      | true => exact .refNull hs
      | false =>
        rcases hn with rfl | hn
        · exact .refNonNull hs
        · cases hn

theorem TypeCtx.checkValR_sound (hok : ∀ d, okD d = true → TyOk Δ d) :
    ∀ {a b : CValType}, Δ.checkValR okD a b = true → Sub Δ a b
  | .num t₁, .num t₂, h => by simp [TypeCtx.checkValR] at h; subst h; exact .num
  | .vec .v128, .vec .v128, _ => .vec
  | .refv _, .refv _, h => .refv (TypeCtx.checkRefR_sound hok h)
  | .botv, _, _ => .botv
  | .num _, .vec _, h | .num _, .refv _, h | .num _, .botv, h
  | .vec _, .num _, h | .vec _, .refv _, h | .vec _, .botv, h
  | .refv _, .num _, h | .refv _, .vec _, h | .refv _, .botv, h => by
    simp [TypeCtx.checkValR] at h

theorem TypeCtx.checkStorageR_sound (hok : ∀ d, okD d = true → TyOk Δ d) {a b : CStorageType}
    (h : Δ.checkStorageR okD a b = true) : Sub Δ a b := by
  cases a <;> cases b <;> simp [TypeCtx.checkStorageR] at h
  · exact .val (TypeCtx.checkValR_sound hok h)
  · subst h; exact .pack

theorem TypeCtx.checkFieldR_sound (hok : ∀ d, okD d = true → TyOk Δ d) :
    ∀ {a b : CFieldType}, Δ.checkFieldR okD a b = true → Sub Δ a b
  | .field .const _, .field .const _, h => .fieldConst (TypeCtx.checkStorageR_sound hok h)
  | .field .var _, .field .var _, h => by
    simp only [TypeCtx.checkFieldR, Bool.and_eq_true] at h
    exact .fieldVar (TypeCtx.checkStorageR_sound hok h.1) (TypeCtx.checkStorageR_sound hok h.2)
  | .field .const _, .field .var _, h | .field .var _, .field .const _, h => by
    simp [TypeCtx.checkFieldR] at h

theorem TypeCtx.checkCompR_sound (hok : ∀ d, okD d = true → TyOk Δ d) {a b : CCompType}
    (h : Δ.checkCompR okD a b = true) : Sub Δ a b := by
  cases a <;> cases b <;> simp only [TypeCtx.checkCompR, Bool.false_eq_true] at h
  · next fs₁ fs₂ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hs := forall2B_sound (fun _ _ => TypeCtx.checkFieldR_sound hok) h.2
    rw [Ty.ofList_toList] at hs
    have := Sub.struct (extra := Ty.ofList (fs₁.toList.drop fs₂.toList.length)) hs
    have e : (Ty.ofList (fs₁.toList.take fs₂.toList.length)).app
        (Ty.ofList (fs₁.toList.drop fs₂.toList.length)) = fs₁ := by
      simp [Ty.app]
    rwa [e] at this
  · exact .array (TypeCtx.checkFieldR_sound hok h)
  · simp only [Bool.and_eq_true] at h
    exact .func (forall2B_sound' (fun _ _ => TypeCtx.checkValR_sound hok) h.1)
      (forall2B_sound' (fun _ _ => TypeCtx.checkValR_sound hok) h.2)

theorem Sub.checkKR_sound (hok : ∀ d, okD d = true → TyOk Δ d) :
    ∀ (k : TKind) (a b : Ty k), Sub.checkKR okD Δ k a b = true → Sub Δ a b
  | .heap, _, _, h => TypeCtx.checkHeapR_sound hok h
  | .ref, _, _, h => TypeCtx.checkRefR_sound hok h
  | .val, _, _, h => TypeCtx.checkValR_sound hok h
  | .storage, _, _, h => TypeCtx.checkStorageR_sound hok h
  | .field, _, _, h => TypeCtx.checkFieldR_sound hok h
  | .comp, _, _, h => TypeCtx.checkCompR_sound hok h
  | .def, _, _, h => Δ.checkDef_sound h
  | .list k, _, _, h => forall2B_sound' (Sub.checkKR_sound hok k) h
  | .use, _, _, h => by simp [Sub.checkKR] at h
  | .sub, _, _, h => by simp [Sub.checkKR] at h
  | .group, _, _, h => by simp [Sub.checkKR] at h

/-- **Soundness** of the `REC`-aware checker, for any sound oracle. -/
theorem Sub.checkRWith_sound (hok : ∀ d, okD d = true → TyOk Δ d) {k : TKind} {a b : Ty k}
    (h : Sub.checkRWith okD Δ a b = true) : Sub Δ a b :=
  Sub.checkKR_sound hok k a b h

end

/-! ## Completeness: well-formed `RECS` -/

/-- The `RECS` of a context form a valid group (`Rectype_ok2` pointwise). -/
def TypeCtx.RecsOk (Δ : TypeCtx) : Prop :=
  ∀ i st, Δ.recs[i]? = some st → SubOk2 Δ st i

/-- The oracle accepts every `_DEF` supertype of a `RECS` entry. -/
def TypeCtx.OracleOk (Δ : TypeCtx) (okD : DefType → Bool) : Prop :=
  ∀ (i : Nat) (st : CSubType) (d : DefType), Δ.recs[i]? = some st →
    (.dt d : CTypeUse) ∈ st.supers → okD d = true

/-- The group premise of `Deftype_ok` makes the extended context's `RECS` valid. -/
theorem TypeCtx.recsOk_withRecs {Δ : TypeCtx} {subs : Ty (.list .sub)}
    (hg : GroupOk2 (Δ.withRecs subs.toList) (.group subs) 0) :
    (Δ.withRecs subs.toList).RecsOk := by
  intro i st h
  have := GroupOk2.get subs hg h
  simpa using this

theorem TypeCtx.Ok.withRecs {Δ : TypeCtx} (hΔ : Δ.Ok) (sts : List CSubType) :
    (Δ.withRecs sts).Ok := by
  intro d hd
  obtain ⟨h1, h2⟩ := hΔ d hd
  exact ⟨h1, TyOk.def_congr (Δ₁ := Δ) (Δ₂ := Δ.withRecs sts) rfl h2⟩

/-- Paths from `REC` members along declared supertypes. -/
inductive TypeCtx.RUp (Δ : TypeCtx) : CTypeUse → CTypeUse → Prop where
  | refl (u : CTypeUse) : Δ.RUp u u
  | step {i : Nat} {st : CSubType} {u w : CTypeUse} (h : Δ.recs[i]? = some st)
      (hu : u ∈ st.supers) (hw : Δ.RUp u w) : Δ.RUp (.recv i) w

theorem TypeCtx.RUp.trans {Δ : TypeCtx} {a b c : CTypeUse} (h₁ : Δ.RUp a b)
    (h₂ : Δ.RUp b c) : Δ.RUp a c := by
  induction h₁ with
  | refl => exact h₂
  | step h hu _ ih => exact .step h hu (ih h₂)

/-- The kind of the expansion of a type use (`REC j` through `RECS`). -/
def TypeCtx.kindR (Δ : TypeCtx) : CTypeUse → Option AbsHeapType
  | .recv j => (Δ.recs[j]?).map fun st => compAbs st.body
  | .idx x => Δ.types[x]? >>= defKind
  | .dt d => defKind d

section
variable {Δ : TypeCtx} {okD : DefType → Bool}

theorem TypeCtx.RecsOk.super (hR : Δ.RecsOk) {i : Nat} {st : CSubType} {u : CTypeUse}
    (h : Δ.recs[i]? = some st) (hu : u ∈ st.supers) :
    TyOk Δ u ∧ before u i = true ∧
      ∃ sups' ct', Δ.unrollUse u = some (.sub false sups' ct') ∧
        compAbs st.body = compAbs ct' := by
  have hs := hR i st h
  cases hs with
  | noSuper hct => simp [Ty.supers] at hu
  | oneSuper hu0 hb hunroll hct hsub =>
    simp only [Ty.supers, Ty.toList_cons, Ty.toList_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hu
    subst hu
    exact ⟨hu0, hb, _, _, hunroll, hsub.compAbs_eq⟩

theorem TypeCtx.RUp.ok (hR : Δ.RecsOk) {u w : CTypeUse} (hp : Δ.RUp u w) (hu : TyOk Δ u) :
    TyOk Δ w := by
  induction hp with
  | refl => exact hu
  | step h hm _ ih => exact ih (hR.super h hm).1

theorem TypeCtx.kindR_of_unrollUse {u : CTypeUse} {fin : Bool} {sups : Ty (.list .use)}
    {ct : CCompType} (hun : Δ.unrollUse u = some (.sub fin sups ct)) :
    Δ.kindR u = some (compAbs ct) := by
  cases u with
  | dt d => exact defKind_of_unroll hun
  | idx x =>
    cases hx : Δ.types[x]? with
    | none => simp [TypeCtx.unrollUse, hx] at hun
    | some d =>
      simp only [TypeCtx.unrollUse, hx] at hun
      simp [TypeCtx.kindR, hx, defKind_of_unroll hun]
  | recv j =>
    simp only [TypeCtx.unrollUse] at hun
    simp [TypeCtx.kindR, hun, Ty.body]

theorem TypeCtx.RUp.kind (hR : Δ.RecsOk) {u w : CTypeUse} (hp : Δ.RUp u w) :
    Δ.kindR w = Δ.kindR u := by
  induction hp with
  | refl => rfl
  | @step i st u w h hm _ ih =>
    rw [ih]
    obtain ⟨-, -, sups', ct', hun, hk⟩ := hR.super h hm
    rw [TypeCtx.kindR_of_unrollUse hun]
    simp [TypeCtx.kindR, h, hk]

theorem TypeCtx.kindR_of_resolve {u : CTypeUse} {d : DefType} (hr : Δ.resolve u = some d) :
    Δ.kindR u = defKind d := by
  cases u with
  | dt e => simp only [TypeCtx.resolve, Option.some.injEq] at hr; subst hr; rfl
  | idx x => simp only [TypeCtx.resolve] at hr; simp [TypeCtx.kindR, hr]
  | recv j => simp [TypeCtx.resolve] at hr

theorem TypeCtx.kindR_compAbs {u : CTypeUse} {k : AbsHeapType} (h : Δ.kindR u = some k) :
    ∃ c, k = compAbs c := by
  cases u with
  | recv j =>
    simp only [TypeCtx.kindR, Option.map_eq_some_iff] at h
    obtain ⟨st, -, rfl⟩ := h
    exact ⟨_, rfl⟩
  | idx x =>
    simp only [TypeCtx.kindR] at h
    cases hx : Δ.types[x]? with
    | none => simp [hx] at h
    | some d => simp only [hx] at h; exact defKind_compAbs h
  | dt d => exact defKind_compAbs h

theorem TypeCtx.use_cases (hΔ : Δ.Ok) {u : CTypeUse} (h : TyOk Δ u) :
    (∃ i st, u = .recv i ∧ Δ.recs[i]? = some st) ∨ ∃ d, Δ.resolve u = some d ∧ TyOk Δ d := by
  cases h with
  | idx hx => exact .inr ⟨_, hx, (hΔ _ (List.mem_of_getElem? hx)).2⟩
  | recv hi => exact .inl ⟨_, _, rfl, hi⟩
  | dt hd => exact .inr ⟨_, rfl, hd⟩

theorem TypeCtx.fuel_ok {u : CTypeUse} (h : TyOk Δ u) :
    ∀ i, u = .recv i → i < Δ.recs.length := by
  cases h with
  | recv hi => intro i e; cases e; exact (List.getElem?_eq_some_iff.1 hi).1
  | idx _ => intro i e; cases e
  | dt _ => intro i e; cases e

theorem TypeCtx.midOk_complete (hO : Δ.OracleOk okD) {i : Nat} {st : CSubType} {u : CTypeUse}
    (hi : Δ.recs[i]? = some st) (hu : u ∈ st.supers) (oku : TyOk Δ u) :
    Δ.midOk okD u = true := by
  cases u with
  | recv j => cases oku with | recv h => simp [TypeCtx.midOk, h]
  | idx x => cases oku with | idx h => simp [TypeCtx.midOk, h]
  | dt d => exact hO i st d hi hu

/-! ## Completeness: the search -/

theorem TypeCtx.recUp_extract :
    ∀ {n i : Nat} {h : CHeapType}, Δ.recUp okD n i h = true →
      ∃ w, Δ.RUp (.recv i) w ∧ Δ.checkUseR okD 0 w h = true
  | 0, i, h, H => ⟨_, .refl _, H⟩
  | n + 1, i, h, H => by
    cases hi : Δ.recs[i]? with
    | none => rw [TypeCtx.recUp_succ_none hi] at H; exact ⟨_, .refl _, H⟩
    | some st =>
      rw [TypeCtx.recUp_succ_some hi] at H
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at H
      rcases H with H | ⟨u, hu, -, hc⟩
      · exact ⟨_, .refl _, H⟩
      · cases u with
        | recv j =>
          obtain ⟨w, hw, hb⟩ := TypeCtx.recUp_extract hc
          exact ⟨w, .step hi hu hw, hb⟩
        | idx x => exact ⟨_, .step hi hu (.refl _), hc⟩
        | dt d => exact ⟨_, .step hi hu (.refl _), hc⟩

theorem TypeCtx.checkUseR_extract {n : Nat} {u : CTypeUse} {h : CHeapType}
    (H : Δ.checkUseR okD n u h = true) :
    ∃ w, Δ.RUp u w ∧ Δ.checkUseR okD 0 w h = true := by
  cases u with
  | recv i => exact TypeCtx.recUp_extract H
  | idx x => exact ⟨_, .refl _, H⟩
  | dt d => exact ⟨_, .refl _, H⟩

theorem TypeCtx.checkUseR_of_zero {w : CTypeUse} {h : CHeapType}
    (H : Δ.checkUseR okD 0 w h = true) (n : Nat) : Δ.checkUseR okD n w h = true := by
  cases w with
  | recv j => exact TypeCtx.recUp_of_direct H n
  | idx x => exact H
  | dt d => exact H

theorem TypeCtx.checkUseR_build (hR : Δ.RecsOk) (hO : Δ.OracleOk okD) {u w : CTypeUse}
    {h : CHeapType} (hp : Δ.RUp u w) :
    Δ.checkUseR okD 0 w h = true →
      ∀ n, (∀ i, u = .recv i → i < n) → Δ.checkUseR okD n u h = true := by
  induction hp with
  | refl => intro hb n _; exact TypeCtx.checkUseR_of_zero hb n
  | @step i st u w hi hu _ ih =>
    intro hb n hn
    have hlt := hn i rfl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨oku, hbef, -⟩ := hR.super hi hu
    show Δ.recUp okD (m + 1) i h = true
    rw [TypeCtx.recUp_succ_some hi]
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    refine .inr ⟨u, hu, TypeCtx.midOk_complete hO hi hu oku, ih hb m ?_⟩
    intro j e
    subst e
    simp [before] at hbef
    omega

theorem TypeCtx.checkUseR_bot {n : Nat} {u : CTypeUse} : Δ.checkUseR okD n u .bot = false := by
  cases H : Δ.checkUseR okD n u .bot
  · rfl
  · obtain ⟨w, -, hb⟩ := TypeCtx.checkUseR_extract H
    cases w <;> simp [TypeCtx.checkUseR, TypeCtx.recUp, TypeCtx.recDirect,
      TypeCtx.checkHeap] at hb

theorem TypeCtx.checkUseR_refl (n : Nat) : ∀ u : CTypeUse, Δ.checkUseR okD n u (.use u) = true
  | .recv i => TypeCtx.recUp_of_direct (by simp [TypeCtx.recDirect]) n
  | .idx x => Δ.checkHeap_refl (.use (.idx x))
  | .dt d => Δ.checkHeap_refl (.use (.dt d))

/-- `typeuse <: absheaptype` is decided by the kind. -/
theorem TypeCtx.kind_of_checkUseR_abs (hR : Δ.RecsOk) {n : Nat} {u : CTypeUse}
    {b : AbsHeapType} (H : Δ.checkUseR okD n u (.abs b) = true) :
    ∃ k, Δ.kindR u = some k ∧ absSub k b = true := by
  obtain ⟨w, hw, hb⟩ := TypeCtx.checkUseR_extract H
  rw [← hw.kind hR]
  cases w with
  | recv j =>
    change Δ.recDirect j (.abs b) = true at hb
    simp only [TypeCtx.recDirect] at hb
    split at hb
    · next st hst => exact ⟨_, by simp [TypeCtx.kindR, hst], hb⟩
    · simp at hb
  | idx x =>
    change Δ.checkUseAbs (.idx x) b = true at hb
    unfold TypeCtx.checkUseAbs at hb
    split at hb
    · next k hk => exact ⟨k, hk, hb⟩
    · simp at hb
  | dt e =>
    change Δ.checkUseAbs (.dt e) b = true at hb
    unfold TypeCtx.checkUseAbs at hb
    split at hb
    · next k hk => exact ⟨k, hk, hb⟩
    · simp at hb

theorem TypeCtx.checkUseR_of_kind {n : Nat} {u : CTypeUse} {k b : AbsHeapType}
    (hk : Δ.kindR u = some k) (hkb : absSub k b = true) :
    Δ.checkUseR okD n u (.abs b) = true := by
  cases u with
  | recv i =>
    apply TypeCtx.recUp_of_direct
    simp only [TypeCtx.kindR] at hk
    cases hi : Δ.recs[i]? with
    | none => simp [hi] at hk
    | some st =>
      simp only [hi, Option.map_some, Option.some.injEq] at hk
      simp only [TypeCtx.recDirect, hi]
      rw [hk]
      exact hkb
  | idx x =>
    change Δ.checkUseAbs (.idx x) b = true
    have hk' : (Δ.resolve (.idx x) >>= defKind) = some k := hk
    simp only [TypeCtx.checkUseAbs, hk', hkb]
  | dt d =>
    change Δ.checkUseAbs (.dt d) b = true
    have hk' : (Δ.resolve (.dt d) >>= defKind) = some k := hk
    simp only [TypeCtx.checkUseAbs, hk', hkb]

theorem TypeCtx.kindR_of_checkUseR_use (hΔ : Δ.Ok) (hR : Δ.RecsOk) {n : Nat} {u v : CTypeUse}
    (oku : TyOk Δ u) (okv : TyOk Δ v) (H : Δ.checkUseR okD n u (.use v) = true) :
    Δ.kindR v = Δ.kindR u := by
  obtain ⟨w, hw, hb⟩ := TypeCtx.checkUseR_extract H
  rw [← hw.kind hR]
  have okw := hw.ok hR oku
  rcases TypeCtx.use_cases hΔ okw with ⟨j, st, rfl, -⟩ | ⟨dw, hdw, okdw⟩
  · change Δ.recDirect j (.use v) = true at hb
    cases v with
    | recv j' => simp only [TypeCtx.recDirect, decide_eq_true_eq] at hb; subst hb; rfl
    | idx _ => simp [TypeCtx.recDirect] at hb
    | dt _ => simp [TypeCtx.recDirect] at hb
  · rw [TypeCtx.checkUseR_of_resolve hdw, TypeCtx.checkHeap_use_left hdw] at hb
    rcases TypeCtx.use_cases hΔ okv with ⟨j, st, rfl, -⟩ | ⟨dv, hdv, okdv⟩
    · simp [TypeCtx.checkHeap, TypeCtx.resolve] at hb
    · rw [TypeCtx.checkHeap_use_right hdv] at hb
      simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt] at hb
      rw [TypeCtx.kindR_of_resolve hdv, TypeCtx.kindR_of_resolve hdw,
        TypeCtx.checkDef_kind hΔ okdw hb]

theorem TypeCtx.checkHeap_trans_def (hΔ : Δ.Ok) {dw dv : DefType} (okdw : TyOk Δ dw)
    (hd : Δ.checkDef dw dv = true) {h₂ : CHeapType}
    (hc : Δ.checkHeap (.use (.dt dv)) h₂ = true) : Δ.checkHeap (.use (.dt dw)) h₂ = true := by
  cases h₂ with
  | bot => simp [TypeCtx.checkHeap] at hc
  | abs b =>
    simp only [TypeCtx.checkHeap] at hc ⊢
    obtain ⟨k, hk, hkb⟩ := (TypeCtx.checkUseAbs_iff (u := .dt dv) rfl).1 hc
    refine (TypeCtx.checkUseAbs_iff rfl).2 ⟨k, ?_, hkb⟩
    rw [← TypeCtx.checkDef_kind hΔ okdw hd]
    exact hk
  | use x =>
    cases hx : Δ.resolve x with
    | none => simp [TypeCtx.checkHeap, hx] at hc
    | some dx =>
      rw [TypeCtx.checkHeap_use_right hx] at hc ⊢
      simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt] at hc ⊢
      exact TypeCtx.checkDef_trans hΔ okdw hd hc

theorem TypeCtx.checkUseR_trans (hΔ : Δ.Ok) (hR : Δ.RecsOk) (hO : Δ.OracleOk okD)
    {u v : CTypeUse} {h₂ : CHeapType} (oku : TyOk Δ u) (okv : TyOk Δ v)
    (c₁ : Δ.checkUseR okD Δ.recs.length u (.use v) = true)
    (c₂ : Δ.checkUseR okD Δ.recs.length v h₂ = true) :
    Δ.checkUseR okD Δ.recs.length u h₂ = true := by
  obtain ⟨w, hw, hb⟩ := TypeCtx.checkUseR_extract c₁
  have okw := hw.ok hR oku
  rcases TypeCtx.use_cases hΔ okw with ⟨j, st, rfl, -⟩ | ⟨dw, hdw, okdw⟩
  · change Δ.recDirect j (.use v) = true at hb
    have hv : v = .recv j := by
      cases v with
      | recv j' => simp only [TypeCtx.recDirect, decide_eq_true_eq] at hb; subst hb; rfl
      | idx _ => simp [TypeCtx.recDirect] at hb
      | dt _ => simp [TypeCtx.recDirect] at hb
    subst hv
    obtain ⟨w', hw', hb'⟩ := TypeCtx.checkUseR_extract c₂
    exact TypeCtx.checkUseR_build hR hO (hw.trans hw') hb' _ (TypeCtx.fuel_ok oku)
  · rw [TypeCtx.checkUseR_of_resolve hdw, TypeCtx.checkHeap_use_left hdw] at hb
    rcases TypeCtx.use_cases hΔ okv with ⟨j, st, rfl, -⟩ | ⟨dv, hdv, okdv⟩
    · simp [TypeCtx.checkHeap, TypeCtx.resolve] at hb
    · rw [TypeCtx.checkHeap_use_right hdv] at hb
      simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt] at hb
      rw [TypeCtx.checkUseR_of_resolve hdv, TypeCtx.checkHeap_use_left hdv] at c₂
      have hc := TypeCtx.checkHeap_trans_def hΔ okdw hb c₂
      refine TypeCtx.checkUseR_build hR hO hw ?_ _ (TypeCtx.fuel_ok oku)
      rw [TypeCtx.checkUseR_of_resolve hdw, TypeCtx.checkHeap_use_left hdw]
      exact hc

/-! ## Completeness: heap types -/

theorem TypeCtx.checkHeapR_refl : ∀ h : CHeapType, Δ.checkHeapR okD h h = true
  | .bot => rfl
  | .abs a => absSub_refl a
  | .use u => TypeCtx.checkUseR_refl _ u

theorem TypeCtx.checkHeapR_bottom {a t : AbsHeapType} (ht : botTop a = some t)
    {h : CHeapType} (hb : h ≠ .bot) (hs : Δ.checkHeapR okD h (.abs t) = true) :
    Δ.checkHeapR okD (.abs a) h = true := by
  cases h with
  | bot => exact absurd rfl hb
  | abs x => exact absSub_of_botTop ht hs
  | use u => simp only [TypeCtx.checkHeapR, ht]; exact hs

theorem TypeCtx.checkHeapR_trans (hΔ : Δ.Ok) (hR : Δ.RecsOk) (hO : Δ.OracleOk okD)
    {h₁ h' h₂ : CHeapType} (ok₁ : TyOk Δ h₁) (ok' : TyOk Δ h') (ok₂ : TyOk Δ h₂)
    (c₁ : Δ.checkHeapR okD h₁ h' = true) (c₂ : Δ.checkHeapR okD h' h₂ = true) :
    Δ.checkHeapR okD h₁ h₂ = true := by
  cases h₁ with
  | bot => rfl
  | abs a =>
    cases h' with
    | bot => simp [TypeCtx.checkHeapR] at c₁
    | abs a' =>
      cases h₂ with
      | bot => simp [TypeCtx.checkHeapR] at c₂
      | abs b => exact absSub_trans c₁ c₂
      | use w =>
        simp only [TypeCtx.checkHeapR] at c₁ c₂ ⊢
        cases ht : botTop a' with
        | none => simp [ht] at c₂
        | some t => rw [absSub_eq_of_botTop c₁ ht]; simpa [ht] using c₂
    | use v =>
      simp only [TypeCtx.checkHeapR] at c₁
      cases ht : botTop a with
      | none => simp [ht] at c₁
      | some t =>
        simp only [ht] at c₁
        obtain ⟨k, hk, hkt⟩ := TypeCtx.kind_of_checkUseR_abs hR c₁
        cases h₂ with
        | bot => simp [TypeCtx.checkHeapR, TypeCtx.checkUseR_bot] at c₂
        | abs b =>
          obtain ⟨k', hk', hkb⟩ := TypeCtx.kind_of_checkUseR_abs hR c₂
          rw [hk] at hk'
          cases hk'
          exact absSub_botTop_trans ht hkt hkb
        | use x =>
          have e := TypeCtx.kindR_of_checkUseR_use hΔ hR ok'.use_inv ok₂.use_inv c₂
          simp only [TypeCtx.checkHeapR, ht]
          exact TypeCtx.checkUseR_of_kind (e.trans hk) hkt
  | use u =>
    cases h' with
    | bot => simp [TypeCtx.checkHeapR, TypeCtx.checkUseR_bot] at c₁
    | abs a' =>
      obtain ⟨k, hk, hka⟩ := TypeCtx.kind_of_checkUseR_abs hR c₁
      cases h₂ with
      | bot => simp [TypeCtx.checkHeapR] at c₂
      | abs b => exact TypeCtx.checkUseR_of_kind hk (absSub_trans hka c₂)
      | use w =>
        simp only [TypeCtx.checkHeapR] at c₂
        cases ht : botTop a' with
        | none => simp [ht] at c₂
        | some t =>
          obtain ⟨c, rfl⟩ := TypeCtx.kindR_compAbs hk
          exact (compAbs_not_bot c hka ht).elim
    | use v => exact TypeCtx.checkUseR_trans hΔ hR hO ok₁.use_inv ok'.use_inv c₁ c₂

end

/-! ## Completeness -/

/-- The declared supertypes of a valid defined type resolve to valid defined types
(they are never `REC j`: unrolling replaces those). -/
theorem TyOk.unroll_super_resolve {Δ : TypeCtx} (hΔ : Δ.Ok) {b : DefType} (hb : TyOk Δ b)
    {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (hu : unrolldt b = some (.sub fin sups ct)) {u : CTypeUse} (hmem : u ∈ sups.toList) :
    ∃ d, Δ.resolve u = some d ∧ TyOk Δ d := by
  cases hb with
  | @defn _ subs i hg hi =>
    simp only [unrolldt, unrollrt, Ty.subs] at hu
    rw [Ty.toList_subst, List.getElem?_map] at hu
    cases hst : subs.toList[i]? with
    | none => simp [hst] at hu
    | some st =>
      rw [hst] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      have hso := GroupOk2.get subs hg hst
      cases st with
      | sub fin0 sups0 ct0 =>
        simp only [Ty.subst, Ty.sub.injEq] at hu
        obtain ⟨-, hsups, -⟩ := hu
        subst hsups
        rw [Ty.toList_subst, List.mem_map] at hmem
        obtain ⟨u0, hu0, rfl⟩ := hmem
        have hok := hso.super_ok u0 hu0
        cases u0 with
        | idx x =>
          cases hok with
          | idx h =>
            simp only [Ty.subst, Option.getD_none]
            exact ⟨_, h, (hΔ _ (List.mem_of_getElem? h)).2⟩
        | recv j =>
          cases hok with
          | recv h =>
            have hj : j < subs.length := by
              have := (List.getElem?_eq_some_iff.1 h).1
              simpa [TypeCtx.withRecs, Ty.length] using this
            simp only [Ty.subst, hj, ite_true, Option.getD_some]
            exact ⟨_, rfl, .defn hg hj⟩
        | dt e =>
          rw [Ty.recFree_dt e _ (fun _ => rfl)]
          cases hok with
          | dt h =>
            exact ⟨e, rfl, TyOk.def_congr (Δ₁ := Δ.withRecs subs.toList) (Δ₂ := Δ) rfl h⟩

/-- **Completeness** of the `REC`-aware checker on valid types in a well-formed
context whose `RECS` form a valid group, given an oracle accepting the `_DEF`
supertypes of `RECS` entries. -/
theorem Sub.completeR {Δ : TypeCtx} {okD : DefType → Bool} (hΔ : Δ.Ok) (hR : Δ.RecsOk)
    (hO : Δ.OracleOk okD) :
    ∀ {k : TKind} {a b : Ty k}, Sub Δ a b → TyOk Δ a → TyOk Δ b →
      Sub.checkKR okD Δ k a b = true
  | _, _, _, .heapRefl, _, _ => TypeCtx.checkHeapR_refl _
  | _, _, _, .heapTrans hok h₁ h₂, ha, hb =>
    TypeCtx.checkHeapR_trans hΔ hR hO ha hok hb (Sub.completeR hΔ hR hO h₁ ha hok)
      (Sub.completeR hΔ hR hO h₂ hok hb)
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
    rw [Sub.checkKR_heap, TypeCtx.checkHeapR_use, TypeCtx.checkUseR_dt]
    simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt]
    exact Sub.completeR hΔ hR hO h ha.use_inv.dt_inv hb.use_inv.dt_inv
  | _, _, _, .idxL (x := x) (d := d) hx hs, _, hb => by
    rw [Sub.checkKR_heap, TypeCtx.checkHeapR_use,
      TypeCtx.checkUseR_use_left (show Δ.resolve (.idx x) = some d from hx),
      ← TypeCtx.checkHeapR_use, ← Sub.checkKR_heap]
    exact Sub.completeR hΔ hR hO hs (.use (.dt (hΔ _ (List.mem_of_getElem? hx)).2)) hb
  | _, _, _, .idxR (x := x) (d := d) hx hs, ha, _ => by
    rw [Sub.checkKR_heap,
      TypeCtx.checkHeapR_use_right (show Δ.resolve (.idx x) = some d from hx),
      ← Sub.checkKR_heap]
    exact Sub.completeR hΔ hR hO hs ha (.use (.dt (hΔ _ (List.mem_of_getElem? hx)).2))
  | _, _, _, .recStruct h, _, _ =>
    TypeCtx.recUp_of_direct (by simp [TypeCtx.recDirect, h, Ty.body, compAbs, absSub]) _
  | _, _, _, .recArray h, _, _ =>
    TypeCtx.recUp_of_direct (by simp [TypeCtx.recDirect, h, Ty.body, compAbs, absSub]) _
  | _, _, _, .recFunc h, _, _ =>
    TypeCtx.recUp_of_direct (by simp [TypeCtx.recDirect, h, Ty.body, compAbs, absSub]) _
  | _, _, _, .recSub (u := u) h hj, ha, _ =>
    TypeCtx.checkUseR_build hR hO (.step h (by simpa [Ty.supers] using List.mem_of_getElem? hj)
      (.refl u)) (TypeCtx.checkUseR_refl 0 u) _ (TypeCtx.fuel_ok ha.use_inv)
  | _, _, _, .none hs hne, _, hb =>
    TypeCtx.checkHeapR_bottom (a := .none) rfl hne (Sub.completeR hΔ hR hO hs hb (.abs _))
  | _, _, _, .nofunc hs hne, _, hb =>
    TypeCtx.checkHeapR_bottom (a := .nofunc) rfl hne (Sub.completeR hΔ hR hO hs hb (.abs _))
  | _, _, _, .noexn hs hne, _, hb =>
    TypeCtx.checkHeapR_bottom (a := .noexn) rfl hne (Sub.completeR hΔ hR hO hs hb (.abs _))
  | _, _, _, .noextern hs hne, _, hb =>
    TypeCtx.checkHeapR_bottom (a := .noextern) rfl hne (Sub.completeR hΔ hR hO hs hb (.abs _))
  | _, _, _, .bot, _, _ => rfl
  | _, _, _, .refNonNull h, ha, hb => by
    show Δ.checkRefR okD _ _ = true
    simp only [TypeCtx.checkRefR, Bool.not_false, Bool.true_or, Bool.true_and]
    exact Sub.completeR hΔ hR hO h ha.ref_inv hb.ref_inv
  | _, _, _, .refNull h, ha, hb => by
    show Δ.checkRefR okD _ _ = true
    simp only [TypeCtx.checkRefR, Bool.or_true, Bool.true_and]
    exact Sub.completeR hΔ hR hO h ha.ref_inv hb.ref_inv
  | _, _, _, .num, _, _ => by simp [Sub.checkKR, TypeCtx.checkValR]
  | _, _, _, .vec, _, _ => by simp [Sub.checkKR, TypeCtx.checkValR]
  | _, _, _, .refv h, ha, hb => by
    have := Sub.completeR hΔ hR hO h ha.refv_inv hb.refv_inv
    exact this
  | _, _, _, .botv, _, _ => by
    show Δ.checkValR okD _ _ = true
    rename_i t
    cases t <;> rfl
  | _, _, _, .val h, ha, hb => by
    have := Sub.completeR hΔ hR hO h ha.val_inv hb.val_inv
    exact this
  | _, _, _, .pack, _, _ => by simp [Sub.checkKR, TypeCtx.checkStorageR]
  | _, _, _, .fieldConst h, ha, hb => by
    have := Sub.completeR hΔ hR hO h ha.field_inv hb.field_inv
    exact this
  | _, _, _, .fieldVar h₁ h₂, ha, hb => by
    show Δ.checkFieldR okD _ _ = true
    simp only [TypeCtx.checkFieldR, Bool.and_eq_true]
    exact ⟨Sub.completeR hΔ hR hO h₁ ha.field_inv hb.field_inv,
      Sub.completeR hΔ hR hO h₂ hb.field_inv ha.field_inv⟩
  | _, _, _, @Sub.struct _ fs₁ extra fs₂ h, ha, hb => by
    have hc := Sub.completeR hΔ hR hO h (TyOk.app_left ha.struct_inv) hb.struct_inv
    change forall2B (Sub.checkKR okD Δ .field) fs₁.toList fs₂.toList = true at hc
    have hlen := forall2B_length hc
    show Δ.checkCompR okD _ _ = true
    simp only [TypeCtx.checkCompR, Ty.app, Ty.toList_ofList, List.length_append,
      Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [List.take_left' hlen]
    exact hc
  | _, _, _, .array h, ha, hb => by
    have := Sub.completeR hΔ hR hO h ha.array_inv hb.array_inv
    exact this
  | _, _, _, .func hp hr', ha, hb => by
    show Δ.checkCompR okD _ _ = true
    simp only [TypeCtx.checkCompR, Bool.and_eq_true]
    exact ⟨Sub.completeR hΔ hR hO hp hb.func_inv.1 ha.func_inv.1,
      Sub.completeR hΔ hR hO hr' ha.func_inv.2 hb.func_inv.2⟩
  | _, _, _, .defRefl h, _, _ => by
    show Δ.checkDef _ _ = true
    exact TypeCtx.reach_of (by simp [h]) _
  | _, _, _, .defSuper hu hj hs, ha, hb => by
    show Δ.checkDef _ _ = true
    have hok := ha.unroll_super hu (List.mem_of_getElem? hj)
    have hc := Sub.completeR hΔ hR hO hs hok (.use (.dt hb))
    obtain ⟨d', hd', -⟩ := TyOk.unroll_super_resolve hΔ ha hu (List.mem_of_getElem? hj)
    change Δ.checkUseR okD _ _ (.use (.dt _)) = true at hc
    rw [TypeCtx.checkUseR_of_resolve hd', TypeCtx.checkHeap_use_left hd'] at hc
    simp only [TypeCtx.checkHeap, TypeCtx.resolve_dt] at hc
    obtain ⟨e, he, hce⟩ := TypeCtx.checkDef_exists hc
    refine TypeCtx.checkDef_of_reach hΔ ha (.step ?_ hd' he) hce
    rw [supersOf_of_unroll hu]
    simpa [Ty.supers] using List.mem_of_getElem? hj
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons h hl, ha, hb => by
    show forall2B _ (_ :: _) (_ :: _) = true
    simp only [forall2B, Bool.and_eq_true]
    exact ⟨Sub.completeR hΔ hR hO h ha.cons_inv.1 hb.cons_inv.1,
      Sub.completeR hΔ hR hO hl ha.cons_inv.2 hb.cons_inv.2⟩

/-- **Completeness** of `Sub.checkRWith`. -/
theorem Sub.checkRWith_complete {Δ : TypeCtx} {okD : DefType → Bool} (hΔ : Δ.Ok)
    (hR : Δ.RecsOk) (hO : Δ.OracleOk okD) {k : TKind} {a b : Ty k} (h : Sub Δ a b)
    (ha : TyOk Δ a) (hb : TyOk Δ b) : Sub.checkRWith okD Δ a b = true :=
  Sub.completeR hΔ hR hO h ha hb

/-- `Sub.checkRWith` decides subtyping between valid types under valid `RECS`. -/
theorem Sub.checkRWith_iff {Δ : TypeCtx} {okD : DefType → Bool}
    (hok : ∀ d, okD d = true → TyOk Δ d) (hΔ : Δ.Ok) (hR : Δ.RecsOk) (hO : Δ.OracleOk okD)
    {k : TKind} {a b : Ty k} (ha : TyOk Δ a) (hb : TyOk Δ b) :
    Sub.checkRWith okD Δ a b = true ↔ Sub Δ a b :=
  ⟨Sub.checkRWith_sound hok, fun h => Sub.checkRWith_complete hΔ hR hO h ha hb⟩

/-- With no `RECS`, the side conditions hold trivially. -/
theorem TypeCtx.recsOk_of_nil {Δ : TypeCtx} (hr : Δ.recs = []) : Δ.RecsOk := by
  intro i st h; simp [hr] at h

theorem TypeCtx.oracleOk_of_nil {Δ : TypeCtx} {okD : DefType → Bool} (hr : Δ.recs = []) :
    Δ.OracleOk okD := by
  intro i st d h; simp [hr] at h

end Silmaril.Wasm.Validation
