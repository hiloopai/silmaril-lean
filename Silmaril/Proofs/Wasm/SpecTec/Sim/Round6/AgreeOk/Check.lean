module

public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.Defs
public import Silmaril.Wasm.Validation.Subtyping.CheckRecs
public import Silmaril.Wasm.Validation.Subtyping.DefInv

/-!
# Round 6: Silmaril's subtyping checker builds canonical derivations

Silmaril's `REC`-aware checker `Sub.checkRWith` (`Subtyping/CheckRecs.lean`) is complete for
Core's `Sub` between valid types under a valid group of `RECS`. Its soundness proof builds a Core
derivation whose `Heaptype_sub/trans` middles are abstract heap types or declared supertypes of
`RECS` members. This file redoes that proof towards **canonical** derivations (`SubB`), in a
context without `TYPES`, with any `RECS` appended (`ext Δ M`):

* `subB_absSub`, `subB_kind`, `subB_reach`, `subB_checkHeap`: the `RECS`-free part (Silmaril's
  `TypeCtx.checkHeap`), whose only middles are abstract heap types;
* `subB_recKind`: Core's `rec-*` kind rules at members with supertypes, through `rec-sub` and
  `trans` (SpecTec's `rec-*` rules need a parent-free member);
* `subB_checkHeapR` … `subB_checkCompR`: every sort the composite types use, from
  `checkRWith (fun _ => true)`; middles are abstract or declared supertypes of `RECS` members,
  which `RecsGoodB` makes bounded and canonically valid.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Validation.DefInv (clos_nil)

/-! ## Appending to `RECS` -/

theorem recs_ext {Δ : TypeCtx} {M : List CSubType} {i : Nat} {st : CSubType}
    (h : Δ.recs[i]? = some st) : (ext Δ M).recs[i]? = some st := by
  simp only [ext]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

theorem unrollUse_ext {Δ : TypeCtx} {M : List CSubType} {u : CTypeUse} {st : CSubType}
    (h : Δ.unrollUse u = some st) : (ext Δ M).unrollUse u = some st := by
  cases u with
  | idx x => exact h
  | recv i => exact recs_ext h
  | dt d => exact h

/-! ## Without `RECS` -/

/-- An abstract heap type is bounded. -/
theorem tyBnd_abs (a : AbsHeapType) : Round4.tyBnd (Ty.abs a : CHeapType) = true := rfl

/-- `Heaptype_sub/trans` through an abstract middle type. -/
theorem SubB.transAbs {Δ : TypeCtx} {h₁ h₂ : CHeapType} (m : AbsHeapType)
    (h₁' : SubB Δ h₁ (.abs m)) (h'₂ : SubB Δ (.abs m) h₂) : SubB Δ h₁ h₂ :=
  .heapTrans (tyBnd_abs m) (.abs m) h₁' h'₂

/-- **The abstract order**, through the abstract middle `EQ` only. -/
theorem subB_absSub {Δ : TypeCtx} {a b : AbsHeapType} (h : absSub a b = true) :
    SubB Δ (.abs a) (.abs b) := by
  have i31Any : SubB Δ (.abs .i31) (.abs .any) := .transAbs .eq .i31Eq .eqAny
  have structAny : SubB Δ (.abs .struct) (.abs .any) := .transAbs .eq .structEq .eqAny
  have arrayAny : SubB Δ (.abs .array) (.abs .any) := .transAbs .eq .arrayEq .eqAny
  cases a <;> cases b <;> simp [absSub] at h
  all_goals first
    | exact .heapRefl
    | exact .eqAny | exact .i31Eq | exact .structEq | exact .arrayEq
    | exact i31Any | exact structAny | exact arrayAny
    | exact .none .heapRefl nofun | exact .none .eqAny nofun | exact .none i31Any nofun
    | exact .none structAny nofun | exact .none arrayAny nofun
    | exact .nofunc .heapRefl nofun | exact .noexn .heapRefl nofun
    | exact .noextern .heapRefl nofun

/-- `deftype <: STRUCT/ARRAY/FUNC`, by the kind of its expansion. -/
theorem subB_kind {Δ : TypeCtx} {d : DefType} {fin : Bool} {sups : Ty (.list .use)}
    {ct : CCompType} (h : unrolldt d = some (.sub fin sups ct)) :
    SubB Δ (.use (.dt d)) (.abs (compAbs ct)) := by
  cases ct with
  | struct fs => exact .defStruct (.mk h)
  | array f => exact .defArray (.mk h)
  | func ps rs => exact .defFunc (.mk h)

/-- Without `TYPES`, a type use resolves only when it is a defined type. -/
theorem resolve_eq {Δ : TypeCtx} (ht : Δ.types = []) {u : CTypeUse} {d : DefType}
    (h : Δ.resolve u = some d) : u = .dt d := by
  cases u with
  | dt e => cases h; rfl
  | idx x => simp [TypeCtx.resolve, ht] at h
  | recv i => cases h

/-- `defKind` gives `deftype <: kind`. -/
theorem subB_defKind {Δ : TypeCtx} {d : DefType} {k : AbsHeapType} (hk : defKind d = some k) :
    SubB Δ (.use (.dt d)) (.abs k) := by
  obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 hk
  cases st with
  | sub fin sups ct => exact subB_kind hst

/-- `Heaptype_sub` from `deftype` to an abstract heap type above its kind. -/
theorem subB_checkUseAbs {Δ Δ' : TypeCtx} (ht : Δ.types = []) {u : CTypeUse}
    {b : AbsHeapType} (h : Δ.checkUseAbs u b = true) : SubB Δ' (.use u) (.abs b) := by
  unfold TypeCtx.checkUseAbs at h
  split at h
  · next k hk =>
    obtain ⟨d, hd, hk'⟩ := Option.bind_eq_some_iff.1 hk
    rw [resolve_eq ht hd]
    exact .transAbs k (subB_defKind hk') (subB_absSub h)
  · simp at h

/-- **A chain of declared supertypes** ending at `d₂` gives `deftype <: deftype` at the heap
sort, through `Deftype_sub/super` and `Heaptype_sub/def` (no middle types). -/
theorem subB_reach {Δ Δ' : TypeCtx} (ht : Δ.types = []) {d e d₂ : DefType}
    (h : Δ.Reach d e) (he : e = d₂) : SubB Δ' (.use (.dt d)) (.use (.dt d₂)) := by
  induction h with
  | refl => subst he; exact .heapRefl
  | step hu hr _ ih =>
    obtain ⟨fin, sups, ct, j, hun, hj⟩ := supersOf_mem hu
    rw [resolve_eq ht hr] at hj
    exact .defDef (.defSuper hun hj (ih he))

/-- `TypeCtx.checkDef` without `TYPES`. -/
theorem subB_checkDef {Δ Δ' : TypeCtx} (ht : Δ.types = []) {d₁ d₂ : DefType}
    (h : Δ.checkDef d₁ d₂ = true) : SubB Δ' (.use (.dt d₁)) (.use (.dt d₂)) := by
  obtain ⟨e, he, hP⟩ := TypeCtx.reach_sound h
  have hc : e.clos Δ.types = d₂.clos Δ.types := by simpa using hP
  rw [ht, clos_nil, clos_nil] at hc
  exact subB_reach ht he hc

/-- The bottom rules `none`, `nofunc`, `noexn`, `noextern`. -/
theorem subB_bottom {Δ : TypeCtx} {a t : AbsHeapType} {h : CHeapType} (ht : botTop a = some t)
    (hs : SubB Δ h (.abs t)) (hb : h ≠ .bot) : SubB Δ (.abs a) h := by
  cases a <;> simp [botTop] at ht <;> subst ht
  · exact .none hs hb
  · exact .nofunc hs hb
  · exact .noexn hs hb
  · exact .noextern hs hb

/-- **Silmaril's `RECS`-free checker builds canonical derivations**, in any context, when the
checked context has no `TYPES`. -/
theorem subB_checkHeap {Δ Δ' : TypeCtx} (ht : Δ.types = []) :
    ∀ {h₁ h₂ : CHeapType}, Δ.checkHeap h₁ h₂ = true → SubB Δ' h₁ h₂
  | .bot, _, _ => .bot
  | .abs _, .abs _, h => subB_absSub h
  | .abs a, .use u, h => by
    simp only [TypeCtx.checkHeap] at h
    split at h
    · next t hb => exact subB_bottom hb (subB_checkUseAbs ht h) nofun
    · simp at h
  | .use _, .abs _, h => subB_checkUseAbs ht h
  | .use u₁, .use u₂, h => by
    simp only [TypeCtx.checkHeap] at h
    split at h
    · next d₁ d₂ hr₁ hr₂ =>
      rw [resolve_eq ht hr₁, resolve_eq ht hr₂]
      exact subB_checkDef ht h
    · simp at h; subst h; exact .heapRefl
    · simp at h
  | .abs _, .bot, h => by simp [TypeCtx.checkHeap] at h
  | .use _, .bot, h => by simp [TypeCtx.checkHeap] at h

/-! ## With `RECS` -/

section
variable {Δ : TypeCtx}

/-- A type use with a canonical validity derivation is not a type index. -/
theorem TyOkB.not_idx {Δ' : TypeCtx} {x : Nat} : ¬ TyOkB Δ' (Ty.idx x : CTypeUse) := nofun

/-- A type use that unrolls to a subtype is below that subtype's kind, given the `REC` case. -/
theorem subB_useKind {M : List CSubType} {u : CTypeUse} {sups : Ty (.list .use)}
    {ct : CCompType} (hu : TyOkB (ext Δ M) u) (h : Δ.unrollUse u = some (.sub false sups ct))
    (hrec : ∀ k, u = .recv k → SubB (ext Δ M) (.use (.recv k)) (.abs (compAbs ct))) :
    SubB (ext Δ M) (.use u) (.abs (compAbs ct)) := by
  cases u with
  | recv k => exact hrec k rfl
  | dt d => exact subB_kind h
  | idx x => exact absurd hu TyOkB.not_idx

/-- `REC i <: STRUCT/ARRAY/FUNC` at a parent-free member. -/
theorem subB_recKindNil {Δ' : TypeCtx} {i : Nat} {fin : Bool} {ct : CCompType}
    (h : Δ'.recs[i]? = some (.sub fin .nil ct)) :
    SubB Δ' (.use (.recv i)) (.abs (compAbs ct)) := by
  cases ct with
  | struct fs => exact .recStruct h
  | array f => exact .recArray h
  | func ps rs => exact .recFunc h

/-- **Core's `rec-*` kind rules are canonical** over a valid group: `REC i` is below the kind of
`RECS[i]`, whatever its supertypes, through `rec-sub` and `trans` at the declared supertype. -/
theorem subB_recKind (hR : RecsGoodB Δ) (M : List CSubType) :
    ∀ (i : Nat) (st : CSubType), Δ.recs[i]? = some st →
      SubB (ext Δ M) (.use (.recv i)) (.abs (compAbs st.body)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro st hst
    cases st with
    | sub fin sups ct =>
    cases sups with
    | nil => exact subB_recKindNil (recs_ext hst)
    | cons u rest =>
      obtain ⟨hb, hbnd, hok, sups', ct', hun, hk⟩ := hR i _ hst u (by simp [Ty.supers])
      have hu : SubB (ext Δ M) (.use u) (.abs (compAbs ct')) :=
        subB_useKind (hok M) hun fun k hk' => by
          subst hk'
          exact ih k (by simpa [before] using hb) _ hun
      have hk' : compAbs ct' = compAbs ct := hk
      show SubB _ _ (.abs (compAbs ct))
      rw [← hk']
      exact .heapTrans hbnd (.use (hok M)) (.recSub (j := 0) (recs_ext hst) rfl) hu

/-- `TypeCtx.recDirect`. -/
theorem subB_recDirect (hR : RecsGoodB Δ) (M : List CSubType) {i : Nat} :
    ∀ {h : CHeapType}, Δ.recDirect i h = true → SubB (ext Δ M) (.use (.recv i)) h
  | .abs b, H => by
    simp only [TypeCtx.recDirect] at H
    split at H
    · next st hst => exact .transAbs _ (subB_recKind hR M i st hst) (subB_absSub H)
    · simp at H
  | .use (.recv j), H => by
    simp only [TypeCtx.recDirect, decide_eq_true_eq] at H
    subst H
    exact .heapRefl
  | .use (.idx _), H => by simp [TypeCtx.recDirect] at H
  | .use (.dt _), H => by simp [TypeCtx.recDirect] at H
  | .bot, H => by simp [TypeCtx.recDirect] at H

/-- One step of the search along declared supertypes: `REC i <: u <: h` through `rec-sub` and
`trans` at the declared supertype `u`. -/
theorem subB_recUpStep (hR : RecsGoodB Δ) (M : List CSubType) {i : Nat} {st : CSubType}
    {u : CTypeUse} {h : CHeapType} (hi : Δ.recs[i]? = some st) (hu : u ∈ st.supers)
    (hc : SubB (ext Δ M) (.use u) h) : SubB (ext Δ M) (.use (.recv i)) h := by
  obtain ⟨-, hbnd, hok, -⟩ := hR i st hi u hu
  obtain ⟨fin, sups, ct, j, rfl, hj⟩ := mem_supers_getElem hu
  exact .heapTrans hbnd (.use (hok M)) (.recSub (recs_ext hi) hj) hc

/-- `TypeCtx.recUp`. -/
theorem subB_recUp (ht : Δ.types = []) (hR : RecsGoodB Δ) (M : List CSubType) :
    ∀ {n i : Nat} {h : CHeapType}, Δ.recUp (fun _ => true) n i h = true →
      SubB (ext Δ M) (.use (.recv i)) h
  | 0, _, _, H => subB_recDirect hR M H
  | n + 1, i, h, H => by
    cases hi : Δ.recs[i]? with
    | none => rw [TypeCtx.recUp_succ_none hi] at H; exact subB_recDirect hR M H
    | some st =>
      rw [TypeCtx.recUp_succ_some hi] at H
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at H
      rcases H with H | ⟨u, hu, -, hc⟩
      · exact subB_recDirect hR M H
      · refine subB_recUpStep hR M hi hu ?_
        cases u with
        | recv j' => exact subB_recUp ht hR M hc
        | idx x => exact subB_checkHeap ht hc
        | dt e => exact subB_checkHeap ht hc

/-- `TypeCtx.checkUseR`. -/
theorem subB_checkUseR (ht : Δ.types = []) (hR : RecsGoodB Δ) (M : List CSubType) {n : Nat} :
    ∀ {u : CTypeUse} {h : CHeapType}, Δ.checkUseR (fun _ => true) n u h = true →
      SubB (ext Δ M) (.use u) h
  | .recv _, _, H => subB_recUp ht hR M H
  | .idx _, _, H => subB_checkHeap ht H
  | .dt _, _, H => subB_checkHeap ht H

/-- **`TypeCtx.checkHeapR` builds canonical derivations.** -/
theorem subB_checkHeapR (ht : Δ.types = []) (hR : RecsGoodB Δ) (M : List CSubType) :
    ∀ {h₁ h₂ : CHeapType}, Δ.checkHeapR (fun _ => true) h₁ h₂ = true → SubB (ext Δ M) h₁ h₂
  | .bot, _, _ => .bot
  | .abs _, .abs _, h => subB_absSub h
  | .abs a, .use u, h => by
    simp only [TypeCtx.checkHeapR] at h
    split at h
    · next t hb => exact subB_bottom hb (subB_checkUseR ht hR M h) nofun
    · simp at h
  | .use _, _, h => subB_checkUseR ht hR M h
  | .abs _, .bot, h => by simp [TypeCtx.checkHeapR] at h

/-- `TypeCtx.checkRefR`. -/
theorem subB_checkRefR (ht : Δ.types = []) (hR : RecsGoodB Δ) (M : List CSubType)
    {a b : CRefType} (h : Δ.checkRefR (fun _ => true) a b = true) : SubB (ext Δ M) a b := by
  cases a with | ref n₁ h₁ =>
  cases b with | ref n₂ h₂ =>
  simp only [TypeCtx.checkRefR, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hn, hh⟩ := h
  have hs := subB_checkHeapR ht hR M hh
  cases n₂ with
  | true => exact .refNull hs
  | false =>
    rcases hn with rfl | hn
    · exact .refNonNull hs
    · cases hn

/-- `TypeCtx.checkValR`. -/
theorem subB_checkValR (ht : Δ.types = []) (hR : RecsGoodB Δ) (M : List CSubType) :
    ∀ {a b : CValType}, Δ.checkValR (fun _ => true) a b = true → SubB (ext Δ M) a b
  | .num t₁, .num t₂, h => by simp [TypeCtx.checkValR] at h; subst h; exact .num
  | .vec .v128, .vec .v128, _ => .vec
  | .refv _, .refv _, h => .refv (subB_checkRefR ht hR M h)
  | .botv, _, _ => .botv
  | .num _, .vec _, h | .num _, .refv _, h | .num _, .botv, h
  | .vec _, .num _, h | .vec _, .refv _, h | .vec _, .botv, h
  | .refv _, .num _, h | .refv _, .vec _, h | .refv _, .botv, h => by
    simp [TypeCtx.checkValR] at h

/-- `TypeCtx.checkStorageR`. -/
theorem subB_checkStorageR (ht : Δ.types = []) (hR : RecsGoodB Δ) (M : List CSubType)
    {a b : CStorageType} (h : Δ.checkStorageR (fun _ => true) a b = true) :
    SubB (ext Δ M) a b := by
  cases a <;> cases b <;> simp [TypeCtx.checkStorageR] at h
  · exact .val (subB_checkValR ht hR M h)
  · subst h; exact .pack

/-- `TypeCtx.checkFieldR`. -/
theorem subB_checkFieldR (ht : Δ.types = []) (hR : RecsGoodB Δ) (M : List CSubType) :
    ∀ {a b : CFieldType}, Δ.checkFieldR (fun _ => true) a b = true → SubB (ext Δ M) a b
  | .field .const _, .field .const _, h => .fieldConst (subB_checkStorageR ht hR M h)
  | .field .var _, .field .var _, h => by
    simp only [TypeCtx.checkFieldR, Bool.and_eq_true] at h
    exact .fieldVar (subB_checkStorageR ht hR M h.1) (subB_checkStorageR ht hR M h.2)
  | .field .const _, .field .var _, h | .field .var _, .field .const _, h => by
    simp [TypeCtx.checkFieldR] at h

end

/-- Pointwise checks build pointwise canonical derivations. -/
theorem subB_forall2B {Δ : TypeCtx} {k : TKind} {f : Ty k → Ty k → Bool}
    (hf : ∀ a b, f a b = true → SubB Δ a b) :
    ∀ {l₁ l₂ : List (Ty k)}, forall2B f l₁ l₂ = true → SubB Δ (Ty.ofList l₁) (Ty.ofList l₂)
  | [], [], _ => .nil
  | a :: l, b :: l', h => by
    simp only [forall2B, Bool.and_eq_true] at h
    exact .cons (hf a b h.1) (subB_forall2B hf h.2)
  | [], _ :: _, h => by simp [forall2B] at h
  | _ :: _, [], h => by simp [forall2B] at h

/-- `subB_forall2B` on sequences. -/
theorem subB_forall2B' {Δ : TypeCtx} {k : TKind} {f : Ty k → Ty k → Bool}
    (hf : ∀ a b, f a b = true → SubB Δ a b) {l₁ l₂ : Ty (.list k)}
    (h : forall2B f l₁.toList l₂.toList = true) : SubB Δ l₁ l₂ := by
  have := subB_forall2B hf h
  rwa [Ty.ofList_toList, Ty.ofList_toList] at this

/-- **`TypeCtx.checkCompR` builds canonical derivations**, in every extension of `RECS`. -/
theorem subB_checkCompR {Δ : TypeCtx} (ht : Δ.types = []) (hR : RecsGoodB Δ) (M : List CSubType)
    {a b : CCompType} (h : Δ.checkCompR (fun _ => true) a b = true) : SubB (ext Δ M) a b := by
  cases a <;> cases b <;> simp only [TypeCtx.checkCompR, Bool.false_eq_true] at h
  · next fs₁ fs₂ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hs := subB_forall2B (fun _ _ => subB_checkFieldR ht hR M) h.2
    rw [Ty.ofList_toList] at hs
    have := SubB.struct (extra := Ty.ofList (fs₁.toList.drop fs₂.toList.length)) hs
    have e : (Ty.ofList (fs₁.toList.take fs₂.toList.length)).app
        (Ty.ofList (fs₁.toList.drop fs₂.toList.length)) = fs₁ := by
      simp [Ty.app]
    rwa [e] at this
  · exact .array (subB_checkFieldR ht hR M h)
  · simp only [Bool.and_eq_true] at h
    exact .func (subB_forall2B' (fun _ _ => subB_checkValR ht hR M) h.1)
      (subB_forall2B' (fun _ _ => subB_checkValR ht hR M) h.2)

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
