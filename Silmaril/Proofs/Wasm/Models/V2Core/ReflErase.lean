module

public import Silmaril.Wasm.V2.ToCore.Validation
public import Silmaril.Wasm.Validation.Subtyping.Check
public import Silmaril.Wasm.Validation.Instructions.Properties

/-!
# Reading Core 3.0 value types back as Wasm 2.0 value types

The reflection half of `V20CoreValid` turns a Core 3.0 typing of the image of 2.0 code into
a 2.0 typing. A Core derivation may mention types that 2.0 does not have: the non-nullable
`(ref $t)` that Core gives `ref.func`, `nofunc`, and arbitrary GC types produced by stack
polymorphism after `unreachable`. `er Δ` reads every Core value type back as a 2.0 one:

* numeric and vector types are themselves;
* a reference into the function hierarchy (`func`, `nofunc`, a defined function type) is
  `funcref`, one into the extern hierarchy is `externref`;
* everything else (the GC and exception hierarchies, `BOT`) is 2.0's `BOT`.

`er_sub` is the key fact: along Core subtyping between valid types (in a well-formed context with
no `RECS`), `er` is either `BOT` on the left or the identity, which is exactly 2.0 subtyping. It
goes through the complete Boolean subtyping checker (`Sub.check_complete`), whose heap-type case
keeps the hierarchy of a type (`checkHeap_er`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.Validation (Ty TyOk Sub TypeCtx defKind absSub botTop compAbs)

/-- Core 3.0 validation value types. -/
abbrev KVal := Silmaril.Wasm.Validation.CValType
/-- Wasm 2.0 validation value types. -/
abbrev VVal := Silmaril.Wasm.V2.Validation.CValType

/-- The 2.0 reference type of an abstract heap type: its hierarchy, if it has a 2.0 top. -/
def erAbs : Silmaril.Wasm.AbsHeapType → Option Silmaril.Wasm.V2.RefType
  | .func | .nofunc => some .funcref
  | .extern | .noextern => some .externref
  | _ => none

/-- The 2.0 reference type of a Core heap type: defined function types are `funcref`. -/
def erHeap (Δ : TypeCtx) : Silmaril.Wasm.Validation.CHeapType → Option Silmaril.Wasm.V2.RefType
  | .abs a => erAbs a
  | .bot => none
  | .use u =>
    match Δ.resolve u >>= defKind with
    | some .func => some .funcref
    | _ => none

/-- **The read-back of a Core value type as a 2.0 one.** -/
def er (Δ : TypeCtx) : KVal → VVal
  | .num t => .val (.num t)
  | .vec t => .val (.vec t)
  | .refv (.ref _ h) =>
    match erHeap Δ h with
    | some r => .val (.ref r)
    | none => .bot
  | .botv => .bot

/-- `er` on result types. -/
abbrev ers (Δ : TypeCtx) (ts : List KVal) : List VVal := ts.map (er Δ)

/-! ## `er` is a retraction of `valToC` -/

@[simp] theorem er_toC (Δ : TypeCtx) (t : Silmaril.Wasm.V2.ValType) :
    er Δ (Silmaril.Wasm.V2.ValType.toC t) = .val t := by
  cases t with
  | num t => rfl
  | vec t => rfl
  | ref r => cases r <;> rfl

@[simp] theorem er_valToC (Δ : TypeCtx) (t : VVal) :
    er Δ (Silmaril.Wasm.V2.Validation.valToC t) = t := by
  cases t with
  | val t => exact er_toC Δ t
  | bot => rfl

@[simp] theorem ers_resultToC (Δ : TypeCtx) (ts : List VVal) :
    ers Δ (Silmaril.Wasm.V2.Validation.resultToC ts) = ts := by
  simp [ers, List.map_map, Function.comp_def]

@[simp] theorem ers_map_toC (Δ : TypeCtx) (ts : List Silmaril.Wasm.V2.ValType) :
    ers Δ (ts.map Silmaril.Wasm.V2.ValType.toC) = Silmaril.Wasm.V2.Validation.liftResult ts := by
  simp [ers, List.map_map, Function.comp_def, Silmaril.Wasm.V2.Validation.liftResult]

@[simp] theorem er_num (Δ : TypeCtx) (t : Silmaril.Wasm.NumType) : er Δ (.num t) = .val (.num t) :=
  rfl

@[simp] theorem er_vec (Δ : TypeCtx) (t : Silmaril.Wasm.VecType) : er Δ (.vec t) = .val (.vec t) :=
  rfl

@[simp] theorem er_botv (Δ : TypeCtx) : er Δ .botv = .bot := rfl

/-! ## Hierarchies are kept along subtyping -/

/-- Abstract heap subtyping keeps the hierarchy (or starts at a bottom with no 2.0 top). -/
theorem absSub_er : ∀ {a b : Silmaril.Wasm.AbsHeapType}, absSub a b = true →
    erAbs a = none ∨ erAbs a = erAbs b := by
  intro a b h
  cases a <;> cases b <;> first | exact .inl rfl | exact .inr rfl | exact absurd h (by decide)

/-- The kind of a defined type is the abstract type of a composite type. -/
theorem defKind_cases {d : Silmaril.Wasm.Validation.DefType} {k : Silmaril.Wasm.AbsHeapType}
    (h : defKind d = some k) : k = .struct ∨ k = .array ∨ k = .func := by
  obtain ⟨c, rfl⟩ := Silmaril.Wasm.Validation.defKind_compAbs h
  cases c <;> simp [compAbs]

/-- `erHeap` of a type use through its kind. -/
theorem erHeap_use (Δ : TypeCtx) (u : Silmaril.Wasm.Validation.CTypeUse) :
    erHeap Δ (.use u) = if Δ.resolve u >>= defKind = some .func then some .funcref else none := by
  simp only [erHeap]
  split <;> simp_all

/-- `checkUseAbs` against an abstract type: the use is a function type exactly when the abstract
type is in the function hierarchy. -/
theorem useAbs_er {Δ : TypeCtx} {u : Silmaril.Wasm.Validation.CTypeUse}
    {b : Silmaril.Wasm.AbsHeapType} (h : Δ.checkUseAbs u b = true) :
    ∃ k, Δ.resolve u >>= defKind = some k ∧ absSub k b = true ∧
      (k = .struct ∨ k = .array ∨ k = .func) := by
  unfold TypeCtx.checkUseAbs at h
  cases hk : Δ.resolve u >>= defKind with
  | none => simp [hk] at h
  | some k =>
    have hab : absSub k b = true := by simpa [hk] using h
    obtain ⟨d, -, hd⟩ := Option.bind_eq_some_iff.mp hk
    exact ⟨k, rfl, hab, defKind_cases hd⟩

/-- A use below an abstract type. -/
theorem checkHeap_use_abs {Δ : TypeCtx} {u : Silmaril.Wasm.Validation.CTypeUse}
    {b : Silmaril.Wasm.AbsHeapType} (h : Δ.checkUseAbs u b = true) :
    erHeap Δ (.use u) = none ∨ erHeap Δ (.use u) = erAbs b := by
  obtain ⟨k, hk, hab, hc⟩ := useAbs_er h
  rw [erHeap_use, hk]
  rcases hc with rfl | rfl | rfl
  · exact .inl (by simp)
  · exact .inl (by simp)
  · cases b <;> first | exact .inr rfl | exact absurd hab (by decide)

/-- A bottom abstract type below a use. -/
theorem checkHeap_abs_use {Δ : TypeCtx} {a t : Silmaril.Wasm.AbsHeapType}
    {u : Silmaril.Wasm.Validation.CTypeUse} (ht : botTop a = some t)
    (h : Δ.checkUseAbs u t = true) : erAbs a = none ∨ erAbs a = erHeap Δ (.use u) := by
  obtain ⟨k, hk, hab, hc⟩ := useAbs_er h
  rw [erHeap_use, hk]
  cases a <;> simp only [botTop, reduceCtorEq, Option.some.injEq] at ht <;> subst ht <;>
    rcases hc with rfl | rfl | rfl <;> first | exact .inl rfl | exact .inr rfl |
      exact absurd hab (by decide)

/-- Two uses related by the definition checker have the same kind. -/
theorem checkHeap_use_use {Δ : TypeCtx} (hΔ : Δ.Ok) {u₁ u₂ : Silmaril.Wasm.Validation.CTypeUse}
    {d₁ d₂ : Silmaril.Wasm.Validation.DefType} (h₁ : Δ.resolve u₁ = some d₁)
    (h₂ : Δ.resolve u₂ = some d₂) (hd : TyOk Δ d₁) (h : Δ.checkDef d₁ d₂ = true) :
    erHeap Δ (.use u₁) = erHeap Δ (.use u₂) := by
  have hk : defKind d₂ = defKind d₁ := Silmaril.Wasm.Validation.TypeCtx.checkDef_kind hΔ hd h
  rw [erHeap_use, erHeap_use, h₁, h₂]
  simp [hk]

/-- **Heap-type checking keeps the 2.0 hierarchy.** -/
theorem checkHeap_er {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {h₁ h₂ : Silmaril.Wasm.Validation.CHeapType} (hok : TyOk Δ h₁)
    (h : Δ.checkHeap h₁ h₂ = true) : erHeap Δ h₁ = none ∨ erHeap Δ h₁ = erHeap Δ h₂ := by
  match h₁, h₂, hok, h with
  | .bot, _, _, _ => exact .inl rfl
  | .abs a, .abs b, _, h => exact absSub_er h
  | .abs a, .use u, _, h =>
    cases ht : botTop a with
    | none => simp [TypeCtx.checkHeap, ht] at h
    | some t => exact checkHeap_abs_use ht (by simpa [TypeCtx.checkHeap, ht] using h)
  | .use u, .abs b, _, h => exact checkHeap_use_abs h
  | .use u₁, .use u₂, hok, h =>
    obtain ⟨d₁, hd₁, hok₁⟩ := Silmaril.Wasm.Validation.TypeCtx.resolve_ok hΔ hr
      (Silmaril.Wasm.Validation.TyOk.use_inv hok)
    cases hd₂ : Δ.resolve u₂ with
    | none => simp [TypeCtx.checkHeap, hd₁, hd₂] at h
    | some d₂ =>
      exact .inr (checkHeap_use_use hΔ hd₁ hd₂ hok₁ (by simpa [TypeCtx.checkHeap, hd₁, hd₂] using h))
  | .abs _, .bot, _, h => simp [TypeCtx.checkHeap] at h
  | .use _, .bot, _, h => simp [TypeCtx.checkHeap] at h

/-- `er` of a reference type through its heap type. -/
theorem er_refv (Δ : TypeCtx) (n : Bool) (h : Silmaril.Wasm.Validation.CHeapType) :
    er Δ (.refv (.ref n h)) = ((erHeap Δ h).map fun r => Silmaril.Wasm.V2.Validation.CValType.val (.ref r)).getD .bot := by
  simp only [er]
  split <;> simp_all

/-- Checked reference subtyping is 2.0 subtyping after reading back. -/
theorem checkRef_er {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {n₁ n₂ : Bool}
    {h₁ h₂ : Silmaril.Wasm.Validation.CHeapType} (hok : TyOk Δ (Silmaril.Wasm.Validation.Ty.refv (.ref n₁ h₁)))
    (h : Δ.checkVal (.refv (.ref n₁ h₁)) (.refv (.ref n₂ h₂)) = true) :
    (er Δ (.refv (.ref n₁ h₁))).Sub (er Δ (.refv (.ref n₂ h₂))) := by
  have hh : Δ.checkHeap h₁ h₂ = true := by
    simp only [TypeCtx.checkVal, TypeCtx.checkRef, Bool.and_eq_true] at h
    exact h.2
  have hok₁ : TyOk Δ h₁ :=
    Silmaril.Wasm.Validation.TyOk.ref_inv (Silmaril.Wasm.Validation.TyOk.refv_inv hok)
  rcases checkHeap_er hΔ hr hok₁ hh with e | e
  · rw [er_refv, e]; exact .bot _
  · rw [er_refv, er_refv, e]; exact .refl _

/-- Checked value subtyping is 2.0 subtyping after reading back. -/
theorem checkVal_er {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {a b : KVal} (hok : TyOk Δ a)
    (h : Δ.checkVal a b = true) : (er Δ a).Sub (er Δ b) := by
  match a, b, hok, h with
  | .num _, .num _, _, h => rw [of_decide_eq_true h]; exact .refl _
  | .vec _, .vec _, _, h => rw [of_decide_eq_true h]; exact .refl _
  | .botv, _, _, _ => exact .bot _
  | .refv (.ref _ _), .refv (.ref _ _), hok, h => exact checkRef_er hΔ hr hok h
  | .num _, .vec _, _, h | .num _, .refv _, _, h | .num _, .botv, _, h
  | .vec _, .num _, _, h | .vec _, .refv _, _, h | .vec _, .botv, _, h
  | .refv _, .num _, _, h | .refv _, .vec _, _, h | .refv _, .botv, _, h =>
    exact absurd h (by simp [TypeCtx.checkVal])

/-- **Core subtyping between valid types reads back as 2.0 subtyping.** -/
theorem er_sub {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {a b : KVal} (ha : TyOk Δ a)
    (hb : TyOk Δ b) (h : Silmaril.Wasm.Validation.Sub Δ a b) : (er Δ a).Sub (er Δ b) :=
  checkVal_er hΔ hr ha (Silmaril.Wasm.Validation.Sub.check_complete hΔ hr h ha hb)

/-- Result subtyping between valid result types reads back pointwise. -/
theorem ers_sub {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) :
    ∀ {a b : List KVal}, Silmaril.Wasm.Validation.ResultOk Δ a →
      Silmaril.Wasm.Validation.ResultOk Δ b → Silmaril.Wasm.Validation.ResultSub Δ a b →
      Silmaril.Wasm.V2.Validation.CResultType.Sub (ers Δ a) (ers Δ b)
  | _, _, _, _, .nil => .nil
  | _, _, ha, hb, .cons h hs =>
    .cons (er_sub hΔ hr (ha _ (by simp)) (hb _ (by simp)) h)
      (ers_sub hΔ hr (fun t ht => ha t (by simp [ht])) (fun t ht => hb t (by simp [ht])) hs)

/-- Subtyping into an image type from a non-bottom read-back is equality. -/
theorem er_sub_val {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {a : KVal}
    {t : Silmaril.Wasm.V2.ValType} (ha : TyOk Δ a)
    (h : Silmaril.Wasm.Validation.Sub Δ (Silmaril.Wasm.V2.ValType.toC t) a) : er Δ a = .val t := by
  have hs := er_sub hΔ hr (Silmaril.Wasm.V2.Validation.tyOk_toC Δ t) ha h
  rw [er_toC] at hs
  rcases Silmaril.Wasm.V2.Validation.CValType.sub_iff.mp hs with e | e
  · exact e.symm
  · cases e

/-- Subtyping between two image types is equality. -/
theorem toC_sub_toC {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {t u : Silmaril.Wasm.V2.ValType}
    (h : Silmaril.Wasm.Validation.Sub Δ (Silmaril.Wasm.V2.ValType.toC t)
      (Silmaril.Wasm.V2.ValType.toC u)) : t = u := by
  have e := er_sub_val hΔ hr (Silmaril.Wasm.V2.Validation.tyOk_toC Δ u) h
  rw [er_toC] at e
  exact (Silmaril.Wasm.V2.Validation.CValType.val.inj e).symm

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
