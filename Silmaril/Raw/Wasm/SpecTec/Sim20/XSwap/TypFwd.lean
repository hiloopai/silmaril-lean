module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.TypBase

/-!
# typing across the re-encoding: the forward direction, with a fuel shift (unrefined)

Round 8's `Raw/…/Round8/FiresC/TypFwd.lean`, for `EXPORTS` and `swapX` in `utf8Env20T B`.
`tFwdAt`: at every fuel `n`, if a member of the typing block answers `true` on checked types
(`xTy tyC20`), it answers `true` at fuel `n + K` on the re-encoded values in the re-encoded scope.
Calls out of the typing block go to the evaluator-level re-encoding (`EraseAll.eraseAt`) and are
lifted from fuel `n` to `n + K` by monotonicity.

The one place where the two sides differ is the `EXPORTS` field of `moduleinst`: the re-encoded
value is `τ u`. The hypothesis `ExpK B K` says that `τ u` is an `exportinst*` at fuel `n + K`
whenever `u` is one at fuel `n`. The field has no premises and its record type is an instance
without argument patterns, so it is typed in a scope without type variables, where `exportinst*`
reads no binding (`hasTyp_exportsT_scope`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll (Hyps SG ER ArgIn gr20 gd20 xExp xPrems xArgs
  xIter eraseAt)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap (exportsT)

variable {B : Builtins}

theorem mem_typs_of_findTyp20 {x : IL.Id} {v : TypDef} (h : (utf8Env20T B).findTyp? x = some v) :
    (x, v) ∈ typsOfDefs Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20 := by
  rw [Utf8Mono.findTyp?_utf8Env20T] at h
  unfold Silmaril.Wasm.SpecTec.Sim20.StoreFix.simEnv20T at h
  rw [show ∀ (e : Env), (e.withBuiltins B).findTyp? x = e.findTyp? x from fun _ => rfl] at h
  rw [envOfScript, envOfDefs_eq] at h
  have hm := Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.mem_of_find' h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

/-- The instances of a `tyC20` type are checked. -/
theorem xInsts_of_find {x : IL.Id} {v : TypDef}
    (h : (utf8Env20T B).findTyp? x = some v) (hS : tyC20.contains x = true) :
    xInsts tyC20 v.2 = true := by
  have hm := mem_typs_of_findTyp20 h
  have := List.all_eq_true.1 xTypMap20 _ hm
  simp only [hS, Bool.not_true, Bool.false_or] at this
  exact this

/-- **The re-encoding of an export list costs at most `K` more fuel to type.** -/
def ExpK (B : Builtins) (K : Nat) : Prop :=
  ∀ n u, hasTyp n (utf8Env20T B) VarEnv.empty exportsT u = .ok true →
    hasTyp (n + K) (utf8Env20T B) VarEnv.empty exportsT (XTau.τ u) = .ok true

theorem hasTypList_varT_scope {env : Env} {ρ ρ' : VarEnv} (hρ : ρ.typs = []) (hρ' : ρ'.typs = [])
    (x : IL.Id) : ∀ n vs, hasTypList n env ρ (.varT x []) vs = hasTypList n env ρ' (.varT x []) vs
  | 0, _ => by simp [hasTypList]
  | _ + 1, [] => by simp [hasTypList]
  | n + 1, v :: vs => by
    simp only [hasTypList]
    rw [Silmaril.Wasm.SpecTec.Sim20.ElseAgree.hasTyp_varT_eq hρ hρ' n x v,
      hasTypList_varT_scope hρ hρ' x n vs]

/-- `exportinst*` reads no binding of a scope without type variables. -/
theorem hasTyp_exportsT_scope {env : Env} {ρ ρ' : VarEnv} (hρ : ρ.typs = []) (hρ' : ρ'.typs = [])
    (n : Nat) (u : Value) : hasTyp n env ρ exportsT u = hasTyp n env ρ' exportsT u := by
  rcases n with _ | n
  · simp [hasTyp]
  · simp only [exportsT, hasTyp]
    cases u.asList? with
    | none => rfl
    | some vs => exact hasTypList_varT_scope hρ hρ' _ n vs

/-- **The typing block goes to the re-encoded side, from fuel `n` to fuel `n + K`.** -/
structure TFwdAt (B : Builtins) (K n : Nat) : Prop where
  typ : ∀ ρ t v, SG QT gd20 ρ → XT ρ → xTy tyC20 t = true →
    hasTyp n (utf8Env20T B) ρ t v = .ok true →
    hasTyp (n + K) (utf8Env20T B) (eraseScope ρ) t (swapX v) = .ok true
  tup : ∀ ρ bs vs, SG QT gd20 ρ → XT ρ → xTyBinds tyC20 bs = true →
    hasTypTup n (utf8Env20T B) ρ bs vs = .ok true →
    hasTypTup (n + K) (utf8Env20T B) (eraseScope ρ) bs (vs.map swapX) = .ok true
  list : ∀ ρ t vs, SG QT gd20 ρ → XT ρ → xTy tyC20 t = true →
    hasTypList n (utf8Env20T B) ρ t vs = .ok true →
    hasTypList (n + K) (utf8Env20T B) (eraseScope ρ) t (vs.map swapX) = .ok true
  defTyp : ∀ ρ dt v, SG QT gd20 ρ → XT ρ → xDefTyp tyC20 dt = true →
    (defTypExp dt = true → ρ.typs = []) →
    hasTypDef n (utf8Env20T B) ρ dt v = .ok true →
    hasTypDef (n + K) (utf8Env20T B) (eraseScope ρ) dt (swapX v) = .ok true
  fields : ∀ ρ fs gs, SG QT gd20 ρ → XT ρ → xTFields tyC20 fs = true →
    (fieldsExp fs = true → ρ.typs = []) →
    hasTypFields n (utf8Env20T B) ρ fs gs = .ok true →
    hasTypFields (n + K) (utf8Env20T B) (eraseScope ρ) fs (swapXf gs) = .ok true
  case : ∀ ρ cs op w, SG QT gd20 ρ → XT ρ → xTCases tyC20 cs = true →
    hasTypCase n (utf8Env20T B) ρ cs op w = .ok true →
    hasTypCase (n + K) (utf8Env20T B) (eraseScope ρ) cs op (swapX w) = .ok true
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgIn QT gd20 w) → (∀ w ∈ ws, ArgTyX w) →
    xInsts tyC20 insts = true → hasTypInsts n (utf8Env20T B) insts ws v = .ok true →
    hasTypInsts (n + K) (utf8Env20T B) insts (ws.map eraseA) (swapX v) = .ok true

theorem tFwdAt_zero {K : Nat} : TFwdAt B K 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (simp only [hasTyp] at *; contradiction)
    | (simp only [hasTypTup] at *; contradiction)
    | (simp only [hasTypList] at *; contradiction)
    | (simp only [hasTypDef] at *; contradiction)
    | (simp only [hasTypFields] at *; contradiction)
    | (simp only [hasTypCase] at *; contradiction)
    | (simp only [hasTypInsts] at *; contradiction)

theorem ite_ok_true {b : Bool} {r : Res Bool} (h : (if b = true then r else .ok false) = .ok true) :
    b = true ∧ r = .ok true := by
  cases b
  · simp at h
  · exact ⟨rfl, by simpa using h⟩

theorem iteP_ok_true {c : Prop} [Decidable c] {r : Res Bool}
    (h : (if c then r else .ok false) = .ok true) : c ∧ r = .ok true := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; exact ⟨hc, h⟩
  · simp [hc] at h

theorem fieldsExp_cons {a : AtomS} {t : Typ} {qs : List Param} {prems : List Prem}
    {fs : List TypField} :
    fieldsExp (.mk a t qs prems :: fs) = ((a == "EXPORTS") || fieldsExp fs) := by
  simp [fieldsExp]

theorem isExpT_eq {t : Typ} (h : isExpT t = true) : t = exportsT := by
  unfold isExpT at h
  split at h
  · rfl
  · cases h

theorem premsOk_nil {env : Env} {m : Nat} {σ σ' : VarEnv}
    (h : premsOk m env σ [] = .ok true) : premsOk m env σ' [] = .ok true := by
  rcases m with _ | m
  · simp [premsOk, premsHold, Res.elimUndef] at h
  · simp [premsOk, premsHold_nil_eq, Res.elimUndef]

/-- An answer of the evaluator at fuel `m`, at fuel `m + K`. -/
theorem evalExp_lift {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} {m K : Nat}
    (h : evalExp m env ρ e = .ok v) : evalExp (m + K) env ρ e = .ok v :=
  evalExp_ok_of_le (Nat.le_add_right m K) h

theorem evalArgs_lift {env : Env} {ρ : VarEnv} {l : List Arg} {ws : List ArgV} {m K : Nat}
    (h : evalArgs m env ρ l = .ok ws) : evalArgs (m + K) env ρ l = .ok ws :=
  ((monoAt_of_le (Nat.le_add_right m K)).args env ρ l).ok h

theorem premsOk_lift {env : Env} {ρ : VarEnv} {prems : List Prem} {b : Bool} {m K : Nat}
    (h : premsOk m env ρ prems = .ok b) : premsOk (m + K) env ρ prems = .ok b :=
  premsOk_ok_of_le (Nat.le_add_right m K) h

theorem matchArgs_lift {env : Env} {ρ : VarEnv} {l : List Arg} {ws : List ArgV} {m K : Nat}
    {r : Res VarEnv} (hr : r ≠ .error .outOfFuel) (h : matchArgs m env ρ l ws = r) :
    matchArgs (m + K) env ρ l ws = r := by
  rw [← h]
  exact ((monoAt_of_le (Nat.le_add_right m K)).matchArgs env ρ l ws).eq_of_ne_oof (h ▸ hr)

section Step

variable (H : Hyps QT gr20 gd20 (utf8Env20T B)) {K : Nat} (hK : ExpK B K) {m : Nat}
  (ih : TFwdAt B K m)
include H ih

/-- `hasTyp`, one step. -/
theorem tf_typ : ∀ ρ t v, SG QT gd20 ρ → XT ρ → xTy tyC20 t = true →
    hasTyp (m + 1) (utf8Env20T B) ρ t v = .ok true →
    hasTyp (m + K + 1) (utf8Env20T B) (eraseScope ρ) t (swapX v) = .ok true := by
  intro ρ t v hρ hX ht h
  cases t with
  | boolT => simpa [hasTyp, asBool?_eraseC] using h
  | numT t => simpa [hasTyp, asNum?_eraseC] using h
  | textT => simpa [hasTyp, asText?_eraseC] using h
  | tupT bs =>
    simp only [xTy] at ht
    simp only [hasTyp, asTuple?_eraseC] at h ⊢
    cases hvt : v.asTuple? with
    | none => rw [hvt] at h; cases h
    | some vs =>
      rw [hvt] at h
      exact ih.tup _ _ _ hρ hX ht h
  | iterT t it =>
    simp only [xTy, Bool.and_eq_true] at ht
    cases it with
    | opt =>
      simp only [hasTyp, asOpt?_eraseC] at h ⊢
      cases hvo : v.asOpt? with
      | none => rw [hvo] at h; cases h
      | some o =>
        rw [hvo] at h
        cases o with
        | none => rfl
        | some w => exact ih.typ _ _ _ hρ hX ht.1 h
    | list =>
      simp only [hasTyp, asList?_eraseC] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        exact ih.list _ _ _ hρ hX ht.1 h
    | list1 =>
      simp only [hasTyp, asList?_eraseC] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        simp only [Option.map_some, List.isEmpty_map]
        by_cases he : vs.isEmpty = true
        · simp [he] at h
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ih.list _ _ _ hρ hX ht.1 h
    | listN e o =>
      have hxe : xExp gr20 gd20 e = true := by simpa [EraseAll.xIter] using ht.2
      simp only [hasTyp, asList?_eraseC] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        simp only [Option.map_some, Res.bind_eq_ok] at h ⊢
        obtain ⟨kv, hkv, k, hk, hl⟩ := h
        have hE := (eraseAt H m).exp ρ e hρ hxe
        refine ⟨swapX kv, evalExp_lift (EraseAll.ER.eq_ok hE hkv), k,
          by rw [asNat?_eraseC]; exact hk, ?_⟩
        obtain ⟨hlen, hl⟩ := iteP_ok_true hl
        simp only [List.length_map, hlen, ↓reduceIte]
        exact ih.list _ _ _ hρ hX ht.1 hl
  | varT x args =>
    simp only [xTy, Bool.and_eq_true] at ht
    simp only [hasTyp] at h ⊢
    have hloc : localTyp? (eraseScope ρ) x args = localTyp? ρ x args := by
      cases args with
      | nil => simp only [localTyp?, VarEnv.findTyp?, EraseAll.eraseScope_typs]
      | cons _ _ => rfl
    rw [hloc]
    cases hl : localTyp? ρ x args with
    | some t' =>
      rw [hl] at h
      have ht' : TyX t' := by
        cases args with
        | nil => exact hX (x, t') (Silmaril.Wasm.SpecTec.Sim.Round7.Script.mem_of_find? hl)
        | cons _ _ => simp [localTyp?] at hl
      exact ih.typ _ _ _ hρ hX ht'.1 h
    | none =>
      rw [hl] at h
      simp only [Res.bind_eq_ok] at h ⊢
      obtain ⟨td, htd, ws, hws, hi⟩ := h
      have htd' : (utf8Env20T B).findTyp? x = some td := by
        cases hf : (utf8Env20T B).findTyp? x with
        | none => rw [hf] at htd; simp [Res.ofOption] at htd
        | some td' => rw [hf] at htd; simp [Res.ofOption] at htd; rw [htd]
      have hE := (eraseAt H m).args ρ args hρ (xArgs_of_xTyArgs ht.2)
      refine ⟨td, htd, ws.map eraseA, evalArgs_lift (EraseAll.ER.eq_ok hE hws), ?_⟩
      exact ih.insts _ _ _ (hE.2 ws hws) (evalArgs_argTyX hX ht.2 hws)
        (xInsts_of_find htd' ht.1) hi

/-- `hasTypTup`, one step. -/
theorem tf_tup : ∀ ρ bs vs, SG QT gd20 ρ → XT ρ → xTyBinds tyC20 bs = true →
    hasTypTup (m + 1) (utf8Env20T B) ρ bs vs = .ok true →
    hasTypTup (m + K + 1) (utf8Env20T B) (eraseScope ρ) bs (vs.map swapX) = .ok true := by
  intro ρ bs vs hρ hX hbs h
  cases bs with
  | nil => cases vs <;> simp_all [hasTypTup]
  | cons b bs =>
    obtain ⟨x, t⟩ := b
    simp only [xTyBinds, Bool.and_eq_true] at hbs
    cases vs with
    | nil => simp [hasTypTup] at h
    | cons v vs =>
      simp only [hasTypTup, Res.bind_eq_ok, List.map_cons] at h ⊢
      obtain ⟨c, hc, hrest⟩ := h
      cases c
      · simp at hrest
      · simp only [↓reduceIte] at hrest
        refine ⟨true, ih.typ _ _ _ hρ hX hbs.1 hc, ?_⟩
        simp only [↓reduceIte]
        rw [← EraseAll.eraseScope_bindVal]
        exact ih.tup _ _ _ (hρ.bindVal (EraseAll.allIn_true v)) hX hbs.2 hrest

/-- `hasTypList`, one step. -/
theorem tf_list : ∀ ρ t vs, SG QT gd20 ρ → XT ρ → xTy tyC20 t = true →
    hasTypList (m + 1) (utf8Env20T B) ρ t vs = .ok true →
    hasTypList (m + K + 1) (utf8Env20T B) (eraseScope ρ) t (vs.map swapX) = .ok true := by
  intro ρ t vs hρ hX ht h
  cases vs with
  | nil => simp [hasTypList]
  | cons v vs =>
    simp only [hasTypList, Res.bind_eq_ok, List.map_cons] at h ⊢
    obtain ⟨c, hc, hrest⟩ := h
    cases c
    · simp at hrest
    · simp only [↓reduceIte] at hrest
      refine ⟨true, ih.typ _ _ _ hρ hX ht hc, ?_⟩
      simp only [↓reduceIte]
      exact ih.list _ _ _ hρ hX ht hrest

/-- `hasTypDef`, one step. -/
theorem tf_defTyp : ∀ ρ dt v, SG QT gd20 ρ → XT ρ → xDefTyp tyC20 dt = true →
    (defTypExp dt = true → ρ.typs = []) →
    hasTypDef (m + 1) (utf8Env20T B) ρ dt v = .ok true →
    hasTypDef (m + K + 1) (utf8Env20T B) (eraseScope ρ) dt (swapX v) = .ok true := by
  intro ρ dt v hρ hX hdt hT h
  cases dt with
  | aliasT t =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef] at h ⊢
    exact ih.typ _ _ _ hρ hX hdt h
  | structT fs =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef, EraseAll.asStruct?_eraseC] at h ⊢
    cases hvs : v.asStruct? with
    | none => rw [hvs] at h; cases h
    | some gs =>
      rw [hvs] at h
      exact ih.fields _ _ _ hρ hX hdt hT h
  | variantT cs =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef, asCase?_eraseC] at h ⊢
    cases hvc : v.asCase? with
    | none => rw [hvc] at h; cases h
    | some p =>
      rw [hvc] at h
      exact ih.case _ _ _ _ hρ hX hdt h

include hK in
/-- **The `EXPORTS` field**: `τ u` is an `exportinst*` at fuel `m + K` when `u` is one at `m`. -/
theorem tf_exports {ρ : VarEnv} (hρT : ρ.typs = []) {w : Value}
    (hc : hasTyp m (utf8Env20T B) ρ exportsT w = .ok true) :
    hasTyp (m + K) (utf8Env20T B) (eraseScope ρ) exportsT (XTau.τ w) = .ok true := by
  rw [hasTyp_exportsT_scope (ρ' := VarEnv.empty) hρT rfl] at hc
  rw [hasTyp_exportsT_scope (ρ' := VarEnv.empty) (by simpa using hρT) rfl]
  exact hK m w hc

include hK in
/-- `hasTypFields`, one step. -/
theorem tf_fields : ∀ ρ fs gs, SG QT gd20 ρ → XT ρ → xTFields tyC20 fs = true →
    (fieldsExp fs = true → ρ.typs = []) →
    hasTypFields (m + 1) (utf8Env20T B) ρ fs gs = .ok true →
    hasTypFields (m + K + 1) (utf8Env20T B) (eraseScope ρ) fs (swapXf gs) = .ok true := by
  intro ρ fs gs hρ hX hfs hT h
  cases fs with
  | nil =>
    cases gs with
    | nil => simp [hasTypFields]
    | cons _ _ => simp [hasTypFields] at h
  | cons f fs =>
    obtain ⟨a, t, qs, prems⟩ := f
    cases gs with
    | nil => simp [hasTypFields] at h
    | cons g gs =>
      obtain ⟨a', w⟩ := g
      simp only [xTFields, Bool.and_eq_true] at hfs
      obtain ⟨hf, hfs⟩ := hfs
      simp only [hasTypFields, swapXf_cons] at h ⊢
      obtain ⟨haa, h₁⟩ := iteP_ok_true h
      subst haa
      rw [Res.bind_eq_ok] at h₁
      obtain ⟨c, hc, h₂⟩ := h₁
      obtain ⟨hc₁, h₃⟩ := ite_ok_true h₂
      subst hc₁
      rw [Res.bind_eq_ok] at h₃
      obtain ⟨hp, hpv, h₄⟩ := h₃
      obtain ⟨hp₁, hrest⟩ := ite_ok_true h₄
      subst hp₁
      have hT' : fieldsExp fs = true → ρ.typs = [] := fun hc => hT (by
        rw [fieldsExp_cons, hc, Bool.or_true])
      have htail := ih.fields _ _ _ hρ hX hfs hT' hrest
      simp only [↓reduceIte]
      rw [Res.bind_eq_ok]
      by_cases hE : a = "EXPORTS"
      · subst hE
        simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.isEmpty_iff] at hf
        obtain ⟨hTc, rfl⟩ := hf
        have hρT : ρ.typs = [] := hT (by rw [fieldsExp_cons]; rfl)
        rw [isExpT_eq hTc] at hc ⊢
        refine ⟨true, tf_exports H hK ih hρT hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        exact ⟨true, premsOk_nil (premsOk_lift hpv), by simpa using htail⟩
      · have hne : (a == "EXPORTS") = false := by simpa using hE
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hf
        simp only [hE, ↓reduceIte]
        refine ⟨true, ih.typ _ _ _ hρ hX hf.1 hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        refine ⟨true, ?_, by simpa using htail⟩
        rw [caseScope_erase, premsOk_er H (sg_caseScope hρ t w) hf.2]
        exact premsOk_lift hpv

/-- `bindQuants` goes to the re-encoded side. -/
theorem tf_bindQuants : ∀ (ρ : VarEnv) (ds : List (IL.Id × Typ × Exp)) (ρq : VarEnv),
    SG QT gd20 ρ → XT ρ → (∀ d ∈ ds, xExp gr20 gd20 d.2.2 = true ∧ xTy tyC20 d.2.1 = true) →
    bindQuants (fun ρ e => evalExp m (utf8Env20T B) ρ e)
      (fun ρ t v => hasTyp m (utf8Env20T B) ρ t v) ρ ds = .ok (some ρq) →
    SG QT gd20 ρq ∧ XT ρq ∧
      bindQuants (fun ρ e => evalExp (m + K) (utf8Env20T B) ρ e)
        (fun ρ t v => hasTyp (m + K) (utf8Env20T B) ρ t v)
        (eraseScope ρ) ds = .ok (some (eraseScope ρq))
  | ρ, [], ρq, hρ, hX, _, h => by
    simp only [bindQuants, Except.ok.injEq, Option.some.injEq] at h
    subst h; exact ⟨hρ, hX, rfl⟩
  | ρ, (x, t, e) :: ds, ρq, hρ, hX, hds, h => by
    have h₀ := hds _ List.mem_cons_self
    simp only [bindQuants, Res.bind_eq_ok] at h ⊢
    obtain ⟨v, hv, c, hc, h⟩ := h
    have hE := (eraseAt H m).exp ρ e hρ h₀.1
    cases c
    · simp at h
    · simp only [↓reduceIte] at h
      have ih' := tf_bindQuants (ρ.bindVal x v) ds ρq
        (hρ.bindVal (EraseAll.allIn_true v)) hX
        (fun d hd => hds d (List.mem_cons_of_mem _ hd)) h
      refine ⟨ih'.1, ih'.2.1, swapX v, evalExp_lift (EraseAll.ER.eq_ok hE hv), true,
        ih.typ _ _ _ hρ hX h₀.2 hc, ?_⟩
      simp only [↓reduceIte]
      rw [← EraseAll.eraseScope_bindVal]
      exact ih'.2.2

/-- `hasTypCase`, one step. -/
theorem tf_case : ∀ ρ cs op w, SG QT gd20 ρ → XT ρ → xTCases tyC20 cs = true →
    hasTypCase (m + 1) (utf8Env20T B) ρ cs op w = .ok true →
    hasTypCase (m + K + 1) (utf8Env20T B) (eraseScope ρ) cs op (swapX w) = .ok true := by
  intro ρ cs op w hρ hX hcs h
  cases cs with
  | nil => simp [hasTypCase] at h
  | cons c cs =>
    obtain ⟨op', t, qs, prems⟩ := c
    simp only [xTCases, Bool.and_eq_true] at hcs
    obtain ⟨⟨⟨hct, hq⟩, hpr⟩, hcs⟩ := hcs
    simp only [hasTypCase] at h ⊢
    by_cases hop : op' = op
    · simp only [hop, ↓reduceIte, Res.bind_eq_ok] at h ⊢
      obtain ⟨c, hc, h⟩ := h
      have hc' : c = true := by cases c <;> simp_all
      subst hc'
      simp only [↓reduceIte] at h
      refine ⟨true, ih.typ _ _ _ hρ hX hct hc, ?_⟩
      simp only [↓reduceIte]
      have hcs₀ := sg_caseScope hρ t w
      have hXc : XT (caseScope ρ t w) :=
        xt_of_typs hX (Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.caseScope_typs ρ t w).1
      rcases Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.elimUndef_eq_ok' h with ⟨o, ho, hk⟩ | ⟨_, hk⟩
      · cases o with
        | none => simp at hk
        | some ρq =>
          obtain ⟨hρq, -, hb⟩ := tf_bindQuants H ih _ _ ρq hcs₀ hXc (quantDefs_x hpr hq) ho
          rw [caseScope_erase, hb]
          simp only [Res.elimUndef]
          rw [premsOk_er H hρq hpr]
          exact premsOk_lift hk
      · simp at hk
    · simp only [hop, ↓reduceIte] at h ⊢
      exact ih.case _ _ _ _ hρ hX hcs h

/-- `hasTypInsts`, one step. -/
theorem tf_insts : ∀ insts ws v, (∀ w ∈ ws, ArgIn QT gd20 w) → (∀ w ∈ ws, ArgTyX w) →
    xInsts tyC20 insts = true → hasTypInsts (m + 1) (utf8Env20T B) insts ws v = .ok true →
    hasTypInsts (m + K + 1) (utf8Env20T B) insts (ws.map eraseA) (swapX v) = .ok true := by
  intro insts ws v hW hWT hins h
  cases insts with
  | nil => simp [hasTypInsts] at h
  | cons i insts =>
    obtain ⟨qs, pats, dt⟩ := i
    simp only [xInsts, List.all_cons, Bool.and_eq_true] at hins
    obtain ⟨⟨⟨hpats, hdt⟩, hexp⟩, hins⟩ := hins
    simp only [hasTypInsts] at h ⊢
    have hE := (eraseAt H m).matchArgs VarEnv.empty pats ws EraseAll.sg_empty hpats hW
    rw [EraseAll.eraseScope_empty] at hE
    rcases Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.elimUndef_eq_ok' h with ⟨ρi, hρi, hk⟩ | ⟨hu, hk⟩
    · have hm' : matchArgs m (utf8Env20T B) VarEnv.empty pats (ws.map eraseA) =
          .ok (eraseScope ρi) := by rw [hE.1, hρi]; rfl
      rw [matchArgs_lift (by simp) hm']
      simp only [Res.elimUndef]
      have hT : defTypExp dt = true → ρi.typs = [] := by
        intro hc
        rw [hc, Bool.not_true, Bool.false_or, List.isEmpty_iff] at hexp
        subst hexp
        rw [matchArgs_nil hρi]
        rfl
      exact ih.defTyp _ _ _ (hE.2 ρi hρi) (matchArgs_xt m xt_empty hWT hρi) hdt hT hk
    · have hm' : matchArgs m (utf8Env20T B) VarEnv.empty pats (ws.map eraseA) =
          .error .undef := by rw [hE.1, hu]; rfl
      rw [matchArgs_lift (by simp) hm']
      simp only [Res.elimUndef]
      exact ih.insts _ _ _ hW hWT (by unfold xInsts; exact hins) hk

end Step

theorem tFwdAt_succ (H : Hyps QT gr20 gd20 (utf8Env20T B)) {K : Nat} (hK : ExpK B K) {m : Nat}
    (ih : TFwdAt B K m) : TFwdAt B K (m + 1) := by
  have e : m + 1 + K = m + K + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rw [e]
  · exact tf_typ H ih _ _ _ ‹_› ‹_› ‹_› ‹_›
  · exact tf_tup H ih _ _ _ ‹_› ‹_› ‹_› ‹_›
  · exact tf_list H ih _ _ _ ‹_› ‹_› ‹_› ‹_›
  · exact tf_defTyp H ih _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›
  · exact tf_fields H hK ih _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›
  · exact tf_case H ih _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  · exact tf_insts H ih _ _ _ ‹_› ‹_› ‹_› ‹_›

/-- **The typing block goes to the re-encoded side, at every fuel, `K` fuel later.** -/
theorem tFwdAt (H : Hyps QT gr20 gd20 (utf8Env20T B)) {K : Nat} (hK : ExpK B K) :
    ∀ n, TFwdAt B K n
  | 0 => tFwdAt_zero
  | n + 1 => tFwdAt_succ H hK (tFwdAt H hK n)

/-- **Typing goes to the re-encoded side**, at a checked type, in a scope whose definition
variables are `gd20` and whose type variables are bound to closed checked types. -/
theorem hasTyp_erase (H : Hyps QT gr20 gd20 (utf8Env20T B)) {K : Nat} (hK : ExpK B K)
    {ρ : VarEnv} {t : Typ} {v : Value} (hρ : SG QT gd20 ρ) (hX : XT ρ) (ht : xTy tyC20 t = true)
    (h : HasTyp (utf8Env20T B) ρ t v) : HasTyp (utf8Env20T B) (eraseScope ρ) t (swapX v) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + K, (tFwdAt H hK n).typ ρ t v hρ hX ht hn⟩

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ
