module

public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # Strengthening validity and subtyping to the empty context

A runtime context `Δ` (e.g. `C.toTypeCtx` for a `Moduleinst_ok` context) has closed
`TYPES` that are valid in the empty context, but an unconstrained `RECS` field.
This file moves validity and subtyping of closed types from `Δ` to `{}`.

The proof has two independent steps:

1. **Translation** (`SubClosed.TyOk.tr`, `SubClosed.Sub.tr`): substituting the
   context's closure `σ` (`_IDX x ↦ _DEF (TYPES[x])`) maps every judgment in
   `⟨T, R⟩` to the same judgment in `⟨[], R.map σ⟩`. This needs only
   `∀ d ∈ T, d.Closed ∧ TyOk {} d` (`TypeCtx.EmptyOk`), no condition on `RECS`.
2. **Dropping `RECS`** in a context with no `TYPES`: for validity, when the type has no
   free `REC` (`Ty.freeRec`); for subtyping, when the left type is not an abstract
   bottom (`none`, `nofunc`, `noexn`, `noextern`) — upward from such a heap type no
   `REC i` is reachable.

**The side condition in step 2 is needed.** With `RECS = [SUB [_DEF dS] (FUNC [] [])]`
for a struct type `dS`: `REC 0 <: func` (`rec-func`) and `REC 0 <: dS <: any`
(`rec-sub`), so `nofunc <: REC 0 <: any` and then `none <: nofunc` (`Heaptype_sub/none`),
while in `{}` `none <: nofunc` would need `nofunc <: any`. So `Sub.to_empty` cannot hold
for arbitrary closed, `{}`-valid `a` and `b` under unconstrained `RECS`. Runtime values
always have a non-bottom minimal type (`ref null bot` for `null`), which is what the
chain lemmas use.
-/

namespace Silmaril.Wasm.Validation

/-- The type fields of a runtime context: every defined type is closed and valid in
the empty context (what `Moduleinst_ok` gives for `TYPES`). -/
def TypeCtx.EmptyOk (Δ : TypeCtx) : Prop := ∀ d ∈ Δ.types, d.Closed ∧ TyOk {} d

/-- The `REC` indices free in a type (a group binds all of its `REC`s). -/
def Ty.freeRec : {k : TKind} → Ty k → List Nat
  | _, .nil => []
  | _, .cons a l => a.freeRec ++ l.freeRec
  | _, .idx _ => []
  | _, .recv i => [i]
  | _, .dt d => d.freeRec
  | _, .defn _ _ => []
  | _, .abs _ => []
  | _, .bot => []
  | _, .use u => u.freeRec
  | _, .ref _ h => h.freeRec
  | _, .num _ => []
  | _, .vec _ => []
  | _, .refv r => r.freeRec
  | _, .botv => []
  | _, .val t => t.freeRec
  | _, .pack _ => []
  | _, .field _ s => s.freeRec
  | _, .struct fs => fs.freeRec
  | _, .array f => f.freeRec
  | _, .func ps rs => ps.freeRec ++ rs.freeRec
  | _, .sub _ sups b => sups.freeRec ++ b.freeRec
  | _, .group _ => []

/-- No abstract bottom heap type at the top of a heap, reference or value type. -/
def Ty.NoBotAbs : {k : TKind} → Ty k → Prop
  | _, .abs a => a ≠ .none ∧ a ≠ .nofunc ∧ a ≠ .noexn ∧ a ≠ .noextern
  | _, .ref _ h => h.NoBotAbs
  | _, .refv r => r.NoBotAbs
  | _, _ => True

namespace SubClosed

theorem subst_ofList (σ : Subst) {k : TKind} :
    ∀ l : List (Ty k), (Ty.ofList l).subst σ = Ty.ofList (l.map (·.subst σ))
  | [] => rfl
  | a :: l => by simp [Ty.subst, subst_ofList σ l]

theorem subst_app (σ : Subst) {k : TKind} (a b : Ty (.list k)) :
    (a.app b).subst σ = (a.subst σ).app (b.subst σ) := by
  simp [Ty.app, subst_ofList, Ty.toList_subst]

theorem subst_all_nil : Subst.all [] = fun _ => none := by
  funext v; cases v <;> rfl

theorem clos_nil {k : TKind} (t : Ty k) : t.clos [] = t := by
  simp only [Ty.clos, closDefTypes, List.foldl_nil, List.map_nil, Ty.substAll, subst_all_nil]
  exact Ty.subst_none t

/-! ### Closedness of `{}`-valid types -/

mutual
theorem TyOk.freeIdx_nil : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k}, TyOk Δ t →
    Δ.types = [] → t.freeIdx = []
  | _, _, _, .idx h, hΔ => by simp [hΔ] at h
  | _, _, _, .recv _, _ => rfl
  | _, _, _, .dt h, hΔ => by have := TyOk.freeIdx_nil h hΔ; exact this
  | _, _, _, .defn h _, hΔ => by have := GroupOk2.freeIdx_nil h hΔ; exact this
  | _, _, _, .abs _, _ => rfl
  | _, _, _, .bot, _ => rfl
  | _, _, _, .use h, hΔ => by have := TyOk.freeIdx_nil h hΔ; exact this
  | _, _, _, .ref h, hΔ => by have := TyOk.freeIdx_nil h hΔ; exact this
  | _, _, _, .num _, _ => rfl
  | _, _, _, .vec _, _ => rfl
  | _, _, _, .refv h, hΔ => by have := TyOk.freeIdx_nil h hΔ; exact this
  | _, _, _, .botv, _ => rfl
  | _, _, _, .val h, hΔ => by have := TyOk.freeIdx_nil h hΔ; exact this
  | _, _, _, .pack _, _ => rfl
  | _, _, _, .field h, hΔ => by have := TyOk.freeIdx_nil h hΔ; exact this
  | _, _, _, .struct h, hΔ => by have := TyOk.freeIdx_nil h hΔ; exact this
  | _, _, _, .array h, hΔ => by have := TyOk.freeIdx_nil h hΔ; exact this
  | _, _, _, .func hp hr, hΔ => by
    simp only [Ty.freeIdx, TyOk.freeIdx_nil hp hΔ, TyOk.freeIdx_nil hr hΔ, List.append_nil]
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons ha hl, hΔ => by
    simp only [Ty.freeIdx, TyOk.freeIdx_nil ha hΔ, TyOk.freeIdx_nil hl hΔ, List.append_nil]

theorem SubOk2.freeIdx_nil : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2 Δ st i →
    Δ.types = [] → st.freeIdx = []
  | _, _, _, .noSuper hct, hΔ => by
    simp only [Ty.freeIdx, TyOk.freeIdx_nil hct hΔ, List.append_nil]
  | _, _, _, .oneSuper hu _ _ hct _, hΔ => by
    simp only [Ty.freeIdx, TyOk.freeIdx_nil hu hΔ, TyOk.freeIdx_nil hct hΔ, List.append_nil]

theorem GroupOk2.freeIdx_nil : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2 Δ g i →
    Δ.types = [] → g.freeIdx = []
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons h hs, hΔ => by
    have h1 := SubOk2.freeIdx_nil h hΔ
    have h2 := GroupOk2.freeIdx_nil hs hΔ
    simp only [Ty.freeIdx] at h2 ⊢
    simp only [h1, h2, List.append_nil]
end

theorem closed_of_empty {k : TKind} {t : Ty k} (h : TyOk {} t) : t.Closed :=
  TyOk.freeIdx_nil h rfl

/-! ### Step 1: translation along the closure substitution -/

/-- The closure substitution of a type list. -/
abbrev σT (T : List DefType) : Subst := TypeCtx.closSubst { types := T }

/-- The translated context: no `TYPES`, closed `RECS`. -/
def trCtx (T : List DefType) (Δ : TypeCtx) : TypeCtx :=
  { types := [], recs := Δ.recs.map (·.subst (σT T)) }

theorem σT_recv (T : List DefType) (i : Nat) : σT T (.recv i) = none := rfl

theorem σT_minusRecs (T : List DefType) : (σT T).minusRecs = σT T :=
  Subst.minusRecs_eq (σT_recv T)

theorem σT_idx {T : List DefType} {x : Nat} {d : DefType} (h : T[x]? = some d) :
    (Ty.idx x).subst (σT T) = .dt d := by
  have := TypeCtx.subst_idx ({ types := T } : TypeCtx) x
  simp only [h, Option.map_some, Option.getD_some] at this
  exact this

theorem unroll_σT (T : List DefType) (d : DefType) :
    unrolldt (d.subst (σT T)) = (unrolldt d).map (·.subst (σT T)) :=
  unrolldt_subst _ (σT_recv T) (TypeCtx.closSubst_recFree _) d

theorem expand_σT (T : List DefType) {d : DefType} {ct : CCompType} (h : Expand d ct) :
    Expand (d.subst (σT T)) (ct.subst (σT T)) := by
  cases h with
  | mk hu => exact .mk (by rw [unroll_σT, hu]; rfl)

theorem closed_σT {T : List DefType} {k : TKind} {t : Ty k} (h : t.Closed) :
    t.subst (σT T) = t :=
  Ty.subst_closed t _ (σT_recv T) h

theorem before_σT (T : List DefType) {u : CTypeUse} {i : Nat} (h : before u i = true) :
    before (u.subst (σT T)) i = true := by
  cases u with
  | idx x =>
    have e := TypeCtx.closSubst_idx ({ types := T } : TypeCtx) x
    show before ((σT T (.idx x)).getD (.idx x)) i = true
    rw [show σT T (.idx x) = _ from e]
    cases T[x]? <;> rfl
  | recv j => exact h
  | dt d => rfl

theorem subst_ne_bot {σ : Subst} {h : CHeapType} (hb : h ≠ .bot) : h.subst σ ≠ .bot := by
  cases h with
  | bot => exact absurd rfl hb
  | abs a => simp [Ty.subst]
  | use u => simp [Ty.subst]

section Tr

variable {T : List DefType}

theorem unrollUse_tr (hT : ∀ d ∈ T, d.Closed ∧ TyOk {} d) {Δ : TypeCtx} (hΔ : Δ.types = T)
    {u : CTypeUse} {st : CSubType} (h : Δ.unrollUse u = some st) :
    (trCtx T Δ).unrollUse (u.subst (σT T)) = some (st.subst (σT T)) := by
  cases u with
  | dt d =>
    show unrolldt (d.subst (σT T)) = _
    simp only [TypeCtx.unrollUse] at h
    rw [unroll_σT, h]; rfl
  | idx x =>
    simp only [TypeCtx.unrollUse, hΔ] at h
    cases hx : T[x]? with
    | none => rw [hx] at h; simp at h
    | some d =>
      rw [hx] at h
      replace h : unrolldt d = some st := h
      rw [σT_idx hx]
      show unrolldt d = _
      have hcl : d.subst (σT T) = d := closed_σT (hT d (List.mem_of_getElem? hx)).1
      have e := unroll_σT T d
      rw [hcl, h] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [h, ← e]
  | recv j =>
    show (Δ.recs.map (·.subst (σT T)))[j]? = _
    simp only [TypeCtx.unrollUse] at h
    simp [List.getElem?_map, h]

mutual

theorem TyOk.tr (hT : ∀ d ∈ T, d.Closed ∧ TyOk {} d) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k},
    TyOk Δ t → Δ.types = T → TyOk (trCtx T Δ) (t.subst (σT T))
  | _, _, _, @TyOk.idx _ x d h, hΔ => by
    have hd : T[x]? = some d := hΔ ▸ h
    rw [σT_idx hd]
    exact .dt (TyOk.def_congr (Δ₁ := {}) (Δ₂ := trCtx T _) rfl (hT d (List.mem_of_getElem? hd)).2)
  | _, _, _, @TyOk.recv Δ i st h, _ =>
    .recv (st := st.subst (σT T)) (by simp [trCtx, List.getElem?_map, h])
  | _, _, _, .dt h, hΔ => .dt (TyOk.tr hT h hΔ)
  | _, _, _, @TyOk.defn Δ subs i h hi, hΔ => by
    have hg := GroupOk2.tr hT h hΔ
    show TyOk _ (Ty.defn (Ty.group (subs.subst (σT T).minusRecs)) i)
    rw [σT_minusRecs]
    refine .defn ?_ (by rwa [Ty.length_subst])
    have e : trCtx T (Δ.withRecs subs.toList) =
        (trCtx T Δ).withRecs (subs.subst (σT T)).toList := by
      simp [trCtx, TypeCtx.withRecs, Ty.toList_subst]
    rw [e] at hg
    exact hg
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, hΔ => .use (TyOk.tr hT h hΔ)
  | _, _, _, .ref h, hΔ => .ref (TyOk.tr hT h hΔ)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, hΔ => .refv (TyOk.tr hT h hΔ)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, hΔ => .val (TyOk.tr hT h hΔ)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, hΔ => .field (TyOk.tr hT h hΔ)
  | _, _, _, .struct h, hΔ => .struct (TyOk.tr hT h hΔ)
  | _, _, _, .array h, hΔ => .array (TyOk.tr hT h hΔ)
  | _, _, _, .func hp hr, hΔ => .func (TyOk.tr hT hp hΔ) (TyOk.tr hT hr hΔ)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, hΔ => .cons (TyOk.tr hT ha hΔ) (TyOk.tr hT hl hΔ)

theorem SubOk2.tr (hT : ∀ d ∈ T, d.Closed ∧ TyOk {} d) : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat},
    SubOk2 Δ st i → Δ.types = T → SubOk2 (trCtx T Δ) (st.subst (σT T)) i
  | _, _, _, .noSuper hct, hΔ => .noSuper (TyOk.tr hT hct hΔ)
  | _, _, _, .oneSuper hu hb hunroll hct hsub, hΔ =>
    .oneSuper (TyOk.tr hT hu hΔ) (before_σT T hb) (unrollUse_tr hT hΔ hunroll)
      (TyOk.tr hT hct hΔ) (Sub.tr hT hsub hΔ)

theorem GroupOk2.tr (hT : ∀ d ∈ T, d.Closed ∧ TyOk {} d) : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat},
    GroupOk2 Δ g i → Δ.types = T → GroupOk2 (trCtx T Δ) (.group (g.subs.subst (σT T))) i
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons h hs, hΔ => .cons (SubOk2.tr hT h hΔ) (GroupOk2.tr hT hs hΔ)

theorem Sub.tr (hT : ∀ d ∈ T, d.Closed ∧ TyOk {} d) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k},
    Sub Δ a b → Δ.types = T → Sub (trCtx T Δ) (a.subst (σT T)) (b.subst (σT T))
  | _, _, _, _, .heapRefl, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ =>
    .heapTrans (TyOk.tr hT hok hΔ) (Sub.tr hT h₁ hΔ) (Sub.tr hT h₂ hΔ)
  | _, _, _, _, .eqAny, _ => .eqAny
  | _, _, _, _, .i31Eq, _ => .i31Eq
  | _, _, _, _, .structEq, _ => .structEq
  | _, _, _, _, .arrayEq, _ => .arrayEq
  | _, _, _, _, .defStruct h, _ => .defStruct (expand_σT T h)
  | _, _, _, _, .defArray h, _ => .defArray (expand_σT T h)
  | _, _, _, _, .defFunc h, _ => .defFunc (expand_σT T h)
  | _, _, _, _, .defDef h, hΔ => .defDef (Sub.tr hT h hΔ)
  | _, _, _, _, @Sub.idxL _ x d _ hx hs, hΔ => by
    have hd : T[x]? = some d := hΔ ▸ hx
    have hcl : d.subst (σT T) = d := closed_σT (hT d (List.mem_of_getElem? hd)).1
    have h1 := Sub.tr hT hs hΔ
    show Sub _ (Ty.use ((Ty.idx x).subst (σT T))) _
    rw [σT_idx hd]
    have e : (Ty.use (Ty.dt d)).subst (σT T) = Ty.use (Ty.dt d) := by
      simp only [Ty.subst, hcl]
    rw [e] at h1
    exact h1
  | _, _, _, _, @Sub.idxR _ x d _ hx hs, hΔ => by
    have hd : T[x]? = some d := hΔ ▸ hx
    have hcl : d.subst (σT T) = d := closed_σT (hT d (List.mem_of_getElem? hd)).1
    have h1 := Sub.tr hT hs hΔ
    show Sub _ _ (Ty.use ((Ty.idx x).subst (σT T)))
    rw [σT_idx hd]
    have e : (Ty.use (Ty.dt d)).subst (σT T) = Ty.use (Ty.dt d) := by
      simp only [Ty.subst, hcl]
    rw [e] at h1
    exact h1
  | _, _, _, _, @Sub.recStruct _ i fin sups fs h, _ =>
    .recStruct (fin := fin) (sups := sups.subst (σT T)) (fs := fs.subst (σT T))
      (by simp [trCtx, List.getElem?_map, h, Ty.subst])
  | _, _, _, _, @Sub.recArray _ i fin sups f h, _ =>
    .recArray (fin := fin) (sups := sups.subst (σT T)) (f := f.subst (σT T))
      (by simp [trCtx, List.getElem?_map, h, Ty.subst])
  | _, _, _, _, @Sub.recFunc _ i fin sups ps rs h, _ =>
    .recFunc (fin := fin) (sups := sups.subst (σT T)) (ps := ps.subst (σT T))
      (rs := rs.subst (σT T)) (by simp [trCtx, List.getElem?_map, h, Ty.subst])
  | _, _, _, _, @Sub.recSub _ i j fin sups ct u h hj, _ =>
    .recSub (fin := fin) (sups := sups.subst (σT T)) (ct := ct.subst (σT T))
      (by simp [trCtx, List.getElem?_map, h, Ty.subst])
      (by rw [Ty.toList_subst, List.getElem?_map, hj]; rfl)
  | _, _, _, _, .none hs hb, hΔ => .none (Sub.tr hT hs hΔ) (subst_ne_bot hb)
  | _, _, _, _, .nofunc hs hb, hΔ => .nofunc (Sub.tr hT hs hΔ) (subst_ne_bot hb)
  | _, _, _, _, .noexn hs hb, hΔ => .noexn (Sub.tr hT hs hΔ) (subst_ne_bot hb)
  | _, _, _, _, .noextern hs hb, hΔ => .noextern (Sub.tr hT hs hΔ) (subst_ne_bot hb)
  | _, _, _, _, .bot, _ => .bot
  | _, _, _, _, .refNonNull h, hΔ => .refNonNull (Sub.tr hT h hΔ)
  | _, _, _, _, .refNull h, hΔ => .refNull (Sub.tr hT h hΔ)
  | _, _, _, _, .num, _ => .num
  | _, _, _, _, .vec, _ => .vec
  | _, _, _, _, .refv h, hΔ => .refv (Sub.tr hT h hΔ)
  | _, _, _, _, .botv, _ => .botv
  | _, _, _, _, .val h, hΔ => .val (Sub.tr hT h hΔ)
  | _, _, _, _, .pack, _ => .pack
  | _, _, _, _, .fieldConst h, hΔ => .fieldConst (Sub.tr hT h hΔ)
  | _, _, _, _, .fieldVar h₁ h₂, hΔ => .fieldVar (Sub.tr hT h₁ hΔ) (Sub.tr hT h₂ hΔ)
  | _, _, _, _, @Sub.struct _ fs₁ extra fs₂ h, hΔ => by
    have e : (Ty.struct (fs₁.app extra)).subst (σT T) =
        Ty.struct ((fs₁.subst (σT T)).app (extra.subst (σT T))) := by
      simp only [Ty.subst, subst_app]
    rw [e]
    exact .struct (Sub.tr hT h hΔ)
  | _, _, _, _, .array h, hΔ => .array (Sub.tr hT h hΔ)
  | _, _, _, _, .func hp hr, hΔ => .func (Sub.tr hT hp hΔ) (Sub.tr hT hr hΔ)
  | _, _, _, _, @Sub.defRefl _ d₁ d₂ h, hΔ => .defRefl (by
    have hc : closDefTypes T = T := closDefTypes_closed (fun d hd => (hT d hd).1)
    rw [hΔ] at h
    simp only [Ty.clos, Ty.substAll, hc] at h
    show Ty.clos [] (d₁.subst (σT T)) = Ty.clos [] (d₂.subst (σT T))
    rw [clos_nil, clos_nil]
    exact h)
  | _, _, _, _, .defSuper hu hj hs, hΔ =>
    .defSuper (by rw [unroll_σT, hu]; rfl) (by rw [Ty.toList_subst, List.getElem?_map, hj]; rfl)
      (Sub.tr hT hs hΔ)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons h hl, hΔ => .cons (Sub.tr hT h hΔ) (Sub.tr hT hl hΔ)

end

end Tr

/-! ### Step 2: dropping `RECS` in a context without `TYPES` -/

theorem TyOk.dropRecs : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k},
    TyOk Δ t → t.freeRec = [] → TyOk { Δ with recs := [] } t
  | _, _, _, .idx h, _ => .idx h
  | _, _, _, .recv _, hr => by simp [Ty.freeRec] at hr
  | _, _, _, .dt h, hr => .dt (TyOk.dropRecs h hr)
  | _, _, _, .defn h hi, _ => .defn h hi
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, hr => .use (TyOk.dropRecs h hr)
  | _, _, _, .ref h, hr => .ref (TyOk.dropRecs h hr)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, hr => .refv (TyOk.dropRecs h hr)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, hr => .val (TyOk.dropRecs h hr)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, hr => .field (TyOk.dropRecs h hr)
  | _, _, _, .struct h, hr => .struct (TyOk.dropRecs h hr)
  | _, _, _, .array h, hr => .array (TyOk.dropRecs h hr)
  | _, _, _, .func hp hr', hr => by
    simp only [Ty.freeRec, List.append_eq_nil_iff] at hr
    exact .func (TyOk.dropRecs hp hr.1) (TyOk.dropRecs hr' hr.2)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, hr => by
    simp only [Ty.freeRec, List.append_eq_nil_iff] at hr
    exact .cons (TyOk.dropRecs ha hr.1) (TyOk.dropRecs hl hr.2)

/-- Heap and defined types from which no `REC` is reachable upward. -/
def Good : {k : TKind} → Ty k → Prop
  | _, .abs a => a ≠ .none ∧ a ≠ .nofunc ∧ a ≠ .noexn ∧ a ≠ .noextern
  | _, .use (.dt d) => TyOk {} d
  | _, .defn g i => TyOk {} (Ty.defn g i)
  | _, _ => False

theorem good_def {d : DefType} : Good d ↔ TyOk {} d := by
  cases d; exact Iff.rfl

theorem good_heap_ok {h : CHeapType} (hg : Good h) : TyOk {} h := by
  match h, hg with
  | .abs a, _ => exact .abs a
  | .use (.dt d), hg => exact .use (.dt hg)

theorem good_use_of_ok {u : CTypeUse} (h : TyOk {} (Ty.use u)) : Good (Ty.use u) := by
  cases h with
  | use h =>
    cases h with
    | idx h => simp at h
    | recv h => simp at h
    | dt h => exact h

theorem Sub.drop : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k},
    Sub Δ a b → Δ.types = [] → Good a → Good b ∧ Sub {} a b
  | _, _, _, _, .heapRefl, _, ha => ⟨ha, .heapRefl⟩
  | _, _, _, _, .heapTrans _ h₁ h₂, hΔ, ha =>
    have ⟨hm, s₁⟩ := Sub.drop h₁ hΔ ha
    have ⟨hb, s₂⟩ := Sub.drop h₂ hΔ hm
    ⟨hb, .heapTrans (good_heap_ok hm) s₁ s₂⟩
  | _, _, _, _, .eqAny, _, _ => ⟨by simp [Good], .eqAny⟩
  | _, _, _, _, .i31Eq, _, _ => ⟨by simp [Good], .i31Eq⟩
  | _, _, _, _, .structEq, _, _ => ⟨by simp [Good], .structEq⟩
  | _, _, _, _, .arrayEq, _, _ => ⟨by simp [Good], .arrayEq⟩
  | _, _, _, _, .defStruct h, _, _ => ⟨by simp [Good], .defStruct h⟩
  | _, _, _, _, .defArray h, _, _ => ⟨by simp [Good], .defArray h⟩
  | _, _, _, _, .defFunc h, _, _ => ⟨by simp [Good], .defFunc h⟩
  | _, _, _, _, .defDef h, hΔ, ha =>
    have ⟨hb, s⟩ := Sub.drop h hΔ (good_def.2 ha)
    ⟨good_def.1 hb, .defDef s⟩
  | _, _, _, _, .idxL hx _, hΔ, _ => by rw [hΔ] at hx; simp at hx
  | _, _, _, _, .idxR hx _, hΔ, _ => by rw [hΔ] at hx; simp at hx
  | _, _, _, _, .recStruct _, _, ha => by simp [Good] at ha
  | _, _, _, _, .recArray _, _, ha => by simp [Good] at ha
  | _, _, _, _, .recFunc _, _, ha => by simp [Good] at ha
  | _, _, _, _, .recSub _ _, _, ha => by simp [Good] at ha
  | _, _, _, _, .none _ _, _, ha => by simp [Good] at ha
  | _, _, _, _, .nofunc _ _, _, ha => by simp [Good] at ha
  | _, _, _, _, .noexn _ _, _, ha => by simp [Good] at ha
  | _, _, _, _, .noextern _ _, _, ha => by simp [Good] at ha
  | _, _, _, _, .bot, _, ha => by simp [Good] at ha
  | _, _, _, _, .refNonNull _, _, ha => by simp [Good] at ha
  | _, _, _, _, .refNull _, _, ha => by simp [Good] at ha
  | _, _, _, _, .num, _, ha => by simp [Good] at ha
  | _, _, _, _, .vec, _, ha => by simp [Good] at ha
  | _, _, _, _, .refv _, _, ha => by simp [Good] at ha
  | _, _, _, _, .botv, _, ha => by simp [Good] at ha
  | _, _, _, _, .val _, _, ha => by simp [Good] at ha
  | _, _, _, _, .pack, _, ha => by simp [Good] at ha
  | _, _, _, _, .fieldConst _, _, ha => by simp [Good] at ha
  | _, _, _, _, .fieldVar _ _, _, ha => by simp [Good] at ha
  | _, _, _, _, .struct _, _, ha => by simp [Good] at ha
  | _, _, _, _, .array _, _, ha => by simp [Good] at ha
  | _, _, _, _, .func _ _, _, ha => by simp [Good] at ha
  | _, _, _, _, @Sub.defRefl _ d₁ d₂ h, hΔ, ha => by
    rw [hΔ, clos_nil, clos_nil] at h
    subst h
    exact ⟨ha, Sub.refl _ (k := .def) trivial _⟩
  | _, _, _, _, .defSuper hu hj hs, hΔ, ha =>
    have hok := TyOk.unroll_super (good_def.1 ha) hu (List.mem_of_getElem? hj)
    have ⟨hb, s⟩ := Sub.drop hs hΔ (good_use_of_ok hok)
    ⟨good_def.2 hb, .defSuper hu hj s⟩
  | _, _, _, _, .nil, _, ha => by simp [Good] at ha
  | _, _, _, _, .cons _ _, _, ha => by simp [Good] at ha

theorem ok_empty : TypeCtx.Ok {} := by
  intro d hd; simp at hd

/-- Heap subtyping in a context without `TYPES`, from a closed non-bottom heap type. -/
theorem Sub.drop_heap {Δ : TypeCtx} (hΔ : Δ.types = []) {a b : CHeapType} (h : Sub Δ a b)
    (ha : TyOk {} a) (hna : a.NoBotAbs) : Sub {} a b := by
  cases a with
  | bot => exact .bot
  | abs x => exact (Sub.drop h hΔ hna).2
  | use u => exact (Sub.drop h hΔ (good_use_of_ok ha)).2

end SubClosed

open SubClosed

/-! ### Main results -/

/-- (1) Validity of a closed, `REC`-free type in a runtime context carries over to `{}`. -/
theorem TyOk.to_empty {Δ : TypeCtx} (hΔ : Δ.EmptyOk) {k : TKind} {t : Ty k} (h : TyOk Δ t)
    (hc : t.Closed) (hr : t.freeRec = []) : TyOk {} t := by
  have h1 := TyOk.tr hΔ h rfl
  rw [closed_σT hc] at h1
  exact TyOk.dropRecs h1 hr

/-- (2, generic form) With an empty `RECS`, subtyping between closed types carries over
to `{}` at every sort. -/
theorem Sub.to_empty_of_recs_nil {Δ : TypeCtx} (hΔ : Δ.EmptyOk) (hr : Δ.recs = [])
    {k : TKind} {a b : Ty k} (h : Sub Δ a b) (ha : a.Closed) (hb : b.Closed) : Sub {} a b := by
  have h1 := Sub.tr hΔ h rfl
  rw [closed_σT ha, closed_σT hb] at h1
  have e : trCtx Δ.types Δ = {} := by simp [trCtx, hr]
  rwa [e] at h1

/-- (2) Heap subtyping from a non-bottom `{}`-valid heap type carries over to `{}`
(for arbitrary `RECS`; see the module doc for why `NoBotAbs` is needed). -/
theorem Sub.to_empty_heap {Δ : TypeCtx} (hΔ : Δ.EmptyOk) {a b : CHeapType} (h : Sub Δ a b)
    (ha : TyOk {} a) (hb : TyOk {} b) (hna : a.NoBotAbs) : Sub {} a b := by
  have h1 := Sub.tr hΔ h rfl
  rw [closed_σT (closed_of_empty ha), closed_σT (closed_of_empty hb)] at h1
  exact Sub.drop_heap rfl h1 ha hna

theorem Sub.to_empty_ref {Δ : TypeCtx} (hΔ : Δ.EmptyOk) {a b : CRefType} (h : Sub Δ a b)
    (ha : TyOk {} a) (hb : TyOk {} b) (hna : a.NoBotAbs) : Sub {} a b := by
  cases ha with
  | ref ha =>
    cases hb with
    | ref hb =>
      cases h with
      | refNonNull h => exact .refNonNull (Sub.to_empty_heap hΔ h ha hb hna)
      | refNull h => exact .refNull (Sub.to_empty_heap hΔ h ha hb hna)

theorem Sub.to_empty_val {Δ : TypeCtx} (hΔ : Δ.EmptyOk) {a b : CValType} (h : Sub Δ a b)
    (ha : TyOk {} a) (hb : TyOk {} b) (hna : a.NoBotAbs) : Sub {} a b := by
  cases h with
  | num => exact .num
  | vec => exact .vec
  | botv => exact .botv
  | refv h =>
    cases ha with
    | refv ha =>
      cases hb with
      | refv hb => exact .refv (Sub.to_empty_ref hΔ h ha hb hna)

/-! ### Chains of subtypings (the shape of `ValTo`) -/

namespace SubClosed

/-- Chains at reference sort in a context without `TYPES`. -/
theorem chain_ref {Δ : TypeCtx} (hΔ : Δ.types = []) {a b : CRefType}
    (h : Relation.ReflTransGen (Sub Δ) a b) (ha : TyOk {} a) (hb : TyOk {} b)
    (hna : a.NoBotAbs) : Sub {} a b := by
  cases ha with
  | @ref _ n h₀ hh₀ =>
    cases h₀ with
    | bot =>
      -- nullability is monotone along the chain
      have key : ∀ c, Relation.ReflTransGen (Sub Δ) (Ty.ref n .bot) c →
          ∃ n' h', c = Ty.ref n' h' ∧ (n' = false → n = false) := by
        intro c hc
        induction hc with
        | refl => exact ⟨n, _, rfl, id⟩
        | tail _ hs ih =>
          obtain ⟨n', h', rfl, hn⟩ := ih
          cases hs with
          | refNonNull _ => exact ⟨false, _, rfl, hn⟩
          | refNull _ => exact ⟨true, _, rfl, by simp⟩
      obtain ⟨n', h', rfl, hn⟩ := key _ h
      cases n' with
      | false => rw [hn rfl]; exact .refNonNull .bot
      | true => exact .refNull .bot
    | abs x =>
      have key : ∀ c, Relation.ReflTransGen (Sub Δ) (Ty.ref n (.abs x)) c →
          ∃ n' h', c = Ty.ref n' h' ∧ Good h' ∧ Sub {} (Ty.ref n (.abs x)) c := by
        intro c hc
        induction hc with
        | refl => exact ⟨n, _, rfl, hna, Sub.refl _ (k := .ref) trivial _⟩
        | tail _ hs ih =>
          obtain ⟨n', h', rfl, hg, s⟩ := ih
          cases hs with
          | refNonNull hs =>
            have ⟨hg', s'⟩ := Sub.drop hs hΔ hg
            exact ⟨false, _, rfl, hg', Sub.trans ok_empty (.ref (good_heap_ok hg)) s (.refNonNull s')⟩
          | refNull hs =>
            have ⟨hg', s'⟩ := Sub.drop hs hΔ hg
            exact ⟨true, _, rfl, hg', Sub.trans ok_empty (.ref (good_heap_ok hg)) s (.refNull s')⟩
      obtain ⟨_, _, rfl, _, s⟩ := key _ h
      exact s
    | use u =>
      have hg := good_use_of_ok hh₀
      have key : ∀ c, Relation.ReflTransGen (Sub Δ) (Ty.ref n (.use u)) c →
          ∃ n' h', c = Ty.ref n' h' ∧ Good h' ∧ Sub {} (Ty.ref n (.use u)) c := by
        intro c hc
        induction hc with
        | refl => exact ⟨n, _, rfl, hg, Sub.refl _ (k := .ref) trivial _⟩
        | tail _ hs ih =>
          obtain ⟨n', h', rfl, hg, s⟩ := ih
          cases hs with
          | refNonNull hs =>
            have ⟨hg', s'⟩ := Sub.drop hs hΔ hg
            exact ⟨false, _, rfl, hg', Sub.trans ok_empty (.ref (good_heap_ok hg)) s (.refNonNull s')⟩
          | refNull hs =>
            have ⟨hg', s'⟩ := Sub.drop hs hΔ hg
            exact ⟨true, _, rfl, hg', Sub.trans ok_empty (.ref (good_heap_ok hg)) s (.refNull s')⟩
      obtain ⟨_, _, rfl, _, s⟩ := key _ h
      exact s

theorem chain_val {Δ : TypeCtx} (hΔ : Δ.types = []) {a b : CValType}
    (h : Relation.ReflTransGen (Sub Δ) a b) (ha : TyOk {} a) (hb : TyOk {} b)
    (hna : a.NoBotAbs) : Sub {} a b := by
  cases ha with
  | botv => exact .botv
  | num t =>
    have : ∀ c, Relation.ReflTransGen (Sub Δ) (Ty.num t) c → c = .num t := by
      intro c hc
      induction hc with
      | refl => rfl
      | tail _ hs ih => subst ih; cases hs; rfl
    rw [this _ h]; exact .num
  | vec t =>
    have : ∀ c, Relation.ReflTransGen (Sub Δ) (Ty.vec t) c → c = .vec t := by
      intro c hc
      induction hc with
      | refl => rfl
      | tail _ hs ih => subst ih; cases hs; rfl
    rw [this _ h]; exact .vec
  | @refv _ r hr =>
    have : ∀ c, Relation.ReflTransGen (Sub Δ) (Ty.refv r) c →
        ∃ r', c = .refv r' ∧ Relation.ReflTransGen (Sub Δ) r r' := by
      intro c hc
      induction hc with
      | refl => exact ⟨r, rfl, .refl⟩
      | tail _ hs ih =>
        obtain ⟨r', rfl, hc⟩ := ih
        cases hs with
        | refv hs => exact ⟨_, rfl, hc.tail hs⟩
    obtain ⟨r', rfl, hc⟩ := this _ h
    cases hb with
    | refv hb => exact .refv (chain_ref hΔ hc hr hb hna)

end SubClosed

/-- (3) A chain of subtypings in a runtime context between `{}`-valid value types,
starting at a non-bottom type, is a single subtyping in `{}`. Middle types are
arbitrary. -/
theorem Sub.chain_to_empty_val {Δ : TypeCtx} (hΔ : Δ.EmptyOk) {a b : CValType}
    (h : Relation.ReflTransGen (Sub Δ) a b) (ha : TyOk {} a) (hb : TyOk {} b)
    (hna : a.NoBotAbs) : Sub {} a b := by
  have h1 : Relation.ReflTransGen (Sub (trCtx Δ.types Δ)) (a.subst (σT Δ.types))
      (b.subst (σT Δ.types)) :=
    h.lift (fun t : CValType => t.subst (σT Δ.types)) (fun _ _ hs => Sub.tr hΔ hs rfl)
  rw [closed_σT (closed_of_empty ha), closed_σT (closed_of_empty hb)] at h1
  exact chain_val rfl h1 ha hb hna

theorem Sub.chain_to_empty_ref {Δ : TypeCtx} (hΔ : Δ.EmptyOk) {a b : CRefType}
    (h : Relation.ReflTransGen (Sub Δ) a b) (ha : TyOk {} a) (hb : TyOk {} b)
    (hna : a.NoBotAbs) : Sub {} a b := by
  have h1 : Relation.ReflTransGen (Sub (trCtx Δ.types Δ)) (a.subst (σT Δ.types))
      (b.subst (σT Δ.types)) :=
    h.lift (fun t : CRefType => t.subst (σT Δ.types)) (fun _ _ hs => Sub.tr hΔ hs rfl)
  rw [closed_σT (closed_of_empty ha), closed_σT (closed_of_empty hb)] at h1
  exact chain_ref rfl h1 ha hb hna

end Silmaril.Wasm.Validation
