module

public import Silmaril.Wasm.Execution.Core.Soundness.RedexTyping

@[expose] public section

/-! # Runtime reference typing: weakening, inversion, heap-type hierarchy

Helper infrastructure for the reference/aggregate soundness units.

* `TyOk.wkTypes`/`Sub.wkTypes`: judgments in a context with no `TYPES` (such as
  the runtime context `{}`) hold in any context with the same `RECS`.
* `RefOk` inversions (non-null, extern).
* The heap-type hierarchy is respected by subtyping (`HeapUp.sub`): the heap
  types above a reference's principal type stay in its hierarchy (`any`, `func`,
  `exn`, `extern`), used to rule out ill-shaped references in progress and
  preservation.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Weakening from an empty `TYPES` field -/

theorem Subst.all_nil : Subst.all [] = fun _ => none := by
  funext v; cases v <;> rfl

theorem Ty.clos_nil {k : TKind} (t : Ty k) : t.clos [] = t := by
  simp only [Ty.clos, closDefTypes, List.foldl_nil, List.map_nil, Ty.substAll, Subst.all_nil]
  exact Ty.subst_none t

theorem TypeCtx.unrollUse_wk {Δ : TypeCtx} {u : CTypeUse} (hu : TyOk Δ u) (hΔ : Δ.types = [])
    (T : List DefType) : ({ Δ with types := T } : TypeCtx).unrollUse u = Δ.unrollUse u := by
  cases u with
  | idx x => cases hu with | idx h => simp [hΔ] at h
  | recv i => rfl
  | dt d => rfl

mutual

theorem TyOk.wkTypes (T : List DefType) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k},
    TyOk Δ t → Δ.types = [] → TyOk { Δ with types := T } t
  | _, _, _, .idx h, hΔ => by simp [hΔ] at h
  | _, _, _, .recv h, _ => .recv h
  | _, _, _, .dt h, hΔ => .dt (TyOk.wkTypes T h hΔ)
  | _, _, _, .defn h hi, hΔ => .defn (GroupOk2.wkTypes T h hΔ) hi
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, hΔ => .use (TyOk.wkTypes T h hΔ)
  | _, _, _, .ref h, hΔ => .ref (TyOk.wkTypes T h hΔ)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, hΔ => .refv (TyOk.wkTypes T h hΔ)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, hΔ => .val (TyOk.wkTypes T h hΔ)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, hΔ => .field (TyOk.wkTypes T h hΔ)
  | _, _, _, .struct h, hΔ => .struct (TyOk.wkTypes T h hΔ)
  | _, _, _, .array h, hΔ => .array (TyOk.wkTypes T h hΔ)
  | _, _, _, .func hp hr, hΔ => .func (TyOk.wkTypes T hp hΔ) (TyOk.wkTypes T hr hΔ)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, hΔ => .cons (TyOk.wkTypes T ha hΔ) (TyOk.wkTypes T hl hΔ)

theorem SubOk2.wkTypes (T : List DefType) : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat},
    SubOk2 Δ st i → Δ.types = [] → SubOk2 { Δ with types := T } st i
  | _, _, _, .noSuper hct, hΔ => .noSuper (TyOk.wkTypes T hct hΔ)
  | _, _, _, .oneSuper hu hb hunroll hct hsub, hΔ =>
    .oneSuper (TyOk.wkTypes T hu hΔ) hb (by rw [TypeCtx.unrollUse_wk hu hΔ]; exact hunroll)
      (TyOk.wkTypes T hct hΔ) (Sub.wkTypes T hsub hΔ)

theorem GroupOk2.wkTypes (T : List DefType) : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat},
    GroupOk2 Δ g i → Δ.types = [] → GroupOk2 { Δ with types := T } g i
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons h hs, hΔ => .cons (SubOk2.wkTypes T h hΔ) (GroupOk2.wkTypes T hs hΔ)

theorem Sub.wkTypes (T : List DefType) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k},
    Sub Δ a b → Δ.types = [] → Sub { Δ with types := T } a b
  | _, _, _, _, .heapRefl, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ =>
    .heapTrans (TyOk.wkTypes T hok hΔ) (Sub.wkTypes T h₁ hΔ) (Sub.wkTypes T h₂ hΔ)
  | _, _, _, _, .eqAny, _ => .eqAny
  | _, _, _, _, .i31Eq, _ => .i31Eq
  | _, _, _, _, .structEq, _ => .structEq
  | _, _, _, _, .arrayEq, _ => .arrayEq
  | _, _, _, _, .defStruct h, _ => .defStruct h
  | _, _, _, _, .defArray h, _ => .defArray h
  | _, _, _, _, .defFunc h, _ => .defFunc h
  | _, _, _, _, .defDef h, hΔ => .defDef (Sub.wkTypes T h hΔ)
  | _, _, _, _, .idxL hx _, hΔ => by simp [hΔ] at hx
  | _, _, _, _, .idxR hx _, hΔ => by simp [hΔ] at hx
  | _, _, _, _, .recStruct h, _ => .recStruct h
  | _, _, _, _, .recArray h, _ => .recArray h
  | _, _, _, _, .recFunc h, _ => .recFunc h
  | _, _, _, _, .recSub h hj, _ => .recSub h hj
  | _, _, _, _, .none hs hb, hΔ => .none (Sub.wkTypes T hs hΔ) hb
  | _, _, _, _, .nofunc hs hb, hΔ => .nofunc (Sub.wkTypes T hs hΔ) hb
  | _, _, _, _, .noexn hs hb, hΔ => .noexn (Sub.wkTypes T hs hΔ) hb
  | _, _, _, _, .noextern hs hb, hΔ => .noextern (Sub.wkTypes T hs hΔ) hb
  | _, _, _, _, .bot, _ => .bot
  | _, _, _, _, .refNonNull h, hΔ => .refNonNull (Sub.wkTypes T h hΔ)
  | _, _, _, _, .refNull h, hΔ => .refNull (Sub.wkTypes T h hΔ)
  | _, _, _, _, .num, _ => .num
  | _, _, _, _, .vec, _ => .vec
  | _, _, _, _, .refv h, hΔ => .refv (Sub.wkTypes T h hΔ)
  | _, _, _, _, .botv, _ => .botv
  | _, _, _, _, .val h, hΔ => .val (Sub.wkTypes T h hΔ)
  | _, _, _, _, .pack, _ => .pack
  | _, _, _, _, .fieldConst h, hΔ => .fieldConst (Sub.wkTypes T h hΔ)
  | _, _, _, _, .fieldVar h₁ h₂, hΔ => .fieldVar (Sub.wkTypes T h₁ hΔ) (Sub.wkTypes T h₂ hΔ)
  | _, _, _, _, .struct h, hΔ => .struct (Sub.wkTypes T h hΔ)
  | _, _, _, _, .array h, hΔ => .array (Sub.wkTypes T h hΔ)
  | _, _, _, _, .func hp hr, hΔ => .func (Sub.wkTypes T hp hΔ) (Sub.wkTypes T hr hΔ)
  | _, _, _, _, .defRefl h, hΔ => .defRefl (by rw [hΔ, Ty.clos_nil, Ty.clos_nil] at h; rw [h])
  | _, _, _, _, .defSuper h hj hs, hΔ => .defSuper h hj (Sub.wkTypes T hs hΔ)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons h hl, hΔ => .cons (Sub.wkTypes T h hΔ) (Sub.wkTypes T hl hΔ)

end

/-! ## Weakening from an empty `RECS` field -/

theorem TyOk.wkRecs (R : List CSubType) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k},
    TyOk Δ t → Δ.recs = [] → TyOk { Δ with recs := R } t
  | _, _, _, .idx h, _ => .idx h
  | _, _, _, .recv h, hΔ => by simp [hΔ] at h
  | _, _, _, .dt h, hΔ => .dt (TyOk.wkRecs R h hΔ)
  | _, _, _, .defn h hi, _ => .defn h hi
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, hΔ => .use (TyOk.wkRecs R h hΔ)
  | _, _, _, .ref h, hΔ => .ref (TyOk.wkRecs R h hΔ)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, hΔ => .refv (TyOk.wkRecs R h hΔ)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, hΔ => .val (TyOk.wkRecs R h hΔ)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, hΔ => .field (TyOk.wkRecs R h hΔ)
  | _, _, _, .struct h, hΔ => .struct (TyOk.wkRecs R h hΔ)
  | _, _, _, .array h, hΔ => .array (TyOk.wkRecs R h hΔ)
  | _, _, _, .func hp hr, hΔ => .func (TyOk.wkRecs R hp hΔ) (TyOk.wkRecs R hr hΔ)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, hΔ => .cons (TyOk.wkRecs R ha hΔ) (TyOk.wkRecs R hl hΔ)

theorem Sub.wkRecs (R : List CSubType) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k},
    Sub Δ a b → Δ.recs = [] → Sub { Δ with recs := R } a b
  | _, _, _, _, .heapRefl, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ =>
    .heapTrans (TyOk.wkRecs R hok hΔ) (Sub.wkRecs R h₁ hΔ) (Sub.wkRecs R h₂ hΔ)
  | _, _, _, _, .eqAny, _ => .eqAny
  | _, _, _, _, .i31Eq, _ => .i31Eq
  | _, _, _, _, .structEq, _ => .structEq
  | _, _, _, _, .arrayEq, _ => .arrayEq
  | _, _, _, _, .defStruct h, _ => .defStruct h
  | _, _, _, _, .defArray h, _ => .defArray h
  | _, _, _, _, .defFunc h, _ => .defFunc h
  | _, _, _, _, .defDef h, hΔ => .defDef (Sub.wkRecs R h hΔ)
  | _, _, _, _, .idxL hx h, hΔ => .idxL hx (Sub.wkRecs R h hΔ)
  | _, _, _, _, .idxR hx h, hΔ => .idxR hx (Sub.wkRecs R h hΔ)
  | _, _, _, _, .recStruct h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recArray h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recFunc h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recSub h _, hΔ => by simp [hΔ] at h
  | _, _, _, _, .none hs hb, hΔ => .none (Sub.wkRecs R hs hΔ) hb
  | _, _, _, _, .nofunc hs hb, hΔ => .nofunc (Sub.wkRecs R hs hΔ) hb
  | _, _, _, _, .noexn hs hb, hΔ => .noexn (Sub.wkRecs R hs hΔ) hb
  | _, _, _, _, .noextern hs hb, hΔ => .noextern (Sub.wkRecs R hs hΔ) hb
  | _, _, _, _, .bot, _ => .bot
  | _, _, _, _, .refNonNull h, hΔ => .refNonNull (Sub.wkRecs R h hΔ)
  | _, _, _, _, .refNull h, hΔ => .refNull (Sub.wkRecs R h hΔ)
  | _, _, _, _, .num, _ => .num
  | _, _, _, _, .vec, _ => .vec
  | _, _, _, _, .refv h, hΔ => .refv (Sub.wkRecs R h hΔ)
  | _, _, _, _, .botv, _ => .botv
  | _, _, _, _, .val h, hΔ => .val (Sub.wkRecs R h hΔ)
  | _, _, _, _, .pack, _ => .pack
  | _, _, _, _, .fieldConst h, hΔ => .fieldConst (Sub.wkRecs R h hΔ)
  | _, _, _, _, .fieldVar h₁ h₂, hΔ => .fieldVar (Sub.wkRecs R h₁ hΔ) (Sub.wkRecs R h₂ hΔ)
  | _, _, _, _, .struct h, hΔ => .struct (Sub.wkRecs R h hΔ)
  | _, _, _, _, .array h, hΔ => .array (Sub.wkRecs R h hΔ)
  | _, _, _, _, .func hp hr, hΔ => .func (Sub.wkRecs R hp hΔ) (Sub.wkRecs R hr hΔ)
  | _, _, _, _, .defRefl h, _ => .defRefl h
  | _, _, _, _, .defSuper h hj hs, hΔ => .defSuper h hj (Sub.wkRecs R hs hΔ)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons h hl, hΔ => .cons (Sub.wkRecs R h hΔ) (Sub.wkRecs R hl hΔ)

/-- Runtime (closed-context) validity holds in every context. -/
theorem TyOk.ofEmpty {k : TKind} {t : Ty k} (h : TyOk {} t) (Δ : TypeCtx) : TyOk Δ t := by
  have h1 := TyOk.wkRecs Δ.recs (TyOk.wkTypes Δ.types h rfl) rfl
  cases Δ; exact h1

/-- Runtime (closed-context) subtyping holds in every context. -/
theorem Sub.of_empty {k : TKind} {a b : Ty k} (h : Sub {} a b) (Δ : TypeCtx) : Sub Δ a b := by
  have h1 := Sub.wkRecs Δ.recs (Sub.wkTypes Δ.types h rfl) rfl
  cases Δ; exact h1

theorem ResultSub.of_empty {a b : List CValType} (h : ResultSub {} a b) (Δ : TypeCtx) :
    ResultSub Δ a b := h.imp fun _ _ h => Sub.of_empty h Δ

/-! ## Composite kinds of defined types -/

/-- The abstract heap type directly above a composite type. -/
def compKind : CCompType → AbsHeapType
  | .struct _ => .struct
  | .array _ => .array
  | .func _ _ => .func

theorem compKind_subst (σ : Subst) (ct : CCompType) : compKind (ct.subst σ) = compKind ct := by
  cases ct <;> rfl

/-- The kind of a defined type (`struct`, `array` or `func`), if it unrolls. -/
def defKind (d : DefType) : Option AbsHeapType := (unrolldt d).map fun st => compKind st.body

theorem expand_defKind {d : DefType} {ct : CCompType} (h : Expand d ct) :
    defKind d = some (compKind ct) := by
  cases h with | mk h => simp [Core.defKind, h, Ty.body]

theorem defKind_subst (σ : Subst) (hσ : ∀ i, σ (.recv i) = none)
    (hσu : ∀ x u, σ (.idx x) = some u → u.RecFree) (d : DefType) :
    defKind (d.subst σ) = defKind d := by
  simp only [defKind, unrolldt_subst σ hσ hσu, Option.map_map]
  cases unrolldt d with
  | none => rfl
  | some st =>
    cases st with
    | sub fin sups b => simp [Ty.subst, Ty.body, compKind_subst]

theorem defKind_clos (T : List DefType) (d : DefType) : defKind (d.clos T) = defKind d :=
  defKind_subst _ (fun _ => rfl)
    (fun x u h => by
      simp only [Subst.all, List.getElem?_map] at h
      cases hx : (closDefTypes T)[x]? with
      | none => simp [hx] at h
      | some e => simp [hx] at h; subst h; exact Ty.recFree_dt e) d

/-- The kind of a type use; `REC` uses have none (they never occur above a
runtime type). -/
def useKind (Δ : TypeCtx) : CTypeUse → Option AbsHeapType
  | .dt d => defKind d
  | .idx x => Δ.types[x]? >>= defKind
  | .recv _ => none

/-- `absUp c a`: `a` is an abstract heap type above the class `c`. -/
def absUp : AbsHeapType → AbsHeapType → Bool
  | .i31, .i31 | .i31, .eq | .i31, .any => true
  | .struct, .struct | .struct, .eq | .struct, .any => true
  | .array, .array | .array, .eq | .array, .any => true
  | .eq, .eq | .eq, .any => true
  | .any, .any => true
  | .func, .func => true
  | .exn, .exn => true
  | .extern, .extern => true
  | _, _ => false

/-- The heap types above class `c`. -/
def HeapUp (Δ : TypeCtx) (c : AbsHeapType) : CHeapType → Prop
  | .abs a => absUp c a = true
  | .use u => useKind Δ u = some c
  | .bot => False

/-- `HeapUp` with validity of a defined type at the source (needed to follow
declared supertypes). -/
def HeapUpV (Δ : TypeCtx) (c : AbsHeapType) (h : CHeapType) : Prop :=
  HeapUp Δ c h ∧ ∀ d, h = .use (.dt d) → TyOk Δ d

theorem HeapUpV.of_ok {Δ : TypeCtx} {c : AbsHeapType} {h : CHeapType} (hu : HeapUp Δ c h)
    (hok : TyOk Δ h) : HeapUpV Δ c h := by
  refine ⟨hu, fun d hd => ?_⟩
  subst hd
  cases hok with | use h => cases h with | dt h => exact h

/-- A valid defined type's declared supertypes are valid and of the same kind. -/
theorem TyOk.super_kind {Δ : TypeCtx} {d : DefType} (hd : TyOk Δ d) {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} (hu : unrolldt d = some (.sub fin sups ct))
    {j : Nat} {u : CTypeUse} (hj : sups.toList[j]? = some u) :
    useKind Δ u = some (compKind ct) ∧ TyOk Δ (.use u) := by
  cases hd with
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
        obtain ⟨-, rfl, rfl⟩ := hu
        cases hso with
        | noSuper =>
          have := (List.getElem?_eq_some_iff.1 hj).1
          exact absurd this (Nat.not_lt_zero _)
        | @oneSuper _ _ u0 _ _ sups' ct' hu0 hb hunroll hct hsub =>
          simp only [Ty.subst, Ty.toList_cons, Ty.toList_nil] at hj
          have hj0 : j = 0 := by
            rcases j with _ | j
            · rfl
            · simp at hj
          subst hj0
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          have hk : compKind ct0 = compKind ct' := by cases hsub <;> rfl
          rw [compKind_subst, hk]
          cases u0 with
          | idx x =>
            cases hu0 with
            | idx hx =>
              try simp only [Ty.subst, Option.getD_none]
              refine ⟨?_, .use (.idx hx)⟩
              obtain ⟨e, hx'⟩ : ∃ e, Δ.types[x]? = some e := ⟨_, hx⟩
              have h2 : (Δ.withRecs subs.toList).unrollUse (.idx x) = unrolldt e := by
                simp [TypeCtx.unrollUse, TypeCtx.withRecs, hx']
              rw [h2] at hunroll
              simp only [useKind, hx']
              show defKind e = _
              simp [defKind, hunroll, Ty.body]
          | recv j' =>
            cases hu0 with
            | recv hr =>
              have hj' : j' < subs.length := by
                have := (List.getElem?_eq_some_iff.1 hr).1
                simpa [TypeCtx.withRecs, Ty.length] using this
              simp only [Ty.subst, hj', ite_true, Option.getD_some]
              refine ⟨?_, .use (.dt (.defn hg hj'))⟩
              simp only [TypeCtx.unrollUse, TypeCtx.withRecs] at hunroll
              simp only [useKind, defKind, unrolldt, unrollrt, Ty.subs, Ty.toList_subst,
                List.getElem?_map, hunroll, Option.map_some, Ty.subst, Ty.body, compKind_subst]
          | dt e =>
            rw [Ty.recFree_dt e _ (fun _ => rfl)]
            cases hu0 with
            | dt he =>
              refine ⟨?_, .use (.dt (TyOk.def_congr (Δ₁ := Δ.withRecs subs.toList) (Δ₂ := Δ) rfl he))⟩
              simp only [TypeCtx.unrollUse] at hunroll
              simp [useKind, defKind, hunroll, Ty.body]

/-- Motive of `Sub.up`, by sort. -/
def UpMotive (Δ : TypeCtx) : (k : TKind) → Ty k → Ty k → Prop
  | .heap, a, b => ∀ c, HeapUpV Δ c a → HeapUp Δ c b
  | .def, a, b => TyOk Δ a → ∀ c, defKind a = some c → defKind b = some c
  | _, _, _ => True

/-- **The hierarchy is respected by subtyping.** In a context whose defined
types are valid, the heap types above a valid member of class `c` stay in `c`'s
upward set. -/
theorem Sub.up {Δ : TypeCtx} (hT : ∀ (x : Nat) (d : DefType), Δ.types[x]? = some d → TyOk Δ d) :
    ∀ {k : TKind} {a b : Ty k}, Sub Δ a b → UpMotive Δ k a b
  | _, _, _, .heapRefl => by intro c hc; exact hc.1
  | _, _, _, .heapTrans hok h₁ h₂ => by
    have ih₁ := Sub.up hT h₁
    have ih₂ := Sub.up hT h₂
    dsimp only [UpMotive] at ih₁ ih₂ ⊢
    intro c hc
    exact ih₂ c (HeapUpV.of_ok (ih₁ c hc) hok)
  | _, _, _, .eqAny => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUp, absUp]
  | _, _, _, .i31Eq => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUp, absUp]
  | _, _, _, .structEq => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUp, absUp]
  | _, _, _, .arrayEq => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUp, absUp]
  | _, _, _, .defStruct h => by
    intro c hc; have := hc.1
    simp only [HeapUp, useKind, expand_defKind h, compKind, Option.some.injEq] at this
    subst this; rfl
  | _, _, _, .defArray h => by
    intro c hc; have := hc.1
    simp only [HeapUp, useKind, expand_defKind h, compKind, Option.some.injEq] at this
    subst this; rfl
  | _, _, _, .defFunc h => by
    intro c hc; have := hc.1
    simp only [HeapUp, useKind, expand_defKind h, compKind, Option.some.injEq] at this
    subst this; rfl
  | _, _, _, .defDef h => by
    have ih := Sub.up hT h
    dsimp only [UpMotive] at ih ⊢
    intro c hc
    exact ih (hc.2 _ rfl) c hc.1
  | _, _, _, .idxL hx hs => by
    have ih := Sub.up hT hs
    dsimp only [UpMotive] at ih ⊢
    intro c hc
    refine ih c ⟨?_, fun d hd => ?_⟩
    · have := hc.1
      simp only [HeapUp, useKind, hx] at this ⊢
      exact this
    · cases hd; exact hT _ _ hx
  | _, _, _, .idxR hx hs => by
    have ih := Sub.up hT hs
    dsimp only [UpMotive] at ih ⊢
    intro c hc
    have := ih c hc
    simp only [HeapUp, useKind, hx] at this ⊢
    exact this
  | _, _, _, .recStruct _ => by intro c hc; exact absurd hc.1 (by simp [HeapUp, useKind])
  | _, _, _, .recArray _ => by intro c hc; exact absurd hc.1 (by simp [HeapUp, useKind])
  | _, _, _, .recFunc _ => by intro c hc; exact absurd hc.1 (by simp [HeapUp, useKind])
  | _, _, _, .recSub _ _ => by intro c hc; exact absurd hc.1 (by simp [HeapUp, useKind])
  | _, _, _, .none _ _ => by intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUp, absUp]
  | _, _, _, .nofunc _ _ => by intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUp, absUp]
  | _, _, _, .noexn _ _ => by intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUp, absUp]
  | _, _, _, .noextern _ _ => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUp, absUp]
  | _, _, _, .bot => by intro c hc; exact absurd hc.1 (by simp [HeapUp])
  | _, _, _, .refNonNull _ => trivial
  | _, _, _, .refNull _ => trivial
  | _, _, _, .num => trivial
  | _, _, _, .vec => trivial
  | _, _, _, .refv _ => trivial
  | _, _, _, .botv => trivial
  | _, _, _, .val _ => trivial
  | _, _, _, .pack => trivial
  | _, _, _, .fieldConst _ => trivial
  | _, _, _, .fieldVar _ _ => trivial
  | _, _, _, .struct _ => trivial
  | _, _, _, .array _ => trivial
  | _, _, _, .func _ _ => trivial
  | _, _, _, .defRefl h => by
    intro _ c hc
    rw [← defKind_clos Δ.types, ← h, defKind_clos]
    exact hc
  | _, _, _, @Sub.defSuper _ _ _ _ _ ct _ _ hu hj hs => by
    intro hd c hc
    obtain ⟨hk, hok⟩ := TyOk.super_kind hd hu hj
    have ih := Sub.up hT hs
    dsimp only [UpMotive] at ih
    have hc' : compKind ct = c := by simpa [defKind, hu, Ty.body] using hc
    have := ih _ (HeapUpV.of_ok hk hok)
    rw [← hc']
    simpa [HeapUp, useKind] using this
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial

/-- Heap types below a leaf class (`i31`, `exn`, `extern`). -/
def HeapDown (a : AbsHeapType) : CHeapType → Prop
  | .abs z => z = a ∨ z = .none ∨ z = .nofunc ∨ z = .noexn ∨ z = .noextern
  | .bot => True
  | .use _ => False

def IsLeaf (a : AbsHeapType) : Prop := a = .i31 ∨ a = .exn ∨ a = .extern

def DownMotive : (k : TKind) → Ty k → Ty k → Prop
  | .heap, x, y => ∀ a, IsLeaf a → HeapDown a y → HeapDown a x
  | _, _, _ => True

/-- Only bottom types lie below a leaf abstract heap type. -/
theorem Sub.down {Δ : TypeCtx} : ∀ {k : TKind} {x y : Ty k}, Sub Δ x y → DownMotive k x y
  | _, _, _, .heapRefl => by intro a _ h; exact h
  | _, _, _, .heapTrans _ h₁ h₂ => by
    have ih₁ := Sub.down h₁
    have ih₂ := Sub.down h₂
    dsimp only [DownMotive] at ih₁ ih₂ ⊢
    intro a ha h
    exact ih₁ a ha (ih₂ a ha h)
  | _, _, _, .eqAny => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .i31Eq => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .structEq => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .arrayEq => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .defStruct _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .defArray _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .defFunc _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .defDef _ => by intro a _ h; simp [HeapDown] at h
  | _, _, _, .idxL _ hs => by
    have ih := Sub.down hs
    dsimp only [DownMotive] at ih ⊢
    intro a ha h
    exact absurd (ih a ha h) (by simp [HeapDown])
  | _, _, _, .idxR _ _ => by intro a _ h; simp [HeapDown] at h
  | _, _, _, .recStruct _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .recArray _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .recFunc _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .recSub _ _ => by intro a _ h; simp [HeapDown] at h
  | _, _, _, .none _ _ => by intro a _ _; simp [HeapDown]
  | _, _, _, .nofunc _ _ => by intro a _ _; simp [HeapDown]
  | _, _, _, .noexn _ _ => by intro a _ _; simp [HeapDown]
  | _, _, _, .noextern _ _ => by intro a _ _; simp [HeapDown]
  | _, _, _, .bot => by intro a _ _; simp [HeapDown]
  | _, _, _, .refNonNull _ => trivial
  | _, _, _, .refNull _ => trivial
  | _, _, _, .num => trivial
  | _, _, _, .vec => trivial
  | _, _, _, .refv _ => trivial
  | _, _, _, .botv => trivial
  | _, _, _, .val _ => trivial
  | _, _, _, .pack => trivial
  | _, _, _, .fieldConst _ => trivial
  | _, _, _, .fieldVar _ _ => trivial
  | _, _, _, .struct _ => trivial
  | _, _, _, .array _ => trivial
  | _, _, _, .func _ _ => trivial
  | _, _, _, .defRefl _ => trivial
  | _, _, _, .defSuper _ _ _ => trivial
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial

theorem Sub.down_leaf {Δ : TypeCtx} {h : CHeapType} {a : AbsHeapType} (hs : Sub Δ h (.abs a))
    (ha : IsLeaf a) : HeapDown a h := by
  have := Sub.down hs
  dsimp only [DownMotive] at this
  exact this a ha (by simp [HeapDown])

/-! ## Inversion of subtyping on reference and value types -/

theorem Sub.ref_inv {Δ : TypeCtx} {n₁ n₂ : Bool} {h₁ h₂ : CHeapType}
    (h : Sub Δ (Ty.ref n₁ h₁) (Ty.ref n₂ h₂)) : Sub Δ h₁ h₂ ∧ (n₁ = true → n₂ = true) := by
  cases h with
  | refNonNull h => exact ⟨h, by simp⟩
  | refNull h => exact ⟨h, by simp⟩

theorem Sub.refv_inv {Δ : TypeCtx} {t : CValType} {r : CRefType} (h : Sub Δ t (.refv r)) :
    t = .botv ∨ ∃ r', t = .refv r' ∧ Sub Δ r' r := by
  cases h with
  | botv => exact .inl rfl
  | refv h => exact .inr ⟨_, rfl, h⟩

/-! ## Principal types of references -/

/-- The non-subsumption rules of `Ref_ok`. -/
inductive RefBase (s : Store H) : Ref → CRefType → Prop where
  | null : RefBase s .null (.ref true .bot)
  | i31 (b : BitVec 31) : RefBase s (.i31 b) (.ref false (.abs .i31))
  | struct {a : Nat} {si : StructInst} (h : s.structs[a]? = some si) :
      RefBase s (.struct a) (.ref false (.defHeap si.type))
  | array {a : Nat} {ai : ArrayInst} (h : s.arrays[a]? = some ai) :
      RefBase s (.array a) (.ref false (.defHeap ai.type))
  | func {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
      RefBase s (.func a) (.ref false (.defHeap fi.type))
  | exn {a : Nat} {e : ExnInst} (h : s.exns[a]? = some e) :
      RefBase s (.exn a) (.ref false (.abs .exn))
  | host (a : Nat) : RefBase s (.host a) (.ref false (.abs .any))
  | extern {r : Ref} (h : RefOk s r (.ref false (.abs .any))) (hn : r ≠ .null) :
      RefBase s (.extern r) (.ref false (.abs .extern))

theorem RefBase.refOk {s : Store H} {r : Ref} {rt : CRefType} (h : RefBase s r rt) :
    RefOk s r rt := by
  cases h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h => exact .func h
  | exn h => exact .exn h
  | host a => exact .host a
  | extern h hn => exact .extern h hn

theorem RefBase.nonnull {s : Store H} {r : Ref} {n : Bool} {h : CHeapType}
    (hb : RefBase s r (.ref n h)) (hr : r ≠ .null) : n = false := by
  cases hb <;> first | rfl | exact absurd rfl hr

theorem RefBase.null_iff {s : Store H} {r : Ref} {n : Bool} {h : CHeapType}
    (hb : RefBase s r (.ref n h)) : r = .null ↔ h = .bot := by
  cases hb <;> simp [Ty.defHeap]

theorem RefOk.principalRT {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∃ rt₀, RefBase s r rt₀ ∧ (rt₀ = rt ∨ (Sub {} rt₀ rt ∧ TyOk {} rt)) := by
  induction h with
  | null => exact ⟨_, .null, .inl rfl⟩
  | i31 b => exact ⟨_, .i31 b, .inl rfl⟩
  | struct h => exact ⟨_, .struct h, .inl rfl⟩
  | array h => exact ⟨_, .array h, .inl rfl⟩
  | func h => exact ⟨_, .func h, .inl rfl⟩
  | exn h => exact ⟨_, .exn h, .inl rfl⟩
  | host a => exact ⟨_, .host a, .inl rfl⟩
  | extern h hn => exact ⟨_, .extern h hn, .inl rfl⟩
  | sub _ hok hs ih =>
    obtain ⟨rt₀, hb, h0⟩ := ih
    rcases h0 with rfl | ⟨hs0, hok0⟩
    · exact ⟨_, hb, .inr ⟨hs, hok⟩⟩
    · exact ⟨_, hb, .inr ⟨Sub.trans_ref hok0 hs0 hs, hok⟩⟩

theorem RefOk.principalBase {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∃ rt₀, RefBase s r rt₀ ∧ (rt₀ = rt ∨ (Sub {} rt₀ rt ∧ TyOk {} rt)) :=
  h.principalRT

/-- A reference typed below `rt'` (in any context) has a principal type below `rt'`. -/
theorem RefOk.principal_sub {s : Store H} {r : Ref} {rt rt' : CRefType} {Δ : TypeCtx}
    (h : RefOk s r rt) (hs : Sub Δ rt rt') : ∃ rt₀, RefBase s r rt₀ ∧ Sub Δ rt₀ rt' := by
  obtain ⟨rt₀, hb, h0⟩ := h.principalRT
  rcases h0 with rfl | ⟨hs0, hok0⟩
  · exact ⟨_, hb, hs⟩
  · exact ⟨_, hb, Sub.trans_ref (TyOk.ofEmpty hok0 Δ) (Sub.of_empty hs0 Δ) hs⟩

/-- A value typed below a reference type is a reference with a principal type
below it. -/
theorem ValOk.ref_invRT {s : Store H} {v : Val} {t : CValType} {rt : CRefType} {Δ : TypeCtx}
    (hv : ValOk s v t) (hs : Sub Δ t (.refv rt)) :
    ∃ r rt₀, v = .ref r ∧ RefBase s r rt₀ ∧ Sub Δ rt₀ rt := by
  rcases Sub.refv_inv hs with rfl | ⟨r', rfl, hs'⟩
  · cases hv
  · cases hv with
    | ref h =>
      obtain ⟨rt₀, hb, h0⟩ := h.principal_sub hs'
      exact ⟨_, _, rfl, hb, h0⟩

theorem ValOk.i32_invRT {s : Store H} {v : Val} {t : CValType} {Δ : TypeCtx}
    (hv : ValOk s v t) (hs : Sub Δ t Ty.i32) : ∃ b, v = Val.i32 b := by
  cases hv with
  | num v =>
    obtain ⟨ty, b⟩ := v
    simp only [Ty.i32] at hs
    cases hs
    exact ⟨b, rfl⟩
  | vec b => cases hs
  | ref h => cases hs

theorem RefOk.nonnull_sub {s : Store H} {r : Ref} {n : Bool} {h : CHeapType}
    (hr : RefOk s r (.ref n h)) (hn : r ≠ .null) : RefOk s r (.ref false h) := by
  obtain ⟨rt₀, hb, h0⟩ := hr.principalRT
  rcases h0 with h0 | ⟨hs0, hok0⟩
  · subst h0; rw [hb.nonnull hn] at hb; exact hb.refOk
  · cases rt₀ with
    | ref n₀ h₀ =>
      have hn₀ := hb.nonnull hn; subst hn₀
      cases hok0 with
      | ref hh => exact .sub hb.refOk (.ref hh) (.refNonNull (Sub.ref_inv hs0).1)

end Silmaril.Wasm.Execution.Core
