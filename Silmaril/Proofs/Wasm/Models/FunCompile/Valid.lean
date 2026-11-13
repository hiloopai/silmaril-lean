module

public import Silmaril.Wasm.Models.FunLang.Defs
public import Silmaril.Wasm.Models.FunCompile.Defs
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Compiling FunLang: the compiled module validates

A typing derivation (`Silmaril.Wasm.Validation.InstrsOk`) of the code of every well-typed term,
by induction on the typing judgement (`ty_compile`): in a context whose locals `1 … n` are set
`anyref`s, the code of a term has type `[] → [anyref]`. Side conditions on concrete types
(subtyping, type validity) are discharged by silmaril's verified checkers (`Sub.check`,
`TyOk.check`, …) evaluated by `decide`.

* the combinators `seqP`, `consP`, `frameP`, `subP`, with `plain` instruction types and no
  initialised locals (a `local.set` is weakened by `subP`, as every local is set already);
* `Good C n`: the context has the module's types and its locals `1 … n` are set `anyref`s;
* `funcOk_main`: `Func_ok` of `main`, and `moduleValid`: `ModuleValid (moduleOf p)` for every
  well-typed program within the local-index limit.

The instruction-group lemmas are stated for any context with the module's types, so the FunRef
compiler reuses them.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCompile

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCompile
open Silmaril.Wasm.Models.FunLang (Tm Prog HasTy Arith Cmp)

/-- `anyref`, closed. -/
def anyC : CValType := .refv (.ref true (.abs .any))

/-! ## Combinators -/

theorem seqP {C : Context} {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
    (h₁ : InstrsOk C is₁ (.plain t₁ t₂)) (h₂ : InstrsOk C is₂ (.plain t₂ t₃)) :
    InstrsOk C (is₁ ++ is₂) (.plain t₁ t₃) :=
  InstrsOk.seq (xs₁ := []) (xs₂ := []) h₁ (fun _ hx => absurd hx List.not_mem_nil) h₂

theorem consP {C : Context} {i : Instr} {is : List Instr} {t₁ t₂ t₃ : List CValType}
    (hi : InstrOk C i (.plain t₁ t₂)) (h : InstrsOk C is (.plain t₂ t₃)) :
    InstrsOk C (i :: is) (.plain t₁ t₃) :=
  InstrsOk.cons (xs₁ := []) (xs₂ := []) hi (fun _ hx => absurd hx List.not_mem_nil) h

theorem frameP {C : Context} {is : List Instr} {ts t₁ t₂ : List CValType}
    (h : InstrsOk C is (.plain t₁ t₂)) (hok : ResultOk C.toTypeCtx ts) :
    InstrsOk C is (.plain (ts ++ t₁) (ts ++ t₂)) :=
  InstrsOk.frame h hok

/-- Subsumption to a `plain` type, by the checkers. -/
theorem subP {C : Context} {is : List Instr} {a b a' b' : List CValType} {xs : List Nat}
    (h : InstrsOk C is ⟨a, xs, b⟩) (h₁ : ResultSub.check C.toTypeCtx a' a = true)
    (h₂ : ResultSub.check C.toTypeCtx b b' = true) (h₃ : ResultOk.check C.toTypeCtx a' = true)
    (h₄ : ResultOk.check C.toTypeCtx b' = true) : InstrsOk C is (.plain a' b') :=
  InstrsOk.sub h ⟨ResultSub.check_sound h₁, ResultSub.check_sound h₂,
      fun _ hx => absurd hx List.not_mem_nil⟩
    ⟨ResultOk.check_sound h₃, ResultOk.check_sound h₄, fun _ hx => absurd hx List.not_mem_nil⟩

/-- Subsumption to a `plain` type, with explicit subtyping derivations. -/
theorem subR {C : Context} {is : List Instr} {a b a' b' : List CValType} {xs : List Nat}
    (h : InstrsOk C is ⟨a, xs, b⟩) (h₁ : ResultSub C.toTypeCtx a' a)
    (h₂ : ResultSub C.toTypeCtx b b') (h₃ : ResultOk.check C.toTypeCtx a' = true)
    (h₄ : ResultOk.check C.toTypeCtx b' = true) : InstrsOk C is (.plain a' b') :=
  InstrsOk.sub h ⟨h₁, h₂, fun _ hx => absurd hx List.not_mem_nil⟩
    ⟨ResultOk.check_sound h₃, ResultOk.check_sound h₄, fun _ hx => absurd hx List.not_mem_nil⟩

/-! ## Contexts -/

/-- The type context of the module. -/
def Δ₀ (ts : List DefType) : TypeCtx := ⟨ts, []⟩

/-- The context has the defined types `ts` and no recursion types. -/
def HasTypes (C : Context) (ts : List DefType) : Prop := C.toTypeCtx = Δ₀ ts

theorem HasTypes.types {C : Context} {ts : List DefType} (h : HasTypes C ts) : C.types = ts :=
  congrArg TypeCtx.types h

theorem HasTypes.withLabel {C : Context} {ts : List DefType} (h : HasTypes C ts)
    (l : List CValType) : HasTypes (C.withLabel l) ts := h

/-- A local index below `2^32`. -/
theorem lx_toNat {n : Nat} (h : n < 2 ^ 32) : (lx n).toNat = n := by
  simp [lx, Idx.toNat]; exact h

theorem fx_toNat {n : Nat} (h : n < 2 ^ 32) : (fx n).toNat = n := by
  simp [fx, Idx.toNat]; exact h

/-- The field types of `$box`, closed. -/
def boxFieldsC : Ty (.list .field) :=
  .cons (.field .const (.val anyC)) (.cons (.field .const (.val anyC)) .nil)

/-! ## Instruction groups, in a context with types `dBox :: ts` -/

section Groups

variable {C : Context} {ts : List DefType}

theorem ty_localGet {x : Nat} {t : CValType} (hx : C.locals[x]? = some ⟨.set, t⟩)
    (hlim : x < 2 ^ 32) : InstrsOk C [.localGet (lx x)] (.plain [] [t]) :=
  .instr (.variable (.localGet (by rw [lx_toNat hlim]; exact hx)))

theorem ty_localSet {x : Nat} (hΔ : HasTypes C ts) (hx : C.locals[x]? = some ⟨.set, anyC⟩)
    (hlim : x < 2 ^ 32) : InstrsOk C [.localSet (lx x)] (.plain [anyC] []) := by
  have h : InstrsOk C [.localSet (lx x)] ⟨[anyC], [(lx x).toNat], []⟩ :=
    .instr (.variable (.localSet (by rw [lx_toNat hlim]; exact hx)))
  exact subP h (by rw [hΔ]; rfl) (by rw [hΔ]; rfl) (by rw [hΔ]; rfl) (by rw [hΔ]; rfl)

theorem ty_const (k : BitVec 32) : InstrOk C (.intConst .i32 k) (.plain [] [.i32]) :=
  .numeric (.intConst .i32 k)

theorem ty_box (hΔ : HasTypes C ts) : InstrsOk C [.refI31] (.plain [.i32] [anyC]) :=
  subP (.instr (.reference .refI31)) (by rw [hΔ]; rfl) (by rw [hΔ]; rfl)
    (by rw [hΔ]; rfl) (by rw [hΔ]; rfl)

theorem ty_constBox (hΔ : HasTypes C ts) (k : BitVec 32) :
    InstrsOk C [.intConst .i32 k, .refI31] (.plain [] [anyC]) :=
  consP (ty_const k) (ty_box hΔ)

theorem ty_unbox (hΔ : HasTypes C ts) : InstrsOk C unbox (.plain [anyC] [.i32]) := by
  have hc : InstrOk C (.refCast i31Ref) (.plain [anyC] [.refT false (.abs .i31)]) :=
    .reference (.refCast (rt' := .ref true (.abs .any)) (TyOk.check_sound (by rw [hΔ]; rfl))
      (TyOk.check_sound (by rw [hΔ]; rfl)) (Sub.check_sound (by rw [hΔ]; rfl)))
  have hg : InstrsOk C [.i31Get .unsigned] (.plain [.refT false (.abs .i31)] [.i32]) :=
    subP (.instr (.reference (.i31Get .unsigned))) (by rw [hΔ]; rfl) (by rw [hΔ]; rfl)
      (by rw [hΔ]; rfl) (by rw [hΔ]; rfl)
  exact consP hc hg

theorem ty_castBox (hΔ : HasTypes C (dBox :: ts)) :
    InstrOk C (.refCast boxRef) (.plain [anyC] [.refT false (Ty.defHeap dBox)]) := by
  have hr : C.closeRef boxRef = .ref false (Ty.defHeap dBox) := by
    simp only [Context.closeRef, hΔ.types]; rfl
  have h := RefInstrOk.refCast (C := C) (rt := boxRef) (rt' := .ref true (.abs .any))
    (TyOk.check_sound (by rw [hΔ, hr]; rfl)) (TyOk.check_sound (by rw [hΔ]; rfl))
    (Sub.check_sound (by rw [hΔ, hr]; rfl))
  rw [hr] at h
  exact .reference h

theorem ty_getBox (hΔ : HasTypes C (dBox :: ts)) {i : Nat} (hi : i < 2) :
    InstrsOk C [.structGet none boxIdx (fx i)] (.plain [.refT false (Ty.defHeap dBox)] [anyC]) := by
  have hfi : (fx i).toNat = i := fx_toNat (by omega)
  have hd : C.type? boxIdx = some dBox := by simp [Context.type?, hΔ.types, boxIdx, Idx.toNat]
  have hft : boxFieldsC.toList[(fx i).toNat]? =
      some (.field .const (.val anyC)) := by
    rw [hfi]; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl
  have h := RefInstrOk.structGet (C := C) (sx := none) hd ⟨rfl⟩ hft rfl
  exact subR (.instr (.reference h)) (.cons (.refv (.refNull .heapRefl)) .nil)
    (.cons (.refv (.refNull .heapRefl)) .nil) (by rw [hΔ]; rfl) (by rw [hΔ]; rfl)

theorem ty_newBox (hΔ : HasTypes C (dBox :: ts)) :
    InstrsOk C [.structNew boxIdx] (.plain [anyC, anyC] [anyC]) := by
  have hd : C.type? boxIdx = some dBox := by simp [Context.type?, hΔ.types, boxIdx, Idx.toNat]
  have h := RefInstrOk.structNew (C := C) (fs := boxFieldsC) hd ⟨rfl⟩
  exact subP (.instr (.reference h)) (by rw [hΔ]; rfl) (by rw [hΔ]; rfl)
    (by rw [hΔ]; rfl) (by rw [hΔ]; rfl)

theorem ty_arith (hΔ : HasTypes C ts) (op : Arith) :
    InstrsOk C [.intBinOp .i32 (Arith.wasm op), .refI31] (.plain [.i32, .i32] [anyC]) :=
  consP (.numeric (.intBinOp .i32 _)) (ty_box hΔ)

theorem ty_cmp (hΔ : HasTypes C ts) (op : Cmp) :
    InstrsOk C [.intRelOp .i32 (Cmp.wasm op), .refI31] (.plain [.i32, .i32] [anyC]) :=
  consP (.numeric (.intRelOp .i32 _)) (ty_box hΔ)

/-- `if (result anyref)`. -/
theorem ty_if (hΔ : HasTypes C ts) {b₁ b₂ : List Instr}
    (h₁ : InstrsOk (C.withLabel [anyC]) b₁ (.plain [] [anyC]))
    (h₂ : InstrsOk (C.withLabel [anyC]) b₂ (.plain [] [anyC])) :
    InstrsOk C [.if_ (.value anyref) b₁ b₂] (.plain [.i32] [anyC]) :=
  .instr (.if_ (t₁ := []) (.value (TyOk.check_sound (by rw [hΔ]; rfl))) h₁ h₂)

/-- Frame one value below. -/
theorem frame1 (hΔ : HasTypes C ts) {is : List Instr} {a : CValType} {t₁ t₂ : List CValType}
    (h : InstrsOk C is (.plain t₁ t₂)) (ha : ResultOk.check (Δ₀ ts) [a] = true) :
    InstrsOk C is (.plain (a :: t₁) (a :: t₂)) :=
  frameP (ts := [a]) h (by rw [hΔ]; exact ResultOk.check_sound ha)

end Groups

/-! ## The code of every well-typed term -/

/-- The context has the module's types, and its locals `1 … n` are set `anyref`s (`n` below
`2^32`). -/
def Good (C : Context) (ts : List DefType) (n : Nat) : Prop :=
  HasTypes C (dBox :: ts) ∧ n < 2 ^ 32 ∧
    ∀ x, 1 ≤ x → x ≤ n → C.locals[x]? = some ⟨.set, anyC⟩

theorem Good.mono {C : Context} {ts : List DefType} {n m : Nat} (h : Good C ts n) (hm : m ≤ n) :
    Good C ts m :=
  ⟨h.1, by have := h.2.1; omega, fun x h₁ h₂ => h.2.2 x h₁ (by omega)⟩

theorem Good.withLabel {C : Context} {ts : List DefType} {n : Nat} (h : Good C ts n)
    (l : List CValType) : Good (C.withLabel l) ts n := h

theorem Good.local {C : Context} {ts : List DefType} {n x : Nat} (h : Good C ts n) (h₁ : 1 ≤ x)
    (h₂ : x ≤ n) : C.locals[x]? = some ⟨.set, anyC⟩ :=
  h.2.2 x h₁ h₂

theorem Good.lim {C : Context} {ts : List DefType} {n x : Nat} (h : Good C ts n) (hx : x ≤ n) :
    x < 2 ^ 32 :=
  lt_of_le_of_lt hx h.2.1

/-- Field `i` of the `$box` in local `x`. -/
theorem ty_getField {C : Context} {ts : List DefType} {n x i : Nat} (hg : Good C ts n)
    (h₁ : 1 ≤ x) (h₂ : x ≤ n) (hi : i < 2) : InstrsOk C (getField x i) (.plain [] [anyC]) :=
  consP (.variable (.localGet (by rw [lx_toNat (hg.lim h₂)]; exact hg.local h₁ h₂)))
    (consP (ty_castBox hg.1) (ty_getBox hg.1 hi))

theorem ok_anyC (ts : List DefType) : ResultOk.check (Δ₀ ts) [anyC] = true := rfl

theorem ok_i32 (ts : List DefType) : ResultOk.check (Δ₀ ts) [.i32] = true := rfl

theorem depth_le_left {d a b : Nat} : d + a ≤ d + max a b := Nat.add_le_add_left (le_max_left _ _) d

theorem depth_le_right {d a b : Nat} : d + b ≤ d + max a b :=
  Nat.add_le_add_left (le_max_right _ _) d

/-- The code of a `case` branch. -/
theorem ty_branch {C : Context} {ts : List DefType} {d : Nat} {t : Tm}
    (hg : Good C ts (d + 1)) (ht : InstrsOk C (compile (d + 1) t) (.plain [] [anyC])) :
    InstrsOk C (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) t)
      (.plain [] [anyC]) :=
  seqP (ty_getField hg (by omega) le_rfl (by omega))
    (seqP (ty_localSet hg.1 (hg.local (by omega) le_rfl) (hg.lim le_rfl)) ht)

/-- The code of `case`, from the code of its parts. -/
theorem ty_case {Γ : List FunLang.Ty} {σ τ : FunLang.Ty} {e l r : Tm}
    (ihe : ∀ {d : Nat} {C : Context} {ts : List DefType}, Γ.length = d → Good C ts (d + e.depth) →
      InstrsOk C (compile d e) (.plain [] [anyC]))
    (ihl : ∀ {d : Nat} {C : Context} {ts : List DefType}, (σ :: Γ).length = d →
      Good C ts (d + l.depth) →
      InstrsOk C (compile d l) (.plain [] [anyC]))
    (ihr : ∀ {d : Nat} {C : Context} {ts : List DefType}, (τ :: Γ).length = d →
      Good C ts (d + r.depth) →
      InstrsOk C (compile d r) (.plain [] [anyC])) {d : Nat} {C : Context} {ts : List DefType}
    (hd : Γ.length = d) (hg : Good C ts (d + (Tm.case e l r).depth)) :
    InstrsOk C (compile d (.case e l r)) (.plain [] [anyC]) := by
  have hdep : (Tm.case e l r).depth = max e.depth (max l.depth r.depth + 1) := rfl
  have hm : max l.depth r.depth + 1 ≤ max e.depth (max l.depth r.depth + 1) := le_max_right _ _
  have hml : l.depth ≤ max l.depth r.depth := le_max_left _ _
  have hmr : r.depth ≤ max l.depth r.depth := le_max_right _ _
  have hl : InstrsOk (C.withLabel [anyC])
      (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) l)
      (.plain [] [anyC]) := ty_branch (d := d) ((hg.mono (by omega)).withLabel [anyC])
    (ihl (d := d + 1) (by simp [hd]) ((hg.mono (by omega)).withLabel [anyC]))
  have hr : InstrsOk (C.withLabel [anyC])
      (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) r)
      (.plain [] [anyC]) := ty_branch (d := d) ((hg.mono (by omega)).withLabel [anyC])
    (ihr (d := d + 1) (by simp [hd]) ((hg.mono (by omega)).withLabel [anyC]))
  exact seqP (seqP (seqP (ihe hd (hg.mono depth_le_left))
    (seqP (ty_localSet hg.1 (hg.local (by omega) (by omega)) (hg.lim (by omega)))
      (ty_getField hg (by omega) (by omega) (by omega)))) (ty_unbox hg.1))
    (ty_if hg.1 hr hl)

/-- **The code of every well-typed term has type `[] → [anyref]`.** -/
theorem ty_compile {Γ : List FunLang.Ty} {e : Tm} {τ : FunLang.Ty} (h : HasTy Γ e τ) :
    ∀ {d : Nat} {C : Context} {ts : List DefType}, Γ.length = d → Good C ts (d + e.depth) →
      InstrsOk C (compile d e) (.plain [] [anyC]) := by
  induction h with
  | var hi =>
    intro d C ts hd hg
    have hlt : _ < d := hd ▸ (List.getElem?_eq_some_iff.1 hi).1
    exact ty_localGet (hg.local (by omega) (by omega)) (hg.lim (by omega))
  | int n => exact fun _ hg => ty_constBox hg.1 _
  | bool b => exact fun _ hg => ty_constBox hg.1 _
  | arith op _ _ iha ihb =>
    exact fun hd hg => seqP (seqP (seqP (seqP (iha hd (hg.mono depth_le_left)) (ty_unbox hg.1))
      (frame1 hg.1 (ihb hd (hg.mono depth_le_right)) (ok_i32 _))) (frame1 hg.1 (ty_unbox hg.1)
        (ok_i32 _))) (ty_arith hg.1 op)
  | cmp op _ _ iha ihb =>
    exact fun hd hg => seqP (seqP (seqP (seqP (iha hd (hg.mono depth_le_left)) (ty_unbox hg.1))
      (frame1 hg.1 (ihb hd (hg.mono depth_le_right)) (ok_i32 _))) (frame1 hg.1 (ty_unbox hg.1)
        (ok_i32 _))) (ty_cmp hg.1 op)
  | ite _ _ _ ihc iht ihe =>
    exact fun hd hg => seqP (seqP (ihc hd (hg.mono depth_le_left)) (ty_unbox hg.1))
      (ty_if hg.1 (iht hd ((hg.mono (le_trans depth_le_left depth_le_right)).withLabel _))
        (ihe hd ((hg.mono (le_trans depth_le_right depth_le_right)).withLabel _)))
  | @let_ Γ a b σ τ _ _ iha ihb =>
    intro d C ts hd hg
    have hdep : (Tm.let_ a b).depth = max a.depth (b.depth + 1) := rfl
    have hm : b.depth + 1 ≤ max a.depth (b.depth + 1) := le_max_right _ _
    have hb : Good C ts (d + 1 + b.depth) := hg.mono (by omega)
    exact seqP (iha hd (hg.mono depth_le_left))
      (seqP (ty_localSet hg.1 (hg.local (by omega) (by omega)) (hg.lim (by omega)))
        (ihb (by simp [hd]) hb))
  | pair _ _ iha ihb =>
    exact fun hd hg => seqP (seqP (iha hd (hg.mono depth_le_left))
      (frame1 hg.1 (ihb hd (hg.mono depth_le_right)) (ok_anyC _))) (ty_newBox hg.1)
  | fst _ ih =>
    exact fun hd hg => seqP (ih hd hg) (consP (ty_castBox hg.1) (ty_getBox hg.1 (by omega)))
  | snd _ ih =>
    exact fun hd hg => seqP (ih hd hg) (consP (ty_castBox hg.1) (ty_getBox hg.1 (by omega)))
  | @inl Γ e σ τ _ ih =>
    intro d C ts hd hg
    show InstrsOk C ([.intConst .i32 0, .refI31] ++ (compile d e ++ [.structNew boxIdx])) _
    exact seqP (ty_constBox hg.1 _) (seqP (frame1 hg.1 (ih hd hg) (ok_anyC _)) (ty_newBox hg.1))
  | @inr Γ e σ τ _ ih =>
    intro d C ts hd hg
    show InstrsOk C ([.intConst .i32 1, .refI31] ++ (compile d e ++ [.structNew boxIdx])) _
    exact seqP (ty_constBox hg.1 _) (seqP (frame1 hg.1 (ih hd hg) (ok_anyC _)) (ty_newBox hg.1))
  | case _ _ _ ihe ihl ihr => exact fun hd hg => ty_case ihe ihl ihr hd hg

/-! ## Functions and modules -/

/-- `anyref` locals are valid and set. -/
theorem localsOk {C : Context} {ts : List DefType} (hΔ : HasTypes C ts) (n : Nat) :
    List.Forall₂ (LocalOk C) (List.replicate n anyref) (List.replicate n ⟨.set, anyC⟩) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    have h : LocalOk C anyref ⟨.set, C.closeVal anyref⟩ :=
      .set (TyOk.check_sound (by rw [hΔ]; rfl)) (show Defaultable anyC by decide)
    exact .cons h ih

/-- The body context of a function with one `i32` parameter and result and `n` `anyref`
locals. -/
def bodyCtx (C : Context) (n : Nat) : Context :=
  C.funcBody [.i32] [.i32] (List.replicate n ⟨.set, anyC⟩)

theorem bodyCtx_good {C : Context} {ts : List DefType} (hΔ : HasTypes C (dBox :: ts)) {n : Nat}
    (hn : n < 2 ^ 32) : Good (bodyCtx C n) ts n := by
  refine ⟨hΔ, hn, fun x h₁ h₂ => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  simp [bodyCtx, Context.funcBody, show y < n by omega]

/-- The prologue `local.get 0; ref.i31; local.set 1`. -/
theorem ty_prologue {C : Context} {ts : List DefType} {n : Nat} (hg : Good (bodyCtx C n) ts n)
    (hn : 1 ≤ n) :
    InstrsOk (bodyCtx C n) [.localGet (lx 0), .refI31, .localSet (lx 1)] (.plain [] []) := by
  have h0 : (bodyCtx C n).locals[0]? = some ⟨.set, .i32⟩ := by simp [bodyCtx, Context.funcBody]
  exact consP (.variable (.localGet (by rw [lx_toNat (by decide)]; exact h0)))
    (seqP (ty_box hg.1) (ty_localSet hg.1 (hg.local le_rfl hn) (hg.lim hn)))

/-- **The body of `main` has type `[] → [i32]`.** -/
theorem ty_mainBody {C : Context} {ts : List DefType} (hΔ : HasTypes C (dBox :: ts)) {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) :
    ExprOk (bodyCtx C (p.body.depth + 1)) (mainBody p) [.i32] := by
  have hg : Good (bodyCtx C (p.body.depth + 1)) ts (p.body.depth + 1) :=
    bodyCtx_good hΔ (by unfold Prog.Fits at hfit; omega)
  have hc : InstrsOk (bodyCtx C (p.body.depth + 1)) (compile 1 p.body) (.plain [] [anyC]) :=
    ty_compile hp.1 rfl (hg.mono (by omega))
  exact seqP (seqP (ty_prologue hg (by omega)) hc) (ty_unbox hg.1)

/-- `Func_ok` of `main`. -/
theorem funcOk_main {C : Context} (hΔ : HasTypes C modTypes) {p : Prog} (hp : p.WellTyped)
    (hfit : p.Fits) : FuncOk C (funcOf p) dMain := by
  have hd : C.type? (funcOf p).type = some dMain := by
    simp [Context.type?, hΔ.types, funcOf, modTypes, Idx.toNat]
  exact .mk (ps := .cons .i32 .nil) (rs := .cons .i32 .nil) hd ⟨rfl⟩ (localsOk hΔ _)
    (ty_mainBody (ts := [dMain]) hΔ hp hfit)

/-- The context `C` of `Module_ok` for a compiled module. -/
def modCtx (p : Prog) : Context :=
  moduleCtx (moduleOf p) (moduleCtx' (moduleOf p) modTypes [] [dMain]) [] [] [] [] []

theorem modCtx_types (p : Prog) : HasTypes (modCtx p) modTypes := rfl

theorem typesOk : TypesOk {} recTypes modTypes :=
  typesCheck?_sound (fun _ _ _ h => RecTypeOkAt.check_sound h) (by decide)

/-- **The compiled module of an accepted program validates.** -/
theorem moduleValid {p : Prog} (hp : p.WellTyped) (hfit : p.Fits) :
    ModuleValid (moduleOf p) :=
  ⟨⟨[], [.func dMain]⟩, ModuleOk.mk (fdts := [dMain]) (jts := []) (gts := []) (tts := [])
    (rts := []) (C' := moduleCtx' (moduleOf p) modTypes [] [dMain]) (C := modCtx p)
    typesOk .nil rfl rfl .nil .nil (fun _ h => absurd h List.not_mem_nil) .nil
    (.cons (funcOk_main (modCtx_types p) hp hfit) .nil) (fun _ h => absurd h List.not_mem_nil)
    .nil (fun _ h => by cases h) (.cons (.func rfl) .nil) (List.nodup_singleton "main")⟩

end Silmaril.Proofs.Wasm.Models.FunCompile
