module

public import Silmaril.Wasm.Execution.Core.Soundness.FrameRegularity
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Preservation for the return rules

`AdminsOk`-level preservation for `Step_pure/return-frame`, `return-label` and
`return-handler` (spec §4.3; `Step.lean` `returnFrame`/`returnLabel`/`returnHandler`).

The code under a frame is typed in the *frame's* context `C'`, whose type
context may differ from the outer `C` (cross-module calls). The returned values
are typed below the frame's (closed, `{} ⊢ t* : OK`) result type in `C'`, and
must be retyped in `C`. This needs:

* principal types of references (`RefOk.principal_sub`);
* that a subtyping derivation starting at a non-bottom heap type never uses the
  `RECS` field (`Sub.recsFreeRet`), since `Moduleinst_ok` here leaves `RECS`
  unconstrained;
* that subtyping between closed valid heap types does not depend on the `TYPES`
  field (`Sub.heap_emptyRet`, via the decision procedure `Sub.check`).

**Statement notes.**
* `returnFrame_presRet` needs `StoreOk s` and `StoreHeapTypesOk s`
  (`FrameRegularity.lean`): with a struct instance of open type `D` (mentioning
  `_IDX 0`), a returned reference may be typed below a closed result type in the
  frame's context (by `Deftype_sub/refl` after closure) but not in the caller's.
* `returnHandler_presRet` needs `ResultOk C.toTypeCtx it.results`: the handler's
  body may end, after the `return`, in a value whose store type is not valid, so
  the handler's result type need not be valid, while every typing of
  `val* return` with no parameters has valid results.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Closedness under substitution -/

theorem Ty.freeIdx_subst_subRet {k : TKind} (t : Ty k) :
    ∀ σ : Subst, (∀ v u, σ v = some u → u.freeIdx = []) →
      ∀ y ∈ (t.subst σ).freeIdx, y ∈ t.freeIdx := by
  induction t with
  | nil => intro σ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy
  | cons a l iha ihl =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · exact .inl (iha σ hσ y hy)
    · exact .inr (ihl σ hσ y hy)
  | idx x =>
    intro σ hσ y hy
    simp only [Ty.subst] at hy
    cases h : σ (.idx x) with
    | none => simp only [h, Option.getD_none] at hy; exact hy
    | some u => simp [h, hσ _ _ h] at hy
  | recv i =>
    intro σ hσ y hy
    simp only [Ty.subst] at hy
    cases h : σ (.recv i) with
    | none => simp [h, Ty.freeIdx] at hy
    | some u => simp [h, hσ _ _ h] at hy
  | dt d ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | defn g i ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | abs a => intro σ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy
  | bot => intro σ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy
  | use u ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | ref n h ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | num t => intro σ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy
  | vec t => intro σ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy
  | refv r ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | botv => intro σ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy
  | val t ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | pack p => intro σ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy
  | field m z ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | struct fs ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | array f ih =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ hσ y hy
  | func ps rs ihp ihr =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · exact .inl (ihp σ hσ y hy)
    · exact .inr (ihr σ hσ y hy)
  | sub f sups b ihs ihb =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · exact .inl (ihs σ hσ y hy)
    · exact .inr (ihb σ hσ y hy)
  | group subs ih =>
    intro σ hσ y hy
    have hσ' : ∀ v u, σ.minusRecs v = some u → u.freeIdx = [] := by
      intro v u h
      cases v with
      | recv _ => simp [Subst.minusRecs] at h
      | idx x => exact hσ _ _ (by simpa [Subst.minusRecs] using h)
    simp only [Ty.subst, Ty.freeIdx] at hy ⊢
    exact ih σ.minusRecs hσ' y hy

theorem closed_of_forall_memRet {l : List Nat} (h : ∀ y ∈ l, False) : l = [] :=
  List.eq_nil_iff_forall_not_mem.mpr h

/-- The declared supertypes of a closed defined type are closed. -/
theorem supersOf_closedRet {d : DefType} (hd : d.Closed) : ∀ u ∈ supersOf d, u.Closed := by
  intro u hu
  cases d with
  | defn g i =>
    cases g with
    | group subs =>
      have hsubs : subs.freeIdx = [] := by simpa [Ty.Closed, Ty.freeIdx] using hd
      unfold supersOf at hu
      cases hst : unrolldt (.defn (.group subs) i) with
      | none => simp [hst] at hu
      | some st =>
        rw [hst] at hu
        simp only [unrolldt, unrollrt, Ty.subs] at hst
        have hmem := List.mem_of_getElem? hst
        cases st with
        | sub fin sups ct =>
          simp only [Ty.supers] at hu
          apply closed_of_forall_memRet
          intro y hy
          have h1 : y ∈ (Ty.sub fin sups ct).freeIdx := by
            simp only [Ty.freeIdx, List.mem_append]
            exact .inl (Ty.freeIdx_of_mem hu hy)
          have h2 := Ty.freeIdx_of_mem hmem h1
          have h3 := Ty.freeIdx_subst_subRet subs _ ?_ y h2
          · rw [hsubs] at h3; simp at h3
          · intro v u' h
            cases v with
            | idx _ => simp at h
            | recv j =>
              simp only at h
              split at h
              · simp only [Option.some.injEq] at h
                subst h
                simpa [Ty.freeIdx] using hsubs
              · simp at h

/-! ## Subtyping of closed heap types does not depend on `TYPES` -/

theorem TypeCtx.resolve_closedRet {Δ₁ Δ₂ : TypeCtx} {u : CTypeUse} (hu : u.Closed) :
    Δ₁.resolve u = Δ₂.resolve u := by
  cases u with
  | idx x => simp [Ty.Closed, Ty.freeIdx] at hu
  | recv i => rfl
  | dt d => rfl

theorem TypeCtx.reach_closedRet {Δ₁ Δ₂ : TypeCtx} {P₁ P₂ : DefType → Bool}
    (hP : ∀ e : DefType, e.Closed → P₁ e = P₂ e) :
    ∀ (n : Nat) (d : DefType), d.Closed → Δ₁.reach P₁ n d = Δ₂.reach P₂ n d
  | 0, d, hd => by simp [TypeCtx.reach, hP d hd]
  | n + 1, d, hd => by
    have hs := supersOf_closedRet hd
    simp only [TypeCtx.reach, hP d hd]
    congr 1
    generalize supersOf d = l at hs ⊢
    induction l with
    | nil => rfl
    | cons u l ih =>
      simp only [List.any_cons]
      have hu := hs u (by simp)
      congr 1
      · cases u with
        | idx x => simp [Ty.Closed, Ty.freeIdx] at hu
        | recv i => rfl
        | dt d' =>
          exact TypeCtx.reach_closedRet hP n d' (by simpa [Ty.Closed, Ty.freeIdx] using hu)
      · exact ih (fun x hx => hs x (by simp [hx]))

theorem TypeCtx.checkDef_closedRet {Δ₁ Δ₂ : TypeCtx} {d₁ d₂ : DefType} (h₁ : d₁.Closed)
    (h₂ : d₂.Closed) : Δ₁.checkDef d₁ d₂ = Δ₂.checkDef d₁ d₂ := by
  unfold TypeCtx.checkDef
  have hf : ∀ Δ : TypeCtx, Δ.fuel d₁ = mu0 d₁ := by
    intro Δ
    have : d₁.freeIdx = [] := h₁
    simp [TypeCtx.fuel, this]
  rw [hf, hf]
  apply TypeCtx.reach_closedRet _ _ _ h₁
  intro e he
  simp [Ty.clos, Ty.substAll_closed he, Ty.substAll_closed h₂]

theorem TypeCtx.checkUseAbs_closedRet {Δ₁ Δ₂ : TypeCtx} {u : CTypeUse} {b : AbsHeapType}
    (hu : u.Closed) : Δ₁.checkUseAbs u b = Δ₂.checkUseAbs u b := by
  unfold TypeCtx.checkUseAbs
  rw [TypeCtx.resolve_closedRet (Δ₂ := Δ₂) hu]

theorem TypeCtx.checkHeap_closedRet {Δ₁ Δ₂ : TypeCtx} {a b : CHeapType} (ha : a.Closed)
    (hb : b.Closed) : Δ₁.checkHeap a b = Δ₂.checkHeap a b := by
  cases a with
  | bot => rfl
  | abs x =>
    cases b with
    | bot => rfl
    | abs y => rfl
    | use u =>
      have hu : u.Closed := by simpa [Ty.Closed, Ty.freeIdx] using hb
      simp only [TypeCtx.checkHeap]
      cases botTop x with
      | none => rfl
      | some t => exact TypeCtx.checkUseAbs_closedRet hu
  | use u₁ =>
    have hu₁ : u₁.Closed := by simpa [Ty.Closed, Ty.freeIdx] using ha
    cases b with
    | bot => rfl
    | abs y => exact TypeCtx.checkUseAbs_closedRet hu₁
    | use u₂ =>
      have hu₂ : u₂.Closed := by simpa [Ty.Closed, Ty.freeIdx] using hb
      cases u₁ with
      | idx x => simp [Ty.Closed, Ty.freeIdx] at hu₁
      | recv i =>
        cases u₂ with
        | idx x => simp [Ty.Closed, Ty.freeIdx] at hu₂
        | recv j => rfl
        | dt e => rfl
      | dt d =>
        cases u₂ with
        | idx x => simp [Ty.Closed, Ty.freeIdx] at hu₂
        | recv j => rfl
        | dt e =>
          simp only [TypeCtx.checkHeap, TypeCtx.resolve]
          exact TypeCtx.checkDef_closedRet (by simpa [Ty.Closed, Ty.freeIdx] using hu₁)
            (by simpa [Ty.Closed, Ty.freeIdx] using hu₂)

/-- Subtyping between closed valid heap types in a context without `RECS` whose
types are closed and valid holds in the empty context. -/
theorem Sub.heap_emptyRet {T : List DefType} (hT : ∀ d ∈ T, TyOk {} d) {a b : CHeapType}
    (ha : TyOk {} a) (hb : TyOk {} b) (h : Sub ({ types := T, recs := [] } : TypeCtx) a b) :
    Sub {} a b := by
  have hΔ : TypeCtx.Ok ({ types := T, recs := [] } : TypeCtx) :=
    fun d hd => ⟨TyOk.closed_of_empty (hT d hd), TyOk.ofEmpty (hT d hd) _⟩
  have hc := Sub.check_complete hΔ rfl h (TyOk.ofEmpty ha _) (TyOk.ofEmpty hb _)
  apply Sub.check_sound
  have e : ({} : TypeCtx).checkHeap a b = ({ types := T, recs := [] } : TypeCtx).checkHeap a b :=
    TypeCtx.checkHeap_closedRet (TyOk.closed_of_empty ha) (TyOk.closed_of_empty hb)
  change ({} : TypeCtx).checkHeap a b = true
  rw [e]
  exact hc

/-! ## Subtyping from a non-bottom heap type does not use `RECS` -/

/-- Type uses that are recursion variables. -/
def BotURet : CTypeUse → Prop
  | .idx _ => False
  | .recv _ => True
  | .dt _ => False

/-- Heap types that may lie below a recursion variable. -/
def BotHRet : CHeapType → Prop
  | .bot => True
  | .abs a => a = .none ∨ a = .nofunc ∨ a = .noexn ∨ a = .noextern
  | .use u => BotURet u

def DownMotiveRet : (k : TKind) → Ty k → Ty k → Prop
  | .heap, x, y => BotHRet y → BotHRet x
  | _, _, _ => True

/-- Only bottom-like heap types lie below bottom-like heap types. -/
theorem Sub.downRet {Δ : TypeCtx} : ∀ {k : TKind} {x y : Ty k}, Sub Δ x y → DownMotiveRet k x y
  | _, _, _, .heapRefl => by intro h; exact h
  | _, _, _, .heapTrans _ h₁ h₂ => by
    have ih₁ := Sub.downRet h₁
    have ih₂ := Sub.downRet h₂
    dsimp only [DownMotiveRet] at ih₁ ih₂ ⊢
    intro h
    exact ih₁ (ih₂ h)
  | _, _, _, .eqAny => by intro h; simp [BotHRet] at h
  | _, _, _, .i31Eq => by intro h; simp [BotHRet] at h
  | _, _, _, .structEq => by intro h; simp [BotHRet] at h
  | _, _, _, .arrayEq => by intro h; simp [BotHRet] at h
  | _, _, _, .defStruct _ => by intro h; simp [BotHRet] at h
  | _, _, _, .defArray _ => by intro h; simp [BotHRet] at h
  | _, _, _, .defFunc _ => by intro h; simp [BotHRet] at h
  | _, _, _, .defDef _ => by intro h; simp [BotHRet, BotURet] at h
  | _, _, _, .idxL _ hs => by
    have ih := Sub.downRet hs
    dsimp only [DownMotiveRet] at ih ⊢
    intro h
    exact absurd (ih h) (by simp [BotHRet, BotURet])
  | _, _, _, .idxR _ _ => by intro h; simp [BotHRet, BotURet] at h
  | _, _, _, .recStruct _ => by intro _; simp [BotHRet, BotURet]
  | _, _, _, .recArray _ => by intro _; simp [BotHRet, BotURet]
  | _, _, _, .recFunc _ => by intro _; simp [BotHRet, BotURet]
  | _, _, _, .recSub _ _ => by intro _; simp [BotHRet, BotURet]
  | _, _, _, .none _ _ => by intro _; simp [BotHRet]
  | _, _, _, .nofunc _ _ => by intro _; simp [BotHRet]
  | _, _, _, .noexn _ _ => by intro _; simp [BotHRet]
  | _, _, _, .noextern _ _ => by intro _; simp [BotHRet]
  | _, _, _, .bot => by intro _; simp [BotHRet]
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

/-- Validity of a non-bottom heap type does not use `RECS`. -/
theorem TyOk.heap_recsRet {Δ : TypeCtx} {m : CHeapType} (hm : ¬ BotHRet m) (h : TyOk Δ m) :
    TyOk ({ types := Δ.types, recs := [] } : TypeCtx) m := by
  cases m with
  | abs a => exact .abs a
  | bot => exact absurd trivial hm
  | use u =>
    cases u with
    | idx x => cases h with | use h => cases h with | idx h => exact .use (.idx h)
    | recv i => exact absurd trivial hm
    | dt d =>
      cases h with
      | use h => cases h with | dt h => exact .use (.dt (TyOk.def_congr (Δ₁ := Δ) (Δ₂ := { types := Δ.types, recs := [] }) rfl h))

/-- The declared supertypes of a valid defined type are valid and not recursion
variables. -/
theorem TyOk.unroll_superRet {Δ : TypeCtx} {b : DefType} (hb : TyOk Δ b) {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType}
    (hu : unrolldt b = some (.sub fin sups ct)) {u : CTypeUse} (hmem : u ∈ sups.toList) :
    TyOk Δ (.use u) ∧ ¬ BotURet u := by
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
            exact ⟨.use (.idx h), by simp [BotURet]⟩
        | recv j =>
          cases hok with
          | recv h =>
            have hj : j < subs.length := by
              have := (List.getElem?_eq_some_iff.1 h).1
              simpa [TypeCtx.withRecs, Ty.length] using this
            simp only [Ty.subst, hj, ite_true, Option.getD_some]
            exact ⟨.use (.dt (.defn hg hj)), by simp [BotURet]⟩
        | dt e =>
          rw [Ty.recFree_dt e _ (fun _ => rfl)]
          cases hok with
          | dt h =>
            exact ⟨.use (.dt (TyOk.def_congr (Δ₁ := Δ.withRecs subs.toList) (Δ₂ := Δ) rfl h)),
              by simp [BotURet]⟩

def RecsMotiveRet (Δ : TypeCtx) : (k : TKind) → Ty k → Ty k → Prop
  | .heap, x, y => ¬ BotHRet x → TyOk Δ x → Sub ({ types := Δ.types, recs := [] } : TypeCtx) x y
  | .def, x, y => TyOk Δ x → Sub ({ types := Δ.types, recs := [] } : TypeCtx) x y
  | _, _, _ => True

/-- A subtyping derivation from a valid non-bottom heap type (or a valid defined
type) does not use `RECS`. -/
theorem Sub.recsFreeRet {Δ : TypeCtx}
    (hT : ∀ (x : Nat) (d : DefType), Δ.types[x]? = some d → TyOk Δ d) :
    ∀ {k : TKind} {x y : Ty k}, Sub Δ x y → RecsMotiveRet Δ k x y
  | _, _, _, .heapRefl => by intro _ _; exact .heapRefl
  | _, _, _, .heapTrans hok h₁ h₂ => by
    have ih₁ := Sub.recsFreeRet hT h₁
    have ih₂ := Sub.recsFreeRet hT h₂
    dsimp only [RecsMotiveRet] at ih₁ ih₂ ⊢
    intro hx hxok
    have hm : ¬ BotHRet _ := fun hm => hx (by
      have := Sub.downRet h₁
      dsimp only [DownMotiveRet] at this
      exact this hm)
    exact .heapTrans (TyOk.heap_recsRet hm hok) (ih₁ hx hxok) (ih₂ hm hok)
  | _, _, _, .eqAny => by intro _ _; exact .eqAny
  | _, _, _, .i31Eq => by intro _ _; exact .i31Eq
  | _, _, _, .structEq => by intro _ _; exact .structEq
  | _, _, _, .arrayEq => by intro _ _; exact .arrayEq
  | _, _, _, .defStruct h => by intro _ _; exact .defStruct h
  | _, _, _, .defArray h => by intro _ _; exact .defArray h
  | _, _, _, .defFunc h => by intro _ _; exact .defFunc h
  | _, _, _, .defDef h => by
    have ih := Sub.recsFreeRet hT h
    dsimp only [RecsMotiveRet] at ih ⊢
    intro _ hx
    cases hx with
    | use hu => cases hu with | dt hd => exact .defDef (ih hd)
  | _, _, _, .idxL hx hs => by
    have ih := Sub.recsFreeRet hT hs
    dsimp only [RecsMotiveRet] at ih ⊢
    intro _ _
    exact .idxL hx (ih (by simp [BotHRet, BotURet]) (.use (.dt (hT _ _ hx))))
  | _, _, _, .idxR hx hs => by
    have ih := Sub.recsFreeRet hT hs
    dsimp only [RecsMotiveRet] at ih ⊢
    intro hnb hxok
    exact .idxR hx (ih hnb hxok)
  | _, _, _, .recStruct _ => by intro hnb; exact absurd (by simp [BotHRet, BotURet]) hnb
  | _, _, _, .recArray _ => by intro hnb; exact absurd (by simp [BotHRet, BotURet]) hnb
  | _, _, _, .recFunc _ => by intro hnb; exact absurd (by simp [BotHRet, BotURet]) hnb
  | _, _, _, .recSub _ _ => by intro hnb; exact absurd (by simp [BotHRet, BotURet]) hnb
  | _, _, _, .none _ _ => by intro hnb; exact absurd (by simp [BotHRet]) hnb
  | _, _, _, .nofunc _ _ => by intro hnb; exact absurd (by simp [BotHRet]) hnb
  | _, _, _, .noexn _ _ => by intro hnb; exact absurd (by simp [BotHRet]) hnb
  | _, _, _, .noextern _ _ => by intro hnb; exact absurd (by simp [BotHRet]) hnb
  | _, _, _, .bot => by intro hnb; exact absurd (by simp [BotHRet]) hnb
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
  | _, _, _, .defRefl h => by intro _; exact .defRefl h
  | _, _, _, .defSuper h hj hs => by
    have ih := Sub.recsFreeRet hT hs
    dsimp only [RecsMotiveRet] at ih ⊢
    intro hd
    obtain ⟨hu, hnr⟩ := TyOk.unroll_superRet hd h (List.mem_of_getElem? hj)
    exact .defSuper h hj (ih hnr hu)
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial

/-! ## Retyping values across type contexts -/

theorem RefBase.heap_caseRet {s : Store H} {r : Ref} {n : Bool} {h : CHeapType}
    (hb : RefBase s r (.ref n h)) : h = .bot ∨ ¬ BotHRet h := by
  cases hb <;> simp [BotHRet, BotURet, Ty.defHeap]

theorem Sub.ref_closeRet {s : Store H} {Δ : TypeCtx} (hT : ∀ d ∈ Δ.types, TyOk {} d)
    {r : Ref} {rt₀ rt' : CRefType} (hb : RefBase s r rt₀) (h0 : TyOk {} rt₀)
    (h' : TyOk {} rt') (hsub : Sub Δ rt₀ rt') : Sub {} rt₀ rt' := by
  cases rt₀ with
  | ref n₀ h₀ =>
    cases rt' with
    | ref n' h₁ =>
      obtain ⟨hh, hn⟩ := Sub.ref_inv hsub
      have hheap : Sub {} h₀ h₁ := by
        rcases hb.heap_caseRet with rfl | hnb
        · exact .bot
        · have hTΔ : ∀ x d, Δ.types[x]? = some d → TyOk Δ d :=
            fun x d hx => TyOk.ofEmpty (hT d (List.mem_of_getElem? hx)) Δ
          have h1 := Sub.recsFreeRet hTΔ hh
          dsimp only [RecsMotiveRet] at h1
          have h0' : TyOk {} h₀ := by cases h0 with | ref hh => exact hh
          have h1' : TyOk {} h₁ := by cases h' with | ref hh => exact hh
          exact Sub.heap_emptyRet hT h0' h1' (h1 hnb (TyOk.ofEmpty h0' Δ))
      cases n' with
      | true => exact .refNull hheap
      | false =>
        cases n₀ with
        | false => exact .refNonNull hheap
        | true => simp at hn

/-- A value typed below a closed valid type in a context whose types are closed
and valid has that type. -/
theorem ValOk.transferRet {s : Store H} (hs : StoreOk s) (hh : StoreHeapTypesOk s)
    {Δ : TypeCtx} (hT : ∀ d ∈ Δ.types, TyOk {} d) {v : Val} {t t' : CValType}
    (hv : ValOk s v t) (hsub : Sub Δ t t') (ht' : TyOk {} t') : ValOk s v t' := by
  cases hv with
  | num nv => cases hsub; exact .num nv
  | vec b => cases hsub; exact .vec b
  | ref hr =>
    cases hsub with
    | @refv _ _ r₂ h =>
      obtain ⟨rt₀, hb, h0⟩ := hr.principal_sub h
      have hok0 : TyOk {} rt₀ := RefOk.tyOk hs hh hb.refOk
      have ht2 : TyOk {} r₂ := by cases ht' with | refv h => exact h
      exact .ref (.sub hb.refOk ht2 (Sub.ref_closeRet hT hb hok0 ht2 h0))

theorem ValOk.forall₂_transferRet {s : Store H} (hs : StoreOk s) (hh : StoreHeapTypesOk s)
    {Δ : TypeCtx} (hT : ∀ d ∈ Δ.types, TyOk {} d) :
    ∀ {vs : List Val} {tv ts : List CValType}, List.Forall₂ (ValOk s) vs tv →
      List.Forall₂ (Sub Δ) tv ts → ResultOk {} ts → List.Forall₂ (ValOk s) vs ts
  | _, _, _, .nil, .nil, _ => .nil
  | _, _, _, .cons hv hvs, .cons hs' hss, hok =>
    .cons (ValOk.transferRet hs hh hT hv hs' (hok _ (by simp)))
      (ValOk.forall₂_transferRet hs hh hT hvs hss (fun x hx => hok x (by simp [hx])))

/-! ## Administrative helpers (copied from the control unit, `Ret` suffix) -/

theorem forall₂_split_leftRet {α β : Type _} {R : α → β → Prop} {a b : List α} {l : List β}
    (h : List.Forall₂ R (a ++ b) l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R a l₁ ∧ List.Forall₂ R b l₂ := by
  refine ⟨l.take a.length, l.drop a.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · have := List.forall₂_take a.length h; simpa using this
  · have := List.forall₂_drop a.length h; simpa using this

/-- Values typed at well-formed supertypes of their types. -/
theorem AdminsOk.vals_toRet {s : Store H} {C : Context} {vs : List Val} {ts : List CValType}
    (hv : List.Forall₂ (ValOk s) vs ts) :
    ∀ {us : List CValType}, ResultSub C.toTypeCtx ts us → ResultOk C.toTypeCtx us →
    AdminsOk s C (vals vs) (.plain [] us) := by
  induction hv with
  | nil => intro us hs _; cases hs; exact .nil
  | @cons v t vs ts hv _ ih =>
    intro us hs hok
    cases hs with
    | @cons _ u _ us hs hss =>
      have hu : TyOk C.toTypeCtx u := hok u (by simp)
      have h1 : AdminsOk s C [v.toAdmin] (.plain [] [u]) := AdminsOk.val_sub hv hs hu
      have h2 : AdminsOk s C (vals vs) (.plain [] us) :=
        ih hss (fun x hx => hok x (by simp [hx]))
      have h3 : AdminsOk s C (vals vs) ⟨[u] ++ [], [], [u] ++ us⟩ :=
        .frame h2 (by simpa using hu)
      have := AdminsOk.seq h1 (by simp) (by simpa using h3)
      simpa [vals] using this

/-- Typings of administrative source code are source typings. -/
theorem AdminsOk.expr_okRet {s : Store H} {C : Context} {is : List Instr} {it : InstrType}
    (hC : C.Wf) (h : AdminsOk s C (expression is) it) : InstrTypeOk C it :=
  AdminsOk.instrTypeOk_of_plain hC h (by simp [expression])

theorem single_repRet {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    (hI : ∀ it', AdminOk s C a it' → it'.inits = []) (h : AdminsOk s C [a] it) :
    ∃ A t₂, AdminOk s C a ⟨A, [], t₂⟩ ∧
      ∀ (s' : Store H) (out : List Admin), AdminsOk s' C out ⟨A, [], t₂⟩ →
        AdminsOk s' C out it := by
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, hrep⟩ :=
    redex_inv_gen (vs := []) (fun it' h' => ⟨hI it' h', by simp⟩) (by simpa [vals] using h)
  cases hvs
  cases hB
  exact ⟨A, t₂, by simpa using hi, hrep⟩

theorem single_at_itRet {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    {out : List Admin} (hC : C.Wf) (hr : ResultOk C.toTypeCtx it.results)
    (hI : ∀ it', AdminOk s C a it' → it'.inits = []) (h : AdminsOk s C [a] it)
    (hout : AdminsOk s C out ⟨it.params, [], it.results⟩) : AdminsOk s C out it := by
  obtain ⟨ts, it₀, ha, -, -, hi⟩ := AdminsOk.single_aux h a rfl hC.types
  have hp := AdminsOk.params_ok hC h
  exact .sub hout ⟨ResultSub.refl _ _, ResultSub.refl _ _,
    fun x hx _ => hi x hx (by rw [hI _ ha]; simp)⟩ ⟨hp.1, hr, hp.2⟩

theorem AdminOk.label_invRet {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {body : List Admin} {it : InstrType} (h : AdminOk s C (.label n cont body) it) :
    it.params = [] ∧ it.inits = [] ∧ ∃ t' xs' xs, t'.length = n ∧
      AdminsOk s C (expression cont) ⟨t', xs', it.results⟩ ∧
      AdminsOk s (C.withLabel t') body ⟨[], xs, it.results⟩ := by
  cases h with
  | label hn hc hb => exact ⟨rfl, rfl, _, _, _, hn, hc, hb⟩

theorem AdminOk.handler_invRet {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {body : List Admin} {it : InstrType} (h : AdminOk s C (.handler n cs body) it) :
    it.params = [] ∧ it.inits = [] ∧ (∀ c ∈ cs, CatchOk C c) ∧ ∃ xs,
      AdminsOk s C body ⟨[], xs, it.results⟩ := by
  cases h with
  | handler hc hb => exact ⟨rfl, rfl, hc, _, hb⟩

theorem AdminOk.frame_invRet {s : Store H} {C : Context} {n : Nat} {fr : Frame}
    {body : List Admin} {it : InstrType} (h : AdminOk s C (.frame n fr body) it) :
    it.params = [] ∧ it.inits = [] ∧ ∃ C', FrameOk s fr C' ∧ it.results.length = n ∧
      AdminsOk s { C' with return_ := some it.results } body (.plain [] it.results) ∧
      ResultOk {} it.results := by
  cases h with
  | frame hf hn hb hok => exact ⟨rfl, rfl, _, hf, hn, hb, hok⟩

theorem AdminOk.label_initsRet {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {body : List Admin} : ∀ it', AdminOk s C (.label n cont body) it' → it'.inits = [] :=
  fun _ h => (AdminOk.label_invRet h).2.1

theorem AdminOk.handler_initsRet {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {body : List Admin} : ∀ it', AdminOk s C (.handler n cs body) it' → it'.inits = [] :=
  fun _ h => (AdminOk.handler_invRet h).2.1

theorem AdminOk.frame_initsRet {s : Store H} {C : Context} {n : Nat} {fr : Frame}
    {body : List Admin} : ∀ it', AdminOk s C (.frame n fr body) it' → it'.inits = [] :=
  fun _ h => (AdminOk.frame_invRet h).2.1

theorem AdminOk.return_invRet {s : Store H} {C : Context} {it₀ : InstrType}
    (h : AdminOk s C (.plain .return_) it₀) :
    ∃ R t₁ t₂, C.return_ = some R ∧ it₀ = ⟨t₁ ++ R, [], t₂⟩ ∧ InstrTypeOk C (.plain t₁ t₂) := by
  cases h with
  | plain h =>
    cases h with
    | return_ hr hok => exact ⟨_, _, _, hr, rfl, hok⟩
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h

/-! ## Inversion of `val* return instr*` -/

/-- Inversion of a sequence `val* return instr*`: the values are typed (pointwise,
above the parameters) below `M ++ R`, where `R` is the context's return type and
`M` is valid. No well-formedness of the context is needed beyond validity of
its return type. -/
theorem ret_inv_auxRet {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it →
    (∀ R, C.return_ = some R → ResultOk C.toTypeCtx R) →
    ∀ (vs : List Val) (rest : List Admin), as = vals vs ++ [.plain .return_] ++ rest →
    ∃ R tv M, C.return_ = some R ∧ List.Forall₂ (ValOk s) vs tv ∧ ResultOk C.toTypeCtx M ∧
      ResultOk C.toTypeCtx it.params ∧
      List.Forall₂ (SubEqR C.toTypeCtx) (it.params ++ tv) (M ++ R)
  | _, _, _, .nil, _, vs, rest, he => by simp at he
  | _, _, _, .single ha, hR, vs, rest, he => by
    cases vs with
    | cons v vs => simp [vals] at he
    | nil =>
      simp only [vals, List.map_nil, List.nil_append, List.singleton_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨R, t₁, t₂, hr, rfl, hok⟩ := AdminOk.return_invRet ha
      refine ⟨R, [], t₁, hr, .nil, hok.1, ResultOk.appendRT hok.1 (hR R hr), ?_⟩
      simpa using forall₂_self (R := SubEqR _) (fun _ => .inl rfl) (t₁ ++ R)
  | C, _, _, .cons (xs₁ := xs₁) ha hx hs, hR, vs, rest, he => by
    have hR' : ∀ R, (C.initLocals xs₁).return_ = some R →
        ResultOk (C.initLocals xs₁).toTypeCtx R := by
      intro R h; simp only [Context.initLocals_return, Context.initLocals_toTypeCtx] at h ⊢
      exact hR R h
    cases vs with
    | nil =>
      simp only [vals, List.map_nil, List.nil_append, List.singleton_append,
        List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨R, t₁, t₂, hr, heq, hok⟩ := AdminOk.return_invRet ha
      simp only [InstrType.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨R, [], t₁, hr, .nil, hok.1, ResultOk.appendRT hok.1 (hR R hr), ?_⟩
      simpa using forall₂_self (R := SubEqR _) (fun _ => .inl rfl) (t₁ ++ R)
    | cons v vs' =>
      simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, has'⟩ := he
      obtain ⟨R, tv', M, hr, hv', hM, -, hsub⟩ := ret_inv_auxRet hs hR' vs' rest has'
      obtain ⟨t, hit, hv⟩ := AdminOk.val_invRT ha
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨rfl, rfl, rfl⟩ := hit
      simp only [Context.initLocals_return, Context.initLocals_toTypeCtx] at hr hM hsub
      exact ⟨R, t :: tv', M, hr, .cons hv hv', hM, by simp [ResultOk], by simpa using hsub⟩
  | C, _, _, .seq (as₁ := as₁) (as₂ := as₂) (t₁ := t₁) (xs₁ := xs₁) h₁ hx h₂, hR, vs, rest, he => by
    have hR' : ∀ R, (C.initLocals xs₁).return_ = some R →
        ResultOk (C.initLocals xs₁).toTypeCtx R := by
      intro R h; simp only [Context.initLocals_return, Context.initLocals_toTypeCtx] at h ⊢
      exact hR R h
    have case1 : ∀ vs₁ vs₂, vs = vs₁ ++ vs₂ → as₁ = vals vs₁ →
        as₂ = vals vs₂ ++ [.plain .return_] ++ rest →
        ∃ R tv M, C.return_ = some R ∧ List.Forall₂ (ValOk s) vs tv ∧ ResultOk C.toTypeCtx M ∧
          ResultOk C.toTypeCtx t₁ ∧ List.Forall₂ (SubEqR C.toTypeCtx) (t₁ ++ tv) (M ++ R) := by
      intro vs₁ vs₂ hvs e₁ e₂
      obtain ⟨p₁, -, ts₁, v₁, r₁⟩ := AdminsOk.vals_aux' h₁ vs₁ e₁
      obtain ⟨R, tv₂, M, hr, hv₂, hM, -, hsub⟩ := ret_inv_auxRet h₂ hR' vs₂ rest e₂
      simp only [Context.initLocals_return, Context.initLocals_toTypeCtx] at hr hM hsub
      subst hvs
      refine ⟨R, ts₁ ++ tv₂, M, hr, forall₂_append v₁ hv₂, hM, p₁, ?_⟩
      rw [← List.append_assoc]
      exact forall₂_comp (forall₂_append r₁ (forall₂_self (fun _ => .inl rfl) tv₂)) hsub
        fun _ _ _ _ _ _ hab hbc => hab.trans_val hbc
    have he' : as₁ ++ as₂ = vals vs ++ (.plain .return_ :: rest) := by simpa using he
    rcases List.append_eq_append_iff.mp he' with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp h1
      exact case1 vs₁ vs₂ rfl e₁.symm (by rw [h2, ← e₂]; simp [vals])
    · cases c' with
      | nil =>
        simp only [List.append_nil, List.nil_append] at h1 h2
        exact case1 vs [] (by simp) h1 (by rw [← h2]; simp [vals])
      | cons x c'' =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ret_inv_auxRet h₁ hR vs c'' (by rw [h1]; simp)
  | _, _, _, .sub (it := it₀) h hs hok, hR, vs, rest, he => by
    obtain ⟨R, tv, M, hr, hv, hM, p, hsub⟩ := ret_inv_auxRet h hR vs rest he
    refine ⟨R, tv, M, hr, hv, hM, hok.1, ?_⟩
    exact forall₂_comp (forall₂_append (forall₂_subEqR_of_sub hs.1 p)
      (forall₂_self (fun _ => .inl rfl) tv)) hsub fun _ _ _ _ _ _ hab hbc => hab.trans_val hbc
  | _, _, _, .frame (ts := ts) h hok, hR, vs, rest, he => by
    obtain ⟨R, tv, M, hr, hv, hM, p, hsub⟩ := ret_inv_auxRet h hR vs rest he
    refine ⟨R, tv, ts ++ M, hr, hv, ResultOk.appendRT hok hM, ResultOk.appendRT hok p, ?_⟩
    simp only [List.append_assoc]
    exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hsub

/-- Retyping `val* return` below a valid prefix `p`. -/
theorem retype_valsRet {s : Store H} {C : Context} {vs : List Val} {R tv M p t₂ : List CValType}
    (hR : C.return_ = some R) (hM : ResultOk C.toTypeCtx M) (hRok : ResultOk C.toTypeCtx R)
    (hp : ResultOk C.toTypeCtx p) (ht₂ : ResultOk C.toTypeCtx t₂)
    (hv : List.Forall₂ (ValOk s) vs tv)
    (hsub : List.Forall₂ (SubEqR C.toTypeCtx) tv (M ++ R)) :
    AdminsOk s C (vals vs ++ [.plain .return_]) ⟨p, [], t₂⟩ := by
  have hMR : ResultOk C.toTypeCtx (M ++ R) := ResultOk.appendRT hM hRok
  have hV : AdminsOk s C (vals vs) (.plain [] (M ++ R)) :=
    AdminsOk.vals_toRet hv (hsub.imp fun _ _ h => h.sub) hMR
  have hV' : AdminsOk s C (vals vs) ⟨p ++ [], [], p ++ (M ++ R)⟩ := .frame hV hp
  have hI : InstrOk C .return_ (.plain ((p ++ M) ++ R) t₂) :=
    .return_ hR ⟨ResultOk.appendRT hp hM, ht₂, by simp⟩
  have := AdminsOk.seq hV' (by simp) (by simpa [List.append_assoc] using
    (AdminsOk.single (.plain hI) : AdminsOk s C [.plain .return_] _))
  simpa using this

/-! ## The return rules -/

/-- `Step_pure/return-frame`. (Statement: needs `StoreOk s` and
`StoreHeapTypesOk s`; see the module doc.) -/
theorem Step.returnFrame_presRet {s : Store H} {C : Context} {n : Nat} {fi : Frame}
    {vs' vs : List Val} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] it)
    (hs : StoreOk s) (hh : StoreHeapTypesOk s) (hn : vs.length = n) :
    AdminsOk s C (vals vs) it := by
  obtain ⟨A, t₂, ha, hrep⟩ := single_repRet AdminOk.frame_initsRet h
  obtain ⟨hA, -, C', hf, hlen, hb, hok⟩ := AdminOk.frame_invRet ha
  simp only at hA hlen hb hok
  subst hA
  have hTC : ∀ d ∈ C'.types, TyOk {} d := by
    intro d hd
    obtain ⟨C₀, hm, -⟩ := hf.inv
    rw [hf.types_eq] at hd
    exact hm.inv.2.1 d hd
  obtain ⟨R, tv, M, hR, hv, -, -, hsub⟩ := ret_inv_auxRet hb
    (by
      intro R hR
      simp only [Option.some.injEq] at hR
      subst hR
      intro t ht
      exact TyOk.ofEmpty (hok t ht) _)
    (vs' ++ vs) rest (by simp [vals, List.append_assoc])
  simp only [Option.some.injEq] at hR
  subst hR
  simp only [List.nil_append] at hsub
  obtain ⟨tv₁, tv₂, rfl, -, hv₂⟩ := forall₂_split_leftRet hv
  obtain ⟨l₁, l₂, hl, -, hs₂⟩ := forall₂_split_leftRet hsub
  have e1 := hs₂.length_eq
  have e2 := hv₂.length_eq
  obtain ⟨-, h2⟩ := List.append_inj' hl (by omega)
  rw [← h2] at hs₂
  have hvt : List.Forall₂ (ValOk s) vs t₂ :=
    ValOk.forall₂_transferRet hs hh (Δ := C'.toTypeCtx) hTC hv₂
      (hs₂.imp fun _ _ h => h.sub) hok
  exact hrep s _ (AdminsOk.of_vals hvt (fun t ht => TyOk.ofEmpty (hok t ht) _))

/-- `Step_pure/return-label`. -/
theorem Step.returnLabel_presRet {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs : List Val} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.label n cont (vals vs ++ [.plain .return_] ++ rest)] it) (hC : C.Wf) :
    AdminsOk s C (vals vs ++ [.plain .return_]) it := by
  obtain ⟨A, t₂, ha, hrep⟩ := single_repRet AdminOk.label_initsRet h
  obtain ⟨hA, -, t', xs', xs, -, hc, hb⟩ := AdminOk.label_invRet ha
  simp only at hA hc hb
  subst hA
  have ht₂ : ResultOk C.toTypeCtx t₂ := (AdminsOk.expr_okRet hC hc).2.1
  obtain ⟨R, tv, M, hR, hv, hM, -, hsub⟩ :=
    ret_inv_auxRet hb (fun R hR => hC.return_ R hR) vs rest rfl
  exact hrep s _ (retype_valsRet (p := []) hR hM (hC.return_ R hR) (by simp [ResultOk]) ht₂ hv
    (by simpa using hsub))

/-- `Step_pure/return-handler`. (Statement: needs valid results; see the module
doc.) -/
theorem Step.returnHandler_presRet {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {vs : List Val} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.handler n cs (vals vs ++ [.plain .return_] ++ rest)] it) (hC : C.Wf)
    (hr : ResultOk C.toTypeCtx it.results) :
    AdminsOk s C (vals vs ++ [.plain .return_]) it := by
  obtain ⟨A, t₂, ha, -⟩ := single_repRet AdminOk.handler_initsRet h
  obtain ⟨hA, -, -, xs, hb⟩ := AdminOk.handler_invRet ha
  obtain ⟨R, tv, M, hR, hv, hM, -, hsub⟩ :=
    ret_inv_auxRet hb (fun R hR => hC.return_ R hR) vs rest rfl
  have hp := (AdminsOk.params_ok hC h).1
  exact single_at_itRet hC hr AdminOk.handler_initsRet h
    (retype_valsRet hR hM (hC.return_ R hR) hp hr hv (by simpa using hsub))

end Silmaril.Wasm.Execution.Core
