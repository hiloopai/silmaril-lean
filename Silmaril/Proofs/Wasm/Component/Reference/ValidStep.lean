module

public import Silmaril.Proofs.Wasm.Component.Reference.ValidCore

/-!
# The validator on the definitions `Simple.toRef` emits

For each kind of definition that `Simple.toRef` emits, an accepted check (`checkDef?` of the
Core 3.0 profile) extends the parts of the validation context that type resolution and the
`canon lift` check read: the type index space (`types`), the core functions and the core
instances. `ValidView s` collects them.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Component.Types (TypeDef)

/-- The part of a definition-validation state that resolution and lifts read: the type
definitions, the core functions and the core instances. -/
def ValidView (s : DefState Core3Extern) :
    List (TypeDef Nat Core3Extern) × List Core3Extern × List (List (String × Core3Extern)) :=
  (s.ctx.types.map (·.def_), s.ctx.coreFuncs, s.ctx.coreInstances)

/-- The validator of the Core 3.0 profile, one definition. -/
abbrev chk (sc : Scopes Core3Extern) (s : DefState Core3Extern)
    (d : Syntax.Definition Silmaril.Wasm.Module) :=
  checkDef? Features.p2 core3Profile core3ModuleType? sc s d

/-- The validator of the Core 3.0 profile, definitions in order. -/
abbrev chks (sc : Scopes Core3Extern) (s : DefState Core3Extern)
    (ds : List (Syntax.Definition Silmaril.Wasm.Module)) :=
  checkDefs? Features.p2 core3Profile core3ModuleType? sc s ds

theorem chks_cons {sc : Scopes Core3Extern} {s s'' : DefState Core3Extern}
    {d : Syntax.Definition Silmaril.Wasm.Module} {ds : List (Syntax.Definition Silmaril.Wasm.Module)}
    (h : chks sc s (d :: ds) = .ok s'') : ∃ s', chk sc s d = .ok s' ∧ chks sc s' ds = .ok s'' := by
  simp only [chks, checkDefs?] at h
  split at h
  · next s' hs => exact ⟨s', hs, h⟩
  · cases h

theorem chks_append {sc : Scopes Core3Extern} :
    ∀ {s s'' : DefState Core3Extern} {ds ds' : List (Syntax.Definition Silmaril.Wasm.Module)},
      chks sc s (ds ++ ds') = .ok s'' → ∃ s', chks sc s ds = .ok s' ∧ chks sc s' ds' = .ok s''
  | s, s'', [], ds', h => ⟨s, rfl, h⟩
  | s, s'', d :: ds, ds', h => by
    obtain ⟨s₁, h₁, h₂⟩ := chks_cons h
    obtain ⟨s', h₃, h₄⟩ := chks_append h₂
    refine ⟨s', ?_, h₄⟩
    simp only [chks, checkDefs?]
    have h₁' : checkDef? Features.p2 core3Profile core3ModuleType? sc s d = .ok s₁ := h₁
    rw [h₁']
    exact h₃

/-! ## One definition at a time -/

variable {sc : Scopes Core3Extern} {s s' : DefState Core3Extern}

/-- `type (val d)`: the resolved value type is pushed. -/
theorem chk_typeVal {d : Syntax.DefValType} (h : chk sc s (.type (.val d)) = .ok s') :
    ∃ t, checkDefValType? Features.p2 s.ctx d = .ok t ∧
      ValidView s' = ((ValidView s).1 ++ [.val t], (ValidView s).2) := by
  simp only [chk, checkDef?] at h
  split at h
  · next st' hst =>
    cases h
    simp only [checkDefType?] at hst
    split at hst
    · next t ht =>
      cases hst
      refine ⟨t, ht, ?_⟩
      simp [ValidView, DefState.step, DState.pushTypeInfo, Ctx.pushType, Ctx.pushTypeSlot,
        Ctx.pushList, Ctx.freshToken]
    · cases hst
  · cases h

/-- `type (func ft)`: the resolved function type is pushed. -/
theorem chk_typeFunc {ft : Syntax.FuncType} (h : chk sc s (.type (.func ft)) = .ok s') :
    ∃ t, checkFuncType? Features.p2 s.ctx ft = .ok t ∧
      ValidView s' = ((ValidView s).1 ++ [.func t], (ValidView s).2) := by
  simp only [chk, checkDef?] at h
  split at h
  · next st' hst =>
    cases h
    simp only [checkDefType?] at hst
    split at hst
    · next t ht =>
      cases hst
      refine ⟨t, ht, ?_⟩
      simp [ValidView, DefState.step, DState.pushTypeInfo, Ctx.pushType, Ctx.pushTypeSlot,
        Ctx.pushList, Ctx.freshToken]
    · cases hst
  · cases h

/-- `core module m`: the parts read by resolution and lifts are unchanged. -/
theorem chk_coreModule {m : Silmaril.Wasm.Module} (h : chk sc s (.coreModule m) = .ok s') :
    ∃ mt, core3ModuleType? m = some mt ∧ s'.ctx.coreModules = s.ctx.coreModules ++ [mt] ∧
      ValidView s' = ValidView s := by
  simp only [chk, checkDef?, checkCoreModule?] at h
  split at h
  · next mt hm =>
    cases h
    exact ⟨mt, hm, rfl, rfl⟩
  · cases h

/-- `core instance (instantiate i [])`: the exports of module `i` become a core instance. -/
theorem chk_coreInstance {i : Nat} (h : chk sc s (.coreInstance (.instantiate i [])) = .ok s') :
    ∃ mt, s.ctx.coreModules[i]? = some mt ∧
      ValidView s' = ((ValidView s).1, (ValidView s).2.1, (ValidView s).2.2 ++ [mt.exports]) := by
  simp only [chk, checkDef?, checkCoreInstance?] at h
  split at h
  · cases h
  · next mt hmt =>
    have hmt' : s.ctx.coreModules[i]? = some mt := Ctx.listAt?_eq_ok.1 hmt
    split at h
    · split at h
      · split at h
        · cases h
        · cases h
          exact ⟨mt, hmt', rfl⟩
      · split at h <;> cases h
    · cases h

/-- `alias core export i n func`: the export `n` of core instance `i` is pushed as a core
function. -/
theorem chk_aliasCoreFunc {i : Nat} {n : String}
    (h : chk sc s (.alias (.coreExport i n .func)) = .ok s') :
    ∃ ex x, s.ctx.coreInstances[i]? = some ex ∧ ex.lookup n = some x ∧
      ValidView s' = ((ValidView s).1, (ValidView s).2.1 ++ [x], (ValidView s).2.2) := by
  simp only [chk, checkDef?, checkAlias?] at h
  split at h
  · cases h
  · next ex hex =>
    have hex' : s.ctx.coreInstances[i]? = some ex := Ctx.listAt?_eq_ok.1 hex
    split at h
    · cases h
    · next x hx =>
      split at h
      · cases h
        exact ⟨ex, x, hex', hx, rfl⟩
      · cases h

/-- `canon lift f opts t`: type `t` is a function type that the lift check accepts; the parts
read by resolution and lifts are unchanged. -/
theorem chk_lift {f t : Nat} {opts : List Syntax.CanonOpt}
    (h : chk sc s (.canon (.lift f opts t)) = .ok s') :
    ∃ ft, s.ctx.type? t = some (.func ft) ∧
      LiftOk Features.p2 core3Profile.view.core s.ctx f opts ft ∧ ValidView s' = ValidView s := by
  simp only [chk, checkDef?, checkCanon?, checkLiftLower?] at h
  split at h
  · next e he =>
    cases h
    cases hft : checkLift? Features.p2 core3Profile.view.core s.ctx f opts t with
    | error err =>
      rw [hft] at he
      cases he
    | ok ft =>
      obtain ⟨hty, hok⟩ := checkLift?_iff.1 hft
      rw [hft] at he
      cases he
      exact ⟨ft, hty, hok, rfl⟩
  · cases h

/-! ## Exports -/

/-- The view of a context. -/
def CtxView (Γ : Ctx Core3Extern) :
    List (TypeDef Nat Core3Extern) × List Core3Extern × List (List (String × Core3Extern)) :=
  (Γ.types.map (·.def_), Γ.coreFuncs, Γ.coreInstances)

theorem foldl_explicit_view :
    ∀ (l : List (Nat × List Nat)) (k : Nat) (g : Ctx Core3Extern),
      CtxView (l.foldl (fun g q => if g.explicitRes.any (·.1 == q.1) then g
        else g.addExplicitRes q.1 (k :: q.2)) g) = CtxView g
  | [], _, _ => rfl
  | q :: l, k, g => by
    rw [List.foldl_cons, foldl_explicit_view l k]
    split
    · rfl
    · rfl

/-- Exporting an item pushes its entity (the view does not see the export map). -/
theorem exportItem_view (st : DState Core3Extern) (n : String)
    (it : Syntax.SortIdx Syntax.Sort_) (e : Types.Entity Nat Core3Extern) :
    CtxView (st.exportItem n it e).ctx = CtxView (st.ctx.pushEntity e).2 := by
  simp only [DState.exportItem]
  rw [foldl_explicit_view]
  rfl

theorem pushEntity_type_view (Γ : Ctx Core3Extern) (td : TypeDef Nat Core3Extern) :
    CtxView (Γ.pushEntity (.type td)).2 = ((CtxView Γ).1 ++ [td], (CtxView Γ).2) := by
  simp [CtxView, Ctx.pushEntity, Ctx.pushType, Ctx.pushTypeSlot, Ctx.pushList, Ctx.freshToken]

theorem pushEntity_func_view (Γ : Ctx Core3Extern) (ft : Types.FuncType Nat) :
    CtxView (Γ.pushEntity (.func ft)).2 = CtxView Γ := rfl

/-- An unascribed export of item `it` pushes the entity of `it`. -/
theorem chk_export {n : Syntax.ExternName} {it : Syntax.SortIdx Syntax.Sort_}
    (hv : valueIdxs [it] = []) (h : chk sc s (.export_ n it none) = .ok s') :
    ∃ e, itemEntity? s.ctx it = some e ∧ CtxView s'.ctx = CtxView (s.ctx.pushEntity e).2 := by
  simp only [chk, checkDef?, checkExport?, hv] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · next e he =>
        simp only [ascribe?] at h
        split at h
        · split at h
          · split at h
            · simp only [consumeValues?] at h
              cases h
              exact ⟨e, he, exportItem_view _ _ _ _⟩
            · cases h
          · cases h
        · cases h
  · cases h

end Silmaril.Proofs.Wasm.Component.Reference
