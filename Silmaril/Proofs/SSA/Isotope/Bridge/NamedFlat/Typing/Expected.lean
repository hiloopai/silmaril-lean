module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Expected.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open LetCase.LocallyNameless (Tm HasType)

universe u v
variable {Base : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)]

private theorem inferAtWith_sound {n : Nat} (ctx : BoundCtx (Ty Base) n) (expr : Tm Empty F n)
    {expected : Option (Ty Base)} {hints : BindingTypes (Ty Base)} {A : Ty Base}
    (inferred : inferAtWith ctx expected hints expr = some A) :
    HasType F .nil ctx expr A := by
  induction expr generalizing expected hints A with
  | fv x => nomatch x
  | bv => cases inferred; exact .bv
  | unit => cases inferred; exact .unit
  | pair a b ihA ihB =>
    simp only [inferAtWith, Option.bind_eq_some_iff, Option.map_eq_some_iff] at inferred
    obtain ⟨_, ha, _, hb, rfl⟩ := inferred
    exact .pair (ihA ctx ha) (ihB ctx hb)
  | op f a ih =>
    by_cases typed : inferAtWith ctx (some (instrSrc f)) (hints.child 0) a = some (instrSrc f)
    · have eq : instrTrg f = A := by simpa [inferAtWith, typed] using inferred
      rw [← eq]
      exact .op (ih ctx typed)
    · simp [inferAtWith, typed] at inferred
  | let₁ value body ihValue ihBody =>
    simp only [inferAtWith, Option.bind_eq_some_iff] at inferred
    obtain ⟨B, valueType, bodyType⟩ := inferred
    split at bodyType
    · exact .let₁ (ihValue ctx valueType) (ihBody (.snoc ctx B) bodyType)
    · cases bodyType
  | let₂ value body ihValue ihBody =>
    cases valueType : inferAtWith ctx none (hints.child 0) value with
    | none => simp [inferAtWith, valueType] at inferred
    | some product =>
      cases product <;> simp only [inferAtWith, valueType] at inferred
      case product B C => exact .let₂ (ihValue ctx valueType) (ihBody (.snoc (.snoc ctx B) C) inferred)
      all_goals cases inferred
  | inl value ih =>
    cases expected with
    | none => cases inferred
    | some ty =>
      cases ty <;> simp only [inferAtWith] at inferred
      case coprod left right =>
        split at inferred
        · cases inferred
          exact .inl (ih ctx (by assumption))
        · cases inferred
      all_goals cases inferred
  | inr value ih =>
    cases expected with
    | none => cases inferred
    | some ty =>
      cases ty <;> simp only [inferAtWith] at inferred
      case coprod left right =>
        split at inferred
        · cases inferred
          exact .inr (ih ctx (by assumption))
        · cases inferred
      all_goals cases inferred
  | case test left right ihTest ihLeft ihRight =>
    cases checked : inferAtWith ctx none (hints.child 0) test with
    | none => simp [inferAtWith, checked] at inferred
    | some ty =>
      cases ty <;> simp only [inferAtWith, checked] at inferred
      case coprod a b =>
        change ((inferAtWith (.snoc ctx a) expected (hints.child 1) left).bind fun c =>
          if inferAtWith (.snoc ctx b) expected (hints.child 2) right = some c ∧ expected.getD c = c then some c else none) = some A at inferred
        obtain ⟨c, arm, next⟩ := Option.bind_eq_some_iff.mp inferred
        split at next
        · rename_i rightTyped
          cases next
          exact .case (ihTest ctx checked) (ihLeft (.snoc ctx a) arm) (ihRight (.snoc ctx b) rightTyped.1)
        · cases next
      all_goals cases inferred
  | abort => cases inferred

private theorem checkBodyWith_sound {labels n : Nat} (types : Fin labels → Ty Base)
    (ctx : BoundCtx (Ty Base) n) (hints : BindingTypes (Ty Base)) (body : LambdaSSA.Flat F labels n)
    (accepted : checkBodyWith types ctx hints body = true) :
    LambdaSSA.Flat.HasType types ctx body := by
  induction body generalizing hints with
  | br label arg =>
    exact .br (inferAtWith_sound ctx arg (of_decide_eq_true accepted))
  | let₁ op rest ih =>
    cases inferred : inferAtWith ctx (hints []) (hints.child 0) op with
    | none => simp [checkBodyWith, inferred] at accepted
    | some A =>
      simp only [checkBodyWith, inferred, Bool.and_eq_true] at accepted
      exact .let₁ (inferAtWith_sound ctx op inferred) (ih _ _ accepted.2)
  | let₂ op rest ih =>
    cases inferred : inferAtWith ctx none (hints.child 0) op with
    | none => simp [checkBodyWith, inferred] at accepted
    | some A =>
      cases A <;> simp only [checkBodyWith, inferred, Bool.false_eq_true] at accepted
      case product A B => exact .let₂ (inferAtWith_sound ctx op inferred) (ih _ _ accepted)
  | case op left right ihLeft ihRight =>
    cases inferred : inferAtWith ctx none (hints.child 0) op with
    | none => simp [checkBodyWith, inferred] at accepted
    | some A =>
      cases A <;> simp only [checkBodyWith, inferred, Bool.false_eq_true, Bool.and_eq_true] at accepted
      case coprod A B =>
        exact .case (inferAtWith_sound ctx op inferred) (ihLeft _ _ accepted.1) (ihRight _ _ accepted.2)

theorem checkWithBindings_sound {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base) (external : Fin exits → Ty Base)
    (entry : BindingTypes (Ty Base)) (rows : Fin blocks → BindingTypes (Ty Base))
    (accepted : checkWithBindings graph captures internal external entry rows = true) :
    graph.HasType captures internal external := by
  simp only [checkWithBindings, Bool.and_eq_true, List.all_eq_true] at accepted
  exact ⟨checkBodyWith_sound _ _ _ _ accepted.1, fun i => checkBodyWith_sound _ _ _ _ (accepted.2 i (by simp))⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat
