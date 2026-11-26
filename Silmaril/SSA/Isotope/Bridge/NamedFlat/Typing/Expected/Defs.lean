module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Defs

/-! # Check written injections and case operands -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open LetCase.LocallyNameless (Tm)

universe u v
variable {Base : Type u} {F : Type v} {labels : Nat} [DecidableEq Base] [HasTy F (Ty Base)]

/-- Optional types for unary binders, addressed by child position in the
written syntax. Variable and label renaming leave these positions intact. -/
abbrev BindingTypes (τ : Type u) := List Nat → Option τ

namespace BindingTypes
variable {τ : Type u}

def empty : BindingTypes τ := fun _ => none

def child (hints : BindingTypes τ) (index : Nat) : BindingTypes τ :=
  fun path => hints (index :: path)

def node (type : Option τ) (first second third : BindingTypes τ) : BindingTypes τ
  | [] => type
  | 0 :: path => first path
  | 1 :: path => second path
  | 2 :: path => third path
  | _ => none

end BindingTypes

/-- Infer an expression using expected sum types and optional unary-binder
ascriptions. An ascribed initializer is checked at its supplied type. -/
def inferAtWith : {n : Nat} → BoundCtx (Ty Base) n → Option (Ty Base) →
    BindingTypes (Ty Base) → Tm Empty F n → Option (Ty Base)
  | _, ctx, _, _, .bv i => some (ctx.get i)
  | _, _, _, _, .unit => some .unit
  | _, ctx, expected, hints, .pair a b =>
    let (left, right) := match expected with
      | some (.product A B) => (some A, some B)
      | _ => (none, none)
    (inferAtWith ctx left (hints.child 0) a).bind fun A =>
      (inferAtWith ctx right (hints.child 1) b).map (.product A)
  | _, ctx, _, hints, .op f a =>
    if inferAtWith ctx (some (instrSrc f)) (hints.child 0) a = some (instrSrc f) then
      some (instrTrg f)
    else none
  | _, ctx, expected, hints, .let₁ value body =>
    (inferAtWith ctx (hints []) (hints.child 0) value).bind fun A =>
      if (hints []).getD A = A then inferAtWith (.snoc ctx A) expected (hints.child 1) body else none
  | _, ctx, expected, hints, .let₂ value body => do
    let .product A B ← inferAtWith ctx none (hints.child 0) value | none
    inferAtWith (.snoc (.snoc ctx A) B) expected (hints.child 1) body
  | _, ctx, some (.coprod A B), hints, .inl a =>
    if inferAtWith ctx (some A) (hints.child 0) a = some A then some (.coprod A B) else none
  | _, ctx, some (.coprod A B), hints, .inr b =>
    if inferAtWith ctx (some B) (hints.child 0) b = some B then some (.coprod A B) else none
  | _, ctx, expected, hints, .case test left right => do
    let .coprod A B ← inferAtWith ctx none (hints.child 0) test | none
    let C ← inferAtWith (.snoc ctx A) expected (hints.child 1) left
    if inferAtWith (.snoc ctx B) expected (hints.child 2) right = some C ∧ expected.getD C = C then
      some C
    else none
  | _, _, _, _, _ => none

def inferAt {n : Nat} (ctx : BoundCtx (Ty Base) n) (expected : Option (Ty Base))
    (expr : Tm Empty F n) : Option (Ty Base) :=
  inferAtWith ctx expected .empty expr

def inferExpected {n : Nat} (ctx : BoundCtx (Ty Base) n) (expr : Tm Empty F n) : Option (Ty Base) :=
  inferAt ctx none expr

/-- Check numbered transfers and binders against their exact types.
A unary binder may supply an expected type for its initializer. -/
def checkBodyWith (types : Fin labels → Ty Base) :
    {n : Nat} → BoundCtx (Ty Base) n → BindingTypes (Ty Base) → LambdaSSA.Flat F labels n → Bool
  | _, ctx, hints, .br label arg =>
    decide (inferAtWith ctx (some (types label)) (hints.child 0) arg = some (types label))
  | _, ctx, hints, .let₁ op rest =>
    match inferAtWith ctx (hints []) (hints.child 0) op with
    | some A => decide ((hints []).getD A = A) && checkBodyWith types (.snoc ctx A) (hints.child 1) rest
    | none => false
  | _, ctx, hints, .let₂ op rest =>
    match inferAtWith ctx none (hints.child 0) op with
    | some (.product A B) => checkBodyWith types (.snoc (.snoc ctx A) B) (hints.child 1) rest
    | _ => false
  | _, ctx, hints, .case op left right =>
    match inferAtWith ctx none (hints.child 0) op with
    | some (.coprod A B) =>
      checkBodyWith types (.snoc ctx A) (hints.child 1) left &&
        checkBodyWith types (.snoc ctx B) (hints.child 2) right
    | _ => false

def checkBodyExpected (types : Fin labels → Ty Base) {n : Nat} (ctx : BoundCtx (Ty Base) n)
    (body : LambdaSSA.Flat F labels n) : Bool :=
  checkBodyWith types ctx .empty body

/-- Verify a complete emitted graph with its recorded binder ascriptions. -/
def checkWithBindings {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base) (external : Fin exits → Ty Base)
    (entry : BindingTypes (Ty Base)) (rows : Fin blocks → BindingTypes (Ty Base)) : Bool :=
  let types := SSA.FiniteSum.append internal external
  checkBodyWith types captures entry graph.entry &&
    (List.finRange blocks).all fun i => checkBodyWith types (.snoc captures (internal i)) (rows i) (graph.block i)

/-- Check the written graph without supplied binder annotations. -/
def checkExpected {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base)
    (external : Fin exits → Ty Base) : Bool :=
  checkWithBindings graph captures internal external .empty (fun _ => .empty)

end Silmaril.Isotope.Bridge.NamedFlat
