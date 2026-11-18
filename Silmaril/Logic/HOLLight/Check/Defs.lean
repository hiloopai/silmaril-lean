module

public import Silmaril.Logic.HOLLight.Typing

/-!
# A HOL Light type checker

`Tm.typeOf? sig Γ t` computes the type of a term in the bound context `Γ`, or `none`. It is
**sound and complete** for `HasType` (`Thms`: `typeOf?_eq_some_iff`): it returns `some A` exactly
when `HasType sig Γ t A`, so `none` means the term has no type. Typing is unique
(`HasType.unique`), so there is no choice to make.

Well-formedness of types (`Ty.WellFormed`) and scoping (`Ty.Scoped`) are decided by the boolean
checks `Ty.wf?` and `Ty.scoped?`.
-/

@[expose] public section

namespace Silmaril.Logic.HOLLight

mutual
/-- Decide `Ty.WellFormed ops`. -/
def Ty.wf? (ops : List Nat) : Ty → Bool
  | .var _ | .bool | .ind => true
  | .arr A B => Ty.wf? ops A && Ty.wf? ops B
  | .app c args => ops[c]? == some args.length && Ty.wfList? ops args
/-- Decide `Ty.WellFormedList ops`. -/
def Ty.wfList? (ops : List Nat) : List Ty → Bool
  | [] => true
  | A :: args => Ty.wf? ops A && Ty.wfList? ops args
end

mutual
/-- Decide `Ty.Scoped n`. -/
def Ty.scoped? (n : Nat) : Ty → Bool
  | .var i => decide (i < n)
  | .bool | .ind => true
  | .arr A B => Ty.scoped? n A && Ty.scoped? n B
  | .app _ args => Ty.scopedList? n args
/-- Decide `Ty.ScopedList n`. -/
def Ty.scopedList? (n : Nat) : List Ty → Bool
  | [] => true
  | A :: args => Ty.scoped? n A && Ty.scopedList? n args
end

/-- The type of a constant, or `none`. -/
def Const.typeOf? (sig : Signature) : Const → Option Ty
  | .eq A => if A.wf? sig.tyOps then some (.arr A (.arr A .bool)) else none
  | .select A => if A.wf? sig.tyOps then some (.arr (.arr A .bool) A) else none
  | .user c As => match sig.consts[c]? with
    | some s =>
      if s.body.wf? sig.tyOps && s.body.scoped? s.arity && As.length == s.arity &&
          As.all (Ty.wf? sig.tyOps) then some (Ty.instantiate As s.body) else none
    | none => none

/-- **The type of a term** in the bound context `Γ`, or `none`. -/
def Tm.typeOf? (sig : Signature) : List Ty → Tm → Option Ty
  | Γ, .bvar i => Γ[i]?.bind fun A => if A.wf? sig.tyOps then some A else none
  | _, .fvar _ A => if A.wf? sig.tyOps then some A else none
  | _, .const c => c.typeOf? sig
  | Γ, .app f x => match Tm.typeOf? sig Γ f, Tm.typeOf? sig Γ x with
    | some (.arr A B), some A' => if A = A' then some B else none
    | _, _ => none
  | Γ, .lam A b => if A.wf? sig.tyOps then (Tm.typeOf? sig (A :: Γ) b).map (.arr A) else none

end Silmaril.Logic.HOLLight
