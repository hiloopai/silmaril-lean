module

public import Silmaril.Cerberus.Elaboration.ControlTests.Defs
public import Silmaril.Cerberus.Elaboration.Constants.Defs

/-! The actual integer `if` branch of pinned `translation.lem:3773–3798`.
The caller supplies its already prepared Boolean wrapper; source construction
scheduling belongs to that caller. This helper allocates the remaining two
binders, synthesizes the actual typed-Ail TestEq-zero expression, invokes the
wrapped-expression callback, then translates both statement children. It adds
no outer statement annotations and assumes no observed condition result.
-/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.ControlFlow
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

/-- Exact invariant supplied by the source's prepared Boolean allocation.
`integerIf` preserves those fields; the scheduling/calling layer owns this
invariant and allocation provenance rather than the control constructor. -/
def CanonicalBoolean (prepared : State.WrappedSymbol) : Prop :=
  prepared.pattern = symbolPattern prepared.symbol .boolean ∧
  prepared.expression = symbolPure prepared.symbol

structure Binders where
  test : State.WrappedSymbol
  specified : State.WrappedSymbol

/-- After the prepared Boolean, allocate loaded integer, then object integer. -/
def freshBinders : State.ElabM Binders := do
  let test ← State.wrappedFreshSymbol (.loaded .integer)
  let specified ← State.wrappedFreshSymbol (.object .integer)
  return ⟨test, specified⟩

/-- The source test is `condition == 0`, so select the then branch precisely
when that specified comparison result differs from object integer one. -/
def specifiedDecision (value : Pure) : Effect :=
  pureEffect (ifPure (notPure (operation .eq value (integer 1)))
    (boolean true) (boolean false))

/-- Preserve the source's actual nondeterministic Core choice for unspecified
test results. No choice is made while constructing the Core expression. -/
def unspecifiedDecision : Effect :=
  nondeterministic [pureEffect (boolean true), pureEffect (boolean false)]

def decision (binders : Binders) : Effect :=
  caseEffect binders.test.expression
    [(specifiedPattern binders.specified.pattern, specifiedDecision binders.specified.expression),
     (unspecifiedPattern (wildcard .ctype), unspecifiedDecision)]

/-- Raw source Core shape: test binding, Boolean decision binding, actual Eif.
Neither child translation nor condition evaluation is replaced by this syntax
boundary. The supplied successful child computations construct its operands. -/
def finish (prepared : State.WrappedSymbol) (binders : Binders)
    (condition yes no : Effect) : Effect :=
  strongSequence binders.test.pattern condition
    (strongSequence prepared.pattern (decision binders)
      (ifEffect prepared.expression yes no))

/-- Integer control lowering with an explicitly prepared canonical Boolean.
The wrapped-condition callback receives the actual enclosing statement location
as well as the synthesized expression, retaining the source's block-expression
context boundary. It must perform actual wrapped expression translation. Parent
marker/location/statement/attribute annotations remain caller-owned. -/
def integerIf (config : Target.Config) (env : Target.Environment)
    (prepared : State.WrappedSymbol) (location : Loc) (input : Ail.TypedExpression)
    (wrappedCondition : Loc → Ail.TypedExpression → State.ElabM Effect)
    (yes no : State.ElabM Effect) : State.ElabM Effect := do
  let binders ← freshBinders
  let test ← Constants.liftResult (ControlTests.equalZero config env input)
  let condition ← wrappedCondition location test
  let coreYes ← yes
  let coreNo ← no
  return finish prepared binders condition coreYes coreNo

end Silmaril.Cerberus.Elaboration.ControlFlow
