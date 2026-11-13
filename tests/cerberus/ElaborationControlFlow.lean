import Silmaril.Cerberus.Elaboration.ControlFlow.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus
open Silmaril.Cerberus.Elaboration
open Construction

private def symbol (index : Nat) : Sym := ⟨⟨[]⟩, index, .none⟩
private def prepared : State.WrappedSymbol :=
  ⟨symbol 99, symbolPattern (symbol 99) .boolean, symbolPure (symbol 99)⟩
private def context : State.Context := State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"
private def statementLocation : Loc := .region "if.c" 2 1 "if.c" 2 30
private def conditionLocation : Loc := .region "if.c" 2 5 "if.c" 2 6
private def input : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.unsigned .int))))) [.marker 7]
    conditionLocation (.ident (symbol 10))

/-- These actual-Core sentinel callbacks test argument transport and monadic
construction order. They do not stand in for a source-condition semantics or
assert that the sentinels implement general expression/statement translation. -/
private def marked (value : Sym) : State.ElabM Effect := do
  let marker ← State.recordObjectTypesMarker
  return .mk [.markerObjectTypes marker] (.pure (symbolPure value))

private def wrappedCondition (location : Loc) (test : Ail.TypedExpression) : State.ElabM Effect := do
  unless location = statementLocation do throw (.message "wrong enclosing statement location")
  let .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [.marker 7] expressionLocation
      (.binary (.mk (.rvalue (.basic (.integer (.concrete (.unsigned .int))))) [.marker 7] leftLocation
          (.ident left)) .eq
        (.mk (.rvalue (.basic (.integer (.concrete (.unsigned .int))))) [.marker 7] zeroLocation
          (.const (.integer (.iconstant 0 .octal none))))) := test
    | throw (.message "wrong actual TestEq typed-Ail syntax")
  unless left = symbol 10 ∧ expressionLocation = conditionLocation ∧
      leftLocation = conditionLocation ∧ zeroLocation = conditionLocation do
    throw (.message "wrong condition/zero provenance")
  let core ← marked (symbol 20)
  return .mk [.std "§6.5#2"] (.bound core)

private def output := State.run
  (ControlFlow.integerIf Target.pinnedApple Target.emptyEnvironment prepared statementLocation input
    wrappedCondition (marked (symbol 30)) (marked (symbol 40))) context

private def shape : Except State.Error Effect → Option (Nat × Nat × Effect × Effect × Pure × Effect × Effect)
  | .ok (.mk [] (.sseq (.mk [] (.base (some test, .loaded .integer))) coreTest
      (.mk [] (.sseq (.mk [] (.base (some choice, .boolean))) decision
        (.mk [] (.if_ condition yes no)))))) =>
      some (test.number, choice.number, coreTest, decision, condition, yes, no)
  | _ => none

-- The helper consumes only its two remaining binders. The condition action
-- then runs before the two branch actions; both branches are translated once.
example : output.2.freshness.next = 105 := by cbv
example : shape output.1 = some (100, 99,
    .mk [.std "§6.5#2"] (.bound (.mk [.markerObjectTypes 102] (.pure (symbolPure (symbol 20))))),
    ControlFlow.decision ⟨
      ⟨symbol 100, symbolPattern (symbol 100) (.loaded .integer), symbolPure (symbol 100)⟩,
      ⟨symbol 101, symbolPattern (symbol 101) (.object .integer), symbolPure (symbol 101)⟩⟩,
    symbolPure (symbol 99),
    .mk [.markerObjectTypes 103] (.pure (symbolPure (symbol 30))),
    .mk [.markerObjectTypes 104] (.pure (symbolPure (symbol 40)))) := by cbv
example : output.2.effects.visibleObjects = [[]] := by cbv
example : ControlFlow.CanonicalBoolean prepared := ControlFlow.canonicalBoolean _

-- The synthesized expression tests equality with zero. Its specified result
-- chooses then when it is not object integer one. Unspecified results keep
-- both actual Core Boolean alternatives, rather than choosing at elaboration.
example : ControlFlow.specifiedDecision (symbolPure (symbol 101)) =
    .mk [] (.pure (.mk [] () (.if_
      (.mk [] () (.not (.mk [] () (.op .eq (symbolPure (symbol 101))
        (.mk [] () (.val (.object (.integer 1))))))))
      (.mk [] () (.val .true)) (.mk [] () (.val .false))))) := rfl
example : ControlFlow.unspecifiedDecision =
    .mk [] (.nd [.mk [] (.pure (.mk [] () (.val .true))),
      .mk [] (.pure (.mk [] () (.val .false)))]) := rfl

-- Outside the integer synthesis domain there is explicit rejection. Freshness
-- exhaustion prevents callback actions; there is no invented successful output.
private def pointerInput : Ail.TypedExpression :=
  .mk (.rvalue (.pointer ⟨false, false, false⟩ (.mk [] .void))) [] conditionLocation (.const .null)
example : (State.run (ControlFlow.integerIf Target.pinnedApple Target.emptyEnvironment
    prepared statementLocation pointerInput wrappedCondition (marked (symbol 30))
    (marked (symbol 40))) context).1.isOk = false := by cbv
example : (State.run (ControlFlow.integerIf Target.pinnedApple Target.emptyEnvironment
    prepared statementLocation input wrappedCondition (marked (symbol 30)) (marked (symbol 40)))
    {context with freshness := {context.freshness with maximum := 100}}).1 =
    .error (.freshness .exhausted) := by cbv
example : (State.run (ControlFlow.integerIf Target.pinnedApple Target.emptyEnvironment
    prepared statementLocation input wrappedCondition (marked (symbol 30)) (marked (symbol 40)))
    {context with freshness := {context.freshness with maximum := 100}}).2.freshness.next = 101 := by cbv

#print axioms ControlFlow.canonicalBoolean
#print axioms ControlFlow.decision_shape
#print axioms ControlFlow.finish_shape
