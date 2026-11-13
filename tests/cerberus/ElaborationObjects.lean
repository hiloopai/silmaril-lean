import Silmaril.Cerberus.Elaboration.MemoryActions.Thms
import Silmaril.Cerberus.Elaboration.ObjectExpressions.Thms
import Silmaril.Cerberus.Elaboration.Lifetimes.Thms
import Silmaril.Cerberus.Elaboration.LocalObjects.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus
open Silmaril.Cerberus.Elaboration
open Construction

private def functionSymbol : Sym := ⟨⟨[]⟩, 506, .id "main"⟩
private def objectSymbol : Sym := ⟨⟨[]⟩, 508, .objectAddress "x"⟩
private def enumSymbol : Sym := ⟨⟨[]⟩, 502, .id "E"⟩
private def labelSymbol : Sym := ⟨⟨[]⟩, 510, .id "ret_510"⟩
private def blockLocation : Loc := .region "enum-return.c" 1 34 "enum-return.c" 1 61
private def identifierLocation : Loc := .region "enum-return.c" 1 43 "enum-return.c" 1 44
private def expressionLocation : Loc := .region "enum-return.c" 1 57 "enum-return.c" 1 58
private def enumType : Ctype := .mk [.loc (.region "enum-return.c" 1 36 "enum-return.c" 1 42)]
  (.basic (.integer (.enum enumSymbol)))
private def qualifiers : Qualifiers := ⟨false, false, false⟩
private def binding : Ail.Bindings :=
  [(objectSymbol, ((identifierLocation, .automatic, false), none, qualifiers, enumType))]
private def context : State.Context := State.initial ⟨⟨[]⟩, 511, 1000⟩ .normal "Driver"
private def types : Target.Environment := ⟨Map.ofList [(enumSymbol, .unsigned .int)]⟩
private def literal : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) []
    (.region "enum-return.c" 1 47 "enum-return.c" 1 48) (.const (.integer (.iconstant 7 .decimal none)))
private def runtimeSymbol : Sym := ⟨⟨[]⟩, 10, .id "conv_loaded_int"⟩
private def runtime : List Runtime.Binding :=
  [(runtimeSymbol, .function (.loaded .integer) [] (Constants.loadedInteger 0))]

-- A real object lvalue remains an object pointer; the actual enum CType and
-- its source annotations reach the positive load action unchanged.
example : (State.run (ObjectExpressions.rvalue Target.pinnedApple expressionLocation enumType
    (ObjectExpressions.identifier Target.pinnedApple objectSymbol)) context).1 =
    .ok (weakSequence (symbolPattern ⟨⟨[]⟩, 511, .none⟩ (.object .pointer))
      (pureEffect (symbolPure objectSymbol))
      (MemoryActions.load expressionLocation (ailCtype enumType) (symbolPure ⟨⟨[]⟩, 511, .none⟩) .na)) := by cbv
example : (State.run (ObjectExpressions.rvalue Target.pinnedApple expressionLocation enumType
    (ObjectExpressions.identifier Target.pinnedApple objectSymbol)) context).2.freshness.next = 512 := by cbv
example : ObjectExpressions.loadOrder (.mk [] (.atomic enumType)) = .seqCst := rfl

-- Allocation uses the caller's source function identity; block exit still
-- emits a kill even when an earlier return will have killed the same object.
example : (State.run (LocalObjects.block Target.pinnedApple functionSymbol blockLocation binding
    (pure [])) context).1 = .ok
    (strongSequence (symbolPattern objectSymbol (.object .pointer))
      (MemoryActions.create blockLocation (alignof (ailCtype enumType)) (ailCtype enumType)
        (.source identifierLocation [functionSymbol, objectSymbol]))
      (strongSequence (wildcard .unit) (MemoryActions.staticKill blockLocation enumType
        (symbolPure objectSymbol)) skip)) := by cbv
example : (State.run (LocalObjects.block Target.pinnedApple functionSymbol blockLocation binding
    (pure [])) context).2.freshness.next = 511 := by cbv
example : (State.run (LocalObjects.block Target.pinnedApple functionSymbol blockLocation binding
    (pure [])) context).2.effects.visibleObjects = [[]] := by cbv

-- Resolve a local through the real block scope; retain its enum CType at the
-- runtime conversion and its existing object symbol at the store action.
private def initialized : State.ElabM Effect := LocalObjects.block Target.pinnedApple
  functionSymbol blockLocation binding do
    let core ← LocalObjects.initializer Target.pinnedApple types runtime blockLocation
      (Constants.wrappedExpression Target.pinnedApple types) objectSymbol (some literal)
    return [core]
example : (State.run initialized context).1.isOk = true := by cbv
example : (State.run initialized context).2.freshness.next = 512 := by cbv
example : (State.run (State.withBlockObjects (LocalObjects.objectBindings binding) do
    LocalObjects.initializer Target.pinnedApple types runtime blockLocation
      (Constants.wrappedExpression Target.pinnedApple types) objectSymbol none) context).1 =
    .ok ([], [], addStandard "§6.2.4#6" (MemoryActions.store blockLocation false
      (ailCtype enumType) (symbolPure objectSymbol) (unspecified enumType) .na)) := by cbv
example : (State.run (State.withBlockObjects (LocalObjects.objectBindings binding) do
    LocalObjects.initializer Target.pinnedApple types [] blockLocation
      (Constants.wrappedExpression Target.pinnedApple types) objectSymbol (some literal)) context).1.isOk = false := by cbv

-- Captured scopes are innermost first. Transfer identity ignores diagnostic
-- descriptions, and a return emits exactly the captured static kill then run.
private def renamedObject : Sym := {objectSymbol with description := .id "diagnostic-only"}
example : Lifetimes.killed [(objectSymbol, enumType)] [(renamedObject, enumType)] = [] := by cbv
example : Lifetimes.created [(objectSymbol, enumType)] [(renamedObject, enumType)] = [] := by cbv
example : Lifetimes.returnRun expressionLocation labelSymbol [(objectSymbol, enumType)] [integer 7] =
    strongSequence (wildcard .unit) (MemoryActions.staticKill expressionLocation enumType
      (symbolPure objectSymbol)) (Construction.run labelSymbol [integer 7]) := rfl
example : (State.run (State.withBlockObjects (LocalObjects.objectBindings binding)
    Lifetimes.captureVisible) context).1 = .ok ([], [], [(objectSymbol, enumType)]) := by cbv

-- Const aliases consume an ID even on Driver; store-lock remains a separate
-- source qualifier. Unsupported cursor information and CHERI reject explicitly.
private def constBinding : Ail.Bindings :=
  [(objectSymbol, ((identifierLocation, .automatic, false), none, {qualifiers with const := true}, enumType))]
example : (State.run (LocalObjects.block Target.pinnedApple functionSymbol blockLocation constBinding
    (pure [])) context).2.freshness.next = 512 := by cbv
example : (LocalObjects.blockActionLocation .unknown).isOk = false := rfl
example : LocalObjects.blockActionLocation (.point "x.c" 2 3) = .ok (.region "x.c" 2 3 "x.c" 2 3) := rfl
example : (State.run (LocalObjects.block {Target.pinnedApple with cheri := true}
    functionSymbol blockLocation binding (pure [])) context).1.isOk = false := by cbv

#print axioms MemoryActions.load_type
#print axioms Lifetimes.contains_same_key
#print axioms LocalObjects.singleton_create
