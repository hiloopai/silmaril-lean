import Silmaril.Cerberus.Elaboration.Construction.Thms
import Silmaril.Cerberus.Elaboration.Freshness.Thms
import Silmaril.Cerberus.Elaboration.Runtime.Thms
import Silmaril.Cerberus.Elaboration.State.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

private def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
private def longType : Ctype := .mk [] (.basic (.integer (.signed .long)))
private def plain : Qualifiers := ⟨false, false, false⟩
private def constant : Qualifiers := ⟨true, false, false⟩
private def symbol (number : Nat) (description : SymbolDescription := .none) : Sym :=
  ⟨⟨[]⟩, number, description⟩

-- AST shape and annotation order are checked against the source equations.
example : integer 17 = .mk [] () (.val (.object (.integer 17))) := rfl
example : specified (integer 17) =
    .mk [] () (.ctor .specified [.mk [] () (.val (.object (.integer 17)))]) := rfl
example : tuplePattern [.mk [.stmt] (.base (none, .unit))] =
    .ok (.mk [.stmt] (.base (none, .unit))) := rfl
example : tuplePure [.mk [.std "retained"] () (.val .unit)] =
    .ok (.mk [.std "retained"] () (.val .unit)) := rfl
example : tuplePattern [] = .error "[Core_aux.mk_tuple_pat] called with |pats| = 0" := rfl
example : tuplePure [] = .error "Core_aux.mk_tuple_pe []" := rfl
example : maybeAnnotateInteger (.mk [] (.atomic intType)) (integer 0) = integer 0 := rfl
example : negate (.signed .int) (integer 1) = .mk [] ()
    (.op .sub (.mk [.value (.integer (.signed .int))] () (.val (.object (.integer 0))))
      (.mk [] () (.val (.object (.integer 1))))) := rfl
example : unseq [] = skip := rfl
example : unseqEffect [] = .mk [] (.unseq []) := rfl
example : addLocation .unknown
    (.mk [.std "first", .loc (.other "old1"), .stmt, .loc (.other "old2")] (.pure unit)) =
    .mk [.loc .unknown, .std "first", .stmt, .loc (.other "old2")] (.pure unit) := rfl
example : addStandards ["one", "two"] (addStandard "old" skip) =
    .mk [.std "one", .std "two", .std "old"] (.pure unit) := rfl

-- Boundaries are independent of a guessed OCaml host width or AST seed.
example : Freshness.integer (Freshness.initial 100) =
    .ok (0, ⟨⟨[]⟩, 1, 100⟩) := rfl
example : Freshness.integer ⟨⟨[1, 2]⟩, 7, 7⟩ =
    .ok (7, ⟨⟨[1, 2]⟩, 8, 7⟩) := rfl
example : Freshness.integer ⟨⟨[1, 2]⟩, 8, 7⟩ = .error .exhausted := rfl
example : Freshness.prettyWithId (fun n => toString n) ⟨⟨[1, 2]⟩, 7, 7⟩ =
    .ok (⟨⟨[1, 2]⟩, 7, .id "7"⟩, ⟨⟨[1, 2]⟩, 8, 7⟩) := by decide

-- Exact SD_Id matching and first-match failure, without invented arity checks.
example : Runtime.fetchSymbol [symbol 0 (.cnId "f"), symbol 1 (.id "f"), symbol 2 (.id "f")] "f" =
    .ok (symbol 1 (.id "f")) := by decide
example : Runtime.standardCall
    [(symbol 0 (.id "f"), .procedureDecl .unknown .unit []),
     (symbol 1 (.id "f"), .function .unit [] unit)] "f" [] =
    .error "[Translate_effect.E.mk_stdcall] `f' is not a Core standard function." := rfl
example : Runtime.standardCall [(symbol 1 (.id "f"), .function .unit [] unit)] "f" [integer 9] =
    .ok (.mk [] () (.call (.sym (symbol 1 (.id "f"))) [integer 9])) := rfl

private def context (backend : String := "Driver") : State.Context :=
  State.initial ⟨⟨[4]⟩, 10, 100⟩ .normal backend

private def compound (number : Nat) : State.CompoundLiteral :=
  (.unknown, .other "fixture", symbol number, false, intType)

private def scopeScenario : State.ElabM (List State.ConstAlias × List State.CompoundLiteral × List Sym) :=
  State.withBlockObjects [(symbol 1, constant, intType), (symbol 2, plain, intType),
      (symbol 3, constant, longType)] do
    State.registerCompoundLiteral .unknown (.other "fixture") (symbol 77) false intType
    State.getVisibleObjects

private def beforeScope : State.Context :=
  let base := context
  {base with effects := {base.effects with
    visibleObjects := [[symbol 99]]
    compoundLiterals := [compound 88]}}

-- Left-to-right allocation, reverse const alias result, original scope order.
example : (State.run scopeScenario beforeScope).1.map
    (fun (aliases, _, visible) =>
      (aliases.map (fun (original, _, _, aliasSymbol) => (original.number, aliasSymbol.number)),
       visible.map Sym.number)) = .ok ([(3, 11), (1, 10)], [1, 2, 3, 99]) := by decide

-- Body compounds are returned; prior compounds and outer scope are restored.
example : (State.run scopeScenario beforeScope).1.map
    (fun (_, compounds, _) => compounds.map (fun (_, _, sym, _, _) => sym.number)) = .ok [77] := by decide
example : (State.run scopeScenario beforeScope).2.effects.compoundLiterals.map
    (fun (_, _, sym, _, _) => sym.number) = [88] := by decide
example : (State.run scopeScenario beforeScope).2.effects.visibleObjects.map
    (List.map Sym.number) = [[99]] := by decide
example : (State.run scopeScenario beforeScope).2.freshness.next = 12 := by decide

-- Scope exit keeps both type and alias maps; descriptions do not affect lookup.
example : Map.lookup (symbol 3 (.id "diagnostic change"))
    (State.run scopeScenario beforeScope).2.effects.visibleObjectTypes = some (constant, longType) := rfl
example : (Map.lookup (symbol 1 (.id "renamed"))
    (State.run scopeScenario beforeScope).2.effects.cheriConstAliases).map Sym.number = some 10 := by decide

-- Pop the body's current head, rather than replacing the stack with its old value.
private def changedScope : State.ElabM (List State.ConstAlias × List State.CompoundLiteral × Unit) :=
  State.withBlockObjects [] do
    State.modifyEffects fun effects => {effects with visibleObjects := [[symbol 5], [symbol 6]]}
example : (State.run changedScope (context)).2.effects.visibleObjects.map
    (List.map Sym.number) = [[6]] := by decide

private def brokenScope : State.ElabM (List State.ConstAlias × List State.CompoundLiteral × Unit) :=
  State.withBlockObjects [] do
    State.modifyEffects fun effects => {effects with visibleObjects := []}
example : (State.run brokenScope (context)).1 =
    .error (.message "[Translation.E.with_block_objects] found an ill-formed scope stack.") := rfl

-- A non-CN marker consumes an ID but does not resolve missing object types.
private def missingVisible (backend : String) : State.Context :=
  let base := context backend
  {base with effects := {base.effects with visibleObjects := [[symbol 42]]}}
example : (State.run State.recordObjectTypesMarker (missingVisible "Driver")).1 = .ok 10 := by decide
example : (State.run State.recordObjectTypesMarker (missingVisible "Driver")).2.freshness.next = 11 := by decide
example : Map.lookup 10
    (State.run State.recordObjectTypesMarker (missingVisible "Driver")).2.effects.visibleObjectTypeMarkers = none := by decide
example : (State.run State.recordObjectTypesMarker (missingVisible "Cn")).1 =
    .error (.missingObjectType (symbol 42)) := by decide

private def markerInScope : State.ElabM (List State.ConstAlias × List State.CompoundLiteral × Nat) :=
  State.withBlockObjects [(symbol 1, plain, intType), (symbol 2, plain, longType)]
    State.recordObjectTypesMarker
example : (Map.lookup 10 (State.run markerInScope (context "Cn")).2.effects.visibleObjectTypeMarkers).map
    (List.map (fun (sym, _) => sym.number)) = some [1, 2] := by decide

-- Registration prepends; tracking returns that order and clears on success.
private def temporaries : State.ElabM (List (State.WrappedSymbol × Ctype) × Unit) :=
  State.trackTemporaryObjects do
    let first ← State.wrappedFreshSymbol .unit
    State.registerTemporaryObject first intType
    let second ← State.wrappedFreshSymbol .unit
    State.registerTemporaryObject second longType
example : (State.run temporaries (context)).1.map
    (fun (objects, _) => objects.map (fun (wrapped, _) => wrapped.symbol.number)) = .ok [11, 10] := by decide
example : (State.run temporaries (context)).2.effects.temporaryObjects.isEmpty = true := by decide

private def nestedTracking : State.ElabM Unit := do
  let pointer ← State.wrappedFreshSymbol .unit
  State.registerTemporaryObject pointer intType
  let _ ← State.trackTemporaryObjects (pure ())
  pure ()
example : (State.run nestedTracking (context)).1 =
    .error (.message "[Translation.E.track_temporary_objects]") := by decide

private def errors : State.ElabM Nat := State.runErrors do
  State.recordError "oldest"
  State.recordError "newest"
  pure 42
example : (State.run errors (context)).1 = .error (.message "oldest") := by decide
example : (State.run errors (context)).2.effects.errors = ["newest", "oldest"] := by decide

#print axioms Freshness.consecutive_keys_ne
#print axioms Freshness.two_descriptions
