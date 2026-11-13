import Silmaril.Cerberus.Elaboration.Scheduling.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

private def context : State.Context := State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"
private def mark (text : String) : State.ElabM Unit :=
  State.modifyEffects fun effects => {effects with errors := effects.errors ++ [text]}
private def observed {α : Type} (action : State.ElabM α) :=
  let (result, after) := State.run action context
  (result, after.freshness.next, after.effects.errors, after.backend)

-- A deferred action keeps its ordinary execution and error behavior.
example : observed (Scheduling.execute (Scheduling.defer (do
    mark "action"
    State.freshInteger))) = (.ok 100, 101, ["action"], "Driver") := by cbv
example : observed (Scheduling.execute (Scheduling.defer (do
    mark "before error"
    throw (.message "stop") : State.ElabM Nat))) =
    (.error (.message "stop"), 100, ["before error"], "Driver") := by cbv

private def first : Scheduling.Computation Nat :=
  (do
    let _ ← Scheduling.freshDescription .none
    return (do
      mark "first action"
      State.freshInteger : State.ElabM Nat) : Scheduling.Build (State.ElabM Nat))
private def staged : Scheduling.Computation (Nat × Nat) :=
  Scheduling.bind first fun firstIndex =>
    Scheduling.map (fun wrapped => (firstIndex, wrapped.symbol.number))
      (Scheduling.wrappedFreshSymbol .boolean)
private def prepared : Scheduling.Computation (Nat × Nat) :=
  (do
    let firstAction ← first
    let secondAction ← Scheduling.wrappedFreshSymbol .boolean
    return (do
      let firstIndex ← firstAction
      let second ← secondAction
      return (firstIndex, second.symbol.number) : State.ElabM (Nat × Nat))
    : Scheduling.Build (State.ElabM (Nat × Nat)))

-- Bind constructs its continuation after the first action. Raw Build bind
-- constructs both actions before either executes.
example : observed (Scheduling.execute staged) =
    (.ok (101, 102), 103, ["first action"], "Driver") := by cbv
example : observed (Scheduling.execute prepared) =
    (.ok (102, 101), 103, ["first action"], "Driver") := by cbv

private def callback (text : String) : Scheduling.Computation (Nat × Nat) :=
  (do
    let symbol ← Scheduling.freshDescription (.id text)
    return (do
      mark text
      let executed ← State.freshInteger
      return (symbol.number, executed) : State.ElabM (Nat × Nat))
    : Scheduling.Build (State.ElabM (Nat × Nat)))

-- Callback construction is reversed for a short list, but action execution
-- and returned values stay in input order. Build preserves effects/backend.
example : observed (Scheduling.execute (Scheduling.mapM callback ["a", "b", "c"])) =
    (.ok [(102, 103), (101, 104), (100, 105)], 106, ["a", "b", "c"], "Driver") := by cbv

private def allocate (input : Nat) : Scheduling.Build (Nat × Nat) := do
  let symbol ← Scheduling.freshDescription .none
  return (input, symbol.number)
private def builtAt (counter : Nat) (inputs : List Nat) :=
  let (result, after) := (Scheduling.buildMapAt counter allocate inputs).run context.freshness
  (result, after.next)

-- These small examples distinguish the exact cutoff from an unconditional
-- reverse traversal and from switching the current head to forward order.
example : builtAt 0 [0, 1, 2] = (.ok [(0, 102), (1, 101), (2, 100)], 103) := by cbv
example : builtAt 5000 [0, 1, 2] = (.ok [(0, 102), (1, 100), (2, 101)], 103) := by cbv
example : builtAt 4999 [0, 1, 2, 3] =
    (.ok [(0, 103), (1, 102), (2, 100), (3, 101)], 104) := by cbv

-- Actual wrapper construction keeps symbol, pattern and pure expression.
example : (State.run (Scheduling.execute (Scheduling.wrappedFreshSymbolWith (.id "named") .boolean))
    context).1 = .ok
      ⟨⟨⟨[]⟩, 100, .id "named"⟩, symbolPattern ⟨⟨[]⟩, 100, .id "named"⟩ .boolean,
        symbolPure ⟨⟨[]⟩, 100, .id "named"⟩⟩ := by cbv

private def exhausting : Scheduling.Computation Nat :=
  (do
    let prepared ← callback "must not execute"
    let _ ← Scheduling.freshDescription .none
    return (do let _ ← prepared; return 0 : State.ElabM Nat)
    : Scheduling.Build (State.ElabM Nat))
private def exhausted := State.run (Scheduling.execute exhausting)
  {context with freshness := {context.freshness with maximum := 100}}

-- Build exhaustion retains the first allocation and executes no prepared action.
example : (exhausted.1, exhausted.2.freshness.next, exhausted.2.effects.errors,
    exhausted.2.backend) = (.error (.freshness .exhausted), 101, [], "Driver") := by cbv

#print axioms Scheduling.execute_defer
#print axioms Scheduling.execute_run
#print axioms Scheduling.execute_bind
#print axioms Scheduling.execute_wrappedFreshSymbol
#print axioms Scheduling.buildMapAt_cutoff
#print axioms Scheduling.execute_mapM_defer
