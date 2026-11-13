module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Session
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public meta import Silmaril.Proofs.Wasm.Examples.LRAT.Session
public meta import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun

@[expose] public section

/-!
# The LRAT checker: tests

* **Proved, for every session** (`satTwo_never_unsat`): when the entire recorded stream
  before the queried `unsat` call is `[1, 2, 0, -1, 2, 0]`, representing the satisfiable
  formula `satTwo = [[1, 2], [-1, 2]]`, that call cannot answer a nonzero value. Proof calls
  may vary while preserving this stream; further input is not covered by this premise. This is a
  consequence of `lrat_session_unsat`, at every profile and against every environment.
* **Executed** (`#guard`, not a proof): sessions run with silmaril-lean's verified interpreter
  (`Silmaril.Wasm.SingleThreaded.Exec.runInvoke?`, whose runs are Core runs,
  `runInvoke?_steps_noHost`), one export call at a time from the instantiated store, the store
  persisting: the checker accepts the RUP refutations `fourClausesProof` of `fourClauses` and
  `php32Proof` of the pigeonhole formula `php32` (both also accepted by the reference checker,
  `fourClauses_check`, `php32_check`) and the refutation `fourClausesRatProof` through two RAT
  steps (`fourClausesRat_check`; a RAT step is `step_begin`, `step_lit`s, per candidate
  `rat_begin(j)` and its hints, then `rat_end`), and rejects the bogus proofs of `satTwo`
  (RUP and RAT) and a RAT step with an uncovered candidate.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Verify
open Silmaril.Wasm.Spec.Multi (Call Session)
open Silmaril.Logic.SAT Silmaril.Logic.SAT.LRAT

/-! ## Proved: no false `unsat` for a satisfiable input -/

/-- **A satisfiable input is never claimed unsatisfiable**: in every session whose DIMACS input
before an `unsat` call is that of `satTwo`, the call answers `0` (if it answers a value). -/
theorem satTwo_never_unsat {P : Silmaril.Wasm.Numerics.Profile} {K : Env lratI.E}
    {l l₁ l₂ : List (Call lratI)} {c : Call lratI} (hs : Session P lratI K lratI.store l)
    (hl : l = l₁ ++ c :: l₂) (hc : c.1.1.val = 7) {v : BitVec 32}
    (hv : Answer.toResult c.2 = .values [Val.i32 v]) (hin : streamOf l₁ = [1, 2, 0, -1, 2, 0]) :
    v = 0#32 := by
  by_contra hne
  have hu := lrat_session_unsat hs hl hc hv hne
  rw [hin] at hu
  have hF : Dimacs.cnf [1, 2, 0, -1, 2, 0] = satTwo := by decide
  rw [hF] at hu
  exact CNF.not_sat_of_unsat hu satTwo_sat

/-! ## Executed: sessions on the verified interpreter -/

/-- One export call, by silmaril-lean's verified interpreter (deterministic profile, no host,
fuel `refFuel`): the store it leaves and its result. -/
def runCall (s : Store Nat) (j : Nat) (args : List Val) : Option (Store Nat × Option Result) :=
  match Silmaril.Wasm.SingleThreaded.Exec.runInvoke? refOracle refFuel s j args with
  | some (c, _, r) => some (c.store, r)
  | none => none

/-- A sequence of export calls from store `s`, the store persisting: their results. -/
def runCalls (s : Store Nat) : List (Nat × List Val) → List (Option Result)
  | [] => []
  | (j, args) :: rest =>
    match runCall s j args with
    | some (s', r) => r :: runCalls s' rest
    | none => [none]

/-- The `i32` argument `x`. -/
def argOf (x : Int) : List Val := [Val.i32 (BitVec.ofInt 32 x)]

/-- The DIMACS input of a formula: `add_lit` for every literal, `end_clause` after a clause. -/
def cnfCalls (F : CNF) : List (Nat × List Val) :=
  F.flatMap fun C => C.map (fun l => (0, argOf l)) ++ [(1, [])]

/-- The calls of an LRAT step. -/
def stepCalls : Step → List (Nat × List Val)
  | .add id lits hints =>
    (2, argOf id) :: lits.map (fun l => (3, argOf l)) ++ hints.map (fun h => (4, argOf h)) ++
      [(5, [])]
  | .del ids => ids.map fun id => (6, argOf id)
  | .rat id lits groups =>
    (2, argOf id) :: lits.map (fun l => (3, argOf l)) ++
      groups.flatMap (fun g => (8, argOf g.1) :: g.2.map (fun h => (4, argOf h))) ++ [(9, [])]

/-- The whole session: the formula, the proof, then `unsat`. -/
def checkCalls (F : CNF) (proof : List Step) : List (Nat × List Val) :=
  cnfCalls F ++ proof.flatMap stepCalls ++ [(7, [])]

/-- Run the checker on a formula and a proof: whether the final `unsat` answers `1`. -/
def wasmCheck (F : CNF) (proof : List Step) : Bool :=
  (runCalls lratS (checkCalls F proof)).getLast? == some (some (.values [Val.i32 1]))

#guard wasmCheck fourClauses fourClausesProof
#guard wasmCheck php32 php32Proof
#guard !wasmCheck fourClauses []
#guard !wasmCheck satTwo [.add 3 [] [1, 2]]
#guard !wasmCheck satTwo [.add 3 [2] [1]]
#guard !wasmCheck satTwo [.add 3 [] [7]]
#guard !wasmCheck satTwo [.add 3 [2] [1, 2]]
#guard !wasmCheck satTwo [.add 3 [2] [1, 2], .del [3], .add 4 [] [3]]
#guard wasmCheck fourClauses fourClausesRatProof
#guard !wasmCheck satTwo [.rat 3 [-2] [], .add 4 [] [1, 2, 3]]
#guard !wasmCheck satTwo [.rat 3 [-2] [(1, [1]), (7, [2])], .add 4 [] [1, 2, 3]]
#guard !wasmCheck satTwo [.rat 3 [-2] [(1, [2]), (2, [1])], .add 4 [] [1, 2, 3]]
#guard !wasmCheck fourClauses [.rat 5 [3] [], .rat 6 [-3, 1] [], .add 7 [1] [5, 6],
  .add 8 [] [7, 2, 4]]

end Silmaril.Wasm.Examples.LRAT
