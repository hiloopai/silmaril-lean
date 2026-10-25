module

public meta import Silmaril.Logic.Metamath.SecondOrder.Syntax
public meta import Silmaril.Logic.Metamath.Verify.EndToEnd

@[expose] public section

/-!
# Tests for the data of `z2.mm`

The committed database `data/metamath/z2.mm` is parsed and checked by the
verified checker (`Verify.verifyText`) at elaboration time. It has 17 syntax
axioms, 80 logical axioms and 4 theorems (97 `$a` and 4 `$p` statements).

The Lean data in `SecondOrder.Data` is cross-checked against the checker:
the checked database is, entry by entry and in order, the syntax axioms of
`SecondOrder.rules`, then the flattenings along `SecondOrder.grammar` of the
tree assertions of `axiomList` and `theoremList`, with the same labels,
kinds, disjoint-variable pairs, hypotheses and conclusions once constants
and variables are printed as their tokens.
-/

namespace Silmaril.Logic.Metamath.SecondOrder.Tests

open Silmaril.Logic.Metamath Grammar Verify

/-- Print a symbol with its token. -/
meta def symStr : Sym C V → Sym String String
  | .const c => .const c.token
  | .var a => .var a.token

/-- Print an expression with tokens. -/
meta def exprStr (e : Expr C V) : Expr String String := ⟨e.tc.token, e.body.map symStr⟩

/-- Print a hypothesis with tokens. -/
meta def hypStr : Hyp C V → Hyp String String
  | .float c a => .float c.token a.token
  | .ess e => .ess (exprStr e)

/-- Print an assertion with tokens. -/
meta def assertionStr (A : Assertion C V) : Assertion String String :=
  ⟨A.dv.map fun p => (p.1.token, p.2.token), A.hyps.map hypStr, exprStr A.concl⟩

/-- All syntax axiom labels, in database order. -/
meta def labels : List L :=
  [.tvar, .t0, .tS, .tpl, .tmu, .wn, .wi, .wb, .wa, .wal, .wex, .wsal, .wsex, .weq, .wlt, .wel,
    .wseq]

/-- The entries the checker should record: label, kind and assertion. -/
meta def expected : List (String × Kind × Assertion String String) :=
  labels.map (fun l => (l.label, .axiom, assertionStr (rules l).toAssertion)) ++
  axiomList.map (fun p => (p.1, .axiom, assertionStr (p.2.flatten grammar))) ++
  theoremList.map (fun p => (p.1, .theorem, assertionStr (p.2.flatten grammar)))

/-- Check `z2.mm` and compare it with the generated data. -/
meta def checkZ2 : IO Unit := do
  let text ← IO.FS.readFile "data/metamath/z2.mm"
  let db ← IO.ofExcept (verifyText text)
  let got := db.entries.toList.map fun e => (e.label, e.kind, e.assertion)
  unless labels.length == 17 && axiomList.length == 80 && theoremList.length == 4 do
    throw (IO.userError "unexpected numbers of generated statements")
  unless got.length == expected.length do
    throw (IO.userError s!"{got.length} checked entries, {expected.length} generated")
  for (g, e) in got.zip expected do
    unless g == e do
      throw (IO.userError s!"entry {g.1} differs from the generated {e.1}")

#guard_msgs in
#eval checkZ2

end Silmaril.Logic.Metamath.SecondOrder.Tests
