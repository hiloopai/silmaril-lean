module

public meta import Silmaril.Logic.Metamath.SetMM.Consistency
public meta import Silmaril.Logic.Metamath.Verify.Thms

@[expose] public section

/-!
# ZFC data correspondence test

The test parses and checks the committed CC0 fragment `set-axioms.mm`.
For each primitive syntax rule and labelled ZFC axiom, it compares the
recorded assertion with the Lean tree assertion, including hypothesis order
and disjoint-variable conditions. This is an executable regression check;
it does not turn file acceptance into a kernel proof of that equality.
-/

namespace Silmaril.Logic.Metamath.SetMM.Regression

open Silmaril.Logic.Metamath Grammar

/-- Require an axiom with this exact label and assertion in the checked database. -/
meta def checkEntry (db : Verify.Database String String) (label : String)
    (A : Assertion String String) : IO Unit := do
  match db.entries.find? (·.label == label) with
  | none => throw (IO.userError s!"{label}: missing axiom")
  | some e =>
    unless e.kind == .axiom && e.assertion == A do
      throw (IO.userError s!"{label}: axiom differs")

/-- Compare every syntax rule and ZFC axiom with the committed source fragment. -/
meta def checkZFC : IO Unit := do
  let text ← IO.FS.readFile "data/metamath/set-axioms.mm"
  let db ← IO.ofExcept (Verify.verifyText text)
  for r in L.all do checkEntry db r.label (rules r).toAssertion
  for (label, A) in zfcList do checkEntry db label (A.flatten grammar)

#guard_msgs in
#eval checkZFC

end Silmaril.Logic.Metamath.SetMM.Regression
