module

import Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Thms
meta import Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Defs

/-! Parsed regressions for obligation scope, exact fact reuse and rule application. -/

namespace Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Examples

meta section

private def source (body : String) : String :=
  "---- MODULE ProofScope ----\n" ++ body ++ "\n====\n"

private def accepted := source r#"
CONSTANT C
Equal(n) == C = n
ASSUME Zero == Equal(0)
THEOREM Exact == C = 0 BY ONLY Zero
THEOREM Alias == Zero BY Zero
THEOREM Different == C = 1 BY Zero
THEOREM Skipped == FALSE OMITTED
THEOREM CitesSkipped == FALSE BY Skipped
THEOREM LocalRule == ASSUME C = 0, TRUE PROVE C = 0 OBVIOUS
ASSUME Later == FALSE
THEOREM Missing == TRUE
THEOREM CitesRule == TRUE BY LocalRule
THEOREM After == FALSE BY Later
"#

#guard match prepare accepted with
  | .ok context =>
    decide (context.assumptions.map (·.unit) = [2, 9]) &&
    decide (context.theorems.map (·.sourceProof) =
      [.byFacts true [.assumption 2], .byFacts false [.assumption 2],
       .byFacts false [.assumption 2], .omitted, .byFacts false [.theoremDecl 6],
       .obvious, .missing, .byFacts false [.theoremDecl 8], .byFacts false [.assumption 9]]) &&
    decide (context.theorems.map (fun o => o.assumptions.map (·.unit)) =
      [[2], [2], [2], [2], [2], [2], [2, 9], [2, 9], [2, 9]]) &&
    decide (context.theorems.map (fun o => o.hypotheses.length) = [0, 0, 0, 0, 0, 2, 0, 0, 0]) &&
    decide (context.theorems.map (fun o => o.checkExact.isSome) =
      [true, true, false, false, false, false, false, false, true])
  | .error _ => false

#guard match prepare (source r#"
ASSUME A == IF TRUE THEN TRUE ELSE FALSE
ASSUME B == TRUE
THEOREM OutsideMatcher == A BY A
THEOREM Multiple == TRUE BY A, B
"#) with
  | .ok context =>
    decide (context.theorems.map (·.sourceProof) =
      [.byFacts false [.assumption 0], .byFacts false [.assumption 0, .assumption 1]]) &&
    context.theorems.all (fun obligation => obligation.checkExact.isNone)
  | .error _ => false

private def namedHypotheses := source r#"
CONSTANT C
Equal(n) == C = n
ASSUME H == FALSE
THEOREM Local == ASSUME H :: Equal(0), K :: Equal(1) PROVE C = 0 BY ONLY Local!H
THEOREM Mismatch == ASSUME H :: Equal(0), K :: Equal(1) PROVE C = 0 BY Mismatch!K
THEOREM Repeated == ASSUME H :: Equal(0) PROVE C = 0 BY Repeated!H, Repeated!H
THEOREM ModuleFact == ASSUME H :: Equal(0) PROVE FALSE BY H
THEOREM RuleConclusion == C = 0 BY Local
"#

#guard match prepare namedHypotheses with
  | .ok context =>
    decide (context.theorems.map (fun o => o.hypotheses.map (·.label)) =
      [[some "H", some "K"], [some "H", some "K"], [some "H"], [some "H"], []]) &&
    decide (context.theorems.map (·.sourceProof) =
      [.byFacts true [.hypothesis "H"], .byFacts false [.hypothesis "K"],
       .byFacts false [.hypothesis "H", .hypothesis "H"], .byFacts false [.assumption 2],
       .byFacts false [.theoremDecl 3]]) &&
    decide (context.checkExact.map (·.2.isSome) = [true, false, false, true, false])
  | .error _ => false

private def dependencies := source r#"
CONSTANT C
ASSUME Noise == IF TRUE THEN TRUE ELSE FALSE
ASSUME Zero == C = 0
THEOREM First == C = 0 BY ONLY Zero
ASSUME Later == C = 1
THEOREM Second == C = 0 BY First
THEOREM Third == C = 0 BY ONLY Second
THEOREM Mismatch == C = 1 BY First
THEOREM UsesMismatch == C = 1 BY Mismatch
THEOREM Obvious == TRUE OBVIOUS
THEOREM UsesObvious == TRUE BY Obvious
THEOREM Omitted == TRUE OMITTED
THEOREM UsesOmitted == TRUE BY Omitted
THEOREM Missing == TRUE
THEOREM UsesMissing == TRUE BY Missing
THEOREM Multiple == C = 0 BY First, Second
"#

#guard match prepare dependencies with
  | .ok context =>
    decide (context.checkExact.map (fun entry => (entry.1.unit, entry.2.isSome)) =
      [(3, true), (5, true), (6, true), (7, false), (8, false), (9, false),
       (10, false), (11, false), (12, false), (13, false), (14, false), (15, false)])
  | .error _ => false

private def ruleApplications := source r#"
CONSTANT C, D, E
ASSUME Zero == C = 0
ASSUME Result == E = 2
THEOREM KnownZero == C = 0 BY ONLY Zero
THEOREM Rule == ASSUME H :: C = 0, K :: D = 1 PROVE E = 2 BY ONLY Result
ASSUME One == D = 1
THEOREM Applied == E = 2 BY ONLY Rule, KnownZero, One
THEOREM Local == ASSUME K :: D = 1 PROVE E = 2 BY KnownZero, Local!K, Rule
THEOREM Chained == E = 2 BY ONLY One, Local
THEOREM RuleAlone == E = 2 BY Rule
THEOREM Missing == ASSUME K :: D = 1 PROVE E = 2 BY Rule, KnownZero
THEOREM OnlyMissing == ASSUME K :: D = 1 PROVE E = 2 BY ONLY Rule, KnownZero
THEOREM WrongPremise == E = 2 BY ONLY Rule, KnownZero, Result
THEOREM WrongGoal == E = 3 BY Rule, KnownZero, One
THEOREM SkippedRule == ASSUME D = 1 PROVE E = 2 OMITTED
THEOREM UseSkippedRule == E = 2 BY SkippedRule, One
THEOREM SkippedFact == D = 1 OMITTED
THEOREM UseSkippedFact == E = 2 BY Rule, KnownZero, SkippedFact
THEOREM TwoRules == E = 2 BY Rule, Local, KnownZero, One
"#

#guard match prepare ruleApplications with
  | .ok context =>
    decide ((context.theorems.take 5).map (fun o => o.assumptions.map (·.unit)) =
      [[1, 2], [1, 2], [1, 2, 5], [1, 2, 5], [1, 2, 5]]) &&
    decide (((context.theorems.drop 2).take 2).map (·.sourceProof) =
      [.byFacts true [.theoremDecl 4, .theoremDecl 3, .assumption 5],
       .byFacts false [.theoremDecl 3, .hypothesis "K", .theoremDecl 4]]) &&
    decide (context.checkExact.map (fun ⟨o, cert⟩ => (o.unit, cert.isSome)) =
      [(3, true), (4, true), (6, true), (7, true), (8, true), (9, false),
       (10, false), (11, false), (12, false), (13, false), (14, false),
       (15, false), (16, false), (17, false), (18, false)])
  | .error _ => false

private def rejected (body : String) (test : Diagnostic → Bool) : Bool :=
  match prepare (source body) with
  | .error diagnostic => test diagnostic
  | .ok _ => false

private def outOfScope (body : String) (unit : Nat) (name : String) : Bool :=
  rejected body fun
    | .factNotInScope index cited => index == unit && cited == name
    | _ => false

#guard outOfScope "THEOREM T == TRUE BY T" 0 "T"
#guard outOfScope "THEOREM T == TRUE BY A\nASSUME A == TRUE" 0 "A"
#guard outOfScope "THEOREM T == TRUE BY U\nTHEOREM U == TRUE" 0 "U"
#guard outOfScope "P == TRUE\nTHEOREM T == TRUE BY P" 1 "P"
#guard outOfScope "THEOREM T == TRUE BY SMT" 0 "SMT"
#guard outOfScope "THEOREM T == ASSUME H :: TRUE PROVE TRUE BY H" 0 "H"

#guard outOfScope r#"
ASSUME Fact == TRUE
THEOREM T == TRUE BY ONLY Rule, Fact
THEOREM Rule == ASSUME H :: TRUE PROVE TRUE BY ONLY Rule!H
"# 1 "Rule"

#guard outOfScope r#"
THEOREM Rule == ASSUME H :: TRUE PROVE TRUE BY ONLY Rule!H
THEOREM T == TRUE BY Rule, Later
ASSUME Later == TRUE
"# 1 "Later"

#guard rejected r#"
THEOREM Rule == ASSUME H :: TRUE PROVE TRUE BY ONLY Rule!H
THEOREM T == ASSUME H :: TRUE PROVE TRUE BY ONLY Rule, Rule!H
"# fun
  | .hypothesisNotInScope 1 "Rule" "H" => true
  | _ => false

#guard rejected "THEOREM T == ASSUME H :: TRUE PROVE H" fun
  | .resolution _ => true
  | _ => false

#guard rejected "THEOREM T == ASSUME H :: TRUE, H :: FALSE PROVE TRUE BY T!H" fun
  | .duplicateHypothesisLabel 0 "H" => true
  | _ => false

#guard rejected "THEOREM T == ASSUME H :: TRUE PROVE TRUE BY T!Other" fun
  | .hypothesisNotInScope 0 "T" "Other" => true
  | _ => false

#guard rejected "THEOREM T == ASSUME TRUE PROVE H :: TRUE BY T!H" fun
  | .resolution _ => true
  | _ => false

#guard rejected "THEOREM T == ASSUME H :: TRUE PROVE TRUE BY T!H\nTHEOREM U == TRUE BY T!H" fun
  | .hypothesisNotInScope 1 "T" "H" => true
  | _ => false

#guard rejected "THEOREM T == TRUE BY U!H\nTHEOREM U == ASSUME H :: TRUE PROVE TRUE" fun
  | .hypothesisNotInScope 0 "U" "H" => true
  | _ => false

#guard rejected "THEOREM T == ASSUME H :: TRUE PROVE TRUE BY T!1" fun
  | .unsupportedCitation 0 => true
  | _ => false

#guard rejected "THEOREM T == ASSUME H :: TRUE PROVE TRUE BY T!H(TRUE)" fun
  | .unsupportedCitation 0 => true
  | _ => false

#guard rejected "THEOREM T == ASSUME H(C) :: TRUE PROVE TRUE" fun
  | .unsupportedStatement 0 => true
  | _ => false

#guard rejected "EXTENDS TLAPS\nTHEOREM T == TRUE BY SMT" fun
  | .imports => true
  | _ => false

#guard rejected "P == TRUE\nTHEOREM T == TRUE BY DEF P" fun
  | .unsupportedCitation 1 => true
  | _ => false

#guard rejected "ASSUME A == TRUE\nTHEOREM T == TRUE BY A!:" fun
  | .unsupportedCitation 1 => true
  | _ => false

#guard rejected "THEOREM T == TRUE\n<1> QED OBVIOUS" fun
  | .unsupportedProof 0 => true
  | _ => false

#guard rejected "THEOREM T == ASSUME NEW x PROVE x = x" fun
  | .unsupportedStatement 0 => true
  | _ => false

#guard rejected "CONSTANT R\nTHEOREM R == ASSUME TRUE PROVE TRUE" fun
  | .nameConflict 1 "R" => true
  | _ => false

#guard rejected "ASSUME A == TRUE\nTHEOREM A == FALSE" fun
  | .nameConflict 1 "A" => true
  | _ => false

#guard rejected "VARIABLE x\nASSUME A == x = x" fun
  | .expectedConstant _ .state => true
  | _ => false

#guard rejected "THEOREM T == <<TRUE>> OBVIOUS" fun
  | .lowering ⟨_, .unsupported .tuple⟩ => true
  | _ => false

end

universe u

-- A caller can prove a denoted goal separately from the source proof status.
example {V : Type u} (obligation : Obligation) (model : Interpretation V)
    (goal : obligation.goal.term = .boolean true) : SuppliedEvidence obligation model := by
  constructor
  intro valuation _ _
  unfold Proposition.holds DataElab.CheckedExpr.eval
  rw [goal]
  rfl

end Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Examples
