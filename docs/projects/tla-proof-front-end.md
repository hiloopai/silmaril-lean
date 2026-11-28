# TLA+ proof obligations, exact fact reuse and rule application

`Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Thms` exposes a constant-level
proof profile for one standalone source module. `prepare` parses source and
returns its module assumptions and theorem obligations in declaration order.
Each obligation has a goal, its preceding module assumptions, its own
`ASSUME … PROVE` hypotheses, and the outcome of scoping the source proof.
[Definitions](../../Silmaril/Logic/Temporal/TLA/ProofFrontEnd/Defs.lean) ·
[Soundness statement](../../Silmaril/Logic/Temporal/TLA/ProofFrontEnd/Thms.lean)

## Scope and denotation

- The admitted statements are expression assumptions, expression theorems and
  plain `ASSUME … PROVE` theorems with a flat list of expression hypotheses.
  In a named theorem, a whole hypothesis can carry a parameterless label.
  Each admitted hypothesis and goal must have constant level and lower in the
  existing core data profile without external primitives. Definitions and
  declarations use the existing resolver and level checks. Module composition,
  proof directives, hierarchical proofs, `NEW`, boxed forms, nested
  `ASSUME … PROVE` hypotheses and general expression labels are outside this profile.
  [Semantic coverage baseline](tla-semantic-coverage.md) ·
  [Data lowering](tla-data-elab.md)
- For expression statements the projection uses the equivalent nullary
  definitions described in TLA+2 §4.1. Anonymous expressions, local hypotheses
  and rule conclusions use generated names outside parsed identifier syntax.
  Named `ASSUME … PROVE` statements enter citation scope as rules. Each cited
  fact and returned statement carries its original zero-based source unit
  index. Resolver, level and lowering diagnostics carry projected paths, which
  can shift when hypotheses add definitions.
  [TLA+ Version 2, §§4.1–4.2](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=7)
- A `BY` or `BY ONLY` citation can name an earlier module assumption or
  theorem. In the proof of `T`, `T!H` can cite the whole local hypothesis
  labelled `H ::`. Labels must be unique within their theorem and introduce
  no bare expression names. The proof profile restricts `T!H` to the
  owning proof, where the hypothesis is a known fact. That restriction
  leaves out the general use of subexpression names as formulas. Bare
  forward and self citations, other selectors, formula citations, module
  citations and `DEF` are rejected. A scoped theorem citation records its
  source unit, independently of its proof status.
  [TLA+ Version 2, §6.4](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=18) ·
  [TLA+ Version 2, §§7.2–7.3](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=22) ·
  [TLA+ Version 2, §7.6.2](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=34) ·
  [TLAPS known and usable facts](https://proofs.tlapl.us/doc/web/content/Documentation/Tutorial/Hierarchical_proofs.html) ·
  [TLAPS prover tactics](https://proofs.tlapl.us/doc/web/content/Documentation/Tutorial/Tactics.html)

`Obligation.Valid` says that for every valuation in a chosen data
interpretation, if the preceding module assumptions and the local hypotheses
evaluate to that interpretation's true value, so does the goal. All
expressions share the same data operations, Boolean policy and valuation.
This is the semantic judgment for the extracted obligation. The source
checker retains the `ONLY` flag and uses only explicitly listed facts as
direct evidence for either `BY` or `BY ONLY`. In the reference, preceding
module assumptions and theorems are known and none are usable by default.
The expression hypotheses of a named theorem are known within its proof.
`BY ONLY` restricts usable facts to the cited facts and known domain
formulas. This profile has no domain formulas from declarations.
[*Specifying Systems*, §§17.5.6–17.6](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=352) ·
[TLA+ Version 2, §§7.2–7.3](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=22) ·
[TLA+ Version 2, §8.2](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=38)

## Evidence

- **Unresolved.** Preparation records missing proofs, `OMITTED`, `OBVIOUS`
  and well-scoped `BY` leaves. This status carries the source proof request.
  Rejected parse, scope or unsupported forms produce a diagnostic instead.
- **Exact reuse.** `Obligation.checkExact` checks a single module assumption
  or local hypothesis cited by `BY` or `BY ONLY`. `Context.checkExact` also
  checks single citations of earlier named formula theorems. It processes
  the actual obligations in declaration order and reuses only a successful
  certificate for the cited theorem in that module.
- **Rule application.** A single flat `BY` or `BY ONLY` leaf can cite one
  earlier certified `ASSUME … PROVE` theorem and facts that match every
  local premise. The other citations may be preceding named module
  assumptions, labelled hypotheses of the current theorem, and earlier
  certified formula theorems. A matching fact can discharge multiple
  identical premises. The rule conclusion must match the current goal.
  Both formula and rule reuse check declaration order and carry evidence
  that the reused certificate's module assumptions remain in scope. Those
  assumptions travel with the certificate, including under `ONLY`. To
  discharge a rule's local premise directly with a module assumption or a
  local hypothesis, the current leaf must cite it.
- **Term matching.** Exact reuse compares expanded typed data terms. The
  matcher covers rigid declaration identities, numerals, Boolean literals
  and structurally matching equality or disequality. A successful
  `ExactCertificate` carries the Lean equality and the in-scope evidence.
  `ExactCertificate.sound` gives the semantic judgment in every data
  interpretation. A failed match, an uncovered premise or a theorem
  citation without a certificate leaves the proof unresolved. Multiple
  citations require exactly one conditional rule.
- **Supplied.** A Lean caller can separately furnish `SuppliedEvidence` for
  `Obligation.Valid`. Its proof is scoped to the supplied interpretation and
  does not change the source proof status.

`Rule` is certified under its own local hypotheses using `Result`.
`Applied` cites `First` and `One` for the two local premises. `WithLocal`
cites its own `WithLocal!K` for the second premise.

```tla
---- MODULE ExactFacts ----
CONSTANT C, D, E
ASSUME Zero == C = 0
ASSUME Result == E = 2
THEOREM First == C = 0 BY ONLY Zero
THEOREM Rule == ASSUME H :: C = 0, K :: D = 1 PROVE E = 2 BY ONLY Result
ASSUME One == D = 1
THEOREM Applied == E = 2 BY ONLY Rule, First, One
THEOREM WithLocal == ASSUME K :: D = 1 PROVE E = 2 BY First, WithLocal!K, Rule
====
```

The soundness theorem covers these exact rules over the landed data
denotation. General source proof checking, TLAPS correspondence and
whole-module validity are outside the contract.

The TLA+ Version 2 guide cited here is dated 11 December 2018, with PDF
SHA-256 `ace1b572ff0c80965de6db654dae69847ec63debe11c595c428d7367ea194951`.
[Reference PDF](https://lamport.azurewebsites.net/tla/tla2-guide.pdf)

## Verification

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Examples
```

The parsed examples cover exact matching, chained rule applications, both
leaf forms, missing or mismatched premises, a mismatched conclusion, and
uncertified or out-of-scope citations. The same module proves an example
of separately supplied Lean evidence.
[Regressions](../../Silmaril/Logic/Temporal/TLA/ProofFrontEnd/Examples.lean)

SANY from the v1.7.4 distribution accepted the rule application fixtures
through semantic processing and rejected forward references to a rule or a
module assumption. SANY accepts the other theorem's labelled subexpression
as a formula reference. This checker restricts its use as a hypothesis
fact to the owning theorem's proof. SANY checks the source forms and
reference resolution. Lean checks certificate validity. The
`tla2tools.jar` SHA-256 is
`936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`.
[SANY distribution](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4)
