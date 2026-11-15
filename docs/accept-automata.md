# Acceptance: state-machine presentations

`Silmaril.Semantics.Accept.Automata` (namespace `Silmaril.Accept.Automata`, region
`Semantics`) presents languages `Language α = Set (List α)` by finite automata and connects them
to the generic acceptor vocabulary of [acceptance](accept.md). It defines no automata of its own:
it reuses Mathlib's `DFA`, `NFA` and `εNFA` (`Mathlib/Computability/{DFA,NFA,EpsilonNFA}.lean`)
and CSLib's `DA.FinAcc` and `NA.FinAcc` (`Cslib/Computability/Automata/{DA,NA}/Basic.lean`),
whose language is `Acceptor.language`.

## Stable API

### `Silmaril.Semantics.Accept.Automata.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `dfaChecker M` | `fun w => decide (M.eval w ∈ M.accept)` (needs a decidable accept set) |
| `dfaRun M` | `detRun M.eval`: the deterministic runner of a DFA |
| `nfaRun M` / `εnfaRun M` | `fun w => M.eval w`: the set of states reachable on `w` |
| `DFASound M L` / `NFASound M L` | `M.accepts ≤ L` (only words of `L` are accepted) |
| `DFAComplete M L` / `NFAComplete M L` | `L ≤ M.accepts` (every word of `L` is accepted) |
| `DFAPresents M L` / `NFAPresents M L` | `M.accepts = L`; `dfaPresents_iff`/`nfaPresents_iff` (sound ∧ complete) |
| `toCslibDA M` / `ofCslibDA A` | Mathlib `DFA α σ` ⇄ CSLib `DA.FinAcc σ α` (same data, mutually inverse by `rfl`) |
| `toCslibNA M` | Mathlib `NFA α σ` as CSLib `NA.FinAcc σ α` (`s →a s'` iff `s' ∈ M.step s a`) |
| `isDigit`, `digitsLang`, `DigitState`, `digitsDFA`, `digitsCheck` | the byte example `[0-9]+` |

Key laws:

* Checkers: `decides_dfaChecker : Decides (dfaChecker M) M.accepts`, `ofBool_dfaChecker`, and
  `sound_dfaChecker_iff`, `complete_dfaChecker_iff`, `decides_dfaChecker_iff`, which turn the
  checker notions `Sound`/`Complete`/`Decides` into `DFASound`/`DFAComplete`/`DFAPresents`.
* Runners: `acceptsSome_dfaRun` and `acceptsAll_dfaRun` (both are `M.accepts`;
  `acceptsSome_dfaRun_eq_acceptsAll`); `accepts_eq_acceptsSome_nfaRun` and
  `accepts_eq_acceptsSome_εnfaRun` (NFA and ε-NFA acceptance are existential).
* Universal acceptance of an NFA runner is a different language in general:
  `acceptsAll_nfaRun_ne_accepts_of_start_eq_empty` (no start state: vacuous `acceptsAll`, empty
  `accepts`); the example `twoStarts` (two start states, one rejecting) accepts `[]`, which is
  not universally accepted. They agree on DFA-shaped NFAs (`nfaRun_toNFA`,
  `acceptsAll_nfaRun_toNFA`), and `acceptsAll_nfaRun_subset_accepts` holds when every word
  reaches some state.
* Transport: `nfaSound_toNFA`, `nfaComplete_toNFA`, `nfaPresents_toNFA` (`DFA.toNFA`);
  `dfaSound_toDFA`, `dfaComplete_toDFA`, `dfaPresents_toDFA` (`NFA.toDFA`);
  `nfaSound_εNFA_toNFA`, `nfaComplete_εNFA_toNFA`, `nfaPresents_εNFA_toNFA` (`εNFA.toNFA`).
* Regularity: `DFAPresents.isRegular` (`Fintype σ`) and `NFAPresents.isRegular` (`Finite σ`)
  give Mathlib's `Language.IsRegular`; CSLib's `Cslib.Language.IsRegular.iff_dfa`/`iff_nfa`
  relate it to CSLib automata.
* CSLib: `language_toCslibDA`, `accepts_ofCslibDA` (by `rfl`), `language_toCslibNA`;
  CSLib's own conversions agree with Mathlib's: `language_toNAFinAcc_toCslibDA`
  (`DA.FinAcc.toNAFinAcc` vs `DFA.toNFA`) and `language_toDAFinAcc_toCslibNA`
  (`NA.FinAcc.toDAFinAcc` vs `NFA.toDFA`).

## Bytes

An automaton over `UInt8` presents a byte language `Language UInt8` (the `ByteLang` of
`Silmaril.Formats.Accept`, which `Semantics` cannot import). The worked example is `digitsDFA`,
three states `start`, `digits`, `dead`, presenting the ASCII decimal numerals
`digitsLang = {w | w ≠ [] ∧ ∀ b ∈ w, isDigit b}` with `isDigit b := 0x30 ≤ b && b ≤ 0x39`:

* `accepts_digitsDFA : digitsDFA.accepts = digitsLang` (sound and complete);
* `decides_digitsCheck : Decides digitsCheck digitsLang`;
* `isRegular_digitsLang`.

Regression tests (`decide`/`rfl` on concrete byte lists, membership derived from one checker
run, the NFA and CSLib views of the same language, and the NFA quantifier separation):
`Silmaril/Semantics/Accept/Automata/Examples.lean`.

## Limitations

* Only finite-word acceptance. CSLib's ω-automata (`DA.Buchi`, `NA.Buchi`, `Muller`) are not
  connected here; see `Silmaril.Semantics.StreamMonitors` for ω-languages.
* No ε-NFA bridge to CSLib's `εNA`: `εNFA` appears only through `εnfaRun` and Mathlib's
  `εNFA.toNFA`.
* No executable NFA checker: `NFA.eval` returns a `Set σ`, and `NFA.toDFA` has state type
  `Set σ`, so neither yields a `Bool` checker without a separate finset-based subset
  construction, which is not provided. Executable checking goes through a DFA with a decidable
  accept set.
* `dfaChecker` is evaluated by kernel reduction in the tests (`decide` on short literal byte
  lists); it is not a performance-oriented matcher, and string literals through
  `String.toUTF8` do not reduce under `decide`.
* Regularity requires finitely many states (`Fintype`/`Finite`); the presentations themselves
  (`DFAPresents` etc.) allow any state type, as Mathlib's and CSLib's automata do.
* The byte example covers one language; regular expressions and grammars are separate
  developments.
