module

public import Silmaril.Wasm.Tools.Wast.Cli.Defs
import Silmaril.Proofs.Wasm.Tools.Wast.Cli

/-!
# The command lines of `json-from-wast` and `wast`: what they mean

* `tokens_ok_iff`: the tokenizer computes exactly the declarative token grammar `Spells`
  (with `Cluster` for short clusters): `--` ends the options, `--name=value`, `--name value`
  (a value must not look like an option), `--flag`, clusters `-abc` whose first option with a
  value takes the rest of the cluster (`-fVALUE`, `-f=VALUE`) or the next argument, and
  positionals (`-` included);
* `jsonOpts?_run`, `wastOpts?_run`: a command line that runs spells some tokens, has no
  `--help`, and its options record is `jsonRecord`/`wastRecord` of those tokens;
* `jsonRecord_ok`: the input is the only positional; `-o`, `--wasm-dir` occur at most once
  and are the record's; `--pretty` is a flag given at most once;
* `wastRecord_ok`: at most one positional (the input); `--ignore-error-messages` and
  `--snapshot` at most once; the asserts are the comma-separated values of `-a`, each one of
  the eight `Assert` names; the features are the `-f` arguments in order, each accepted by
  the feature parser (`Features.parseFeatures`), from which `WastOpts.featureSet` folds the
  wasmparser feature set.

Proofs in `Silmaril.Proofs.Wasm.Tools.Wast.Cli`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast.Cli

theorem tokens_spells {specs : List OptSpec} {args : List String} {ts : List Tok} :
    tokens specs args = .ok ts ↔ Spells specs args ts := tokens_ok_iff

theorem json_run {args : List String} {o : JsonOpts} (h : jsonOpts? args = .run o) :
    ∃ ts, Spells jsonSpecs args ts ∧ values ts "help" = [] ∧ positionals ts = [o.wast] ∧
      single ts "output" = .ok o.output ∧ single ts "wasm-dir" = .ok o.wasmDir ∧
      flag ts "pretty" = .ok o.pretty := by
  obtain ⟨ts, hs, hh, hr⟩ := jsonOpts?_run h
  exact ⟨ts, hs, hh, jsonRecord_ok hr⟩

theorem wast_run {args : List String} {o : WastOpts} (h : wastOpts? args = .run o) :
    ∃ ts, Spells wastSpecs args ts ∧ values ts "help" = [] ∧
      positionals ts = o.input.toList ∧
      flag ts "ignore-error-messages" = .ok o.ignoreErrorMessages ∧
      single ts "snapshot" = .ok o.snapshot ∧
      o.asserts = listValues ts "assert" ∧ (∀ a ∈ o.asserts, a ∈ assertValues) ∧
      o.features = (values ts "features").filterMap id ∧
      (∀ v ∈ o.features, ∃ acts, Features.parseFeatures v = .ok acts) := by
  obtain ⟨ts, hs, hh, hr⟩ := wastOpts?_run h
  exact ⟨ts, hs, hh, wastRecord_ok hr⟩

end Silmaril.Wasm.Tools.Wast.Cli
