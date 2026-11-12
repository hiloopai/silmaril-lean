module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec
public import Silmaril.Raw.Wasm.SpecTec.Generated
public import Silmaril.Raw.Wasm.SpecTec.Examples

/-!
# SpecTec: the WebAssembly specification's own DSL, imported and given a meaning

This header exposes the SpecTec development in `Silmaril.Raw.Wasm.SpecTec`
(see `docs/projects/spectec/README.md`). The modules keep their namespaces `Silmaril.SpecTec.*` and
`Silmaril.Wasm.SpecTec.*`; their public prerequisites (the hand-written Core 3.0 syntax, binary
grammar and step relation) come from the pinned silmaril-lean.

Everything is relative to the SpecTec pin `WebAssembly/spec@608711107b7f1edb13efd57b7d79b49477462d36`,
whose three elaborated `--ast` streams are vendored in `specs/spectec/` and read at elaboration
time by `spectec_import`.

The layers, and the names that matter:

* **the IL and its stream** (`Silmaril.SpecTec.IL`, `Silmaril.SpecTec.SExp`): the IL AST
  (`IL.Script`, `IL.Def`), its printer `IL.defS`/`IL.scriptS` to S-expressions transcribed from
  SpecTec's `print.ml`, and the decoder `IL.decodeDef?`/`IL.decodeScript?` that inverts it;
  `Silmaril.SpecTec.Specs.wasm10`, `wasm20`, `wasm30` are the three pinned scripts;
* **a denotational semantics of the IL** (`Silmaril.SpecTec.Sem`): a universal value domain
  `Sem.Value`, a fuel-indexed evaluator with its relation `Sem.EvalExp`, relations as their
  step-indexed least fixpoint `Sem.Derives`, grammars as encoding relations `Sem.gramRelSup`,
  and a partial well-formedness checker (scope, kind, arity and shape, not typing);
* **errata as AST patches** (`Silmaril.SpecTec.IL.Binary51`, `…Text6x`, `…Wasm10`, `…Wasm20`):
  corrected scripts produced by checked textual patches of printed definitions;
* **the equivalence layer** (`Silmaril.SpecTec.Equiv`): the grammar and reduction rules of the
  pinned wasm-3.0 script, compared rule by rule with silmaril-lean's hand-written binary
  grammar (`Silmaril.Wasm.Binary`) and Core 3.0 step (`Silmaril.Wasm.Execution.Core`), through
  explicit value bridges (`Sem.Encode`, `Equiv.Execution.instrV?`, `Equiv.Execution.StepImage`,
  and the store/frame bridge `Equiv.RuntimeBridge`);
* **the structural schema view** (`Silmaril.Wasm.SpecTecEnc`): constructor tags and payload
  families of silmaril-lean's instructions checked against fingerprints generated from the
  pinned AST.

Theorems are in `Silmaril.Wasm.SpecTec.Thms`.
-/
