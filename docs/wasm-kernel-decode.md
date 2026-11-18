# Next experiment: kernel Wasm decoding, not evaluator memory

Start from the decoder already on main. `Silmaril.Wasm.Binary.Core.decode?` is
the compatibility baseline, and `Silmaril.Wasm.Perf.CoreDecode.decodeF` is
the byte-array performance baseline with the checked `decodeF_eq` transfer.
The latter already addresses the native LEB128 repeated `Nat.pow` cost. Do not
start a second Wasm parser or mistake `Wasm.Tools.Meta.parseBinaryB_spec` (a
proved *framing* tool) for instruction/body decoding.

Entry points: `Silmaril/Wasm/Binary/Core/Decode.lean` and
`Silmaril/Wasm/Binary/Core/Decode/Leb.lean` for the compatibility reader;
`Silmaril/Wasm/Perf/CoreDecode/{Defs,Thms}.lean` for `decodeF` and its transfer;
`Silmaril/Prelude/Bytes/{Defs,Thms}.lean` and
`Silmaril/Prelude/Bytes/Elab/Defs.lean` for byte terms and proofs.

1. **Scope the first witness to Core 3.0.** Compare `decode?` and `decodeF` on
   the same embedded bytes and the same successful decoded-module proposition.
   Run the two in one compiled native executable, and measure kernel proofs in
   separate processes. Use `examples/wasm-acceptors/{empty_check,ex_start}.wasm`
   and `examples/wasm-checkers/lrat.wasm` as first fixtures. Add a generated module with many small code
   bodies and a separate module with one large data segment; increasing only a
   data payload does not exercise recursive decode. Include boundary negatives:
   truncated sections and LEB128 groups, incorrect counts/body lengths,
   invalid UTF-8 names, and opcode/profile mismatches. Pin exact fixture hashes
   with each report; do not commit large generated fixtures.
2. **Separate construction, framing, and checking.** Benchmark direct reduction
   from `ByteArray`, then a `KBytes` cursor for reads/section slices. First prove
   the cursor operations agree with the existing cursor on well-formed bytes.
   Measure header/section parsing, first body query, full section/body checking,
   and `.olean` import. Keep separate acceptance results and source-linked
   results. If byte access is not the bottleneck, do not migrate the whole
   decoder; isolate LEB/vector/AST construction. Section certificates should
   enforce both exact byte range/consumption and a proof of the semantic body
   or module projection, not just render or hash the section.
3. **Treat macros like the JSON import.** Ordinary preprocessing can emit an
   explicit `Wasm.Module` term plus optionally an independent `KBytes` source
   definition; its type is not a source proof. The explicit source theorem
   should check decode agreement in the kernel, ideally from per-section/body
   proofs composed by framing. No silent retry, no native equality promoted to
   a theorem. Native proof execution (if later approved) is a separate policy
   decision, not an implementation detail of preprocessing.

## Dependency and merge order

- Main already contains `Silmaril.Prelude.Bytes` and its literal elaborator.
  Reuse these first; do not require the full [#125](https://github.com/hiloopai/silmaril-lean/pull/125)
  stack for a kernel-only experiment. Reconcile the still-open ProcDecl/trust
  changes against main separately if needed. Confirm the actual whitelist and
  emitted axiom audit before enabling any native proof backend; #125 explicitly
  records that such proofs are not kernel-only.
- [#127](https://github.com/hiloopai/silmaril-lean/pull/127) illustrates the useful
  interface: native `ByteArray` and kernel `KBytes` checkers proving the same
  proposition under a byte-link hypothesis. It is stacked on ELF leaves and
  incorporates #125. Use it as a design example, not as a Wasm dependency.
- [#131](https://github.com/hiloopai/silmaril-lean/pull/131) concerns *executing*
  decoded modules (`MemSimOn`, Core `ByteArray`/`KMem`, overlays/pages), stacked
  on #105. [#133](https://github.com/hiloopai/silmaril-lean/pull/133) adds the
  KBytes `KRope` and `KPath` evaluator baselines on #131 and an older pinned
  #125. Evaluate them in that order on the evaluator track; `PageMem` wins
  some update/share workloads, so do not conflate selection of decode storage
  with selection of mutable execution memory. Establish Core `Step` coverage
  separately before generalizing the evaluator.
- No merge of #125, #127, #131, or #133 is part of this task. #126 is available
  on main for later sparse overlays or symbol-style finite maps; it is not a
  prerequisite to read bytecode.
