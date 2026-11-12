module

public import Silmaril.Wasm.Tools.Wast.CheckSpec.Defs
import Silmaril.Proofs.Wasm.Tools.Wast.Check

/-!
# The `wast` directive logic meets its declarative statement

The transcription of `wasm-tools wast` (`Silmaril.Wasm.Tools.Wast.Check`) is shown equal to the
declarative propositions of `Silmaril.Wasm.Tools.Wast.CheckSpec` for the pure check (the `Id`
monad, no snapshot directory), over any backend (encoder, decoder, validator, round trip
tools). `val x` is the result of a check (`Id.run x.run`).

* `testRoundtrip_spec`: `test_wasm_roundtrip` passes iff `RoundtripOk`;
* `checkInvalid_spec`, `checkMalformed_spec`: `assert_invalid`/`assert_malformed` (and their
  `_custom` forms) pass iff `InvalidOk`/`MalformedOk`;
* `checkBase_spec`: a directive other than `thread` passes iff `DirectiveOk`;
* `checkDirective_spec`: any directive with its positioned tree, `thread` included, passes iff
  `NodeOk` (by mutual induction with `checkThread`);
* `checkScriptPure_spec`, `checkScriptPure_inline_spec`: `wast` reports no failure for a script
  iff every directive (paired with its tree) satisfies `NodeOk`; for a file that is one inline
  module, iff it has a field and the module passes `ModuleOk`.

Proofs in `Silmaril.Proofs.Wasm.Tools.Wast.Check`. The IO layer (`tools/wasm-tools/WasmTools/Wast.lean`)
runs `checkScript` in `IO` with the snapshot files; snapshots and error rendering are not
covered here (they are tested: `tools/wasm-tools/tests/wast/snapshot.sh`, `args.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

theorem testRoundtrip_spec {b : Backend} {o : CheckOpts} {test : String} {bytes : ByteArray}
    {rb es : Bool} :
    val (testRoundtrip b o noSnap test bytes rb es) = .ok () ↔ RoundtripOk b o bytes rb es :=
  testRoundtrip_ok_iff

theorem checkInvalid_spec {b : Backend} {o : CheckOpts} {test src : String} {custom : Bool}
    {q : QuoteWat} {s : List UInt8} :
    val (checkInvalid b o noSnap test src custom q s) = .ok () ↔ InvalidOk b o src custom q s :=
  checkInvalid_ok_iff

theorem checkMalformed_spec {b : Backend} {o : CheckOpts} {test src : String} {custom : Bool}
    {q : QuoteWat} {s : List UInt8} :
    val (checkMalformed b o noSnap test src custom q s) = .ok () ↔
      MalformedOk b o src custom q s :=
  checkMalformed_ok_iff

theorem checkBase_spec {b : Backend} {o : CheckOpts} {test src : String} {idx : Nat}
    {d : Directive} :
    val (checkBase b o noSnap test idx src d) = .ok () ↔ DirectiveOk b o src d :=
  checkBase_ok_iff

theorem checkDirective_spec {b : Backend} {o : CheckOpts} {test : String} {source : ByteArray}
    {idx : Nat} {d : Directive} {p : PNode} :
    val (checkDirective b o noSnap test source idx d p) = .ok () ↔ NodeOk b o source d p :=
  checkDirective_ok_iff idx d p

theorem checkScriptPure_spec {b : Backend} {o : CheckOpts} {test : String}
    {source : ByteArray} {ds : List Directive} {ps : List PNode} :
    checkScriptPure b o test source (.directives ds) ps = [] ↔
      ∀ dp ∈ ds.zip ps, NodeOk b o source dp.1 dp.2 :=
  checkScriptPure_directives_nil_iff

theorem checkScriptPure_inline_spec {b : Backend} {o : CheckOpts} {test : String}
    {source : ByteArray} {xs : List Silmaril.Formats.SExpEncoding.SExp} {ps : List PNode} :
    checkScriptPure b o test source (.inline xs) ps = [] ↔
      xs ≠ [] ∧ ModuleOk b o (String.fromUTF8! source) (.wat .core none (.fields xs)) true :=
  checkScriptPure_inline_nil_iff

end Silmaril.Wasm.Tools.Wast
