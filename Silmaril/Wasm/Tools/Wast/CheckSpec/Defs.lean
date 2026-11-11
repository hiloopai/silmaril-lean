module

public import Silmaril.Wasm.Tools.Wast.Check.Defs

/-!
# The `wast` directive logic, stated declaratively

When does `wasm-tools wast` (1.262.0, `src/bin/wasm-tools/wast.rs`) pass a directive? This
module states it as propositions over the backend's tools (`Backend`: encoder, decoder,
validator, round trip), one per function of `Silmaril.Wasm.Tools.Wast.Check` (the executable
transcription of `test_wast_directive`, `test_wasm`, `test_wasm_roundtrip`):

* `RoundtripOk`: `test_wasm_roundtrip` — print, (folded print,) whitespace checks, parse
  back, print again to the same text, (byte comparison,) the folded round trip when
  `test-folded` is on, re-encoding to the same bytes; a snapshot is never requested;
* `ModuleOk`: `module`, `module definition`, `assert_unlinkable` — the module encodes,
  validates and round-trips;
* `InvalidOk`: `assert_invalid`(`_custom`) — encodes, decodes, round-trips without snapshots,
  and validation fails with a matching message;
* `MalformedOk`: `assert_malformed`(`_custom`) — encoding fails with a matching message, or
  decoding fails with a matching message and validation succeeds exactly for the `_custom`
  form, or (`--assert permissive`) a `data count section required` module is checked as
  invalid;
* `DirectiveOk`: the above by directive; every other directive passes;
* `NodeOk`/`ThreadOk`: a directive with its positioned tree, `thread` directives recursively.

The equivalences with the transcription, for the pure check (`Id`, no snapshot directory:
`noSnap`), are in `Silmaril.Wasm.Tools.Wast.Check.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

/-- `test_wasm_roundtrip` passes, without a snapshot directory (`rb`: compare bytes; `es`:
snapshots enabled for this module). -/
def RoundtripOk (b : Backend) (o : CheckOpts) (bytes : ByteArray) (rb es : Bool) : Prop :=
  match b.roundtrip with
  | none => True
  | some rt =>
    ∃ t1, rt.print bytes = .ok t1 ∧
      (es = true → o.on .snapshotPrint = false) ∧
      ∃ f1, (if o.on .testFolded then rt.folded bytes else .ok "") = .ok f1 ∧
        (o.on .testFolded = true → es = true → o.on .snapshotFolded = false) ∧
        (o.on .prettyWhitespace = true →
          prettyWhitespace t1 = .ok () ∧ prettyWhitespace f1 = .ok ()) ∧
        ∃ b2, rt.parse t1 = .ok b2 ∧ rt.print b2 = .ok t1 ∧
          (rb = true → b2.data = bytes.data) ∧
          (o.on .testFolded = true →
            ∃ bf, rt.parse f1 = .ok bf ∧ (rb = true → bf.data = bytes.data) ∧
              rt.print bf = .ok t1) ∧
          (rb = true → ∃ re, rt.reencode bytes = .ok re ∧ re.data = bytes.data)

/-- `test_wasm`: valid, and round-trips with snapshots enabled. -/
def ModuleOk (b : Backend) (o : CheckOpts) (src : String) (q : QuoteWat) (rb : Bool) : Prop :=
  ∃ bytes, encodeQW b.enc src q = .ok bytes ∧ b.validate bytes = .ok () ∧
    RoundtripOk b o bytes rb true

/-- `assert_invalid`(`_custom`). -/
def InvalidOk (b : Backend) (o : CheckOpts) (src : String) (custom : Bool) (q : QuoteWat)
    (s : List UInt8) : Prop :=
  ∃ bytes, encodeQW b.enc src q = .ok bytes ∧ b.decode bytes = .ok () ∧
    RoundtripOk b o bytes (!custom && expectBinaryRoundtrip q) false ∧
    ∃ e, b.validate bytes = .error e ∧ errorMatches o e s = .ok ()

/-- `assert_malformed`(`_custom`). -/
def MalformedOk (b : Backend) (o : CheckOpts) (src : String) (custom : Bool) (q : QuoteWat)
    (s : List UInt8) : Prop :=
  (∃ e, encodeQW b.enc src q = .error e ∧ errorMatches o e s = .ok ()) ∨
  (∃ bytes e, encodeQW b.enc src q = .ok bytes ∧ b.decode bytes = .error e ∧
    errorMatches o e s = .ok () ∧ (b.validate bytes).toBool = custom) ∨
  (∃ bytes, encodeQW b.enc src q = .ok bytes ∧ b.decode bytes = .ok () ∧
    o.on .permissive = true ∧ utf8? s = some "data count section required" ∧
    InvalidOk b o src custom q s)

/-- `test_wast_directive` on a directive other than `thread`. -/
def DirectiveOk (b : Backend) (o : CheckOpts) (src : String) : Directive → Prop
  | .module q => ModuleOk b o src q (expectBinaryRoundtrip q)
  | .moduleDefinition k id body =>
    ModuleOk b o src (.wat k id body) (expectBinaryRoundtrip (.wat k id body))
  | .assertUnlinkable q _ => ModuleOk b o src q true
  | .assertMalformed q s => MalformedOk b o src false q s
  | .assertMalformedCustom q s => MalformedOk b o src true q s
  | .assertInvalid q s => InvalidOk b o src false q s
  | .assertInvalidCustom q s => InvalidOk b o src true q s
  | _ => True

mutual
  /-- A directive with its positioned tree passes: `thread` directives by their nested
  directives (paired with the trees after the thread's name and shared module), every other
  directive by `DirectiveOk` on its module's source slice (`modSrc`). -/
  def NodeOk (b : Backend) (o : CheckOpts) (source : ByteArray) : Directive → PNode → Prop
    | .thread _ sh ds, p => ThreadOk b o source ds (p.children.drop (if sh.isSome then 3 else 2))
    | d, p => DirectiveOk b o (modSrc source p d) d

  /-- The nested directives of a thread pass, up to the shorter of the two lists. -/
  def ThreadOk (b : Backend) (o : CheckOpts) (source : ByteArray) :
      List Directive → List PNode → Prop
    | [], _ => True
    | _ :: _, [] => True
    | d :: ds, q :: qs => NodeOk b o source d q ∧ ThreadOk b o source ds qs
end

/-- The value of a check over `Id`. -/
abbrev val {α : Type} (x : CM Id α) : Except Chain α := Id.run x.run

end Silmaril.Wasm.Tools.Wast
