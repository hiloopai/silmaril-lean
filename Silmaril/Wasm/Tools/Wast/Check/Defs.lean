module

public import Silmaril.Wasm.Tools.Wast.Json.Defs
public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# `wasm-tools wast`: structural checking of a `.wast` script

The pure core of `wasm-tools wast` (1.262.0, `src/bin/wasm-tools/wast.rs`): every
directive is checked short of executing code.

* `module`, `module definition`, `assert_unlinkable`: the module encodes, decodes and
  validates (`test_wasm`);
* `assert_malformed`(`_custom`): encoding fails, or decoding fails (and then a
  non-custom module must not validate), with the expected message;
* `assert_invalid`(`_custom`): encoding and decoding succeed and validation fails with the
  expected message;
* `thread`: its directives, with indices `1000 i + j`;
* actions and their assertions, `register`, `wait`: nothing.

The tools are a `Backend` (encoder, decoder, validator, and optionally the
print/parse round trip `test_wasm_roundtrip` performs). `defaultBackend` is the one
available in this pass: silmaril-lean's certified WAT elaborator
(`Wat.parseSupported?`, sound for `Text.Core.ModuleT`) and executable encoder
(`Exe.encodeModuleWith?`), the binary decoder `Binary.Core.Decode.decodeModule` and the
executable validator `Validation.validate?`. It does not encode component text, and its
error messages are not `wasmparser`'s: with the default message check (no
`--ignore-error-messages`) a mismatch is reported as `wasm-tools` would report it.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Formats Silmaril.Formats.SExpEncoding
open Silmaril.Wasm

/-- `test_wasm_roundtrip`'s tools: the printer (`wasmprinter::print_bytes`), the folding
printer (`fold_instructions(true)`, when available), the text parser (`wat::parse_str`) and the
re-encoder (`RoundtripReencoder`: decode and encode again). -/
structure Roundtrip where
  print : ByteArray → Except String String
  printFolded : Option (ByteArray → Except String String) := none
  parse : String → Except String ByteArray
  reencode : ByteArray → Except String ByteArray

/-- The tools `wast` checks a script with. -/
structure Backend where
  enc : Encoder
  /-- `parse_binary_wasm` under the feature set: decode a binary (module or component). -/
  decode : ByteArray → Except String Unit
  /-- `wasm_tools::validate` under the feature set. -/
  validate : ByteArray → Except String Unit
  /-- `test_wasm_roundtrip`'s print/parse round trip, when available. -/
  roundtrip : Option Roundtrip := none

/-! ## The default backend -/

/-- Encode a core module, without a data count section unless the code needs one (as the
`wast` encoder), with one otherwise. -/
def encodeCore (m : Module) : Except String ByteArray :=
  match Binaryen.Exe.encodeModuleWith? false m with
  | .ok bs => .ok ⟨bs.toArray⟩
  | .error _ => (Binaryen.Exe.encodeModule? m).map fun bs => ⟨bs.toArray⟩

/-- Encode a text module from its S-expression. -/
def encodeText : ModKind → SExp → String → Except String ByteArray
  | .core, x, _ =>
    -- the elaborator reads a whole document: the list of top-level S-expressions
    match Binaryen.Toolkit.Wat.parseSupported? (lst [x]) with
    | some m => encodeCore m
    | none => .error "text module outside the supported WAT fragment"
  | .component, _, _ => .error "component text modules are not supported by this encoder"

/-- `QuoteWat::encode` for quoted text: read the text (lexically checked), then encode it as
`(module …)`, or as the fields of an anonymous module. -/
def encodeQuoted (text : ByteArray) : Except String ByteArray :=
  match String.fromUTF8? text with
  | none => .error "malformed UTF-8 encoding"
  | some s =>
    match Wat.sexpWatFullExec? .core3 s with
    | none => .error "malformed WAT lexical syntax"
    | some tree =>
      match elems? tree with
      | some [x] =>
        match elems? x with
        | some (.atom (.sym "module") :: _) => encodeText .core x s
        | some (.atom (.sym "component") :: _) => encodeText .component x s
        | _ => encodeText .core (lst (sym "module" :: [x])) s
      | some xs => encodeText .core (lst (sym "module" :: xs)) s
      | none => .error "malformed WAT"

/-- Is this binary a component (layer field 1)? -/
def isComponent (b : ByteArray) : Bool := b.size ≥ 8 && b.get! 6 == 1

def decodeDefault (b : ByteArray) : Except String Unit :=
  if isComponent b then .error "component binaries are not supported by this decoder"
  else (Binary.Core.Decode.decodeModule b).map fun _ => ()

def validateDefault (b : ByteArray) : Except String Unit := do
  if isComponent b then throw "component binaries are not supported by this validator"
  let m ← Binary.Core.Decode.decodeModule b
  match Validation.validate? m with
  | some _ => pure ()
  | none => throw "invalid module"

def defaultEncoder : Encoder := ⟨encodeText, encodeQuoted⟩

def defaultBackend : Backend :=
  { enc := defaultEncoder, decode := decodeDefault, validate := validateDefault }

/-! ## Asserts (`--assert`) -/

/-- `Assert` of `wast.rs`: the extra checks `--assert` turns on. -/
inductive Assert where
  | default
  | prettyWhitespace
  | snapshotPrint
  | snapshotJson
  | snapshotFolded
  | testFolded
  | noTestFolded
  | permissive
  deriving Repr, DecidableEq

/-- The value names of `--assert` (clap's kebab-case `ValueEnum`). -/
def Assert.ofString? : String → Option Assert
  | "default" => some .default
  | "pretty-whitespace" => some .prettyWhitespace
  | "snapshot-print" => some .snapshotPrint
  | "snapshot-json" => some .snapshotJson
  | "snapshot-folded" => some .snapshotFolded
  | "test-folded" => some .testFolded
  | "no-test-folded" => some .noTestFolded
  | "permissive" => some .permissive
  | _ => none

/-- `Opts::assert`: is `a` enabled by the list `as`, read in order? An explicit request
enables; `default` enables all but `snapshot-folded` and `permissive`; `no-test-folded`
disables `test-folded`. -/
def Assert.enabled (as : List Assert) (a : Assert) : Bool :=
  as.foldl (fun en x =>
    if x == a then true
    else if x == .default && a != .snapshotFolded && a != .permissive then true
    else if x == .noTestFolded && a == .testFolded then false
    else en) false

/-! ## The checking monad

A failure is an `anyhow`-style context chain, outermost context first. The check runs in
`ExceptT (List String) m` for a monad `m` that provides only the snapshot comparison (`Snap`):
`m = Id` with `noSnap` is the pure check; the IO layer passes a `Snap IO` that reads (or, with
`BLESS`, writes) the snapshot files. -/

/-- A context chain, outermost first. -/
abbrev Chain := List String

abbrev CM (m : Type → Type) := ExceptT Chain m

/-- `snapshot(kind, test, contents)`: compare (or write) the snapshot of `contents`. -/
abbrev Snap (m : Type → Type) := String → String → String → m (Except String Unit)

/-- Snapshots without a `--snapshot` directory. -/
def noSnap {m : Type → Type} [Monad m] : Snap m := fun _ _ _ =>
  pure (.error "must pass `--snapshot <dir>` to indicate where to place snapshots")

section
variable {m : Type → Type} [Monad m]

def liftE {α : Type} (e : Except String α) : CM m α := match e with
  | .ok a => pure a
  | .error s => throw [s]

/-- `.context(c)`. -/
def ctx {α : Type} (c : String) (x : CM m α) : CM m α :=
  ExceptT.mk do
    match ← x.run with
    | .ok a => pure (.ok a)
    | .error e => pure (.error (c :: e))

def liftSnap (x : m (Except String Unit)) : CM m Unit :=
  ExceptT.mk do pure ((← x).mapError fun e => [e])

end

/-- Options of `wast` that the check reads. -/
structure CheckOpts where
  ignoreErrorMessages : Bool := false
  asserts : List Assert := []

def CheckOpts.on (o : CheckOpts) (a : Assert) : Bool := Assert.enabled o.asserts a

/-! ## Pieces of `test_wasm_roundtrip` -/

def isWsChar (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The rest after a string literal whose opening quote was consumed. -/
def skipStr : Nat → List Char → List Char
  | 0, cs => cs
  | _, [] => []
  | f + 1, '\\' :: _ :: cs => skipStr f cs
  | _ + 1, '"' :: cs => cs
  | f + 1, _ :: cs => skipStr f cs

/-- The rest after a block comment whose `(;` was consumed (`d` open comments). -/
def skipBlock : Nat → Nat → List Char → List Char
  | 0, _, cs => cs
  | _, _, [] => []
  | f + 1, d, '(' :: ';' :: cs => skipBlock f (d + 1) cs
  | f + 1, d, ';' :: ')' :: cs => if d ≤ 1 then cs else skipBlock f (d - 1) cs
  | f + 1, d, _ :: cs => skipBlock f d cs

def prettyGo : Nat → List Char → Except String Unit
  | 0, _ => .ok ()
  | _, [] => .ok ()
  | f + 1, ';' :: ';' :: cs => prettyGo f (cs.dropWhile (· != '\n'))
  | f + 1, '(' :: ';' :: cs => prettyGo f (skipBlock f 1 cs)
  | f + 1, '"' :: cs => prettyGo f (skipStr f cs)
  | f + 1, c :: cs =>
    if isWsChar c then
      let ws := (c :: cs).takeWhile isWsChar
      if ws.head? == some '\n' || ws == [' '] then prettyGo f ((c :: cs).dropWhile isWsChar)
      else .error s!"found non-one-length whitespace in `wasmprinter` output: {repr (String.ofList ws)}"
    else prettyGo f cs

/-- `test_pretty_whitespace`: every whitespace token of the text starts with a line feed or
is one space. -/
def prettyWhitespace (s : String) : Except String Unit := prettyGo (s.length + 1) s.toList

def hexNat (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- `binary_compare` (first line of its message). -/
def binaryCompare (actual expected : ByteArray) : Except String Unit :=
  if actual.data == expected.data then .ok ()
  else
    let pos := (List.range (min actual.size expected.size)).find?
      fun i => actual.get! i != expected.get! i
    .error (match pos with
      | some p => s!"error: actual wasm differs at byte {p} ({hexNat p}) from expected wasm"
      | none => "error: actual wasm differs by being too small from expected wasm")

/-- The folding printer, or why there is none. -/
def Roundtrip.folded (rt : Roundtrip) (b : ByteArray) : Except String String :=
  match rt.printFolded with
  | some f => f b
  | none => .error "printing with folded instructions (`fold_instructions`) is not implemented"

/-- `QuoteWat::encode`. -/
def encodeQW (enc : Encoder) (src : String) : QuoteWat → Except String ByteArray
  | .wat _ _ (.binary ss) => .ok ⟨(ss.flatMap fun x => x).toArray⟩
  | m@(.wat k _ (.fields _)) => enc.text k m.toSExp src
  | .quote k ss => enc.quoted (quoteText k ss)

/-- `expect_binary_roundtrip`: not for `binary` modules (their bytes need not be canonical). -/
def expectBinaryRoundtrip : QuoteWat → Bool
  | .wat _ _ (.binary _) => false
  | _ => true

/-- `assert_error_matches`. -/
def errorMatches (o : CheckOpts) (err : String) (msg : List UInt8) : Except String Unit :=
  let m := (utf8? msg).getD ""
  if o.ignoreErrorMessages || (err.splitOn m).length > 1 then .ok ()
  else .error s!"bad error: {err}\nshould have failed with: {repr m}\nsuppress this failure with `--ignore-error-messages`"

/-- The path of a directive's test (`test.push(idx)`). -/
def testPath (test : String) (idx : Nat) : String := test ++ "/" ++ toString idx

/-- The snapshot file of `kind` for `path` under `dir` (`Opts::snapshot`): the components of
`path` after the first `tests` component, then `.kind`. -/
def snapshotName (dir kind path : String) : String :=
  let comps := (path.splitOn "/").filter fun c => c != "" && c != "."
  let rest := (comps.dropWhile (· != "tests")).drop 1
  let name := "/".intercalate rest ++ "." ++ kind
  if dir.endsWith "/" then dir ++ name else dir ++ "/" ++ name

section
variable {m : Type → Type} [Monad m] (b : Backend) (o : CheckOpts) (snap : Snap m)

/-- `if c { x? }`: the check `x` when `c` holds. A named combinator (rather than `if` in
`do` notation, which copies the rest of the block into both branches) keeps the checks a
flat sequence, which `Silmaril.Wasm.Tools.Wast.Check.Thms` reads off step by step. The check is
a thunk: it is built only when `c` holds. -/
def whenC (c : Bool) (x : Unit → CM m Unit) : CM m Unit := if c then x () else pure ()

/-- The folded print of `test_wasm_roundtrip` (`""` when `test-folded` is off), with its
snapshot. -/
def foldedPrint (test : String) (rt : Roundtrip) (contents : ByteArray) (enableSnapshot : Bool) :
    CM m String :=
  if o.on .testFolded then do
    let f ← ctx "failed to print wasm in folded form" (liftE (rt.folded contents))
    whenC (enableSnapshot && o.on .snapshotFolded) fun _ =>
      (ctx "failed to validate the `print-folded` snapshot" (liftSnap (snap "print-folded" test f)))
    pure f
  else pure ""

/-- The folded half of `test_wasm_roundtrip` (when `test-folded` is on). -/
def foldedRoundtrip (rt : Roundtrip) (contents : ByteArray) (roundtripBinary : Bool)
    (text1 folded1 : String) : CM m Unit := do
  let bf ← ctx "failed to parse folded `wat` from `wasmprinter`" (liftE (rt.parse folded1))
  let folded2 ← ctx "failed to print wasm in folded form" (liftE (rt.folded contents))
  whenC roundtripBinary fun _ =>
    (ctx "failed to compare original `wat` with roundtrip folded `wat`"
      (liftE (binaryCompare bf contents)))
  let text3 ← ctx "failed to print wasm" (liftE (rt.print bf))
  whenC (folded1 != folded2) fun _ => (throw ["original folded print does not match roundtrip folded print"])
  whenC (text1 != text3) fun _ => (throw ["original print does not match roundtrip folded->flat print"])

/-- The re-encoding half of `test_wasm_roundtrip`. -/
def reencodeCheck (rt : Roundtrip) (contents : ByteArray) : CM m Unit := do
  let re ← ctx "failed to reencode module" (liftE (rt.reencode contents))
  ctx "failed to compare reencoded module with original encoding"
    (liftE (binaryCompare re contents))

/-- `test_wasm_roundtrip` with the round trip tools `rt`. -/
def roundtripWith (rt : Roundtrip) (test : String) (contents : ByteArray)
    (roundtripBinary enableSnapshot : Bool) : CM m Unit := do
  let text1 ← ctx "failed to print wasm" (liftE (rt.print contents))
  whenC (enableSnapshot && o.on .snapshotPrint) fun _ =>
    (ctx "failed to validate the `print` snapshot" (liftSnap (snap "print" test text1)))
  let folded1 ← foldedPrint o snap test rt contents enableSnapshot
  whenC (o.on .prettyWhitespace) fun _ => (do
    liftE (prettyWhitespace text1)
    liftE (prettyWhitespace folded1))
  let binary2 ← ctx "failed to parse `wat` from `wasmprinter`" (liftE (rt.parse text1))
  let text2 ← ctx "failed to print wasm" (liftE (rt.print binary2))
  whenC roundtripBinary fun _ =>
    (ctx "failed to compare original binary with roundtrip through wasmparser->wasmprinter->wat"
      (liftE (binaryCompare binary2 contents)))
  whenC (text1 != text2) fun _ => (throw ["original print does not match roundtrip print"])
  whenC (o.on .testFolded) fun _ => foldedRoundtrip rt contents roundtripBinary text1 folded1
  whenC roundtripBinary fun _ => reencodeCheck rt contents

/-- `test_wasm_roundtrip`. -/
def testRoundtrip (test : String) (contents : ByteArray) (roundtripBinary enableSnapshot : Bool) :
    CM m Unit :=
  match b.roundtrip with
  | none => pure ()
  | some rt => roundtripWith o snap rt test contents roundtripBinary enableSnapshot

/-- `test_wasm`: valid, and round-trips. -/
def testWasm (test : String) (bytes : ByteArray) (roundtripBinary : Bool) : CM m Unit := do
  ctx "wasm isn't valid" (liftE (b.validate bytes))
  ctx "wasm did not roundtrip" (testRoundtrip b o snap test bytes roundtripBinary true)

/-- `assert_invalid`(`_custom`): encodes, decodes, round-trips (without snapshots) and fails
validation with the expected message. -/
def checkInvalid (test : String) (src : String) (custom : Bool) (q : QuoteWat)
    (s : List UInt8) : CM m Unit := do
  let bytes ← liftE (encodeQW b.enc src q)
  liftE (b.decode bytes)
  testRoundtrip b o snap test bytes (!custom && expectBinaryRoundtrip q) false
  match b.validate bytes with
  | .ok () => throw [s!"encoded and validated successfully but should have failed with: {(utf8? s).getD ""}"]
  | .error e => liftE (errorMatches o e s)

/-- `assert_malformed`(`_custom`): encoding fails, or decoding fails (and a non-custom module
does not validate), with the expected message. -/
def checkMalformed (test : String) (src : String) (custom : Bool) (q : QuoteWat)
    (s : List UInt8) : CM m Unit :=
  match encodeQW b.enc src q with
  | .error e => liftE (errorMatches o e s)
  | .ok bytes =>
    match b.decode bytes with
    | .error e => do
      liftE (errorMatches o e s)
      match custom, b.validate bytes with
      | true, .ok _ => pure ()
      | false, .error _ => pure ()
      | true, .error _ => throw ["invalid custom section caused validation to fail"]
      | false, .ok _ => throw ["validator thought malformed module was valid"]
    | .ok () =>
      if o.on .permissive && utf8? s == some "data count section required" then
        checkInvalid b o snap test src custom q s
      else throw [s!"encoded and parsed successfully but should have failed with: {repr ((utf8? s).getD "")}"]

/-- The check of one directive other than `thread` (`test_wast_directive`); `test` is the
script's path and `idx` the directive's index. -/
def checkBase (test : String) (idx : Nat) (src : String) : Directive → CM m Unit
  | .module q => do
    let bytes ← liftE (encodeQW b.enc src q)
    ctx "failed testing wasm binary produced by `wast`"
      (testWasm b o snap (testPath test idx) bytes (expectBinaryRoundtrip q))
  | .moduleDefinition k id body => do
    let q := QuoteWat.wat k id body
    let bytes ← liftE (encodeQW b.enc src q)
    ctx "failed testing wasm binary produced by `wast`"
      (testWasm b o snap (testPath test idx) bytes (expectBinaryRoundtrip q))
  | .assertUnlinkable q _ => do
    let bytes ← liftE (encodeQW b.enc src q)
    ctx "failed testing wasm binary produced by `wast`"
      (testWasm b o snap (testPath test idx) bytes true)
  | .assertMalformed q s => checkMalformed b o snap (testPath test idx) src false q s
  | .assertMalformedCustom q s => checkMalformed b o snap (testPath test idx) src true q s
  | .assertInvalid q s => checkInvalid b o snap (testPath test idx) src false q s
  | .assertInvalidCustom q s => checkInvalid b o snap (testPath test idx) src true q s
  | _ => pure ()

/-- The source of the module a directive is about: the directive itself for `module`, its
second element for an assertion. -/
def modSrc (source : ByteArray) (p : PNode) : Directive → String
  | .module _ | .moduleDefinition .. => p.slice source
  | _ => (p.children.getD 1 p).slice source

mutual
  /-- A directive, nested thread directives included (index `1000 idx + i`; the first failure
  stops the thread). -/
  def checkDirective (test : String) (source : ByteArray) :
      Nat → Directive → PNode → CM m Unit
    | idx, .thread _ sh ds, p =>
      checkThread test source idx 0 ds (p.children.drop (if sh.isSome then 3 else 2))
    | idx, d, p => checkBase b o snap test idx (modSrc source p d) d

  def checkThread (test : String) (source : ByteArray) :
      Nat → Nat → List Directive → List PNode → CM m Unit
    | _, _, [], _ => pure ()
    | _, _, _ :: _, [] => pure ()
    | idx, i, d :: ds, q :: qs => do
      checkDirective test source (idx * 1000 + i) d q
      checkThread test source idx (i + 1) ds qs
end

/-- The failures of the directives `l` (the `i`-th first), in order, after `acc`, with the
position of each failing directive. -/
def checkAll (test : String) (source : ByteArray) :
    Nat → List (Directive × PNode) → Array (Nat × Chain) → m (List (Nat × Chain))
  | _, [], acc => pure acc.toList
  | i, (d, p) :: rest, acc => do
    let r ← (checkDirective b o snap test source i d p).run
    checkAll test source (i + 1) rest (match r with
      | .ok () => acc
      | .error e => acc.push (p.pos, e))

/-- All failures of a script, in directive order, with the position of the directive. -/
def checkScript (test : String) (source : ByteArray) (s : Script) (ps : List PNode) :
    m (List (Nat × Chain)) :=
  match s with
  | .directives ds => checkAll b o snap test source 0 (ds.zip ps) #[]
  | .inline [] => pure [(0, ["expected at least one module field"])]
  | .inline xs => do
    match ← (checkBase b o snap test 0 (String.fromUTF8! source)
        (.module (.wat .core none (.fields xs)))).run with
    | .ok () => pure []
    | .error e => pure [(0, e)]

end

/-- The pure check (no snapshot directory). -/
def checkScriptPure (b : Backend) (o : CheckOpts) (test : String) (source : ByteArray)
    (s : Script) (ps : List PNode) : List (Nat × Chain) :=
  Id.run (checkScript b o noSnap test source s ps)

/-- `anyhow`'s `{:?}` of a failed directive: the context, then the causes. -/
def renderChain (head : String) : Chain → String
  | [] => head
  | [e] => s!"{head}\n\nCaused by:\n    {e}"
  | es => s!"{head}\n\nCaused by:" ++
      String.join (es.zipIdx.map fun (e, i) =>
        s!"\n    {i}: " ++ "\n       ".intercalate (e.splitOn "\n"))

end Silmaril.Wasm.Tools.Wast
