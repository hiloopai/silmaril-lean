import Lean.Data.Json
import Silmaril.X86.Decompile.Defs
import Silmaril.Semantics.CPort.Formats.ELF.Extract.Defs
import Silmaril.Machine.CSupport.Crypto.X86.Objects.Sha256ClangO0.Defs
/-!
# The Lean driver behind `sil decompile`

`tools/sil/src/decompile.rs` is a thin wrapper: it finds the input file, builds
this executable and runs it with the request in the environment. Everything
that reads bytes, decodes, proposes and checks happens here, in the same
definitions `Silmaril/X86/Decompile/` proves theorems about — `Region.decode?`,
`Propose.ofSymbols`, `Propose.ofStripped`, `check`, `CfgPropose.ofFunction` and
`checkCfg`. The driver adds no analysis of its own.

Run it from the repository root:

    SIL_DECOMPILE_MODE=check SIL_DECOMPILE_FILE=tests/x86/md5_memset_clang_O0.hex \
      lake env .lake/build/bin/decompile

The request is passed in the environment, in the style of
`scripts/CheckWatCorpus.lean`:

* `SIL_DECOMPILE_MODE` — `disasm`, `propose` or `check`;
* `SIL_DECOMPILE_FILE` — the input: an ELF object, a file of hexadecimal text,
  or raw bytes. The three are told apart by sniffing, not by the extension:
  the ELF magic first, then "every byte is a hex digit or whitespace";
* `SIL_DECOMPILE_INGESTED` — instead of a file, the name of an object already
  ingested into Lean (`sha256-clang-O0`). No `.o` file is kept in git, so this
  is how the pinned objects of `xcompile/manifest.json` are reached;
* `SIL_DECOMPILE_BASE` — the virtual address of the first byte, decimal or
  `0x`-prefixed, default `0`. For an ELF object the addresses are section
  offsets and the base is `0`, which is what `Propose.ofSymbols` assumes;
* `SIL_DECOMPILE_SECTION` — which section of an object to read, default
  `.text`;
* `SIL_DECOMPILE_CFG` — set to anything to add the proposed control-flow
  graphs to a `propose` result;
* `SIL_DECOMPILE_PARTITION` — a JSON file holding the partition `check` should
  judge; without it, `check` judges what the proposer produced.

`disasm` prints lines; `propose` and `check` print JSON. A failure — bytes that
do not decode, a rejected partition, a missing file — is reported on standard
output in the result and signalled by exit status 1, so that a caller can
branch on the status and still read the diagnostic.

## What is and is not trusted here

Nothing in `Propose` or `CfgPropose` is trusted, and this driver does not make
it so: a `propose` result is a guess. A `check` result is the decidable
checker's verdict, and acceptance has the meaning
`Silmaril/X86/Decompile/Functions.lean` proves for it — but note that running
the checker in a compiled executable is *evaluation*, not a kernel proof. To
get a proof, write the proposal into a Lean file and close the goal with the
`split_functions` and `recover_cfg` tactics, as
`Silmaril/X86/Decompile/Examples.lean` and
`Silmaril/X86/Decompile/RoundTrip.lean` do. This tool is for finding the
proposal that will be accepted; the Lean file is for proving that it is.

## Why the instructions print as Lean terms

There is no AT&T or Intel printer for `Ext.Instr` in the repository, and this
driver does not introduce one. A disassembly printer is a second spelling of
the instruction set, and a second spelling that nothing checks is a second
place for the model and the output to disagree. So `disasm` prints the model's
own `Repr`, whitespace collapsed to one line: it is uglier and it cannot lie.

Not a `module` file, so that it can run the imported definitions, in the style
of `scripts/TestElfIngest.lean`.
-/

open Lean
open Silmaril.X86 (Byte)
open Silmaril.X86.Decompile
open Silmaril.Formats.ELF

namespace DecompileTool

/-! ## Reading the input -/

/-- The value of an environment variable, or `none` when it is unset or empty. -/
def envVar (name : String) : IO (Option String) := do
  match ← IO.getEnv name with
  | some value => pure (if value.isEmpty then none else some value)
  | none => pure none

/-- The value of one hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Whitespace removed from both ends of a character list. -/
def trimChars (chars : List Char) : List Char :=
  (chars.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace |>.reverse

/-- The digits of a character list in the given radix, or `none` if any
character is not a digit of it. The list must be non-empty. -/
def digitsIn (radix : Nat) : List Char → Option Nat
  | [] => none
  | chars => chars.foldl (fun acc c => do
      let value ← hexDigit? c
      if radix ≤ value then none else pure (radix * (← acc) + value)) (some 0)

/-- A decimal or `0x`-prefixed address. -/
def parseAddr (text : String) : Option Nat :=
  match trimChars text.toList with
  | '0' :: 'x' :: rest => digitsIn 16 rest
  | '0' :: 'X' :: rest => digitsIn 16 rest
  | chars => digitsIn 10 chars

/-- Hexadecimal text as bytes, ignoring whitespace. `none` if a character is
neither a hex digit nor whitespace, or if the digits do not pair up. -/
def ofHex (text : String) : Option (List Byte) :=
  let rec pair : List Nat → Option (List Byte)
    | [] => some []
    | [_] => none
    | hi :: lo :: rest => (pair rest).map fun bs => BitVec.ofNat 8 (16 * hi + lo) :: bs
  let rec digits : List Char → Option (List Nat)
    | [] => some []
    | c :: rest =>
      if c.isWhitespace then digits rest
      else match hexDigit? c with
        | none => none
        | some value => (digits rest).map (value :: ·)
  (digits text.toList).bind pair

/-- What the input file turned out to hold. -/
inductive Input where
  /-- An ELF object, already parsed. -/
  | object (file : ObjectFile)
  /-- A flat run of code bytes. -/
  | code (bytes : List Byte)

/-- Sniff the file's contents: the ELF magic first, then hexadecimal text, then
raw bytes. An extension is not evidence, so none is consulted. -/
def classify (raw : ByteArray) : Except String Input :=
  let bytes := raw.toList.map fun b => (BitVec.ofNat 8 b.toNat : Byte)
  if raw.size ≥ 4 && raw[0]! == 0x7f && raw[1]! == 0x45 && raw[2]! == 0x4c && raw[3]! == 0x46 then
    match readObject bytes.toArray with
    | some file => .ok (.object file)
    | none => .error "the file begins with the ELF magic but does not parse as an object"
  else
    match String.fromUTF8? raw with
    | some text =>
      let chars := text.toList
      if chars.all (fun c => c.isWhitespace || (hexDigit? c).isSome) &&
          chars.any (fun c => (hexDigit? c).isSome) then
        match ofHex text with
        | some bytes => .ok (.code bytes)
        | none => .error "the file is hexadecimal text with an odd number of digits"
      else .ok (.code bytes)
    | none => .ok (.code bytes)

/-- The objects ingested into Lean, by the name `sil decompile --ingested`
takes. No object file is kept in git, so a pinned object is reached through the
module that carries its bytes and its digest. -/
def ingested : List (String × ObjectFile) :=
  [("sha256-clang-O0", Silmaril.Crypto.X86.Objects.Sha256ClangO0.object)]

/-- A named section's bytes. -/
def sectionBytes (file : ObjectFile) (name : String) : Option (Nat × List Byte) := do
  let wanted := Silmaril.X86.Decompile.Propose.nameBytes name
  let index ← file.sections.findIdx? fun part => part.name == wanted
  let owner ← file.sections[index]?
  pure (index, owner.data.toList)

/-! ## Rendering -/

/-- A `Repr` rendering with every run of whitespace collapsed to one space, so
that one instruction is one line. -/
def oneLine {α : Type} [Repr α] (value : α) : String :=
  let chars := (reprStr value).toList.map fun c => if c.isWhitespace then ' ' else c
  let rec squash : List Char → List Char
    | [] => []
    | ' ' :: ' ' :: rest => squash (' ' :: rest)
    | c :: rest => c :: squash rest
  String.ofList (trimChars (squash chars))

/-- Lowercase hexadecimal, `width` digits wide. -/
def hex (value width : Nat) : String :=
  let digit (v : Nat) : Char :=
    if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)
  let rec go : Nat → Nat → List Char
    | 0, _ => []
    | n + 1, v => digit (v % 16) :: go n (v / 16)
  String.ofList (go width value).reverse

/-- The bytes of one listed instruction, as hexadecimal. -/
def instrBytes (region : Region) (d : Decoded) : String :=
  String.intercalate " "
    (((region.bytes.drop (d.addr - region.base)).take d.size).map fun b => hex b.toNat 2)

/-- One edge, as a short word and a target. -/
def edgeString : Edge → String
  | .fallthrough t => s!"fallthrough→{hex t 8}"
  | .jump t => s!"jump→{hex t 8}"
  | .branch t => s!"branch→{hex t 8}"
  | .call t => s!"call→{hex t 8}"
  | .ret => "ret"
  | .halt => "halt"

/-! ## JSON -/

/-- A relocation or call target, as JSON. -/
def targetJson : Target → Json
  | .internal addr => Json.mkObj [("kind", "internal"), ("address", toJson addr)]
  | .external name => Json.mkObj [("kind", "external"), ("symbol", toJson name)]

/-- A proposed function, as JSON. -/
def funcJson (f : FunctionSpec) : Json :=
  Json.mkObj [("name", toJson f.name), ("entry", toJson f.entry), ("size", toJson f.size)]

/-- A partition, as JSON. -/
def partitionJson (p : Partition) : Json :=
  Json.mkObj [
    ("functions", Json.arr ((p.funcs.map funcJson).toArray)),
    ("padding", Json.arr ((p.padding.map fun q =>
      Json.mkObj [("start", toJson q.1), ("stop", toJson q.2)]).toArray)),
    ("relocs", Json.arr ((p.relocs.map fun e =>
      Json.mkObj [("offset", toJson e.1), ("target", targetJson e.2)]).toArray)),
    ("externals", Json.arr ((p.externals.map toJson).toArray))]

/-- A proposed or checked control-flow graph, as JSON. -/
def cfgJson (spec : CfgSpec) : Json :=
  Json.mkObj [
    ("function", toJson spec.func.name),
    ("entry", toJson spec.func.entry),
    ("blocks", Json.arr ((spec.blocks.map fun b =>
      Json.mkObj [("start", toJson b.start), ("terminator", toJson b.terminator)]).toArray)),
    ("edges", Json.arr ((spec.edges.map fun e =>
      Json.mkObj [("source", toJson e.1), ("target", toJson e.2)]).toArray))]

/-- A claim, as JSON. -/
def claimJson (c : Claim) : Json :=
  Json.mkObj [("start", toJson c.start), ("stop", toJson c.stop)]

/-- A rejection, as the constructor that fired and the addresses it names. The
`kind` is the constructor's own name, so that
`docs/agents/decompile-split-functions.md` can be consulted directly. -/
def rejectJson : Reject → Json
  | .undecodable addr =>
    Json.mkObj [("kind", "undecodable"), ("address", toJson addr)]
  | .outOfFuel => Json.mkObj [("kind", "outOfFuel")]
  | .uncovered start stop =>
    Json.mkObj [("kind", "uncovered"), ("start", toJson start), ("stop", toJson stop)]
  | .overlap first second =>
    Json.mkObj [("kind", "overlap"), ("first", claimJson first), ("second", claimJson second)]
  | .unordered first second =>
    Json.mkObj [("kind", "unordered"), ("first", claimJson first), ("second", claimJson second)]
  | .outside claim => Json.mkObj [("kind", "outside"), ("claim", claimJson claim)]
  | .entryNotAligned f =>
    Json.mkObj [("kind", "entryNotAligned"), ("function", funcJson f)]
  | .straddlesClaim addr =>
    Json.mkObj [("kind", "straddlesClaim"), ("address", toJson addr)]
  | .paddingNotNop addr =>
    Json.mkObj [("kind", "paddingNotNop"), ("address", toJson addr)]
  | .escapingEdge f source target =>
    Json.mkObj [("kind", "escapingEdge"), ("function", funcJson f), ("source", toJson source),
      ("target", toJson target)]
  | .callToNonEntry source target =>
    Json.mkObj [("kind", "callToNonEntry"), ("source", toJson source), ("target", toJson target)]
  | .undeclaredExternal source name =>
    Json.mkObj [("kind", "undeclaredExternal"), ("source", toJson source), ("symbol", toJson name)]
  | .misalignedTarget f source target =>
    Json.mkObj [("kind", "misalignedTarget"), ("function", funcJson f), ("source", toJson source),
      ("target", toJson target)]
  | .fallsOffEnd f source =>
    Json.mkObj [("kind", "fallsOffEnd"), ("function", funcJson f), ("source", toJson source)]

/-- A control-flow rejection, as the constructor that fired and what it names. -/
def cfgRejectJson : CfgReject → Json
  | .regionWraps limit => Json.mkObj [("kind", "regionWraps"), ("limit", toJson limit)]
  | .notAFunction f => Json.mkObj [("kind", "notAFunction"), ("function", funcJson f)]
  | .unordered first second =>
    Json.mkObj [("kind", "unordered"), ("first", toJson first.start),
      ("second", toJson second.start)]
  | .blockOutside b =>
    Json.mkObj [("kind", "blockOutside"), ("start", toJson b.start),
      ("terminator", toJson b.terminator)]
  | .blockNotAligned addr =>
    Json.mkObj [("kind", "blockNotAligned"), ("address", toJson addr)]
  | .uncovered start stop =>
    Json.mkObj [("kind", "uncovered"), ("start", toJson start), ("stop", toJson stop)]
  | .overlap first second =>
    Json.mkObj [("kind", "overlap"), ("first", toJson first.start), ("second", toJson second.start)]
  | .interiorTransfer block addr =>
    Json.mkObj [("kind", "interiorTransfer"), ("block", toJson block.start),
      ("address", toJson addr)]
  | .noEntryBlock entry => Json.mkObj [("kind", "noEntryBlock"), ("entry", toJson entry)]
  | .missingEdge source target =>
    Json.mkObj [("kind", "missingEdge"), ("source", toJson source), ("target", toJson target)]
  | .unjustifiedEdge source target =>
    Json.mkObj [("kind", "unjustifiedEdge"), ("source", toJson source), ("target", toJson target)]
  | .edgeTargetNotBlockStart source target =>
    Json.mkObj [("kind", "edgeTargetNotBlockStart"), ("source", toJson source),
      ("target", toJson target)]
  | .terminatorFallsOut block =>
    Json.mkObj [("kind", "terminatorFallsOut"), ("block", toJson block.start),
      ("terminator", toJson block.terminator)]

/-! ## Reading a partition back from JSON -/

/-- A natural number field. -/
def natField (obj : Json) (name : String) : Except String Nat := do
  let value ← obj.getObjValAs? Nat name
  pure value

/-- A partition in the shape `partitionJson` prints. -/
def partitionOfJson (json : Json) : Except String Partition := do
  let funcs ← (← json.getObjValAs? (Array Json) "functions").toList.mapM fun entry => do
    pure ({ name := ← entry.getObjValAs? String "name", entry := ← natField entry "entry",
            size := ← natField entry "size" } : FunctionSpec)
  let padding ← (← json.getObjValAs? (Array Json) "padding").toList.mapM fun entry => do
    pure (← natField entry "start", ← natField entry "stop")
  let relocs ← (← json.getObjValAs? (Array Json) "relocs").toList.mapM fun entry => do
    let target ← entry.getObjVal? "target"
    let kind ← target.getObjValAs? String "kind"
    let what ← match kind with
      | "internal" => pure (Target.internal (← natField target "address"))
      | "external" => pure (Target.external (← target.getObjValAs? String "symbol"))
      | other => throw s!"unknown relocation target kind {other}"
    pure (← natField entry "offset", what)
  let externals ← (← json.getObjValAs? (Array Json) "externals").toList.mapM fun entry =>
    entry.getStr?
  pure { funcs, padding, relocs, externals }

/-! ## The three modes -/

/-- Decode a region and print one line per instruction, then its edges. -/
def disasm (region : Region) : IO UInt32 := do
  match region.decode region.bytes.length with
  | .error (.undecodable addr) =>
    IO.println s!"error: no instruction of the model decodes at {hex addr 8}"
    IO.println s!"  the region is {region.bytes.length} bytes from {hex region.base 8}"
    pure 1
  | .error .outOfFuel =>
    IO.println "error: the decoding walk ran out of fuel"
    pure 1
  | .ok ds =>
    for d in ds do
      IO.println s!"{hex d.addr 8}  {instrBytes region d}  {oneLine d.instr}"
      IO.println s!"          edges: {String.intercalate ", " (d.edges.map edgeString)}"
    IO.println s!"{ds.length} instructions, {region.bytes.length} bytes"
    pure 0

/-- The accepted decomposition, as JSON. -/
def acceptedJson (region : Region) (acc : Accepted) (instructions : Nat) : Json :=
  Json.mkObj [
    ("accepted", Json.bool true),
    ("base", toJson region.base),
    ("bytes", toJson region.bytes.length),
    ("instructions", toJson instructions),
    ("functions", Json.arr ((acc.bodies.map fun entry =>
      Json.mkObj [("name", toJson entry.1.name), ("entry", toJson entry.1.entry),
        ("size", toJson entry.1.size), ("instructions", toJson entry.2.length)]).toArray)),
    ("padding", Json.arr ((acc.partition.padding.map fun q =>
      Json.mkObj [("start", toJson q.1), ("stop", toJson q.2)]).toArray)),
    ("relocatedCalls", Json.arr ((acc.relocatedCalls.map fun e =>
      Json.mkObj [("site", toJson e.1), ("target", targetJson e.2)]).toArray)),
    ("assumedExternal", Json.arr ((acc.assumedExternal.map fun e =>
      Json.mkObj [("site", toJson e.1), ("symbol", toJson e.2)]).toArray))]

/-- Run the checker and print its verdict. -/
def runCheck (region : Region) (p : Partition) (withCfg : Bool) : IO UInt32 := do
  let fuel := region.bytes.length
  match check region p fuel with
  | .error rej =>
    IO.println (Json.mkObj [("accepted", Json.bool false),
      ("rejection", rejectJson rej)]).pretty
    pure 1
  | .ok acc =>
    let instructions := (acc.bodies.map fun entry => entry.2.length).sum
    if !withCfg then
      IO.println (acceptedJson region acc instructions).pretty
      pure 0
    else
      let mut graphs : Array Json := #[]
      let mut failed := false
      for f in acc.partition.funcs do
        let spec := CfgPropose.ofFunction acc f
        match checkCfg acc spec with
        | .ok _ => graphs := graphs.push (cfgJson spec)
        | .error rej =>
          failed := true
          graphs := graphs.push (Json.mkObj [("function", toJson f.name),
            ("accepted", Json.bool false), ("rejection", cfgRejectJson rej)])
      let body := (acceptedJson region acc instructions).setObjVal! "cfg" (Json.arr graphs)
      IO.println body.pretty
      pure (if failed then 1 else 0)

/-! ## The entry point -/

/-- Read the request from the environment, run it, and exit with its status. -/
def main : IO UInt32 := do
  let mode := (← envVar "SIL_DECOMPILE_MODE").getD "check"
  let sectionName := (← envVar "SIL_DECOMPILE_SECTION").getD ".text"
  let withCfg := (← envVar "SIL_DECOMPILE_CFG").isSome
  let input ← match ← envVar "SIL_DECOMPILE_INGESTED" with
    | some name =>
      match ingested.lookup name with
      | some obj => pure (Input.object obj)
      | none => do
        IO.eprintln s!"no ingested object named {name}; known:           {String.intercalate ", " (ingested.map Prod.fst)}"
        return 1
    | none =>
      match ← envVar "SIL_DECOMPILE_FILE" with
      | none => do IO.eprintln "neither SIL_DECOMPILE_FILE nor SIL_DECOMPILE_INGESTED is set"
                   return 1
      | some file => do
        let raw ← IO.FS.readBinFile file
        match classify raw with
        | .error message => do IO.eprintln s!"{file}: {message}"; return 1
        | .ok input => pure input
  let baseText := (← envVar "SIL_DECOMPILE_BASE").getD "0"
  let some base := parseAddr baseText
    | do IO.eprintln s!"SIL_DECOMPILE_BASE: {baseText} is not an address"; return 1
  -- The region, and the partition the proposer offers for it.
  let (region, proposed, source) ← match input with
    | .object obj =>
      match sectionBytes obj sectionName with
      | none => do IO.eprintln s!"no section named {sectionName}"; return 1
      | some (_, bytes) =>
        let region : Region := { base := 0, bytes }
        match Silmaril.X86.Decompile.Propose.ofSymbols obj sectionName with
        | some p => pure (region, p, "symbols")
        | none => pure (region, Propose.ofStripped region bytes.length, "stripped")
    | .code bytes =>
      let region : Region := { base, bytes }
      pure (region, Propose.ofStripped region bytes.length, "stripped")
  match mode with
  | "disasm" => disasm region
  | "propose" =>
    let base := partitionJson proposed
    let body := base.setObjVal! "base" (toJson region.base)
      |>.setObjVal! "bytes" (toJson region.bytes.length)
      |>.setObjVal! "source" (toJson source)
    let body ← if !withCfg then pure body else
      match check region proposed region.bytes.length with
      | .error _ => pure (body.setObjVal! "cfg" (toJson "unavailable: the partition is rejected"))
      | .ok acc =>
        pure (body.setObjVal! "cfg"
          (Json.arr ((acc.partition.funcs.map fun f => cfgJson (CfgPropose.ofFunction acc f))
            |>.toArray)))
    IO.println body.pretty
    pure 0
  | "check" =>
    let p ← match ← envVar "SIL_DECOMPILE_PARTITION" with
      | none => pure proposed
      | some path =>
        match Json.parse (← IO.FS.readFile path) with
        | .error message => do IO.eprintln s!"{path}: {message}"; return 1
        | .ok json =>
          match partitionOfJson json with
          | .error message => do IO.eprintln s!"{path}: {message}"; return 1
          | .ok p => pure p
    runCheck region p withCfg
  | other => do IO.eprintln s!"unknown mode {other}"; return 1

end DecompileTool

/-- The executable's entry point. -/
def main : IO UInt32 := DecompileTool.main
