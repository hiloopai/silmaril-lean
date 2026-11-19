module

public import Silmaril.Elf.Asm.Defs
public import Lean.Data.Json

/-! # The JSON form of assembly functions (`silmaril.elf.asm/1`), for views

A view (the explorer's assembly tab, a report) reads functions as JSON. This module fixes that
form; `tools/elf-asm` writes it for the sample functions, with each function's **evidence read
from theorem statements** (the tool imports the checked theorem modules and classifies every
theorem by the heads of its statement's conjuncts, its function argument and its file argument,
never by its name; a self-test on decoys checks that a copy of a function, another file, a lone
contract or a misleading name gives no evidence).

```
{ "schema": "silmaril.elf.asm/1",
  "files": [ { "decl", "path", "sha256" } ],
  "functions": [ {
      "decl", "file", "name",                      -- "file": the decl of the function's file
      "arch": { "id": "elf64-le/em62", "machine", "class", "data", "osabi" },
      "abiRef": "sysv64" | null,                   -- metadata, never evidence
      "abi": { "id", "source", "note" },           -- the same metadata, with its cited document
      "symbol": { "table": "symtab" | "dynsym", "index" } | null,
      "extent": { "vaddr": "0x…", "size", "fileOff": "0x…" | null, "segment": n | null, "shndx": n | null,
                  "addrKind": "link", "loadBase": null },  -- link-time addresses; no load base
      "listing": { "tool", "verified": false },     -- who printed the lines; never verified
      "bytesHex": "89d2…",
      "lines": [ { "off", "len", "addr": "0x…", "text", "label" } ],   -- display only
      "refs": [ { "off", "target": "0x…" | null, "symbol", "kind", "addend", "origin",
                  "targetIn": { "segment", "section", "readOnly", "provenance" } } ],  -- metadata
      "decodings": [ { "model", "decl", "insns": [ { "off", "len", "addr", "render" } ] } ],
      "evidence": [ { "kind", "decl", "model", "axioms", "hypotheses" } ] } ] }
```

**Version 1.1** adds optional fields only: `schemaVersion`; `abi {id, source}`; `extent.addrKind`
(`"link"`: link-time addresses) and `extent.loadBase` (`null`); `listing {tool, verified: false}`;
per line `source` (`"objdump"`) and `unverified: true`; per decoding `source: "lean-decode"`; per
ref `version` and `targetIn {segment, section, readOnly, provenance, note}` (metadata); per
evidence `axis`, `status`, `problemId` (`null`: evidence comes from theorems, not registered
rows), `assumptions`, `note`; per function `axes` (each axis's status, per model where models
differ; `none` when no theorem speaks to it).

**Version 1.2** makes evidence status a theorem status, never a problem status: `statusKind` is
`"theorem"`, `status` is `proved` or `refuted` (every piece of evidence is a proved theorem), and
`applicability` is `unconditional` (no `Prop` premise in the statement) or `conditional`
(premises in `assumptions`, not discharged). Universally quantified data is not a premise, and
`unconditional` concerns the statement only: each claim stays relative to its `model`, the file
and its definitions. 1.1's `open` is no longer emitted; it never meant an open standard problem. A `noDecode` refutation says only that the model's decoder
(an `Option`) returns nothing: invalid, unsupported and incomplete bytes are not told apart.

Addresses and file offsets are hexadecimal strings (they exceed JavaScript's exact integers);
counts and in-function offsets are numbers. Unknown values are `null`, never `0`.

Evidence kinds (one per proposition of `Silmaril.Elf.Asm`, plus the two neighbours views need):
`arch` (`ArchOf`), `bytes` (`BytesAt`), `sectionBytes` (`SectionBytesAt`), `code` (`Silmaril.Elf.CodeAt` of the function's
address and bytes), `symbol` (`SymbolOf`), `lineTiles` (`LinesTile`), `decode` (`DecodesAs`;
`model` is the `Isa`), `noDecode` (`¬ DecodesAs` for every decoding), `notArch` (`¬ ArchOf`), `notBytes` (`¬ BytesAt`),
`refs` (`RefsGrounded`),
`unrelocated` (`Unrelocated`), `present` (`Load.PresentFn` of the function's name),
`contract` (a machine contract `FnContract.Spec.Total`, counted only when stated in the same
theorem as the function's `bytes` or `code` fact; `model` is the machine). `hypotheses` lists
the theorem's premises (empty for an unconditional fact); `axioms` its axioms. There is no single
status rank: the kinds are independent (`Silmaril.Elf.Asm`, module doc).
-/

@[expose] public section

namespace Silmaril.Elf.Asm.Export

open Lean (Json Name ToJson toJson)

def schema : String := "silmaril.elf.asm/1"

/-- The minor version: `1.2` replaces 1.1's evidence status `open` by `status: proved` with
`applicability: conditional` (and adds `statusKind: "theorem"`); `1.1` added optional fields only (`abi`, `extent.addrKind`/`loadBase`,
`listing`, line `source`/`unverified`, decoding `source`, ref `version`/`targetIn`, evidence
`axis`/`status`/`problemId`/`assumptions`/`note`, function `axes`). -/
def schemaVersion : String := "1.2"

/-- `0x…`, lowercase. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Two lowercase hexadecimal digits per byte. -/
def bytesHex (bs : List Byte) : String :=
  String.join (bs.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length < 2 then "0" ++ s else s)

/-- One piece of evidence, as read from a theorem statement. -/
structure Evidence where
  kind : String
  decl : Name
  model : Option String := none
  axioms : List Name := []
  hypotheses : List String := []
  deriving Inhabited

/-- One decoding, rendered. -/
structure Decoding where
  model : String
  decl : Name
  /-- `(offset, length, rendering)` of each instruction. -/
  insns : List (Nat × Nat × String)

/-- A decoding as data for the view. -/
def Decoding.of (isa : Isa) (decl : Name) (d : List (Nat × isa.Instr)) : Decoding :=
  ⟨isa.name, decl, (d.foldl (fun (o, acc) (n, i) => (o + n, (o, n, isa.render i) :: acc)) (0, [])).2.reverse⟩

def optNat (o : Option Nat) : Json := match o with | some n => toJson n | none => Json.null
def optHex (o : Option Nat) : Json := match o with | some n => Json.str (hex n) | none => Json.null
def optStr (o : Option String) : Json := match o with | some s => Json.str s | none => Json.null
def name (n : Name) : Json := Json.str n.toString

def archJson (a : Arch) : Json := Json.mkObj [
  ("id", Json.str s!"elf{if a.cls = 2 then "64" else "32"}-{if a.data = 1 then "le" else "be"}/em{a.machine}"),
  ("machine", toJson a.machine), ("class", toJson a.cls), ("data", toJson a.data),
  ("osabi", toJson a.osABI)]

def extentJson (e : Extent) : Json := Json.mkObj [
  ("vaddr", Json.str (hex e.vaddr)), ("size", toJson e.size), ("fileOff", optHex e.fileOff),
  ("segment", optNat e.segment), ("shndx", optNat e.shndx)]

def originJson : RefOrigin → Json
  | .reloc sel k => Json.mkObj [("kind", "reloc"), ("index", toJson k),
      ("selector", match sel with
        | .dynamic => Json.str "dynamic"
        | .forSection i => Json.str s!"section {i}")]
  | .decoded => Json.mkObj [("kind", "decoded")]
  | .display => Json.mkObj [("kind", "display")]

def refJson (r : CodeRef) : Json := Json.mkObj [
  ("off", toJson r.off), ("target", optHex r.target), ("symbol", optStr r.symbol),
  ("version", optStr r.version),
  ("kind", toJson r.kind), ("addend", Json.str (toString r.addend)), ("origin", originJson r.origin)]

/-- A listing line. Its `source` is the tool that printed it; it is always `unverified`: no
proposition reads a line's text. -/
def lineJson (base : Nat) (src : Option String) (l : Line) : Json := Json.mkObj [
  ("off", toJson l.off), ("len", toJson l.len), ("addr", Json.str (hex (base + l.off))),
  ("text", Json.str l.text), ("label", optStr l.label),
  ("source", Json.str (src.getD "unknown")), ("unverified", Json.bool true)]

def decodingJson (base : Nat) (d : Decoding) : Json := Json.mkObj [
  ("model", Json.str d.model), ("decl", name d.decl), ("source", Json.str "lean-decode"),
  ("note", Json.str "the instructions are this model's decoder output; that they decode the bytes is the `decode` evidence of this model, the renderings are display"),
  ("insns", Json.arr (d.insns.toArray.map fun (o, n, s) => Json.mkObj [
    ("off", toJson o), ("len", toJson n), ("addr", Json.str (hex (base + o))), ("render", Json.str s)]))]

/-- The axis an evidence kind is about, and whether it refutes it. -/
def axisOf : String → String × Bool
  | "notArch" => ("arch", true)
  | "notBytes" => ("bytes", true)
  | "noDecode" => ("decode", true)
  | k => (k, false)

/-- The axes every function is reported on (`none` when no theorem speaks to one). -/
def axes : List String :=
  ["arch", "bytes", "sectionBytes", "code", "symbol", "lineTiles", "decode", "refs", "unrelocated",
    "present", "contract"]

/-- The proof status of one piece of evidence: `refuted` (a negation is proved) or `proved`.
Every piece of evidence is a proved theorem; there is no `open` status here, which would mean an
unsolved standard problem. -/
def statusOf (e : Evidence) : String := if (axisOf e.kind).2 then "refuted" else "proved"

/-- Whether the theorem holds outright or under premises: `conditional` when its statement has
`Prop`-typed premises (listed in `assumptions`, not discharged), `unconditional` otherwise.
Universally quantified data (an entry address, a decoding) is not a premise. `unconditional` is
about the theorem statement only: every claim stays relative to its model, the file, and the
definitions it is stated with. -/
def applicabilityOf (e : Evidence) : String :=
  if e.hypotheses.isEmpty then "unconditional" else "conditional"

def evidenceJson (e : Evidence) : Json := Json.mkObj [
  ("kind", Json.str e.kind), ("axis", Json.str (axisOf e.kind).1),
  ("statusKind", Json.str "theorem"), ("status", Json.str (statusOf e)),
  ("applicability", Json.str (applicabilityOf e)),
  ("decl", name e.decl), ("problemId", Json.null), ("model", optStr e.model),
  ("axioms", Json.arr (e.axioms.toArray.map name)),
  ("hypotheses", Json.arr (e.hypotheses.toArray.map Json.str)),
  ("assumptions", Json.arr (e.hypotheses.toArray.map Json.str)),
  ("note", if e.kind == "noDecode" then
      Json.str "the model's decoder returns none at some instruction: these bytes are not decodable by this model; invalid, unsupported and incomplete are not distinguished (the decoder is an Option)"
    else Json.null)]

/-- **The status of each axis** (and, for `decode`, `refs` and `contract`, each model):
`proved` or `refuted` with `applicability` (`unconditional` if some proof of it has no premise,
else `conditional`), `conflict` if a statement and its negation are both proved, `none` when no
theorem speaks to the axis. -/
def axesJson (ev : List Evidence) : Json :=
  let keys := (ev.map fun e => ((axisOf e.kind).1, e.model)).eraseDups
  let st (k : String × Option String) : String × Option String :=
    let es := ev.filter fun e => ((axisOf e.kind).1, e.model) == k
    let pr := es.filter (statusOf · == "proved")
    let rf := es.filter (statusOf · == "refuted")
    let app (xs : List Evidence) : Option String :=
      some (if xs.any (applicabilityOf · == "unconditional") then "unconditional" else "conditional")
    if !pr.isEmpty && !rf.isEmpty then ("conflict", none)
    else if !pr.isEmpty then ("proved", app pr)
    else if !rf.isEmpty then ("refuted", app rf) else ("none", none)
  let present := keys.map fun k => let (a, b) := st k
    Json.mkObj [("axis", Json.str k.1), ("model", optStr k.2), ("status", Json.str a),
      ("applicability", optStr b)]
  let absent := (axes.filter fun a => !(keys.any (·.1 == a))).map fun a =>
    Json.mkObj [("axis", Json.str a), ("model", Json.null), ("status", Json.str "none"),
      ("applicability", Json.null)]
  Json.arr (present ++ absent).toArray

/-- The name of a section, as text (display). -/
def nameText (n : Silmaril.Formats.ELF.NameBytes) : String := String.ofList (n.map fun b => Char.ofNat b.toNat)

/-- **Where a reference's target lies in the file** (provenance metadata for views, computed from
the parse; not a theorem): the first `PT_LOAD` and the first allocated section containing the
target address, and whether that segment is read-only. -/
def targetJson (A : File) (t : Nat) : Json :=
  let seg := (A.phdrs.zipIdx.find? fun (ph, _) => ph.kind == PT_LOAD &&
    decide (ph.virtualAddress ≤ t) && decide (t < ph.virtualAddress + ph.memorySize))
  let sec := (A.sections.zipIdx.find? fun (s, _) => s.header.flags / 2 % 2 == 1 &&
    decide (s.header.address ≤ t) && decide (t < s.header.address + s.header.size))
  Json.mkObj [
    ("segment", match seg with | some (_, i) => toJson i | none => Json.null),
    ("section", match sec with | some (s, _) => Json.str (nameText s.name) | none => Json.null),
    ("readOnly", match seg with | some (ph, _) => Json.bool (ph.flags / 2 % 2 == 0) | none => Json.null),
    ("provenance", Json.str "metadata: computed from the parse, not a theorem"),
    ("note", Json.str "readOnly is the flag of the first segment containing the target address; it does not authorize the address as the code's data and says nothing about a range (the theorems are Asm.RefTargetIn, Asm.RefTargetReadOnly)")]

/-- **A function as JSON**, with its decodings and evidence. With the file's parse `A`, each
reference with a target also gets its target's segment, section and read-only flag
(`targetJson`, metadata). -/
def functionJson (decl : Name) (f : AsmFunction) (ds : List Decoding) (ev : List Evidence)
    (A : Option File := none) : Json :=
  Json.mkObj [
    ("decl", name decl), ("name", Json.str f.name), ("arch", archJson f.arch),
    ("abiRef", optStr f.abiRef),
    ("abi", Json.mkObj [("id", optStr f.abiRef), ("source", optStr f.abiSource),
      ("note", Json.str "metadata: no proposition reads it")]),
    ("symbol", match f.symbol with
      | some r => Json.mkObj [("table", Json.str (match r.table with
          | .symtab => "symtab" | .dynsym => "dynsym")), ("index", toJson r.index)]
      | none => Json.null),
    ("extent", match extentJson f.extent with
      | .obj kvs => .obj ((kvs.insert "addrKind" (Json.str "link")).insert "loadBase" Json.null)
      | j => j),
    ("bytesHex", Json.str (bytesHex f.bytes)),
    ("listing", Json.mkObj [("tool", optStr f.listingTool), ("verified", Json.bool false)]),
    ("lines", Json.arr (f.lines.toArray.map (lineJson f.extent.vaddr
      (f.listingTool.map fun t => if (t.splitOn "objdump").length > 1 then "objdump" else t)))),
    ("refs", Json.arr (f.refs.toArray.map fun r => match refJson r, A, r.target with
      | .obj kvs, some A, some t => .obj (kvs.insert "targetIn" (targetJson A t))
      | j, _, _ => j)),
    ("decodings", Json.arr (ds.toArray.map (decodingJson f.extent.vaddr))),
    ("evidence", Json.arr (ev.toArray.map evidenceJson)),
    ("axes", axesJson ev)]

end Silmaril.Elf.Asm.Export
