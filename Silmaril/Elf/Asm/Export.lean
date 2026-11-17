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
      "symbol": { "table": "symtab" | "dynsym", "index" } | null,
      "extent": { "vaddr": "0x…", "size", "fileOff": "0x…" | null, "segment": n | null, "shndx": n | null },
      "bytesHex": "89d2…",
      "lines": [ { "off", "len", "addr": "0x…", "text", "label" } ],   -- display only
      "refs": [ { "off", "target": "0x…" | null, "symbol", "kind", "addend", "origin" } ],
      "decodings": [ { "model", "decl", "insns": [ { "off", "len", "addr", "render" } ] } ],
      "evidence": [ { "kind", "decl", "model", "axioms", "hypotheses" } ] } ] }
```

Addresses and file offsets are hexadecimal strings (they exceed JavaScript's exact integers);
counts and in-function offsets are numbers. Unknown values are `null`, never `0`.

Evidence kinds (one per proposition of `Silmaril.Elf.Asm`, plus the two neighbours views need):
`arch` (`ArchOf`), `bytes` (`BytesAt`), `sectionBytes` (`SectionBytesAt`), `code` (`Silmaril.Elf.CodeAt` of the function's
address and bytes), `symbol` (`SymbolOf`), `lineTiles` (`LinesTile`), `decode` (`DecodesAs`;
`model` is the `Isa`), `noDecode` (`¬ DecodesAs` for every decoding), `notArch` (`¬ ArchOf`), `notBytes` (`¬ BytesAt`),
`refs` (`RefsGrounded`),
`contract` (a machine contract `FnContract.Spec.Total`, counted only when stated in the same
theorem as the function's `bytes` or `code` fact; `model` is the machine). `hypotheses` lists
the theorem's premises (empty for an unconditional fact); `axioms` its axioms. There is no single
status rank: the kinds are independent (`Silmaril.Elf.Asm`, module doc).
-/

@[expose] public section

namespace Silmaril.Elf.Asm.Export

open Lean (Json Name ToJson toJson)

def schema : String := "silmaril.elf.asm/1"

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
  ("kind", toJson r.kind), ("addend", Json.str (toString r.addend)), ("origin", originJson r.origin)]

def lineJson (base : Nat) (l : Line) : Json := Json.mkObj [
  ("off", toJson l.off), ("len", toJson l.len), ("addr", Json.str (hex (base + l.off))),
  ("text", Json.str l.text), ("label", optStr l.label)]

def decodingJson (base : Nat) (d : Decoding) : Json := Json.mkObj [
  ("model", Json.str d.model), ("decl", name d.decl),
  ("insns", Json.arr (d.insns.toArray.map fun (o, n, s) => Json.mkObj [
    ("off", toJson o), ("len", toJson n), ("addr", Json.str (hex (base + o))), ("render", Json.str s)]))]

def evidenceJson (e : Evidence) : Json := Json.mkObj [
  ("kind", Json.str e.kind), ("decl", name e.decl), ("model", optStr e.model),
  ("axioms", Json.arr (e.axioms.toArray.map name)),
  ("hypotheses", Json.arr (e.hypotheses.toArray.map Json.str))]

/-- **A function as JSON**, with its decodings and evidence. -/
def functionJson (decl : Name) (f : AsmFunction) (ds : List Decoding) (ev : List Evidence) : Json :=
  Json.mkObj [
    ("decl", name decl), ("name", Json.str f.name), ("arch", archJson f.arch),
    ("abiRef", optStr f.abiRef),
    ("symbol", match f.symbol with
      | some r => Json.mkObj [("table", Json.str (match r.table with
          | .symtab => "symtab" | .dynsym => "dynsym")), ("index", toJson r.index)]
      | none => Json.null),
    ("extent", extentJson f.extent), ("bytesHex", Json.str (bytesHex f.bytes)),
    ("lines", Json.arr (f.lines.toArray.map (lineJson f.extent.vaddr))),
    ("refs", Json.arr (f.refs.toArray.map refJson)),
    ("decodings", Json.arr (ds.toArray.map (decodingJson f.extent.vaddr))),
    ("evidence", Json.arr (ev.toArray.map evidenceJson))]

end Silmaril.Elf.Asm.Export
