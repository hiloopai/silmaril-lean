import Lean.Data.Json
import Silmaril.Data.Layout.Header.Defs
import Silmaril.Data.Layout.Bitfield.Defs
import Silmaril.Machine.Abi.Conformance.Defs
import Silmaril.Machine.Abi.Conformance.Win64.Defs
import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs
import Silmaril.Machine.Abi.Conformance.Import.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.Arith.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.Probe.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.ZlibSolo.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.ZlibHosted.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.GlibcString.Defs

/-!
# The explorer's Headers tab data (`OUTDIR/headers/index.json`)

For each pinned header: what the subset reader (`Silmaril.Data.Layout.Header.read`) reads or why
it refuses; each prototype's C spelling and qualifiers; what each versioned ABI definition
(`sysvInt`, `win64Int`, `sysvScalar`) lowers it to, with the header's own tag definitions
(`Header.env`: `sysvScalar` classifies small aggregates passed by value from their layout), or the
reason it refuses; the call plan of
`sysvScalar` (where each argument and the result go); and each aggregate's layout under the
System V x86-64 and Microsoft x64 data models (`bitLayout`).

**The clang route.** A header may also have a pinned clang import
(`Data.Layout.Header.Import.Pinned`, associated by `clangOf`; glibc's `string.h` has only this
route). For it: the provenance (`Provenance.parse` of the committed `.prov`), the entry counts,
and per entry its name, kind, location, C declaration (or the import's reason), calling
convention, attributes, symbol and asm label, and per ABI definition the `status`
(`Machine.Abi.Conformance.Import`: claimable, unsupported or internal, with the reason) with the
conventions `clangCcs` names, plus, for a prototype, the same lowering and call plan as on the
subset route. The entries are the generated literals (`Pinned.<Name>.entries`); the JSON
artifact is not read here.

Every value is computed by the definitions that conformance rows and layout theorems use, run
here on the header files and literals; none is a theorem. A view must say so.

    lake env .lake/build/bin/header-pages OUTDIR
-/

open Lean (Json)
open Silmaril.Data.Layout
open Silmaril.Data.Layout.Header
open Silmaril.Machine.Abi.Conformance
open Silmaril.Data.Layout.Header.Import (Entry Body Fn Got CallConv Attr DeclKind Imported Provenance)

def js (s : String) : Json := Json.str s
def jn (n : Nat) : Json := Json.num n

/-- A pinned header: id, title, the files (name in the include graph, path), the root. -/
structure Src where
  id : String
  title : String
  files : List (String × String)
  root : String
  note : String := ""
  /-- Whether the subset reader is run on `files` (a clang-only header has no files here). -/
  subset : Bool := true

def sources : List Src := [
  { id := "arith", title := "elf-ladder rung 01 arith.h (and the rt.h it includes)",
    files := [("rt.h", "examples/elf-ladder/common/rt.h"), ("arith.h", "examples/elf-ladder/01-leaf-arith/arith.h")],
    root := "arith.h", note := "the header of the leaf-arith conformance rows (their status is in the registry, not here)" },
  { id := "zlib-hosted", title := "zlib 1.3.1 zlib.h checksum excerpt, hosted",
    files := [("zconf.h", "examples/headers/zlib-1.3.1/zconf-hosted.h"), ("zlib.h", "examples/headers/zlib-1.3.1/zlib.h")],
    root := "zlib.h", note := "the header of the shared-library rows" },
  { id := "zlib-solo", title := "zlib 1.3.1 zlib.h checksum excerpt, -DZ_SOLO",
    files := [("zconf.h", "examples/headers/zlib-1.3.1/zconf-solo.h"), ("zlib.h", "examples/headers/zlib-1.3.1/zlib.h")],
    root := "zlib.h", note := "the header of the static zlib-checksums rows" },
  { id := "probe", title := "probe.h (the clang import's probe header)",
    files := [("probe.h", "examples/headers/probe/probe.h")], root := "probe.h",
    note := "exercises what the subset reader refuses" },
  { id := "layout-demo", title := "layout demo: aggregates under two data models",
    files := [("demo.h", "examples/headers/layout/demo.h")], root := "demo.h" },
  { id := "glibc-string", title := "glibc string.h (the clang import's hosted header)",
    files := [], root := "/usr/include/string.h", subset := false,
    note := "only the clang route: the file is the pinned clang image's, not in this repository" }]

/-- The ABI definitions a prototype is lowered by. -/
def abis : List (String × AbiDef) := [("sysvInt", sysvInt), ("win64Int", win64Int), ("sysvScalar", sysvScalar)]

/-- A pinned clang import: its key, the Lean names of its value and literal, the `.prov` text and
the literal entries (`Pinned.<Name>.entries`). -/
structure Artifact where
  key : String
  value : String
  literal : String
  prov : String
  entries : List Entry

open Silmaril.Data.Layout.Header.Import.Pinned in
def artifacts : List Artifact := [
  ⟨"arith", "Pinned.arith", "Pinned.Arith.entries", arithProv, Arith.entries⟩,
  ⟨"probe", "Pinned.probe", "Pinned.Probe.entries", probeProv, Probe.entries⟩,
  ⟨"zlibSolo", "Pinned.zlibSolo", "Pinned.ZlibSolo.entries", zlibSoloProv, ZlibSolo.entries⟩,
  ⟨"zlibHosted", "Pinned.zlibHosted", "Pinned.ZlibHosted.entries", zlibHostedProv, ZlibHosted.entries⟩,
  ⟨"glibcString", "Pinned.glibcString", "Pinned.GlibcString.entries", glibcStringProv,
    GlibcString.entries⟩]

/-- The import of an artifact: its provenance and the literal entries. -/
def Artifact.imported (a : Artifact) : Imported := ⟨.parse a.prov, a.entries, none⟩

/-- **Which clang artifact a header page shows**, and how its input relates to the files the
subset route reads. -/
def clangOf : String → Option (String × String)
  | "arith" => some ("arith", "the same arith.h and rt.h the subset route reads")
  | "probe" => some ("probe", "the same probe.h the subset route reads")
  | "zlib-solo" => some ("zlibSolo", "the full zlib 1.3.1 release zlib.h and its zconf.h, with \
      -DZ_SOLO; the subset route reads a checksum excerpt")
  | "zlib-hosted" => some ("zlibHosted", "the full zlib 1.3.1 release zlib.h and its zconf.h, \
      hosted; the subset route reads a checksum excerpt")
  | "glibc-string" => some ("glibcString", "glibc's string.h in the pinned clang image")
  | _ => none

/-- The conventions each ABI definition accepts on the import's target
(`x86_64-unknown-linux-gnu`): the System V definitions `sysvCcs` (the default C convention and
`sysv_abi`); the Microsoft x64 definition `ms_abi`, the attribute that selects it there. -/
def clangCcs : String → List CallConv
  | "win64Int" => [.msAbi]
  | _ => sysvCcs

/-- Why an ABI definition accepts the conventions it does on the imports' target. -/
def clangCcsNote : String → String
  | "win64Int" => "every pinned import targets x86_64-unknown-linux-gnu, where the default C \
      convention is System V: only ms_abi declarations follow Microsoft x64 there, so a \
      default-convention function is unsupported under win64Int here. A Windows-target import \
      (where the default is Microsoft x64) is not pinned."
  | _ => "the default C convention and sysv_abi: System V on the imports' target \
      x86_64-unknown-linux-gnu"

def exceptJson {α : Type} (f : α → Json) : Except String α → Json
  | .ok a => Json.mkObj [("ok", f a)]
  | .error e => Json.mkObj [("refused", js e)]

def locText : Silmaril.Machine.SystemV.Abi.Location → String
  | .gp r => (reprStr r).replace "Silmaril.X86.Reg." ""
  | .vector i o => s!"xmm{i}" ++ (if o = 0 then "" else s!"+{o}")
  | .x87 i => s!"st({i})"

def chunksText (cs : List Silmaril.Machine.SystemV.Abi.Chunk) : String :=
  ", ".intercalate (cs.map fun c => s!"{locText c.location}[{c.offset}..{c.offset + c.bytes})")

def planJson (p : Silmaril.Machine.SystemV.Abi.CallPlan) : Json :=
  Json.mkObj [
    ("arguments", Json.arr (p.arguments.toArray.map fun a =>
      js (if a.chunks.isEmpty then (match a.stackOffset with
        | some o => s!"stack [rsp+8+{o}]" | none => "?") else chunksText a.chunks))),
    ("result", js (match p.result with
      | .void => "void" | .direct cs => chunksText cs | .indirect s al => s!"memory (sret, {s} B, align {al})")),
    ("stackSize", jn p.stackSize)]

/-- A constructor's name without its namespace (`Silmaril.C.Api.Scalar.int32` → `int32`). -/
def short (s : String) : String := (s.splitOn ".").getLast!

def sigText (args : List String) (ret : Option String) : String :=
  "(" ++ ", ".intercalate args ++ ") → " ++ ret.getD "void"

/-- A scalar-fragment argument as text: its kind, or an aggregate's size and alignment. -/
def argText : Silmaril.Machine.Abi.SystemV.Scalar.Arg → String
  | .scalar k => short (reprStr k)
  | .agg a _ => s!"{a.name} ({a.size} B, align {a.align}, eightbytes {((reprStr a.eights).replace "Silmaril.Machine.Abi.SystemV.Scalar." "").replace "Silmaril.Machine.SystemV.Abi." ""})"

/-- An integer-fragment lowering: the C API signature, or the refusal. -/
def intLowering (r : Except String Silmaril.Machine.Abi.SystemV.Proto) : Json :=
  exceptJson (fun p => js (sigText (p.signature.arguments.map (short ∘ reprStr)) (p.signature.result.map (short ∘ reprStr)))) r

/-- Each ABI's view of one prototype. -/
def lowerings (env : Env) (cp : CProto) : Json := Json.mkObj <| abis.map fun (name, _) =>
  (name, match name with
    | "sysvScalar" =>
      match lowerScalar Silmaril.Data.Layout.sysvX86_64 env cp with
      | .error e => Json.mkObj [("refused", js e)]
      | .ok p => Json.mkObj [("ok", js (sigText (p.args.map argText) (p.result.map argText))),
          ("plan", exceptJson planJson (p.plan {}))]
    | "win64Int" =>
      match (win64Int.lower env cp : Except String Silmaril.Machine.Abi.SystemV.Proto) with
      | .error e => Json.mkObj [("refused", js e)]
      | .ok p => Json.mkObj [
          ("ok", js (sigText (p.signature.arguments.map (short ∘ reprStr)) (p.signature.result.map (short ∘ reprStr)))),
          -- Microsoft x64's closed-form plan (`Win64.plan`, the convention's `msPlan`): RCX, RDX,
          -- R8, R9, then 8-byte slots above the 32-byte shadow space; the outgoing area is the
          -- shadow space plus the stack arguments, 16-aligned.
          ("plan", Json.mkObj [("ok", planJson (Silmaril.Machine.Abi.Win64.plan p))]),
          ("planNote", js "Microsoft x64: RCX, RDX, R8, R9, then 8-byte stack slots; the outgoing area includes the 32-byte shadow space")]
    | _ => intLowering (sysvInt.lower env cp : Except String Silmaril.Machine.Abi.SystemV.Proto))

def protoJson (h : Header) (f : String) (cp : CProto) : Json :=
  Json.mkObj [("name", js f), ("c", js (cp.render f)),
    ("quals", match h.quals? f with
      | some q => js (reprStr q) | none => Json.null),
    ("lowering", lowerings h.env cp)]

def slotJson (s : BitSlot) : Json :=
  Json.mkObj [("name", js s.name), ("bitOffset", jn s.off), ("bits", jn s.width)]

/-- The bytes of `[0, size)` that no named member occupies (an unnamed bit-field is not a member
in C), as maximal ranges `[lo, hi)`. A byte a bit-field uses only partly is not padding here. -/
def paddingRanges (slots : List BitSlot) (size : Nat) : List (Nat × Nat) :=
  let used (b : Nat) : Bool := slots.any fun s =>
    s.name != "" && s.width > 0 && s.off < 8 * (b + 1) && 8 * b < s.off + s.width
  let pad := (List.range size).filter fun b => !used b
  (pad.foldl (fun (acc : List (Nat × Nat)) b => match acc with
    | (lo, hi) :: rest => if hi == b then (lo, b + 1) :: rest else (b, b + 1) :: acc
    | [] => [(b, b + 1)]) []).reverse

def layoutJson (pol : BitPolicy) (dm : DataModel) (env : Env) (d : Decl) : Json :=
  exceptJson (fun (slots, sh) =>
    let pad := paddingRanges slots sh.size
    Json.mkObj [("size", jn sh.size), ("align", jn sh.align),
      ("members", Json.arr (slots.toArray.map slotJson)),
      ("padding", Json.arr (pad.toArray.map fun (lo, hi) => Json.arr #[jn lo, jn hi])),
      -- the library's counts (`Data.Layout.paddingBytes`/`paddingBits`, the definitions the
      -- layout theorems state, e.g. `Header.rec_layout_sysv`); the ranges above are this tool's
      -- rendering of the same byte predicate, checked against `paddingBytes` by headers.mjs
      ("paddingBytes", jn (paddingBytes slots sh)),
      ("paddingBits", jn (paddingBits slots sh))]) (bitLayout pol dm env d)

def declJson (env : Env) (d : Decl) : Json :=
  Json.mkObj [("kind", js (match d.kind with | .struct => "struct" | .union => "union")),
    ("tag", js d.tag),
    ("members", Json.arr (d.fields.toArray.map fun fl => Json.mkObj [("name", js fl.name),
      ("type", js (fl.ty.declare "")), ("bits", match fl.bits with | some b => jn b | none => Json.null)])),
    ("layouts", Json.mkObj [("sysvX86_64", layoutJson .sysv sysvX86_64 env d),
      ("msX64", layoutJson .ms msX64 env d)])]

/-! ## The clang route -/

def ccText : CallConv → String
  | .c => "default"
  | .msAbi => "ms_abi"
  | .sysvAbi => "sysv_abi"
  | .regcall => "regcall"
  | .vectorcall => "vectorcall"
  | .other s => s

def attrText : Attr → String
  | .noreturn => "noreturn" | .nonnull => "nonnull" | .format => "format"
  | .deprecated => "deprecated" | .visibility v => s!"visibility({v})" | .asmLabel => "asm label"
  | .pure => "pure" | .const => "const" | .nothrow => "nothrow" | .leaf => "leaf"
  | .builtin => "builtin" | .restrict => "restrict" | .warnUnusedResult => "warn_unused_result"
  | .allocSize => "alloc_size" | .aligned => "aligned" | .weak => "weak" | .alias => "alias"
  | .section => "section" | .used => "used" | .unused => "unused" | .cold => "cold"
  | .returnsTwice => "returns_twice" | .other k => k

def kindText : DeclKind → String
  | .function => "function" | .typedef => "typedef" | .struct => "struct" | .union => "union"
  | .enum => "enum" | .variable => "variable" | .other k => k

def gotJson {α : Type} (f : α → String) : Got α → Json
  | .ok a => Json.mkObj [("ok", js (f a))]
  | .unsupported w => Json.mkObj [("unsupported", js w)]

/-- The reason the import gives for not reading (part of) an entry, if any: a function type
outside `CProto`, a typedef's or variable's type outside `CTy`, a declaration it does not read. -/
def importReason? (e : Entry) : Option String :=
  match e.body with
  | .function f => match f.proto with
    | .unsupported w => some w
    | .ok _ => none
  | .typedef (.unsupported w) | .variable (.unsupported w) _ | .unsupported w => some w
  | _ => none

def statusJson : Status → Json
  | .claimable => Json.mkObj [("status", js "claimable")]
  | .unsupported w => Json.mkObj [("status", js "unsupported"), ("why", js w)]
  | .internal w => Json.mkObj [("status", js "internal"), ("why", js w)]
  | .notFunction => Json.mkObj [("status", js "notFunction")]

def optStr : Option String → Json
  | some s => js s
  | none => Json.null

/-- One entry: what the import reads of it, and its status for each ABI definition (`stat`, from
`table`). A prototype also gets the subset route's lowering and call plan, in `env`. -/
def entryJson (env : Env) (e : Entry) (stat : List (String × Status)) : Json :=
  let loc := match e.loc with
    | some l => Json.mkObj [("file", js l.file), ("line", jn l.line)]
    | none => Json.null
  let decl : Json := match e.body with
    | .function f => gotJson (fun cp => cp.render e.name) f.proto
    | .typedef t => gotJson (fun t => "typedef " ++ t.declare e.name) t
    | .tag d => Json.mkObj [("ok", js (kindText e.kind ++ " " ++ e.name ++ (if d then " { … }" else "")))]
    | .variable t st =>
      gotJson (fun t => (match st with | some x => x ++ " " | none => "") ++ t.declare e.name) t
    | .unsupported w => Json.mkObj [("unsupported", js w)]
  let base := [("name", js e.name), ("kind", js (kindText e.kind)), ("loc", loc),
    ("implicit", Json.bool e.implicit), ("decl", decl),
    ("status", Json.mkObj (stat.map fun (n, s) => (n, statusJson s)))]
  Json.mkObj <| match e.body with
    | .function f => base ++ [("variadic", Json.bool f.variadic), ("cc", js (ccText f.cc)),
        ("attrs", Json.arr (f.attrs.toArray.map (js ∘ attrText))), ("symbol", js f.symbol),
        ("asmLabel", optStr f.asmLabel), ("storage", optStr f.storage),
        ("inline", Json.bool f.inline), ("definition", Json.bool f.definition)] ++
        (match f.proto with
          | .ok cp => [("lowering", lowerings env cp)]
          | .unsupported _ => [])
    | _ => base

def provJson (p : Provenance) : Json :=
  Json.mkObj [("artifact", js p.artifact), ("image", js p.image), ("clang", js p.clang),
    ("target", js p.target), ("std", js p.std), ("cwd", js p.cwd), ("command", js p.command),
    ("defines", Json.arr (p.defines.toArray.map js)),
    ("includes", Json.arr (p.includes.toArray.map js)),
    ("filter", js p.filter), ("filterSha256", js p.filterSha256), ("source", optStr p.source),
    ("inputs", Json.arr (p.inputs.toArray.map fun (f, h) =>
      Json.mkObj [("file", js f), ("sha256", js h)])),
    ("jsonSha256", js p.jsonSha256), ("jsonBytes", jn p.jsonBytes)]

/-- An artifact's clang route: provenance, counts (`abiCounts` from `interface`, `claimable`
and `unsupportedFns`) and every entry with its status per ABI (`table`). -/
def clangJson (a : Artifact) (relation : String) : Json :=
  let imp := a.imported
  let env := imp.header.env
  let tables := abis.map fun (n, A) => (n, (table A (clangCcs n) imp).toArray)
  let es := imp.entries
  Json.mkObj [("artifact", js a.key), ("value", js a.value), ("literal", js a.literal),
    ("relation", js relation), ("provenance", provJson imp.provenance),
    ("counts", Json.mkObj [("total", jn es.length),
      ("functions", jn (es.filter (·.kind == .function)).length),
      ("implicit", jn (es.filter (·.implicit)).length),
      ("unsupported", jn (es.filter fun e => (importReason? e).isSome).length)]),
    ("abiCounts", Json.mkObj (abis.map fun (n, A) => (n, Json.mkObj [
      ("interface", jn (interface A (clangCcs n) imp).length),
      ("claimable", jn (claimable A (clangCcs n) imp).length),
      ("unsupported", jn (unsupportedFns A (clangCcs n) imp).length)]))),
    ("entries", Json.arr (es.toArray.mapIdx fun i e =>
      entryJson env e (tables.map fun (n, t) => (n, (t[i]?.map (·.2)).getD .notFunction))))]

def clangFor (id : String) : Json :=
  match clangOf id with
  | some (k, rel) => match artifacts.find? (·.key == k) with
    | some a => clangJson a rel
    | none => Json.null
  | none => Json.null

def headerJson (s : Src) : IO Json := do
  let mut files : Array (String × String) := #[]
  for (n, p) in s.files do files := files.push (n, ← IO.FS.readFile p)
  let base := [("id", js s.id), ("title", js s.title), ("note", js s.note), ("root", js s.root),
    ("files", Json.arr (s.files.toArray.map fun (n, p) => Json.mkObj [("name", js n), ("path", js p)])),
    ("clang", clangFor s.id)]
  if !s.subset then return Json.mkObj (base ++ [("read", Json.null)])
  match read files.toList s.root with
  | .error e => pure (Json.mkObj (base ++ [("read", Json.mkObj [("refused", js e)])]))
  | .ok h => pure (Json.mkObj (base ++ [("read", Json.mkObj [("ok", Json.bool true)]),
      ("typedefs", Json.arr (h.typedefs.toArray.map fun (n, t) => Json.mkObj [("name", js n), ("type", js (t.declare ""))])),
      ("enums", Json.arr (h.enums.toArray.map fun (t, cs) => Json.mkObj [("tag", js t),
        ("constants", Json.arr (cs.toArray.map fun (c, v) => Json.arr #[js c, js (toString v)]))])),
      ("aggregates", Json.arr (h.env.toArray.map (declJson h.env))),
      ("prototypes", Json.arr (h.protos.toArray.map fun (f, cp) => protoJson h f cp))]))

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: header-pages OUTDIR"; return 2
  let mut hs : Array Json := #[]
  for s in sources do hs := hs.push (← headerJson s)
  let j := Json.mkObj [("schema", js "silmaril.header-pages/2"),
    ("note", js "computed by the reader, the ABI definitions' lowering and the layout definitions, run on the header files; not theorems"),
    ("clangNote", js "computed by the import's status, interface and lowering definitions, run on the literal entries of each pinned clang import and its .prov; not theorems"),
    ("abis", Json.arr (abis.toArray.map fun (n, A) => Json.mkObj [("name", js n), ("id", js A.id), ("source", js A.source),
      ("clangCcs", Json.arr ((clangCcs n).toArray.map (js ∘ ccText))),
      ("clangCcsNote", js (clangCcsNote n))])),
    ("dataModels", Json.arr #[js "sysvX86_64", js "msX64"]),
    ("headers", Json.arr hs)]
  IO.FS.createDirAll (out ++ "/headers")
  IO.FS.writeFile (out ++ "/headers/index.json") j.pretty
  IO.println s!"header-pages: wrote {out}/headers/index.json ({hs.size} headers)"
  return 0
