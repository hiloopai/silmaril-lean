import Lean.Data.Json
import Silmaril.Data.Layout.Header.Defs
import Silmaril.Data.Layout.Bitfield.Defs
import Silmaril.Machine.Abi.Conformance.Defs
import Silmaril.Machine.Abi.Conformance.Win64.Defs
import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs

/-!
# The explorer's Headers tab data (`OUTDIR/headers/index.json`)

For each pinned header: what the subset reader (`Silmaril.Data.Layout.Header.read`) reads or why
it refuses; each prototype's C spelling and qualifiers; what each versioned ABI definition
(`sysvInt`, `win64Int`, `sysvScalar`) lowers it to, with the header's own tag definitions
(`Header.env`: `sysvScalar` classifies small aggregates passed by value from their layout), or the
reason it refuses; the call plan of
`sysvScalar` (where each argument and the result go); and each aggregate's layout under the
System V x86-64 and Microsoft x64 data models (`bitLayout`).

Every value is computed by the definitions that conformance rows and layout theorems use, run
here on the header files; none is a theorem. A view must say so.

    lake env .lake/build/bin/header-pages OUTDIR
-/

open Lean (Json)
open Silmaril.Data.Layout
open Silmaril.Data.Layout.Header
open Silmaril.Machine.Abi.Conformance

def js (s : String) : Json := Json.str s
def jn (n : Nat) : Json := Json.num n

/-- A pinned header: id, title, the files (name in the include graph, path), the root. -/
structure Src where
  id : String
  title : String
  files : List (String × String)
  root : String
  note : String := ""

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
    files := [("demo.h", "examples/headers/layout/demo.h")], root := "demo.h" }]

/-- The ABI definitions a prototype is lowered by. -/
def abis : List (String × AbiDef) := [("sysvInt", sysvInt), ("win64Int", win64Int), ("sysvScalar", sysvScalar)]

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
    | "win64Int" => intLowering (win64Int.lower env cp : Except String Silmaril.Machine.Abi.SystemV.Proto)
    | _ => intLowering (sysvInt.lower env cp : Except String Silmaril.Machine.Abi.SystemV.Proto))

def protoJson (h : Header) (f : String) (cp : CProto) : Json :=
  Json.mkObj [("name", js f), ("c", js (cp.render f)),
    ("quals", match h.quals? f with
      | some q => js (reprStr q) | none => Json.null),
    ("lowering", lowerings h.env cp)]

def slotJson (s : BitSlot) : Json :=
  Json.mkObj [("name", js s.name), ("bitOffset", jn s.off), ("bits", jn s.width)]

def layoutJson (pol : BitPolicy) (dm : DataModel) (env : Env) (d : Decl) : Json :=
  exceptJson (fun (slots, sh) => Json.mkObj [("size", jn sh.size), ("align", jn sh.align),
    ("members", Json.arr (slots.toArray.map slotJson))]) (bitLayout pol dm env d)

def declJson (env : Env) (d : Decl) : Json :=
  Json.mkObj [("kind", js (match d.kind with | .struct => "struct" | .union => "union")),
    ("tag", js d.tag),
    ("members", Json.arr (d.fields.toArray.map fun fl => Json.mkObj [("name", js fl.name),
      ("type", js (fl.ty.declare "")), ("bits", match fl.bits with | some b => jn b | none => Json.null)])),
    ("layouts", Json.mkObj [("sysvX86_64", layoutJson .sysv sysvX86_64 env d),
      ("msX64", layoutJson .ms msX64 env d)])]

def headerJson (s : Src) : IO Json := do
  let mut files : Array (String × String) := #[]
  for (n, p) in s.files do files := files.push (n, ← IO.FS.readFile p)
  let base := [("id", js s.id), ("title", js s.title), ("note", js s.note), ("root", js s.root),
    ("files", Json.arr (s.files.toArray.map fun (n, p) => Json.mkObj [("name", js n), ("path", js p)]))]
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
  let j := Json.mkObj [("schema", js "silmaril.header-pages/1"),
    ("note", js "computed by the reader, the ABI definitions' lowering and the layout definitions, run on the header files; not theorems"),
    ("abis", Json.arr (abis.toArray.map fun (n, A) => Json.mkObj [("name", js n), ("id", js A.id), ("source", js A.source)])),
    ("dataModels", Json.arr #[js "sysvX86_64", js "msX64"]),
    ("headers", Json.arr hs)]
  IO.FS.createDirAll (out ++ "/headers")
  IO.FS.writeFile (out ++ "/headers/index.json") j.pretty
  IO.println s!"header-pages: wrote {out}/headers/index.json ({hs.size} headers)"
  return 0
