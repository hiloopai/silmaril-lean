/-
Emit the normalized header of each pinned clang artifact as a Lean literal.

    lake env lean --run examples/headers/emit.lean JSONDIR OUTDIR

reads `JSONDIR/<artifact>.json` and `.prov`, imports it with
`Silmaril.Data.Layout.Header.Import.Imported.ofJson` (compiled), and writes
`OUTDIR/<Name>/Defs.lean` with `def entries : List Entry := [...]`. `recipe.sh` runs it and
`recipe.sh --check` compares the output byte for byte. Nothing here is trusted: the theorem
`Pinned.import_<name>` checks in the kernel that the import of the JSON is this literal.
-/
import Silmaril.Data.Layout.Header.Import.Defs

open Silmaril.Data.Layout Silmaril.Data.Layout.Header Silmaril.Data.Layout.Header.Import

def esc (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else c.toString) ++ "\""

def opt {α : Type} (f : α → String) : Option α → String
  | none => "none"
  | some a => "(some " ++ f a ++ ")"

def list {α : Type} (f : α → String) (xs : List α) : String :=
  "[" ++ ", ".intercalate (xs.map f) ++ "]"

def boolS (b : Bool) : String := if b then "true" else "false"

def intKind : IntKind → String
  | .char => ".char" | .short => ".short" | .int => ".int" | .long => ".long"
  | .longLong => ".longLong" | .int128 => ".int128" | .size => ".size"
  | .ptrdiff => ".ptrdiff" | .intptr => ".intptr" | .wchar => ".wchar"
  | .exact n => s!"(.exact {n})"

def sign : Sign → String
  | .plain => ".plain" | .signed => ".signed" | .unsigned => ".unsigned"

def floatKind : FloatKind → String
  | .float => ".float" | .double => ".double" | .longDouble => ".longDouble"
  | .float128 => ".float128"

def cty : CTy → String
  | .void => ".void"
  | .bool => ".bool"
  | .int k s => s!"(.int {intKind k} {sign s})"
  | .float k => s!"(.float {floatKind k})"
  | .ptr t => s!"(.ptr {cty t})"
  | .enum t u => s!"(.enum {esc t} {opt (fun (k, s) => s!"({intKind k}, {sign s})") u})"
  | .array t n => s!"(.array {cty t} {n})"
  | .struct t => s!"(.struct {esc t})"
  | .union t => s!"(.union {esc t})"
  | .typedef n t => s!"(.typedef {esc n} {cty t})"

def got {α : Type} (f : α → String) : Got α → String
  | .ok a => s!"(.ok {f a})"
  | .unsupported w => s!"(.unsupported {esc w})"

def proto (p : CProto) : String := s!"⟨{cty p.ret}, {list cty p.params}, {boolS p.variadic}⟩"

def quals (q : Quals) : String := list (list esc) q

def protoQuals (q : ProtoQuals) : String := s!"⟨{quals q.ret}, {list quals q.params}⟩"

def cc : CallConv → String
  | .c => ".c" | .msAbi => ".msAbi" | .sysvAbi => ".sysvAbi" | .regcall => ".regcall"
  | .vectorcall => ".vectorcall" | .other s => s!"(.other {esc s})"

def attr : Attr → String
  | .noreturn => ".noreturn" | .nonnull => ".nonnull" | .format => ".format"
  | .deprecated => ".deprecated" | .visibility v => s!"(.visibility {esc v})"
  | .asmLabel => ".asmLabel" | .pure => ".pure" | .const => ".const" | .nothrow => ".nothrow"
  | .leaf => ".leaf" | .builtin => ".builtin" | .restrict => ".restrict"
  | .warnUnusedResult => ".warnUnusedResult" | .allocSize => ".allocSize"
  | .aligned => ".aligned" | .weak => ".weak" | .alias => ".alias" | .section => ".section"
  | .used => ".used" | .unused => ".unused" | .cold => ".cold"
  | .returnsTwice => ".returnsTwice" | .other k => s!"(.other {esc k})"

def kind : DeclKind → String
  | .function => ".function" | .typedef => ".typedef" | .struct => ".struct"
  | .union => ".union" | .enum => ".enum" | .variable => ".variable"
  | .other k => s!"(.other {esc k})"

def body : Body → String
  | .function f =>
    s!"(.function\n      ⟨{got proto f.proto}, {opt protoQuals f.quals},\n       {boolS f.variadic}, {cc f.cc}, {list attr f.attrs}, " ++
    s!"{esc f.symbol}, {opt esc f.asmLabel}, {opt esc f.storage}, {boolS f.inline}, " ++
    s!"{boolS f.definition}⟩)"
  | .typedef t => s!"(.typedef {got cty t})"
  | .tag d => s!"(.tag {boolS d})"
  | .variable t s => s!"(.variable {got cty t} {opt esc s})"
  | .unsupported w => s!"(.unsupported {esc w})"

def entry (e : Entry) : String :=
  s!"  ⟨{esc e.name}, {kind e.kind}, {opt (fun l => s!"⟨{esc l.file}, {l.line}⟩") e.loc}, " ++
  s!"{boolS e.implicit},\n    {body e.body}⟩"

/-- The artifacts: file stem, module name, what it is. -/
def artifacts : List (String × String × String) :=
  [("arith", "Arith", "`arith.h` and the `rt.h` it includes"),
   ("probe", "Probe", "The probe header `examples/headers/probe/probe.h`"),
   ("zlib-solo", "ZlibSolo", "zlib 1.3.1's `zlib.h` under `-DZ_SOLO`"),
   ("zlib-hosted", "ZlibHosted", "zlib 1.3.1's `zlib.h`, hosted"),
   ("glibc-string", "GlibcString", "glibc's `string.h`, hosted"),
   ("glibc-math", "GlibcMath", "glibc's `math.h` (libm), hosted"),
   ("glibc-stdlib", "GlibcStdlib", "glibc's `stdlib.h` (with `alloca.h`), hosted")]

def moduleText (file name what prov : String) (imp : Imported) : String :=
  let v := name.decapitalize
  let up := "../../../../../../../examples/headers/clang/"
  s!"module

public import Silmaril.Data.Layout.Header.Import.Defs

/-! # `{file}.json`: the pinned artifact and its import (generated: do not edit)

Written by `examples/headers/emit.lean` and compared byte for byte by
`examples/headers/recipe.sh --check`. `{v}Json` and `{v}Prov` are the committed
`examples/headers/clang/{file}.json` and `.prov`; `{v}` is their import, and `{name}.entries`
the entries that import gives, as a literal. `import_{v}` (`Pinned.{name}.Thms`) proves in the
kernel that they are equal; other theorems compute on the literal, never on the JSON.

The provenance, verbatim. It changes whenever the JSON does, so this module changes with it
and is rebuilt: Lake does not track the files `include_str` reads.

```text
{prov}```
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

/-- `examples/headers/clang/{file}.json`. -/
def {v}Json : String :=
  include_str \"{up}{file}.json\"
/-- `examples/headers/clang/{file}.prov`. -/
def {v}Prov : String :=
  include_str \"{up}{file}.prov\"
/-- {what}, as clang reads it: the import of `{v}Json`. Noncomputable: the kernel computes it (in
`import_{v}`), and compiled code uses the literal `{name}.entries`. Compiling it would parse the
JSON when a program that imports this module starts, with recursion as deep as the JSON is long. -/
noncomputable def {v} : Imported := .ofJson (.parse {v}Prov) {v}Json

/-- The entries of `{v}`, as a literal. -/
def {name}.entries : List Entry := [
" ++ ",\n".intercalate (imp.entries.map entry) ++ s!"]

end Silmaril.Data.Layout.Header.Import.Pinned

end
"

def main (args : List String) : IO UInt32 := do
  let [jsonDir, outDir] := args | IO.eprintln "usage: emit.lean JSONDIR OUTDIR"; return 2
  for (file, name, what) in artifacts do
    let json ← IO.FS.readFile s!"{jsonDir}/{file}.json"
    let prov ← IO.FS.readFile s!"{jsonDir}/{file}.prov"
    let imp := Imported.ofJson (.parse prov) json
    if let some e := imp.error then
      IO.eprintln s!"{file}: {e}"; return 1
    IO.FS.createDirAll s!"{outDir}/{name}"
    IO.FS.writeFile s!"{outDir}/{name}/Defs.lean" (moduleText file name what prov imp)
  return 0
