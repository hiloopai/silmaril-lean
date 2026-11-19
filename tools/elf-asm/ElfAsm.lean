import Lean
import Silmaril.Elf.Asm.Export
import Silmaril.Elf.Asm.Example.Thms
import Silmaril.Elf.Asm.Example.Reloc.Thms
import Silmaril.Elf.Asm.Example.LeafArith.Thms
import ElfAsmDecoys
import Silmaril.Elf.Pin.Examples
import Silmaril.Elf.Staged.Pinned.LeafArith.Defs

/-!
# `elf-asm`: assembly functions as JSON, with evidence read from theorem statements

```
lake env .lake/build/bin/elf-asm OUT.json          write the sample functions (`silmaril.elf.asm/1`)
lake env .lake/build/bin/elf-asm --check OUT.json  regenerate and compare
```

Both modes first run a **self-test** on the decoys of `ElfAsmDecoys` (true theorems about a moved
copy of a function, about another file, a contract with no bytes, a misleading name, and one
conditional fact): each must classify exactly as expected, or the tool fails.

The functions are the values of `Silmaril.Elf.Asm.Example` and `….Example.Reloc` (evaluated natively: names, bytes,
display lines, references, and the decodings by each function's model). Their **evidence** is not
listed by hand: the tool imports the checked modules `Silmaril.Elf.Asm.Example.Thms` and `….Reloc.Thms`, reads
the statement of every theorem in them, and classifies it by the head of each conjunct
(`Silmaril.Elf.Asm.Export`, module doc, lists the kinds). A conjunct counts for a function only
when its function argument is that function's constant, and only when its file argument (if the
proposition has one) is that function's file; theorem names are never read. Each
piece of evidence carries the theorem's axioms (`collectAxioms`) and premises.
-/

open Lean Meta
open Silmaril.Elf.Asm
open Silmaril.Elf.Asm.Export

namespace ElfAsm

/-- The checked theorem modules whose statements are read. -/
def thmModules : List Name :=
  [`Silmaril.Elf.Asm.Example.Thms, `Silmaril.Elf.Asm.Example.Reloc.Thms,
    `Silmaril.Elf.Asm.Example.LeafArith.Thms]

/-- The decoy module of the self-test. -/
def decoyModule : Name := `ElfAsmDecoys

/-- A file of the records, with the path and SHA-256 the JSON shows. When the record's file is not
itself an `include_bytes` pin, `pin` names one, `(F, theorem)`: the path and SHA-256 are that pin's
(`elf-pages`/`gen.sh` and `examples/elf/pin.sh --check` tie them to the bytes), and the theorem
must state exactly `decl = F` (checked: `checkPin`), so the record's blob is that file. -/
structure FileInfo where
  decl : Name
  path : String
  digest : String
  pin : Option (Name × Name) := none
  deriving Inhabited

def files : List FileInfo := [
  ⟨`Silmaril.Elf.Staged.Pinned.ZlibChecksums.F, Silmaril.Elf.Staged.Pinned.ZlibChecksums.path,
    Silmaril.Elf.Staged.Pinned.ZlibChecksums.sha256, none⟩,
  -- an object file of this repository, not a pinned file: its path and SHA-256 are metadata
  ⟨`Silmaril.Elf.Asm.Example.Reloc.F, Example.Reloc.path, Example.Reloc.fileSha256, none⟩,
  ⟨`Silmaril.Elf.Asm.Example.LeafArith.F, Silmaril.Elf.Staged.Pinned.LeafArith.path,
    Silmaril.Elf.Staged.Pinned.LeafArith.sha256,
    some (`Silmaril.Elf.Staged.Pinned.LeafArith.F, `Silmaril.Elf.Pin.Examples.leafArith_record_file)⟩]

/-- The modules the file theorems are in (imported, not scanned for evidence). -/
def pinModules : List Name := [`Silmaril.Elf.Pin.Examples]

/-- **The record's file is the pin's file**: the theorem exists, states exactly `decl = F` (no
other proposition), and uses only the standard axioms. -/
def checkPin (env : Environment) (fi : FileInfo) : Except String Unit := do
  let some (F, thm) := fi.pin | return
  let some (.thmInfo ti) := env.find? thm | throw s!"{fi.decl}: {thm} is not a theorem"
  let want := mkApp3 (.const ``Eq [Level.one]) (.const ``Silmaril.X86.Link.Blob [])
    (.const fi.decl []) (.const F [])
  unless ti.type.consumeMData == want do throw s!"{fi.decl}: {thm} does not state exactly {fi.decl} = {F}"

structure Sample where
  decl : Name
  /-- The file the function belongs to: evidence must be stated against it. -/
  file : Name
  f : AsmFunction
  decodings : List Decoding

def zlibF : Name := `Silmaril.Elf.Staged.Pinned.ZlibChecksums.F

def samples : List Sample := [
  ⟨``Example.adler32_z, zlibF, Example.adler32_z,
    [Decoding.of x86Open9 ``Example.adler32zDecoding Example.adler32zDecoding]⟩,
  ⟨``Example.adler32, zlibF, Example.adler32,
    [Decoding.of x86Open9 ``Example.adler32Decoding Example.adler32Decoding]⟩,
  ⟨``Example.crc32_z, zlibF, Example.crc32_z,
    [Decoding.of x86Open ``Example.crc32zDecoding Example.crc32zDecoding]⟩,
  ⟨``Example.crc32, zlibF, Example.crc32,
    [Decoding.of x86Open ``Example.crc32Decoding Example.crc32Decoding]⟩,
  ⟨``Example.otherMachine, zlibF, Example.otherMachine, []⟩,
  ⟨``Example.Reloc.scaledPlusBias, `Silmaril.Elf.Asm.Example.Reloc.F, Example.Reloc.scaledPlusBias,
    [Decoding.of x86Ext ``Example.Reloc.scaledDecoding Example.Reloc.scaledDecoding]⟩,
  ⟨``Example.LeafArith.clamp, `Silmaril.Elf.Asm.Example.LeafArith.F, Example.LeafArith.clamp,
    [Decoding.of x86Open ``Example.LeafArith.clampDecoding Example.LeafArith.clampDecoding]⟩,
  ⟨``Example.LeafArith.sat, `Silmaril.Elf.Asm.Example.LeafArith.F, Example.LeafArith.sat,
    [Decoding.of x86Open ``Example.LeafArith.satDecoding Example.LeafArith.satDecoding]⟩]

/-- The instruction models, by constant. -/
def isas : List (Name × String) :=
  [(``x86Ext, x86Ext.name), (``x86Open, x86Open.name), (``x86Open9, x86Open9.name)]

def isaName (e : Expr) : String :=
  match e.consumeMData.constName? with
  | some n => (isas.lookup n).getD n.toString
  | none => toString e

/-- The function constant `e` denotes, if it is one of the samples. -/
def fnConst? (e : Expr) : Option Name :=
  match e.consumeMData.constName? with
  | some n => if samples.any (·.decl == n) then some n else none
  | none => none

/-- `f.bytes`, `f.extent.vaddr` of a sample `f`. -/
def projOf? (field : Name) (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .app (.const n _) x => if n == field then some x else none
  | .proj _ _ x => some x
  | _ => none

def bytesOf? (e : Expr) : Option Name := (projOf? ``AsmFunction.bytes e).bind fnConst?

def vaddrOf? (e : Expr) : Option Name :=
  (projOf? ``Extent.vaddr e).bind fun x => (projOf? ``AsmFunction.extent x).bind fnConst?

def fileOf (e : Expr) : Option Name := e.consumeMData.constName?

partial def conjuncts (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg! else [e]

/-- A finding: function, kind, model, and the file the statement is about (`none`: no file). -/
abbrev Finding := Name × String × Option String × Option Name

/-- What one conjunct (under its own universal quantifiers) says. -/
def classifyConj (c : Expr) : MetaM (Option Finding) :=
  forallTelescope c fun _ body => do
    let body := body.consumeMData
    let args := body.getAppArgs
    let withFile (k : String) (m : Option String) (file f : Expr) : Option Finding :=
      (fnConst? f).map fun n => (n, k, m, some (fileOf file |>.getD .anonymous))
    match body.getAppFn.constName? with
    | some ``ArchOf => pure (withFile "arch" none args[0]! args[1]!)
    | some ``BytesAt => pure (withFile "bytes" none args[0]! args[1]!)
    | some ``SectionBytesAt => pure (withFile "sectionBytes" none args[0]! args[1]!)
    | some ``SymbolOf => pure (withFile "symbol" none args[0]! args[1]!)
    | some ``LinesTile => pure ((fnConst? args[0]!).map (·, "lineTiles", none, none))
    | some ``DecodesAs => pure ((fnConst? args[1]!).map (·, "decode", some (isaName args[0]!), none))
    | some ``RefsGrounded => pure (withFile "refs" (some (isaName args[2]!)) args[0]! args[1]!)
    | some ``Unrelocated => pure (withFile "unrelocated" none args[0]! args[1]!)
    | some ``Silmaril.Elf.Load.PresentFn =>
      -- `PresentFn F (nameOf "f")`: the sample of that name and file
      let n := args[1]!.consumeMData
      pure (match n.getAppFn.constName?, n.appArg!.consumeMData with
        | some ``Silmaril.Elf.nameOf, .lit (.strVal str) =>
          (samples.find? fun s => s.f.name == str && some s.file == fileOf args[0]!).map
            fun s => (s.decl, "present", none, fileOf args[0]!)
        | _, _ => none)
    | some ``Silmaril.Elf.CodeAt =>
      pure (match vaddrOf? args[1]!, bytesOf? args[2]! with
        | some n, some m => if n == m then some (n, "code", none, fileOf args[0]!) else none
        | _, _ => none)
    | some ``Not =>
      let p := args[0]!.consumeMData
      let pa := p.getAppArgs
      match p.getAppFn.constName? with
      | some ``DecodesAs => pure ((fnConst? pa[1]!).map (·, "noDecode", some (isaName pa[0]!), none))
      | some ``ArchOf => pure (withFile "notArch" none pa[0]! pa[1]!)
      | some ``BytesAt => pure (withFile "notBytes" none pa[0]! pa[1]!)
      | _ => pure none
    | some ``Silmaril.X86.FnContract.Spec.Total =>
      -- `@Spec.Total σ isa spec`: the machine is the instruction-set argument
      pure (some (.anonymous, "contract", some (toString (← ppExpr args[1]!)), none))
    | _ => pure none

/-- The evidence a theorem gives, by function: only findings whose file (when the statement has
one) is the function's own file. -/
def classify (decl : Name) (ty : Expr) : MetaM (List (Name × Evidence)) :=
  forallTelescope ty fun xs body => do
    let mut hyps : List String := []
    for x in xs do
      let t ← inferType x
      if ← isProp t then hyps := hyps ++ [toString (← ppExpr t)]
    let mut found : List Finding := []
    for c in conjuncts body do
      if let some r ← classifyConj c then found := found ++ [r]
    let own (n : Name) (file : Option Name) : Bool :=
      match file, samples.find? (·.decl == n) with
      | some fl, some s => fl == s.file
      | none, some _ => true
      | _, none => false
    let kept := found.filter fun (n, k, _, fl) => k == "contract" || own n fl
    -- a contract counts for the function whose bytes or code the same statement grounds
    let grounded := kept.filterMap fun (n, k, _, _) =>
      if k == "bytes" || k == "sectionBytes" || k == "code" then some n else none
    let out := kept.flatMap fun (n, k, m, _) =>
      if k == "contract" then grounded.eraseDups.map (·, k, m) else [(n, k, m)]
    pure (out.map fun (n, k, m) => (n, { kind := k, decl, model := m, hypotheses := hyps }))

def runMeta {α : Type} (env : Environment) (x : MetaM α) : IO α := do
  let (a, _) ← (x.run' {} {}).toIO { fileName := "<elf-asm>", fileMap := default } { env }
  pure a

/-- The theorems of a module, by name. -/
def theoremsOf (env : Environment) (m : Name) : IO (Array (Name × Expr)) := do
  let some idx := env.getModuleIdx? m | throw (IO.userError s!"{m} not imported")
  let thms := env.constants.toList.filterMap fun (n, ci) =>
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      match ci with
      | .thmInfo v => some (n, v.type)
      | _ => none
    else none
  pure (thms.toArray.qsort (fun a b => a.1.toString < b.1.toString))

def loadEnv : IO Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  importModules ((decoyModule :: thmModules ++ pinModules).toArray.map ({ module := · })) {}

/-- **The self-test**: each decoy gives exactly the expected `(function, kind, #premises)`. -/
def selfTest (env : Environment) : IO Unit := do
  let want : List (String × List (Name × String × Nat)) := [
    ("moved_tiles", []), ("crc32_bytes", []), ("crc32_other_file", []),
    ("crc32_z_bytes_if", [(``Example.crc32_z, "bytes", 1)]), ("contract_alone", []),
    ("other_decodes", []), ("present_other_file", []), ("present_other_name", [])]
  let thms ← theoremsOf env decoyModule
  for (short, exp) in want do
    let some (n, ty) := thms.find? (·.1 == decoyModule ++ short.toName)
      | throw (IO.userError s!"self-test: decoy {short} missing")
    let got := (← runMeta env (classify n ty)).map fun (f, e) => (f, e.kind, e.hypotheses.length)
    unless got == exp do throw (IO.userError s!"self-test: {short} gives {got}, expected {exp}")
  -- file identity: the true pins pass; a pin to another file, or a theorem about another file, fails
  for fi in files do
    if let .error m := checkPin env fi then throw (IO.userError s!"self-test: {m}")
  let leaf := (files.find? (·.decl == `Silmaril.Elf.Asm.Example.LeafArith.F)).get!
  for (what, bad) in [("another file", { leaf with pin := some (`Silmaril.Elf.Staged.Pinned.ZlibChecksums.F,
        `Silmaril.Elf.Pin.Examples.leafArith_record_file) }),
      ("a theorem about another pair", { leaf with pin := some (`Silmaril.Elf.Staged.Pinned.LeafArith.F,
        `Silmaril.Elf.Pin.Examples.zlibChecksums_exe_eq) })] do
    if let .ok () := checkPin env bad then throw (IO.userError s!"self-test: a pin to {what} is accepted")

/-- The parse of a pinned file, read from its path (metadata for `targetIn`; natively computed). -/
def parseFile (fi : FileInfo) : IO (Option Silmaril.Elf.File) := do
  let raw ← IO.FS.readBinFile fi.path
  pure (Silmaril.Elf.parse (Silmaril.Elf.blobOf ⟨raw⟩))

def generate : IO Json := do
  let env ← loadEnv
  let mut asts : List (Name × Option Silmaril.Elf.File) := []
  for fi in files do asts := asts ++ [(fi.decl, ← parseFile fi)]
  selfTest env
  let mut ev : List (Name × Evidence) := []
  for m in thmModules do
    for (n, ty) in ← theoremsOf env m do
      let es ← runMeta env (classify n ty)
      let axs ← runMeta env (Lean.collectAxioms n)
      let axs := (axs.qsort Name.lt).toList
      ev := ev ++ es.map fun (f, e) => (f, { e with axioms := axs })
  pure <| Json.mkObj [
    ("schema", Json.str schema), ("schemaVersion", Json.str schemaVersion),
    ("files", Json.arr (files.toArray.map fun fi => Json.mkObj [
      ("decl", Json.str fi.decl.toString), ("path", Json.str fi.path), ("sha256", Json.str fi.digest)])),
    ("functions", Json.arr (samples.toArray.map fun s =>
      match functionJson s.decl s.f s.decodings
          (ev.filterMap fun (f, e) => if f == s.decl then some e else none) ((asts.lookup s.file).join) with
      | .obj kvs => .obj (kvs.insert "file" (Json.str s.file.toString))
      | j => j))]

end ElfAsm

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] => IO.FS.writeFile out ((← ElfAsm.generate).pretty ++ "\n"); pure 0
  | ["--check", out] =>
    let want := (← ElfAsm.generate).pretty ++ "\n"
    if (← IO.FS.readFile out) == want then pure 0
    else IO.eprintln s!"{out}: out of date (lake env .lake/build/bin/elf-asm {out})"; pure 1
  | _ => IO.eprintln "usage: elf-asm [--check] OUT.json"; pure 2
