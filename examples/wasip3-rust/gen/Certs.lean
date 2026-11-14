import Silmaril.Wasm.Component.Chunked.Defs
import Silmaril.Wasm.Component.Binary.Encode.Defs
import Silmaril.Wasm.Component.BinaryP3.Defs

/-!
The generator of the chunked decode certificates of the WASI 0.3 Rust examples
(`Silmaril/Project/WasmP3Rust/<Name>/**`). Run from the repository root:

    lake env lean --run examples/wasip3-rust/gen/Certs.lean <file.wasm> <Name> [out-root]
    lake env lean --run examples/wasip3-rust/gen/Certs.lean --p3 <file.wasm> <Name> [out-root]

for each of `hello.wasm Hello`, `echo.wasm Echo`, `cat.wasm Cat`, `cat-debug.wasm CatDebug`
(files under `examples/wasip3-rust/dist/`; `out-root` defaults to `.`).

It writes **plans** only: where each component frame, core section, vector element run, data
segment, custom section, code entry and run of instructions ends. Plans are computed here by
compiled evaluation of silmaril's core readers on the whole file; nothing here is trusted. The
kernel checks every plan with the checkers of `Silmaril.Wasm.Component.Chunked` on slices of the
file that `include_chunks` reads at elaboration time, and their soundness theorems turn the checks
into silmaril's Core grammar (`Encodes`) for each core module and the raw framing of the
component.

With `--p3` it writes only `<Name>/P3/{Defs,Thms}.lean`: the whole component as an AST of the
grammar with async built-ins (`Silmaril.Wasm.Component.BinaryP3`), from the sections certified
before (`Section.ofV0 secN`), the core modules as the bytes of their slices, and the `canon`
sections with async built-ins (`canonN`, certified with `BinaryP3.Encode.section_`), composed
to `BinaryP3.parse` by `Silmaril.Wasm.Component.Chunked.ast_of`.
-/

open Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Component.Chunked

namespace P3Gen

/-- Leaf size for instruction runs and vector elements, in bytes. -/
def T : Nat := 16
/-- Code bytes per group module (each group is one kernel check, about 1.6 ms per byte). -/
def groupBytes : Nat := 5000

def runAt {α : Type} (b : ByteArray) (p : DecodeM α) (pos : Nat) : Option (α × Nat) :=
  match p.run ⟨b, pos⟩ with
  | .ok (a, c) => some (a, c.pos)
  | .error _ => none

def leb (b : ByteArray) (pos : Nat) : Nat × Nat :=
  match runAt b (readU 32) pos with
  | some (n, e) => (n, e)
  | none => panic! s!"bad LEB128 at {pos}"

/-- A frame: id, start, contents start, end. -/
structure Frame where
  id : Nat
  s : Nat
  x : Nat
  e : Nat
  deriving Inhabited

partial def frames (b : ByteArray) (pos stop : Nat) : List Frame :=
  if pos ≥ stop then [] else
  let (n, j) := leb b (pos + 1)
  ⟨b[pos]!.toNat, pos, j, j + n⟩ :: frames b (j + n) stop

def instrEnd (b : ByteArray) (pos : Nat) : Nat :=
  match runAt b (do let op ← readByte; readInstr (b.size + 1) op.toNat) pos with
  | some (_, e) => e
  | none => panic! s!"bad instruction at {pos}"

/-- The plan of the instructions from `pos` up to the terminator at this level. -/
partial def seqPlan (b : ByteArray) (pos : Nat) : IPlan × Nat :=
  let rec go (pos leafStart : Nat) : IPlan × Nat :=
    let op := b[pos]!
    let flush (k : IPlan) : IPlan := if pos > leafStart then .leaf (pos - leafStart) k else k
    if op = 0x0B ∨ op = 0x05 then (flush .nil, pos)
    else
      let e := instrEnd b pos
      if e - pos ≤ T ∨ ¬(op = 0x02 ∨ op = 0x03 ∨ op = 0x04) then
        if e - leafStart ≤ T ∨ pos = leafStart then go e leafStart
        else
          let (rest, t) := go e pos
          (.leaf (pos - leafStart) rest, t)
      else
        let hdrEnd := match runAt b readBlockType (pos + 1) with
          | some (_, h) => h
          | none => panic! s!"bad block type at {pos}"
        let (body, t₁) := seqPlan b hdrEnd
        if b[t₁]! = 0x05 then
          let (els, t₂) := seqPlan b (t₁ + 1)
          let (rest, t) := go (t₂ + 1) (t₂ + 1)
          (flush (.ifElse (hdrEnd - pos) body els rest), t)
        else
          let (rest, t) := go (t₁ + 1) (t₁ + 1)
          (flush (.block (hdrEnd - pos) body rest), t)
  go pos pos

def codePlan (b : ByteArray) (pos : Nat) : CPlan × Nat :=
  let (len, c) := leb b pos
  let locEnd := match runAt b (readVec readLocalsGroup) c with
    | some (_, e) => e
    | none => panic! s!"bad locals at {c}"
  let (body, t) := seqPlan b locEnd
  if t + 1 ≠ c + len then panic! s!"code entry at {pos}: body ends at {t}" else
  (⟨c - pos, locEnd - c, body⟩, c + len)

partial def ppI : IPlan → String
  | .nil => "nil"
  | .leaf k p => s!"(leaf {k} {ppI p})"
  | .block k body p => s!"(block {k} {ppI body} {ppI p})"
  | .ifElse k t e p => s!"(ifElse {k} {ppI t} {ppI e} {ppI p})"

def ppC (p : CPlan) : String := s!"⟨{p.kSize}, {p.kLocals}, {ppI p.body}⟩"

def lst (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"

/-- Element runs of a vector at `y` with `n` elements read by `f`: lengths of runs of at most
`T` bytes (or one element), and the end. -/
def elemRuns {α : Type} (b : ByteArray) (f : DecodeM α) (n y : Nat) : List Nat × Nat := Id.run do
  let mut runs : Array Nat := #[]
  let mut start := y
  let mut pos := y
  for _ in [0:n] do
    let e := match runAt b f pos with
      | some (_, e) => e
      | none => panic! s!"bad vector element at {pos}"
    if e - start > T ∧ pos > start then
      runs := runs.push (pos - start); start := pos
    pos := e
  if pos > start then runs := runs.push (pos - start)
  return (runs.toList, pos)


/-! ## Component AST printers (as in `examples/wasm-components/gen/Kernel.lean`) -/

section Pp
open Silmaril.Wasm.Component.Binary

def hexDigits : List Char := "0123456789abcdef".toList

def hexLE (bs : List UInt8) : String := Id.run do
  let mut s := ""
  for b in bs.reverse do
    s := (s.push (hexDigits[b.toNat / 16]!)).push (hexDigits[b.toNat % 16]!)
  return if s.isEmpty then "0" else "0x" ++ s

def chunks4k : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | fuel + 1, l => if l.isEmpty then [] else l.take 4096 :: chunks4k fuel (l.drop 4096)

def ppBytes (b : ByteArray) : String :=
  let l := b.data.toList
  s!"(Silmaril.IncludeBytes.decode 4096 {l.length} [{", ".intercalate ((chunks4k l.length l).map hexLE)}])"

def r {α : Type} [Repr α] (a : α) : String := Std.Format.pretty (repr a) 100000
def par (s : String) : String := "(" ++ s ++ ")"
def B : String := "Silmaril.Wasm.Component.Binary."

mutual
partial def ppDefType : DefType → String
  | .val d => s!"{B}DefType.val {par (r d)}"
  | .func f => s!"{B}DefType.func {par (r f)}"
  | .component ds => s!"{B}DefType.component {lst (ds.map ppComponentDecl)}"
  | .instance ds => s!"{B}DefType.instance {lst (ds.map ppInstanceDecl)}"
  | .resource rep d => s!"{B}DefType.resource {par (r rep)} {par (r d)}"
partial def ppInstanceDecl : InstanceDecl → String
  | .coreType t => s!"{B}InstanceDecl.coreType {par (r t)}"
  | .type t => s!"{B}InstanceDecl.type {par (ppDefType t)}"
  | .alias a => s!"{B}InstanceDecl.alias {par (r a)}"
  | .export n d => s!"{B}InstanceDecl.export {par (r n)} {par (r d)}"
partial def ppComponentDecl : ComponentDecl → String
  | .import n d => s!"{B}ComponentDecl.import {par (r n)} {par (r d)}"
  | .inst d => s!"{B}ComponentDecl.inst {par (ppInstanceDecl d)}"
end

mutual
partial def ppSection : Section → String
  | .custom n d => s!"{B}Section.custom {r n} {ppBytes d}"
  | .coreModule b => s!"{B}Section.coreModule {ppBytes b}"
  | .coreInstances xs => s!"{B}Section.coreInstances {r xs}"
  | .coreTypes xs => s!"{B}Section.coreTypes {r xs}"
  | .component c => s!"{B}Section.component {par (ppAst c)}"
  | .instances xs => s!"{B}Section.instances {r xs}"
  | .aliases xs => s!"{B}Section.aliases {r xs}"
  | .types xs => s!"{B}Section.types {lst (xs.map ppDefType)}"
  | .canons xs => s!"{B}Section.canons {r xs}"
  | .start s => s!"{B}Section.start {par (r s)}"
  | .imports xs => s!"{B}Section.imports {r xs}"
  | .exports xs => s!"{B}Section.exports {r xs}"
  | .values _ => "(panic! \"value sections are not printed\")"
partial def ppAst : Ast → String
  | .mk ss => s!"{B}Ast.mk {lst (ss.map ppSection)}"
end

end Pp

/-! ## Output -/

def header (imports : List String) (doc : String) : String :=
  "module\n\n" ++ String.join (imports.map (s!"public import {·}\n")) ++
  s!"\n/-!\n{doc}\n\nGENERATED by `lake env lean --run examples/wasip3-rust/gen/Certs.lean`; do not edit.\n-/\n\n@[expose] public section\n\n" ++
  (if imports.any (·.endsWith "Chunked.Thms") || imports.any (·.endsWith "Sections.Thms") || imports.any (·.endsWith "File.Thms") then
    "-- Generated proofs share one simp set; some of its lemmas are unused in some files.\nset_option linter.unusedSimpArgs false\n\n" else "")

def writeFile (path : System.FilePath) (s : String) : IO Unit := do
  if let some d := path.parent then IO.FS.createDirAll d
  IO.FS.writeFile path s

/-- The reader, grammar and section abbreviation of each vector section id. -/
def vecInfo : Nat → Option (String × String × String)
  | 1 => some ("readRecType", "readRecType_sound", "TypeSec Forms.all")
  | 2 => some ("readImport", "readImport_sound", "ImportSec Forms.all")
  | 3 => some ("(readIdx (k := .type_))", "readIdx_sound", "FuncSec")
  | 4 => some ("readTable", "readTable_sound", "TableSec Forms.all")
  | 5 => some ("readMemType", "readMemType_sound", "MemSec Forms.all")
  | 6 => some ("readGlobal", "readGlobal_sound", "GlobalSec Forms.all")
  | 7 => some ("readExport", "readExport_sound", "ExportSec")
  | 9 => some ("readElem", "readElem_sound", "ElemSec Forms.all")
  | _ => none

/-- The Core section ids in their order (`sectionRank`), and the value names. -/
def order : List (Nat × String) :=
  [(1, "types"), (2, "imports"), (3, "funcTypes"), (4, "tables"), (5, "memories"),
   (13, "tags"), (6, "globals"), (7, "exports"), (8, "start"), (9, "elems"),
   (12, "dataCount"), (10, "codes"), (11, "datas")]

def W : String := "(by simp only [bytes, slice_decode]; decide +kernel)"

/-- Generate the certificate modules of core module `ci` (contents `ms` to `me`). -/
def genCore (b : ByteArray) (root : System.FilePath) (Name : String) (ci ms me : Nat) :
    IO String := do
  let ns := s!"Silmaril.Project.WasmP3Rust.{Name}"
  let cn := s!"{ns}.Core{ci}"
  let dir := root / "Silmaril" / "Project" / "WasmP3Rust" / Name / s!"Core{ci}"
  let fileMod := s!"{ns}.File.Defs"
  let fr := frames b (ms + 8) me
  -- assign customs to slots
  let mut slot := 0  -- index into `order` of the next expected section
  let mut customs : Array (Array Frame) := Array.replicate 14 #[]
  let mut present : Array (Option Frame) := Array.replicate 13 none
  for f in fr do
    if f.id = 0 then
      customs := customs.modify slot (·.push f)
    else
      let some i := order.findIdx? (·.1 = f.id) | panic! s!"unknown section {f.id}"
      if i < slot then panic! s!"section {f.id} out of order"
      present := present.set! i (some f)
      slot := i + 1
  -- code groups
  let cfo := (order.findIdx? (·.1 = 10)).bind (present[·]!)
  let (nCodes, firstEntry) := match cfo with
    | some cf => leb b cf.x
    | none => (0, 0)
  let mut groups : Array (Nat × Nat × Array String) := #[]
  let mut gStart := firstEntry
  let mut gPlans : Array String := #[]
  let mut pos := firstEntry
  for _ in [0:nCodes] do
    let (p, e) := codePlan b pos
    if e - gStart > groupBytes ∧ gPlans.size > 0 then
      groups := groups.push (gStart, pos, gPlans); gStart := pos; gPlans := #[]
    gPlans := gPlans.push (ppC p)
    pos := e
  if gPlans.size > 0 then groups := groups.push (gStart, pos, gPlans)
  if let some cf := cfo then
    if pos ≠ cf.e then panic! "code entries do not fill the code section"
  let gN := groups.size
  for h : gi in [0:gN] do
    let (x, y, ps) := groups[gi]
    let gns := s!"{cn}.Code.G{gi}"
    writeFile (dir / "Code" / s!"G{gi}" / "Defs.lean") <| header [fileMod]
      s!"# `{Name}`, core module {ci}: code entries {x} to {y} (group {gi} of {gN}), their plans" ++
      s!"namespace {gns}\nopen Silmaril.Wasm.Component.Chunked IPlan\nopen {ns}.File\n\n" ++
      s!"set_option maxRecDepth 100000 in\n/-- The plans of the {ps.size} code entries. -/\ndef plans : List CPlan := {lst ps.toList}\n\n" ++
      s!"/-- The code entries. -/\nnoncomputable def codes : List (List Silmaril.Wasm.ValType × Silmaril.Wasm.Expr) :=\n  codesOf plans (slice bytes {x} {y})\n\nend {gns}\n\nend\n"
    writeFile (dir / "Code" / s!"G{gi}" / "Thms.lean") <| header [s!"{gns}.Defs", "Silmaril.Wasm.Component.Chunked.Thms"]
      s!"# `{Name}`, core module {ci}: code entries {x} to {y} (group {gi} of {gN})\n\n**PROVED** (kernel): the plans check, so the bytes are the `Seq` of `Code` entries `codes`\n(`codesOk_sound`)." ++
      s!"namespace {gns}\nopen Silmaril.Wasm.Component.Chunked Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core\nopen {ns}.File\n\n" ++
      s!"set_option maxRecDepth 100000 in\ntheorem ok : codesOk plans (slice bytes {x} {y}) = true := {W}\n\n" ++
      s!"theorem seq : Seq (Code Forms.all) (slice bytes {x} {y}) codes := (codesOk_sound ok).1\n\n" ++
      s!"theorem length : codes.length = {ps.size} := (codesOk_sound ok).2.1\n\n" ++
      s!"theorem dataIdxs : codesDataIdxs codes = [] := (codesOk_sound ok).2.2\n\nend {gns}\n\nend\n"
  -- section values
  let mut defs := ""
  let mut thms := ""
  let mut importsThm : Option String := none
  let mut pieces : Array String := #[]   -- the 27 hypotheses' names, in `ModuleWithImports.mk` order
  let mut cuts : Array Nat := #[ms + 8]
  for i in [0:14] do
    -- customs slot i
    let cs := customs[i]!
    let name := s!"c{i}"
    if cs.isEmpty then
      let p := cuts.back!
      thms := thms ++ s!"theorem {name} : Customs (slice bytes {p} {p}) := customs_empty bytes {p}\n\n"
    else
      let a := cs[0]!.s
      let e := cs.back!.e
      if a ≠ cuts.back! then panic! "customs are not contiguous"
      let mut proofs : Array String := #[]
      for f in cs do
        let (nm, y) := match runAt b readName f.x with
          | some (nm, y) => (nm, y)
          | none => panic! s!"bad custom name at {f.x}"
        proofs := proofs.push s!"customSec_of bytes (s := {f.s}) (x := {f.x}) (y := {y}) (e := {f.e}) (nm := {nm.quote}) {W} {W} {W} rfl (by decide) (by decide) (by decide) (le_length bytes_length (by decide))"
      let cutsC := cs.toList.map (·.e)
      thms := thms ++ s!"theorem {name} : Customs (slice bytes {a} {e}) := by\n  have h := customs_of_spans bytes (a := {a}) (cuts := {lst (cutsC.map toString)}) (by decide) (by\n    simp only [pieces, allP]\n    exact ⟨{", ⟨".intercalate proofs.toList}, trivial{String.join (List.replicate proofs.size "⟩")})\n  simpa only [lastCut] using h\n\n"
      cuts := cuts.push e
    pieces := pieces.push name
    if i = 13 then break
    let (sid, vname) := order[i]!
    match present[i]! with
    | none =>
      let p := cuts.back!
      let (ty, v, pf) := match sid with
        | 13 => ("TagSec Forms.all", "([] : List Silmaril.Wasm.TagType)", "TagSec.absent")
        | 8 => ("StartSec", "(none : Option Silmaril.Wasm.FuncIdx)", "StartSec.mk Section.empty")
        | 12 => ("DataCntSec Forms.all", "(none : Option Nat)", "DataCntSec.absent")
        | 11 => ("DataSec Forms.all", "([] : List Silmaril.Wasm.Data)", "Section.empty")
        | 10 => ("CodeSec Forms.all", "([] : List (List Silmaril.Wasm.ValType × Silmaril.Wasm.Expr))", "Section.empty")
        | 1 => ("TypeSec Forms.all", "([] : List Silmaril.Wasm.RecType)", "Section.empty")
        | 2 => ("ImportSec Forms.all", "([] : List Silmaril.Wasm.Import)", "Section.empty")
        | 3 => ("FuncSec", "([] : List Silmaril.Wasm.TypeIdx)", "Section.empty")
        | 4 => ("TableSec Forms.all", "([] : List Silmaril.Wasm.Table)", "Section.empty")
        | 5 => ("MemSec Forms.all", "([] : List Silmaril.Wasm.MemoryType)", "Section.empty")
        | 6 => ("GlobalSec Forms.all", "([] : List Silmaril.Wasm.Global)", "Section.empty")
        | 7 => ("ExportSec", "([] : List Silmaril.Wasm.Export)", "Section.empty")
        | 9 => ("ElemSec Forms.all", "([] : List Silmaril.Wasm.Elem)", "Section.empty")
        | _ => panic! s!"section {sid}"
      defs := defs ++ s!"/-- No section {sid}. -/\ndef {vname} := {v}\n\n"
      thms := thms ++ s!"theorem h_{vname} : {ty} (slice bytes {p} {p}) {vname} := by\n  rw [slice_self]; exact {pf}\n\n"
      if sid = 10 then thms := thms ++ "theorem dataIdxs : codesDataIdxs codes = [] := rfl\n\n"
    | some f =>
      if f.s ≠ cuts.back! then panic! "section not contiguous"
      let kS := f.x - f.s - 1
      if sid = 10 then
        let (_, y) := leb b f.x
        let gcuts := groups.toList.map (·.2.1)
        let gcodes := (List.range gN).map (s!"Code.G{·}.codes")
        defs := defs ++ s!"/-- The code entries, from the {gN} groups. -/\nnoncomputable def codes : List (List Silmaril.Wasm.ValType × Silmaril.Wasm.Expr) :=\n  {lst gcodes}.flatten\n\n"
        let seqs := (List.range gN).map (s!"Code.G{·}.seq")
        thms := thms ++ s!"theorem h_codes : CodeSec Forms.all (slice bytes {f.s} {f.e}) codes := by\n" ++
          s!"  have hs : Seq (Code Forms.all) (slice bytes {y} {f.e}) codes := by\n" ++
          s!"    have h := seq_of_spans bytes (a := {y}) (cuts := {lst (gcuts.map toString)}) (by decide)\n      (xss := {lst gcodes}) (by simp only [pieces]; exact {String.join (seqs.map (s!"(.cons {·} "))}.nil{String.join (seqs.map fun _ => ")")})\n    simpa only [lastCut, codes] using h\n" ++
          s!"  have hl : codes.length = {nCodes} :=\n    (length_flatten_of {String.join ((List.range gN).map (s!"(.cons Code.G{·}.length "))}.nil{String.join ((List.range gN).map fun _ => ")")}).trans (by decide)\n" ++
          s!"  exact section_of_parts bytes (s := {f.s}) (x := {f.x}) (e := {f.e}) {W} {W} rfl (by decide) (by decide)\n    (le_length bytes_length (by decide)) (vec_of_parts bytes (x := {f.x}) (y := {y}) (e := {f.e}) {W} hl (by decide) (by decide) hs)\n\n"
        thms := thms ++ s!"theorem dataIdxs : codesDataIdxs codes = [] :=\n  codesDataIdxs_flatten_of ⟨{", ⟨".intercalate ((List.range gN).map (s!"Code.G{·}.dataIdxs"))}, trivial{String.join ((List.range gN).map fun _ => "⟩")}\n\n"
      else if sid = 11 then
        let (n, y) := leb b f.x
        let mut segs : Array String := #[]
        let mut p := y
        for _ in [0:n] do
          let (k, p1) := leb b p
          if k ≠ 0 then panic! s!"data segment kind {k} at {p}"
          let p2 := match runAt b readExpr p1 with
            | some (_, e) => e
            | none => panic! s!"bad data offset at {p1}"
          let (len, p3) := leb b p2
          segs := segs.push s!"({p1 - p}, {p2 - p1}, {p3 - p2})"
          p := p3 + len
        if p ≠ f.e then panic! "data segments do not fill the section"
        defs := defs ++ s!"/-- The data segments. -/\nnoncomputable def datas : List Silmaril.Wasm.Data :=\n  (chkSection 11 {kS} (chkDataVec {y - f.x} {lst segs.toList}) (slice bytes {f.s} {f.e})).getD []\n\n"
        thms := thms ++ s!"theorem h_datas : DataSec Forms.all (slice bytes {f.s} {f.e}) datas :=\n  dataSection_of {W}\n\n"
      else if sid = 8 then panic! "start sections are not generated"
      else if sid = 12 then panic! "data count sections are not generated"
      else
        let some (rd, snd, ty) := vecInfo sid | panic! s!"section {sid}"
        let (n, y) := leb b f.x
        let (runs, e) := match sid with
          | 1 => elemRuns b readRecType n y
          | 2 => elemRuns b readImport n y
          | 3 => elemRuns b (readIdx (k := .type_)) n y
          | 4 => elemRuns b readTable n y
          | 5 => elemRuns b readMemType n y
          | 6 => elemRuns b readGlobal n y
          | 7 => elemRuns b readExport n y
          | 9 => elemRuns b readElem n y
          | _ => panic! "unreachable"
        if e ≠ f.e then panic! s!"section {sid} elements do not fill it"
        let chk := s!"chkSection {sid} {kS} (chkVec {rd} {y - f.x} {lst (runs.map toString)}) (slice bytes {f.s} {f.e})"
        defs := defs ++ s!"/-- Section {sid}. -/\nnoncomputable def {vname} := ({chk}).getD []\n\n"
        let t := s!"theorem h_{vname} : {ty} (slice bytes {f.s} {f.e}) {vname} :=\n  vecSection_of {snd} {W}\n\n"
        if sid = 2 then importsThm := some t else thms := thms ++ t
      cuts := cuts.push f.e
    pieces := pieces.push s!"h_{vname}"
  if cuts.back! ≠ me then panic! s!"core module {ci} does not end at {me}"
  let coreDefs := header [fileMod] (s!"# `{Name}`, core module {ci}: section values\n\nThe values each section's plan decodes to (`getD` of the checker; the checks are in\n`{cn}.Sections.Thms`), and the module they form.") ++
    s!"namespace {cn}\nopen Silmaril.Wasm.Component.Chunked\nopen Silmaril.Wasm.Binary.Core Silmaril.Wasm.Binary.Core.Decode\nopen {ns}.File\n\n" ++
    (defs.replace "noncomputable def codes" "noncomputable def codes") ++ "end " ++ cn ++ "\n\nend\n"
  -- codes come from the group modules: put them in the Defs via imports
  let groupDefImports := (List.range gN).map (s!"{cn}.Code.G{·}.Defs")
  let coreDefs := coreDefs.replace s!"public import {fileMod}\n" (String.join ((fileMod :: groupDefImports).map (s!"public import {·}\n")))
  let moduleVal := s!"\n/-- **The core module** of the plans. -/\nnoncomputable def module : Silmaril.Wasm.Module :=\n  \{ types, imports, tags, globals, memories, tables,\n    funcs := zipFuncs funcTypes codes, data := datas, elems, start, exports }\n\n"
  writeFile (dir / "Defs.lean") (coreDefs.replace s!"end {cn}\n\nend\n" (moduleVal ++ s!"end {cn}\n\nend\n"))
  if let some t := importsThm then
    writeFile (dir / "Imports" / "Thms.lean") <| header [s!"{cn}.Defs", "Silmaril.Wasm.Component.Chunked.Thms", s!"{ns}.File.Thms"]
        s!"# `{Name}`, core module {ci}: the import section\n\n**PROVED** (kernel check of the plan): the import section has its Core grammar production\n(its own module: the names' UTF-8 checks cost about 7 ms per byte in the kernel)." ++
      s!"namespace {cn}\nopen Silmaril.Wasm.Component.Chunked\nopen Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core Silmaril.Wasm.Binary.Core.Decode\nopen {ns}.File\n\nset_option maxRecDepth 100000\n\n" ++ t ++ s!"end {cn}\n\nend\n"
  writeFile (dir / "Sections" / "Thms.lean") <| header ([s!"{cn}.Defs", "Silmaril.Wasm.Component.Chunked.Thms", s!"{ns}.File.Thms"] ++ (if importsThm.isSome then [s!"{cn}.Imports.Thms"] else []) ++ (List.range gN).map (s!"{cn}.Code.G{·}.Thms"))
      s!"# `{Name}`, core module {ci}: the sections\n\n**PROVED** (kernel checks of the plans on windows of the file): each section and each block of\ncustom sections has its Core grammar production on its slice." ++
    s!"namespace {cn}\nopen Silmaril.Wasm.Component.Chunked\nopen Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core Silmaril.Wasm.Binary.Core.Decode\nopen {ns}.File\n\nset_option maxRecDepth 100000\n\n" ++ thms ++ s!"end {cn}\n\nend\n"
  -- assembly
  let cutStr := lst (cuts.toList.drop 1 |>.map toString)
  let args := " ".intercalate pieces.toList
  writeFile (dir / "Thms.lean") <| header [s!"{cn}.Sections.Thms"]
      s!"# `{Name}`, core module {ci}: the whole module\n\n**PROVED**: the bytes {ms} to {me} of the file encode `module` under silmaril's Core binary\ngrammar (`Encodes`), assembled from the section certificates with `ModuleWithImports.mk`." ++
    s!"namespace {cn}\nopen Silmaril.Wasm.Component.Chunked\nopen Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core\nopen {ns}.File\n\n" ++
    s!"theorem header : slice bytes {ms} {ms + 8} = magic ++ version := {W}\n\n" ++
    (if gN = 0 then "theorem funcs_length : funcTypes.length = codes.length := by\n  simp only [funcTypes, codes, bytes, slice_decode]\n  decide +kernel\n\n" else
    s!"theorem funcs_length : funcTypes.length = codes.length := by\n  have hc : codes.length = {nCodes} :=\n    (length_flatten_of {String.join ((List.range gN).map (s!"(.cons Code.G{·}.length "))}.nil{String.join ((List.range gN).map fun _ => ")")}).trans (by decide)\n  have hf : funcTypes.length = {nCodes} := by\n    simp only [funcTypes, bytes, slice_decode]\n    decide +kernel\n  exact hf.trans hc.symm\n\n") ++
    s!"/-- **Core module {ci} decodes**: its bytes encode `module` (silmaril's `Encodes`). -/\ntheorem encodes : Encodes (slice bytes {ms} {me}) module := by\n" ++
    s!"  have H := ModuleWithImports.mk (F := Forms.all) (I := Vec (Import Forms.all)) {args}\n    (by simp [dataCount]) (Or.inr dataIdxs) funcs_length\n" ++
    s!"  refine moduleWith_of_eq H ?_\n" ++
    s!"  have e := slice_eq_flatten bytes {ms} ({ms + 8} :: {cutStr}) (by decide)\n" ++
    s!"  simp only [lastCut, pieces, List.flatten_cons, List.flatten_nil, List.append_nil] at e\n" ++
    s!"  rw [e, header]\n  simp only [slice_self, List.append_assoc, List.nil_append, List.append_nil]\n\nend {cn}\n\nend\n"
  return cn


/-- `<Name>/P3/{Defs,Thms}.lean`: the whole component under the grammar with async built-ins. -/
def genP3 (file Name : String) (root : System.FilePath) : IO Unit := do
  let b ← IO.FS.readBinFile (root / "examples" / "wasip3-rust" / "dist" / file)
  let ns := s!"Silmaril.Project.WasmP3Rust.{Name}"
  let dir := root / "Silmaril" / "Project" / "WasmP3Rust" / Name / "P3"
  let fr := frames b 8 b.size
  let mut defs := ""
  let mut thms := ""
  let mut terms : Array String := #[]
  let mut proofs : Array String := #[]
  let mut nV0 := 0
  let mut nCanon := 0
  let mut nCore := 0
  for f in fr do
    if f.id = 1 then
      terms := terms.push s!"Silmaril.Wasm.Component.BinaryP3.Section.coreModule (arr (slice bytes {f.x} {f.e}))"
      proofs := proofs.push s!"(coreModule_eq bytes (s := {f.s}) (x := {f.x}) (e := {f.e}) {W} {W} (by decide) (by decide) (le_length bytes_length (by decide)))"
      nCore := nCore + 1
    else
      let mini := ByteArray.mk ((Silmaril.Wasm.Component.Binary.preambleBytes ++ (b.extract f.s f.e).data.toList).toArray)
      match Silmaril.Wasm.Component.Binary.parse mini with
      | .ok (.mk [_]) =>
        terms := terms.push s!"Silmaril.Wasm.Component.BinaryP3.Section.ofV0 {ns}.sec{f.s}"
        proofs := proofs.push s!"(ofV0_eq sec{f.s}_eq)"
        nV0 := nV0 + 1
      | _ =>
        match Silmaril.Wasm.Component.BinaryP3.parse mini with
        | .ok (.mk [.canons xs]) =>
          let nm := s!"canon{f.s}"
          defs := defs ++ s!"/-- The `canon` section at {f.s}: {", ".intercalate (xs.map (·.kind))}. -/\ndef {nm} : Silmaril.Wasm.Component.BinaryP3.Section :=\n  Silmaril.Wasm.Component.BinaryP3.Section.canons {r xs}\n\n"
          thms := thms ++ s!"theorem {nm}_eq : Silmaril.Wasm.Component.BinaryP3.Encode.section_ {nm} = some (slice bytes {f.s} {f.e}) := {W}\n\n"
          terms := terms.push nm
          proofs := proofs.push s!"{nm}_eq"
          nCanon := nCanon + 1
        | _ => throw (IO.userError s!"section at {f.s} (id {f.id}) is neither old nor a canon section")
  writeFile (dir / "Defs.lean") <| header [s!"{ns}.Component.Defs", "Silmaril.Wasm.Component.BinaryP3.Defs"]
      s!"# `{Name}`: the whole component under the grammar with async built-ins\n\n`ast` is `{file}` as an AST of `Silmaril.Wasm.Component.BinaryP3` (component-model `d095e2f`):\n{nV0} sections of the old grammar (`Section.ofV0 secN`), {nCore} core modules (the bytes of\ntheir slices) and {nCanon} `canon` sections with async built-ins (`canonN`)." ++
    s!"namespace {ns}.P3\nopen Silmaril.Wasm.Component.Chunked\nopen {ns}.File\n\n" ++ defs ++
    s!"set_option maxRecDepth 100000 in\n/-- The component's sections. -/\nnoncomputable def secs : List Silmaril.Wasm.Component.BinaryP3.Section :=\n  {lst terms.toList}\n\n/-- **`{file}` as a component.** -/\nnoncomputable def ast : Silmaril.Wasm.Component.BinaryP3.Ast := .mk secs\n\nend {ns}.P3\n\nend\n"
  writeFile (dir / "Thms.lean") <| header [s!"{ns}.P3.Defs", s!"{ns}.Component.Thms", "Silmaril.Wasm.Component.Chunked.P3.Thms"]
      s!"# `{Name}`: the whole component parses\n\n**PROVED** (kernel, windows of the file): `encode_eq`, Silmaril's encoder with async built-ins\nwrites `ast` as the whole file, and so `parse_eq`, `BinaryP3.parse` reads the file as `ast`." ++
    s!"namespace {ns}.P3\nopen Silmaril.Wasm.Component.Chunked\nopen {ns} {ns}.File\n\n" ++ thms ++
    s!"set_option maxRecDepth 100000 in\n/-- **The encoding of the whole component.** -/\ntheorem encode_eq : Silmaril.Wasm.Component.BinaryP3.Encode.ast ast = some bytes := by\n  refine ast_of bytes {W} (cuts := {lst (fr.map (toString ·.e))}) (by decide)\n    (by simp only [lastCut, bytes_length]) ?_\n  simp only [secs, pieces]\n  exact {" ".intercalate (proofs.toList.map (s!"(.cons {·}"))} .nil{String.join (proofs.toList.map fun _ => ")")}\n\n" ++
    s!"/-- **`{file}` parses** under the grammar with async built-ins, as `ast`. -/\ntheorem parse_eq : Silmaril.Wasm.Component.BinaryP3.parse (arr bytes) = .ok ast :=\n  parse_of_ast encode_eq\n\nend {ns}.P3\n\nend\n"
  IO.println s!"{Name}: P3 modules: {nV0} old sections, {nCore} core modules, {nCanon} canon sections"

def main (args : List String) : IO Unit := do
  if args.head? = some "--p3" then
    genP3 args[1]! args[2]! ⟨(args.drop 3).headD "."⟩
    return
  let file := args[0]!
  let Name := args[1]!
  let root : System.FilePath := ⟨(args.drop 2).headD "."⟩
  let b ← IO.FS.readBinFile (root / "examples" / "wasip3-rust" / "dist" / file)
  let ns := s!"Silmaril.Project.WasmP3Rust.{Name}"
  let dir := root / "Silmaril" / "Project" / "WasmP3Rust" / Name
  -- chunk size: 256 bytes, or 1024 above 512 KiB (the kernel's recursion limit on the literal list)
  let C := if b.size > 512 * 1024 then 1024 else 256
  -- the file
  writeFile (dir / "File" / "Defs.lean") <| header ["Silmaril.Wasm.Component.Chunked.Defs"]
      s!"# `{Name}`: the file `examples/wasip3-rust/dist/{file}`\n\nIts bytes, read at elaboration time as {C}-byte chunk literals (`include_chunks`); the SHA-256\nof the file is in `examples/wasip3-rust/dist/SHA256SUMS`." ++
    s!"namespace {ns}.File\n\n/-- The chunk literals of `{file}`. -/\nnoncomputable def cs : List Nat :=\n  include_chunks {C} \"../../../../../examples/wasip3-rust/dist/{file}\"\n\n" ++
    s!"/-- The size of `{file}`. -/\ndef size : Nat := {b.size}\n\n/-- The bytes of `{file}`. -/\nnoncomputable def bytes : List UInt8 := Silmaril.IncludeBytes.bytesChunks {C} size cs\n\nend {ns}.File\n\nend\n"
  writeFile (dir / "File" / "Thms.lean") <| header [s!"{ns}.File.Defs", "Silmaril.Wasm.Component.Chunked.Thms"]
      s!"# `{Name}`: the size of the file" ++
    s!"namespace {ns}.File\nopen Silmaril.Wasm.Component.Chunked\n\ntheorem bytes_length : bytes.length = {b.size} :=\n  length_bytesChunks {C} size cs (by decide +kernel)\n\nend {ns}.File\n\nend\n"
  -- component frames
  let fr := frames b 8 b.size
  let mut cores : Array String := #[]
  let mut ci := 0
  for f in fr do
    if f.id = 1 then
      cores := cores.push (← genCore b root Name ci f.x f.e)
      ci := ci + 1
  -- the component's own sections other than core modules, through Silmaril's component grammar
  let mut ieDefs := ""
  let mut ieThms := ""
  let mut impNames : Array String := #[]
  let mut expNames : Array String := #[]
  let mut ieNames : Array String := #[]
  let mut undecoded : Array String := #[]
  let mut nDecoded := 0
  for f in fr do
    if f.id ≠ 1 then
      let mini := ByteArray.mk ((Silmaril.Wasm.Component.Binary.preambleBytes ++ (b.extract f.s f.e).data.toList).toArray)
      match Silmaril.Wasm.Component.Binary.parse mini with
      | .ok (.mk [sec]) =>
        let nm := s!"sec{f.s}"
        match sec with
        | .imports xs => impNames := impNames ++ (xs.map (·.name.name)).toArray; ieNames := ieNames.push nm
        | .exports xs => expNames := expNames ++ (xs.map (·.name.name)).toArray; ieNames := ieNames.push nm
        | _ => pure ()
        ieDefs := ieDefs ++ s!"/-- The component section at {f.s} (id {f.id}). -/\ndef {nm} : Section :=\n  {ppSection sec}\n\n"
        ieThms := ieThms ++ s!"theorem {nm}_eq : Encode.section_ {nm} = some (slice bytes {f.s} {f.e}) := {W}\n\n"
        nDecoded := nDecoded + 1
      | _ => undecoded := undecoded.push s!"{f.s} (id {f.id})"
  let ieDoc := s!"/-! ## The component's own sections\n\n{nDecoded} of the {fr.length} sections (all but the core modules and the sections listed next) are\nASTs of Silmaril's component grammar, checked with its encoder (`secN_eq`; `N` is the\nsection's offset). Silmaril's parser rejects the `canon` sections at offsets\n{", ".intercalate undecoded.toList} (compiled run of `Binary.parse`, not a kernel\nrefutation): they hold async built-ins. -/\n\n"
  writeFile (dir / "Component" / "Defs.lean") <| header [s!"{ns}.File.Defs"]
      s!"# `{Name}`: the component's own sections as ASTs of Silmaril's component grammar" ++
    s!"namespace {ns}\nopen Silmaril.Wasm.Component.Binary\n\n" ++
    s!"/-- The names of the component's imports and exports, from its import and export sections. -/\ndef names : List Section → List String × List String\n  | [] => ([], [])\n  | .imports xs :: ss => (xs.map (·.name.name) ++ (names ss).1, (names ss).2)\n  | .exports xs :: ss => ((names ss).1, xs.map (·.name.name) ++ (names ss).2)\n  | _ :: ss => names ss\n\n" ++
    ieDefs ++ s!"end {ns}\n\nend\n"
  writeFile (dir / "Component" / "Thms.lean") <| header [s!"{ns}.Component.Defs", s!"{ns}.File.Thms"]
      s!"# `{Name}`: the component's own sections, checked\n\n**PROVED** (kernel, windows of the file): Silmaril's component encoder writes each of these\nsections from its AST; `world_names` lists the imports and exports they declare." ++
    s!"namespace {ns}\nopen Silmaril.Wasm.Component.Chunked Silmaril.Wasm.Component.Binary\nopen {ns}.File\n\n" ++ ieDoc ++ ieThms ++
    s!"/-- **The component's imports and exports**, as its import and export sections (checked above\nwith Silmaril's component encoder) name them. -/\ntheorem world_names : names {lst ieNames.toList} =\n    ({lst (impNames.toList.map (·.quote))}, {lst (expNames.toList.map (·.quote))}) := by decide\n\n" ++
    s!"end {ns}\n\nend\n"
  let frameTerms := fr.map fun f => s!"({f.id}, slice bytes {f.x} {f.e})"
  let frameProofs := fr.map fun f =>
    s!"(.cons (frameEnc_of bytes (s := {f.s}) (x := {f.x}) (e := {f.e}) {W} {W} (by decide) (by decide) (le_length bytes_length (by decide)))"
  writeFile (dir / "Thms.lean") <| header ([s!"{ns}.File.Thms", s!"{ns}.Component.Thms"] ++ cores.toList.map (s!"{·}.Thms"))
      s!"# `{Name}`: the component's framing and its core modules\n\n**PROVED**: `{file}` is the preamble and {fr.length} framed sections (`frames`, whose bodies are\nslices of the file), and each of its {cores.size} core modules encodes its `module` under\nsilmaril's Core binary grammar." ++
    s!"namespace {ns}\nopen Silmaril.Wasm.Component.Chunked Silmaril.Wasm.Component.Binary\nopen {ns}.File\n\n" ++
    s!"/-- The component's sections: id and body. -/\nnoncomputable def frames : List RawSection :=\n  {lst frameTerms}\n\n" ++
    s!"set_option maxRecDepth 100000 in\n/-- **The framing of the file.** -/\ntheorem framing_eq : framing frames = some bytes := by\n  refine framing_of bytes {W} (cuts := {lst (fr.map (toString ·.e))}) (by decide)\n    (by simp only [lastCut, bytes_length]) ?_\n  simp only [frames, pieces]\n  exact {" ".intercalate frameProofs} .nil{String.join (frameProofs.map fun _ => ")")}\n\n" ++
    s!"/-- **The core modules decode.** -/\ntheorem cores_encode : {" ∧ ".intercalate ((List.range cores.size).zip (fr.filter (·.id = 1)) |>.map fun (i, f) => s!"Silmaril.Wasm.Binary.Core.Encodes (slice bytes {f.x} {f.e}) Core{i}.module")} :=\n  ⟨{", ".intercalate ((List.range cores.size).map (s!"Core{·}.encodes"))}⟩\n\nend {ns}\n\nend\n"
  IO.println s!"{Name}: {fr.length} frames, {cores.size} core modules"

end P3Gen

def main (args : List String) : IO Unit := P3Gen.main args
