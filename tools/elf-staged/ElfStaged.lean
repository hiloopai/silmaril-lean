import Silmaril.Elf.Staged.Defs
import Silmaril.Elf.Staged.Symbols.Defs
import Silmaril.Elf.Staged.Leaf.Defs
import Silmaril.Elf.Link.Dyn.Pages.Defs

/-!
# `elf-staged`: staged ELF parsing, natively (fast mode) and as kernel certificates

```
elf-staged layout FILE                 the stage-1 layout: sections, segments, spans
elf-staged bench FILE [TILES]          time every stage natively (fastRead and pageRead)
elf-staged emit FILE OUT.lean [opts]   a Lean module that kernel-checks stages (paranoid mode)
```

`TILES` is a file of `offset length` lines (instruction boundaries, file offsets in hex), as
`benchmarks/elf-staged/boundaries.sh` derives from `objdump -d`. The tool checks them as a
tiling (`tilesCover`, `tilesOk`) with the per-tile predicate "`Silmaril.X86.Ext.decode` reads an
instruction of exactly this length", and reports how many tiles the model accepts.

Everything this tool prints is **trusted computation**: the compiled reader on a `ByteArray`
(`fastRead`, proved to answer as the file by `Staged.sub_fast`). The theorems come from the
emitted module, checked by the kernel.
-/

open Silmaril.Elf
open Silmaril.Elf.Staged
open Silmaril.Elf.Link.DynElf (Rd Chunk pageRead pagesFrom)
open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader NameBytes Rela)

namespace ElfStaged

def nameStr (n : NameBytes) : String := String.ofList (n.map fun b => Char.ofNat b.toNat)

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Monotonic time of an action, in microseconds. -/
def timed {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← act
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 1000)

/-- Time `f x`, evaluated inside the measured interval (`noinline` and `IO.lazyPure` keep the
compiler from floating the computation out of it). -/
@[noinline] def timedOn {α β : Type} (x : β) (f : β → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure fun _ => f x
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 1000)

def ms (us : Nat) : String :=
  let s := toString (us / 1000) ++ "." ++ (toString (1000 + us % 1000)).drop 1
  s ++ " ms"

/-- The little-endian value of bytes `[lo, hi)` (divide and conquer: linearithmic, where a
byte-by-byte fold is quadratic). -/
partial def leRange (a : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 32 then Id.run do
    let mut v := 0
    let mut j := hi
    while j > lo do
      j := j - 1
      v := v * 256 + (a.get! j).toNat
    return v
  else
    let mid := (lo + hi) / 2
    leRange a lo mid + (leRange a mid hi <<< (8 * (mid - lo)))

/-- Little-endian 4 KiB chunk literals of a byte array (as `include_bytes` stores them). -/
def chunksOf (a : ByteArray) (c : Nat := 4096) : List Nat :=
  (List.range ((a.size + c - 1) / c)).map fun k => leRange a (c * k) (min a.size (c * (k + 1)))

def kindName (k : Nat) : String :=
  match k with
  | 0 => "NULL" | 1 => "PROGBITS" | 2 => "SYMTAB" | 3 => "STRTAB" | 4 => "RELA" | 5 => "HASH"
  | 6 => "DYNAMIC" | 7 => "NOTE" | 8 => "NOBITS" | 9 => "REL" | 11 => "DYNSYM" | 14 => "INIT_ARRAY"
  | 15 => "FINI_ARRAY" | 19 => "RELR" | 0x6ffffff6 => "GNU_HASH" | _ => hex k

def bodySize : Body → Nat
  | .symbols _ es => es.length | .relas es => es.length | .rels es => es.length
  | .relr ws => ws.length | .dynamic es => es.length | .versym vs => vs.length
  | .notes ns => ns.length | .gnuHash g => g.chain.length | .hash t => t.chains.length
  | _ => 0

def printLayout (L : Layout) (len : Nat) : IO Unit := do
  IO.println s!"type {L.header.fileType}  machine {L.header.machine}  entry {hex L.header.entry}  file {len} bytes"
  IO.println s!"bounds ok: {L.boundsOk len}"
  IO.println "segments (PT_LOAD):"
  for ph in L.phdrs do
    if ph.kind == PT_LOAD then
      IO.println s!"  off {hex ph.offset} filesz {hex ph.fileSize} vaddr {hex ph.virtualAddress} flags {ph.flags}"
  IO.println "sections:"
  for s in L.sections do
    let seg := match L.segmentOf s.span with
      | some ph => s!"in LOAD@{hex ph.offset}"
      | none => "-"
    IO.println s!"  {nameStr s.name}: {kindName s.header.kind} span [{hex s.span.off}, +{hex s.span.len}] {seg}"

def readFile (path : String) : IO ByteArray := IO.FS.readBinFile path

/-- Instruction tiles: `offset length` lines, hex offsets. -/
def readTiles (path : String) : IO (List (Nat × Nat)) := do
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for line in txt.splitOn "\n" do
    match line.trimAscii.toString.splitOn " " with
    | [o, l] =>
      let o' := (o.drop 2).foldl (fun acc ch => acc * 16 + (if ch.isDigit then ch.toNat - 48 else ch.toLower.toNat - 87)) 0
      out := out.push (o', l.toNat!)
    | _ => pure ()
  return out.toList

def layoutOrFail (r : Silmaril.Elf.Check.Src) : IO Layout :=
  match readLayout.run r with
  | some L => pure L
  | none => throw (IO.userError "not an ELF64 little-endian file the reader accepts")

def bench (path : String) (tiles? : Option String) : IO Unit := do
  let (a, tRead) ← timed (readFile path)
  IO.println s!"file {path}: {a.size} bytes, read in {ms tRead}"
  let src := fastRead a
  let (L?, tL) ← timedOn src fun r => readLayout.run r
  let some L := L? | throw (IO.userError "not an ELF64 file the reader accepts")
  IO.println s!"[fast] stage 1 layout ({L.phdrs.length} phdrs, {L.sections.length} sections): {ms tL}"
  IO.println s!"[fast] bounds ok: {L.boundsOk a.size}"
  let mut tBodies := 0
  let mut bodies : Array Body := #[]
  for s in L.sections do
    let (b?, t) ← timedOn src fun r => (Parse.body L.shs s.header).run r
    let some b := b? | throw (IO.userError s!"body of {nameStr s.name} failed")
    -- force the result before stopping the clock
    let n := bodySize b
    tBodies := tBodies + t
    bodies := bodies.push b
    if t > 1000 || n > 0 then
      IO.println s!"[fast] stage 2 body {nameStr s.name} ({n} entries): {ms t}"
  IO.println s!"[fast] stage 2 all bodies: {ms tBodies}"
  let (ld?, tLd) ← timedOn src fun r => (readLoader L.phdrs).run r
  let some ld := ld? | throw (IO.userError "loader view failed")
  IO.println s!"[fast] stage 2' loader view ({ld.dynamic.length} dynamic entries, interp {ld.interp.isSome}): {ms tLd}"
  let (A?, tA) ← timedOn src fun r => Silmaril.Elf.read.run r
  let some A := A? | throw (IO.userError "whole-file parse failed")
  IO.println s!"[fast] whole-file spec `read` ({A.sections.length} sections): {ms tA}"
  IO.println s!"[fast] stages assemble to the whole parse: {decide (L.assemble bodies.toList ld = A)}"
  let (ok, tC) ← timedOn src fun r => Silmaril.Elf.Check.file r A
  IO.println s!"[fast] existing checker Check.file on the parse: {ok} in {ms tC}"
  -- RELA windows
  for s in L.sections do
    if s.header.kind == SHT_RELA then
      if let .relas es := (Parse.body L.shs s.header).run src |>.getD .null then
        let w := 1024
        let (okw, tw) ← timedOn src fun src => (Id.run do
          let mut ok := true
          let mut i := 0
          while i < es.length do
            ok := ok && entriesOk src Parse.rela s.header.offset 24 i ((es.drop i).take w)
            i := i + w
          return ok)
        IO.println s!"[fast] stage 3 {nameStr s.name}: {(es.length + w - 1) / w} windows of {w} entries, ok {okw}: {ms tw}"
  -- the kernel's source, natively
  let (cs, tCs) ← timedOn a fun a => chunksOf a
  let pg := pagesFrom 4096 0 a.size cs
  IO.println s!"[pages] {cs.length} chunk literals built natively in {ms tCs}"
  let (Lp?, tLp) ← timedOn pg fun pg => readLayout.run (pageRead 4096 pg)
  IO.println s!"[pages] stage 1 layout on pageRead (native): {ms tLp}, agrees {decide (Lp? = some L)}"
  -- disassembly tiles
  if let some tp := tiles? then
    let ts ← readTiles tp
    let text := L.section? ".text"
    IO.println s!"[tiles] {ts.length} instruction tiles from {tp}"
    -- contiguous runs: tilesOk walks consecutive tiles from one start offset
    let lens := ts.map (·.2)
    let start := (ts.head?.map (·.1)).getD 0
    let contiguous := (ts.zip (ts.drop 1)).all fun (x, y) => x.1 + x.2 == y.1
    IO.println s!"[tiles] contiguous {contiguous}; covers .text {match text with
      | some s => tilesCover ⟨start, s.span.len⟩ lens && start == s.span.off
      | none => false}"
    let (n, tT) ← timedOn src fun src => ts.foldl (fun acc (o, l) =>
      match src o l with
      | some v => if x86Ok l v then acc + 1 else acc
      | none => acc) 0
    IO.println s!"[tiles] Silmaril.X86.Ext.decode accepts {n} / {ts.length} tiles ({n * 1000 / max 1 ts.length / 10}.{n * 1000 / max 1 ts.length % 10}%) in {ms tT}"
    let (okAll, tW) ← timedOn src fun src => tilesOk src (fun _ _ => true) start lens
    IO.println s!"[tiles] tilesOk (bounds only) over all tiles: {okAll} in {ms tW}"

/-! ## Emitting a paranoid-mode module -/

def litName (n : NameBytes) : String :=
  let v := (n.reverse.foldl (fun acc b => acc * 256 + b.toNat) 0)
  s!"(Silmaril.Elf.Lit.name {n.length} {v})"

def litHeader (h : Header) : String :=
  s!"⟨{h.osABI}, {h.abiVersion}, {h.fileType}, {h.machine}, {h.version}, {h.entry}, {h.programOffset}, {h.sectionOffset}, {h.flags}, {h.headerSize}, {h.programEntrySize}, {h.programCount}, {h.sectionEntrySize}, {h.sectionCount}, {h.sectionNameIndex}⟩"

def litPh (p : ProgramHeader) : String :=
  s!"⟨{p.kind}, {p.flags}, {p.offset}, {p.virtualAddress}, {p.physicalAddress}, {p.fileSize}, {p.memorySize}, {p.alignment}⟩"

def litSh (s : SectionHeader) : String :=
  s!"⟨{s.name}, {s.kind}, {s.flags}, {s.address}, {s.offset}, {s.size}, {s.link}, {s.info}, {s.alignment}, {s.entrySize}⟩"

def litLayout (L : Layout) : String :=
  let phs := ",\n    ".intercalate (L.phdrs.map litPh)
  let secs := ",\n    ".intercalate (L.sections.map fun s => s!"⟨{litSh s.header}, {litName s.name}⟩")
  s!"⟨{litHeader L.header},\n  [{phs}],\n  [{secs}]⟩"

def litRela (r : Rela) : String :=
  let a := match r.addend with
    | .ofNat n => s!"Int.ofNat {n}"
    | .negSucc n => s!"Int.negSucc {n}"
  s!"⟨{r.offset}, {r.info}, {a}⟩"

def litDyn (d : Dyn) : String := s!"⟨{d.tag}, {d.val}⟩"

def litOptName : Option NameBytes → String
  | none => "none"
  | some n => s!"(some {litName n})"

def litLoader (ld : Loader) : String :=
  s!"⟨[{", ".intercalate (ld.dynamic.map litDyn)}], {litOptName ld.interp}, [{", ".intercalate (ld.needed.map litName)}], {litOptName ld.soname}, {litOptName ld.runpath}⟩"

structure EmitOpts where
  relaWindows : Nat := 1
  relaWindow : Nat := 256
  tiles : Option String := none
  tileCount : Nat := 64
  /-- Also emit the monolithic baseline: the whole parse, one `decide +kernel`. -/
  whole : Bool := false
  /-- Also emit every section body and the assembled parse (small files). -/
  bodies : Bool := false
  /-- Use this existing `include_bytes` constant instead of including the file. -/
  bytesConst : Option String := none
  imports : List String := []
  ns : String := "ElfStagedBench"
  /-- The `kbytes_def` constant of the file (`emit-example`). -/
  kbytes : Option String := none
  /-- First tile: the entry point by default. -/
  tileFrom : Option Nat := none

def emit (path out : String) (o : EmitOpts) : IO Unit := do
  let a ← readFile path
  let src := fastRead a
  let L ← layoutOrFail src
  let some ld := (readLoader L.phdrs).run src | throw (IO.userError "loader view failed")
  let absPath ← IO.FS.realPath path
  let cname := o.bytesConst.getD "bytes"
  let bytesDef := if o.bytesConst.isSome then "" else
    s!"noncomputable def bytes : Silmaril.Formats.Bytes := ⟨include_bytes \"{absPath}\"⟩\n\n"
  let mut s := s!"import Silmaril.Elf.Staged.Leaf.Thms
import Silmaril.Elf.Shapes.Thms
import Silmaril.Elf.Link.Dyn.Pages.Defs
{o.imports.foldl (fun acc m => acc ++ s!"import {m}\n") ""}
/-! Generated by `elf-staged emit` from {path} ({a.size} bytes). Paranoid mode: every theorem
below is checked by the kernel (`decide +kernel` on 4 KiB page literals); no compiled evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace {o.ns}

open Silmaril.Elf Silmaril.Elf.Staged
open Silmaril.Elf.Link.DynElf (pageRead pagesFrom ChunksOf)

{bytesDef}/-- The file. -/
noncomputable abbrev F : Silmaril.X86.Link.Blob := blobOf {cname}

/-- Its 4 KiB pages (the kernel's byte source). -/
noncomputable def pg := pagesFrom 4096 0 {a.size} (chunks_of% {cname})

theorem hc : ChunksOf F pg := Rows.pages_of_bytes rfl

/-- The stage-1 layout (emitted by the fast mode; checked below). -/
def L : Layout :=
{litLayout L}

/-- **Stage 1**, kernel-checked. -/
theorem layout : LayoutIs F L := Leaf.layout.of_kernel hc (c := L) (by decide +kernel)

/-- Every span of the layout lies in the file. -/
theorem bounds : L.boundsOk {a.size} = true := by decide +kernel

"
  s := s ++ s!"/-- **Stage 2'**: the loader view (`PT_DYNAMIC`, `PT_INTERP`, `DT_NEEDED`, …). -/
theorem loader : LoaderIs F L {litLoader ld} :=
  Leaf.loader.of_kernel hc (c := (L, {litLoader ld})) (by decide +kernel)

"
  let mut idx := 0
  for sec in L.sections do
    if sec.header.kind == SHT_RELA then
      if let .relas es := ((Parse.body L.shs sec.header).run src).getD .null then
        for k in List.range o.relaWindows do
          let i := k * o.relaWindow
          let win := (es.drop i).take o.relaWindow
          if !win.isEmpty then
            s := s ++ s!"/-- Window {k} of section {idx} (`{nameStr sec.name}`): entries {i}…{i + win.length - 1}. -/
def relaW_{idx}_{k} : List Silmaril.Formats.ELF.Rela :=
  [{", ".intercalate (win.map litRela)}]
/-- **Stage 3** (`elf.rela`): window {k} of section {idx}, kernel-checked. -/
theorem rela_{idx}_{k} : EntriesAt F Parse.rela {sec.header.offset} 24 {i} relaW_{idx}_{k} :=
  Leaf.rela.of_kernel hc (c := ({sec.header.offset}, {i}, relaW_{idx}_{k})) (by decide +kernel)

"
    idx := idx + 1
  if let some tp := o.tiles then
    let from_ := o.tileFrom.getD ((L.offsetOf L.header.entry).getD 0)
    let ts := ((← readTiles tp).dropWhile (·.1 < from_)).take o.tileCount
    if let some (start, _) := ts.head? then
      let lens := ts.map (·.2)
      let pre := ts.takeWhile fun (o, l) => match src o l with | some v => x86Ok l v | none => false
      s := s ++ s!"/-- **Disassembly tiles**: {ts.length} consecutive instruction boundaries from {hex start} lie in the
file (bounds only). -/
theorem tiles : TilesAt F (fun _ _ => true) {start} {lens} :=
  Leaf.tiles.of_kernel hc (c := ({start}, {lens})) (by decide +kernel)

"
      if !pre.isEmpty then
        s := s ++ s!"/-- **Decoded tiles**: the first {pre.length} of them are each one instruction of the local
x86 model (`Silmaril.X86.Ext.decode` reads exactly the tile). -/
theorem tiles_x86 : TilesAt F x86Ok {start} {pre.map (·.2)} :=
  Leaf.tilesX86.of_kernel hc (c := ({start}, {pre.map (·.2)})) (by decide +kernel)

"
  if o.whole then
    let some A := Silmaril.Elf.read.run src | throw (IO.userError "whole-file parse failed")
    s := s ++ s!"/-- The whole parse (emitted by the fast mode). -/
def A : File := {(reprStr A).replace "\n" " "}

/-- **Baseline**: the whole parse in one kernel run of the specification on the pages. -/
theorem whole : Parses F A := Rows.parses_of_pages (c := 4096) hc (by decide +kernel)

"
  if o.bodies then
    let mut names : Array String := #[]
    let mut bs : Array String := #[]
    for (sec, k) in L.sections.zipIdx do
      let some b := (Parse.body L.shs sec.header).run src | throw (IO.userError "body failed")
      names := names.push s!"body_{k}"
      bs := bs.push s!"b{k}"
      s := s ++ s!"/-- The body of section {k} (`{nameStr sec.name}`), emitted by the fast mode. -/
def b{k} : Body :=
  {(reprStr b).replace "\n" " "}

/-- **Stage 2**: the body of section {k}, kernel-checked. -/
theorem body_{k} : BodyIs F L {litSh sec.header} b{k} := bodyIs_of_pages hc (by decide +kernel)

"
    let forall2 := names.foldr (fun n acc => s!"(.cons {n} {acc})") ".nil"
    s := s ++ s!"/-- The loader view, emitted by the fast mode. -/
def ld : Loader := {litLoader ld}

/-- **The stages assemble to the whole parse** (`parses_assemble`; no further kernel run). -/
theorem parses : Parses F (L.assemble [{", ".intercalate bs.toList}] ld) :=
  parses_assemble layout
    {forall2}
    loader

"
  s := s ++ s!"end {o.ns}\n"
  IO.FS.writeFile out s
  IO.println s!"wrote {out}"


/-! ## Emitting an example: an object module and a leaf module -/

def litSym (s : Silmaril.Formats.ELF.ObjectSymbol) : String := s!"{litName s.name}"

/-- `emit-example`: the shared objects (layout, loader view, bodies, symbol indexes, the tiles
of one function) as small named definitions in `defsOut`, and the leaf theorems that check them
against the bytes in `thmsOut` (which imports `defsOut`'s module and the bytes). -/
def emitExample (path defsMod defsOut thmsOut : String) (o : EmitOpts) (fn : Option String) :
    IO Unit := do
  let a ← readFile path
  let src := fastRead a
  let L ← layoutOrFail src
  let some ld := (readLoader L.phdrs).run src | throw (IO.userError "loader view failed")
  let some cname := o.bytesConst | throw (IO.userError "emit-example needs --bytes-const")
  let ns := o.ns
  let hdr := s!"(generated by `elf-staged emit-example` from {path}, {a.size} bytes)"
  -- objects
  let mut d := s!"module

public import Silmaril.Elf.Staged.Symbols.Defs
import Silmaril.Elf.Staged.Leaf.Defs

/-! # Shared objects for the staged checks of `{path}`

Untrusted data {hdr}: each definition is a small certificate a leaf in
`{defsMod.replace ".Defs" ".Thms"}` checks against the file's bytes. Nothing here is believed
until a leaf checks it. -/

set_option maxRecDepth 100000

@[expose] public section

namespace {ns}

open Silmaril.Elf Silmaril.Elf.Staged

/-- The stage-1 layout. -/
def L : Layout :=
{litLayout L}

/-- The loader view. -/
def ld : Loader := {litLoader ld}

"
  let kn := o.kbytes.getD "kbytes"
  -- one leaf proof: the native run when the policy allows `proc`, else the kernel run
  let leaf (_proc fn : String) (c : Option String) : String :=
    let (cn, ca) := match fn, c with
      | "layout", _ => ("L", "L")
      | "byName", _ => ("x", "byName")
      | "byAddr", _ => ("x", "byAddr")
      | _, some c => ("c", c)
      | _, none => ("c", "_")
    let kn' := if fn == "byName" || fn == "byAddr" then "s" else cn
    s!"by\n  edge_pair\n    (native := Native.{fn}_sound (raw := {cname}) ({cn} := {ca}))\n    (kernel := Kernel.{fn}_sound {kn}.wf {kn}.toByteArray_eq ({kn'} := {ca}))"
  let mut t := s!"module

public import {defsMod}
public import Silmaril.Elf.Staged.Native.Defs
{o.imports.foldl (fun acc m => acc ++ s!"public import {m}\n") ""}-- Native runs interpret the objects, the bytes and the checkers while elaborating.
public meta import {defsMod}
public meta import Silmaril.Elf.Staged.Native.Defs
{o.imports.foldl (fun acc m => acc ++ s!"public meta import {m}\n") ""}
/-! # Staged checks of `{path}`

Every theorem is one leaf (`Silmaril.Elf.Staged.Leaf`) proved by `edge_pair` {hdr}: natively on
the file's `ByteArray` when the trust policy allows the leaf's procedure in this module, and
otherwise by the kernel on the same file's kernel bytes `{kn}`. The propositions are the same
in every profile; `Silmaril.Elf.Staged.Example.Profiles` checks them under `local` and
`paranoid`. -/

@[expose] public section

namespace {ns}

open Silmaril.Elf Silmaril.Elf.Staged

/-- The file. -/
noncomputable abbrev F : Silmaril.X86.Link.Blob := blobOf ⟨{cname}⟩

-- The kernel bytes of the same literals (`{kn}.wf`, `{kn}.toByteArray_eq`). Defined here, not in
-- the bytes module: a `kbytes_def` body is not yet exported to importing modules.
kbytes_def {kn} of_include {cname}

/-- **Stage 1** (`elf.layout`). -/
theorem layout : LayoutIs F L := {leaf "elf.layout" "layout" none}

/-- **Stage 2'** (`elf.loader`). -/
theorem loader : LoaderIs F L ld := {leaf "elf.loader" "loader" (some "(L, ld)")}

"
  let mut names : Array String := #[]
  let mut bs : Array String := #[]
  for (sec, k) in L.sections.zipIdx do
    let some b := (Parse.body L.shs sec.header).run src | throw (IO.userError "body failed")
    names := names.push s!"body_{k}"
    bs := bs.push s!"b{k}"
    d := d ++ s!"/-- The body of section {k} (`{nameStr sec.name}`). -/
def b{k} : Body :=
  {(reprStr b).replace "\n" " "}

"
    t := t ++ s!"theorem body_{k} : BodyIs F L {litSh sec.header} b{k} :=
  {leaf "elf.body" "body" (some s!"(L, {litSh sec.header}, b{k})")}

"
  let forall2 := names.foldr (fun n acc => s!"(.cons {n} {acc})") ".nil"
  d := d ++ s!"/-- The section bodies, in order. -/
def bodies : List Body := [{", ".intercalate bs.toList}]

"
  t := t ++ s!"/-- **The stages assemble to the whole parse** (`parses_assemble`; no further kernel run). -/
theorem parses : Parses F (L.assemble bodies ld) :=
  parses_assemble layout
    {forall2}
    loader

"
  -- symbol indexes over .symtab
  let symtab? := L.sections.find? (·.header.kind == SHT_SYMTAB)
  if let some st := symtab? then
    let some strs := L.shs[st.header.link]? | throw (IO.userError "symtab link")
    let tab : Symbols.Tab := ⟨strs, st.header⟩
    let syms := (List.range tab.count).filterMap fun i => ((tab.entry i).run src).map (i, ·)
    -- forward: first entry of each nonempty name, sorted by name
    let named := syms.filter (·.2.name ≠ [])
    let sorted := named.toArray.qsort (fun x y => Symbols.nameCmp x.2.name y.2.name == .lt) |>.toList
    let fwd := sorted.foldl (fun (acc : List (Nat × Silmaril.Formats.ELF.ObjectSymbol)) e =>
      match acc.head? with
      | some h => if Symbols.nameCmp h.2.name e.2.name == .eq then acc else e :: acc
      | none => [e]) [] |>.reverse
    let rev := (syms.filter (0 < ·.2.raw.size)).toArray.qsort (fun x y => x.2.raw.value < y.2.raw.value) |>.toList
    d := d ++ s!"/-- The symbol table `{nameStr st.name}` and its string table. -/
def symtab : Symbols.Tab := ⟨{litSh strs}, {litSh st.header}⟩

/-- **Forward index**: each named symbol's first entry, sorted by name. -/
def byName : Symbols.ByName := ⟨symtab, #[{", ".intercalate (fwd.map fun (i, s) => s!"({litSym s}, {i})")}]⟩

/-- **Reverse map**: `(value, size, entry)` of the symbols with a size, sorted by value. -/
def byAddr : Symbols.ByAddr := ⟨symtab, #[{", ".intercalate (rev.map fun (i, s) => s!"({s.raw.value}, {s.raw.size}, {i})")}]⟩

"
    t := t ++ s!"/-- `elf.symbols.byName`. -/
theorem byName_ok : byName.sorted = true ∧ byName.Sound F :=
  {leaf "elf.symbols.byName" "byName" none}

/-- `elf.symbols.byAddr`. -/
theorem byAddr_ok : byAddr.sorted = true ∧ byAddr.Sound F :=
  {leaf "elf.symbols.byAddr" "byAddr" none}

"
    -- one function, grounded in the file
    if let (some f, some tp) := (fn, o.tiles) then
      let some (i, s) := fwd.find? (fun e => e.2.name == nameOf f) | throw (IO.userError s!"no symbol {f}")
      let v := s.raw.value
      let some off := L.offsetOf v | throw (IO.userError "function not in a PT_LOAD")
      let ts := ((← readTiles tp).dropWhile (·.1 < off)).takeWhile (·.1 < off + s.raw.size)
      let lens := ts.map (·.2)
      d := d ++ s!"/-- The instruction boundaries of `{f}`, from a disassembler. -/
def {f}Tiles : List Nat := {lens}

"
      t := t ++ s!"/-- **`{f}` by name**: the forward index names entry {i}, and it is `{f}`. -/
theorem {f}_entry : ∃ s, Symbols.SymAt F symtab {i} s ∧ s.name = nameOf \"{f}\" :=
  Symbols.ByName.find_sound byName_ok.2 (n := nameOf \"{f}\") (by decide)

/-- **Its extent**: the reverse map sends its first address back to entry {i}. -/
theorem {f}_extent : ∃ s, Symbols.SymAt F symtab {i} s ∧ s.raw.value ≤ {v} ∧ {v} < s.raw.value + s.raw.size :=
  Symbols.ByAddr.find_sound byAddr_ok.2 (by decide)

/-- **Its code**: address {hex v} is file offset {hex off}, the tiles cover its {s.raw.size} bytes, and
each tile is one instruction of the local x86 model (`elf.tiles.x86`). -/
theorem {f}_code : L.offsetOf {v} = some {off} ∧ tilesCover ⟨{off}, {s.raw.size}⟩ {f}Tiles = true ∧
    TilesAt F x86Ok {off} {f}Tiles :=
  ⟨by decide, by decide, {leaf "elf.tiles.x86" "tilesX86" (some s!"({off}, {f}Tiles)")}⟩

"
  d := d ++ s!"end {ns}\n"
  t := t ++ s!"end {ns}\n"
  IO.FS.writeFile defsOut d
  IO.FS.writeFile thmsOut t
  IO.println s!"wrote {defsOut} and {thmsOut}"

def usage : String :=
  "usage: elf-staged layout FILE | bench FILE [TILES] | emit-example FILE DEFS_MODULE DEFS.lean THMS.lean --bytes-const RAW --kbytes K [--import M] [--namespace NS] [--tiles TILES --function F] | emit FILE OUT.lean [--rela-windows N] [--rela-window N] [--tiles TILES] [--tile-count N] [--tile-from OFFSET] [--whole] [--bodies] [--bytes-const NAME] [--import MODULE] [--namespace NS]"

partial def parseOpts : List String → EmitOpts → EmitOpts
  | "--rela-windows" :: n :: rest, o => parseOpts rest { o with relaWindows := n.toNat! }
  | "--rela-window" :: n :: rest, o => parseOpts rest { o with relaWindow := n.toNat! }
  | "--tiles" :: p :: rest, o => parseOpts rest { o with tiles := some p }
  | "--bodies" :: rest, o => parseOpts rest { o with bodies := true }
  | "--bytes-const" :: c :: rest, o => parseOpts rest { o with bytesConst := some c }
  | "--import" :: m :: rest, o => parseOpts rest { o with imports := o.imports ++ [m] }
  | "--kbytes" :: n :: rest, o => parseOpts rest { o with kbytes := some n }
  | "--namespace" :: n :: rest, o => parseOpts rest { o with ns := n }
  | "--whole" :: rest, o => parseOpts rest { o with whole := true }
  | "--tile-count" :: n :: rest, o => parseOpts rest { o with tileCount := n.toNat! }
  | "--tile-from" :: n :: rest, o => parseOpts rest { o with tileFrom := some n.toNat! }
  | _, o => o

end ElfStaged

open ElfStaged in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["layout", path] =>
    let a ← readFile path
    let L ← layoutOrFail (fastRead a)
    printLayout L a.size
    pure 0
  | ["bench", path] => bench path none; pure 0
  | ["bench", path, tiles] => bench path (some tiles); pure 0
  | "emit" :: path :: out :: rest => emit path out (parseOpts rest {}); pure 0
  | "emit-example" :: path :: defsMod :: defsOut :: thmsOut :: rest =>
    let fn := match rest.dropWhile (· != "--function") with
      | _ :: f :: _ => some f
      | _ => none
    emitExample path defsMod defsOut thmsOut (parseOpts (rest.filter (· != "--function")) {}) fn
    pure 0
  | _ => IO.eprintln usage; pure 2
