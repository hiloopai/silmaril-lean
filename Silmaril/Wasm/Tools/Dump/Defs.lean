module

public import Silmaril.Wasm.Tools.DumpOps.Defs
public import Silmaril.Wasm.Tools.DumpFlat.Defs
public import Silmaril.Wasm.Tools.DumpComp.Defs
public import Silmaril.Wasm.Tools.RustDebug.Defs

/-!
# `wasm-tools dump`: a module binary, byte by byte

`wasm-tools dump` (wasm-tools 1.262.0, `src/bin/wasm-tools/dump.rs`) classifies every byte of a
binary: one line per item, with the offset of its first byte, its bytes in rows of four and a
description (wasmparser's `Debug` forms), plus `... N bytes of data` lines for payloads and
`--- rec group ---` / `==== func ====` separators.

The transcription keeps upstream's machine: a pending description (`state`), a cursor
(`cur`), `print stop` (the bytes `[cur, stop)` with the pending description, then
`cur := stop`; upstream asserts `cur < stop` and panics otherwise, here an error),
`dataLine` (a `---` line, `cur := stop`) and raw separator lines.

* Items are read with the transcription of wasmparser's readers (`DumpFlat`), bounded by
  their section, as wasmparser's `SectionLimited` readers are.
* **Operators** of function bodies and constant expressions come from the certified decoder
  with a log, `DumpOps.dExpr` (`DumpOps.Thms.dExpr_erase`: without the log it is silmaril-lean's
  `readExpr`), whenever it reads the whole body (respectively an expression). Otherwise (a
  proposal outside silmaril-lean's Core 3.0 model, or a malformed body) they come from
  `DumpFlat.opR`, wasmparser's flat operator reader with its control-frame stack, printing `??`
  for an operator that fails and continuing where the reader stopped, as upstream.
* The checks of wasmparser's `Parser` (section order, function/code and data-count/data
  counts, malformed ids, sizes) stop the walk with an error, as upstream's `item?`.

* `Line`: what is printed (a byte line, a data line or a raw line), with its byte range;
* `walk`: the walker over a core module, producing `Line`s;
* `renderLine`: upstream's text of a line;
* `dump b color`: the whole output, and the error if the walk stopped early (what was printed
  before the error is kept, as upstream's streaming output).

`Thms`: the byte ranges of the lines of a successful dump tile `[0, b.size)` (`dump_tiles`).

Components are not walked (see `tools/wasm-tools/README.md`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Dump

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Tools.DumpOps (listDbg dExpr)
open Silmaril.Wasm.Tools.DumpFlat (R)

/-- A printed line. `bytes`: the bytes `[start, stop)` with a description (`color`: printed
with `color_print`); `data`: a `---| ... msg` line standing for the bytes `[start, stop)`;
`raw`: a separator line, no bytes. -/
inductive Line where
  | bytes (nest start stop : Nat) (text : String) (color : Bool)
  | data (nest start stop : Nat) (msg : String)
  | raw (text : String)
  deriving Repr, Inhabited

/-- The byte range of a line (`none` for a raw line). -/
def Line.range : Line → Option (Nat × Nat)
  | .bytes _ s t _ _ => some (s, t)
  | .data _ s t _ => some (s, t)
  | .raw _ => none

/-- Index counters (`Indices` of `dump.rs`, the core part). -/
structure Counters where
  types : Nat := 0
  funcs : Nat := 0
  globals : Nat := 0
  tables : Nat := 0
  memories : Nat := 0
  tags : Nat := 0
  recGroups : Nat := 0
  coreModules : Nat := 0
  coreInstances : Nat := 0
  /-- Component index spaces. -/
  cTypes : Nat := 0
  cFuncs : Nat := 0
  components : Nat := 0
  instances : Nat := 0
  values : Nat := 0
  deriving Inhabited

/-- The machine state. -/
structure St where
  cur : Nat := 0
  state : String := ""
  lines : Array Line := #[]
  nest : Nat := 1
  ix : Counters := {}
  /-- The end of the current section: readers do not read past it. -/
  lim : Nat := 0
  /-- The rank of the last non-custom section (`Order` of wasmparser's `Parser`). -/
  order : Nat := 0
  funcEntries : Option Nat := none
  codeEntries : Option Nat := none
  dataCount : Option Nat := none
  dataEntries : Option Nat := none
  /-- Whether the unit being walked is a component. -/
  component : Bool := false
  startSeen : Bool := false

/-- The walker monad: the input bytes, failure with a message, the state (kept on failure, so
the lines printed before an error survive, as upstream's streaming output). -/
abbrev M := ReaderT ByteArray (ExceptT String (StateM St))

/-- Append to the pending description. -/
def stw (s : String) : M Unit := modify fun st => { st with state := st.state ++ s }

/-- Upstream's `print_`: the bytes `[cur, stop)` with the pending description. -/
def printC (stop : Nat) (color : Bool := false) : M Unit := do
  let st ← get
  unless st.cur < stop do
    throw s!"dump: {st.cur} >= {stop} while printing: {st.state} (upstream panics here)"
  set { st with cur := stop, state := "",
                lines := st.lines.push (.bytes st.nest st.cur stop st.state color) }

/-- `print`. -/
def print (stop : Nat) : M Unit := printC stop false

/-- `color_print`. -/
def cprint (stop : Nat) : M Unit := printC stop true

/-- A `---| ... msg` line standing for `[cur, stop)`; `cur := stop`. -/
def dataLine (msg : String) (stop : Nat) : M Unit :=
  modify fun st => { st with cur := stop, lines := st.lines.push (.data st.nest st.cur stop msg) }

/-- A separator line. -/
def raw (s : String) : M Unit := modify fun st => { st with lines := st.lines.push (.raw s) }

/-- Run a transcribed wasmparser reader at `p`, bounded by the current section: its value and
the offset after it. -/
def rd {α : Type} (m : R α) (p : Nat) : M (α × Nat) := do
  let st ← get
  match DumpFlat.runR m (← read) st.lim p with
  | (.ok a, q) => pure (a, q)
  | (.error e, _) => throw e

/-- The counters. -/
def ix : M Counters := do pure (← get).ix

def setIx (f : Counters → Counters) : M Unit := modify fun st => { st with ix := f st.ix }

/-- The next index of the space `dump` names `space`, counted. -/
def bump (space : String) : M Nat := do
  let i ← ix
  let (n, j) := match space with
    | "core type" => (i.types, { i with types := i.types + 1 })
    | "core func" => (i.funcs, { i with funcs := i.funcs + 1 })
    | "core table" => (i.tables, { i with tables := i.tables + 1 })
    | "core memory" => (i.memories, { i with memories := i.memories + 1 })
    | "core global" => (i.globals, { i with globals := i.globals + 1 })
    | "core tag" => (i.tags, { i with tags := i.tags + 1 })
    | "module" => (i.coreModules, { i with coreModules := i.coreModules + 1 })
    | "core instance" => (i.coreInstances, { i with coreInstances := i.coreInstances + 1 })
    | "type" => (i.cTypes, { i with cTypes := i.cTypes + 1 })
    | "func" => (i.cFuncs, { i with cFuncs := i.cFuncs + 1 })
    | "component" => (i.components, { i with components := i.components + 1 })
    | "instance" => (i.instances, { i with instances := i.instances + 1 })
    | _ => (i.values, { i with values := i.values + 1 })
  setIx fun _ => j
  pure n

/-- The flat operators of `[p, e)` (a function body), printed as upstream's `print_ops`: `??`
for an operator the reader fails on. -/
def flatOps (p e : Nat) : M Unit := do
  let b ← read
  let mut q := p
  let mut frames : List DumpFlat.Frame := [.block]
  for _ in [0:e - p + 1] do
    if q ≥ e then break
    match DumpFlat.runR (DumpFlat.opR frames) b e q with
    | (.ok (t, fs), q') => stw t; print q'; frames := fs; q := q'
    | (.error _, q') => stw "??"; print q'; q := q'

/-- The operators of a function body `[p, e)`: the certified decoder's lines if it reads
exactly the body, else the flat reader's. -/
def bodyOps (p e : Nat) : M Unit := do
  let b ← read
  match dExpr.run ⟨b, p⟩ with
  | .ok ((_, es), c) =>
    if c.pos == e then
      for x in es do
        stw x.text; print x.stop
      return
    flatOps p e
  | .error _ => flatOps p e

/-- `skip_const_expr`: the end of the constant expression at `p` (flat operators until the
outermost `end`). -/
def constEnd (p : Nat) : M Nat := do
  let b ← read
  let lim := (← get).lim
  let mut q := p
  let mut frames : List DumpFlat.Frame := [.block]
  for _ in [0:lim - p + 1] do
    if frames.isEmpty then break
    match DumpFlat.runR (DumpFlat.opR frames) b lim q with
    | (.ok (_, fs), q') => frames := fs; q := q'
    | (.error e, _) => throw e
  unless frames.isEmpty do throw "control frames remain at end of expression"
  pure q

/-- The operators of the constant expression at `p`, printed; the offset after it. -/
def ops (p : Nat) : M Nat := do
  let e ← constEnd p
  bodyOps p e
  pure e

/-! ## Sections -/

/-- `print_iter`: the count, then `n` items; `item k p` prints the item at `p` and returns the
offset after it. -/
def items (p : Nat) (item : Nat → Nat → M Nat) : M Nat := do
  let (n, p) ← rd DumpFlat.varU32 p
  stw s!"{n} count"; print p
  let mut q := p
  for k in [0:n] do
    q ← item k q
  pure q

/-- `section`: the header line (coloured), then `items`. -/
def sectionL (name : String) (q : Nat) (item : Nat → Nat → M Nat) : M Nat := do
  stw s!"{name} section"; cprint q
  items q item

def endCheck (p e : Nat) : M Unit := do
  unless p == e do
    throw s!"section size mismatch: unexpected data at the end of the section (at offset 0x{RustDebug.hexDigits p})"

/-- One recursion group of the type section. -/
def recGroup (p : Nat) : M Nat := do
  let k := (← ix).recGroups
  setIx fun i => { i with recGroups := k + 1 }
  let (b0, _) ← rd DumpFlat.peek p
  if b0 == 0x4E then
    raw s!"--- rec group {k} (explicit) ---"
    let (n, p) ← rd (DumpFlat.size 1000000 "rec group types") (p + 1)
    let mut q := p
    for _ in [0:n] do
      print q
      let (s, q') ← rd DumpFlat.subTypeR q
      let t := (← ix).types
      setIx fun i => { i with types := t + 1 }
      stw s!"[type {t}] {s}"
      q := q'
    print q
    pure q
  else
    raw s!"--- rec group {k} (implicit) ---"
    let (s, q) ← rd DumpFlat.subTypeR p
    let t := (← ix).types
    setIx fun i => { i with types := t + 1 }
    stw s!"[type {t}] {s}"
    print q
    pure q

/-- `[func N]`, `[table N]`, …: the index an import takes, counted. -/
def importIdx (kind : String) : M String := do
  let i ← ix
  match kind with
  | "func" => setIx (fun i => { i with funcs := i.funcs + 1 }); pure s!"[func {i.funcs}]"
  | "func_exact" => setIx (fun i => { i with funcs := i.funcs + 1 }); pure s!"[func_exact {i.funcs}]"
  | "table" => setIx (fun i => { i with tables := i.tables + 1 }); pure s!"[table {i.tables}]"
  | "memory" => setIx (fun i => { i with memories := i.memories + 1 }); pure s!"[memory {i.memories}]"
  | "global" => setIx (fun i => { i with globals := i.globals + 1 }); pure s!"[global {i.globals}]"
  | _ => setIx (fun i => { i with tags := i.tags + 1 }); pure s!"[tag {i.tags}]"

def importItem (_ : Nat) (p : Nat) : M Nat := do
  let (m, q) ← rd DumpFlat.str p
  let (n, q) ← rd DumpFlat.str q
  let (disc, _) ← rd DumpFlat.peek q
  if n == "" && disc == 0x7F then
    raw "--- import group (common module) ---"
    let (cnt, q) ← rd DumpFlat.varU32 (q + 1)
    stw s!"module: {RustDebug.debugStr m}, count: {cnt}"
    let mut r := q
    for _ in [0:cnt] do
      print r
      let (nm, r') ← rd DumpFlat.str r
      let ((k, ty), r') ← rd DumpFlat.typeRefR r'
      let idx ← importIdx k
      stw s!"import {idx} ImportItemCompact \{ name: {RustDebug.debugStr nm}, ty: {ty} }"
      r := r'
    print r
    pure r
  else if n == "" && disc == 0x7E then
    raw "--- import group (common module and type) ---"
    let ((k, ty), q) ← rd DumpFlat.typeRefR (q + 1)
    let (cnt, q) ← rd DumpFlat.varU32 q
    stw s!"module: {RustDebug.debugStr m}, type: {ty}, count: {cnt}"
    let mut r := q
    for _ in [0:cnt] do
      print r
      let (nm, r') ← rd DumpFlat.str r
      let idx ← importIdx k
      stw s!"import {idx} {RustDebug.debugStr nm}"
      r := r'
    print r
    pure r
  else
    let ((k, ty), q) ← rd DumpFlat.typeRefR q
    let idx ← importIdx k
    stw s!"import {idx} Import \{ module: {RustDebug.debugStr m}, name: {RustDebug.debugStr n}, ty: {ty} }"
    print q
    pure q

/-- `ConstExpr`'s `Debug`: its offset and its bytes (the final `end` included). -/
def constExprDbg (b : ByteArray) (p q : Nat) : String :=
  s!"ConstExpr \{ offset: {p}, data: " ++ listDbg ((b.extract p q).toList.map (·.toNat)) ++ " }"

def tableItem (_ : Nat) (p : Nat) : M Nat := do
  let b ← read
  let n := (← ix).tables
  setIx fun i => { i with tables := n + 1 }
  let (b0, _) ← rd DumpFlat.peek p
  if b0 == 0x40 then
    let (z, _) ← rd DumpFlat.u8 (p + 1)
    unless z == 0 do throw "invalid table encoding"
    let (t, e0) ← rd DumpFlat.tableTypeR (p + 2)
    let q ← constEnd e0
    stw s!"[table {n}] Table \{ ty: {t}, init: Expr({constExprDbg b e0 q}) }"
    print q; pure q
  else
    let (t, q) ← rd DumpFlat.tableTypeR p
    stw s!"[table {n}] Table \{ ty: {t}, init: RefNull }"
    print q; pure q

def memoryItem (_ : Nat) (p : Nat) : M Nat := do
  let (t, q) ← rd DumpFlat.memTypeR p
  let n := (← ix).memories
  setIx fun i => { i with memories := n + 1 }
  stw s!"[memory {n}] {t}"; print q; pure q

def tagItem (_ : Nat) (p : Nat) : M Nat := do
  let (t, q) ← rd DumpFlat.tagTypeR p
  let n := (← ix).tags
  setIx fun i => { i with tags := n + 1 }
  stw s!"[tag {n}] {t}"; print q; pure q

def globalItem (_ : Nat) (p : Nat) : M Nat := do
  let (t, e0) ← rd DumpFlat.globalTypeR p
  let _ ← constEnd e0
  let n := (← ix).globals
  setIx fun i => { i with globals := n + 1 }
  stw s!"[global {n}] {t}"; print e0
  ops e0

def exportItem (_ : Nat) (p : Nat) : M Nat := do
  let (nm, q) ← rd DumpFlat.str p
  let (k, q) ← rd DumpFlat.exportKindR q
  let (i, q) ← rd DumpFlat.varU32 q
  stw s!"export Export \{ name: {RustDebug.debugStr nm}, kind: {k}, index: {i} }"
  print q; pure q

/-- The items of an element segment: function indices, or expressions of type `ty`. -/
def elemItems (p : Nat) (ty : Option String) : M Nat := do
  let (n, p) ← rd DumpFlat.varU32 p
  match ty with
  | none => stw " [indices]"
  | some t => stw s!" [exprs {t}]"
  print p
  let mut q := p
  for _ in [0:n] do
    match ty with
    | none =>
      let (x, q') ← rd DumpFlat.varU32 q
      stw s!"item {x}"; print q'; q := q'
    | some _ =>
      let q' ← constEnd q
      stw s!"item {constExprDbg (← read) q q'}"; print q'; q := q'
  pure q

/-- The item count of an element segment's vector at `p` (not consumed). -/
def peekCount (p : Nat) : M Nat := do pure (← rd DumpFlat.varU32 p).1

def elemKind (p : Nat) : M Unit := do
  let (k, _) ← rd DumpFlat.u8 p
  unless k == 0 do throw s!"invalid leading byte (0x{RustDebug.hexDigits k}) for external kind"

def elemItem (_ : Nat) (p : Nat) : M Nat := do
  let (flags, p) ← rd DumpFlat.varU32 p
  if flags > 7 then throw "invalid flags byte in element segment"
  stw "element"
  match flags with
  | 0 => do
    stw " table[None]"; print p
    let p ← ops p
    stw s!"{← peekCount p} items"; elemItems p none
  | 1 => do
    elemKind p
    stw s!" passive, {← peekCount (p + 1)} items"; elemItems (p + 1) none
  | 2 => do
    let (x, p) ← rd DumpFlat.varU32 p
    stw s!" table[Some({x})]"; print p
    let p ← ops p
    elemKind p
    stw s!"{← peekCount (p + 1)} items"; elemItems (p + 1) none
  | 3 => do
    elemKind p
    stw s!" declared {← peekCount (p + 1)} items"; elemItems (p + 1) none
  | 4 => do
    stw " table[None]"; print p
    let p ← ops p
    stw s!"{← peekCount p} items"; elemItems p (some "funcref")
  | 5 => do
    let (t, p) ← rd DumpFlat.refR p
    stw s!" passive, {← peekCount p} items"; elemItems p (some t.dbg)
  | 6 => do
    let (x, p) ← rd DumpFlat.varU32 p
    stw s!" table[Some({x})]"; print p
    let p ← ops p
    let (t, p) ← rd DumpFlat.refR p
    stw s!"{← peekCount p} items"; elemItems p (some t.dbg)
  | _ => do
    let (t, p) ← rd DumpFlat.refR p
    stw s!" declared {← peekCount p} items"; elemItems p (some t.dbg)

def dataItem (_ : Nat) (p : Nat) : M Nat := do
  let (flags, p1) ← rd DumpFlat.varU32 p
  let (p, head) ← match flags with
    | 0 => do pure (p1, "data memory[0]")
    | 1 => do pure (p1, "data passive")
    | 2 => do let (x, q) ← rd DumpFlat.varU32 p1; pure (q, s!"data memory[{x}]")
    | _ => throw "invalid flags byte in data segment"
  if flags == 1 then
    let (n, q) ← rd DumpFlat.varU32 p
    let _ ← rd (DumpFlat.bytes n) q
    stw head; print q
    dataLine s!"{n} bytes of data" (q + n)
    pure (q + n)
  else
    let e0 ← constEnd p
    let (n, q) ← rd DumpFlat.varU32 e0
    let _ ← rd (DumpFlat.bytes n) q
    stw head; print p
    let _ ← ops p
    dataLine s!"{n} bytes of data" (q + n)
    pure (q + n)

def funcItem (base : Nat) (k : Nat) (p : Nat) : M Nat := do
  let (t, q) ← rd DumpFlat.varU32 p
  stw s!"[func {base + k}] type {t}"; print q; pure q

/-- One function body. -/
def codeItem (_ : Nat) (p : Nat) : M Nat := do
  let (size, p) ← rd DumpFlat.varU32 p
  let e := p + size
  unless e ≤ (← get).lim do throw "unexpected end-of-file"
  let n := (← ix).funcs
  setIx fun i => { i with funcs := n + 1 }
  raw s!"============== func {n} ===================="
  stw "size of function"; print p
  let saved := (← get).lim
  modify fun st => { st with lim := e }
  let (g, q0) ← rd DumpFlat.varU32 p
  stw s!"{g} local blocks"; print q0
  let mut q := q0
  let mut total := 0
  for _ in [0:g] do
    let (amt, q') ← rd DumpFlat.varU32 q
    total := total + amt
    if total > 50000 then throw "too many locals"
    let (t, q') ← rd DumpFlat.valR q'
    stw s!"{amt} locals of type {t.dbg}"; print q'
    q := q'
  bodyOps q e
  modify fun st => { st with lim := saved }
  pure e

/-! ## Custom sections -/

/-- `print_name_map`: `{thing} name section`, then the namings. -/
def nameMap (thing : String) (p : Nat) : M Nat := do
  stw s!"{thing} name section"; cprint p
  items p fun _ q => do
    let (i, q) ← rd DumpFlat.varU32 q
    let (s, q) ← rd DumpFlat.str q
    stw s!"Naming \{ index: {i}, name: {RustDebug.debugStr s} }"; print q; pure q

/-- `print_indirect_name_map`. -/
def indirectNameMap (a b : String) (p : Nat) : M Nat := do
  stw s!"{b} section"; cprint p
  items p fun _ q => do
    -- `IndirectNaming::from_reader` reads the whole inner map before anything is printed
    let _ ← rd (do
      let _ ← DumpFlat.varU32
      let n ← DumpFlat.varU32
      for _ in [0:n] do
        let _ ← DumpFlat.varU32; let _ ← DumpFlat.str
      pure ()) q
    let (i, q) ← rd DumpFlat.varU32 q
    stw s!"{a} {i} "
    nameMap b q

/-- A try-block for the walker: run `act`; on failure, the message (the state is kept). -/
def attempt (act : M Unit) : M (Option String) := do
  try act; pure none
  catch e => pure (some e)

/-- `print_subsections`: the subsections (`id`, `size`, contents) in `[p, e)`, each printed by
`f id s t`. A subsection that fails to read or print ends the list with upstream's
`failed to decode N more bytes: …` line. -/
def subsections (p e : Nat) (f : Nat → Nat → Nat → M Unit) : M Unit := do
  let b ← read
  let mut p := p
  for _ in [0:e - p + 1] do
    if p ≥ e then break
    let hdr := DumpFlat.runR (do
      let id ← DumpFlat.u8
      if id ≥ 0x80 then DumpFlat.bailAt "invalid u7" ((← get) - 1)
      let size ← DumpFlat.varU32
      let s ← get
      let _ ← DumpFlat.bytes size
      pure (id, s, s + size)) b e p
    let (err, pos) ← match hdr with
      | (.error msg, q) => pure (some msg, q)
      | (.ok (id, s, t), _) => do
        let saved := (← get).lim
        modify fun st => { st with lim := t }
        let r ← attempt (f id s t)
        modify fun st => { st with lim := saved }
        pure (r, t)
    match err with
    | none => p := pos
    | some msg =>
      let st ← get
      if st.cur != pos then
        if st.state.isEmpty then stw "???"
        print pos
      dataLine s!"failed to decode {e - pos} more bytes: {msg}" e
      break

/-- One subsection of the `name` section. -/
def nameSub (id s t : Nat) : M Unit := do
  match id with
  | 0 => do
    stw "module name"; print s
    let (nm, q) ← rd DumpFlat.str s
    unless q == t do throw "trailing data at the end of a name"
    stw (RustDebug.debugStr nm); print t
  | 1 => endCheck (← nameMap "function" s) t
  | 2 => endCheck (← indirectNameMap "function" "local" s) t
  | 3 => endCheck (← indirectNameMap "function" "label" s) t
  | 4 => endCheck (← nameMap "type" s) t
  | 5 => endCheck (← nameMap "table" s) t
  | 6 => endCheck (← nameMap "memory" s) t
  | 7 => endCheck (← nameMap "global" s) t
  | 8 => endCheck (← nameMap "element" s) t
  | 9 => endCheck (← nameMap "data" s) t
  | 10 => endCheck (← indirectNameMap "type" "field" s) t
  | 11 => endCheck (← nameMap "tag" s) t
  | 12 => endCheck (← indirectNameMap "func" "param" s) t
  | 13 => endCheck (← indirectNameMap "tag" "param" s) t
  | n => do
    stw s!"unknown names: {n}"; print s
    print t

/-- The `producers` section from `p`. -/
def producers (p : Nat) : M Nat :=
  items p fun _ q => do
    let (nm, q) ← rd (do
      let o ← get
      let nm ← DumpFlat.ustr
      unless nm == "language" || nm == "sdk" || nm == "processed-by" do
        DumpFlat.bailAt s!"invalid producers field name: `{nm}`" o
      pure nm) q
    stw s!"field: {nm}"; print q
    items q fun _ r => do
      let (n, r) ← rd DumpFlat.ustr r
      let (v, r) ← rd DumpFlat.ustr r
      stw s!"ProducersFieldValue \{ name: {RustDebug.debugStr n}, version: {RustDebug.debugStr v} }"
      print r; pure r

/-- `metadata.code.branch_hint`: per function, its hints. -/
def branchHints (p : Nat) : M Nat :=
  items p fun _ q => do
    let (f, q) ← rd DumpFlat.varU32 q
    stw s!"func: {f}"; print q
    items q fun _ r => do
      let (off, r) ← rd DumpFlat.varU32 r
      let (one, r) ← rd DumpFlat.u8 r
      unless one == 1 do throw "invalid branch hint byte"
      let (t, r) ← rd DumpFlat.u8 r
      let taken ← match t with
        | 0 => pure "false" | 1 => pure "true" | _ => throw "invalid branch hint taken byte"
      stw s!"BranchHint \{ func_offset: {off}, taken: {taken} }"; print r; pure r

/-- `SymbolFlags`' `Debug` (bitflags 2: the names of the set flags, then unknown bits). -/
def symbolFlagsDbg (n : Nat) : String :=
  let names : List (Nat × String) :=
    [(1, "BINDING_WEAK"), (2, "BINDING_LOCAL"), (4, "VISIBILITY_HIDDEN"), (16, "UNDEFINED"),
     (32, "EXPORTED"), (64, "EXPLICIT_NAME"), (128, "NO_STRIP"), (256, "TLS"), (512, "ABSOLUTE")]
  let set := names.filter fun (bit, _) => n / bit % 2 == 1
  let known := set.foldl (fun acc (bit, _) => acc + bit) 0
  let parts := set.map (·.2) ++
    (if n - known != 0 then ["0x" ++ RustDebug.hexDigits (n - known)] else [])
  if parts.isEmpty then "SymbolFlags(0x0)" else "SymbolFlags(" ++ " | ".intercalate parts ++ ")"

def strListDbg (xs : List String) : String :=
  "[" ++ ", ".intercalate (xs.map RustDebug.debugStr) ++ "]"

/-- One `dylink.0` subsection with id `id` and contents `[s, t)`. -/
def dylinkSub (id s t : Nat) : M Unit := do
  let text ← match id with
    | 1 => do
      let ((a, b, c, d), _) ← rd (do
        let a ← DumpFlat.varU32; let b ← DumpFlat.varU32; let c ← DumpFlat.varU32
        let d ← DumpFlat.varU32; pure (a, b, c, d)) s
      pure s!"MemInfo(MemInfo \{ memory_size: {a}, memory_alignment: {b}, table_size: {c}, table_alignment: {d} })"
    | 2 => do
      let (xs, _) ← rd (do let n ← DumpFlat.varU32; (List.range n).mapM fun _ => DumpFlat.ustr) s
      pure s!"Needed({strListDbg xs})"
    | 3 => do
      let (xs, _) ← rd (do
        let n ← DumpFlat.varU32
        (List.range n).mapM fun _ => do
          let nm ← DumpFlat.ustr; let f ← DumpFlat.varU32
          pure s!"ExportInfo \{ name: {RustDebug.debugStr nm}, flags: {symbolFlagsDbg f} }") s
      pure ("ExportInfo([" ++ ", ".intercalate xs ++ "])")
    | 4 => do
      let (xs, _) ← rd (do
        let n ← DumpFlat.varU32
        (List.range n).mapM fun _ => do
          let m ← DumpFlat.ustr; let fld ← DumpFlat.ustr; let f ← DumpFlat.varU32
          pure (s!"ImportInfo \{ module: {RustDebug.debugStr m}, field: " ++
            s!"{RustDebug.debugStr fld}, flags: {symbolFlagsDbg f} }")) s
      pure ("ImportInfo([" ++ ", ".intercalate xs ++ "])")
    | 5 => do
      let (xs, _) ← rd (do let n ← DumpFlat.varU32; (List.range n).mapM fun _ => DumpFlat.ustr) s
      pure s!"RuntimePath({strListDbg xs})"
    | 6 => do
      let (a, _) ← rd DumpFlat.ustr s
      pure s!"TargetArch({RustDebug.debugStr a})"
    | ty => do
      let b ← read
      pure (s!"Unknown \{ ty: {ty}, data: " ++ listDbg ((b.extract s t).toList.map (·.toNat)) ++
        s!", range: {s}..{t} }")
  stw text; print t

/-- `SegmentFlags`' `Debug`. -/
def segmentFlagsDbg (n : Nat) : String :=
  let names : List (Nat × String) := [(1, "STRINGS"), (2, "TLS")]
  let set := names.filter fun (bit, _) => n / bit % 2 == 1
  let known := set.foldl (fun acc (bit, _) => acc + bit) 0
  let parts := set.map (·.2) ++
    (if n - known != 0 then ["0x" ++ RustDebug.hexDigits (n - known)] else [])
  if parts.isEmpty then "SegmentFlags(0x0)" else "SegmentFlags(" ++ " | ".intercalate parts ++ ")"

def optStrDbg : Option String → String
  | none => "None"
  | some s => s!"Some({RustDebug.debugStr s})"

/-- `SymbolInfo`'s `Debug`, read. -/
def symbolR : R String := do
  let o ← get
  let kind ← DumpFlat.u8
  let flags ← DumpFlat.varU32
  let defined := flags / 16 % 2 == 0
  let explicitName := flags / 64 % 2 == 1
  let fl := symbolFlagsDbg flags
  match kind with
  | 0 | 2 | 4 | 5 => do
    let i ← DumpFlat.varU32
    let nm ← if defined || explicitName then do pure (some (← DumpFlat.ustr)) else pure none
    let k := match kind with | 0 => "Func" | 2 => "Global" | 4 => "Event" | _ => "Table"
    pure s!"{k} \{ flags: {fl}, index: {i}, name: {optStrDbg nm} }"
  | 1 => do
    let nm ← DumpFlat.ustr
    let sym ← if defined then do
        let i ← DumpFlat.varU32; let off ← DumpFlat.varU32; let sz ← DumpFlat.varU32
        pure s!"Some(DefinedDataSymbol \{ index: {i}, offset: {off}, size: {sz} })"
      else pure "None"
    pure s!"Data \{ flags: {fl}, name: {RustDebug.debugStr nm}, symbol: {sym} }"
  | 3 => do pure s!"Section \{ flags: {fl}, section: {← DumpFlat.varU32} }"
  | k => DumpFlat.bailAt s!"invalid leading byte (0x{RustDebug.hexDigits k}) for symbol kind" o

/-- One `linking` subsection with id `id` and contents `[s, t)`. -/
def linkingSub (id s t : Nat) : M Unit := do
  let mapped (name : String) (item : R String) : M Unit := do
    let e ← sectionL name s fun _ q => do
      let (x, q) ← rd item q
      stw x; print q; pure q
    endCheck e t
  match id with
  | 5 => mapped "segment info" (do
      let nm ← DumpFlat.ustr; let al ← DumpFlat.varU32; let fl ← DumpFlat.varU32
      pure s!"Segment \{ name: {RustDebug.debugStr nm}, alignment: {al}, flags: {segmentFlagsDbg fl} }")
  | 6 => mapped "init funcs" (do
      let pr ← DumpFlat.varU32; let si ← DumpFlat.varU32
      pure s!"InitFunc \{ priority: {pr}, symbol_index: {si} }")
  | 8 => mapped "symbol table" symbolR
  | 9 => do
    let (a, _) ← rd DumpFlat.str s
    stw s!"target arch: {RustDebug.debugStr a}"; print t
  | 7 => throw "dump: comdat info subsections are not supported (see tools/wasm-tools/README.md)"
  | n => do
    stw s!"unknown subsection: {n}"; print s
    print t

/-- The relocation types (`RelocationType`) and their addend widths (0, 32, 64). -/
def relocType : Nat → Option (String × Nat)
  | 0 => some ("FunctionIndexLeb", 0) | 1 => some ("TableIndexSleb", 0)
  | 2 => some ("TableIndexI32", 0) | 3 => some ("MemoryAddrLeb", 32)
  | 4 => some ("MemoryAddrSleb", 32) | 5 => some ("MemoryAddrI32", 32)
  | 6 => some ("TypeIndexLeb", 0) | 7 => some ("GlobalIndexLeb", 0)
  | 8 => some ("FunctionOffsetI32", 32) | 9 => some ("SectionOffsetI32", 32)
  | 10 => some ("EventIndexLeb", 0) | 11 => some ("MemoryAddrRelSleb", 32)
  | 12 => some ("TableIndexRelSleb", 0) | 13 => some ("GlobalIndexI32", 0)
  | 14 => some ("MemoryAddrLeb64", 64) | 15 => some ("MemoryAddrSleb64", 64)
  | 16 => some ("MemoryAddrI64", 64) | 17 => some ("MemoryAddrRelSleb64", 64)
  | 18 => some ("TableIndexSleb64", 0) | 19 => some ("TableIndexI64", 0)
  | 20 => some ("TableNumberLeb", 0) | 21 => some ("MemoryAddrTlsSleb", 32)
  | 22 => some ("FunctionOffsetI64", 64) | 23 => some ("MemoryAddrLocrelI32", 32)
  | 24 => some ("TableIndexRelSleb64", 0) | 25 => some ("MemoryAddrTlsSleb64", 64)
  | 26 => some ("FunctionIndexI32", 0)
  | _ => none

def relocR : R String := do
  let t ← DumpFlat.u8
  let (name, w) ← match relocType t with
    | some x => pure x
    | none => DumpFlat.bailAt s!"invalid leading byte (0x{RustDebug.hexDigits t}) for RelocEntryType" ((← get) - 1)
  let off ← DumpFlat.varU32
  let i ← DumpFlat.varU32
  let add ← if w == 32 then DumpFlat.varS32 else if w == 64 then DumpFlat.varS64 else pure 0
  pure s!"RelocationEntry \{ ty: {name}, offset: {off}, index: {i}, addend: {add} }"

def custom (q e : Nat) : M Unit := do
  stw "custom section"; cprint q
  let (nm, p) ← rd DumpFlat.str q
  stw s!"name: {RustDebug.debugStr nm}"; print p
  let b ← read
  -- `as_known`: a reader whose constructor fails is an unknown section
  let countOk := (DumpFlat.runR DumpFlat.varU32 b e p).1 matches .ok _
  let linkVer := DumpFlat.runR DumpFlat.varU32 b e p
  let unknown := dataLine s!"{e - p} bytes of data" e
  if nm == "name" then subsections p e nameSub
  else if nm == "producers" then
    if countOk then endCheck (← producers p) e else unknown
  else if nm == "metadata.code.branch_hint" then
    if countOk then endCheck (← branchHints p) e else unknown
  else if nm == "dylink.0" then subsections p e dylinkSub
  else if nm == "linking" then
    match linkVer with
    | (.ok 2, q) => do
      stw "linking version 2"; print q
      subsections q e linkingSub
    | _ => unknown
  else if nm.startsWith "reloc." then
    match linkVer with
    | (.ok idx, q) => do
      stw s!"section {idx}"; print q
      endCheck (← items q fun _ r => do
        let (x, r) ← rd relocR r
        stw x; print r; pure r) e
    | _ => unknown
  else unknown

/-! ## The module -/

/-- One section with id `id` whose contents are `[q, e)`. -/
def sectionAt (id q e : Nat) : M Unit := do
  match id with
  | 0 => custom q e
  | 1 => endCheck (← sectionL "type" q fun _ p => recGroup p) e
  | 2 => endCheck (← sectionL "import" q importItem) e
  | 3 => do
    let base := (← ix).funcs
    endCheck (← sectionL "func" q (funcItem base)) e
  | 4 => endCheck (← sectionL "table" q tableItem) e
  | 5 => endCheck (← sectionL "memory" q memoryItem) e
  | 13 => endCheck (← sectionL "tag" q tagItem) e
  | 6 => endCheck (← sectionL "global" q globalItem) e
  | 7 => endCheck (← sectionL "export" q exportItem) e
  | 8 => do
    let (f, p) ← rd DumpFlat.varU32 q
    unless p == e do throw "unexpected content in the start section"
    stw "start section"; cprint q
    stw s!"start function {f}"; print e
  | 12 => do
    let (n, p) ← rd DumpFlat.varU32 q
    unless p == e do throw "unexpected content in the data count section"
    stw "data count section"; cprint q
    stw s!"data count {n}"; print e
  | 9 => endCheck (← sectionL "element" q elemItem) e
  | 10 => do
    let (n, p) ← rd DumpFlat.varU32 q
    stw "code section"; cprint q
    stw s!"{n} count"; print p
    let mut r := p
    for k in [0:n] do
      r ← codeItem k r
    unless r == e do throw "trailing bytes at end of section"
  | 11 => endCheck (← sectionL "data" q dataItem) e
  | n => do
    stw s!"unknown section: {n}"; cprint q
    dataLine s!"{e - q} bytes of data" e

/-- The rank of a section id in wasmparser's `Order` (0: not ordered). -/
def orderRank : Nat → Nat
  | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 13 => 6 | 6 => 7 | 7 => 8 | 8 => 9
  | 9 => 10 | 12 => 11 | 10 => 12 | 11 => 13
  | _ => 0

/-- `check_function_code_counts`. -/
def checkFuncCode : M Unit := do
  let st ← get
  match st.funcEntries, st.codeEntries with
  | some n, some m => unless n == m do throw "function and code section have inconsistent lengths"
  | some n, none => unless n == 0 do
      throw "function section has non-zero count but code section is absent"
  | none, some m => unless m == 0 do
      throw "function section is absent but code section has non-zero count"
  | none, none => pure ()

/-- `check_data_count`. -/
def checkDataCount : M Unit := do
  let st ← get
  match st.dataCount, st.dataEntries with
  | some n, some m => unless n == m do throw "data count and data section have inconsistent lengths"
  | some n, none => unless n == 0 do throw "data count is non-zero but data section is absent"
  | _, _ => pure ()

/-- The checks wasmparser's `Parser` makes before it hands a section over: the order of the
sections and the function/code and data-count/data counts. -/
def preSection (id q : Nat) : M Unit := do
  let r := orderRank id
  if r > 0 then
    if (← get).order ≥ r then throw "section out of order"
    modify fun st => { st with order := r }
  match id with
  | 3 => do let (n, _) ← rd DumpFlat.varU32 q; modify fun st => { st with funcEntries := some n }
  | 10 => do
    let (n, _) ← rd DumpFlat.varU32 q
    modify fun st => { st with codeEntries := some n }
    checkFuncCode
  | 12 => do let (n, _) ← rd DumpFlat.varU32 q; modify fun st => { st with dataCount := some n }
  | 11 => do
    let (n, _) ← rd DumpFlat.varU32 q
    modify fun st => { st with dataEntries := some n }
    checkDataCount
  | _ => pure ()

/-! ## Components -/

/-- One item of a component section, printed: `[space N] text`. -/
def numbered (space text : String) (q : Nat) : M Nat := do
  stw s!"[{space} {← bump space}] {text}"; print q; pure q

/-- `print_component_name`: one subsection of a `component-name` section. -/
def compNameSub (id s t : Nat) : M Unit := do
  match id with
  | 0 => do
    stw "component name"; print s
    let (nm, q) ← rd DumpFlat.ustr s
    unless q == t do throw "trailing data at the end of a name"
    stw (RustDebug.debugStr nm); print t
  | 1 => do
    let (b1, q) ← rd DumpFlat.u8 s
    let (thing, q) ← if b1 == 0 then do
        let (b2, q) ← rd DumpFlat.u8 q
        pure ((match b2 with
          | 0x00 => some "core func" | 0x01 => some "core table" | 0x02 => some "core memory"
          | 0x03 => some "core global" | 0x04 => some "core tag" | 0x10 => some "core type"
          | 0x11 => some "core module" | 0x12 => some "core instance" | _ => none), q)
      else pure ((match b1 with
          | 0x01 => some "func" | 0x02 => some "value" | 0x03 => some "type"
          | 0x04 => some "component" | 0x05 => some "instance" | _ => none), q)
    match thing with
    | some th => endCheck (← nameMap th q) t
    | none => do
      stw "unknown names: 1"; print q
      print t
  | n => do
    stw s!"unknown names: {n}"; print s
    print t

/-- One section of a component (other than nested modules and components). -/
def compSectionAt (id q e : Nat) : M Unit := do
  match id with
  | 0 => do
    -- `component-name` is a component custom section; the rest as for modules
    let (nm, p) ← rd DumpFlat.str q
    if nm == "component-name" then
      stw "custom section"; cprint q
      stw s!"name: {RustDebug.debugStr nm}"; print p
      subsections p e compNameSub
    else custom q e
  | 2 => endCheck (← sectionL "core instance" q fun _ p => do
      let (x, p) ← rd DumpComp.coreInstanceR p; numbered "core instance" x p) e
  | 3 => endCheck (← sectionL "core type" q fun _ p => do
      let (x, p) ← rd DumpComp.coreTypeR p; numbered "core type" x p) e
  | 5 => endCheck (← sectionL "component instance" q fun _ p => do
      let (x, p) ← rd DumpComp.instanceR p; numbered "instance" x p) e
  | 6 => endCheck (← sectionL "component alias" q fun _ p => do
      let ((x, space), p) ← rd DumpComp.aliasR p
      stw s!"alias [{space} {← bump space}] {x}"; print p; pure p) e
  | 7 => endCheck (← sectionL "component type" q fun _ p => do
      let (x, p) ← rd DumpComp.componentTypeR p; numbered "type" x p) e
  | 8 => endCheck (← sectionL "canonical function" q fun _ p => do
      let ((x, lift), p) ← rd DumpComp.canonR p
      numbered (if lift then "func" else "core func") x p) e
  | 9 => do
    if (← get).startSeen then throw "component cannot have more than one start function"
    modify fun st => { st with startSeen := true }
    let (x, p) ← rd DumpComp.startR q
    unless p == e do throw "unexpected content in the component start section"
    stw "start section"; print q
    stw x; print e
  | 10 => endCheck (← sectionL "component import" q fun _ p => do
      let ((x, space), p) ← rd DumpComp.importR p
      let space := if space == "module" then "module" else space
      stw s!"[{space} {← bump space}] {x}"; print p; pure p) e
  | 11 => endCheck (← sectionL "component export" q fun _ p => do
      let (x, p) ← rd DumpComp.exportR p
      stw s!"export {x}"; print p; pure p) e
  | n => do
    stw s!"unknown section: {n}"; cprint q
    dataLine s!"{e - q} bytes of data" e

/-- The parser state of a unit, saved around a nested one. -/
structure Saved where
  ix : Counters
  order : Nat
  funcEntries : Option Nat
  codeEntries : Option Nat
  dataCount : Option Nat
  dataEntries : Option Nat
  component : Bool
  startSeen : Bool

def save : M Saved := do
  let st ← get
  pure ⟨st.ix, st.order, st.funcEntries, st.codeEntries, st.dataCount, st.dataEntries,
    st.component, st.startSeen⟩

def restore (s : Saved) : M Unit := modify fun st =>
  { st with ix := s.ix, order := s.order, funcEntries := s.funcEntries,
            codeEntries := s.codeEntries, dataCount := s.dataCount, dataEntries := s.dataEntries,
            component := s.component, startSeen := s.startSeen }

/-- Walk a module or component at `[start, stop)` (`expect`: the encoding a nested section
requires, `none` at the top). -/
def walkUnit : Nat → Nat → Nat → Option Bool → M Unit
  | 0, _, _, _ => throw "dump: nesting too deep"
  | fuel + 1, start, stop, expect => do
    let b ← read
    modify fun st => { st with lim := stop, order := 0, funcEntries := none }
    modify fun st => { st with codeEntries := none, dataCount := none, dataEntries := none }
    modify fun st => { st with startSeen := false, ix := default }
    let byte (i : Nat) : Option UInt8 := if start + i < stop then b[start + i]? else none
    unless byte 0 == some 0 && byte 1 == some 0x61 && byte 2 == some 0x73 && byte 3 == some 0x6d do
      throw "magic header not detected: bad magic number"
    let comp ← if byte 4 == some 1 && byte 5 == some 0 && byte 6 == some 0 && byte 7 == some 0 then
        pure false
      else if byte 4 == some 0x0d && byte 5 == some 0 && byte 6 == some 1 && byte 7 == some 0 then
        pure true
      else throw "unknown binary version"
    if expect == some true && !comp then throw "expected a version header for a component"
    if expect == some false && comp then throw "expected a version header for a module"
    modify fun st => { st with component := comp }
    stw (if comp then "version 13 (Component)" else "version 1 (Module)"); cprint (start + 8)
    let mut p := start + 8
    for _ in [0:stop - start] do
      if p ≥ stop then break
      if byte (p - start) == some 0 && byte (p - start + 1) == some 0x61 &&
          byte (p - start + 2) == some 0x73 && byte (p - start + 3) == some 0x6d then
        throw "expected section, got wasm magic number"
      modify fun st => { st with lim := stop }
      let (id, q) ← rd DumpFlat.u8 p
      if id ≥ 0x80 then throw "malformed section id"
      let (size, q) ← rd DumpFlat.varU32 q
      let e := q + size
      unless e ≤ stop do throw s!"section too large, {size} goes past 0x{RustDebug.hexDigits stop}"
      if comp && (id == 1 || id == 4) then
        let label := if id == 1 then "core module" else "component"
        let k ← bump (if id == 1 then "module" else "component")
        stw s!"[{label} {k}] inline size"
        print q
        let sv ← save
        modify fun st => { st with nest := st.nest + 1 }
        walkUnit fuel q e (some (id == 4))
        modify fun st => { st with nest := st.nest - 1 }
        restore sv
      else
        if !comp then preSection id q
        modify fun st => { st with lim := e }
        if comp then compSectionAt id q e else sectionAt id q e
      unless (← get).cur == e do throw s!"dump: section ending at {e} not fully printed"
      p := e
    if !comp then
      checkFuncCode
      checkDataCount

/-- The whole walk. -/
def walk : M Unit := do
  let b ← read
  walkUnit (b.size + 1) 0 b.size none

/-! ## Rendering -/

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def hex2 (x : UInt8) : String :=
  let h := hex x.toNat
  if h.length < 2 then "0" ++ h else h

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- `print_byte_header`: indentation, then `{:#w$x} |` with `w = width + 2`. -/
def header (width nest at_ : Nat) : String :=
  let o := "0x" ++ hex at_
  String.join (List.replicate (nest - 1) "  ") ++ spaces (width + 2 - o.length) ++ o ++ " |"

/-- The rows of four bytes. -/
def chunks4 : List UInt8 → List (List UInt8)
  | a :: b :: c :: d :: rest => [a, b, c, d] :: chunks4 rest
  | [] => []
  | xs => [xs]

def row (xs : List UInt8) : String :=
  String.join (xs.map (" " ++ hex2 ·)) ++ spaces (3 * (4 - xs.length))

/-- The text of a line (with its newlines). `color`: the output is coloured (ANSI). -/
def renderLine (b : ByteArray) (width : Nat) (color : Bool) : Line → String
  | .raw s => s ++ "\n"
  | .data nest s _ msg => header width nest s ++ "-------------| ... " ++ msg ++ "\n"
  | .bytes nest s t text c =>
    match chunks4 (b.extract s t).toList with
    | [] => ""
    | first :: rest =>
      header width nest s ++ row first ++ " | " ++
        (if color && c then "\x1b[0m\x1b[32m" else "") ++ text ++ (if color then "\x1b[0m" else "") ++
        "\n" ++
        String.join (rest.map fun r =>
          String.join (List.replicate (nest - 1) "  ") ++ spaces width ++ "   |" ++ row r ++ "\n")

/-- The offset column width of upstream: `len(format!("{:x}", size)) + 1`. -/
def width (b : ByteArray) : Nat := (hex b.size).length + 1

/-- The input offsets a line stands for. -/
def Line.offsets : Line → List Nat
  | .raw _ => []
  | .bytes _ s t _ _ => List.range' s (t - s)
  | .data _ s t _ => List.range' s (t - s)

/-- The lines, read from offset `c`, cover `[c, n)` contiguously, in order, each byte line
non-empty. -/
def tilesFrom : List Line → Nat → Nat → Bool
  | [], c, n => c == n
  | .raw _ :: ls, c, n => tilesFrom ls c n
  | .bytes _ s t _ _ :: ls, c, n => s == c && s < t && tilesFrom ls t n
  | .data _ s t _ :: ls, c, n => s == c && s ≤ t && tilesFrom ls t n

/-- The lines of a dump, and the error that stopped the walk, if any. A successful walk is
also checked to tile the input (`Thms.dump_tiles`). -/
def dumpLines (b : ByteArray) : Array Line × Option String :=
  match (walk.run b).run.run {} with
  | (.ok (), st) =>
    if tilesFrom st.lines.toList 0 b.size then (st.lines, none)
    else (st.lines, some "dump: internal error: the lines do not tile the input")
  | (.error e, st) => (st.lines, some e)

/-- `wasm-tools dump`: the text, and the error if any. -/
def dump (b : ByteArray) (color : Bool := false) : String × Option String :=
  let (ls, err) := dumpLines b
  let w := width b
  (String.join (ls.toList.map (renderLine b w color)), err)

end Silmaril.Wasm.Tools.Dump
