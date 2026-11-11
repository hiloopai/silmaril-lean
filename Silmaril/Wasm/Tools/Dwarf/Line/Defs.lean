module

public import Silmaril.Wasm.Tools.Dwarf.Read.Defs

/-!
# DWARF line number programs (`.debug_line`, DWARF 2–5)

What addr2line 0.27 (`Lines::parse`, over gimli 0.34's `LineProgramHeader::parse` and
`LineRows`) makes of a line number program:

* `parseHeader`: the header (DWARF §6.2.4): unit length (32- or 64-bit), version 2–5,
  (v5) address and segment selector sizes, header length, minimum instruction length (not 0),
  (v4+) maximum operations per instruction (not 0), `default_is_stmt`, `line_base`,
  `line_range` (not 0), `opcode_base` (not 0), the standard opcode lengths; then the include
  directories and file names: null-terminated lists (v2–4) or entry formats and counted entries
  (v5, forms `string`, `line_strp`, `strp`, `strx*`, `udata`, `data1`/`2`/`4`/`8`/`16`, `block`);
* `rows`: the state machine (§6.2.5): special opcodes, the standard opcodes 1–12 (others skipped
  by their declared operand count), the extended opcodes `end_sequence`, `set_address`,
  `define_file`, `set_discriminator` (others skipped); addresses advance with gimli's checked
  `add_sized`, lines with its saturating decrement; a `set_address` that goes backwards or to a
  tombstone (`≥ 2^(8·size) − 2`) suppresses rows until the end of the sequence;
* `Lines`: rows grouped in sequences (`start < end` kept, sorted by start), a row replacing the
  previous one at the same address; the file names rendered with the unit's `comp_dir` and the
  directory (`render_file`, `path_push`);
* `findLocation`: the sequence containing the address and the last row at or before it
  (Rust's `binary_search_by`), as `(file, line, column)` with line 0 meaning none.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Dwarf

/-- The string sections a line program header may refer to. -/
structure StrSecs where
  debugStr : ByteArray := ByteArray.empty
  debugLineStr : ByteArray := ByteArray.empty
  debugStrOffsets : ByteArray := ByteArray.empty
  /-- `DW_AT_str_offsets_base` of the unit. -/
  strOffsetsBase : Nat := 0
  dwarf64 : Bool := false

/-- A string attribute value as gimli's `attr_string` resolves it: inline bytes, or an offset
into `.debug_str` or `.debug_line_str`, or an index into `.debug_str_offsets`. -/
inductive SVal where
  | inline (b : ByteArray)
  | strp (o : Nat)
  | lineStrp (o : Nat)
  | strx (i : Nat)
  | none
  deriving Inhabited

/-- The null-terminated string at `o` of a section. -/
def strAt (sec : ByteArray) (o : Nat) : Except String ByteArray :=
  (cstr.run' sec o sec.size).map (·.1)

/-- `attr_string`. -/
def SVal.get (s : StrSecs) : SVal → Except String ByteArray
  | .inline b => .ok b
  | .strp o => strAt s.debugStr o
  | .lineStrp o => strAt s.debugLineStr o
  | .strx i => do
    let sz := if s.dwarf64 then 8 else 4
    let (o, _) ← (offset s.dwarf64).run' s.debugStrOffsets (s.strOffsetsBase + i * sz) s.debugStrOffsets.size
    strAt s.debugStr o
  | .none => .error "Expected an attribute value to be a string form"

/-- A file entry: its path and directory index. -/
structure FileEntry where
  path : SVal
  dir : Nat
  deriving Inhabited

/-- The line number program header. -/
structure LineHeader where
  version : Nat
  addressSize : Nat
  minInstLen : Nat
  maxOps : Nat
  defaultIsStmt : Bool
  lineBase : Int
  lineRange : Nat
  opcodeBase : Nat
  stdLengths : Array Nat
  dirs : Array SVal
  files : Array FileEntry
  /-- The unit's name (file 0 of DWARF 2–4). -/
  compFile : Option FileEntry
  /-- The program: its bytes are `[progStart, progEnd)` of `.debug_line`. -/
  progStart : Nat
  progEnd : Nat
  deriving Inhabited

/-- Read one attribute of a v5 entry format with form `form`. -/
def readForm (dwarf64 : Bool) (form : Nat) : DR (Option SVal × Option Nat) := do
  match form with
  | 0x08 => pure (some (.inline (← cstr)), none)
  | 0x1f => pure (some (.lineStrp (← offset dwarf64)), none)
  | 0x0e => pure (some (.strp (← offset dwarf64)), none)
  | 0x1a => pure (some (.strx (← uleb)), none)
  | 0x25 => pure (some (.strx (← u8)), none)
  | 0x26 => pure (some (.strx (← u16)), none)
  | 0x27 => pure (some (.strx (← uN 3)), none)
  | 0x28 => pure (some (.strx (← u32)), none)
  | 0x0b => pure (none, some (← u8))
  | 0x05 => pure (none, some (← u16))
  | 0x06 => pure (none, some (← u32))
  | 0x07 => pure (none, some (← u64))
  | 0x0f => pure (none, some (← uleb))
  | 0x1e => skip 16; pure (none, none)
  | 0x09 => let n ← uleb; skip n; pure (none, none)
  | 0x0a => let n ← u8; skip n; pure (none, none)
  | 0x03 => let n ← u16; skip n; pure (none, none)
  | 0x04 => let n ← u32; skip n; pure (none, none)
  | _ => throw "Found an unknown `DW_FORM_*` type"

/-- A v5 entry format: (content type, form) pairs. -/
def entryFormat : DR (List (Nat × Nat)) := do
  let n ← u8
  let mut out := []
  for _ in [0:n] do
    let ct ← uleb
    let form ← uleb
    out := out ++ [(ct, form)]
  pure out

/-- A v5 directory or file entry: path and directory index. -/
def entryV5 (dwarf64 : Bool) (fmt : List (Nat × Nat)) : DR FileEntry := do
  let mut path : SVal := .none
  let mut dir := 0
  for (ct, form) in fmt do
    let (s, n) ← readForm dwarf64 form
    if ct == 1 then
      match s with
      | some v => path := v
      | none => throw "Expected an attribute value to be a string form"
    else if ct == 2 then
      dir := n.getD 0
  pure ⟨path, dir⟩

/-- **The header of the line program at `o` of `.debug_line`.** `addrSize` is the unit's
address size, `compName` its `DW_AT_name`. -/
def parseHeader (debugLine : ByteArray) (o addrSize : Nat) (compName : Option SVal) :
    Except String LineHeader :=
  (go.run' debugLine o debugLine.size).map (·.1)
where
  go : DR LineHeader := do
    let (len, d64) ← initialLength
    sub len do
      let version ← u16
      if version < 2 || 5 < version then throw "Found an unknown DWARF version"
      let mut addressSize := addrSize
      if version ≥ 5 then
        addressSize ← u8
        if !(addressSize ∈ [1, 2, 4, 8]) then throw "The specified address size is not supported"
        let seg ← u8
        if seg != 0 then throw "The specified segment size is not supported"
      let hlen ← offset d64
      let progStart := (← pos) + hlen
      let progEnd ← lim
      if progEnd < progStart then throw errEof
      sub hlen do
        let minInstLen ← u8
        if minInstLen == 0 then throw "The `minimum_instruction_length` field in the line number program header was zero"
        let maxOps ← if version ≥ 4 then u8 else pure 1
        if maxOps == 0 then throw "The `maximum_operations_per_instruction` field in the line number program header was zero"
        let defaultIsStmt := (← u8) != 0
        let lineBase ← i8
        let lineRange ← u8
        if lineRange == 0 then throw "The `line_range` field in the line number program header was zero"
        let opcodeBase ← u8
        if opcodeBase == 0 then throw "The `opcode_base` field in the line number program header was zero"
        let mut stdLengths := #[]
        for _ in [0:opcodeBase - 1] do
          stdLengths := stdLengths.push (← u8)
        let mut dirs : Array SVal := #[]
        let mut files : Array FileEntry := #[]
        if version ≤ 4 then
          for _ in [0:(← left) + 1] do
            let d ← cstr
            if d.isEmpty then break
            dirs := dirs.push (.inline d)
          for _ in [0:(← left) + 1] do
            let p ← cstr
            if p.isEmpty then break
            let dir ← uleb
            let _ ← uleb
            let _ ← uleb
            files := files.push ⟨.inline p, dir⟩
        else
          let dfmt ← entryFormat
          let dn ← uleb
          for _ in [0:dn] do
            dirs := dirs.push (← entryV5 d64 dfmt).path
          let ffmt ← entryFormat
          let fn ← uleb
          for _ in [0:fn] do
            files := files.push (← entryV5 d64 ffmt)
        let compFile := if version ≤ 4 then compName.map (⟨·, 0⟩) else none
        pure { version, addressSize, minInstLen, maxOps, defaultIsStmt, lineBase, lineRange,
               opcodeBase, stdLengths, dirs, files, compFile, progStart, progEnd }

/-- `header.file(index)`. -/
def LineHeader.file (h : LineHeader) (i : Nat) : Option FileEntry :=
  if h.version ≤ 4 then (if i == 0 then h.compFile else h.files[i - 1]?) else h.files[i]?

/-- `header.directory(index)` for an index other than 0 (DWARF 2–4 count from 1). -/
def LineHeader.dir (h : LineHeader) (i : Nat) : Option SVal :=
  if h.version ≤ 4 then h.dirs[i - 1]? else h.dirs[i]?

/-- A row of the line table (the registers addr2line keeps). -/
structure LRow where
  address : Nat
  file : Nat
  line : Nat
  column : Nat
  deriving Inhabited, Repr

/-- A sequence: `[start, end)` and its rows. -/
structure LSeq where
  start : Nat
  stop : Nat
  rows : Array LRow
  deriving Inhabited

/-- The state machine's registers. -/
structure Regs where
  tombstone : Bool := false
  address : Nat := 0
  opIndex : Nat := 0
  file : Nat := 1
  line : Nat := 1
  column : Nat := 0
  endSeq : Bool := false

/-- `add_sized`: checked against 64 bits, then masked to the address size. -/
def addSizedChecked (a b size : Nat) : Except String Nat :=
  if 2 ^ 64 ≤ a + b then .error "Address computation overflow" else .ok ((a + b) % 2 ^ (8 * size))

/-- `apply_operation_advance`. -/
def opAdvance (h : LineHeader) (r : Regs) (adv : Nat) : Except String Regs :=
  if r.tombstone then .ok r else
  let w := 2 ^ 64
  let (opIndex, addrAdv) :=
    if h.maxOps == 1 then (0, h.minInstLen * adv % w)
    else ((r.opIndex + adv) % w % h.maxOps, h.minInstLen * ((r.opIndex + adv) % w / h.maxOps) % w)
  (addSizedChecked r.address addrAdv h.addressSize).map fun a => { r with address := a, opIndex }

/-- `apply_line_advance`. -/
def lineAdvance (r : Regs) (d : Int) : Regs :=
  if d < 0 then { r with line := r.line - d.natAbs }
  else { r with line := (r.line + d.toNat) % 2 ^ 64 }

/-- A special opcode `op ≥ opcode_base` (DWARF §6.2.5.1): the operation advance
`(op - opcode_base) / line_range`, then the line advance
`line_base + (op - opcode_base) % line_range`. -/
def specialRegs (h : LineHeader) (r : Regs) (op : Nat) : Except String Regs := do
  let adj := op - h.opcodeBase
  let r1 ← opAdvance h r (adj / h.lineRange)
  pure (lineAdvance r1 (h.lineBase + (adj % h.lineRange : Nat)))

/-- The accumulated table: finished sequences, the rows of the current one. -/
structure LAcc where
  seqs : Array LSeq := #[]
  cur : Array LRow := #[]

/-- A row is emitted (`Lines::parse`). -/
def LAcc.emit (acc : LAcc) (r : Regs) : LAcc :=
  if r.endSeq then
    match acc.cur[0]? with
    | none => acc
    | some first =>
      let acc' := { acc with cur := #[] }
      if first.address < r.address then { acc' with seqs := acc'.seqs.push ⟨first.address, r.address, acc.cur⟩ }
      else acc'
  else
    let row : LRow := ⟨r.address, r.file, r.line, r.column⟩
    match acc.cur.back? with
    | some last => if last.address == r.address then { acc with cur := acc.cur.pop.push row }
      else { acc with cur := acc.cur.push row }
    | none => { acc with cur := acc.cur.push row }

/-- Run the program; `extraFiles` collects `DW_LNE_define_file` entries. -/
def runProgram (h : LineHeader) : DR (LAcc × Array FileEntry) := do
  let mut acc : LAcc := {}
  let mut r : Regs := { }
  let mut extra : Array FileEntry := #[]
  for _ in [0:(← left) + 1] do
    if ← isEmpty then break
    let op ← u8
    let mut emitRow := false
    if op ≥ h.opcodeBase then
      r ← match specialRegs h r op with
        | .ok x => pure x
        | .error e => throw e
      emitRow := true
    else if op == 0 then
      let len ← uleb
      let (r', e', x) ← sub len do
        let sop ← u8
        if sop == 1 then return ({ r with endSeq := true }, true, none)
        else if sop == 2 then
          let a ← address h.addressSize
          let tomb := a < r.address || a ≥ minTombstone h.addressSize
          return (if tomb then { r with tombstone := true } else { r with tombstone := false, address := a, opIndex := 0 }, false, none)
        else if sop == 3 then
          if h.version ≤ 4 then
            let p ← cstr
            let dir ← uleb
            let _ ← uleb
            let _ ← uleb
            return (r, false, some ⟨SVal.inline p, dir⟩)
          else return (r, false, none)
        else if sop == 4 then
          let _ ← uleb
          return (r, false, none)
        else
          return (r, false, none)
      r := r'
      emitRow := e'
      if let some fe := x then extra := extra.push fe
    else if op == 1 then emitRow := true
    else if op == 2 then
      let n ← uleb
      r ← match opAdvance h r n with
        | .ok x => pure x
        | .error e => throw e
    else if op == 3 then r := lineAdvance r (← sleb)
    else if op == 4 then r := { r with file := ← uleb }
    else if op == 5 then r := { r with column := ← uleb }
    else if op == 6 || op == 7 then pure ()
    else if op == 8 then
      let adj := 255 - h.opcodeBase
      r ← match opAdvance h r (adj / h.lineRange) with
        | .ok x => pure x
        | .error e => throw e
    else if op == 9 then
      let n ← u16
      if !r.tombstone then
        r ← match addSizedChecked r.address n h.addressSize with
          | .ok a => pure { r with address := a, opIndex := 0 }
          | .error e => throw e
    else if op == 10 || op == 11 then pure ()
    else if op == 12 then let _ ← uleb
    else
      for _ in [0:h.stdLengths[op - 1]!] do
        let _ ← uleb
    if emitRow then
      if !r.tombstone then acc := acc.emit r
      -- the reset after a row: new registers after `end_sequence`
      if r.endSeq then r := {}
  pure (acc, extra)

/-- A sequence of rows is ordered by address (the binary search assumes it). -/
def LSeq.lt (a b : LSeq) : Bool := a.start < b.start

/-- `path_push`. -/
def pathPush (path p : String) : String :=
  let fwd (s : String) := s.startsWith "/" || (s.drop 1).toString.startsWith ":/"
  let bwd (s : String) := s.startsWith "\\" || (s.drop 1).toString.startsWith ":\\"
  if fwd p || bwd p then p
  else
    let sep := if bwd path then "\\" else "/"
    (if !path.isEmpty && !path.endsWith sep then path ++ sep else path) ++ p

/-- Bytes as text, invalid UTF-8 replaced (`to_string_lossy`). -/
def lossy (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => String.ofList (b.toList.map fun c => if c.toNat < 128 then Char.ofNat c.toNat else '�')

/-- `render_file`. -/
def renderFile (s : StrSecs) (compDir : Option String) (h : LineHeader) (f : FileEntry) :
    Except String String := do
  let mut path := compDir.getD ""
  if f.dir != 0 then
    if let some d := h.dir f.dir then
      path := pathPush path (lossy (← d.get s))
  pure (pathPush path (lossy (← f.path.get s)))

/-- The line table of a unit. -/
structure Lines where
  files : Array String
  seqs : Array LSeq
  deriving Inhabited

/-- **`Lines::parse`**: run the program at `o` and render its file names. -/
def parseLines (debugLine : ByteArray) (s : StrSecs) (compDir : Option String) (h : LineHeader) :
    Except String Lines := do
  let ((acc, extra), _) ← (runProgram h).run' debugLine h.progStart h.progEnd
  let seqs := acc.seqs.toList.mergeSort (fun a b => a.start ≤ b.start) |>.toArray
  let h := { h with files := h.files ++ extra }
  let mut files := #[]
  match h.file 0 with
  | some f => files := files.push (← renderFile s compDir h f)
  | none => files := files.push ""
  let mut i := 1
  for _ in [0:h.files.size + 1] do
    match h.file i with
    | some f => files := files.push (← renderFile s compDir h f); i := i + 1
    | none => break
  pure ⟨files, seqs⟩

/-- A source location: file, line, column (`none` when unknown). -/
structure Loc where
  file : Option String
  line : Option Nat
  column : Option Nat
  deriving Inhabited, Repr

/-- `row_location`. -/
def Lines.rowLoc (ls : Lines) (r : LRow) : Loc :=
  ⟨ls.files[r.file]?, if r.line != 0 then some r.line else none, if r.line != 0 then some r.column else none⟩

/-- **`find_location`**. -/
def Lines.findLocation (ls : Lines) (probe : Nat) : Option Loc :=
  match binarySearch ls.seqs (fun s => if probe < s.start then .gt else if probe ≥ s.stop then .lt else .eq) with
  | .error _ => none
  | .ok i =>
    let s := ls.seqs[i]!
    match binarySearch s.rows (fun r => compare r.address probe) with
    | .ok j => some (ls.rowLoc s.rows[j]!)
    | .error 0 => none
    | .error j => some (ls.rowLoc s.rows[j - 1]!)

/-- The rank of an ordering (less < equal < greater), the order `binarySearch` assumes. -/
def ordRank : Ordering → Nat
  | .lt => 0
  | .eq => 1
  | .gt => 2

end Silmaril.Wasm.Tools.Dwarf

end
