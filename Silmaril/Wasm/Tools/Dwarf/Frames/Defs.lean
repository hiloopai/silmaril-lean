module

public import Silmaril.Wasm.Tools.Dwarf.Info.Defs

/-!
# addr2line's frames: units, functions, inlined calls

`Context.parse` is addr2line 0.27's `Context::from_dwarf` (`ResUnits::parse`) and
`Context.findFrames` its `find_frames`: the units whose ranges contain the address (in the order
of `ResUnits::find`), in the first that has a function or a location for it, the function
(`Functions::find_address`) and its chain of inlined calls (`find_inlined_functions`), each frame
with its name and language, and the location of the innermost frame from the line table and of
each outer frame from the call site of the inner one. A unit without a function but with a
location gives one frame without a name.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Dwarf

open Std

/-- A unit header: offsets, version, address size, format, unit type, abbreviation offset;
the position after it. -/
def readUnitHeader (s : Secs) (o : Nat) : Except String (Unit × Option (Nat × Nat)) := do
  let go : DR (Nat × Nat × Bool × Nat × Nat × Nat × Nat) := do
    let (len, d64) ← initialLength
    let start ← pos
    if (← left) < len then throw errEof
    let version ← u16
    if version < 2 || 5 < version then throw "Found an unknown DWARF version"
    let (ut, abbrevOff, asz) ← if version ≥ 5 then do
        let ut ← u8
        let asz ← u8
        let ao ← offset d64
        pure (ut, ao, asz)
      else do
        let ao ← offset d64
        let asz ← u8
        pure (1, ao, asz)
    if !(asz ∈ [1, 2, 4, 8]) then throw "The specified address size is not supported"
    if version ≥ 5 then
      if ut == 2 || ut == 6 then let _ ← u64; let _ ← offset d64
      else if ut == 4 || ut == 5 then let _ ← u64
      else if !(ut == 1 || ut == 3) then throw "Found an unknown `DW_UT_*` type"
    pure (version, ut, d64, asz, abbrevOff, ← pos, start + len)
  let ((version, ut, d64, asz, ao, ea, stop), _) ← go.run' s.info o s.info.size
  let unit : Unit := { hdrOffset := o, version, addrSize := asz, dwarf64 := d64, unitType := ut,
                       abbrevs := {}, entriesAt := ea, stop, headerSize := ea - o }
  pure (unit, some (ao, stop))

/-- `Dwarf::unit(header)`: the abbreviations, the root entry's attributes and the line program
header. -/
def loadUnit (s : Secs) (u : Unit) (ao : Nat) : Except String Unit := do
  let abbrevs ← parseAbbrevs s.abbr ao
  let u := { u with abbrevs }
  let rootRead : DR (Option (Array (Nat × AV))) := do
    let (a, _) ← readAbbrevAt u {}
    match a with
    | none => pure none
    | some a => some <$> readAttrs u a #[] fun acc n v => .ok (acc.push (n, v))
  let (root, _) ← rootRead.run' s.info u.entriesAt u.stop
  let some attrs := root | pure u
  let mut name : Option SVal := none
  let mut compDirV : Option SVal := none
  let mut lowPc : Option AV := none
  let mut stmt : Option Nat := none
  let mut u := u
  for (n, v) in attrs do
    match n, v with
    | 0x03, .str x => name := some x
    | 0x1b, .str x => compDirV := some x
    | 0x11, v => lowPc := some v
    | 0x10, .secOffset o => stmt := some o
    | 0x10, .udata o => stmt := some o
    | 0x72, .secOffset o => u := { u with strOffsetsBase := o }
    | 0x73, .secOffset o => u := { u with addrBase := o }
    | 0x74, .secOffset o => u := { u with rnglistsBase := o }
    | _, _ => pure ()
  let ss := u.strSecs s
  -- `attr_string(..).ok()`
  let nameOk := name.bind fun x => match x.get ss with | .ok _ => some x | .error _ => none
  let compDir := compDirV.bind fun x => match x.get ss with | .ok b => some (lossy b) | .error _ => none
  let low ← match lowPc with
    | some (.addr a) => pure a
    | some (.addrx i) => u.address s i
    | _ => pure 0
  u := { u with name := nameOk, compDir, lowPc := low }
  match stmt with
  | some o =>
    let h ← parseHeader s.line o u.addrSize nameOk
    pure { u with lineHeader := some h }
  | none => pure u

/-- A unit as addr2line keeps it. -/
structure ResUnit where
  unit : Unit
  lang : Option Nat
  deriving Inhabited

/-- An entry of the sorted unit ranges. -/
structure UnitRange where
  range : Range
  unitId : Nat
  minBegin : Nat := 0
  deriving Inhabited

/-- The `.debug_aranges` sets: the unit offset and the ranges of each. -/
def parseAranges (s : Secs) : Except String (Array (Nat × Array Range)) := do
  let d := s.aranges
  let mut out := #[]
  let mut o := 0
  for _ in [0:d.size + 1] do
    if d.size ≤ o then break
    let go : DR (Nat × Array Range × Nat) := do
      let start ← pos
      let (len, d64) ← initialLength
      let hdr ← pos
      if (← left) < len then throw errEof
      let stop := hdr + len
      let version ← u16
      if version != 2 then throw "Found an unknown DWARF version"
      let infoOff ← offset d64
      let asz ← u8
      if !(asz ∈ [1, 2, 4, 8]) then throw "The specified address size is not supported"
      let seg ← u8
      if seg != 0 then throw "The specified segment size is not supported"
      -- entries are aligned to twice the address size, from the start of the set
      let tuple := 2 * asz
      let p ← pos
      let rem := (p - start) % tuple
      if rem != 0 then skip (tuple - rem)
      let mut rs := #[]
      for _ in [0:(stop - (← pos)) + 1] do
        if stop < (← pos) + tuple then break
        let a ← address asz
        let l ← address asz
        if a == 0 && l == 0 then break
        if l != 0 then rs := rs.push ⟨a, addSized a l asz⟩
      pure (infoOff, rs, stop)
    let ((io, rs, stop), _) ← go.run' d o d.size
    out := out.push (io, rs)
    o := stop
  pure out

/-- The DWARF of a module, ready for lookups. -/
structure Context where
  secs : Secs
  units : Array ResUnit
  ranges : Array UnitRange
  deriving Inhabited

/-- **`Context::from_dwarf`** (`ResUnits::parse`). -/
def Context.parse (s : Secs) : Except String Context := do
  let aranges := (← parseAranges s).toList.mergeSort (fun a b => a.1 ≤ b.1)
  let mut unitRanges : Array UnitRange := #[]
  let mut units : Array ResUnit := #[]
  let mut o := 0
  for _ in [0:s.info.size + 1] do
    if s.info.size ≤ o then break
    let (hdr, rest) ← readUnitHeader s o
    let some (ao, stop) := rest | break
    o := stop
    if hdr.unitType == 2 || hdr.unitType == 6 then continue
    let needRange := hdr.unitType != 3
    let some u := (loadUnit s hdr ao).toOption | continue
    let unitId := units.size
    let mut lang : Option Nat := none
    let mut need := needRange
    if needRange then
      let rootRead : DR (Option (RangeAttrs × Option Nat)) := do
        let (a, _) ← readAbbrevAt u {}
        match a with
        | none => pure none
        | some a => some <$> readAttrs u a (({} : RangeAttrs), (none : Option Nat)) fun (r, l) n v => do
            let r ← r.add s u n v
            let l := if n == 0x13 then (match v with | .udata x => some x | _ => l) else l
            pure (r, l)
      let (root, _) ← rootRead.run' s.info u.entriesAt u.stop
      let some (ra, l) := root | continue
      lang := l
      if ra.rangesOffset.isNone then
        for (io, rs) in aranges do
          if io == hdr.hdrOffset then
            for r in rs do
              unitRanges := unitRanges.push { range := r, unitId }
              need := false
      if need then
        let rs ← ra.ranges s u
        for r in rs do unitRanges := unitRanges.push { range := r, unitId }
        if !rs.isEmpty then need := false
    if need then
      if let some h := u.lineHeader then
        if let .ok ls := parseLines s.line (u.strSecs s) u.compDir h then
          for q in ls.seqs do unitRanges := unitRanges.push { range := ⟨q.start, q.stop⟩, unitId }
    units := units.push ⟨u, lang⟩
  let sorted := unitRanges.toList.mergeSort fun a b =>
    a.range.stop < b.range.stop || (a.range.stop == b.range.stop && a.unitId ≤ b.unitId)
  let mut arr := sorted.toArray
  let mut mn := 2 ^ 64 - 1
  for k in [0:arr.size] do
    let i := arr.size - 1 - k
    mn := min mn arr[i]!.range.begin
    arr := arr.set! i { arr[i]! with minBegin := mn }
  pure ⟨s, units, arr⟩

/-- **`ResUnits::find`**: the units whose ranges contain `probe`, in order. -/
def Context.find (c : Context) (probe : Nat) : List Nat := Id.run do
  let p := match binarySearch c.ranges (fun r => compare r.range.stop probe) with
    | .ok i => i + 1
    | .error i => i
  let mut out := []
  for i in [p:c.ranges.size] do
    let r := c.ranges[i]!
    if !(probe + 1 > r.minBegin) then break
    if probe ≥ r.range.stop || probe + 1 ≤ r.range.begin then continue
    out := out ++ [r.unitId]
  return out

/-- An inlined call: its entry offset, name, call file, line and column. -/
structure Inlined where
  name : Option ByteArray
  callFile : Option Nat
  callLine : Nat
  callColumn : Nat
  deriving Inhabited

/-- A function: its name and inlined calls with their ranges and depths. -/
structure Func where
  name : Option ByteArray
  inlined : Array Inlined
  /-- (range, call depth, index into `inlined`), sorted by depth then start. -/
  addrs : Array (Range × Nat × Nat)

/-- The unit containing the `.debug_info` offset `o` and the offset within it (`find_unit`). -/
def Context.findUnit (c : Context) (o : Nat) : Except String (Unit × Nat) :=
  match binarySearch c.units (fun ru => compare ru.unit.hdrOffset o) with
  | .ok _ | .error 0 => .error "No entry at the given offset"
  | .error i =>
    let u := c.units[i - 1]!.unit
    if o < u.entriesAt || u.stop ≤ o then .error "No entry at the given offset"
    else .ok (u, o - u.hdrOffset)

/-- `name_entry`/`name_attr`: the name of the entry at unit offset `uo`, following
`abstract_origin` and `specification` (`limit` levels). -/
def Context.nameEntry (c : Context) : Nat → Unit → Nat → Except String (Option ByteArray)
  | 0, _, _ => .ok none
  | limit + 1, u, uo => do
    let go : DR (Option (Option ByteArray × Option ByteArray × Option AV)) := do
      let (a, _) ← readAbbrevAt u {}
      match a with
      | none => pure none
      | some a =>
        some <$> readAttrs u a ((none : Option ByteArray), (none : Option ByteArray), (none : Option AV))
          fun (lk, nm, nx) n v =>
            let str := match v with
              | .str x => (x.get (u.strSecs c.secs)).toOption
              | _ => none
            if (n == 0x6e || n == 0x2007) && lk.isNone && str.isSome then .ok (str, nm, nx)
            else if n == 0x03 && str.isSome then .ok (lk, str, nx)
            else if n == 0x31 || n == 0x47 then .ok (lk, nm, some v)
            else .ok (lk, nm, nx)
    let (r, _) ← go.run' c.secs.info (u.hdrOffset + uo) u.stop
    match r with
    | none => .error "No entry at the given offset"
    | some (some lk, _, _) => pure (some lk)
    | some (none, some nm, _) => pure (some nm)
    | some (none, none, some (.unitRef o)) => c.nameEntry limit u o
    | some (none, none, some (.infoRef o)) => do
      let (u', uo) ← c.findUnit o
      c.nameEntry limit u' uo
    | some (none, none, _) => pure none

/-- `name_attr`: the name behind a reference (`limit` levels). -/
def Context.nameAttr (c : Context) (limit : Nat) (u : Unit) (v : AV) : Except String (Option ByteArray) :=
  match v with
  | .unitRef o => c.nameEntry limit u o
  | .infoRef o => do let (u', uo) ← c.findUnit o; c.nameEntry limit u' uo
  | _ => .ok none

end Silmaril.Wasm.Tools.Dwarf

end
