module

public import Silmaril.Wasm.Tools.Dwarf.Line.Defs
public import Std.Data.HashMap

/-!
# DWARF units, entries, ranges and functions (`.debug_info`, `.debug_abbrev`, …)

What addr2line 0.27 reads from `.debug_info` (over gimli 0.34), for `find_frames`:

* `units`: the unit headers (DWARF 2–5, 32- and 64-bit; v5 unit types, type units skipped),
  their abbreviation tables (`.debug_abbrev`: code, tag, children flag, attribute
  specifications with `DW_FORM_implicit_const`), and the attributes of the root entry
  (`DW_AT_name`, `comp_dir`, `low_pc`, `stmt_list`, `str_offsets_base`, `addr_base`,
  `rnglists_base`, `language`) and its line program header;
* attribute values for every form of DWARF 5 and the GNU forms `GNU_addr_index`,
  `GNU_str_index`, `GNU_ref_alt`, `GNU_strp_alt`, with gimli's conversions (`high_pc` as a
  size, `DW_AT_ranges` as an offset or an `rnglistx` index, addresses through `.debug_addr`);
* address ranges: `low_pc`/`high_pc` (address or size), `DW_AT_ranges` in `.debug_ranges`
  (v2–4: pairs, base address selection) or `.debug_rnglists` (v5: the eight `DW_RLE_*`
  kinds), with gimli's tombstone and empty-range filtering; `.debug_aranges`;
* the unit ranges sorted by end (`ResUnits::parse`, `find`), the functions of a unit
  (`DW_TAG_subprogram` entries with addresses, `Functions::parse`), a function's name
  (`linkage_name`, `name`, following `abstract_origin`/`specification` up to 16 levels) and its
  inlined subroutines with call depth, call file, line and column (`Function::parse`).

Searches use Rust's `binary_search_by` (`Read.binarySearch`); sorts are stable where Rust's
`sort_unstable` leaves equal keys in an unspecified order.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Dwarf

open Std

/-- The DWARF sections of a module (empty when absent). -/
structure Secs where
  info : ByteArray := ByteArray.empty
  abbr : ByteArray := ByteArray.empty
  line : ByteArray := ByteArray.empty
  str : ByteArray := ByteArray.empty
  lineStr : ByteArray := ByteArray.empty
  strOffsets : ByteArray := ByteArray.empty
  addr : ByteArray := ByteArray.empty
  ranges : ByteArray := ByteArray.empty
  rnglists : ByteArray := ByteArray.empty
  aranges : ByteArray := ByteArray.empty
  deriving Inhabited

/-- An abbreviation: tag, children flag, attribute specifications (name, form, implicit
constant). -/
structure Abbrev where
  tag : Nat
  children : Bool
  attrs : Array (Nat × Nat × Int)
  deriving Inhabited

/-- The abbreviation table at `o` of `.debug_abbrev`. -/
def parseAbbrevs (d : ByteArray) (o : Nat) : Except String (HashMap Nat Abbrev) :=
  (go.run' d o d.size).map (·.1)
where
  go : DR (HashMap Nat Abbrev) := do
    let mut m : HashMap Nat Abbrev := {}
    for _ in [0:(← left) + 1] do
      let code ← uleb
      if code == 0 then break
      let tag ← uleb
      if tag == 0 then throw "Found an abbreviation with a zero tag"
      let ch ← u8
      if ch > 1 then throw "Found an unknown `DW_CHILDREN_*` value"
      let mut attrs := #[]
      for _ in [0:(← left) + 1] do
        let name ← uleb
        let form ← uleb
        if name == 0 && form == 0 then break
        if name == 0 || form == 0 then throw "Found an attribute with a zero name or form"
        let ic ← if form == 0x21 then sleb else pure 0
        attrs := attrs.push (name, form, ic)
      if m.contains code then throw "Found a duplicate abbreviation code"
      m := m.insert code ⟨tag, ch == 1, attrs⟩
    pure m

/-- An attribute value, as far as addr2line looks at it. -/
inductive AV where
  | addr (n : Nat)
  | addrx (i : Nat)
  | udata (n : Nat)
  | sdata (i : Int)
  | str (s : SVal)
  | unitRef (o : Nat)
  | infoRef (o : Nat)
  | secOffset (o : Nat)
  | rnglistx (i : Nat)
  | other
  deriving Inhabited

/-- A unit: header fields, abbreviations, root attributes, line program header. -/
structure Unit where
  hdrOffset : Nat
  version : Nat
  addrSize : Nat
  dwarf64 : Bool
  unitType : Nat
  abbrevs : HashMap Nat Abbrev
  /-- The entries are `[entriesAt, stop)` of `.debug_info`. -/
  entriesAt : Nat
  stop : Nat
  /-- The offset of the entries from the start of the header. -/
  headerSize : Nat
  name : Option SVal := none
  compDir : Option String := none
  lowPc : Nat := 0
  strOffsetsBase : Nat := 0
  addrBase : Nat := 0
  rnglistsBase : Nat := 0
  lineHeader : Option LineHeader := none
  deriving Inhabited

/-- The string sections as a unit sees them. -/
def Unit.strSecs (s : Secs) (u : Unit) : StrSecs :=
  { debugStr := s.str, debugLineStr := s.lineStr, debugStrOffsets := s.strOffsets,
    strOffsetsBase := u.strOffsetsBase, dwarf64 := u.dwarf64 }

/-- Read the value of one attribute specification (gimli's `read_attribute` and `value()`);
`fuel` bounds the `DW_FORM_indirect` chain. -/
def readAttrF (u : Unit) (name : Nat) (fuel : Nat) (form : Nat) (ic : Int) : DR AV := do
  let d64 := u.dwarf64
  let refAddrSize := if u.version == 2 then u.addrSize else if d64 then 8 else 4
  let data (n : Nat) : AV :=
    -- gimli's conversions of constants by attribute
    if name == 0x12 || name == 0x13 || name == 0x58 || name == 0x59 || name == 0x57 then .udata n
    else if name == 0x55 || name == 0x10 || name == 0x72 || name == 0x73 || name == 0x74 then .secOffset n
    else .udata n
  match form with
  | 0x01 => pure (.addr (← address u.addrSize))
  | 0x03 => let n ← u16; skip n; pure .other
  | 0x04 => let n ← u32; skip n; pure .other
  | 0x05 => pure (data (← u16))
  | 0x06 =>
    let n ← u32
    pure (if u.version ≤ 3 && (name == 0x55 || name == 0x10) then .secOffset n else data n)
  | 0x07 =>
    let n ← u64
    pure (if u.version ≤ 3 && (name == 0x55 || name == 0x10) then .secOffset n else data n)
  | 0x08 => pure (.str (.inline (← cstr)))
  | 0x09 => let n ← uleb; skip n; pure .other
  | 0x0a => let n ← u8; skip n; pure .other
  | 0x0b => pure (data (← u8))
  | 0x0c => let _ ← u8; pure .other
  | 0x0d => pure (.sdata (← sleb))
  | 0x0e => pure (.str (.strp (← offset d64)))
  | 0x0f => pure (data (← uleb))
  | 0x10 => pure (.infoRef (← uN refAddrSize))
  | 0x11 => pure (.unitRef (← u8))
  | 0x12 => pure (.unitRef (← u16))
  | 0x13 => pure (.unitRef (← u32))
  | 0x14 => pure (.unitRef (← u64))
  | 0x15 => pure (.unitRef (← uleb))
  | 0x16 =>
    match fuel with
    | 0 => throw "Found an unknown `DW_FORM_*` type"
    | k + 1 => let f ← uleb; readAttrF u name k f ic
  | 0x17 => pure (.secOffset (← offset d64))
  | 0x18 => let n ← uleb; skip n; pure .other
  | 0x19 => pure .other
  | 0x1a => pure (.str (.strx (← uleb)))
  | 0x1b => pure (.addrx (← uleb))
  | 0x1c => let _ ← u32; pure .other
  | 0x1d => let _ ← offset d64; pure .other
  | 0x1e => skip 16; pure .other
  | 0x1f => pure (.str (.lineStrp (← offset d64)))
  | 0x20 => let _ ← u64; pure .other
  | 0x21 => pure (if ic < 0 then .sdata ic else data ic.toNat)
  | 0x22 => let _ ← uleb; pure .other
  | 0x23 => pure (.rnglistx (← uleb))
  | 0x24 => let _ ← u64; pure .other
  | 0x25 => pure (.str (.strx (← u8)))
  | 0x26 => pure (.str (.strx (← u16)))
  | 0x27 => pure (.str (.strx (← uN 3)))
  | 0x28 => pure (.str (.strx (← u32)))
  | 0x29 => pure (.addrx (← u8))
  | 0x2a => pure (.addrx (← u16))
  | 0x2b => pure (.addrx (← uN 3))
  | 0x2c => pure (.addrx (← u32))
  | 0x1f01 => pure (.addrx (← uleb))
  | 0x1f02 => pure (.str (.strx (← uleb)))
  | 0x1f20 => let _ ← offset d64; pure .other
  | 0x1f21 => let _ ← offset d64; pure .other
  | _ => throw "Found an unknown `DW_FORM_*` type"

/-- `readAttrF` with a bounded indirection. -/
def readAttr (u : Unit) (name form : Nat) (ic : Int) : DR AV := readAttrF u name 8 form ic

/-- The address at index `i` of `.debug_addr` (`unit.address(index)`). -/
def Unit.address (s : Secs) (u : Unit) (i : Nat) : Except String Nat :=
  ((Dwarf.address u.addrSize).run' s.addr (u.addrBase + i * u.addrSize) s.addr.size).map (·.1)

/-- DIE traversal state of `EntriesRaw`: depth and the pending change. -/
structure Walk where
  depth : Int := 0
  delta : Int := 0

/-- `read_abbreviation`: the next entry's abbreviation (`none` for a null entry). -/
def readAbbrevAt (u : Unit) (w : Walk) : DR (Option Abbrev × Walk) := do
  let w := { w with depth := w.depth + w.delta }
  let code ← uleb
  if code == 0 then return (none, { w with delta := -1 })
  match u.abbrevs[code]? with
  | some a => pure (some a, { w with delta := if a.children then 1 else 0 })
  | none => throw "Found an unknown abbreviation code"

/-- The range attributes of an entry. -/
structure RangeAttrs where
  lowPc : Option Nat := none
  highPc : Option Nat := none
  size : Option Nat := none
  rangesOffset : Option Nat := none

/-- The offset of an `rnglistx` index (`ranges_offset`). -/
def Unit.rnglistOffset (s : Secs) (u : Unit) (i : Nat) : Except String Nat := do
  let sz := if u.dwarf64 then 8 else 4
  let (o, _) ← (offset u.dwarf64).run' s.rnglists (u.rnglistsBase + i * sz) s.rnglists.size
  pure (u.rnglistsBase + o)

/-- Record a range attribute (`low_pc`, `high_pc`, `ranges`). -/
def RangeAttrs.add (s : Secs) (u : Unit) (r : RangeAttrs) (name : Nat) (v : AV) : Except String RangeAttrs :=
  if name == 0x11 then
    match v with
    | .addr a => .ok { r with lowPc := some a }
    | .addrx i => do pure { r with lowPc := some (← u.address s i) }
    | _ => .ok r
  else if name == 0x12 then
    match v with
    | .addr a => .ok { r with highPc := some a }
    | .addrx i => do pure { r with highPc := some (← u.address s i) }
    | .udata n => .ok { r with size := some n }
    | _ => .ok r
  else if name == 0x55 then
    match v with
    | .secOffset o => .ok { r with rangesOffset := some o }
    | .udata o => .ok { r with rangesOffset := some o }
    | .rnglistx i => do pure { r with rangesOffset := some (← u.rnglistOffset s i) }
    | _ => .ok r
  else .ok r

/-- A half-open address range. -/
structure Range where
  begin : Nat
  stop : Nat
  deriving Inhabited, Repr

/-- The ranges of a range list at `o` (`unit.ranges(offset)`, gimli's `RngListIter`). -/
def rangeList (s : Secs) (u : Unit) (o : Nat) : Except String (Array Range) := do
  let sz := u.addrSize
  let tomb := minTombstone sz
  let conv (r : Range) : Option Range :=
    if r.begin ≥ tomb || r.begin ≥ r.stop then none else some r
  if u.version ≤ 4 then
    let go : DR (Array Range) := do
      let mut out := #[]
      let mut base := u.lowPc
      for _ in [0:(← left) + 1] do
        let b ← Dwarf.address sz
        let e ← Dwarf.address sz
        if b == 0 && e == 0 then break
        if b == onesSized sz then base := e
        else
          if base ≥ tomb then continue
          let r : Range := ⟨addSized base b sz, addSized base e sz⟩
          if let some r := conv r then out := out.push r
      pure out
    pure (← go.run' s.ranges o s.ranges.size).1
  else
    let go : DR (Array Range) := do
      let mut out := #[]
      let mut base := u.lowPc
      for _ in [0:(← left) + 1] do
        let k ← u8
        let addrx (i : Nat) : DR Nat := match u.address s i with
          | .ok a => pure a
          | .error e => throw e
        let r : Option Range ← match k with
          | 0 => break
          | 1 => base ← addrx (← uleb); pure none
          | 2 => do let b ← addrx (← uleb); let e ← addrx (← uleb); pure (some ⟨b, e⟩)
          | 3 => do let b ← addrx (← uleb); let l ← uleb; pure (some ⟨b, addSized b l sz⟩)
          | 4 => do
            let b ← uleb
            let e ← uleb
            if base ≥ tomb then pure none
            else pure (some ⟨addSized base b sz, addSized base e sz⟩)
          | 5 => base ← Dwarf.address sz; pure none
          | 6 => do let b ← Dwarf.address sz; let e ← Dwarf.address sz; pure (some ⟨b, e⟩)
          | 7 => do let b ← Dwarf.address sz; let l ← uleb; pure (some ⟨b, addSized b l sz⟩)
          | _ => throw "Found an unknown `DW_RLE_*` type"
        if let some r := r then
          if let some r := conv r then out := out.push r
      pure out
    pure (← go.run' s.rnglists o s.rnglists.size).1

/-- `RangeAttributes::for_each_range`: the non-empty ranges. -/
def RangeAttrs.ranges (s : Secs) (u : Unit) (r : RangeAttrs) : Except String (Array Range) := do
  let keep (x : Range) : Bool := x.begin < x.stop
  match r.rangesOffset with
  | some o => pure ((← rangeList s u o).filter keep)
  | none =>
    match r.lowPc, r.highPc, r.size with
    | some b, some e, _ => pure (#[⟨b, e⟩].filter keep)
    | some b, none, some n => pure (#[⟨b, (b + n) % 2 ^ 64⟩].filter keep)
    | _, _, _ => pure #[]

/-- Read the attributes of an entry with abbreviation `a`, folding `f` over them. -/
def readAttrs {σ : Type} (u : Unit) (a : Abbrev) (init : σ) (f : σ → Nat → AV → Except String σ) : DR σ := do
  let mut st := init
  for (name, form, ic) in a.attrs do
    let v ← readAttr u name form ic
    st ← match f st name v with
      | .ok x => pure x
      | .error e => throw e
  pure st

end Silmaril.Wasm.Tools.Dwarf

end
