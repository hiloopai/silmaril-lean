module

public import Std.Data.HashMap

/-!
# Raw section structure of a module binary

What the printer needs beyond the decoded module (`Silmaril.Wasm.Binary.Core.Decode`): the
order and offsets of the sections, the custom sections (their names, payloads and places),
the `name` section and the `producers` section. Nothing here decides what module the bytes
encode; the printer's output is checked against the certified decoder and text elaborator
(`Silmaril.Wasm.Tools.Print.Defs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Print.Raw

/-- A cursor over a byte array; every reader returns `none` past the end. -/
abbrev R := StateT Nat (OptionT Id)

variable (b : ByteArray)

def byte : R UInt8 := do
  let p ← get
  if h : p < b.size then set (p + 1); pure b[p] else failure

/-- Unsigned LEB128 (at most 10 bytes). -/
def leb : R Nat := go 0 0 10
where
  go (acc shift : Nat) : Nat → R Nat
    | 0 => failure
    | fuel + 1 => do
      let x ← byte b
      let acc := acc + (x.toNat % 128) * 2 ^ shift
      if x.toNat < 128 then pure acc else go acc (shift + 7) fuel

def bytes (n : Nat) : R ByteArray := do
  let p ← get
  if p + n ≤ b.size then set (p + n); pure (b.extract p (p + n)) else failure

/-- A `name` (length-prefixed UTF-8). -/
def name : R String := do
  let n ← leb b
  let bs ← bytes b n
  match String.fromUTF8? bs with
  | some s => pure s
  | none => failure

/-- A vector, read with `f`. -/
def vec {α : Type} (f : R α) : R (List α) := do
  let n ← leb b
  let rec loop : Nat → List α → R (List α)
    | 0, acc => pure acc.reverse
    | k + 1, acc => do let x ← f; loop k (x :: acc)
  loop n []

/-- One section: its id, the offset of its id byte, of its payload, and the payload size. -/
structure Section where
  id : Nat
  start : Nat
  payload : Nat
  size : Nat
  deriving Repr, Inhabited

/-- The sections after the 8-byte header, in order. -/
def sections : Option (List Section) :=
  let rec loop : Nat → Nat → List Section → Option (List Section)
    | 0, _, _ => none
    | fuel + 1, p, acc =>
      if p ≥ b.size then some acc.reverse
      else
        match (do let id ← byte b; let n ← leb b; pure (id, n) : R _).run p |>.run with
        | some ((id, n), q) =>
          if q + n ≤ b.size then loop fuel (q + n) (⟨id.toNat, p, q, n⟩ :: acc) else none
        | none => none
  if b.size < 8 then none else loop (b.size + 1) 8 []

/-- The name and the payload offset of a custom section. -/
def customName (s : Section) : Option (String × Nat) :=
  match (name b).run s.payload |>.run with
  | some (n, q) => if q ≤ s.payload + s.size then some (n, q) else none
  | none => none

/-! ## The `name` section -/

/-- How wasmprinter writes a name (`Naming` in `lib.rs`). -/
inductive Kind where
  | dollar
  | quoted
  | synthetic (pre : String)
  deriving Repr, Inhabited, BEq

structure Naming where
  name : String
  kind : Kind
  deriving Repr, Inhabited

def isIdChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') ||
    "!#$%&'*+-./:<=>?@\\^_`|~".contains c

/-- `Naming::new`: `used` is the set of names already given in this map (`none` for labels). -/
def mkNaming (n : String) (index : Nat) (group : String) (used : Option (Std.HashMap String Unit)) :
    Naming × Option (Std.HashMap String Unit) :=
  let kind := if n.toList.any (fun c => !isIdChar c) then Kind.quoted else Kind.dollar
  let (dup, used') := match used with
    | some u => (u.contains n, some (u.insert n ()))
    | none => (false, none)
  let kind := if n.isEmpty || n.startsWith "#" || dup then
      Kind.synthetic ("#" ++ group ++ toString index) else kind
  (⟨n, kind⟩, used')

abbrev NameMap := Std.HashMap Nat Naming
abbrev IndirectMap := Std.HashMap (Nat × Nat) Naming

/-- The names of a module, as wasmprinter registers them. -/
structure Names where
  module : Option Naming := none
  funcs : NameMap := {}
  locals : IndirectMap := {}
  labels : IndirectMap := {}
  types : NameMap := {}
  tables : NameMap := {}
  memories : NameMap := {}
  globals : NameMap := {}
  elems : NameMap := {}
  datas : NameMap := {}
  fields : IndirectMap := {}
  tags : NameMap := {}
  params : IndirectMap := {}
  tagParams : IndirectMap := {}
  deriving Inhabited

def nameMap (group : String) : R NameMap := do
  let entries ← vec b (do let i ← leb b; let n ← name b; pure (i, n))
  let (m, _) := entries.foldl (fun (acc : NameMap × Std.HashMap String Unit) (i, n) =>
    let (nm, u) := mkNaming n i group (some acc.2)
    (acc.1.insert i nm, u.getD acc.2)) ({}, {})
  pure m

def indirectMap (group : String) (tracked : Bool) : R IndirectMap := do
  let outer ← vec b (do
    let i ← leb b
    let inner ← vec b (do let j ← leb b; let n ← name b; pure (j, n))
    pure (i, inner))
  pure <| outer.foldl (fun acc (i, inner) =>
    let (m, _) := inner.foldl (fun (acc2 : IndirectMap × Option (Std.HashMap String Unit)) (j, n) =>
      let (nm, u) := mkNaming n j group acc2.2
      (acc2.1.insert (i, j) nm, if tracked then u else none))
      (acc, if tracked then some {} else none)
    m) {}

/-- Read the subsections of a `name` section payload `[p, e)`; a malformed subsection stops
the reading, keeping what was read (wasmprinter ignores errors in the name section). -/
def readNames (p e : Nat) : Names :=
  let rec loop : Nat → Nat → Names → Names
    | 0, _, ns => ns
    | fuel + 1, q, ns =>
      if q ≥ e then ns
      else
        match (do let id ← byte b; let n ← leb b; pure (id, n) : R _).run q |>.run with
        | none => ns
        | some ((id, n), r) =>
          if r + n > e then ns
          else
            let sub {α : Type} (f : R α) : Option α :=
              match f.run r |>.run with
              | some (x, _) => some x
              | none => none
            let ns' : Option Names := match id.toNat with
              | 0 => (sub (name b)).map fun s =>
                  { ns with module := some (mkNaming s 0 "module" none).1 }
              | 1 => (sub (nameMap b "func")).map fun m => { ns with funcs := m }
              | 2 => (sub (indirectMap b "local" true)).map fun m => { ns with locals := m }
              | 3 => (sub (indirectMap b "label" false)).map fun m => { ns with labels := m }
              | 4 => (sub (nameMap b "type")).map fun m => { ns with types := m }
              | 5 => (sub (nameMap b "table")).map fun m => { ns with tables := m }
              | 6 => (sub (nameMap b "memory")).map fun m => { ns with memories := m }
              | 7 => (sub (nameMap b "global")).map fun m => { ns with globals := m }
              | 8 => (sub (nameMap b "elem")).map fun m => { ns with elems := m }
              | 9 => (sub (nameMap b "data")).map fun m => { ns with datas := m }
              | 10 => (sub (indirectMap b "field" true)).map fun m => { ns with fields := m }
              | 11 => (sub (nameMap b "tag")).map fun m => { ns with tags := m }
              | 12 => (sub (indirectMap b "parameter" true)).map fun m => { ns with params := m }
              | 13 => (sub (indirectMap b "tag parameter" true)).map fun m =>
                  { ns with tagParams := m }
              | _ => some ns
            match ns' with
            | some ns' => loop fuel (r + n) ns'
            | none => ns
  loop (e - p + 1) p {}

/-! ## The `producers` section -/

/-- Fields of a `producers` section: `(field, [(name, version)])`. -/
def readProducers (p : Nat) : Option (List (String × List (String × String))) :=
  match (vec b (do
      let f ← name b
      let vs ← vec b (do let n ← name b; let v ← name b; pure (n, v))
      pure (f, vs))).run p |>.run with
  | some (x, _) => some x
  | none => none

end Silmaril.Wasm.Tools.Print.Raw

namespace Silmaril.Wasm.Tools.Print.Raw

/-! ## Element segment encodings

The decoded module does not say how an element segment was encoded; the printer needs it
(`func 0 1` versus `funcref (ref.func 0) …`, an explicit `(table 0)`). `elemForms` reads
the flags of every segment of an element section. -/

variable (b : ByteArray)

/-- Skip an LEB128 number (signed or unsigned), at most 10 bytes. -/
def skipLeb : R Unit := go 10
where
  go : Nat → R Unit
    | 0 => failure
    | fuel + 1 => do
      let x ← byte b
      if x.toNat < 128 then pure () else go fuel

/-- Skip a value or reference type. -/
def skipValType : R Unit := do
  let x ← byte b
  if x == 0x63 || x == 0x64 then skipLeb b else pure ()

/-- An opcode occurrence. -/
inductive Ev where
  | op | block | if_ | else_ | end_
  deriving Repr, Inhabited, BEq

/-- Skip a block type: `0x40`, a value type, or a type index (s33). -/
def skipBlockType : R Unit := do
  let p ← get
  let x ← byte b
  if x == 0x63 || x == 0x64 then skipLeb b
  else if x.toNat ≥ 0x80 then set p; skipLeb b
  else pure ()

/-- Skip a memory argument (alignment with the memory-index bit, optional memory index,
offset). -/
def skipMemarg : R Unit := do
  let a ← leb b
  if a / 64 % 2 == 1 then skipLeb b
  skipLeb b

/-- One opcode with its immediates: its kind. -/
def instrEv : R Ev := do
  let op ← byte b
  match op.toNat with
  | 0x02 | 0x03 | 0x06 => do skipBlockType b; pure .block
  | 0x04 => do skipBlockType b; pure .if_
  | 0x05 => pure .else_
  | 0x0b => pure .end_
  | 0x1f => do
    skipBlockType b
    let _ ← vec b (do
      let k ← byte b
      if k.toNat < 2 then skipLeb b
      skipLeb b)
    pure .block
  | 0x07 | 0x08 | 0x09 | 0x0c | 0x0d | 0x10 | 0x12 | 0x14 | 0x15 | 0x18 | 0x20 | 0x21 | 0x22
  | 0x23 | 0x24 | 0x25 | 0x26 | 0x3f | 0x40 | 0x41 | 0x42 | 0xd0 | 0xd2 | 0xd5 | 0xd6 => do
    skipLeb b; pure .op
  | 0x0e => do let _ ← vec b (skipLeb b); skipLeb b; pure .op
  | 0x11 | 0x13 => do skipLeb b; skipLeb b; pure .op
  | 0x1c => do let _ ← vec b (skipValType b); pure .op
  | 0x43 => do let _ ← bytes b 4; pure .op
  | 0x44 => do let _ ← bytes b 8; pure .op
  | 0xfb => do
    let sub ← leb b
    if sub ≤ 1 || (6 ≤ sub && sub ≤ 7) || (11 ≤ sub && sub ≤ 14) || sub == 16 ||
        (20 ≤ sub && sub ≤ 23) then skipLeb b
    else if (2 ≤ sub && sub ≤ 5) || (8 ≤ sub && sub ≤ 10) || (17 ≤ sub && sub ≤ 19) then do
      skipLeb b; skipLeb b
    else if sub == 24 || sub == 25 then do
      let _ ← byte b; skipLeb b; skipLeb b; skipLeb b
    else if sub == 15 || (26 ≤ sub && sub ≤ 30) then pure ()
    else failure
    pure .op
  | 0xfc => do
    let sub ← leb b
    if sub ≤ 7 then pure ()
    else if sub == 8 || sub == 10 || sub == 12 || sub == 14 then do skipLeb b; skipLeb b
    else if sub ≤ 17 then skipLeb b
    else failure
    pure .op
  | 0xfd => do
    let sub ← leb b
    if sub ≤ 11 || sub == 92 || sub == 93 then skipMemarg b
    else if sub == 12 || sub == 13 then do let _ ← bytes b 16
    else if 21 ≤ sub && sub ≤ 34 then do let _ ← byte b
    else if 84 ≤ sub && sub ≤ 91 then do skipMemarg b; let _ ← byte b
    else pure ()
    pure .op
  | o =>
    if 0x28 ≤ o && o ≤ 0x3e then do skipMemarg b; pure .op
    else if o ≤ 0x01 || o == 0x0a || o == 0x0f || o == 0x19 || o == 0x1a || o == 0x1b ||
        (0x45 ≤ o && o ≤ 0xc4) || o == 0xd1 || o == 0xd3 || o == 0xd4 then pure .op
    else failure

/-- Skip a constant expression through its first `end` (as wasmparser's `skip_const_expr`:
any operator is read, whether constant or not, and the first `end` closes the expression). -/
def skipConstExpr : R Unit := go 100000
where
  go : Nat → R Unit
    | 0 => failure
    | fuel + 1 => do
      let ev ← instrEv b
      if ev == .end_ then pure () else go fuel

/-- The form of an element segment: is the table index explicit, are the items
expressions? -/
structure ElemForm where
  explicitTable : Bool
  exprs : Bool
  deriving Repr, Inhabited, BEq

/-- One segment: its form, after skipping its body. -/
def elemSegment : R ElemForm := do
  let flags ← leb b
  if flags > 7 then failure
  let active := flags % 2 == 0
  let explicitTable := flags == 2 || flags == 6
  let exprs := flags ≥ 4
  if explicitTable then skipLeb b
  if active then skipConstExpr b
  if exprs then
    if flags != 4 then skipValType b
    let _ ← vec b (skipConstExpr b)
  else
    if flags != 0 then let _ ← byte b
    let _ ← vec b (skipLeb b)
  pure ⟨explicitTable, exprs⟩

/-- The forms of the segments of the element section with payload at `p`. -/
def elemForms (p : Nat) : Option (List ElemForm) :=
  match (vec b (elemSegment b)).run p |>.run with
  | some (x, _) => some x
  | none => none

/-- Skip table limits (flags, minimum, optional maximum). -/
def skipLimits : R Unit := do
  let flags ← byte b
  skipLeb b
  if flags.toNat % 2 == 1 then skipLeb b

/-- Does each table of the table section at `p` carry an explicit initializer
(`0x40 0x00` form)? -/
def tableInits (p : Nat) : Option (List Bool) :=
  match (vec b (do
      let x ← byte b
      if x == 0x40 then
        let _ ← byte b
        skipValType b; skipLimits b; skipConstExpr b; pure true
      else
        if x == 0x63 || x == 0x64 then skipLeb b
        skipLimits b; pure false)).run p |>.run with
  | some (x, _) => some x
  | none => none

/-- Skip a storage type and its mutability byte. -/
def skipFieldType : R Unit := do
  let x ← byte b
  if x == 0x63 || x == 0x64 then skipLeb b
  let _ ← byte b

/-- Skip a composite type. -/
def skipComposite : R Unit := do
  let x ← byte b
  match x.toNat with
  | 0x60 => do let _ ← vec b (skipValType b); let _ ← vec b (skipValType b)
  | 0x5f => do let _ ← vec b (skipFieldType b)
  | 0x5e => skipFieldType b
  | _ => failure

/-- Skip a subtype. -/
def skipSubType : R Unit := do
  let p ← get
  let x ← byte b
  if x == 0x50 || x == 0x4f then
    let _ ← vec b (skipLeb b)
    skipComposite b
  else
    set p; skipComposite b

/-- For each recursion group of the type section at `p`: was it written with the `rec`
prefix (`0x4e`)? -/
def recForms (p : Nat) : Option (List Bool) :=
  match (vec b (do
      let q ← get
      let x ← byte b
      if x == 0x4e then
        let _ ← vec b (skipSubType b); pure true
      else
        set q; skipSubType b; pure false)).run p |>.run with
  | some (x, _) => some x
  | none => none

/-! ## Instructions of the code section

The decoded module does not keep byte offsets or whether an `if` had an explicit empty
`else`. `codeEvents` walks the code section and lists, per function, the opcodes in flat
order with their offsets relative to the start of the function body (after its size), as
wasmparser reports them. -/


/-- The opcodes of one function body `[p, e)` (offsets relative to `p`), through the final
`end` (excluded). -/
def bodyEvents (p e : Nat) : Option (Array (Nat × Ev)) :=
  let locals : R Unit := do let _ ← vec b (do skipLeb b; skipValType b)
  match locals.run p |>.run with
  | none => none
  | some ((), q) =>
    let rec loop : Nat → Nat → Nat → Array (Nat × Ev) → Option (Array (Nat × Ev))
      | 0, _, _, _ => none
      | fuel + 1, q, depth, acc =>
        if q ≥ e then none
        else
          match (instrEv b).run q |>.run with
          | none => none
          | some (ev, q') =>
            match ev with
            | .end_ => if depth = 0 then some acc else loop fuel q' (depth - 1) (acc.push (q - p, ev))
            | .block | .if_ => loop fuel q' (depth + 1) (acc.push (q - p, ev))
            | _ => loop fuel q' depth (acc.push (q - p, ev))
    loop (e - q + 1) q 0 #[]

/-- Per function of the code section at payload `p`: its body offset and opcodes. -/
def codeEvents (p : Nat) : Option (List (Nat × Array (Nat × Ev))) :=
  match (vec b (do
      let n ← leb b
      let q ← get
      set (q + n)
      pure (q, q + n))).run p |>.run with
  | none => none
  | some (fs, _) => fs.mapM fun (q, e) => (bodyEvents b q e).map (q, ·)

/-- Per `if` in flat order: was its `else` written? -/
def explicitElses (evs : Array (Nat × Ev)) : Array Bool := Id.run do
  let mut out : Array Bool := #[]
  -- the open blocks: `some k` for the `k`-th `if`, `none` for other blocks
  let mut stack : List (Option Nat) := []
  for (_, ev) in evs do
    match ev with
    | .if_ => stack := some out.size :: stack; out := out.push false
    | .block => stack := none :: stack
    | .else_ =>
      match stack with
      | some k :: _ => out := out.set! k true
      | _ => pure ()
    | .end_ => stack := stack.drop 1
    | .op => pure ()
  return out

/-- The `metadata.code.branch_hint` section: per function index, `(offset, taken)`. -/
def readBranchHints (p : Nat) : Option (List (Nat × List (Nat × Bool))) :=
  match (vec b (do
      let f ← leb b
      let hs ← vec b (do
        let off ← leb b
        let n ← leb b
        let v ← bytes b n
        pure (off, v.size == 1 && v[0]! == 1))
      pure (f, hs))).run p |>.run with
  | some (x, _) => some x
  | none => none

/-! ## Offsets for `--print-offsets` -/

/-- Skip one import. -/
def skipImport : R Unit := do
  let _ ← name b; let _ ← name b
  let k ← byte b
  match k.toNat with
  | 0 => skipLeb b
  | 1 => do skipValType b; skipLimits b
  | 2 => skipLimits b
  | 3 => do skipValType b; let _ ← byte b
  | 4 => do let _ ← byte b; skipLeb b
  | _ => failure

/-- Skip one table entry. -/
def skipTable : R Unit := do
  let x ← byte b
  if x == 0x40 then
    let _ ← byte b
    skipValType b; skipLimits b; skipConstExpr b
  else
    if x == 0x63 || x == 0x64 then skipLeb b
    skipLimits b

/-- Skip one data segment. -/
def skipData : R Unit := do
  let flags ← leb b
  if flags == 2 then skipLeb b
  if flags != 1 then skipConstExpr b
  let n ← leb b
  let _ ← bytes b n

/-- Skip one entry of a vector section with id `id`. -/
def skipEntry (id : Nat) : R Unit :=
  match id with
  | 1 => do
    let q ← get
    let x ← byte b
    if x == 0x4e then let _ ← vec b (skipSubType b) else set q; skipSubType b
  | 2 => skipImport b
  | 4 => skipTable b
  | 5 => skipLimits b
  | 6 => do skipValType b; let _ ← byte b; skipConstExpr b
  | 7 => do let _ ← name b; let _ ← byte b; skipLeb b
  | 9 => do let _ ← elemSegment b; pure ()
  | 11 => skipData b
  | 13 => do let _ ← byte b; skipLeb b
  | _ => failure

/-- The offsets of the entries of the vector section `s`. -/
def entryOffsets (s : Section) : Option (List Nat) :=
  match (vec b (do let q ← get; skipEntry b s.id; pure q)).run s.payload |>.run with
  | some (x, _) => some x
  | none => none

/-- A function body for `--print-offsets`: its start (after the size), the offset of the
first non-empty local group, its opcodes (offsets relative to the start) and the offset of
its final `end`. -/
structure BodyInfo where
  start : Nat
  localsAt : Option Nat
  evs : Array (Nat × Ev)
  endAt : Nat
  deriving Inhabited

def bodyInfo (p e : Nat) : Option BodyInfo :=
  let locals : R (Option Nat) := do
    let groups ← vec b (do let q ← get; let n ← leb b; skipValType b; pure (q, n))
    pure ((groups.find? (·.2 > 0)).map (·.1))
  match locals.run p |>.run with
  | none => none
  | some (la, q) =>
    let rec loop : Nat → Nat → Nat → Array (Nat × Ev) → Option BodyInfo
      | 0, _, _, _ => none
      | fuel + 1, q, depth, acc =>
        if q ≥ e then none
        else
          match (instrEv b).run q |>.run with
          | none => none
          | some (ev, q') =>
            match ev with
            | .end_ =>
              if depth = 0 then some ⟨p, la, acc, q⟩
              else loop fuel q' (depth - 1) (acc.push (q - p, ev))
            | .block | .if_ => loop fuel q' (depth + 1) (acc.push (q - p, ev))
            | _ => loop fuel q' depth (acc.push (q - p, ev))
    loop (e - q + 1) q 0 #[]

/-- The bodies of the code section at payload `p`. -/
def codeInfo (p : Nat) : Option (List BodyInfo) :=
  match (vec b (do
      let n ← leb b
      let q ← get
      set (q + n)
      pure (q, q + n))).run p |>.run with
  | none => none
  | some (fs, _) => fs.mapM fun (q, e) => bodyInfo b q e

/-- The branch hints with the offset of each hint entry: per function index,
`(instruction offset, taken, entry offset)`. -/
def readBranchHintsAt (p : Nat) : Option (List (Nat × List (Nat × Bool × Nat))) :=
  match (vec b (do
      let f ← leb b
      let hs ← vec b (do
        let at_ ← get
        let off ← leb b
        let n ← leb b
        let v ← bytes b n
        pure (off, v.size == 1 && v[0]! == 1, at_))
      pure (f, hs))).run p |>.run with
  | some (x, _) => some x
  | none => none

/-- The `producers` section with the offset of each value. -/
def readProducersAt (p : Nat) : Option (List (String × List (String × String × Nat))) :=
  match (vec b (do
      let f ← name b
      let vs ← vec b (do let at_ ← get; let n ← name b; let v ← name b; pure (n, v, at_))
      pure (f, vs))).run p |>.run with
  | some (x, _) => some x
  | none => none

end Silmaril.Wasm.Tools.Print.Raw
