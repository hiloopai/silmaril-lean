module

public import Silmaril.Wasm.Tools.Meta.Fast.Defs
public import Silmaril.Wasm.Tools.Dwarf.Lookup.Defs
public import Silmaril.Wasm.Tools.Meta.Demangle.Rust.Defs
public import Silmaril.Wasm.Tools.Meta.Demangle.Cpp.Defs

/-!
# `wasm-tools addr2line`: the core

`wasm-tools addr2line [INPUT] [ADDRESSES]...` (1.262.0, `src/bin/wasm-tools/addr2line.rs` and
`src/addr2line.rs`) maps byte offsets of a binary to source locations through its DWARF:

1. `modulesOf`: every core module of the binary (the outer one or those nested in components),
   with its range (header to end, inclusive), the start of its code section's contents, and its
   custom sections by name (the last of a name wins), from the payload walk (`parseBinaryB`);
   a parse error is "failed to parse input and read custom sections".
2. `parseAddr`: `0x…` or `@…` hexadecimal, else decimal (Rust's `u64::from_str_radix`: an
   optional `+`, digits, at most `2^64 − 1`).
3. `pick`: the module containing the address (or, with `--code-section-relative`, the only
   module), and the address relative to its code section; none: "no module found which contains
   this address".
4. `Dwarf.Context.parse` on the module's DWARF sections and `findFrames` on the address.
5. `render`: `ADDR: ` then the frames separated by tabs, each the function name (demangled for
   the unit's language: Rust, C++, or by trying both when the unit has none; `<unnamed>`
   without a name) and ` file:line:column` when known; or `ADDR: no dwarf frames found for
   this address`.

The DWARF reading is the subset documented in `Silmaril.Wasm.Tools.Dwarf.*` (DWARF 2–5, 32- and
64-bit, no split DWARF, no supplementary files).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Addr2line

open Silmaril.Wasm.Tools.Meta Silmaril.Wasm.Tools.Dwarf

/-- A core module: range, code section start, custom sections (name, contents range). -/
structure Mod where
  start : Nat
  stop : Nat
  codeStart : Option Nat
  customs : List (String × Nat × Nat)
  deriving Inhabited

mutual
/-- The modules of a list of items (`enc` is the encoding of the unit holding them). -/
def modsOfItems (ba : ByteArray) : List ItemB → Array Mod → Array Mod
  | [], acc => acc
  | .sec _ :: is, acc => modsOfItems ba is acc
  | .nest _ _ a b enc items :: is, acc => modsOfItems ba is (modsOfUnit ba a b enc items acc)
/-- The modules of a unit `[a, b)`. -/
def modsOfUnit (ba : ByteArray) (a b : Nat) (enc : Enc) (items : List ItemB) (acc : Array Mod) : Array Mod :=
  match enc with
  | .component => modsOfItems ba items acc
  | .module =>
    let code := items.findSome? fun
      | .sec s => if s.id == 10 then some s.bodyAt else none
      | _ => none
    let customs := items.filterMap fun
      | .sec s =>
        if s.id != 0 then none else
        match customOfB ba s.bodyAt s.bodyEnd with
        | .ok (ns, ne) => some (lossy (ba.extract ns ne), ne, s.bodyEnd)
        | .error _ => none
      | _ => none
    acc.push ⟨a, b, code, customs⟩
end

/-- **`Addr2lineModules::parse`**. -/
def modulesOf (ba : ByteArray) : Except (String × String) (Array Mod) :=
  match parseBinaryB ba with
  | .error e => .error ("failed to parse input and read custom sections", e.render)
  | .ok (enc, items) => .ok (modsOfUnit ba 0 ba.size enc items #[])

/-- The DWARF sections of a module (`gimli::Dwarf::load` from its custom sections). -/
def Mod.secs (ba : ByteArray) (m : Mod) : Secs :=
  let get (n : String) : ByteArray :=
    match (m.customs.filter (·.1 == n)).getLast? with
    | some (_, a, b) => ba.extract a b
    | none => ByteArray.empty
  { info := get ".debug_info", abbr := get ".debug_abbrev", line := get ".debug_line",
    str := get ".debug_str", lineStr := get ".debug_line_str",
    strOffsets := get ".debug_str_offsets", addr := get ".debug_addr",
    ranges := get ".debug_ranges", rnglists := get ".debug_rnglists",
    aranges := get ".debug_aranges" }

/-- Rust's `u64::from_str_radix`. -/
def parseU64 (s : String) (radix : Nat) : Except String Nat := do
  let s := if s.startsWith "+" && s.length > 1 then (s.drop 1).toString else s
  if s.isEmpty then throw "cannot parse integer from empty string"
  let mut n := 0
  for c in s.toList do
    let d ← if c.isDigit then pure (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'z' then pure (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'Z' then pure (c.toNat - 55)
      else throw "invalid digit found in string"
    if radix ≤ d then throw "invalid digit found in string"
    n := n * radix + d
  if 2 ^ 64 ≤ n then throw "number too large to fit in target type"
  pure n

/-- An address argument: `0x…`/`@…` hexadecimal, else decimal. -/
def parseAddr (a : String) : Except String Nat :=
  if a.startsWith "0x" then parseU64 (a.drop 2).toString 16
  else if a.startsWith "@" then parseU64 (a.drop 1).toString 16
  else parseU64 a 10

/-- `Addr2lineModules::context`: the module and the code-relative address. -/
def pick (mods : Array Mod) (addr : Nat) (csr : Bool) : Except String (Option (Nat × Nat)) :=
  if csr then
    if mods.size == 1 then .ok (some (0, addr))
    else .error "cannot use `--code-section-relative` with more than one module"
  else
    match (mods.toList.zipIdx.find? fun (m, _) => m.start ≤ addr && addr ≤ m.stop) with
    | none => .ok none
    | some (m, i) =>
      match m.codeStart with
      | some c => if c ≤ addr then .ok (some (i, addr - c)) else .ok none
      | none => .ok none

/-- `FunctionName::demangle`: by the unit's language. -/
def demangleFor (lang : Option Nat) (name : String) : String :=
  let rust := Demangle.rustDemangle name (alt := true)
  let cpp := Demangle.cppDemangle name
  match lang with
  | some 0x1c => rust.getD name
  | some l => if l ∈ [0x04, 0x19, 0x1a, 0x21, 0x2a, 0x2b] then cpp.getD name else name
  | none => (rust <|> cpp).getD name

/-- The output line(s) for an address and its frames. -/
def render (addr : String) (frames : List Frame) : String :=
  if frames.isEmpty then addr ++ ": no dwarf frames found for this address\n" else
  String.join (frames.zipIdx.map fun (f, i) =>
    (if i == 0 then addr ++ ": " else "\t") ++
    (match f.name with
      | some n => demangleFor f.lang (lossy n)
      | none => "<unnamed>") ++
    (match f.loc with
      | some l => " " ++ l.file.getD "" ++ (l.line.map (":" ++ toString ·)).getD "" ++
          (l.column.map (":" ++ toString ·)).getD ""
      | none => "") ++ "\n")

end Silmaril.Wasm.Tools.Meta.Addr2line

end
