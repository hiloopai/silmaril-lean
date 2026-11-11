module

public import Silmaril.Wasm.Tools.Framing.Defs

/-!
# `wasm-tools objdump`

`wasm-tools objdump` (wasm-tools 1.262.0, `src/bin/wasm-tools/objdump.rs`) prints one line per
section: its name, the byte range of its contents in the file, the range's size and the number
of items, plus start/end markers around nested modules and components.

* `secName e id`: the section's name (`none` for an unknown id: no line);
* `fmtLine`: `{:40} | {:#10x} - {:#10x} | {:9} bytes | {} count`, with Rust's `{:?}` quoting
  of custom section names (`debugStr`, ASCII escapes; see the parity document);
* `Space`, `Printer`: upstream's index spaces and indentation (`header`), including its counter
  quirks (a nested component's start/end lines show the counter of the new space);
* `lines fuel e base ss`: the lines of a section list whose first section starts at offset
  `base`; `objdump b`: the whole output.

`Thms`: the range printed for a section is where its contents are in the file
(`offsets_spec`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Objdump

open Silmaril.Wasm.Binary (Bytes)
open Silmaril.Wasm.Tools.Framing

/-- The name of a module section. -/
def moduleName : Nat → Option String
  | 1 => some "types" | 2 => some "imports" | 3 => some "functions" | 4 => some "tables"
  | 5 => some "memories" | 13 => some "tags" | 6 => some "globals" | 7 => some "exports"
  | 8 => some "start" | 9 => some "elements" | 12 => some "data count" | 10 => some "code"
  | 11 => some "data"
  | _ => none

/-- The name of a component section. -/
def componentName : Nat → Option String
  | 1 => some "module" | 2 => some "core instances" | 3 => some "core types"
  | 4 => some "component" | 5 => some "component instances" | 6 => some "component alias"
  | 7 => some "component types" | 8 => some "canonical functions" | 9 => some "component start"
  | 10 => some "component imports" | 11 => some "component exports"
  | _ => none

/-- The name of a (non-custom) section. -/
def secName : Enc → Nat → Option String
  | .module, id => moduleName id
  | .component, id => componentName id

/-! ## Rust formatting -/

/-- Lower-case hexadecimal digits. -/
def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- Pad on the left to `w` characters. -/
def padLeft (s : String) (w : Nat) : String := String.ofList (List.replicate (w - s.length) ' ') ++ s

/-- Pad on the right to `w` characters. -/
def padRight (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - s.length) ' ')

/-- `{:#10x}`. -/
def hex10 (n : Nat) : String := padLeft ("0x" ++ hexDigits n) 10

/-- Characters Rust's `char::escape_debug` writes as `\u{…}` besides the ASCII controls: a
table of the C1 controls, format characters (Cf), non-ASCII spaces (Zs), line and paragraph
separators and private use (a subset of `core::unicode::printable`; see the parity document). -/
def nonPrintableRanges : List (Nat × Nat) :=
  [(0x80, 0x9F), (0xA0, 0xA0), (0xAD, 0xAD), (0x600, 0x605), (0x61C, 0x61C), (0x6DD, 0x6DD),
    (0x70F, 0x70F), (0x1680, 0x1680), (0x180E, 0x180E), (0x2000, 0x200F), (0x2028, 0x202F),
    (0x205F, 0x2064), (0x2066, 0x206F), (0x3000, 0x3000), (0xE000, 0xF8FF), (0xFEFF, 0xFEFF),
    (0xFFF9, 0xFFFB), (0xFFFE, 0xFFFF)]

/-- Rust's `{:?}` of a string: quotes, `\0 \t \r \n \\ \"`, other control and non-printable
characters (`nonPrintableRanges`) as `\u{…}`. -/
def debugStr (s : String) : String :=
  let esc (c : Char) : String :=
    if c = '\\' then "\\\\" else if c = '"' then "\\\"" else if c = '\n' then "\\n"
    else if c = '\r' then "\\r" else if c = '\t' then "\\t" else if c = '\x00' then "\\0"
    else if c.toNat < 0x20 || c.toNat = 0x7f ||
        nonPrintableRanges.any (fun (lo, hi) => lo ≤ c.toNat && c.toNat ≤ hi) then
      "\\u{" ++ hexDigits c.toNat ++ "}"
    else c.toString
  "\"" ++ String.join (s.toList.map esc) ++ "\""

/-- **One line**: `{:40} | {:#10x} - {:#10x} | {:9} bytes | {} count`. -/
def fmtLine (header name : String) (start stop count : Nat) : String :=
  padRight (header ++ name) 40 ++ " | " ++ hex10 start ++ " - " ++ hex10 stop ++ " | " ++
    padLeft (toString (stop - start)) 9 ++ " bytes | " ++ toString count ++ " count"

/-! ## The printer state -/

/-- An index space: modules and components ended in it, and the encodings being processed. -/
structure Space where
  modules : Nat := 0
  components : Nat := 0
  processing : List Enc := []

/-- The stack of index spaces (head: the innermost). -/
abbrev Printer := List Space

/-- The indentation (`Printer::header`). -/
def header (p : Printer) : String :=
  let depth := match p with
    | [] => 0
    | sp :: _ => match sp.processing with
      | .module :: _ => p.length + 1
      | _ => p.length
  String.ofList (List.replicate (2 * depth) ' ')

/-- `Printer::start`. -/
def start (p : Printer) (e : Enc) : Printer × String :=
  match p with
  | [] => ([], "")
  | sp :: rest =>
    let p' := { sp with processing := e :: sp.processing } :: rest
    let line := match e with
      | .module => header p' ++ s!"------ start module {sp.modules} -------------"
      | .component => header p' ++ s!"------ start component {sp.components} ----------"
    (p', line)

/-- `Printer::end`: the printer and the line, if any. -/
def «end» (p : Printer) : Printer × Option String :=
  let h := header p
  match p with
  | [] => ([], none)
  | sp :: rest =>
    match sp.processing with
    | .module :: more =>
      ({ sp with processing := more, modules := sp.modules + 1 } :: rest,
        some s!"{h}------ end module {sp.modules} -------------")
    | .component :: _ =>
      let rest' := match rest with
        | [] => []
        | par :: rs => { par with components := par.components + 1 } :: rs
      (rest', some s!"{h}------ end component {sp.components} ----------")
    | [] => (rest, none)

/-! ## Lines -/

/-- The offset of each section's contents, the first section starting at `base`. -/
def offsets : Nat → List RawSec → List (RawSec × Nat)
  | _, [] => []
  | base, s :: ss =>
    (s, base + 1 + s.size.length) :: offsets (base + (1 + s.size.length + s.content.length)) ss

/-- The count printed for a section: the leading count of a vector section, the code entry
count, otherwise 1. -/
def count (e : Enc) (s : RawSec) : Nat :=
  let id := s.id.toNat
  let limited := match e with
    | .module => moduleLimited id || id = 10
    | .component => componentLimited id
  if limited then
    match readU32 s.content with
    | some (n, _, _) => n
    | none => 0
  else 1

/-- **The lines of a section list** of encoding `e` whose first section starts at `base`,
recursing into nested modules and components. -/
def lines (fuel : Nat) (e : Enc) (base : Nat) (ss : List RawSec) (p : Printer) :
    Except String (List String × Printer) :=
  go fuel e (offsets base ss) p
where
  go : Nat → Enc → List (RawSec × Nat) → Printer → Except String (List String × Printer)
  | _, _, [], p => .ok ([], p)
  | fuel, e, (s, o) :: rest, p => do
    let stop := o + s.content.length
    let (here, p) ← (do
      if s.id = 0 then
        let (n, d) ← customName s.content
        return ([fmtLine (header p) ("custom " ++ debugStr n) (o + d) stop 1], p)
      match secName e s.id.toNat with
      | none => return ([], p)
      | some name =>
        let l := fmtLine (header p) name o stop (count e s)
        match nestedEnc e s, fuel with
        | some e', fuel' + 1 =>
          let (_, inner) ← frame (some e') s.content
          let p := if e' = .component then {} :: p else p
          let (p, sl) := start p e'
          let (ls, p) ← lines.go fuel' e' (offsets (o + 8) inner) p
          let (p, el) := «end» p
          return ([l, sl] ++ ls ++ el.toList, p)
        | some _, 0 => .error "nesting too deep"
        | none, _ => return ([l], p) : Except String (List String × Printer))
    let (more, p) ← go fuel e rest p
    return (here ++ more, p)
  termination_by fuel _ ss => (fuel, ss.length)

/-- **`wasm-tools objdump`**: the output lines. -/
def objdump (b : Bytes) : Except String (List String) := do
  let (e, ss) ← frame none b
  let (ls, _) ← lines b.length e 8 ss [{}]
  return ls

end Silmaril.Wasm.Tools.Objdump
