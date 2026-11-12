module

/-!
# Rust symbol demangling (rustc-demangle 0.1.28)

A port of `rustc_demangle::try_demangle` and its `Display` (without `{:#}`), the Rust demangler
`wasm-tools 1.262.0` links (`Cargo.lock`: `rustc-demangle 0.1.28`).

* `stripLlvm`: an `.llvm.<hex>` suffix (characters `A–F 0–9 @`) is removed first.
* **Legacy** symbols (`legacyParse`): `_ZN`, `ZN` or `__ZN`, ASCII only, then elements
  `<decimal length><bytes>` up to `E`. They print (`legacyShow`) as the elements joined by `::`
  (the hash element `h<hex>` included), with `..` → `::`, a leading `_$` → `$`, and the escapes
  `$SP$ $BP$ $RF$ $LT$ $GT$ $LP$ $RP$ $C$ $u<hex>$` decoded (an unknown escape stops decoding of
  that element, which is then printed as is).
* **v0** symbols (`v0Parse`, `v0Show`): `_R`, `R` or `__R`, an upper-case letter, ASCII only;
  the grammar of RFC 2603 with the extensions of 0.1.28 (pattern types `W`, `#[splat]` `w`,
  `dyn` associated constants), parsed by a recursive descent that is also the printer (as
  upstream: the same code runs once without output to check the syntax and find the suffix,
  then again to print, following back references only when printing). Errors met while
  printing print `{invalid syntax}`, `{recursion limit reached}` or `?`, as upstream. Nesting is
  limited to depth 500.
* A suffix after the symbol is kept if it starts with `.` and is ASCII alphanumeric or
  punctuation; otherwise the symbol is not demangled.
* The output is limited to 1 000 000 bytes (`{size limit reached}` replaces the write that
  would exceed it, as `SizeLimitedFmtAdapter` does).

Not exact: `escape_debug` of non-ASCII characters in `str`/`char` constants escapes only
control characters (`Cc`), where Rust also escapes other non-printable characters and
grapheme extenders (`\u{…}`); const `str` generics are unstable Rust.

`rustDemangle s = some t` when `try_demangle` succeeds with `to_string() = t`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Demangle

/-- The output limit of rustc-demangle's `Display`. -/
def maxSize : Nat := 1000000

/-- Output under the size limit: once a write does not fit, nothing more is written and
`{size limit reached}` is printed at the end. -/
structure Out where
  buf : String := ""
  rem : Nat := maxSize
  failed : Bool := false
  deriving Inhabited

/-- One `write_str` through `SizeLimitedFmtAdapter`. -/
def Out.write (o : Out) (s : String) : Out :=
  if o.failed then o
  else if s.utf8ByteSize ≤ o.rem then { o with buf := o.buf ++ s, rem := o.rem - s.utf8ByteSize }
  else { o with failed := true }

/-- The text after the adapter: what was written, then the marker if a write failed. -/
def Out.finish (o : Out) : String := if o.failed then o.buf ++ "{size limit reached}" else o.buf

/-- The byte at `i` (`0` past the end; callers check bounds). -/
def byteAt (s : ByteArray) (i : Nat) : UInt8 := s.get! i

/-- A slice of an ASCII byte string as a `String`. -/
def slice (s : ByteArray) (a b : Nat) : String :=
  String.fromUTF8! (s.extract a b)

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isLowerHex (c : UInt8) : Bool := isDigit c || (97 ≤ c && c ≤ 102)
def isUpper (c : UInt8) : Bool := 65 ≤ c && c ≤ 90
def isLower (c : UInt8) : Bool := 97 ≤ c && c ≤ 122

/-- Lower-case hexadecimal of a number, without leading zeros. -/
def hexStr (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- `char::is_control`: general category `Cc`. -/
def isControl (c : Char) : Bool := c.toNat < 0x20 || (0x7f ≤ c.toNat && c.toNat < 0xa0)

/-! ## Legacy symbols -/

/-- The prefix of a legacy symbol, if any: the bytes after `_ZN`, `ZN` or `__ZN`. -/
def legacyInner (s : List UInt8) : Option (List UInt8) :=
  match s with
  | 95 :: 90 :: 78 :: r => some r
  | 90 :: 78 :: r => some r
  | 95 :: 95 :: 90 :: 78 :: r => some r
  | _ => none

/-- The digits at the front of a list, and the rest. -/
def spanDigits : List UInt8 → List UInt8 × List UInt8
  | c :: r => if isDigit c then let (d, r') := spanDigits r; (c :: d, r') else ([], c :: r)
  | [] => ([], [])

/-- The value of decimal digits. -/
def digitsVal (d : List UInt8) : Nat := d.foldl (fun n c => 10 * n + (c.toNat - 48)) 0

/-- The elements of a legacy symbol's inner part up to `E`, and the rest after `E`.
An element is a decimal length (fitting a `usize`) and that many bytes; `fuel` bounds their
number. -/
def legacyElems : Nat → List UInt8 → Option (List (List UInt8) × List UInt8)
  | _, [] => none
  | 0, _ :: _ => none
  | f + 1, c :: r =>
    if c == 69 then some ([], r) else
    if !isDigit c then none else
    let (d, r') := spanDigits (c :: r)
    let n := digitsVal d
    if 2 ^ 64 ≤ n then none else
    -- upstream reads the character after the digits and then `len` more: the identifier must
    -- be followed by at least one character
    if r'.length ≤ n then none else
    match legacyElems f (r'.drop n) with
    | none => none
    | some (es, rest) => some (r'.take n :: es, rest)

/-- `legacy::demangle`: the elements and the suffix after `E`. -/
def legacyParse (s : List UInt8) : Option (List (List UInt8) × List UInt8) := do
  let inner ← legacyInner s
  if inner.any (fun c => 128 ≤ c.toNat) then none
  legacyElems inner.length inner

/-- The text of a legacy escape (`$..$`), if it is one upstream decodes. -/
def legacyEscape (e : List UInt8) : Option String :=
  match e with
  | [83, 80] => some "@" | [66, 80] => some "*" | [82, 70] => some "&" | [76, 84] => some "<"
  | [71, 84] => some ">" | [76, 80] => some "(" | [82, 80] => some ")" | [67] => some ","
  | 117 :: ds =>
    if ds.isEmpty || !ds.all isLowerHex || 8 < (ds.dropWhile (· == 48)).length then none else
    let v := ds.foldl (fun n c => 16 * n + (if isDigit c then c.toNat - 48 else c.toNat - 87)) 0
    if h : v.isValidChar then
      let ch := Char.ofNatAux v h
      if isControl ch then none else some ch.toString
    else none
  | _ => none

/-- Index of the first byte satisfying `p`. -/
def findIdx? (p : UInt8 → Bool) : List UInt8 → Option Nat
  | [] => none
  | c :: r => if p c then some 0 else (findIdx? p r).map (· + 1)

/-- The decoding loop of one element (after the `_$` adjustment); `fuel` bounds its steps. -/
def legacyElemGo : Nat → List UInt8 → Out → Out
  | 0, rest, o => o.write (String.fromUTF8! (ByteArray.mk rest.toArray))
  | f + 1, rest, o =>
    match rest with
    | 46 :: 46 :: r => legacyElemGo f r (o.write "::")
    | 46 :: r => legacyElemGo f r (o.write ".")
    | 36 :: r =>
      match findIdx? (· == 36) r with
      | none => o.write (String.fromUTF8! (ByteArray.mk rest.toArray))
      | some i =>
        match legacyEscape (r.take i) with
        | some t => legacyElemGo f (r.drop (i + 1)) (o.write t)
        | none => o.write (String.fromUTF8! (ByteArray.mk rest.toArray))
    | _ =>
      match findIdx? (fun c => c == 36 || c == 46) rest with
      | some i => legacyElemGo f (rest.drop i)
          (o.write (String.fromUTF8! (ByteArray.mk (rest.take i).toArray)))
      | none => o.write (String.fromUTF8! (ByteArray.mk rest.toArray))

/-- The display of one element. -/
def legacyElem (e : List UInt8) (o : Out) : Out :=
  let e := match e with
    | 95 :: 36 :: r => 36 :: r
    | _ => e
  legacyElemGo (e.length + 1) e o

/-- `is_rust_hash`: `h` and hexadecimal digits. -/
def isRustHash (e : List UInt8) : Bool :=
  match e with
  | 104 :: r => r.all fun c => isDigit c || (97 ≤ c && c ≤ 102) || (65 ≤ c && c ≤ 70)
  | _ => false

/-- `legacy::Demangle`'s `Display`; the alternate format (`alt`) omits a final hash element. -/
def legacyShow (es : List (List UInt8)) (o : Out) (alt : Bool := false) : Out :=
  let es := if alt && (es.getLast?.map isRustHash).getD false then es.dropLast else es
  (es.zipIdx.foldl fun o (e, k) => legacyElem e (if k == 0 then o else o.write "::")) o

/-! ## v0 symbols -/

/-- The errors of the v0 parser. -/
inductive PErr where
  | invalid
  | tooDeep
  deriving DecidableEq, Inhabited

def PErr.message : PErr → String
  | .invalid => "{invalid syntax}"
  | .tooDeep => "{recursion limit reached}"

/-- The v0 parser: the next position and the depth. -/
structure P where
  next : Nat
  depth : Nat
  deriving Inhabited

/-- A parser step over the symbol `s`. -/
abbrev PStep (α : Type) := ByteArray → P → Except PErr (α × P)

def P.peek (s : ByteArray) (p : P) : Option UInt8 :=
  if p.next < s.size then some (byteAt s p.next) else none

def P.eat (s : ByteArray) (p : P) (b : UInt8) : Bool × P :=
  if p.peek s == some b then (true, { p with next := p.next + 1 }) else (false, p)

def pNext : PStep UInt8 := fun s p =>
  match p.peek s with
  | some b => .ok (b, { p with next := p.next + 1 })
  | none => .error .invalid

def pushDepth : PStep Unit := fun _ p =>
  if 500 < p.depth + 1 then .error .tooDeep else .ok ((), { p with depth := p.depth + 1 })

/-- Hex nibbles up to `_`: their positions `[start, end)`. -/
def hexNibblesGo (s : ByteArray) (start : Nat) : Nat → P → Except PErr ((Nat × Nat) × P)
  | 0, _ => .error .invalid
  | f + 1, p =>
    match p.peek s with
    | none => .error .invalid
    | some b =>
      let p' := { p with next := p.next + 1 }
      if isLowerHex b then hexNibblesGo s start f p'
      else if b == 95 then .ok ((start, p.next), p')
      else .error .invalid

def hexNibbles : PStep (Nat × Nat) := fun s p => hexNibblesGo s p.next (s.size + 1) p

def digit10 : PStep Nat := fun s p =>
  match p.peek s with
  | some d => if isDigit d then .ok (d.toNat - 48, { p with next := p.next + 1 }) else .error .invalid
  | none => .error .invalid

def digit62 : PStep Nat := fun s p =>
  match p.peek s with
  | some d =>
    if isDigit d then .ok (d.toNat - 48, { p with next := p.next + 1 })
    else if isLower d then .ok (10 + d.toNat - 97, { p with next := p.next + 1 })
    else if isUpper d then .ok (36 + d.toNat - 65, { p with next := p.next + 1 })
    else .error .invalid
  | none => .error .invalid

def integer62Go (s : ByteArray) : Nat → Nat → P → Except PErr (Nat × P)
  | 0, _, _ => .error .invalid
  | f + 1, x, p =>
    let (e, p) := p.eat s 95
    if e then (if x + 1 < 2 ^ 64 then .ok (x + 1, p) else .error .invalid) else
    match digit62 s p with
    | .error e => .error e
    | .ok (d, p) =>
      let x := x * 62 + d
      if 2 ^ 64 ≤ x then .error .invalid else integer62Go s f x p

def integer62 : PStep Nat := fun s p =>
  let (e, p') := p.eat s 95
  if e then .ok (0, p') else integer62Go s (s.size + 1) 0 p

def optInteger62 (tag : UInt8) : PStep Nat := fun s p =>
  let (e, p) := p.eat s tag
  if !e then .ok (0, p) else
  match integer62 s p with
  | .error e => .error e
  | .ok (x, p) => if x + 1 < 2 ^ 64 then .ok (x + 1, p) else .error .invalid

def disambiguator : PStep Nat := optInteger62 115

def pNamespace : PStep (Option Char) := fun s p =>
  match pNext s p with
  | .error e => .error e
  | .ok (b, p) =>
    if isUpper b then .ok (some (Char.ofNat b.toNat), p)
    else if isLower b then .ok (none, p) else .error .invalid

def backref : PStep P := fun s p =>
  let sStart := p.next - 1
  match integer62 s p with
  | .error e => .error e
  | .ok (i, p) =>
    if sStart ≤ i then .error .invalid else
    let np : P := { next := i, depth := p.depth }
    match pushDepth s np with
    | .error e => .error e
    | .ok ((), np) => .ok (np, p)

/-- An identifier: ASCII part and punycode part (positions in the symbol). -/
structure Ident where
  ascii : String
  puny : String
  deriving Inhabited

def digitsGo (s : ByteArray) : Nat → Nat → P → Except PErr (Nat × P)
  | 0, len, p => .ok (len, p)
  | f + 1, len, p =>
    match digit10 s p with
    | .error _ => .ok (len, p)
    | .ok (d, p) =>
      let len := len * 10 + d
      if 2 ^ 64 ≤ len then .error .invalid else digitsGo s f len p

def ident : PStep Ident := fun s p =>
  let (isPuny, p) := p.eat s 117
  match digit10 s p with
  | .error e => .error e
  | .ok (len0, p) =>
    let r := if len0 != 0 then digitsGo s (s.size + 1) len0 p else .ok (len0, p)
    match r with
    | .error e => .error e
    | .ok (len, p) =>
      let (_, p) := p.eat s 95
      let start := p.next
      if s.size < start + len then .error .invalid else
      let p := { p with next := start + len }
      let idBytes := (s.extract start (start + len)).toList
      if isPuny then
        let lastUnd := (idBytes.zipIdx.filter (·.1 == 95)).getLast?.map (·.2)
        let (a, pc) := match lastUnd with
          | some i => (idBytes.take i, idBytes.drop (i + 1))
          | none => ([], idBytes)
        if pc.isEmpty then .error .invalid else
        .ok (⟨String.fromUTF8! (ByteArray.mk a.toArray), String.fromUTF8! (ByteArray.mk pc.toArray)⟩, p)
      else .ok (⟨String.fromUTF8! (ByteArray.mk idBytes.toArray), ""⟩, p)

/-! ### Punycode -/

/-- Insert `c` at position `i`. -/
def insertAt (cs : Array Char) (i : Nat) (c : Char) : Array Char :=
  (cs.extract 0 i).push c ++ cs.extract i cs.size

/-- One punycode delta (`loop` over digits): the delta and the remaining digits. -/
def punyDelta (bias : Nat) : Nat → Nat → Nat → Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _, _, _, _ => none
  | f + 1, delta, w, k, ds =>
    let k := k + 36
    let t := min (max (k - bias) 1) 26
    match ds with
    | [] => none
    | d :: ds =>
      let dv := if isLower d then some (d.toNat - 97) else if isDigit d then some (26 + d.toNat - 48)
        else none
      match dv with
      | none => none
      | some dv =>
        let delta := delta + dv * w
        if 2 ^ 64 ≤ delta then none else
        if dv < t then some (delta, ds) else
        let w := w * (36 - t)
        if 2 ^ 64 ≤ w then none else punyDelta bias f delta w k ds

/-- The punycode decoding loop (RFC 3492 as rustc-demangle runs it, with at most 128 output
characters for the display). -/
def punyGo : Nat → Array Char → Nat → Nat → Nat → Nat → List UInt8 → Option (Array Char)
  | 0, _, _, _, _, _, _ => none
  | f + 1, out, i, n, bias, damp, ds =>
    match punyDelta bias 64 0 1 0 ds with
    | none => none
    | some (delta, ds) =>
      let len := out.size + 1
      let i := i + delta
      if 2 ^ 64 ≤ i then none else
      let n := n + i / len
      if 2 ^ 64 ≤ n then none else
      let i := i % len
      if h : n < 2 ^ 32 ∧ n.isValidChar then
        if 128 ≤ out.size then none else
        let out := insertAt out i (Char.ofNatAux n h.2)
        let i := i + 1
        if ds.isEmpty then some out else
        let delta := delta / damp
        let delta := delta + delta / len
        let rec adapt : Nat → Nat → Nat → Nat × Nat
          | 0, d, k => (d, k)
          | g + 1, d, k => if d > (35 * 26) / 2 then adapt g (d / 35) (k + 36) else (d, k)
        let (delta, k) := adapt 64 delta 0
        let bias := k + (36 * delta) / (delta + 38)
        punyGo f out i n bias 2 ds
      else none

/-- `try_small_punycode_decode`: the decoded characters, if decoding succeeds within 128. -/
def punyDecode (id : Ident) : Option (Array Char) :=
  if id.puny.isEmpty then none else
  let a := id.ascii.toList.toArray
  if 128 < a.size then none else
  punyGo (id.puny.length + 1) a 0 0x80 72 700 id.puny.toUTF8.toList

/-- `Ident`'s `Display`. Decoded characters are written one at a time. -/
def Ident.show (id : Ident) (o : Out) : Out :=
  match punyDecode id with
  | some cs => cs.foldl (fun o c => o.write c.toString) o
  | none =>
    if !id.puny.isEmpty then
      let o := o.write "punycode{"
      let o := if !id.ascii.isEmpty then (o.write id.ascii).write "-" else o
      (o.write id.puny).write "}"
    else o.write id.ascii

/-! ### Constants -/

/-- `HexNibbles::try_parse_uint`. -/
def parseUint (nib : List UInt8) : Option Nat :=
  let n := nib.dropWhile (· == 48)
  if 16 < n.length then none
  else some (n.foldl (fun v c => 16 * v + (if isDigit c then c.toNat - 48 else c.toNat - 87)) 0)

/-- The UTF-8 length announced by a first byte. -/
def utf8LenOf (b : UInt8) : Option Nat :=
  if b < 0x80 then some 1 else if b < 0xc0 then none else if b < 0xe0 then some 2
  else if b < 0xf0 then some 3 else if b < 0xf8 then some 4 else none

/-- `HexNibbles::try_parse_str_chars`: the characters, if every one decodes. -/
def parseStrChars (nib : List UInt8) : Option (List Char) :=
  if nib.length % 2 != 0 then none else
  let half (c : UInt8) : Nat := if isDigit c then c.toNat - 48 else c.toNat - 87
  let rec bytes : List UInt8 → List UInt8
    | a :: b :: r => (16 * half a + half b).toUInt8 :: bytes r
    | _ => []
  let rec chars : Nat → List UInt8 → Option (List Char)
    | _, [] => some []
    | 0, _ :: _ => none
    | f + 1, b :: r =>
      match utf8LenOf b with
      | none => none
      | some k =>
        let u := (b :: r).take k
        if u.length < k then none else
        match String.fromUTF8? (ByteArray.mk u.toArray) with
        | none => none
        | some str =>
          match str.toList with
          | [c] => (chars f ((b :: r).drop k)).map (c :: ·)
          | _ => none
  let bs := bytes nib
  chars (bs.length + 1) bs

/-- `char::escape_debug` (ASCII exact; see the module note for other characters). -/
def escapeDebug (c : Char) : String :=
  match c with
  | '\x00' => "\\0" | '\t' => "\\t" | '\r' => "\\r" | '\n' => "\\n" | '\\' => "\\\\"
  | '"' => "\\\"" | '\'' => "\\'"
  | c => if isControl c then "\\u{" ++ hexStr c.toNat ++ "}" else c.toString

/-! ### The printer -/

/-- The printer's state: the parser (or the error it stopped at), whether it prints, the bound
lifetime depth and the output. -/
structure PrSt where
  parser : Except PErr P
  out : Bool
  bld : Nat
  o : Out
  /-- The alternate format (`{:#}`): no crate disambiguators, no integer type suffixes. -/
  alt : Bool := false
  deriving Inhabited

/-- The printer over the symbol `s`. -/
abbrev PM := ReaderT ByteArray (StateM PrSt)

/-- `print`: write when printing. -/
def pr (x : String) : PM Unit :=
  modify fun st => if st.out then { st with o := st.o.write x } else st

/-- Whether output is live (printing and the size limit not reached). -/
def live : PM Bool := do let st ← get; pure (st.out && !st.o.failed)

/-- `parse!`: run a parser step; on an error print its message (or `?` if the parser had
already failed) and give `none`. -/
def parseM {α : Type} (f : PStep α) : PM (Option α) := do
  let s ← read
  let st ← get
  match st.parser with
  | .error _ => pr "?"; pure none
  | .ok p =>
    match f s p with
    | .ok (a, p') => set { st with parser := .ok p' }; pure (some a)
    | .error e => pr e.message; modify fun st => { st with parser := .error e }; pure none

/-- `invalid!`. -/
def invalid : PM Unit := do
  pr PErr.invalid.message
  modify fun st => { st with parser := .error .invalid }

/-- `Printer::eat`. -/
def eatM (b : UInt8) : PM Bool := do
  let s ← read
  let st ← get
  match st.parser with
  | .ok p => let (e, p) := p.eat s b; set { st with parser := .ok p }; pure e
  | .error _ => pure false

def popDepth : PM Unit :=
  modify fun st => match st.parser with
    | .ok p => { st with parser := .ok { p with depth := p.depth - 1 } }
    | .error _ => st

def parserOk : PM Bool := do pure (← get).parser.toBool

/-- `print_lifetime_from_index`. -/
def printLifetime (lt : Nat) : PM Unit := do
  if !(← get).out then return
  pr "'"
  if lt == 0 then pr "_"; return
  let bld := (← get).bld
  if lt ≤ bld then
    let depth := bld - lt
    if depth < 26 then pr (Char.ofNat (97 + depth)).toString
    else pr "_"; pr (toString depth)
  else invalid

/-- `print_quoted_escaped_chars`. -/
def printQuoted (q : Char) (cs : List Char) : PM Unit := do
  if !(← get).out then return
  pr q.toString
  for c in cs do
    if (q == '\'' && c == '"') || (q == '"' && c == '\'') then pr c.toString
    else
      for e in (escapeDebug c).toList do pr e.toString
  pr q.toString

def basicType (t : UInt8) : Option String :=
  match t.toNat with
  | 98 => "bool" | 99 => "char" | 101 => "str" | 117 => "()" | 97 => "i8" | 115 => "i16"
  | 108 => "i32" | 120 => "i64" | 110 => "i128" | 105 => "isize" | 104 => "u8" | 116 => "u16"
  | 109 => "u32" | 121 => "u64" | 111 => "u128" | 106 => "usize" | 102 => "f32" | 100 => "f64"
  | 122 => "!" | 112 => "_" | 118 => "..."
  | _ => none

/-- `print_const_uint`. -/
def printConstUint (tag : UInt8) : PM Unit := do
  let some (a, b) ← parseM hexNibbles | return
  let s ← read
  let nib := (s.extract a b).toList
  match parseUint nib with
  | some v => pr (toString v)
  | none => pr "0x"; pr (String.fromUTF8! (ByteArray.mk nib.toArray))
  if (← get).out && !(← get).alt then pr ((basicType tag).getD "")

/-- `print_const_str_literal`. -/
def printConstStr : PM Unit := do
  let some (a, b) ← parseM hexNibbles | return
  let s ← read
  match parseStrChars (s.extract a b).toList with
  | some cs => printQuoted '"' cs
  | none => invalid

/-- A loop bound for `print_sep_list` (each iteration consumes input or stops). -/
def loopFuel (s : ByteArray) : Nat := s.size + 1

mutual
/-- `print_sep_list`, with an iteration bound. -/
def sepList (fuel : Nat) (k : Nat) (item : Nat) (sep : String) (i : Nat) : PM Nat :=
  match k with
  | 0 => pure i
  | k + 1 => do
    if !(← parserOk) then return i
    if (← eatM 69) then return i
    if i > 0 then pr sep
    runItem fuel item
    sepList fuel k item sep (i + 1)
  termination_by (fuel, 1, k)

/-- The list items `print_sep_list` is used with: 0 generic arg, 1 type, 2 const in value,
3 dyn trait, 4 const struct field. -/
def runItem (fuel : Nat) (item : Nat) : PM Unit :=
  match fuel with
  | 0 => pure ()
  | f + 1 =>
    match item with
    | 0 => printGenericArg f
    | 1 => printType f
    | 2 => printConst f true
    | 3 => printDynTrait f
    | _ => do
      let some _ ← parseM disambiguator | return
      let some name ← parseM ident | return
      modify fun st => if st.out then { st with o := name.show st.o } else st
      pr ": "
      printConst f true
  termination_by (fuel, 0, 0)

/-- `print_backref` applied to one of the printers: 0 path, 1 type, 2 const,
3 path-maybe-open-generics (whose result is returned). -/
def printBackref (fuel : Nat) (what : Nat) (inValue : Bool) : PM Bool :=
  match fuel with
  | 0 => pure false
  | f + 1 => do
    let some bp ← parseM backref | return false
    if !(← live) then return false
    let orig := (← get).parser
    modify fun st => { st with parser := .ok bp }
    let r ← match what with
      | 0 => do printPath f inValue; pure false
      | 1 => do printType f; pure false
      | 2 => do printConst f inValue; pure false
      | _ => printPathMaybeOpen f
    modify fun st => { st with parser := orig }
    pure r
  termination_by (fuel, 0, 0)

/-- `in_binder` around a function type (`what = 0`) or a `dyn` trait list (`what = 1`). -/
def inBinder (fuel : Nat) (what : Nat) : PM Unit :=
  match fuel with
  | 0 => pure ()
  | f + 1 => do
    let some n ← parseM (optInteger62 71) | return
    if !(← get).out then
      if what == 0 then fnBody f else let _ ← sepList f (loopFuel (← read)) 3 " + " 0
      return
    if n > 0 then
      pr "for<"
      for i in List.range n do
        if i > 0 then pr ", "
        modify fun st => { st with bld := st.bld + 1 }
        printLifetime 1
      pr "> "
    if what == 0 then fnBody f else let _ ← sepList f (loopFuel (← read)) 3 " + " 0
    modify fun st => { st with bld := st.bld - n }
  termination_by (fuel, 0, 0)

/-- The body of a function type inside its binder. -/
def fnBody (fuel : Nat) : PM Unit := do
  let isUnsafe ← eatM 85
  let mut abi : Option String := none
  if (← eatM 75) then
    if (← eatM 67) then abi := some "C"
    else
      let some a ← parseM ident | return
      if a.ascii.isEmpty || !a.puny.isEmpty then invalid; return
      abi := some a.ascii
  if isUnsafe then pr "unsafe "
  if let some a := abi then
    pr "extern \""
    let parts := a.splitOn "_"
    pr (parts.headD "")
    for part in parts.drop 1 do
      pr "-"; pr part
    pr "\" "
  pr "fn("
  let _ ← sepList fuel (loopFuel (← read)) 1 ", " 0
  pr ")"
  if (← eatM 117) then pure () else
    pr " -> "
    printType fuel
  termination_by (fuel, 2, 0)

/-- `print_path`. -/
def printPath (fuel : Nat) (inValue : Bool) : PM Unit :=
  match fuel with
  | 0 => do pr PErr.tooDeep.message; modify fun st => { st with parser := .error .tooDeep }
  | f + 1 => do
    let some () ← parseM pushDepth | return
    let some tag ← parseM pNext | return
    match tag.toNat with
    | 67 => -- C
      let some dis ← parseM disambiguator | return
      let some name ← parseM ident | return
      modify fun st => if st.out then { st with o := name.show st.o } else st
      if (← get).out && !(← get).alt && dis != 0 then
        pr "["; pr (hexStr dis); pr "]"
    | 78 => -- N
      let some ns ← parseM pNamespace | return
      printPath f inValue
      if !(← parserOk) then pr "::"
      let some dis ← parseM disambiguator | return
      let some name ← parseM ident | return
      match ns with
      | some c =>
        pr "::{"
        if c == 'C' then pr "closure" else if c == 'S' then pr "shim" else pr c.toString
        if !name.ascii.isEmpty || !name.puny.isEmpty then
          pr ":"
          modify fun st => if st.out then { st with o := name.show st.o } else st
        pr "#"; pr (toString dis); pr "}"
      | none =>
        if !name.ascii.isEmpty || !name.puny.isEmpty then
          pr "::"
          modify fun st => if st.out then { st with o := name.show st.o } else st
    | 77 | 88 | 89 => -- M X Y
      if tag.toNat != 89 then
        let some _ ← parseM disambiguator | return
        let out ← (fun st => st.out) <$> get
        modify fun st => { st with out := false }
        printPath f false
        modify fun st => { st with out := out }
      pr "<"
      printType f
      if tag.toNat != 77 then
        pr " as "
        printPath f false
      pr ">"
    | 73 => -- I
      printPath f inValue
      if inValue then pr "::"
      pr "<"
      let _ ← sepList f (loopFuel (← read)) 0 ", " 0
      pr ">"
    | 66 => -- B
      let _ ← printBackref f 0 inValue
    | _ => invalid; return
    popDepth
  termination_by (fuel, 0, 0)

/-- `print_generic_arg`. -/
def printGenericArg (fuel : Nat) : PM Unit := do
  if (← eatM 76) then
    let some lt ← parseM integer62 | return
    printLifetime lt
  else if (← eatM 75) then printConst fuel false
  else printType fuel
  termination_by (fuel, 2, 0)

/-- `print_type`. -/
def printType (fuel : Nat) : PM Unit :=
  match fuel with
  | 0 => do pr PErr.tooDeep.message; modify fun st => { st with parser := .error .tooDeep }
  | f + 1 => do
    if (← eatM 119) then pr "#[splat] "
    let some tag ← parseM pNext | return
    if let some ty := basicType tag then pr ty; return
    let some () ← parseM pushDepth | return
    match tag.toNat with
    | 82 | 81 => -- R Q
      pr "&"
      if (← eatM 76) then
        let some lt ← parseM integer62 | return
        if lt != 0 then printLifetime lt; pr " "
      if tag.toNat != 82 then pr "mut "
      printType f
    | 80 | 79 => -- P O
      pr "*"
      if tag.toNat != 80 then pr "mut " else pr "const "
      printType f
    | 65 | 83 => -- A S
      pr "["
      printType f
      if tag.toNat == 65 then pr "; "; printConst f true
      pr "]"
    | 84 => -- T
      pr "("
      let count ← sepList f (loopFuel (← read)) 1 ", " 0
      if count == 1 then pr ","
      pr ")"
    | 70 => inBinder f 0 -- F
    | 68 => -- D
      pr "dyn "
      inBinder f 1
      if !(← eatM 76) then invalid; return
      let some lt ← parseM integer62 | return
      if lt != 0 then pr " + "; printLifetime lt
    | 66 => let _ ← printBackref f 1 false -- B
    | 87 => -- W
      printType f
      pr " is "
      printPat f
    | _ =>
      modify fun st => match st.parser with
        | .ok p => { st with parser := .ok { p with next := p.next - 1 } }
        | .error _ => st
      printPath f false
    popDepth
  termination_by (fuel, 0, 0)

/-- `print_path_maybe_open_generics`. -/
def printPathMaybeOpen (fuel : Nat) : PM Bool :=
  match fuel with
  | 0 => pure false
  | f + 1 => do
    if (← eatM 66) then printBackref f 3 false
    else if (← eatM 73) then
      printPath f false
      pr "<"
      let _ ← sepList f (loopFuel (← read)) 0 ", " 0
      pure true
    else
      printPath f false
      pure false
  termination_by (fuel, 0, 0)

/-- `print_dyn_trait`. -/
def printDynTrait (fuel : Nat) : PM Unit := do
  let mut open_ ← printPathMaybeOpen fuel
  for _ in List.range (loopFuel (← read)) do
    if !(← eatM 112) then break
    if !open_ then pr "<"; open_ := true else pr ", "
    let some name ← parseM ident | return
    modify fun st => if st.out then { st with o := name.show st.o } else st
    pr " = "
    if (← eatM 75) then printConst fuel false else printType fuel
  if open_ then pr ">"
  termination_by (fuel, 2, 0)

/-- `print_pat`. -/
def printPat (fuel : Nat) : PM Unit :=
  match fuel with
  | 0 => pure ()
  | f + 1 => do
    let some tag ← parseM pNext | return
    match tag.toNat with
    | 82 => printConst f false; pr "..="; printConst f false
    | 79 =>
      let some () ← parseM pushDepth | return
      printPat f
      for _ in List.range (loopFuel (← read)) do
        if (← eatM 69) then break
        if !(← parserOk) then invalid; return
        pr " | "
        printPat f
      popDepth
    | 78 => pr "!null"
    | _ => invalid
  termination_by (fuel, 0, 0)

/-- `print_const`. -/
def printConst (fuel : Nat) (inValue : Bool) : PM Unit :=
  match fuel with
  | 0 => do pr PErr.tooDeep.message; modify fun st => { st with parser := .error .tooDeep }
  | f + 1 => do
    let some tag ← parseM pNext | return
    let some () ← parseM pushDepth | return
    let mut opened := false
    let t := tag.toNat
    if t == 112 then pr "_"
    else if t ∈ [104, 116, 109, 121, 111, 106] then printConstUint tag
    else if t ∈ [97, 115, 108, 120, 110, 105] then
      if (← eatM 110) then pr "-"
      printConstUint tag
    else if t == 98 then
      let some (a, b) ← parseM hexNibbles | return
      match parseUint ((← read).extract a b).toList with
      | some 0 => pr "false"
      | some 1 => pr "true"
      | _ => invalid; return
    else if t == 99 then
      let some (a, b) ← parseM hexNibbles | return
      let v := parseUint ((← read).extract a b).toList
      match v with
      | some v =>
        if h : v < 2 ^ 32 ∧ v.isValidChar then printQuoted '\'' [Char.ofNatAux v h.2]
        else invalid; return
      | none => invalid; return
    else if t == 101 then
      if !inValue then opened := true; pr "{"
      pr "*"
      printConstStr
    else if t == 82 || t == 81 then
      if t == 82 && (← eatM 101) then printConstStr
      else
        if !inValue then opened := true; pr "{"
        pr "&"
        if t != 82 then pr "mut "
        printConst f true
    else if t == 65 then
      if !inValue then opened := true; pr "{"
      pr "["
      let _ ← sepList f (loopFuel (← read)) 2 ", " 0
      pr "]"
    else if t == 84 then
      if !inValue then opened := true; pr "{"
      pr "("
      let count ← sepList f (loopFuel (← read)) 2 ", " 0
      if count == 1 then pr ","
      pr ")"
    else if t == 86 then
      if !inValue then opened := true; pr "{"
      printPath f true
      let some k ← parseM pNext | return
      if k.toNat == 85 then pure ()
      else if k.toNat == 84 then
        pr "("
        let _ ← sepList f (loopFuel (← read)) 2 ", " 0
        pr ")"
      else if k.toNat == 83 then
        pr " { "
        let _ ← sepList f (loopFuel (← read)) 4 ", " 0
        pr " }"
      else invalid; return
    else if t == 66 then
      let _ ← printBackref f 2 inValue
    else invalid; return
    if opened then pr "}"
    popDepth
  termination_by (fuel, 0, 0)
end

/-- The recursion budget: depth 500 times the printer frames between two depth pushes. -/
def recFuel : Nat := 4000

/-- The inner part of a v0 symbol, if it has a v0 prefix, starts with an upper-case letter and
is ASCII. -/
def v0Inner (s : List UInt8) : Option (List UInt8) := do
  let inner ← match s with
    | 95 :: 82 :: r@(_ :: _) => some r
    | 82 :: r@(_ :: _) => some r
    | 95 :: 95 :: 82 :: r@(_ :: _) => some r
    | _ => none
  match inner with
  | c :: _ => if !isUpper c then none else pure ()
  | [] => none
  if inner.any (fun c => 128 ≤ c.toNat) then none
  pure inner

/-- A run of `print_path` without output from a parser state. -/
def skipPath (s : ByteArray) (p : P) : Except PErr P :=
  let st : PrSt := { parser := .ok p, out := false, bld := 0, o := {} }
  ((printPath recFuel false).run s |>.run st).2.parser

/-- `v0::demangle`: the inner part and the suffix, if the syntax check passes. -/
def v0Parse (s : List UInt8) : Option (ByteArray × List UInt8) := do
  let inner ← v0Inner s
  let sym := ByteArray.mk inner.toArray
  let p ← (skipPath sym ⟨0, 0⟩).toOption
  let p ← if (p.peek sym).any isUpper then (skipPath sym p).toOption else pure p
  pure (sym, inner.drop p.next)

/-- `v0::Demangle`'s `Display` (`alt`: the alternate format). -/
def v0Show (sym : ByteArray) (o : Out) (alt : Bool := false) : Out :=
  let st : PrSt := { parser := .ok ⟨0, 0⟩, out := true, bld := 0, o := o, alt }
  ((printPath recFuel true).run sym |>.run st).2.o

/-! ## `try_demangle` and `to_string` -/

/-- The `.llvm.` suffix removal. -/
def stripLlvm (s : List UInt8) : List UInt8 :=
  let pat : List UInt8 := ".llvm.".toUTF8.toList
  let rec find : Nat → List UInt8 → Option Nat
    | _, [] => none
    | i, l@(_ :: r) => if pat.isPrefixOf l then some i else find (i + 1) r
  match find 0 s with
  | none => s
  | some i =>
    let cand := s.drop (i + pat.length)
    if cand.all (fun c => (65 ≤ c && c ≤ 70) || isDigit c || c == 64) then s.take i else s

/-- `is_symbol_like`. -/
def symbolLike (s : List UInt8) : Bool :=
  s.all fun c => (33 ≤ c && c ≤ 126)

/-- **`rustc_demangle::try_demangle(s).map(|d| d.to_string())`**, on the UTF-8 bytes of `s`.
Non-ASCII input is never demangled (both styles require ASCII). -/
def rustDemangle (str : String) (alt : Bool := false) : Option String :=
  let s := stripLlvm str.toUTF8.toList
  let (style, suffix) : Option (Out → Out) × List UInt8 :=
    match legacyParse s with
    | some (es, suf) => (some (legacyShow es · alt), suf)
    | none =>
      match v0Parse s with
      | some (sym, suf) => (some (v0Show sym · alt), suf)
      | none => (none, [])
  match style with
  | none => none
  | some shw =>
    if !suffix.isEmpty && !(suffix.head? == some 46 && symbolLike suffix) then none
    else some ((shw {}).finish ++ String.fromUTF8! (ByteArray.mk suffix.toArray))

end Silmaril.Wasm.Tools.Meta.Demangle

end
