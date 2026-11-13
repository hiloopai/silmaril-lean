module

public import Silmaril.Libc.Stdio.Printf.Defs

/-!
# C99 `scanf` formats, in tiers

The `scanf` directives of ISO C 7.21.6.2 (`parse`: white space, ordinary bytes, conversion
specifications with assignment suppression `*`, a field width, a length modifier and the
specifiers `d i o u x X c s [ n %`), and **what a format reads** from an input (`scan`): the
values stored (`Formats.SVal`: integers with their width in bytes, bytes for `c s [`), the
number of input items assigned, the number of conversions completed, how it stopped
(`Stop`: completed, matching failure, input failure, or `ub`) and the unread input.

* An integer conversion reads the longest prefix of the field (cut at the width) that is a
  subject sequence of `strtol` for its base (`scanIntS`; `%i` detects `0x` and `0`); a value
  out of the range of the object is undefined behaviour (7.21.6.2p10), and so is a dangling
  prefix (`-`, `0x` without a digit), on which implementations differ: both are `ub`, and a
  valid use excludes them.
* `Result` is the value `scanf` returns: the number of items assigned, or `EOF` after an input
  failure before the first conversion. When only suppressed conversions completed before an
  input failure, ISO C says `0` and glibc returns `EOF`; `Result` allows both.

**Tiers**: `leet` (`%d %ld %lld %u %x %s %c` without `*` or width), `intc` (every conversion but
the floating ones, scansets without implementation-defined ranges, `%n` neither suppressed nor
with a width); `c99` is `intc` for now: reading `a e f g` is correct rounding of decimal and
hexadecimal strings, not stated here.

**Checked against glibc 2.39.** `scan` and `Result` agree with Ubuntu 24.04's glibc 2.39
`sscanf` (return value and every stored value) on 4,500 randomly generated calls of the `intc`
tier whose outcome is defined; the test generator is not part of this library.
-/

@[expose] public section

namespace Silmaril.Libc.Stdio.Scanf

open Silmaril.X86 (Byte)
open Silmaril.Libc.Formats (ch)
open Silmaril.Libc.Stdio (isSpace isDigit digitsVal)
open Silmaril.Libc.Stdio.Printf (Len Tier len1 parseLen)

/-! ## Directives (C99 7.21.6.2p3) -/

/-- The conversion specifiers (`X` reads as `x`; `flt` is any of `a A e E f F g G`). -/
inductive Kind where
  | d | i | o | u | x | c | s | n | pct | flt
  /-- `[...]` (`neg`: `[^...]`), with its bytes. -/
  | set (neg : Bool) (bs : List Byte)
  deriving DecidableEq, Repr

/-- **A conversion specification**: assignment suppression `*`, a maximum field width, a length
modifier, the specifier. -/
structure Spec where
  skip : Bool := false
  width : Option Nat := none
  len : Len := .none
  kind : Kind
  deriving DecidableEq, Repr

/-- A directive: white space, an ordinary byte, a conversion specification. -/
inductive Item where
  | ws
  | lit (b : Byte)
  | spec (c : Spec)
  deriving DecidableEq, Repr

/-- The bytes of a scanset up to its `]` (a `]` first is a member). -/
def setBody : List Byte → Option (List Byte × List Byte)
  | [] => none
  | b :: r =>
    let body := r.takeWhile (· != ch ']')
    match r.dropWhile (· != ch ']') with
    | _ :: r' => some (b :: body, r')
    | [] => none

/-- A conversion specifier and the rest. -/
def kindOf : List Byte → Option (Kind × List Byte)
  | [] => none
  | b :: r =>
    if b = ch 'd' then some (.d, r) else if b = ch 'i' then some (.i, r)
    else if b = ch 'o' then some (.o, r) else if b = ch 'u' then some (.u, r)
    else if b = ch 'x' ∨ b = ch 'X' then some (.x, r)
    else if b = ch 'c' then some (.c, r) else if b = ch 's' then some (.s, r)
    else if b = ch 'n' then some (.n, r) else if b = ch '%' then some (.pct, r)
    else if b = ch 'a' ∨ b = ch 'A' ∨ b = ch 'e' ∨ b = ch 'E' ∨ b = ch 'f' ∨ b = ch 'F' ∨
      b = ch 'g' ∨ b = ch 'G' then some (.flt, r)
    else if b = ch '[' then
      match r with
      | c :: r' =>
        if c = ch '^' then (setBody r').map fun p => (.set true p.1, p.2)
        else (setBody r).map fun p => (.set false p.1, p.2)
      | [] => none
    else none

/-- The conversion specification after a `%`. -/
def specOf (r : List Byte) : Option (Spec × List Byte) :=
  let (sk, r) : Bool × List Byte := match r with
    | b :: r' => if b = ch '*' then (true, r') else (false, b :: r')
    | [] => (false, [])
  let ds := r.takeWhile isDigit
  let w := if ds = [] then none else some (digitsVal ds)
  let r := r.dropWhile isDigit
  let (ln, r) := parseLen r
  if w = some 0 then none
  else (kindOf r).map fun p => ({ skip := sk, width := w, len := ln, kind := p.1 }, p.2)

/-- Parse with `fuel` steps. -/
def parseAux : Nat → List Byte → Option (List Item)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, b :: rest =>
    if b = ch '%' then
      match specOf rest with
      | some (sp, r') => (parseAux k r').map (.spec sp :: ·)
      | none => none
    else if isSpace b then (parseAux k rest).map (.ws :: ·)
    else (parseAux k rest).map (.lit b :: ·)

/-- **A `scanf` format**; `none`: not a format. -/
def parse (f : List Byte) : Option (List Item) := parseAux (f.length + 1) f

/-! ## Tiers -/

/-- The length modifier fits the specifier (`hh h l ll j z t` with the integer specifiers and
`n`; none with `c s [` and `%`: `l` there reads wide characters). -/
def Spec.lenOk (c : Spec) : Bool :=
  match c.kind with
  | .d | .i | .o | .u | .x | .n => c.len != .L
  | _ => c.len == .none

/-- A scanset whose meaning is defined: no `-` except first or last (a range is
implementation-defined, 7.21.6.2p12). -/
def setOk (b : List Byte) : Bool := !((b.drop 1).dropLast.contains (ch '-'))

/-- **The leetcode tier**: `%d %ld %lld %u %x %s %c`, no `*`, no width. -/
def Spec.leet (c : Spec) : Bool :=
  !c.skip && c.width == none &&
    match c.len, c.kind with
    | .none, .d | .l, .d | .ll, .d | .none, .u | .none, .x | .none, .s | .none, .c => true
    | _, _ => false

/-- **The integer tier**: every C99 conversion but the floating ones (`d i o u x X c s [ n %`, with
`*`, widths and the integer length modifiers; `%n` not suppressed). -/
def Spec.intc (c : Spec) : Bool :=
  c.lenOk && match c.kind with
    | .flt => false
    | .set _ b => setOk b
    | .n => !c.skip && c.width == none
    | _ => true

/-- A specification of the tier. The floating conversions are not in any tier yet (reading them
is correct rounding of a decimal or hexadecimal string, not stated here), so `c99` is `intc`. -/
def Spec.inTier : Tier → Spec → Bool
  | .leet, c => c.leet
  | .intc, c => c.intc
  | .c99, c => c.intc

/-- The specifications of a format are in the tier. -/
def InTier (t : Tier) (is : List Item) : Prop := ∀ c, Item.spec c ∈ is → c.inTier t = true

/-! ## Reading -/

/-- A digit's value in `base` (2 to 16). -/
def digitIn (base : Nat) (b : Byte) : Option Nat :=
  let v := if isDigit b then some (b.toNat - 48)
    else if 97 ≤ b.toNat ∧ b.toNat ≤ 102 then some (b.toNat - 87)
    else if 65 ≤ b.toNat ∧ b.toNat ≤ 70 then some (b.toNat - 55)
    else none
  v.bind fun d => if d < base then some d else none

/-- The value of digits in `base`. -/
def valIn (base : Nat) (ds : List Byte) : Nat :=
  ds.foldl (fun v b => base * v + (digitIn base b).getD 0) 0

/-- The outcome of reading an integer subject sequence. -/
inductive IRes where
  /-- No byte of a subject sequence: a matching failure. -/
  | none
  /-- A nonempty prefix of a subject sequence that is not one (`-`, `0x` with no digit): left
  out of every tier (C calls it a matching failure after consuming bytes that cannot be pushed
  back; implementations differ). -/
  | dangle
  /-- The value and the number of bytes read. -/
  | some (v : Int) (k : Nat)

/-- **An integer subject sequence** in `s` (the input cut at the field width), as `strtol` with
the base `base` (`0`: `%i`'s detection of `0x` and `0`; `16` accepts `0x`). -/
def scanIntS (base : Nat) (s : List Byte) : IRes :=
  let (neg, sk, s) : Bool × Nat × List Byte := match s with
    | b :: r => if b = ch '-' then (true, 1, r) else if b = ch '+' then (false, 1, r) else (false, 0, s)
    | [] => (false, 0, [])
  let hx : Bool := match s with
    | z :: x :: _ => (base == 0 || base == 16) && z == ch '0' && (x == ch 'x' || x == ch 'X')
    | _ => false
  let base := if hx then 16 else if base == 0 then (if s.head? == some (ch '0') then 8 else 10) else base
  let s' := if hx then s.drop 2 else s
  let ds := s'.takeWhile fun b => (digitIn base b).isSome
  if ds = [] then (if sk + (if hx then 2 else 0) = 0 then .none else .dangle)
  else
    let v := valIn base ds
    .some (if neg then -(v : Int) else v) (sk + (if hx then 2 else 0) + ds.length)

/-- How a format stopped. -/
inductive Stop where
  | ok
  /-- A matching failure. -/
  | mfail
  /-- An input failure (end of input). -/
  | ifail
  /-- Undefined (or left out): a value out of range, a dangling subject sequence. -/
  | ub
  deriving DecidableEq, Repr

/-- **The outcome of reading a format**: the values stored (`Formats.SVal`: an integer stored in
`w` bytes, or bytes), the counts, how it stopped, the unread input. -/
structure Out where
  /-- The values stored, in order (`%n` included). -/
  vs : List Silmaril.Libc.Formats.SVal
  /-- The number of input items assigned (`%n` not included). -/
  cnt : Nat
  /-- The number of conversions completed, assigned or suppressed (not `%n`, `%%`). -/
  done : Nat
  stop : Stop
  rest : List Byte

/-- The value an integer conversion assigns, if it fits (`none`: undefined, 7.21.6.2p10). -/
def intVal (k : Kind) (ln : Len) (v : Int) : Option Silmaril.Libc.Formats.SVal :=
  let w := ln.bits
  match k with
  | .d | .i => if -(2 ^ (w - 1) : Int) ≤ v ∧ v < (2 ^ (w - 1) : Int) then some (.int v (w / 8)) else none
  | _ => if 0 ≤ v ∧ v < (2 ^ w : Int) then some (.int v (w / 8)) else none

/-- One conversion from `inp`: `some (value, unread)` (`value` `none` for `%%`), or a stop. The
input read so far is `pos` bytes (`%n`). -/
def convOne (c : Spec) (pos : Nat) (inp : List Byte) : Except Stop (Option Silmaril.Libc.Formats.SVal × List Byte) :=
  let w := c.width
  match c.kind with
  | .n => .ok (some (.int pos (c.len.bits / 8)), inp)
  | .c =>
    let k := w.getD 1
    if inp = [] then .error .ifail
    else if inp.length < k then .error .ub
    else .ok (some (.bytes (inp.take k)), inp.drop k)
  | .set neg b =>
    let ok := fun x => b.contains x != neg
    let t := (inp.takeWhile ok)
    let t := match w with
      | some k => t.take k
      | none => t
    if t = [] then .error (if inp = [] then .ifail else .mfail)
    else .ok (some (.bytes (t ++ [0])), inp.drop t.length)
  | k =>
    let r := inp.dropWhile isSpace
    match r with
    | [] => .error .ifail
    | b :: _ =>
      match k with
      | .pct => if b = ch '%' then .ok (none, r.drop 1) else .error .mfail
      | .s =>
        let t := r.takeWhile fun x => !isSpace x
        let t := match w with
          | some k => t.take k
          | none => t
        .ok (some (.bytes (t ++ [0])), r.drop t.length)
      | .d | .i | .o | .u | .x =>
        let base := match k with
          | .d | .u => 10
          | .i => 0
          | .o => 8
          | _ => 16
        let s := match w with
          | some k => r.take k
          | none => r
        match scanIntS base s with
        | .none => .error .mfail
        | .dangle => .error .ub
        | .some v n =>
          match intVal k c.len v with
          | some sv => .ok (some sv, r.drop n)
          | none => .error .ub
      | _ => .error .ub

/-- **Reading the directives** `is` from `inp` (`n0`: the length of the whole input, for `%n`). -/
def scanAux (n0 : Nat) : List Item → List Byte → Out
  | [], inp => ⟨[], 0, 0, .ok, inp⟩
  | .ws :: is, inp => scanAux n0 is (inp.dropWhile isSpace)
  | .lit b :: is, inp =>
    match inp with
    | x :: r => if x = b then scanAux n0 is r else ⟨[], 0, 0, .mfail, inp⟩
    | [] => ⟨[], 0, 0, .ifail, []⟩
  | .spec c :: is, inp =>
    match convOne c (n0 - inp.length) inp with
    | .error st => ⟨[], 0, 0, st, inp⟩
    | .ok (v, r) =>
      let o := scanAux n0 is r
      let cnt := if c.kind == .n || c.kind == .pct then 0 else 1
      match v with
      | some sv => if c.skip then { o with done := o.done + cnt }
        else { o with vs := sv :: o.vs, cnt := o.cnt + cnt, done := o.done + cnt }
      | none => o

/-- **What a format reads** from `inp`. -/
def scan (is : List Item) (inp : List Byte) : Out := scanAux inp.length is inp

/-- **`scanf`'s result** for the outcome `o`: the number of values assigned (`%n` not counted),
or `EOF` (`-1`) after an input failure before any conversion completed. After an input failure
with conversions completed (suppressed only) but nothing assigned, `0` or `EOF` (glibc returns
`EOF`). -/
def Result (o : Out) (r : Int) : Prop :=
  if o.stop = .ifail ∧ o.cnt = 0 then (o.done = 0 → r = -1) ∧ (r = -1 ∨ r = 0) else r = o.cnt

end Silmaril.Libc.Stdio.Scanf
