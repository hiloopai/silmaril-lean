module

public import Silmaril.Libc.Stdio.Defs
public import Silmaril.Libc.Formats.Defs

/-!
# C99 `printf` formats, in tiers

The `printf` conversion specifications of ISO C 7.21.6.1 (C99/C11, as POSIX.1-2017 aligns with
them): the parser (`parse`: flags `- + space # 0`, field width and precision, both possibly `*`,
the length modifiers `hh h l ll j z t L`, every specifier), and the **text** of a format with
its arguments (`render`), byte for byte:

* integers (`intText`): `d i` signed, `o u x X` unsigned, of the width the length modifier
  names (an argument is read as the promoted type and converted), with precision (the minimum
  number of digits, none for `0` with precision `0`), `#` (`0` for `o`, `0x`/`0X` for nonzero
  `x X`), the sign flags and zero padding (ignored with a precision or `-`);
* `c` (the `int` as `unsigned char`), `s` (at most the precision's bytes);
* `f F e E g G` (`floatText`) of an IEEE binary64 `double` or an x87 80-bit `long double`
  (`decode64`, `decode80`), **exactly**: the value is the fraction `a / b`, rounded to the
  digits printed with ties to even (the default rounding mode); `g` chooses the style by the
  exponent and removes trailing zeros; infinities and NaNs print as `inf`/`nan` (`INF`/`NAN`)
  with their sign and are never zero-padded;
* `p` by an implementation-defined text (`pt`; `glibcPtr` is glibc's).

**Tiers** (`Tier`), each allowing more formats, so each a stronger contract: `leet` (the
leetcode formats `%d %ld %lld %u %x %s %c`, no flags, width or precision), `intc` (every
integer, character and string conversion with any defined flags, width and precision), `c99`
(also the decimal floating conversions). A tier contains only defined uses (`Spec.flagsOk`);
`%a %A` (implementation-defined digits) and `%n` (a store) are in no tier, and neither is `#`
with `g G`: glibc 2.39 prints `%#g` of `999999.5` as `1.e+06`, not ISO C's `1.00000e+06`.

**Checked against glibc 2.39.** The text agrees byte for byte with Ubuntu 24.04's glibc 2.39
`printf` on 10,500 randomly generated calls (every specifier of the `c99` tier, the flags,
widths and precisions including `*`, the length modifiers, `long double`, random `double` bit
patterns, the subnormal, infinite and NaN values); the test generator is not part of this
library.
-/

@[expose] public section

namespace Silmaril.Libc.Stdio.Printf

open Silmaril.X86 (Byte)
open Silmaril.Libc.Formats (ch)
open Silmaril.Libc.Stdio (isDigit digitsVal)

/-! ## The conversion specifications (C99 7.21.6.1p4) -/

/-- The flags `-`, `+`, space, `#`, `0`. -/
structure Flags where
  minus : Bool := false
  plus : Bool := false
  space : Bool := false
  hash : Bool := false
  zero : Bool := false
  deriving DecidableEq, Repr

/-- A field width or a precision: absent, a decimal number, or `*` (taken from an argument). -/
inductive Count where
  | none
  | lit (n : Nat)
  | star
  deriving DecidableEq, Repr

/-- The length modifiers. -/
inductive Len where
  | none | hh | h | l | ll | j | z | t | L
  deriving DecidableEq, Repr

/-- The conversion specifiers. -/
inductive Kind where
  | d | i | o | u | x | X | f | F | e | E | g | G | a | A | c | s | p | n
  deriving DecidableEq, Repr

/-- **A conversion specification**: flags, field width, precision, length modifier, specifier. -/
structure Spec where
  flags : Flags := {}
  width : Count := .none
  prec : Count := .none
  len : Len := .none
  kind : Kind
  deriving DecidableEq, Repr

/-- A piece of a format: an ordinary byte (`%%` is the byte `%`) or a conversion. -/
inductive Item where
  | lit (b : Byte)
  | spec (c : Spec)
  deriving DecidableEq, Repr

/-! ## Parsing -/

/-- One flag byte. -/
def flagOf (fl : Flags) (b : Byte) : Option Flags :=
  if b = ch '-' then some { fl with minus := true }
  else if b = ch '+' then some { fl with plus := true }
  else if b = ch ' ' then some { fl with space := true }
  else if b = ch '#' then some { fl with hash := true }
  else if b = ch '0' then some { fl with zero := true }
  else none

/-- The flags, in any order and repeated. -/
def parseFlags : Flags → List Byte → Flags × List Byte
  | fl, [] => (fl, [])
  | fl, b :: r => match flagOf fl b with
    | some fl' => parseFlags fl' r
    | none => (fl, b :: r)

/-- A field width: `*` or a nonempty run of digits. -/
def parseCount : List Byte → Count × List Byte
  | [] => (.none, [])
  | b :: r =>
    if b = ch '*' then (.star, r)
    else
      let ds := (b :: r).takeWhile isDigit
      if ds = [] then (.none, b :: r) else (.lit (digitsVal ds), (b :: r).dropWhile isDigit)

/-- A precision: `.` then `*` or digits (none: `0`). -/
def parsePrec : List Byte → Count × List Byte
  | [] => (.none, [])
  | b :: r =>
    if b = ch '.' then
      match parseCount r with
      | (.none, r') => (.lit 0, r')
      | q => q
    else (.none, b :: r)

/-- A one-byte length modifier. -/
def len1 (b : Byte) : Option Len :=
  if b = ch 'h' then some .h
  else if b = ch 'l' then some .l
  else if b = ch 'j' then some .j
  else if b = ch 'z' then some .z
  else if b = ch 't' then some .t
  else if b = ch 'L' then some .L
  else none

/-- A length modifier. -/
def parseLen : List Byte → Len × List Byte
  | [] => (.none, [])
  | [b] => match len1 b with
    | some m => (m, [])
    | none => (.none, [b])
  | b :: c :: r =>
    if b = ch 'h' ∧ c = ch 'h' then (.hh, r)
    else if b = ch 'l' ∧ c = ch 'l' then (.ll, r)
    else match len1 b with
      | some m => (m, c :: r)
      | none => (.none, b :: c :: r)

/-- A conversion specifier. -/
def kindOf (b : Byte) : Option Kind :=
  if b = ch 'd' then some .d else if b = ch 'i' then some .i
  else if b = ch 'o' then some .o else if b = ch 'u' then some .u
  else if b = ch 'x' then some .x else if b = ch 'X' then some .X
  else if b = ch 'f' then some .f else if b = ch 'F' then some .F
  else if b = ch 'e' then some .e else if b = ch 'E' then some .E
  else if b = ch 'g' then some .g else if b = ch 'G' then some .G
  else if b = ch 'a' then some .a else if b = ch 'A' then some .A
  else if b = ch 'c' then some .c else if b = ch 's' then some .s
  else if b = ch 'p' then some .p else if b = ch 'n' then some .n
  else none

/-- The conversion specification after a `%`. -/
def specOf (r : List Byte) : Option (Spec × List Byte) :=
  let (fl, r) := parseFlags {} r
  let (w, r) := parseCount r
  let (p, r) := parsePrec r
  let (ln, r) := parseLen r
  match r with
  | b :: r => (kindOf b).map fun k => ({ flags := fl, width := w, prec := p, len := ln, kind := k }, r)
  | [] => none

/-- Parse with `fuel` steps. -/
def parseAux : Nat → List Byte → Option (List Item)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, b :: rest =>
    if b = ch '%' then
      match rest with
      | c :: r =>
        if c = ch '%' then (parseAux k r).map (.lit b :: ·)
        else match specOf rest with
          | some (sp, r') => (parseAux k r').map (.spec sp :: ·)
          | none => none
      | [] => none
    else (parseAux k rest).map (.lit b :: ·)

/-- **A `printf` format** (the bytes before its terminating zero); `none`: not a format. -/
def parse (f : List Byte) : Option (List Item) := parseAux (f.length + 1) f

/-! ## Valid specifications and the tiers -/

/-- `d i o u x X`. -/
def Kind.isInt : Kind → Bool
  | .d | .i | .o | .u | .x | .X => true
  | _ => false

/-- `d i`. -/
def Kind.isSigned : Kind → Bool
  | .d | .i => true
  | _ => false

/-- `f F e E g G` (`a A` are not in any tier: their digits are implementation-defined). -/
def Kind.isFloat : Kind → Bool
  | .f | .F | .e | .E | .g | .G => true
  | _ => false

/-- `o x X` and the floating specifiers (`#` is defined for them). -/
def Kind.hashOk : Kind → Bool
  | .o | .x | .X | .f | .F | .e | .E | .g | .G => true
  | _ => false

/-- The upper-case floating specifiers. -/
def Kind.upper : Kind → Bool
  | .F | .E | .G => true
  | _ => false

/-- **The flags and the precision are defined** for the specifier (7.21.6.1p6: `#` only with
`o x X` and the floating specifiers, `0` only with the numeric ones; a precision only with the
numeric ones and `s`), and not `#` with `g G`: glibc 2.39 prints `%#g` of `999999.5` as
`1.e+06` where ISO C requires `1.00000e+06` (the trailing zeros are lost when rounding carries
into a new digit), so the tiers leave that combination out. -/
def Spec.flagsOk (c : Spec) : Bool :=
  (!c.flags.hash || c.kind.hashOk) && (!c.flags.zero || c.kind.isInt || c.kind.isFloat) &&
    !(c.flags.hash && (c.kind == .g || c.kind == .G)) &&
    (c.prec == .none || c.kind.isInt || c.kind.isFloat || c.kind == .s)

/-- **The leetcode tier**: `%d %ld %lld %u %x %s %c` without flags, width or precision. -/
def Spec.leet (c : Spec) : Bool :=
  c.flags == {} && c.width == .none && c.prec == .none &&
    match c.len, c.kind with
    | .none, .d | .l, .d | .ll, .d | .none, .u | .none, .x | .none, .s | .none, .c => true
    | _, _ => false

/-- **The integer tier**: every C99 integer, character and string conversion (`d i o u x X`
with any flags, width, precision and integer length modifier; `c s` without a length modifier). -/
def Spec.intc (c : Spec) : Bool :=
  c.flagsOk && match c.kind with
    | .d | .i | .o | .u | .x | .X => c.len != .L
    | .c | .s => c.len == .none
    | _ => false

/-- **The C99 tier**: the integer tier and the decimal floating conversions `f F e E g G`
(`double`, or `long double` with `L`). -/
def Spec.c99 (c : Spec) : Bool :=
  c.intc || (c.flagsOk && c.kind.isFloat && (c.len == .none || c.len == .l || c.len == .L))

/-- **`%p`** with at most the `-` flag and a width (its text is implementation-defined). -/
def Spec.ptr (c : Spec) : Bool :=
  c.kind == .p && !c.flags.plus && !c.flags.space && !c.flags.hash && !c.flags.zero &&
    c.prec == .none && c.len == .none

/-- **The format tiers**, each a stronger contract than the one before. -/
inductive Tier where
  | leet
  | intc
  | c99
  deriving DecidableEq, Repr

/-- The position of a tier. -/
def Tier.rank : Tier → Nat
  | .leet => 0
  | .intc => 1
  | .c99 => 2

/-- `t ≤ t'`: `t'` allows every format `t` does. -/
def Tier.le (t t' : Tier) : Prop := t.rank ≤ t'.rank

/-- A specification of the tier. -/
def Spec.inTier : Tier → Spec → Bool
  | .leet, c => c.leet
  | .intc, c => c.intc
  | .c99, c => c.c99

/-! ## The arguments -/

/-- **A `printf` argument**: an integer (`d i o u x X c` and `*` widths: its value as the
promoted type, signed or unsigned), a `double`, an x87 `long double`, the bytes of a string
before its zero (`s`), a pointer (`p`). -/
inductive PArg where
  | int (v : Int)
  | dbl (b : BitVec 64)
  | ldbl (b : BitVec 80)
  | str (s : List Byte)
  | ptr (p : Nat)

/-! ## Text -/

/-- The bytes of an ASCII string. -/
def bs (s : String) : List Byte := s.toList.map ch

/-- The digits of `n` in `base` (`0` is `"0"`), upper case when `upper`. -/
def digitsB (base : Nat) (upper : Bool) (n : Nat) : List Byte :=
  (Nat.toDigits base n).map fun c =>
    BitVec.ofNat 8 (if upper && 97 ≤ c.toNat then c.toNat - 32 else c.toNat)

/-- `k` zeros. -/
def zeros (k : Nat) : List Byte := List.replicate k (ch '0')

/-- Left-pad with zeros to `k` bytes. -/
def padTo (k : Nat) (ds : List Byte) : List Byte := zeros (k - ds.length) ++ ds

/-- **The field**: the prefix `pre` (sign, `0x`) and the body, padded to the width `w`: spaces on
the right with `-`, zeros between prefix and body when `z`, else spaces on the left. -/
def pad (fl : Flags) (w : Nat) (z : Bool) (pre body : List Byte) : List Byte :=
  let n := pre.length + body.length
  if fl.minus then pre ++ body ++ List.replicate (w - n) (ch ' ')
  else if z then pre ++ zeros (w - n) ++ body
  else List.replicate (w - n) (ch ' ') ++ pre ++ body

/-- The sign: `-`, or `+`/space by the flags. -/
def signPre (fl : Flags) (neg : Bool) : List Byte :=
  if neg then [ch '-'] else if fl.plus then [ch '+'] else if fl.space then [ch ' '] else []

/-! ## Integer conversions -/

/-- The width of the promoted argument type: `int` for `hh h` and none, else 64 bits. -/
def Len.promoted : Len → Nat
  | .none | .hh | .h => 32
  | _ => 64

/-- The width of the converted type (`signed char` for `hh`, ...). -/
def Len.bits : Len → Nat
  | .hh => 8
  | .h => 16
  | .none => 32
  | _ => 64

/-- An integer reduced to `w` bits, unsigned. -/
def wrapU (w : Nat) (v : Int) : Nat := (v % (2 ^ w : Nat)).toNat

/-- An integer reduced to `w` bits, signed. -/
def wrapS (w : Nat) (v : Int) : Int :=
  let u := wrapU w v
  if u < 2 ^ (w - 1) then u else (u : Int) - (2 ^ w : Nat)

/-- **`d i o u x X`** of the value `v`, with the flags, width and precision (7.21.6.1p6, p8). -/
def intText (c : Spec) (fl : Flags) (w : Nat) (p : Option Nat) (v : Int) : List Byte :=
  let bits := c.len.bits
  let sv := wrapS bits v
  let neg := c.kind.isSigned && decide (sv < 0)
  let n := if c.kind.isSigned then sv.natAbs else wrapU bits v
  let base := match c.kind with
    | .o => 8
    | .x | .X => 16
    | _ => 10
  let ds := if p = some 0 ∧ n = 0 then [] else padTo (p.getD 1) (digitsB base (c.kind == .X) n)
  let ds := if c.kind == .o && fl.hash && ds.head? != some (ch '0') then ch '0' :: ds else ds
  let pre :=
    if c.kind.isSigned then signPre fl neg
    else if fl.hash && n != 0 && c.kind == .x then bs "0x"
    else if fl.hash && n != 0 && c.kind == .X then bs "0X"
    else []
  pad fl w (fl.zero && p.isNone) pre ds

/-! ## Floating conversions -/

/-- A floating value: a NaN or an infinity (with its sign), or `±m·2^e`. -/
inductive FVal where
  | nan (neg : Bool)
  | inf (neg : Bool)
  | fin (neg : Bool) (m : Nat) (e : Int)

/-- **An IEEE 754 binary64** (`double`). -/
def decode64 (b : BitVec 64) : FVal :=
  let neg := b.msb
  let ex := (b.extractLsb' 52 11).toNat
  let fr := (b.extractLsb' 0 52).toNat
  if ex = 2047 then (if fr = 0 then .inf neg else .nan neg)
  else if ex = 0 then .fin neg fr (-1074)
  else .fin neg (fr + 2 ^ 52) ((ex : Int) - 1075)

/-- **An x87 extended-precision value** (`long double`, explicit integer bit); `none` for the
encodings the 80387 no longer supports (pseudo-NaNs, pseudo-infinities, unnormals,
pseudo-denormals). -/
def decode80 (b : BitVec 80) : Option FVal :=
  let neg := b.msb
  let ex := (b.extractLsb' 64 15).toNat
  let sg := (b.extractLsb' 0 64).toNat
  let ib := sg / 2 ^ 63
  if ex = 32767 then
    if ib = 1 then (if sg % 2 ^ 63 = 0 then some (.inf neg) else some (.nan neg)) else none
  else if ex = 0 then (if ib = 0 then some (.fin neg sg (-16445)) else none)
  else if ib = 1 then some (.fin neg sg ((ex : Int) - 16446)) else none

/-- `m·2^e` as a fraction `a / b`. -/
def ratio (m : Nat) (e : Int) : Nat × Nat :=
  if 0 ≤ e then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)

/-- `a / b` rounded to the nearest integer, ties to even (the default rounding mode). -/
def roundHE (a b : Nat) : Nat :=
  let q := a / b
  let r := a % b
  if 2 * r > b ∨ (2 * r = b ∧ q % 2 = 1) then q + 1 else q

/-- **`f F`**: `a / b` with `p` digits after the point (the point also when `p = 0` and `#`). -/
def fixedText (a b p : Nat) (hash : Bool) : List Byte :=
  let N := roundHE (a * 10 ^ p) b
  let ip := digitsB 10 false (N / 10 ^ p)
  if p = 0 then ip ++ (if hash then [ch '.'] else [])
  else ip ++ [ch '.'] ++ padTo p (digitsB 10 false (N % 10 ^ p))

/-- The least `k` with `b ≤ a·10^k`, searched from `k` with `fuel` steps. -/
def negLog (a b : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => if b ≤ a * 10 ^ k then k else negLog a b fuel (k + 1)

/-- `⌊log₁₀ (a / b)⌋` for `a, b > 0`. -/
def flog10 (a b : Nat) : Int :=
  if b ≤ a then ((Nat.toDigits 10 (a / b)).length - 1 : Nat)
  else -((negLog a b (b + 1) 0 : Nat) : Int)

/-- **The `p + 1` significant digits and the exponent** of `a / b > 0`, rounded. -/
def sci (a b p : Nat) : Nat × Int :=
  let X := flog10 a b
  let sh : Int := (p : Int) - X
  let N := if 0 ≤ sh then roundHE (a * 10 ^ sh.toNat) b else roundHE a (b * 10 ^ (-sh).toNat)
  if N = 10 ^ (p + 1) then (10 ^ p, X + 1) else (N, X)

/-- The exponent: `e`/`E`, its sign, at least two digits. -/
def expText (upper : Bool) (X : Int) : List Byte :=
  ch (if upper then 'E' else 'e') :: (if X < 0 then ch '-' else ch '+') ::
    padTo 2 (digitsB 10 false X.natAbs)

/-- The digits `N` (`k` of them) with a point after the first. -/
def mantText (N k : Nat) (hash : Bool) : List Byte :=
  let ds := padTo k (digitsB 10 false N)
  ds.take 1 ++ (if k = 1 ∧ !hash then [] else ch '.' :: ds.drop 1)

/-- **`e E`**: `a / b` with one digit, the point, `p` digits and the exponent. -/
def sciText (a b p : Nat) (hash upper : Bool) : List Byte :=
  let (N, X) := if a = 0 then (0, 0) else sci a b p
  mantText N (p + 1) hash ++ expText upper X

/-- Remove the trailing zeros of a fraction, and the point when nothing follows it. -/
def stripZeros (ds : List Byte) : List Byte :=
  if ch '.' ∈ ds then
    let r := ds.reverse.dropWhile (· = ch '0')
    (if r.head? = some (ch '.') then r.drop 1 else r).reverse
  else ds

/-- **`g G`** (7.21.6.1p8): the style `e` when the exponent is below `-4` or not below the
precision, else `f`; trailing zeros removed unless `#`. -/
def genText (a b : Nat) (p0 : Option Nat) (hash upper : Bool) : List Byte :=
  let P := match p0 with
    | none => 6
    | some 0 => 1
    | some k => k
  let (N, X) := if a = 0 then (0, 0) else sci a b (P - 1)
  if X < P ∧ -4 ≤ X then
    let t := fixedText a b (((P : Int) - 1 - X).toNat) hash
    if hash then t else stripZeros t
  else
    let m := mantText N P hash
    (if hash then m else stripZeros m) ++ expText upper X

/-- **`f F e E g G`** of a floating value: infinities and NaNs as `inf`/`nan` (`INF`/`NAN` for
the upper-case specifiers) with their sign, never zero-padded. -/
def floatText (c : Spec) (fl : Flags) (w : Nat) (p : Option Nat) : FVal → List Byte
  | .nan neg => pad fl w false (signPre fl neg) (bs (if c.kind.upper then "NAN" else "nan"))
  | .inf neg => pad fl w false (signPre fl neg) (bs (if c.kind.upper then "INF" else "inf"))
  | .fin neg m e =>
    let (a, b) := ratio m e
    let upper := c.kind.upper
    let body := match c.kind with
      | .f | .F => fixedText a b (p.getD 6) fl.hash
      | .e | .E => sciText a b (p.getD 6) fl.hash upper
      | _ => genText a b p fl.hash upper
    pad fl w fl.zero (signPre fl neg) body

/-! ## Rendering -/

/-- A width or precision, with the argument `*` takes (an `int`). -/
def takeCount : Count → List PArg → Option (Option Int × List PArg)
  | .none, as => some (none, as)
  | .lit n, as => some (some n, as)
  | .star, .int v :: as => if -2 ^ 31 ≤ v ∧ v < 2 ^ 31 then some (some v, as) else none
  | .star, _ => none

/-- An integer argument fits the promoted type, read as signed or unsigned. -/
def fitsW (w : Nat) (v : Int) : Bool := decide (-(2 ^ (w - 1) : Int) ≤ v) && decide (v < (2 ^ w : Int))

/-- **One conversion of one argument**, with the flags `fl`, the width `wn` and the precision
`pn`; `pt` is the text of `%p` (`none`: `%p` is not supported). `none`: the argument does not
fit the conversion (the behaviour is undefined, 7.21.6.1p9). -/
def convText (pt : Option (Nat → List Byte)) (c : Spec) (fl : Flags) (wn : Nat) (pn : Option Nat) :
    PArg → Option (List Byte)
  | .int v =>
    if c.kind.isInt && fitsW c.len.promoted v then some (intText c fl wn pn v)
    else if c.kind == .c && fitsW 32 v then some (pad fl wn false [] [BitVec.ofInt 8 v])
    else none
  | .str s =>
    if c.kind == .s && !(s.contains 0) then some (pad fl wn false [] (match pn with
      | some q => s.take q
      | none => s))
    else none
  | .ptr q => if c.kind == .p then pt.map fun f => pad fl wn false [] (f q) else none
  | .dbl b =>
    if c.kind.isFloat && c.len != .L then some (floatText c fl wn pn (decode64 b)) else none
  | .ldbl b =>
    if c.kind.isFloat && c.len == .L then (decode80 b).map (floatText c fl wn pn) else none

/-- **One conversion** with the arguments it takes (a `*` width or precision first; a negative
width is the `-` flag, a negative precision none). -/
def renderSpec (pt : Option (Nat → List Byte)) (c : Spec) (as : List PArg) :
    Option (List Byte × List PArg) :=
  match takeCount c.width as with
  | none => none
  | some (w, as) =>
    match takeCount c.prec as with
    | none => none
    | some (p, as) =>
      match as with
      | [] => none
      | a :: as =>
        (convText pt c (if w.any (· < 0) then { c.flags with minus := true } else c.flags)
          (w.getD 0).natAbs (p.bind fun q => if q < 0 then none else some q.toNat) a).map (·, as)

/-- **The text of a format** with its arguments (extra arguments are ignored, 7.21.6.1p2). -/
def render (pt : Option (Nat → List Byte)) : List Item → List PArg → Option (List Byte)
  | [], _ => some []
  | .lit b :: is, as => (render pt is as).map (b :: ·)
  | .spec c :: is, as => match renderSpec pt c as with
    | some (t, as') => (render pt is as').map (t ++ ·)
    | none => none

/-- The specifications of a format are in the tier `t`, or are `%p` when `pt` supports it. -/
def InTier (t : Tier) (pt : Option (Nat → List Byte)) (is : List Item) : Prop :=
  ∀ c, Item.spec c ∈ is → c.inTier t = true ∨ (pt.isSome ∧ c.ptr = true)

/-- **`printf`'s text**: `fmt` is a format of the tier whose arguments fit, and `out` is its text. -/
def Text (t : Tier) (pt : Option (Nat → List Byte)) (fmt : List Byte) (as : List PArg)
    (out : List Byte) : Prop :=
  ∃ is, parse fmt = some is ∧ InTier t pt is ∧ render pt is as = some out

/-- **glibc's `%p`**: `(nil)` for a null pointer, else `0x` and the lower-case hexadecimal
digits. -/
def glibcPtr (q : Nat) : List Byte := if q = 0 then bs "(nil)" else bs "0x" ++ digitsB 16 false q

/-- `pt'` fixes the `%p` text wherever `pt` does. -/
def PtrLe (pt pt' : Option (Nat → List Byte)) : Prop := ∀ f, pt = some f → pt' = some f

end Silmaril.Libc.Stdio.Printf
