module

public import Silmaril.Apps.Sha256sum.Basic

/-! # `quotef`: file names in diagnostics

spec.md §6. gnulib `quotearg` in the `shell_escape` style with `:` also quoted, in the C
locale (every byte outside `0x20…0x7E` is unprintable). Three cases:

1. the name is printed bare when it is nonempty and no byte needs quoting;
2. a name with an apostrophe whose bytes are all "c and shell compatible" is printed in
   double quotes;
3. otherwise the `shell_escape_always` form. For a name with an apostrophe gnulib scans
   once and then reprocesses the name without resetting its "pending `$'`" flag; `quotef`
   reproduces that, including the spurious leading `''` and the dropped `$'` it causes
   (`it's\r` ↦ `'''it'\''s'$'\r'`). These quirks are observable and were measured on the
   real binary.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

/-- The C escape letter for `\a \b \f \n \r \t \v`. -/
def cEscLetter (c : UInt8) : Option UInt8 :=
  if c = 7 then some 97 else if c = 8 then some 98 else if c = 12 then some 102
  else if c = 10 then some 110 else if c = 13 then some 114 else if c = 9 then some 116
  else if c = 11 then some 118 else none

def isPrint (c : UInt8) : Bool := 32 ≤ c && c ≤ 126

/-- The bytes that are safe everywhere (`%+,-./0-9A-Z]_a-z`). -/
def isSafe (c : UInt8) : Bool :=
  c == 37 || c == 43 || c == 44 || c == 45 || c == 46 || c == 47 ||
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || c == 93 || c == 95 || (97 ≤ c && c ≤ 122)

/-- Shell metacharacters `space ! " $ & ( ) * ; < = > [ ^ ` |`. -/
def isShellSpecial (c : UInt8) : Bool :=
  c == 32 || c == 33 || c == 34 || c == 36 || c == 38 || c == 40 || c == 41 || c == 42 ||
  c == 59 || c == 60 || c == 61 || c == 62 || c == 91 || c == 94 || c == 96 || c == 124

/-- Does byte `c` at position `i` of `s` force quoting? -/
def needsQuotingAt (s : Bytes) (i : Nat) (c : UInt8) : Bool :=
  (cEscLetter c).isSome || c == 92 || c == 63 || c == 39 || c == 58 || isShellSpecial c ||
  ((c == 35 || c == 126) && i == 0) || ((c == 123 || c == 125) && s.length == 1) || !isPrint c

def needsQuoting (s : Bytes) : Bool :=
  s.isEmpty || (s.zipIdx.any fun (c, i) => needsQuotingAt s i c)

/-- gnulib `c_and_shell_quote_compat`, byte by byte. -/
def compatAt (s : Bytes) (i : Nat) (c : UInt8) : Bool :=
  isSafe c || c == 58 || c == 32 || c == 39 ||
  ((c == 35 || c == 126) && i == 0) || ((c == 123 || c == 125) && s.length == 1) ||
  ((cEscLetter c).isNone && c != 92 && c != 63 && !isShellSpecial c &&
    !(c == 35 || c == 126 || c == 123 || c == 125) && isPrint c)

def compat (s : Bytes) : Bool := s.zipIdx.all fun (c, i) => compatAt s i c

/-- The three octal digits of a byte. -/
def octal3 (c : UInt8) : Bytes :=
  [48 + c / 64, 48 + (c / 8) % 8, 48 + c % 8]

/-- One byte of the `shell_escape_always` pass: the bytes it appends, and the new
"pending" flag (inside a `$'…'` segment). -/
def quoteStep (pending : Bool) (c : UInt8) : Bytes × Bool :=
  let esc : Option Bytes :=
    match cEscLetter c with
    | some e => some [92, e]
    | none => if isPrint c then none else some (92 :: octal3 c)
  match esc with
  | some e => ((if pending then [] else lit "'$'") ++ e, true)
  | none =>
    if c = 39 then (lit "'\\''", false)
    else ((if pending then lit "''" else []) ++ [c], false)

/-- One pass of `quotearg_buffer_restyled` in `shell_escape_always` style. -/
def quotePass (s : Bytes) (pending : Bool) : Bytes × Bool :=
  let r := s.foldl (fun (acc : Bytes × Bool) c =>
    let (out, p) := quoteStep acc.2 c
    (acc.1 ++ out, p)) ([39], pending)
  (r.1 ++ [39], r.2)

def quotef (s : Bytes) : Bytes :=
  if !needsQuoting s then s
  else if s.contains 39 then
    if compat s then [34] ++ s ++ [34]
    else (quotePass s (quotePass s false).2).1
  else (quotePass s false).1

/-! Spot checks against the measured table of spec.md §6. -/

example : quotef (lit "a b") = lit "'a b'" := by decide
example : quotef (lit "x:y") = lit "'x:y'" := by decide
example : quotef (lit "it's") = lit "\"it's\"" := by decide
example : quotef (lit "a\nb") = lit "'a'$'\\n''b'" := by decide
example : quotef [0x80] = lit "''$'\\200'" := by decide
example : quotef (lit "it's\r") = lit "'''it'\\''s'$'\\r'" := by decide
example : quotef (lit "\r'x\n") = lit "'\\r'\\''x'$'\\n'" := by decide
example : quotef (lit "e%f") = lit "e%f" := by decide

end Silmaril.Apps.Sha256sum
