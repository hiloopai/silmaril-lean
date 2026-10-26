module

public import Silmaril.Apps.Sha256sum.Escape

/-! # `--check` line grammar

spec.md §7.3: digest.c `split_3` and `bsd_split_3`, with their C-string semantics.

A line `L` is a nonempty byte string that may contain NUL. Two forms:

* **tagged** `[WS*][\]SHA256[ ](NAME)WS*=WS*HEX`. The name runs to the *last* `)`. The
  tagged form never reads or changes the format lock.
* **untagged** `[WS*][\]HEX SEP REST`, with `SEP` a space, tab or NUL. Whether `REST` is
  read in the standard form (`' '` or `'*'` then the name) or in the BSD-reversed form (the
  whole of `REST` is the name) depends on, and updates, the per-invocation format lock
  `BsdMode`.

When the leading backslash is present the name is unescaped (`unescape`); otherwise it is
cut at its first NUL.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

/-- The format lock of digest.c (`bsd_reversed`): global for the whole invocation. -/
inductive BsdMode where
  | unknown | standard | reversed
  deriving DecidableEq, Repr

/-- The byte at `i`, reading past the end as the C string terminator NUL. -/
def at0 (L : Bytes) (i : Nat) : UInt8 := L.getD i 0

/-- 64 hex digits, and nothing else. -/
def validDigits (d : Bytes) : Bool := d.length = 64 && d.all isHex

/-- The index of the last occurrence of `c`. -/
def lastIndexOf (c : UInt8) : Bytes → Option Nat
  | [] => none
  | x :: xs =>
    match lastIndexOf c xs with
    | some i => some (i + 1)
    | none => if x = c then some 0 else none

/-- The name as stored: unescaped when the line had a leading backslash, otherwise cut at
the first NUL. -/
def nameOf (esc : Bool) (nameField : Bytes) : Option Bytes :=
  if esc then unescape nameField else some (beforeNul nameField)

/-- `bsd_split_3`: the part after `SHA256[ ](`. The name runs to the last `)`. -/
def bsdSplit (R : Bytes) (esc : Bool) : Option (Bytes × Bytes) :=
  match lastIndexOf 41 R with
  | none => none
  | some p =>
    match nameOf esc (R.take p) with
    | none => none
    | some name =>
      let after := (R.drop (p + 1)).dropWhile isWS
      match after with
      | 61 :: rest =>
        let hex := rest.dropWhile isWS
        if validDigits hex then some (hex, name) else none
      | _ => none

/-- The separator-terminated digest field: bytes not in `WS ∪ {NUL}`. -/
def isDigestByte (c : UInt8) : Bool := !isWS c && c != 0

/-- The format-lock step of `split_3`, on the bytes `rest` after the digest separator:
the new lock, and the name field (or rejection, when the line mixes formats). -/
def lockStep (mode : BsdMode) (rest : Bytes) : BsdMode × Option Bytes :=
  let looksReversed := rest.length == 1 || (at0 rest 0 != 32 && at0 rest 0 != 42)
  if looksReversed then
    if mode = .standard then (mode, none) else (.reversed, some rest)
  else if mode ≠ .reversed then (.standard, some (rest.drop 1))
  else (mode, some rest)

/-- `split_3` on one line, with the format lock. Returns the new lock (which may change
even when the line is then rejected) and, on success, the digest and the name. -/
def parseLine (mode : BsdMode) (L : Bytes) : BsdMode × Option (Bytes × Bytes) :=
  let i₀ := (L.takeWhile isWS).length
  let esc := at0 L i₀ == 92
  let j := if esc then i₀ + 1 else i₀
  let body := L.drop j
  if (body.take 6) = lit "SHA256" then
    let k := if at0 body 6 == 32 then 7 else 6
    if at0 body k == 40 then (mode, bsdSplit (body.drop (k + 1)) esc)
    else (mode, none)
  else if L.length - j < 66 + (if at0 L j == 92 then 1 else 0) then (mode, none)
  else
    let D := body.takeWhile isDigestByte
    if D.length = body.length then (mode, none)
    else if !validDigits D then (mode, none)
    else
      let r := lockStep mode (body.drop (D.length + 1))
      (r.1, r.2.bind fun nameField => (nameOf esc nameField).map fun name => (D, name))

theorem lockStep_fst (mode : BsdMode) (rest : Bytes) (h : mode ≠ .unknown) :
    (lockStep mode rest).1 = mode := by
  unfold lockStep
  cases mode <;> simp_all; split <;> rfl

/-- Format-lock monotonicity (spec.md §11.6): once set, the lock never changes. -/
theorem parseLine_mode (mode : BsdMode) (L : Bytes) (h : mode ≠ .unknown) :
    (parseLine mode L).1 = mode := by
  unfold parseLine
  simp only
  split_ifs <;> simp [lockStep_fst _ _ h]

/-- The lock only moves away from `unknown`. -/
theorem parseLine_mode_cases (mode : BsdMode) (L : Bytes) :
    (parseLine mode L).1 = mode ∨ mode = .unknown := by
  by_cases h : mode = .unknown
  · exact .inr h
  · exact .inl (parseLine_mode mode L h)

/-! ## Spot checks (spec.md §7.3) -/

private def hx : Bytes := lit "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

example : parseLine .unknown (hx ++ lit "  f") = (.standard, some (hx, lit "f")) := by decide
example : parseLine .unknown (hx ++ lit " *") = (.reversed, some (hx, lit "*")) := by decide
example : parseLine .unknown (hx ++ lit "  ") = (.reversed, some (hx, lit " ")) := by decide
example : parseLine .unknown (hx ++ lit " ") = (.unknown, none) := by decide
example : parseLine .standard (hx ++ lit " f") = (.standard, none) := by decide
example : parseLine .reversed (hx ++ lit "  f") = (.reversed, some (hx, lit " f")) := by decide
example : parseLine .unknown (lit "SHA256(f)=" ++ hx) = (.unknown, some (hx, lit "f")) := by decide
example : parseLine .unknown (lit "SHA256 (a)b) = " ++ hx) =
    (.unknown, some (hx, lit "a)b")) := by decide
example : parseLine .unknown (lit "SHA256  (f) = " ++ hx) = (.unknown, none) := by decide
example : parseLine .unknown (lit "SHA256 (f) = " ++ hx ++ lit " ") = (.unknown, none) := by decide
example : parseLine .unknown (lit "\\" ++ hx ++ lit "  a\\nb") =
    (.standard, some (hx, lit "a\nb")) := by decide +kernel

end Silmaril.Apps.Sha256sum
