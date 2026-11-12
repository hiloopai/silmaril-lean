module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Escape
public import Mathlib.Data.List.Basic

/-!
# The numeral renderings printed by `spectec --ast`

`spectec --ast` prints five kinds of numeral, each with a fixed spelling:

| rendering | OCaml |
| --- | --- |
| `decDigits` | `Z.to_string n` (`spectec/src/xl/num.ml:22`) |
| `signedDigits` | `(if i >= Z.zero then "+" else "-") ^ Z.to_string (Z.abs i)` (`num.ml:23`) |
| `intDigits` | `string_of_int i` (`spectec/src/backend-ast/print.ml:119`) |
| `ratDigits` | `Z.to_string (Q.num q) ^ "/" ^ Z.to_string (Q.den q)` (`num.ml:24`) |
| `hexByte` | `Printf.sprintf "0x%02X" n` (`print.ml:149`) |

The first three rows are the atoms of the `nat`, `int` and `rat` nodes that
`Print.num` emits (`spectec/src/backend-ast/print.ml:17-19`); `intDigits` is
the projection index of a `proj` node and `hexByte` the terminal of a `num`
grammar symbol.  Examples drawn from `specs/spectec/wasm-3.0.ast`: `0`,
`1024`, `+0`, `-7`, `-7/2`, `0x00`, `0xFD`, `0x10FFFF`.

The decimal renderings have no leading zeros and `0` renders as `0`;
`signedDigits` always carries a sign, so `0` renders as `+0`, while
`intDigits` carries one only when the argument is negative.  `hexByte` uses
uppercase hexadecimal zero-padded to a minimum width of two.

## Exactness

The IL decoder must recover a definition from its printed form, so each
parser below accepts *exactly* the image of the corresponding renderer: a
leading zero, a lone sign, an empty digit run, a zero denominator and a
lowercase hexadecimal digit are all rejected.  This is enforced structurally
rather than by case analysis: a parser scans a value and then accepts the
input only if the renderer reproduces it (`guardBy`).  Consequently
`parse? s = some a ↔ render a = s` holds unconditionally, and the four
round-trip theorems and the injectivity corollaries are immediate.

## Kernel reduction

Lean's `String` is UTF-8 backed, so kernel evaluation of `String` operations
is prohibitively slow; all of the content below therefore lives at the
`List Char` level, with thin `String` wrappers at the end.  Every recursive
definition is structural, taking an explicit fuel argument where the natural
recursion is on `n / 10` or `n / 16`, because well-founded recursion does not
reduce in the kernel at all.
-/

@[expose] public section

namespace Silmaril.SpecTec.Digits

/-! ## Digit characters -/

/-- `Escape.digitChar d` is the ASCII code point `d + 48` when `d` is a digit. -/
theorem toNat_digitChar {d : Nat} (h : d < 10) : (Escape.digitChar d).toNat = d + 48 :=
  Silmaril.Unicode.charToNat_ofNat (Or.inl (by omega))

/-- `Escape.digitVal?` inverts `Escape.digitChar` on digits. -/
theorem digitVal?_digitChar {d : Nat} (h : d < 10) :
    Escape.digitVal? (Escape.digitChar d) = some d := by
  unfold Escape.digitVal?
  rw [toNat_digitChar h, ite_eq_left (show 48 ≤ d + 48 ∧ d + 48 ≤ 57 by omega)]
  exact congrArg some (by omega)

/-- `Escape.digitChar` inverts `Escape.digitVal?` wherever the latter succeeds. -/
theorem digitVal?_eq_some {c : Char} {d : Nat} (h : Escape.digitVal? c = some d) :
    d < 10 ∧ Escape.digitChar d = c := by
  unfold Escape.digitVal? at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨by omega, ?_⟩
    unfold Escape.digitChar
    rw [show c.toNat - 48 + 48 = c.toNat by omega, Char.ofNat_toNat]
  · exact absurd h (by simp)

/-! ## The canonicity guard

Every parser in this file is a scanner followed by `guardBy`, which keeps a
scanned value only when it passes a decidable test.  The test is always "the
renderer reproduces the input", which is what makes the parsers exact. -/

/-- Keep a scanned value only when it passes `ok`. -/
def guardBy {α : Type} (ok : α → Bool) (v : Option α) : Option α :=
  match v with
  | none => none
  | some a => if ok a then some a else none

/-- `guardBy` succeeds exactly when the scan succeeded and the test passed. -/
theorem guardBy_eq_some {α : Type} {ok : α → Bool} {v : Option α} {a : α} :
    guardBy ok v = some a ↔ v = some a ∧ ok a = true := by
  constructor
  · intro h
    cases v with
    | none => simp only [guardBy] at h; exact absurd h (by simp)
    | some b =>
        simp only [guardBy] at h
        split at h
        · rename_i hok
          injection h with h'
          subst h'
          exact ⟨rfl, hok⟩
        · exact absurd h (by simp)
  · rintro ⟨rfl, h2⟩
    simp only [guardBy]
    rw [ite_eq_left h2]

/-- Injectivity of a renderer that some parser inverts. -/
theorem injective_of_parse {α : Type} {render : α → List Char} {parse : List Char → Option α}
    (h : ∀ a, parse (render a) = some a) : Function.Injective render := by
  intro a b hab
  have hp := h a
  rw [hab, h b] at hp
  exact (Option.some_inj.1 hp).symm

/-! ## Decimal naturals

`Z.to_string n` for `n ≥ 0` (`spectec/src/xl/num.ml:22`,
`spectec/src/backend-ast/print.ml:17`). -/

/-- The decimal digits of `n`, least significant first.  `fuel` makes the
recursion structural; `decDigits` supplies `n + 1`, which always suffices. -/
def decRev : Nat → Nat → List Char
  | 0, _ => []
  | f + 1, n =>
      if n < 10 then [Escape.digitChar n]
      else Escape.digitChar (n % 10) :: decRev f (n / 10)

/-- `Z.to_string n` for `n ≥ 0` (`spectec/src/xl/num.ml:22`): plain decimal
with no leading zeros, `0` rendering as `0`. -/
def decDigits (n : Nat) : List Char := (decRev (n + 1) n).reverse

/-- `decDigits` as a `String`. -/
def decString (n : Nat) : String := String.ofList (decDigits n)

/-- The value of a little-endian decimal digit list; the empty list is `0`. -/
def scanRev? : List Char → Option Nat
  | [] => some 0
  | c :: cs =>
      match Escape.digitVal? c with
      | none => none
      | some d =>
          match scanRev? cs with
          | none => none
          | some v => some (d + 10 * v)

/-- The value of a big-endian decimal digit list, with no canonicity check. -/
def scanDec? (s : List Char) : Option Nat := scanRev? s.reverse

/-- `scanRev?` of the empty list. -/
theorem scanRev?_nil : scanRev? [] = some 0 := rfl

/-- `scanRev?` of a cons whose head and tail both scan. -/
theorem scanRev?_cons {c : Char} {cs : List Char} {d v : Nat}
    (hc : Escape.digitVal? c = some d) (hcs : scanRev? cs = some v) :
    scanRev? (c :: cs) = some (d + 10 * v) := by
  rw [scanRev?, hc, hcs]

/-- `scanRev?` inverts `decRev` whenever the fuel suffices. -/
theorem scanRev?_decRev : ∀ (f n : Nat), n < f → scanRev? (decRev f n) = some n := by
  intro f
  induction f with
  | zero => intro n h; exact absurd h (Nat.not_lt_zero n)
  | succ f ih =>
      intro n h
      rw [decRev]
      split
      · rename_i h10
        rw [scanRev?_cons (digitVal?_digitChar h10) scanRev?_nil]
        exact congrArg some (by omega)
      · rename_i h10
        rw [scanRev?_cons (digitVal?_digitChar (show n % 10 < 10 by omega))
              (ih (n / 10) (by omega))]
        exact congrArg some (by omega)

/-- `scanDec?` inverts `decDigits`. -/
@[simp] theorem scanDec?_decDigits (n : Nat) : scanDec? (decDigits n) = some n := by
  show scanRev? ((decRev (n + 1) n).reverse).reverse = some n
  rw [List.reverse_reverse]
  exact scanRev?_decRev (n + 1) n (Nat.lt_succ_self n)

/-- `decDigits n` is never empty. -/
theorem decDigits_ne_nil (n : Nat) : decDigits n ≠ [] := by
  show (decRev (n + 1) n).reverse ≠ []
  simp only [ne_eq, List.reverse_eq_nil_iff]
  rw [decRev]
  split <;> simp

/-- Every character of `decRev f n` is an ASCII digit. -/
theorem toNat_of_mem_decRev : ∀ (f : Nat) {n : Nat} {c : Char}, c ∈ decRev f n →
    48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  intro f
  induction f with
  | zero => intro n c h; simp [decRev] at h
  | succ f ih =>
      intro n c h
      rw [decRev] at h
      split at h
      · rename_i h10
        rw [List.mem_singleton] at h
        subst h
        rw [toNat_digitChar h10]
        omega
      · rw [List.mem_cons] at h
        rcases h with h | h
        · subst h
          rw [toNat_digitChar (show n % 10 < 10 by omega)]
          omega
        · exact ih h

/-- Every character of `decDigits n` is an ASCII digit. -/
theorem toNat_of_mem_decDigits {n : Nat} {c : Char} (h : c ∈ decDigits n) :
    48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  rw [show decDigits n = (decRev (n + 1) n).reverse from rfl, List.mem_reverse] at h
  exact toNat_of_mem_decRev _ h

/-- A decimal rendering contains no sign, no solidus and no quotation mark, so
it is never confused with `signedDigits`, `ratDigits` or a quoted text. -/
theorem ne_of_mem_decDigits {n : Nat} {c : Char} (h : c ∈ decDigits n) :
    c ≠ '+' ∧ c ≠ '-' ∧ c ≠ '/' ∧ c ≠ '"' := by
  have hb := toNat_of_mem_decDigits h
  have h1 : ('+' : Char).toNat = 43 := rfl
  have h2 : ('-' : Char).toNat = 45 := rfl
  have h3 : ('/' : Char).toNat = 47 := rfl
  have h4 : ('"' : Char).toNat = 34 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> omega

/-- `decDigits n` is a nonempty list whose head is an ASCII digit. -/
theorem decDigits_eq_cons (n : Nat) :
    ∃ c cs, decDigits n = c :: cs ∧ c ≠ '+' ∧ c ≠ '-' ∧ c ≠ '/' ∧ c ≠ '"' := by
  cases hd : decDigits n with
  | nil => exact absurd hd (decDigits_ne_nil n)
  | cons c cs => exact ⟨c, cs, rfl, ne_of_mem_decDigits (by rw [hd]; simp)⟩

/-- A decimal rendering never begins with a sign or a quotation mark, so the
IL decoder can tell a `nat` atom from an `int` atom or a text. -/
theorem decDigits_head?_ne (n : Nat) :
    (decDigits n).head? ≠ some '+' ∧ (decDigits n).head? ≠ some '-' ∧
      (decDigits n).head? ≠ some '"' := by
  obtain ⟨c, cs, hc, h1, h2, -, h4⟩ := decDigits_eq_cons n
  rw [hc]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [List.head?_cons, ne_eq, Option.some.injEq]
  exacts [h1, h2, h4]

/-- The exact inverse of `decDigits`. -/
def parseDec? (s : List Char) : Option Nat :=
  guardBy (fun n => decide (decDigits n = s)) (scanDec? s)

/-- `parseDec?` accepts exactly the image of `decDigits`. -/
theorem parseDec?_eq_some_iff {s : List Char} {n : Nat} :
    parseDec? s = some n ↔ decDigits n = s := by
  unfold parseDec?
  rw [guardBy_eq_some]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨by rw [← h, scanDec?_decDigits], h⟩⟩

/-- `parseDec?` inverts `decDigits`. -/
@[simp] theorem parseDec?_decDigits (n : Nat) : parseDec? (decDigits n) = some n :=
  parseDec?_eq_some_iff.2 rfl

/-- `decDigits` inverts `parseDec?`. -/
theorem decDigits_of_parseDec? {s : List Char} {n : Nat} (h : parseDec? s = some n) :
    decDigits n = s := parseDec?_eq_some_iff.1 h

/-- Distinct naturals have distinct decimal renderings. -/
theorem decDigits_injective : Function.Injective decDigits :=
  injective_of_parse parseDec?_decDigits

/-! ## Signed integers

`(if i >= Z.zero then "+" else "-") ^ Z.to_string (Z.abs i)`
(`spectec/src/xl/num.ml:23`, `spectec/src/backend-ast/print.ml:18`). -/

/-- The `Int` case of `Num.to_string` (`spectec/src/xl/num.ml:23`): an explicit sign
followed by the decimal absolute value, so `0` renders as `+0`. -/
def signedDigits (i : Int) : List Char :=
  if 0 ≤ i then '+' :: decDigits i.natAbs else '-' :: decDigits i.natAbs

/-- `signedDigits` as a `String`. -/
def signedString (i : Int) : String := String.ofList (signedDigits i)

/-- The rendering of a nonnegative integer. -/
theorem signedDigits_of_nonneg {i : Int} (h : 0 ≤ i) :
    signedDigits i = '+' :: decDigits i.natAbs := by
  unfold signedDigits; rw [ite_eq_left h]

/-- The rendering of a negative integer. -/
theorem signedDigits_of_neg {i : Int} (h : ¬ 0 ≤ i) :
    signedDigits i = '-' :: decDigits i.natAbs := by
  unfold signedDigits; rw [ite_eq_right h]

/-- The value of a signed decimal rendering, with no canonicity check. -/
def scanSigned? (s : List Char) : Option Int :=
  match s with
  | [] => none
  | c :: rest =>
      if c = '+' then (scanDec? rest).map (fun (n : Nat) => (n : Int))
      else if c = '-' then (scanDec? rest).map (fun (n : Nat) => -(n : Int))
      else none

/-- `scanSigned?` on a `+` sign. -/
theorem scanSigned?_plus (cs : List Char) :
    scanSigned? ('+' :: cs) = (scanDec? cs).map (fun (n : Nat) => (n : Int)) := rfl

/-- `scanSigned?` on a `-` sign. -/
theorem scanSigned?_minus (cs : List Char) :
    scanSigned? ('-' :: cs) = (scanDec? cs).map (fun (n : Nat) => -(n : Int)) := rfl

/-- `scanSigned?` inverts `signedDigits`. -/
theorem scanSigned?_signedDigits (i : Int) : scanSigned? (signedDigits i) = some i := by
  by_cases h : 0 ≤ i
  · rw [signedDigits_of_nonneg h, scanSigned?_plus, scanDec?_decDigits]
    exact congrArg some (show ((i.natAbs : Nat) : Int) = i by omega)
  · rw [signedDigits_of_neg h, scanSigned?_minus, scanDec?_decDigits]
    exact congrArg some (show -((i.natAbs : Nat) : Int) = i by omega)

/-- The exact inverse of `signedDigits`. -/
def parseSigned? (s : List Char) : Option Int :=
  guardBy (fun i => decide (signedDigits i = s)) (scanSigned? s)

/-- `parseSigned?` accepts exactly the image of `signedDigits`. -/
theorem parseSigned?_eq_some_iff {s : List Char} {i : Int} :
    parseSigned? s = some i ↔ signedDigits i = s := by
  unfold parseSigned?
  rw [guardBy_eq_some]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨by rw [← h, scanSigned?_signedDigits], h⟩⟩

/-- `parseSigned?` inverts `signedDigits`. -/
@[simp] theorem parseSigned?_signedDigits (i : Int) : parseSigned? (signedDigits i) = some i :=
  parseSigned?_eq_some_iff.2 rfl

/-- `signedDigits` inverts `parseSigned?`. -/
theorem signedDigits_of_parseSigned? {s : List Char} {i : Int} (h : parseSigned? s = some i) :
    signedDigits i = s := parseSigned?_eq_some_iff.1 h

/-- Distinct integers have distinct signed renderings. -/
theorem signedDigits_injective : Function.Injective signedDigits :=
  injective_of_parse parseSigned?_signedDigits

/-! ## Plain integers

`string_of_int i` (`spectec/src/backend-ast/print.ml:119`), used for the
projection index of `ProjE`. -/

/-- `string_of_int i`: a bare `-` for negative arguments and no sign
otherwise, so `0` renders as `0`. -/
def intDigits (i : Int) : List Char :=
  if i < 0 then '-' :: decDigits i.natAbs else decDigits i.natAbs

/-- `intDigits` as a `String`. -/
def intString (i : Int) : String := String.ofList (intDigits i)

/-- The rendering of a negative integer. -/
theorem intDigits_of_neg {i : Int} (h : i < 0) : intDigits i = '-' :: decDigits i.natAbs := by
  unfold intDigits; rw [ite_eq_left h]

/-- The rendering of a nonnegative integer. -/
theorem intDigits_of_nonneg {i : Int} (h : ¬ i < 0) : intDigits i = decDigits i.natAbs := by
  unfold intDigits; rw [ite_eq_right h]

/-- The value of a `string_of_int` rendering, with no canonicity check. -/
def scanInt? (s : List Char) : Option Int :=
  match s with
  | [] => none
  | c :: rest =>
      if c = '-' then (scanDec? rest).map (fun (n : Nat) => -(n : Int))
      else (scanDec? (c :: rest)).map (fun (n : Nat) => (n : Int))

/-- `scanInt?` on a `-` sign. -/
theorem scanInt?_minus (cs : List Char) :
    scanInt? ('-' :: cs) = (scanDec? cs).map (fun (n : Nat) => -(n : Int)) := rfl

/-- `scanInt?` on an unsigned rendering. -/
theorem scanInt?_of_ne {c : Char} (h : ¬ c = '-') (cs : List Char) :
    scanInt? (c :: cs) = (scanDec? (c :: cs)).map (fun (n : Nat) => (n : Int)) := by
  simp only [scanInt?]
  rw [ite_eq_right h]

/-- `scanInt?` inverts `intDigits`. -/
theorem scanInt?_intDigits (i : Int) : scanInt? (intDigits i) = some i := by
  by_cases h : i < 0
  · rw [intDigits_of_neg h, scanInt?_minus, scanDec?_decDigits]
    exact congrArg some (show -((i.natAbs : Nat) : Int) = i by omega)
  · obtain ⟨c, cs, hc, -, hm, -, -⟩ := decDigits_eq_cons i.natAbs
    rw [intDigits_of_nonneg h, hc, scanInt?_of_ne hm, ← hc, scanDec?_decDigits]
    exact congrArg some (show ((i.natAbs : Nat) : Int) = i by omega)

/-- The exact inverse of `intDigits`. -/
def parseInt? (s : List Char) : Option Int :=
  guardBy (fun i => decide (intDigits i = s)) (scanInt? s)

/-- `parseInt?` accepts exactly the image of `intDigits`. -/
theorem parseInt?_eq_some_iff {s : List Char} {i : Int} :
    parseInt? s = some i ↔ intDigits i = s := by
  unfold parseInt?
  rw [guardBy_eq_some]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨by rw [← h, scanInt?_intDigits], h⟩⟩

/-- `parseInt?` inverts `intDigits`. -/
@[simp] theorem parseInt?_intDigits (i : Int) : parseInt? (intDigits i) = some i :=
  parseInt?_eq_some_iff.2 rfl

/-- `intDigits` inverts `parseInt?`. -/
theorem intDigits_of_parseInt? {s : List Char} {i : Int} (h : parseInt? s = some i) :
    intDigits i = s := parseInt?_eq_some_iff.1 h

/-- Distinct integers have distinct `string_of_int` renderings. -/
theorem intDigits_injective : Function.Injective intDigits :=
  injective_of_parse parseInt?_intDigits

/-! ## Rationals

`Z.to_string (Q.num q) ^ "/" ^ Z.to_string (Q.den q)`
(`spectec/src/xl/num.ml:24`, `spectec/src/backend-ast/print.ml:19`).  `Q.den`
is positive, and the numerator is rendered `string_of_int`-style. -/

/-- The `Rat` case of `Num.to_string` (`spectec/src/xl/num.ml:24`). -/
def ratDigits (num : Int) (den : Nat) : List Char :=
  intDigits num ++ '/' :: decDigits den

/-- `ratDigits` as a `String`. -/
def ratString (num : Int) (den : Nat) : String := String.ofList (ratDigits num den)

/-- An integer rendering never contains a solidus, so the first solidus of a
rational rendering separates numerator from denominator. -/
theorem ne_slash_of_mem_intDigits {i : Int} {c : Char} (h : c ∈ intDigits i) : ¬ c = '/' := by
  by_cases hi : i < 0
  · rw [intDigits_of_neg hi, List.mem_cons] at h
    rcases h with rfl | h
    · decide
    · exact (ne_of_mem_decDigits h).2.2.1
  · rw [intDigits_of_nonneg hi] at h
    exact (ne_of_mem_decDigits h).2.2.1

/-- Split a list at its first solidus. -/
def splitSlash? : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if c = '/' then some ([], rest)
      else (splitSlash? rest).map fun p => (c :: p.1, p.2)

/-- `splitSlash?` finds the separator of a rational rendering. -/
theorem splitSlash?_append : ∀ (a b : List Char), (∀ c ∈ a, ¬ c = '/') →
    splitSlash? (a ++ '/' :: b) = some (a, b) := by
  intro a
  induction a with
  | nil =>
      intro b _
      show splitSlash? ('/' :: b) = some ([], b)
      unfold splitSlash?
      rw [ite_eq_left rfl]
  | cons c cs ih =>
      intro b h
      show splitSlash? (c :: (cs ++ '/' :: b)) = some (c :: cs, b)
      unfold splitSlash?
      rw [ite_eq_right (h c (by simp)), ih b (fun d hd => h d (by simp [hd]))]
      rfl

/-- The value of a rational rendering, with no canonicity check. -/
def scanRat? (s : List Char) : Option (Int × Nat) :=
  match splitSlash? s with
  | none => none
  | some p =>
      match scanInt? p.1, scanDec? p.2 with
      | some num, some den => some (num, den)
      | _, _ => none

/-- `scanRat?` inverts `ratDigits`. -/
theorem scanRat?_ratDigits (num : Int) (den : Nat) :
    scanRat? (ratDigits num den) = some (num, den) := by
  have hsplit : splitSlash? (intDigits num ++ '/' :: decDigits den)
      = some (intDigits num, decDigits den) :=
    splitSlash?_append _ _ (fun c hc => ne_slash_of_mem_intDigits hc)
  unfold ratDigits
  simp only [scanRat?, hsplit, scanInt?_intDigits, scanDec?_decDigits]

/-- The exact inverse of `ratDigits`, rejecting a zero denominator. -/
def parseRat? (s : List Char) : Option (Int × Nat) :=
  guardBy (fun p => decide (0 < p.2 ∧ ratDigits p.1 p.2 = s)) (scanRat? s)

/-- `parseRat?` accepts exactly the image of `ratDigits` on positive
denominators. -/
theorem parseRat?_eq_some_iff {s : List Char} {num : Int} {den : Nat} :
    parseRat? s = some (num, den) ↔ 0 < den ∧ ratDigits num den = s := by
  unfold parseRat?
  rw [guardBy_eq_some]
  simp only [decide_eq_true_eq]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [← h.2, scanRat?_ratDigits]

/-- `parseRat?` inverts `ratDigits` on positive denominators. -/
@[simp] theorem parseRat?_ratDigits (num : Int) {den : Nat} (h : 0 < den) :
    parseRat? (ratDigits num den) = some (num, den) :=
  parseRat?_eq_some_iff.2 ⟨h, rfl⟩

/-- `ratDigits` inverts `parseRat?`. -/
theorem ratDigits_of_parseRat? {s : List Char} {num : Int} {den : Nat}
    (h : parseRat? s = some (num, den)) : ratDigits num den = s :=
  (parseRat?_eq_some_iff.1 h).2

/-- `parseRat?` never returns a zero denominator. -/
theorem pos_den_of_parseRat? {s : List Char} {num : Int} {den : Nat}
    (h : parseRat? s = some (num, den)) : 0 < den :=
  (parseRat?_eq_some_iff.1 h).1

/-- Distinct rationals with positive denominators have distinct renderings. -/
theorem ratDigits_injective {n₁ n₂ : Int} {d₁ d₂ : Nat} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h : ratDigits n₁ d₁ = ratDigits n₂ d₂) : n₁ = n₂ ∧ d₁ = d₂ := by
  have hp := parseRat?_ratDigits n₁ h₁
  rw [h, parseRat?_ratDigits n₂ h₂] at hp
  have := Option.some_inj.1 hp
  exact ⟨(Prod.mk.injEq .. ▸ this).1.symm, (Prod.mk.injEq .. ▸ this).2.symm⟩

/-! ## Hexadecimal bytes

`Printf.sprintf "0x%02X" n` (`spectec/src/backend-ast/print.ml:149`), the
rendering of the `NumG` terminal of a grammar. -/

/-- The uppercase hexadecimal digit for `n < 16`. -/
def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Escape.digitChar n else Char.ofNat (n + 55)

/-- The value of an uppercase hexadecimal digit; lowercase is rejected. -/
def hexVal? (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else none

/-- `hexVal?` inverts `hexDigitChar` on hexadecimal digits. -/
theorem hexVal?_hexDigitChar {d : Nat} (h : d < 16) : hexVal? (hexDigitChar d) = some d := by
  unfold hexDigitChar
  split
  · rename_i h10
    unfold hexVal?
    rw [toNat_digitChar h10, ite_eq_left (show 48 ≤ d + 48 ∧ d + 48 ≤ 57 by omega)]
    exact congrArg some (by omega)
  · rename_i h10
    have ht : (Char.ofNat (d + 55)).toNat = d + 55 :=
      Silmaril.Unicode.charToNat_ofNat (Or.inl (by omega))
    unfold hexVal?
    rw [ht, ite_eq_right (show ¬ (48 ≤ d + 55 ∧ d + 55 ≤ 57) by omega),
      ite_eq_left (show 65 ≤ d + 55 ∧ d + 55 ≤ 70 by omega)]
    exact congrArg some (by omega)

/-- The hexadecimal digits of `n`, least significant first. -/
def hexRev : Nat → Nat → List Char
  | 0, _ => []
  | f + 1, n =>
      if n < 16 then [hexDigitChar n]
      else hexDigitChar (n % 16) :: hexRev f (n / 16)

/-- `Printf.sprintf "0x%02X" n` (`spectec/src/backend-ast/print.ml:149`):
the literal `0x`, then uppercase hexadecimal zero-padded to width two. -/
def hexByte (n : Nat) : List Char :=
  '0' :: 'x' :: (if n < 16 then ['0', hexDigitChar n] else (hexRev (n + 1) n).reverse)

/-- `hexByte` as a `String`. -/
def hexByteString (n : Nat) : String := String.ofList (hexByte n)

/-- Every hexadecimal rendering begins with `0x`. -/
theorem hexByte_eq_cons (n : Nat) : ∃ body, hexByte n = '0' :: 'x' :: body := ⟨_, rfl⟩

/-- The value of a little-endian hexadecimal digit list. -/
def scanHexRev? : List Char → Option Nat
  | [] => some 0
  | c :: cs =>
      match hexVal? c with
      | none => none
      | some d =>
          match scanHexRev? cs with
          | none => none
          | some v => some (d + 16 * v)

/-- The value of a big-endian hexadecimal digit list. -/
def scanHex? (s : List Char) : Option Nat := scanHexRev? s.reverse

/-- `scanHexRev?` of the empty list. -/
theorem scanHexRev?_nil : scanHexRev? [] = some 0 := rfl

/-- `scanHexRev?` of a cons whose head and tail both scan. -/
theorem scanHexRev?_cons {c : Char} {cs : List Char} {d v : Nat}
    (hc : hexVal? c = some d) (hcs : scanHexRev? cs = some v) :
    scanHexRev? (c :: cs) = some (d + 16 * v) := by
  rw [scanHexRev?, hc, hcs]

/-- `scanHexRev?` inverts `hexRev` whenever the fuel suffices. -/
theorem scanHexRev?_hexRev : ∀ (f n : Nat), n < f → scanHexRev? (hexRev f n) = some n := by
  intro f
  induction f with
  | zero => intro n h; exact absurd h (Nat.not_lt_zero n)
  | succ f ih =>
      intro n h
      rw [hexRev]
      split
      · rename_i h16
        rw [scanHexRev?_cons (hexVal?_hexDigitChar h16) scanHexRev?_nil]
        exact congrArg some (by omega)
      · rename_i h16
        rw [scanHexRev?_cons (hexVal?_hexDigitChar (show n % 16 < 16 by omega))
              (ih (n / 16) (by omega))]
        exact congrArg some (by omega)

/-- The value of a `0x`-prefixed rendering, with no canonicity check. -/
def scanHexByte? (s : List Char) : Option Nat :=
  match s with
  | c₀ :: c₁ :: body => if c₀ = '0' ∧ c₁ = 'x' then scanHex? body else none
  | _ => none

/-- `scanHexByte?` on a `0x` prefix. -/
theorem scanHexByte?_prefix (body : List Char) :
    scanHexByte? ('0' :: 'x' :: body) = scanHex? body := rfl

/-- `scanHexByte?` inverts `hexByte`. -/
theorem scanHexByte?_hexByte (n : Nat) : scanHexByte? (hexByte n) = some n := by
  unfold hexByte
  rw [scanHexByte?_prefix]
  split
  · rename_i h16
    show scanHexRev? (['0', hexDigitChar n] : List Char).reverse = some n
    rw [show (['0', hexDigitChar n] : List Char).reverse = [hexDigitChar n, '0'] from rfl,
      scanHexRev?_cons (hexVal?_hexDigitChar h16)
        (scanHexRev?_cons (show hexVal? '0' = some 0 from rfl) scanHexRev?_nil)]
    exact congrArg some (by omega)
  · show scanHexRev? ((hexRev (n + 1) n).reverse).reverse = some n
    rw [List.reverse_reverse]
    exact scanHexRev?_hexRev (n + 1) n (Nat.lt_succ_self n)

/-- The exact inverse of `hexByte`. -/
def parseHexByte? (s : List Char) : Option Nat :=
  guardBy (fun n => decide (hexByte n = s)) (scanHexByte? s)

/-- `parseHexByte?` accepts exactly the image of `hexByte`. -/
theorem parseHexByte?_eq_some_iff {s : List Char} {n : Nat} :
    parseHexByte? s = some n ↔ hexByte n = s := by
  unfold parseHexByte?
  rw [guardBy_eq_some]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨by rw [← h, scanHexByte?_hexByte], h⟩⟩

/-- `parseHexByte?` inverts `hexByte`. -/
@[simp] theorem parseHexByte?_hexByte (n : Nat) : parseHexByte? (hexByte n) = some n :=
  parseHexByte?_eq_some_iff.2 rfl

/-- `hexByte` inverts `parseHexByte?`. -/
theorem hexByte_of_parseHexByte? {s : List Char} {n : Nat} (h : parseHexByte? s = some n) :
    hexByte n = s := parseHexByte?_eq_some_iff.1 h

/-- Distinct naturals have distinct hexadecimal renderings. -/
theorem hexByte_injective : Function.Injective hexByte :=
  injective_of_parse parseHexByte?_hexByte

/-! ## `String` wrappers

Thin corollaries for callers that hold a `String`; all of the content is at
the `List Char` level above. -/

/-- `parseDec?` on a `String`. -/
def parseDecString? (s : String) : Option Nat := parseDec? s.toList

/-- `parseSigned?` on a `String`. -/
def parseSignedString? (s : String) : Option Int := parseSigned? s.toList

/-- `parseInt?` on a `String`. -/
def parseIntString? (s : String) : Option Int := parseInt? s.toList

/-- `parseRat?` on a `String`. -/
def parseRatString? (s : String) : Option (Int × Nat) := parseRat? s.toList

/-- `parseHexByte?` on a `String`. -/
def parseHexByteString? (s : String) : Option Nat := parseHexByte? s.toList

/-- `parseDecString?` inverts `decString`. -/
@[simp] theorem parseDecString?_decString (n : Nat) : parseDecString? (decString n) = some n := by
  show parseDec? (String.ofList (decDigits n)).toList = some n
  rw [String.toList_ofList, parseDec?_decDigits]

/-- `decString` inverts `parseDecString?`. -/
theorem decString_of_parseDecString? {s : String} {n : Nat} (h : parseDecString? s = some n) :
    decString n = s := by
  show String.ofList (decDigits n) = s
  rw [decDigits_of_parseDec? h, String.ofList_toList]

/-- `parseSignedString?` inverts `signedString`. -/
@[simp] theorem parseSignedString?_signedString (i : Int) :
    parseSignedString? (signedString i) = some i := by
  show parseSigned? (String.ofList (signedDigits i)).toList = some i
  rw [String.toList_ofList, parseSigned?_signedDigits]

/-- `signedString` inverts `parseSignedString?`. -/
theorem signedString_of_parseSignedString? {s : String} {i : Int}
    (h : parseSignedString? s = some i) : signedString i = s := by
  show String.ofList (signedDigits i) = s
  rw [signedDigits_of_parseSigned? h, String.ofList_toList]

/-- `parseIntString?` inverts `intString`. -/
@[simp] theorem parseIntString?_intString (i : Int) : parseIntString? (intString i) = some i := by
  show parseInt? (String.ofList (intDigits i)).toList = some i
  rw [String.toList_ofList, parseInt?_intDigits]

/-- `intString` inverts `parseIntString?`. -/
theorem intString_of_parseIntString? {s : String} {i : Int} (h : parseIntString? s = some i) :
    intString i = s := by
  show String.ofList (intDigits i) = s
  rw [intDigits_of_parseInt? h, String.ofList_toList]

/-- `parseRatString?` inverts `ratString` on positive denominators. -/
@[simp] theorem parseRatString?_ratString (num : Int) {den : Nat} (h : 0 < den) :
    parseRatString? (ratString num den) = some (num, den) := by
  show parseRat? (String.ofList (ratDigits num den)).toList = some (num, den)
  rw [String.toList_ofList, parseRat?_ratDigits num h]

/-- `ratString` inverts `parseRatString?`. -/
theorem ratString_of_parseRatString? {s : String} {num : Int} {den : Nat}
    (h : parseRatString? s = some (num, den)) : ratString num den = s := by
  show String.ofList (ratDigits num den) = s
  rw [ratDigits_of_parseRat? h, String.ofList_toList]

/-- `parseHexByteString?` inverts `hexByteString`. -/
@[simp] theorem parseHexByteString?_hexByteString (n : Nat) :
    parseHexByteString? (hexByteString n) = some n := by
  show parseHexByte? (String.ofList (hexByte n)).toList = some n
  rw [String.toList_ofList, parseHexByte?_hexByte]

/-- `hexByteString` inverts `parseHexByteString?`. -/
theorem hexByteString_of_parseHexByteString? {s : String} {n : Nat}
    (h : parseHexByteString? s = some n) : hexByteString n = s := by
  show String.ofList (hexByte n) = s
  rw [hexByte_of_parseHexByte? h, String.ofList_toList]

/-! ## Checks against the printed streams

The renderings below are taken from `specs/spectec/wasm-3.0.ast`; the
rejections record the spellings that the parsers must refuse. -/

example : decString 0 = "0" := by rfl
example : decString 1234 = "1234" := by rfl
example : signedString 0 = "+0" := by rfl
example : signedString (-7) = "-7" := by rfl
example : signedString 7 = "+7" := by rfl
example : intString (-7) = "-7" := by rfl
example : intString 0 = "0" := by rfl
example : intString 3 = "3" := by rfl
example : ratString (-7) 2 = "-7/2" := by rfl
example : hexByteString 0 = "0x00" := by rfl
example : hexByteString 5 = "0x05" := by rfl
example : hexByteString 253 = "0xFD" := by rfl
example : hexByteString 255 = "0xFF" := by rfl
example : hexByteString 256 = "0x100" := by rfl
example : hexByteString 0x10FFFF = "0x10FFFF" := by rfl

example : parseDec? ['1', '2', '3', '4'] = some 1234 := by rfl
example : parseDec? ['0'] = some 0 := by rfl
example : parseDec? ['0', '7'] = none := by rfl
example : parseDec? [] = none := by rfl
example : parseSigned? ['+', '0'] = some 0 := by rfl
example : parseSigned? ['-', '0'] = none := by rfl
example : parseSigned? ['+'] = none := by rfl
example : parseSigned? ['7'] = none := by rfl
example : parseInt? ['-', '7'] = some (-7) := by rfl
example : parseInt? ['+', '7'] = none := by rfl
example : parseInt? ['-', '0'] = none := by rfl
example : parseRat? ['-', '7', '/', '2'] = some (-7, 2) := by rfl
example : parseRat? ['1', '/', '0'] = none := by rfl
example : parseRat? ['+', '1', '/', '2'] = none := by rfl
example : parseHexByte? ['0', 'x', 'F', 'D'] = some 253 := by rfl
example : parseHexByte? ['0', 'x', 'f', 'd'] = none := by rfl
example : parseHexByte? ['0', 'x', '0'] = none := by rfl
example : parseHexByte? ['0', 'x', '5'] = none := by rfl
example : parseHexByte? ['0', 'x', '0', '5'] = some 5 := by rfl
example : parseHexByte? ['F', 'D'] = none := by rfl

end Silmaril.SpecTec.Digits
