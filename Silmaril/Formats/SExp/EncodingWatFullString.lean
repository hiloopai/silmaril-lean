module

public import Silmaril.Formats.SExp.EncodingWatByteLexer

@[expose] public section

/-! Proof-carrying execution of the existing WAT string-element grammar,
including mnemonic and Unicode escapes. Earlier lexical APIs are retained. -/

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

def hexNumberFuel? : Nat → (ds : Chars) → Option {n : Nat // HexNum ds n}
  | 0, _ => none
  | fuel + 1, ds => do
      let d ← ds.getLast?
      let hd ← if h : IsHexDigit d then some (PLift.up h) else none
      let stem := ds.dropLast
      if he : ds = [d] then
        pure ⟨hexVal d, he ▸ .one hd.down⟩
      else if stem.getLast? = some '_' then
        let prev := stem.dropLast
        let n ← hexNumberFuel? fuel prev
        if he : ds = prev ++ ['_', d] then
          pure ⟨16 * n.1 + hexVal d, he ▸ .snocSep n.2 hd.down⟩
        else none
      else
        let n ← hexNumberFuel? fuel stem
        if he : ds = stem ++ [d] then
          pure ⟨16 * n.1 + hexVal d, he ▸ .snoc n.2 hd.down⟩
        else none

def mnemonic? : (c : Char) → Option {bs : List UInt8 // StringElem ['\\', c] bs}
  | 't' => some ⟨[0x09], .tab⟩
  | 'n' => some ⟨[0x0a], .newline⟩
  | 'r' => some ⟨[0x0d], .ret⟩
  | '"' => some ⟨[0x22], .dquote⟩
  | '\'' => some ⟨[0x27], .squote⟩
  | '\\' => some ⟨[0x5c], .backslash⟩
  | _ => none

structure EscapeTail (cs : Chars) where
  spelling : Chars
  bytes : List UInt8
  rest : Chars
  split : cs = spelling ++ rest
  sound : StringElem ('\\' :: spelling) bytes

def escapeTail? (cs : Chars) : Option (EscapeTail cs) := do
  match hcs : cs with
  | [] => none
  | c :: rest =>
      match mnemonic? c with
      | some bs => some ⟨[c], bs.1, rest, hcs, bs.2⟩
      | none =>
          match hc : cs with
          | 'u' :: '{' :: tail => do
              let ds := tail.takeWhile (· != '}')
              let '}' :: rest := tail.drop ds.length | none
              let n ← hexNumberFuel? (ds.length + 1) ds
              if hn : n.1 < 0x110000 then
                if hs : cs = ('u' :: '{' :: ds ++ ['}']) ++ rest then
                  some ⟨'u' :: '{' :: ds ++ ['}'], escapeUtf8 n.1, rest, hs,
                    .unicode n.2 hn⟩
                else none
              else none
          | h₁ :: h₂ :: tail =>
              if hd : IsHexDigit h₁ ∧ IsHexDigit h₂ then
                some ⟨[h₁, h₂], [UInt8.ofNat (16 * hexVal h₁ + hexVal h₂)],
                  tail, hc, .byte hd.1 hd.2⟩
              else none
          | _ => none

structure StringTail (cs : Chars) where
  spelling : Chars
  bytes : List UInt8
  rest : Chars
  split : cs = spelling ++ '"' :: rest
  sound : StringBody spelling bytes

def fullStrBodyFuel? : Nat → (cs : Chars) → Option (StringTail cs)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, c :: r =>
      if hq : c = '"' then
        some ⟨[], [], r, by simp [hq], .nil⟩
      else if hb : c = '\\' then do
        let e ← escapeTail? r
        let tail ← fullStrBodyFuel? fuel e.rest
        some ⟨'\\' :: e.spelling ++ tail.spelling, e.bytes ++ tail.bytes, tail.rest,
          by simp [hb, e.split, tail.split, List.append_assoc],
          by simpa using StringBody.cons e.sound tail.sound⟩
      else if hp : PlainStrChar c then do
        let tail ← fullStrBodyFuel? fuel r
        some ⟨c :: tail.spelling, charUtf8 c ++ tail.bytes, tail.rest,
          by simp [tail.split],
          by simpa using StringBody.cons (StringElem.char hp.1 hp.2.1 hp.2.2.1 hp.2.2.2) tail.sound⟩
      else none

/-- Match the existing string parser interface, retaining a certificate inside
its implementation instead of assuming the candidate's decoding is correct. -/
def fullStrBody? (cs : Chars) : Option (Chars × List UInt8 × Chars) :=
  (fullStrBodyFuel? (cs.length + 1) cs).map fun t => (t.spelling, t.bytes, t.rest)

theorem fullStrBody?_sound {cs b : Chars} {bytes : List UInt8} {rest : Chars}
    (h : fullStrBody? cs = some (b, bytes, rest)) :
    cs = b ++ '"' :: rest ∧ StringBody b bytes := by
  obtain ⟨t, _, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact ⟨t.split, t.sound⟩

end Silmaril.Formats.SExpEncoding.Wat
