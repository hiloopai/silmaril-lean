module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Encoding

/-!
# Printed scripts are lexable

`Silmaril/SpecTec/SExp/Lexical.lean` defines `SExp.Printable`: every atom of
the tree is a token (`IsBareToken` or `IsQuotedToken`) and every node tag is a
non-empty bare token.  The string-level theorems of
`Silmaril/SpecTec/IL/Encoding.lean` and
`Silmaril/SpecTec/SExp/LexicalPrinter.lean` all carry it as a hypothesis.
This file discharges it for printed scripts, and so closes the chain

```
IL.Script --scriptS--> List SExp --SExp.astFile w--> String --lexer--> List SExp
```

with `astRel_astFile`: the exact bytes `spectec --ast -o FILE` writes lex and
decode back to the script they came from, at every `--ast-width`.

## The side condition

The statement is *not* unconditional.  Almost every atom
`Silmaril/SpecTec/IL/Print.lean` emits is a token by construction:

* identifiers, texts, atoms and mixfix operators go through `textS`, i.e.
  `Escape.quote`, and `isQuotedToken_quote` shows that a quoted atom is a
  token **whatever its contents** — `IL.AtomS` and `IL.MixopS` are plain
  `String`s, but an escaped body can neither contain a bare `"` nor end in a
  dangling backslash, which is exactly `QuotedBody`;
* the numerals `decString`, `signedString`, `intString`, `ratString` and
  `hexByteString` (`Silmaril/SpecTec/IL/Digits.lean`) are nonempty runs of
  characters with code point at least `42` — digits, `+`, `-`, `/`, `0x`,
  `A`–`F` — hence bare tokens (`isBare_of_toNat_ge`);
* the fixed atoms (`true`, `false`, `bool`, `text`, `nat`, `int`, `rat`,
  `real`, the operator names, `opt`, `list`, `list1`, `root`, `eps`, `else`)
  and all forty-odd node tags are bare tokens by `decide`.

The **one** leaf that is not constrained is the payload of `Num.realN`, which
`spectec/src/xl/num.ml:25` produces with `Printf.sprintf "%.17g"` and
`Silmaril/SpecTec/IL/Ast.lean` stores as a bare `String`: a hand-built `Def`
may carry `Num.realN " "`, whose printed atom `(real  )` the lexer reads as
nothing at all.  The side condition is therefore

```
AllToken (realsDef d)
```

where `realsDef` collects exactly those payloads — one collection function per
printer, so that the hypothesis of each theorem below is a statement about the
constructor at hand — and `AllToken l` says every string in `l` is a token.
It is decidable, it is empty for every script in `specs/spectec/` (none of
which uses a `` `Real `` numeral, `docs/projects/spectec/README.md`), and it is *exact*: the
theorems are stated as iffs (`printable_defS_iff`,
`printableList_scriptS_iff`, and one per printer), so no weaker condition
would do.

`IsToken`, not `IsBareToken`, is what is needed: an atom is printable when it
is a bare token *or* a quoted one, and a real rendering that happened to be
spelled `"…"` would be read back verbatim.  Using the exact condition is what
makes the iffs true, and the iffs are what give the converse direction for
free.

## Why the condition is harmless

`allToken_realsDef_of_decodeDef?` and `allToken_realsScript_of_decodeScript?`
prove it of everything the decoder returns *from a lexable tree*, and
`allToken_realsScript_of_lexesStream` specializes that to a script read out of
an actual file, which is the form an import needs.

The hypothesis that the decoded tree is lexable cannot be dropped:
`decodeNum?` accepts *any* atom under a `real` tag, so
`exists_decodeDef?_not_printable` exhibits an `s` with `decodeDef? s = some d`
and `¬ SExp.Printable (defS d)`.  What rules the bad atom out in practice is
not the decoder but the lexer, and `printableList_of_lexesStream` — the
converse of `pp_lexesPre` — is what connects the two.

## Structure

One `mutual` block of structural-recursion theorems over `il/ast.ml`'s
recursive group, in the order of `Print.lean` and the same shape as
`Silmaril/SpecTec/IL/DecodeSound.lean`, preceded by the leaf obligations:
`isBareToken_decString` and friends for the numerals, `isQuotedToken_quote`
for the quoted atoms.  The `QuotedBody` induction runs over the escaped
*byte* list, at the `List Char` level, so it reduces; `String.toList` is only
ever forced on short literal tags.

## Axiom check

```
#print axioms printable_defS
#print axioms printableList_scriptS
#print axioms astRel_astFile
#print axioms eq_of_astFile_eq
#print axioms allToken_realsScript_of_lexesStream
```

all report `'…' depends on axioms: [propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

namespace Silmaril.SpecTec

/-! ## Everything the lexer reads is printable

The converse of `pp_lexesPre` (`Silmaril/SpecTec/SExp/LexicalPrinter.lean`):
the three rules of `LexesPre` *are* the three clauses of `SExp.Printable`, so
an S-expression that was read from a file can never be one the printer cannot
write back.  These belong next to `Printable` in
`Silmaril/SpecTec/SExp/Lexical.lean` and are proved here only because nothing
below the IL layer needs them. -/

mutual

/-- Anything the lexer reads is printable. -/
theorem printable_of_lexesPre {l : List Char} {e : SExp} {r : List Char}
    (h : LexesPre l e r) : SExp.Printable e := by
  match h with
  | .bare hs _ => exact Or.inl hs
  | .quoted hs => exact Or.inr hs
  | .node ht _ hseq => exact ⟨ht, printableList_of_lexesSeq hseq⟩

/-- Anything the lexer reads as a child list is printable. -/
theorem printableList_of_lexesSeq {l : List Char} {es : List SExp} {r : List Char}
    (h : LexesSeq l es r) : SExp.PrintableList es := by
  match h with
  | .nil _ => exact trivial
  | .cons _ hpre hseq => exact ⟨printable_of_lexesPre hpre, printableList_of_lexesSeq hseq⟩

end

/-- Every stream the lexer reads is printable. -/
theorem printableList_of_lexesStream {l : List Char} {es : List SExp}
    (h : LexesStream l es) : SExp.PrintableList es := by
  induction h with
  | nil _ => exact trivial
  | cons _ hpre _ ih => exact ⟨printable_of_lexesPre hpre, ih⟩

end Silmaril.SpecTec

namespace Silmaril.SpecTec.IL

open Silmaril.SpecTec

/-- Every character with code point at least `42` is bare: the five characters
the lexer reserves — `' '`, `'\n'`, `'('`, `')'` and `'"'` — all have smaller
code points.  This covers every character the numeral renderings of
`Silmaril/SpecTec/IL/Digits.lean` can contain. -/
theorem isBare_of_toNat_ge {c : Char} (h : 42 ≤ c.toNat) : IsBare c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (rfl | rfl) <;> exact absurd h (by decide)
  · rintro rfl; exact absurd h (by decide)
  · rintro rfl; exact absurd h (by decide)
  · rintro rfl; exact absurd h (by decide)

/-- A nonempty list of bare characters spells a bare token. -/
theorem isBareToken_ofList {l : List Char} (hne : l ≠ []) (hb : ∀ c ∈ l, IsBare c) :
    IsBareToken (String.ofList l) := by
  rw [IsBareToken, String.toList_ofList]
  exact ⟨hne, hb⟩

/-- Decimal digits are bare. -/
theorem isBare_of_mem_decDigits {n : Nat} {c : Char} (h : c ∈ Digits.decDigits n) : IsBare c :=
  isBare_of_toNat_ge (by have := Digits.toNat_of_mem_decDigits h; omega)

/-- `decString` is a bare token. -/
theorem isBareToken_decString (n : Nat) : IsBareToken (Digits.decString n) :=
  isBareToken_ofList (Digits.decDigits_ne_nil n) fun _ h => isBare_of_mem_decDigits h

/-- `signedString` is a bare token. -/
theorem isBareToken_signedString (i : Int) : IsBareToken (Digits.signedString i) := by
  refine isBareToken_ofList ?_ ?_ <;> unfold Digits.signedDigits <;> split
  · simp
  · simp
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | h
    · exact isBare_of_toNat_ge (by decide)
    · exact isBare_of_mem_decDigits h
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | h
    · exact isBare_of_toNat_ge (by decide)
    · exact isBare_of_mem_decDigits h

/-- Every character of `intDigits` is bare. -/
theorem isBare_of_mem_intDigits {i : Int} {c : Char} (h : c ∈ Digits.intDigits i) : IsBare c := by
  unfold Digits.intDigits at h
  split at h
  · rcases List.mem_cons.mp h with rfl | h
    · exact isBare_of_toNat_ge (by decide)
    · exact isBare_of_mem_decDigits h
  · exact isBare_of_mem_decDigits h

/-- `intDigits` is never empty. -/
theorem intDigits_ne_nil (i : Int) : Digits.intDigits i ≠ [] := by
  unfold Digits.intDigits
  split
  · simp
  · exact Digits.decDigits_ne_nil _

/-- `intString` is a bare token. -/
theorem isBareToken_intString (i : Int) : IsBareToken (Digits.intString i) :=
  isBareToken_ofList (intDigits_ne_nil i) fun _ h => isBare_of_mem_intDigits h

/-- `ratString` is a bare token. -/
theorem isBareToken_ratString (num : Int) (den : Nat) :
    IsBareToken (Digits.ratString num den) := by
  refine isBareToken_ofList ?_ ?_
  · simp [Digits.ratDigits]
  · intro c hc
    rw [Digits.ratDigits, List.mem_append] at hc
    rcases hc with h | h
    · exact isBare_of_mem_intDigits h
    · rcases List.mem_cons.mp h with rfl | h
      · exact isBare_of_toNat_ge (by decide)
      · exact isBare_of_mem_decDigits h

/-- Uppercase hexadecimal digits are bare. -/
theorem isBare_hexDigitChar {d : Nat} (h : d < 16) : IsBare (Digits.hexDigitChar d) := by
  unfold Digits.hexDigitChar
  split
  · rename_i h10
    exact isBare_of_toNat_ge (by rw [Digits.toNat_digitChar h10]; omega)
  · rename_i h10
    refine isBare_of_toNat_ge ?_
    rw [Silmaril.Unicode.charToNat_ofNat (Or.inl (by omega))]
    omega

/-- Every character of `hexRev` is a hexadecimal digit, hence bare. -/
theorem isBare_of_mem_hexRev : ∀ (f : Nat) {n : Nat} {c : Char},
    c ∈ Digits.hexRev f n → IsBare c := by
  intro f
  induction f with
  | zero => intro n c h; simp [Digits.hexRev] at h
  | succ f ih =>
      intro n c h
      rw [Digits.hexRev] at h
      split at h
      · rename_i h16
        rw [List.mem_singleton] at h
        exact h ▸ isBare_hexDigitChar h16
      · rcases List.mem_cons.mp h with rfl | h
        · exact isBare_hexDigitChar (Nat.mod_lt _ (by omega))
        · exact ih h

/-- Every character of `hexByte` is bare. -/
theorem isBare_of_mem_hexByte {n : Nat} {c : Char} (h : c ∈ Digits.hexByte n) : IsBare c := by
  rw [Digits.hexByte] at h
  rcases List.mem_cons.mp h with rfl | h
  · exact isBare_of_toNat_ge (by decide)
  rcases List.mem_cons.mp h with rfl | h
  · exact isBare_of_toNat_ge (by decide)
  split at h
  · rename_i h16
    rcases List.mem_cons.mp h with rfl | h
    · exact isBare_of_toNat_ge (by decide)
    · rw [List.mem_singleton] at h
      exact h ▸ isBare_hexDigitChar h16
  · exact isBare_of_mem_hexRev _ (List.mem_reverse.mp h)

/-- `hexByteString` is a bare token. -/
theorem isBareToken_hexByteString (n : Nat) : IsBareToken (Digits.hexByteString n) :=
  isBareToken_ofList (by simp [Digits.hexByte]) fun _ h => isBare_of_mem_hexByte h

/-! ## Quoted tokens -/

/-- One step: prefixing the escape of a byte preserves `QuotedBody`. -/
theorem quotedBody_escapeByte_append (b : UInt8) {rest : List Char} (h : QuotedBody rest) :
    QuotedBody (Escape.escapeByte b ++ rest) := by
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  simp only [Escape.escapeByte]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · exact .esc _ h
  · exact .esc _ h
  · exact .esc _ h
  · exact .esc _ h
  · exact .esc _ h
  · exact .esc _ h
  · have hn : (Char.ofNat b.toNat).toNat = b.toNat :=
      Silmaril.Unicode.charToNat_ofNat (Or.inl (by omega))
    refine .lit (fun hh => h1 ?_) (fun hh => h2 ?_) h
    · rw [← hn, hh]; rfl
    · rw [← hn, hh]; rfl
  · have k1 : b.toNat / 100 < 10 := by omega
    have k2 : b.toNat / 10 % 10 < 10 := by omega
    have k3 : b.toNat % 10 < 10 := by omega
    exact .esc _ (.lit (Escape.digitChar_ne k2 (by decide))
      (Escape.digitChar_ne k2 (by decide))
      (.lit (Escape.digitChar_ne k3 (by decide))
        (Escape.digitChar_ne k3 (by decide)) h))

/-- An escaped byte string is a quoted body: it contains no bare `"`, and
every backslash in it is followed by a character. -/
theorem quotedBody_escapeBytes (bs : List UInt8) : QuotedBody (Escape.escapeBytes bs) := by
  induction bs with
  | nil => exact .nil
  | cons b bs ih => rw [Escape.escapeBytes]; exact quotedBody_escapeByte_append b ih

/-- `String.escaped t` is a quoted body. -/
theorem quotedBody_escape (t : String) : QuotedBody (Escape.escape t).toList := by
  rw [Escape.escape_eq, String.toList_ofList]
  exact quotedBody_escapeBytes _

/-- **Every quoted atom is a token**, whatever the text inside it: identifiers,
texts, atoms and mixfix operators are therefore never a problem. -/
theorem isQuotedToken_quote (t : String) : IsQuotedToken (Escape.quote t) :=
  ⟨(Escape.escape t).toList, Escape.toList_quote t, quotedBody_escape t⟩

/-! ## The side condition -/

/-- Every string in `l` is a token. -/
def AllToken (l : List String) : Prop := ∀ t ∈ l, IsToken t

/-- The side condition is decidable. -/
instance (l : List String) : Decidable (AllToken l) := by unfold AllToken; infer_instance

/-- The empty list of real renderings. -/
@[simp] theorem allToken_nil : AllToken [] := by simp [AllToken]

/-- `AllToken` on a cons. -/
@[simp] theorem allToken_cons {t : String} {l : List String} :
    AllToken (t :: l) ↔ IsToken t ∧ AllToken l := by simp [AllToken]

/-- `AllToken` distributes over concatenation, which is how the hypotheses of
the theorems below split along the child lists `print.ml` glues together. -/
@[simp] theorem allToken_append {a b : List String} :
    AllToken (a ++ b) ↔ AllToken a ∧ AllToken b := by
  simp only [AllToken, List.mem_append]
  exact ⟨fun h => ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩,
    fun h t ht => ht.elim (h.1 t) (h.2 t)⟩

/-- The `` `Real `` renderings of a numeral: the one atom `print.ml:16-20`
emits that is not built by `Escape.quote` or by `Silmaril/SpecTec/IL/Digits.lean`. -/
def realsNum : Num → List String
  | .natN _ => []
  | .intN _ => []
  | .ratN _ => []
  | .realN r => [r]

/-! The `` `Real `` renderings of a definition and its companions, in the
order of `Silmaril/SpecTec/IL/Print.lean`: one function per printer,
collecting the payload of every `Num.realN` the printer would emit as a bare
atom.  Everything else the printers emit is a token unconditionally, so this
list is exactly the set of leaves that can make a printed tree unlexable. -/

mutual

/-- The real renderings of an `iter` (`print.ml:55`). -/
def realsIter : Iter → List String
  | .opt => []
  | .list => []
  | .list1 => []
  | .listN e none => realsExp e
  | .listN e (some _) => realsExp e

/-- The real renderings of a `typ` (`print.ml:71`). -/
def realsTyp : Typ → List String
  | .varT _ args => realsArgs args
  | .boolT => []
  | .numT _ => []
  | .textT => []
  | .tupT binds => realsTypBinds binds
  | .iterT t it => realsTyp t ++ realsIter it

/-- The real renderings of a `typbind` list (`print.ml:77`). -/
def realsTypBinds : List TypBind → List String
  | [] => []
  | b :: bs => realsTypBind b ++ realsTypBinds bs

/-- The real renderings of a `typbind` (`print.ml:86`). -/
def realsTypBind : TypBind → List String
  | .mk _ t => realsTyp t

/-- The real renderings of a `deftyp` (`print.ml:80`). -/
def realsDefTyp : DefTyp → List String
  | .aliasT t => realsTyp t
  | .structT fields => realsTypFields fields
  | .variantT cases => realsTypCases cases

/-- The real renderings of a `typfield` list (`print.ml:83`). -/
def realsTypFields : List TypField → List String
  | [] => []
  | f :: fs => realsTypField f ++ realsTypFields fs

/-- The real renderings of a `typfield` (`print.ml:89`). -/
def realsTypField : TypField → List String
  | .mk _ t quants prems => realsTyp t ++ realsParams quants ++ realsPrems prems

/-- The real renderings of a `typcase` list (`print.ml:84`). -/
def realsTypCases : List TypCase → List String
  | [] => []
  | c :: cs => realsTypCase c ++ realsTypCases cs

/-- The real renderings of a `typcase` (`print.ml:92`). -/
def realsTypCase : TypCase → List String
  | .mk _ t quants prems => realsTyp t ++ realsParams quants ++ realsPrems prems

/-- The real renderings of an `exp` (`print.ml:98`). -/
def realsExp : Exp → List String
  | .varE _ => []
  | .boolE _ => []
  | .numE n => realsNum n
  | .textE _ => []
  | .unE _ _ e => realsExp e
  | .binE _ _ e₁ e₂ => realsExp e₁ ++ realsExp e₂
  | .cmpE _ _ e₁ e₂ => realsExp e₁ ++ realsExp e₂
  | .idxE e₁ e₂ => realsExp e₁ ++ realsExp e₂
  | .sliceE e₁ e₂ e₃ => realsExp e₁ ++ realsExp e₂ ++ realsExp e₃
  | .updE e₁ p e₂ => realsExp e₁ ++ realsPath p ++ realsExp e₂
  | .extE e₁ p e₂ => realsExp e₁ ++ realsPath p ++ realsExp e₂
  | .strE fields => realsExpFields fields
  | .dotE e _ => realsExp e
  | .compE e₁ e₂ => realsExp e₁ ++ realsExp e₂
  | .memE e₁ e₂ => realsExp e₁ ++ realsExp e₂
  | .lenE e => realsExp e
  | .tupE es => realsExps es
  | .callE _ args => realsArgs args
  | .iterE e it => realsExp e ++ realsIterExp it
  | .projE e _ => realsExp e
  | .caseE _ e => realsExp e
  | .uncaseE e _ => realsExp e
  | .optE none => []
  | .optE (some e) => realsExp e
  | .theE e => realsExp e
  | .listE es => realsExps es
  | .liftE e => realsExp e
  | .catE e₁ e₂ => realsExp e₁ ++ realsExp e₂
  | .cvtE e _ _ => realsExp e
  | .subE e t₁ t₂ => realsTyp t₁ ++ realsTyp t₂ ++ realsExp e

/-- The real renderings of an `exp` list (`print.ml:116,124`). -/
def realsExps : List Exp → List String
  | [] => []
  | e :: es => realsExp e ++ realsExps es

/-- The real renderings of an `expfield` list (`print.ml:111`). -/
def realsExpFields : List ExpField → List String
  | [] => []
  | f :: fs => realsExpField f ++ realsExpFields fs

/-- The real renderings of an `expfield` (`print.ml:130`). -/
def realsExpField : ExpField → List String
  | .mk _ e => realsExp e

/-- The real renderings of a `path` (`print.ml:133`). -/
def realsPath : Path → List String
  | .rootP => []
  | .idxP p e => realsPath p ++ realsExp e
  | .sliceP p e₁ e₂ => realsPath p ++ realsExp e₁ ++ realsExp e₂
  | .dotP p _ => realsPath p

/-- The real renderings of an `iterexp` (`print.ml:140`). -/
def realsIterExp : IterExp → List String
  | .mk it doms => realsIter it ++ realsDoms doms

/-- The real renderings of a `dom` list (`print.ml:141`). -/
def realsDoms : List Dom → List String
  | [] => []
  | d :: ds => realsDom d ++ realsDoms ds

/-- The real renderings of a `dom` (`print.ml:141`). -/
def realsDom : Dom → List String
  | .mk _ e => realsExp e

/-- The real renderings of a `sym` (`print.ml:146`). -/
def realsSym : Sym → List String
  | .varG _ args => realsArgs args
  | .numG _ => []
  | .textG _ => []
  | .epsG => []
  | .seqG gs => realsSyms gs
  | .altG gs => realsSyms gs
  | .rangeG g₁ g₂ => realsSym g₁ ++ realsSym g₂
  | .iterG g it => realsSym g ++ realsIterExp it
  | .attrG e g => realsExp e ++ realsSym g

/-- The real renderings of a `sym` list (`print.ml:152,153`). -/
def realsSyms : List Sym → List String
  | [] => []
  | g :: gs => realsSym g ++ realsSyms gs

/-- The real renderings of a `prem` (`print.ml:161`). -/
def realsPrem : Prem → List String
  | .rulePr _ args _ e => realsArgs args ++ realsExp e
  | .ifPr e => realsExp e
  | .letPr e₁ e₂ => realsExp e₁ ++ realsExp e₂
  | .elsePr => []
  | .iterPr pr it => realsPrem pr ++ realsIterExp it

/-- The real renderings of a `prem` list (`print.ml:90,93`). -/
def realsPrems : List Prem → List String
  | [] => []
  | p :: ps => realsPrem p ++ realsPrems ps

/-- The real renderings of an `arg` (`print.ml:172`). -/
def realsArg : Arg → List String
  | .expA e => realsExp e
  | .typA t => realsTyp t
  | .defA _ => []
  | .gramA g => realsSym g

/-- The real renderings of an `arg` list (`print.ml:73,117,148`). -/
def realsArgs : List Arg → List String
  | [] => []
  | a :: as => realsArg a ++ realsArgs as

/-- The real renderings of a `param` (`print.ml:179`). -/
def realsParam : Param → List String
  | .expP _ t => realsTyp t
  | .typP _ => []
  | .defP _ ps t => realsParams ps ++ realsTyp t
  | .gramP _ ps t => realsParams ps ++ realsTyp t

/-- The real renderings of a `param` list (`print.ml:183`). -/
def realsParams : List Param → List String
  | [] => []
  | p :: ps => realsParam p ++ realsParams ps

/-- The real renderings of an `inst` (`print.ml:186`). -/
def realsInst : Inst → List String
  | .instD quants args dt => realsParams quants ++ realsArgs args ++ realsDefTyp dt

/-- The real renderings of an `inst` list (`print.ml:209`). -/
def realsInsts : List Inst → List String
  | [] => []
  | i :: is => realsInst i ++ realsInsts is

/-- The real renderings of a `rule` (`print.ml:191`). -/
def realsRule : Rule → List String
  | .ruleD _ quants _ e prems => realsParams quants ++ realsExp e ++ realsPrems prems

/-- The real renderings of a `rule` list (`print.ml:211`). -/
def realsRules : List Rule → List String
  | [] => []
  | r :: rs => realsRule r ++ realsRules rs

/-- The real renderings of a `clause` (`print.ml:196`). -/
def realsClause : Clause → List String
  | .defD quants args e prems =>
      realsParams quants ++ realsArgs args ++ realsExp e ++ realsPrems prems

/-- The real renderings of a `clause` list (`print.ml:213`). -/
def realsClauses : List Clause → List String
  | [] => []
  | c :: cs => realsClause c ++ realsClauses cs

/-- The real renderings of a `prod` (`print.ml:201`). -/
def realsProd : Prod → List String
  | .prodD quants g e prems =>
      realsParams quants ++ realsSym g ++ realsExp e ++ realsPrems prems

/-- The real renderings of a `prod` list (`print.ml:215`). -/
def realsProds : List Prod → List String
  | [] => []
  | q :: qs => realsProd q ++ realsProds qs

/-- The real renderings of a `def` (`print.ml:206`). -/
def realsDef : Def → List String
  | .typD _ ps insts => realsParams ps ++ realsInsts insts
  | .relD _ ps _ t rules => realsParams ps ++ realsTyp t ++ realsRules rules
  | .decD _ ps t clauses => realsParams ps ++ realsTyp t ++ realsClauses clauses
  | .gramD _ ps t prods => realsParams ps ++ realsTyp t ++ realsProds prods
  | .recD ds => realsDefs ds

/-- The real renderings of a `def` list (`print.ml:217`). -/
def realsDefs : List Def → List String
  | [] => []
  | d :: ds => realsDef d ++ realsDefs ds

end

/-- The real renderings of a whole script (`print.ml:225`). -/
def realsScript (s : Script) : List String := realsDefs s

/-! ## Leaves -/

/-- `PrintableList` distributes over concatenation. -/
@[simp] theorem printableList_append (a b : List SExp) :
    SExp.PrintableList (a ++ b) ↔ SExp.PrintableList a ∧ SExp.PrintableList b := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, and_assoc]

/-- Every quoted atom is printable. -/
@[simp] theorem printable_textS (t : String) : SExp.Printable (textS t) :=
  Or.inr (isQuotedToken_quote t)

/-- `bool b = Atom (Bool.to_string b)` is a bare atom (`print.ml:11`). -/
@[simp] theorem printable_boolS (b : Bool) : SExp.Printable (boolS b) := by
  cases b
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)

/-- `print.ml:16-20`: the `` `Real `` payload is the only atom here that is
not a numeral rendering. -/
@[simp] theorem printable_numS (n : Num) : SExp.Printable (numS n) ↔ AllToken (realsNum n) := by
  cases n with
  | natN k => simp +decide [numS, realsNum, IsToken, isBareToken_decString k]
  | intN i => simp +decide [numS, realsNum, IsToken, isBareToken_signedString i]
  | ratN q => simp +decide [numS, realsNum, IsToken, isBareToken_ratString q.num q.den]
  | realN r => simp +decide [numS, realsNum, IsToken]

/-- `unop` is a bare atom (`print.ml:25`). -/
@[simp] theorem printable_unOpS (op : UnOp) : SExp.Printable (unOpS op) := by
  cases op <;> exact Or.inl (by decide)

/-- `binop` is a bare atom (`print.ml:32`). -/
@[simp] theorem printable_binOpS (op : BinOp) : SExp.Printable (binOpS op) := by
  cases op <;> exact Or.inl (by decide)

/-- `cmpop` is a bare atom (`print.ml:44`). -/
@[simp] theorem printable_cmpOpS (op : CmpOp) : SExp.Printable (cmpOpS op) := by
  cases op <;> exact Or.inl (by decide)

/-- `numtyp` is a bare atom (`print.ml:65`). -/
@[simp] theorem printable_numTypS (t : NumTyp) : SExp.Printable (numTypS t) := by
  cases t <;> exact Or.inl (by decide)

/-- `optyp` is a bare atom (`print.ml:67`). -/
@[simp] theorem printable_opTypS (t : OpTyp) : SExp.Printable (opTypS t) := by
  cases t with
  | boolT => exact Or.inl (by decide)
  | numT t => exact printable_numTypS t

/-! ## The recursive group -/

mutual

/-- `iterS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:55`). -/
theorem printable_iterS : ∀ it : Iter, SExp.Printable (iterS it) ↔ AllToken (realsIter it)
  | .opt => by simp +decide
  | .list => by simp +decide
  | .list1 => by simp +decide
  | .listN e none => by simp +decide [iterS, realsIter, printable_expS e]
  | .listN e (some x) => by simp +decide [iterS, realsIter, printable_expS e]

/-- `typS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:71`). -/
theorem printable_typS : ∀ t : Typ, SExp.Printable (typS t) ↔ AllToken (realsTyp t)
  | .varT x args => by simp +decide [typS, realsTyp, printableList_argsS args]
  | .boolT => by simp +decide
  | .numT t => by simp +decide [typS, realsTyp]
  | .textT => by simp +decide
  | .tupT binds => by simp +decide [typS, realsTyp, printableList_typBindsS binds]
  | .iterT t it => by
      simp +decide [typS, realsTyp, printable_typS t, printable_iterS it]

/-- `typBindsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:77`). -/
theorem printableList_typBindsS :
    ∀ bs : List TypBind, SExp.PrintableList (typBindsS bs) ↔ AllToken (realsTypBinds bs)
  | [] => by simp [typBindsS, realsTypBinds]
  | b :: bs => by
      simp [typBindsS, realsTypBinds, printable_typBindS b, printableList_typBindsS bs]

/-- `typBindS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:86`). -/
theorem printable_typBindS :
    ∀ b : TypBind, SExp.Printable (typBindS b) ↔ AllToken (realsTypBind b)
  | .mk x t => by simp +decide [typBindS, realsTypBind, printable_typS t]

/-- `defTypS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:80`). -/
theorem printable_defTypS :
    ∀ dt : DefTyp, SExp.Printable (defTypS dt) ↔ AllToken (realsDefTyp dt)
  | .aliasT t => by simp +decide [defTypS, realsDefTyp, printable_typS t]
  | .structT fs => by simp +decide [defTypS, realsDefTyp, printableList_typFieldsS fs]
  | .variantT cs => by simp +decide [defTypS, realsDefTyp, printableList_typCasesS cs]

/-- `typFieldsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:83`). -/
theorem printableList_typFieldsS :
    ∀ fs : List TypField, SExp.PrintableList (typFieldsS fs) ↔ AllToken (realsTypFields fs)
  | [] => by simp [typFieldsS, realsTypFields]
  | f :: fs => by
      simp [typFieldsS, realsTypFields, printable_typFieldS f, printableList_typFieldsS fs]

/-- `typFieldS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:89`). -/
theorem printable_typFieldS :
    ∀ f : TypField, SExp.Printable (typFieldS f) ↔ AllToken (realsTypField f)
  | .mk a t quants prems => by
      simp +decide [typFieldS, realsTypField, printable_typS t,
        printableList_paramsS quants, printableList_premsS prems]

/-- `typCasesS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:84`). -/
theorem printableList_typCasesS :
    ∀ cs : List TypCase, SExp.PrintableList (typCasesS cs) ↔ AllToken (realsTypCases cs)
  | [] => by simp [typCasesS, realsTypCases]
  | c :: cs => by
      simp [typCasesS, realsTypCases, printable_typCaseS c, printableList_typCasesS cs]

/-- `typCaseS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:92`). -/
theorem printable_typCaseS :
    ∀ c : TypCase, SExp.Printable (typCaseS c) ↔ AllToken (realsTypCase c)
  | .mk op t quants prems => by
      simp +decide [typCaseS, realsTypCase, printable_typS t,
        printableList_paramsS quants, printableList_premsS prems]

/-- `expS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:98`). -/
theorem printable_expS : ∀ e : Exp, SExp.Printable (expS e) ↔ AllToken (realsExp e)
  | .varE x => by simp +decide [expS, realsExp]
  | .boolE b => by simp +decide [expS, realsExp]
  | .numE n => by simp +decide [expS, realsExp, printable_numS n]
  | .textE t => by simp +decide [expS, realsExp]
  | .unE op t e => by simp +decide [expS, realsExp, printable_expS e]
  | .binE op t e₁ e₂ => by
      simp +decide [expS, realsExp, printable_expS e₁, printable_expS e₂]
  | .cmpE op t e₁ e₂ => by
      simp +decide [expS, realsExp, printable_expS e₁, printable_expS e₂]
  | .idxE e₁ e₂ => by simp +decide [expS, realsExp, printable_expS e₁, printable_expS e₂]
  | .sliceE e₁ e₂ e₃ => by
      simp +decide [expS, realsExp, printable_expS e₁, printable_expS e₂,
        printable_expS e₃]
  | .updE e₁ p e₂ => by
      simp +decide [expS, realsExp, printable_expS e₁, printable_pathS p,
        printable_expS e₂]
  | .extE e₁ p e₂ => by
      simp +decide [expS, realsExp, printable_expS e₁, printable_pathS p,
        printable_expS e₂]
  | .strE fields => by simp +decide [expS, realsExp, printableList_expFieldsS fields]
  | .dotE e a => by simp +decide [expS, realsExp, printable_expS e]
  | .compE e₁ e₂ => by simp +decide [expS, realsExp, printable_expS e₁, printable_expS e₂]
  | .memE e₁ e₂ => by simp +decide [expS, realsExp, printable_expS e₁, printable_expS e₂]
  | .lenE e => by simp +decide [expS, realsExp, printable_expS e]
  | .tupE es => by simp +decide [expS, realsExp, printableList_expsS es]
  | .callE x args => by simp +decide [expS, realsExp, printableList_argsS args]
  | .iterE e it => by
      simp +decide [expS, realsExp, printable_expS e, printableList_iterExpS it]
  | .projE e i => by
      simp +decide [expS, realsExp, printable_expS e, IsToken, isBareToken_intString i]
  | .caseE op e => by simp +decide [expS, realsExp, printable_expS e]
  | .uncaseE e op => by simp +decide [expS, realsExp, printable_expS e]
  | .optE none => by simp +decide
  | .optE (some e) => by simp +decide [expS, realsExp, printable_expS e]
  | .theE e => by simp +decide [expS, realsExp, printable_expS e]
  | .listE es => by simp +decide [expS, realsExp, printableList_expsS es]
  | .liftE e => by simp +decide [expS, realsExp, printable_expS e]
  | .catE e₁ e₂ => by simp +decide [expS, realsExp, printable_expS e₁, printable_expS e₂]
  | .cvtE e t₁ t₂ => by simp +decide [expS, realsExp, printable_expS e]
  | .subE e t₁ t₂ => by
      simp +decide [expS, realsExp, printable_typS t₁, printable_typS t₂,
        printable_expS e]

/-- `expsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:116,124`). -/
theorem printableList_expsS :
    ∀ es : List Exp, SExp.PrintableList (expsS es) ↔ AllToken (realsExps es)
  | [] => by simp [expsS, realsExps]
  | e :: es => by simp [expsS, realsExps, printable_expS e, printableList_expsS es]

/-- `expFieldsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:111`). -/
theorem printableList_expFieldsS :
    ∀ fs : List ExpField, SExp.PrintableList (expFieldsS fs) ↔ AllToken (realsExpFields fs)
  | [] => by simp [expFieldsS, realsExpFields]
  | f :: fs => by
      simp [expFieldsS, realsExpFields, printable_expFieldS f, printableList_expFieldsS fs]

/-- `expFieldS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:130`). -/
theorem printable_expFieldS :
    ∀ f : ExpField, SExp.Printable (expFieldS f) ↔ AllToken (realsExpField f)
  | .mk a e => by simp +decide [expFieldS, realsExpField, printable_expS e]

/-- `pathS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:133`). -/
theorem printable_pathS : ∀ p : Path, SExp.Printable (pathS p) ↔ AllToken (realsPath p)
  | .rootP => by simp +decide
  | .idxP p e => by simp +decide [pathS, realsPath, printable_pathS p, printable_expS e]
  | .sliceP p e₁ e₂ => by
      simp +decide [pathS, realsPath, printable_pathS p, printable_expS e₁,
        printable_expS e₂]
  | .dotP p a => by simp +decide [pathS, realsPath, printable_pathS p]

/-- `iterExpS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:140`). -/
theorem printableList_iterExpS :
    ∀ it : IterExp, SExp.PrintableList (iterExpS it) ↔ AllToken (realsIterExp it)
  | .mk i doms => by
      simp [iterExpS, realsIterExp, printable_iterS i, printableList_domsS doms]

/-- `domsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:141`). -/
theorem printableList_domsS :
    ∀ ds : List Dom, SExp.PrintableList (domsS ds) ↔ AllToken (realsDoms ds)
  | [] => by simp [domsS, realsDoms]
  | d :: ds => by simp [domsS, realsDoms, printable_domS d, printableList_domsS ds]

/-- `domS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:141`). -/
theorem printable_domS : ∀ d : Dom, SExp.Printable (domS d) ↔ AllToken (realsDom d)
  | .mk x e => by simp +decide [domS, realsDom, printable_expS e]

/-- `symS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:146`). -/
theorem printable_symS : ∀ g : Sym, SExp.Printable (symS g) ↔ AllToken (realsSym g)
  | .varG x args => by simp +decide [symS, realsSym, printableList_argsS args]
  | .numG n => by simp +decide [symS, realsSym, IsToken, isBareToken_hexByteString n]
  | .textG t => by simp +decide [symS, realsSym]
  | .epsG => by simp +decide
  | .seqG gs => by simp +decide [symS, realsSym, printableList_symsS gs]
  | .altG gs => by simp +decide [symS, realsSym, printableList_symsS gs]
  | .rangeG g₁ g₂ => by simp +decide [symS, realsSym, printable_symS g₁, printable_symS g₂]
  | .iterG g it => by
      simp +decide [symS, realsSym, printable_symS g, printableList_iterExpS it]
  | .attrG e g => by simp +decide [symS, realsSym, printable_expS e, printable_symS g]

/-- `symsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:152,153`). -/
theorem printableList_symsS :
    ∀ gs : List Sym, SExp.PrintableList (symsS gs) ↔ AllToken (realsSyms gs)
  | [] => by simp [symsS, realsSyms]
  | g :: gs => by simp [symsS, realsSyms, printable_symS g, printableList_symsS gs]

/-- `premS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:161`). -/
theorem printable_premS : ∀ p : Prem, SExp.Printable (premS p) ↔ AllToken (realsPrem p)
  | .rulePr x args op e => by
      simp +decide [premS, realsPrem, printableList_argsS args, printable_expS e]
  | .ifPr e => by simp +decide [premS, realsPrem, printable_expS e]
  | .letPr e₁ e₂ => by simp +decide [premS, realsPrem, printable_expS e₁, printable_expS e₂]
  | .elsePr => by simp +decide
  | .iterPr pr it => by
      simp +decide [premS, realsPrem, printable_premS pr, printableList_iterExpS it]

/-- `premsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:90,93`). -/
theorem printableList_premsS :
    ∀ ps : List Prem, SExp.PrintableList (premsS ps) ↔ AllToken (realsPrems ps)
  | [] => by simp [premsS, realsPrems]
  | p :: ps => by simp [premsS, realsPrems, printable_premS p, printableList_premsS ps]

/-- `argS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:172`). -/
theorem printable_argS : ∀ a : Arg, SExp.Printable (argS a) ↔ AllToken (realsArg a)
  | .expA e => by simp +decide [argS, realsArg, printable_expS e]
  | .typA t => by simp +decide [argS, realsArg, printable_typS t]
  | .defA x => by simp +decide [argS, realsArg]
  | .gramA g => by simp +decide [argS, realsArg, printable_symS g]

/-- `argsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:73,117,148`). -/
theorem printableList_argsS :
    ∀ as : List Arg, SExp.PrintableList (argsS as) ↔ AllToken (realsArgs as)
  | [] => by simp [argsS, realsArgs]
  | a :: as => by simp [argsS, realsArgs, printable_argS a, printableList_argsS as]

/-- `paramS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:179`). -/
theorem printable_paramS : ∀ p : Param, SExp.Printable (paramS p) ↔ AllToken (realsParam p)
  | .expP x t => by simp +decide [paramS, realsParam, printable_typS t]
  | .typP x => by simp +decide [paramS, realsParam]
  | .defP x ps t => by
      simp +decide [paramS, realsParam, printableList_paramsS ps, printable_typS t]
  | .gramP x ps t => by
      simp +decide [paramS, realsParam, printableList_paramsS ps, printable_typS t]

/-- `paramsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:183`). -/
theorem printableList_paramsS :
    ∀ ps : List Param, SExp.PrintableList (paramsS ps) ↔ AllToken (realsParams ps)
  | [] => by simp [paramsS, realsParams]
  | p :: ps => by simp [paramsS, realsParams, printable_paramS p, printableList_paramsS ps]

/-- `instS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:186`). -/
theorem printable_instS : ∀ i : Inst, SExp.Printable (instS i) ↔ AllToken (realsInst i)
  | .instD quants args dt => by
      simp +decide [instS, realsInst, printableList_paramsS quants,
        printableList_argsS args, printable_defTypS dt]

/-- `instsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:209`). -/
theorem printableList_instsS :
    ∀ is : List Inst, SExp.PrintableList (instsS is) ↔ AllToken (realsInsts is)
  | [] => by simp [instsS, realsInsts]
  | i :: is => by simp [instsS, realsInsts, printable_instS i, printableList_instsS is]

/-- `ruleS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:191`). -/
theorem printable_ruleS : ∀ r : Rule, SExp.Printable (ruleS r) ↔ AllToken (realsRule r)
  | .ruleD x quants op e prems => by
      simp +decide [ruleS, realsRule, printableList_paramsS quants, printable_expS e,
        printableList_premsS prems]

/-- `rulesS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:211`). -/
theorem printableList_rulesS :
    ∀ rs : List Rule, SExp.PrintableList (rulesS rs) ↔ AllToken (realsRules rs)
  | [] => by simp [rulesS, realsRules]
  | r :: rs => by simp [rulesS, realsRules, printable_ruleS r, printableList_rulesS rs]

/-- `clauseS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:196`). -/
theorem printable_clauseS :
    ∀ c : Clause, SExp.Printable (clauseS c) ↔ AllToken (realsClause c)
  | .defD quants args e prems => by
      simp +decide [clauseS, realsClause, printableList_paramsS quants,
        printableList_argsS args, printable_expS e, printableList_premsS prems]

/-- `clausesS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:213`). -/
theorem printableList_clausesS :
    ∀ cs : List Clause, SExp.PrintableList (clausesS cs) ↔ AllToken (realsClauses cs)
  | [] => by simp [clausesS, realsClauses]
  | c :: cs => by
      simp [clausesS, realsClauses, printable_clauseS c, printableList_clausesS cs]

/-- `prodS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:201`). -/
theorem printable_prodS : ∀ q : Prod, SExp.Printable (prodS q) ↔ AllToken (realsProd q)
  | .prodD quants g e prems => by
      simp +decide [prodS, realsProd, printableList_paramsS quants, printable_symS g,
        printable_expS e, printableList_premsS prems]

/-- `prodsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:215`). -/
theorem printableList_prodsS :
    ∀ qs : List Prod, SExp.PrintableList (prodsS qs) ↔ AllToken (realsProds qs)
  | [] => by simp [prodsS, realsProds]
  | q :: qs => by simp [prodsS, realsProds, printable_prodS q, printableList_prodsS qs]

/-- `defS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:206`). -/
theorem printable_defS_iff : ∀ d : Def, SExp.Printable (defS d) ↔ AllToken (realsDef d)
  | .typD x ps insts => by
      simp +decide [defS, realsDef, printableList_paramsS ps, printableList_instsS insts]
  | .relD x ps op t rules => by
      simp +decide [defS, realsDef, printableList_paramsS ps, printable_typS t,
        printableList_rulesS rules]
  | .decD x ps t clauses => by
      simp +decide [defS, realsDef, printableList_paramsS ps, printable_typS t,
        printableList_clausesS clauses]
  | .gramD x ps t prods => by
      simp +decide [defS, realsDef, printableList_paramsS ps, printable_typS t,
        printableList_prodsS prods]
  | .recD ds => by simp +decide [defS, realsDef, printableList_defsS ds]

/-- `defsS` is printable exactly when its `` `Real `` renderings are tokens
(`print.ml:217`). -/
theorem printableList_defsS :
    ∀ ds : List Def, SExp.PrintableList (defsS ds) ↔ AllToken (realsDefs ds)
  | [] => by simp [defsS, realsDefs]
  | d :: ds => by simp [defsS, realsDefs, printable_defS_iff d, printableList_defsS ds]

end

/-! ## The headline statements -/

/-- **Every printed definition is lexable** as soon as its `` `Real ``
renderings are tokens — which is automatic for everything `--ast` writes,
since `Printf.sprintf "%.17g"` (`spectec/src/xl/num.ml:25`) never emits a
space, a parenthesis or a quotation mark. -/
theorem printable_defS (d : Def) (h : AllToken (realsDef d)) : SExp.Printable (defS d) :=
  (printable_defS_iff d).mpr h

/-- The script-level form of `printable_defS_iff` (`print.ml:225`). -/
theorem printableList_scriptS_iff (s : Script) :
    SExp.PrintableList (scriptS s) ↔ AllToken (realsScript s) := printableList_defsS s

/-- **Every printed script is lexable** under the same side condition. -/
theorem printableList_scriptS (s : Script) (h : AllToken (realsScript s)) :
    SExp.PrintableList (scriptS s) := (printableList_scriptS_iff s).mpr h

/-! ## The side condition is harmless -/

/-- Everything `decodeDef?` reads out of a *lexable* tree satisfies the side
condition.  The hypothesis cannot be dropped: see
`exists_decodeDef?_not_printable`. -/
theorem allToken_realsDef_of_decodeDef? {s : SExp} {d : Def} (hs : SExp.Printable s)
    (h : decodeDef? s = some d) : AllToken (realsDef d) := by
  refine (printable_defS_iff d).mp ?_
  rw [defS_of_decodeDef? h]
  exact hs

/-- The script-level form. -/
theorem allToken_realsScript_of_decodeScript? {ss : List SExp} {s : Script}
    (hs : SExp.PrintableList ss) (h : decodeScript? ss = some s) :
    AllToken (realsScript s) := by
  refine (printableList_scriptS_iff s).mp ?_
  rw [scriptS_of_decodeScript? h]
  exact hs

/-- **What an import needs.**  A script read out of an actual `--ast` file —
lexed by the convention of `Silmaril/SpecTec/SExp/Lexical.lean`, then decoded
— always satisfies the side condition, so `astRel_astFile` applies to it
with no further obligation. -/
theorem allToken_realsScript_of_lexesStream {str : String} {ss : List SExp} {s : Script}
    (hl : LexesStream str.toList ss) (hd : decodeScript? ss = some s) :
    AllToken (realsScript s) :=
  allToken_realsScript_of_decodeScript? (printableList_of_lexesStream hl) hd

/-- A definition the decoder accepts but the printer cannot write back: the
`` `Real `` rendering `" "` is neither a bare run nor a quoted token, so the
atom `(real  )` would lex as nothing at all. -/
def badRealDef : Def := .decD "x" [] .boolT [.defD [] [] (.numE (.realN " ")) []]

/-- `badRealDef` fails the side condition. -/
theorem not_printable_defS_badRealDef : ¬ SExp.Printable (defS badRealDef) := by
  rw [printable_defS_iff]
  decide

/-- **The side condition is necessary.**  `decodeDef?` alone does not imply
it, because `decodeNum?` (`Decode.lean`) accepts any atom at all under a
`real` tag; what rules out the bad atom is that the tree was *lexed*, which
is what `allToken_realsDef_of_decodeDef?` assumes. -/
theorem exists_decodeDef?_not_printable :
    ∃ (s : SExp) (d : Def), decodeDef? s = some d ∧ ¬ SExp.Printable (defS d) :=
  ⟨defS badRealDef, badRealDef, decodeDef?_defS badRealDef, not_printable_defS_badRealDef⟩

/-! ## The `--ast` file -/

/-- **End to end.**  The exact bytes `spectec --ast -o FILE` writes for a
script lex and decode back to that script, at every `--ast-width`. -/
theorem astRel_astFile (width : Nat) (s : Script) (h : AllToken (realsScript s)) :
    astRel (astFile width s) s := astFile_astRel (printableList_scriptS s h)

/-- `astFile` is a correct encoder for `astRel` on the scripts that satisfy
the side condition; sharper than `astRel_encoderCorrectOn`, whose predicate is
about the printed tree. -/
theorem astRel_encoderCorrectOn_allToken (width : Nat) :
    astRel.EncoderCorrectOn (fun s => AllToken (realsScript s)) (astFile width) :=
  fun s h => astRel_astFile width s h

/-- **The bytes determine the script.**  Two scripts whose `--ast` files agree
are equal, even when the two files were written at different `--ast-width`
settings: `astRel_functional` does not see the width. -/
theorem eq_of_astFile_eq {w w' : Nat} {s s' : Script} (h : AllToken (realsScript s))
    (h' : AllToken (realsScript s')) (heq : astFile w s = astFile w' s') : s = s' :=
  astRel_functional (heq ▸ astRel_astFile w s h) (astRel_astFile w' s' h')

end Silmaril.SpecTec.IL
