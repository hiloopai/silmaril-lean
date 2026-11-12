module

/-!
# SpecTec atoms

A transcription of `atom'` and `Atom.to_string` from `spectec/src/xl/atom.ml`
at `608711107b7f1edb13efd57b7d79b49477462d36`.

OCaml's `atom` is `(atom', info) note_phrase` (`spectec/src/xl/atom.ml:7`), so
a full atom carries two things besides the constructor transcribed below: the
source region of the `phrase`, and the mutable note
`info = {mutable def : string; mutable case : string}`
(`spectec/src/xl/atom.ml:3`), which the elaborator fills in with the type and
the case an atom was resolved against.  Neither is transcribed here:
`spectec/src/backend-ast/print.ml:12` prints an atom as
`text (Atom.to_string atom)`, i.e. as the rendering of `atom.it` alone, so no
`--ast` stream can observe a region or an `info`.

`Atom.toString` is therefore the whole observable content of an atom, and
`Atom.ofString` is the section of it through which the `Silmaril.SpecTec.IL`
AST's rendered atoms (`AtomS`) are read back.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

/-- `atom'`, the SpecTec atom constructors (`spectec/src/xl/atom.ml:8`).

The `info` note and the source region of `atom = (atom', info) note_phrase`
(`spectec/src/xl/atom.ml:7`) are deliberately not transcribed; see the module
docstring. -/
inductive Atom where
  /-- `Atom of string`, an atom identifier (`spectec/src/xl/atom.ml:9`).
  Rendered as the identifier itself, the wildcard `Atom "_"` included. -/
  | atom (id : String)
  /-- `Infinity`, rendered `"infinity"` (`spectec/src/xl/atom.ml:10`). -/
  | infinity
  /-- `Bot`, rendered `"_|_"` (`spectec/src/xl/atom.ml:11`). -/
  | bot
  /-- `Top`, rendered `"^|^"` (`spectec/src/xl/atom.ml:12`). -/
  | top
  /-- `Dot`, rendered `"."` (`spectec/src/xl/atom.ml:13`). -/
  | dot
  /-- `Dot2`, rendered `".."` (`spectec/src/xl/atom.ml:14`). -/
  | dot2
  /-- `Dot3`, rendered `"..."` (`spectec/src/xl/atom.ml:15`). -/
  | dot3
  /-- `Semicolon`, rendered `";"` (`spectec/src/xl/atom.ml:16`). -/
  | semicolon
  /-- `Slash`, rendered `"/"` (`spectec/src/xl/atom.ml:17`). -/
  | slash
  /-- `Backslash`, rendered `"\\"` (`spectec/src/xl/atom.ml:18`). -/
  | backslash
  /-- `Not`, rendered `"~"` (`spectec/src/xl/atom.ml:19`). -/
  | not
  /-- `And`, rendered `"/\\"` (`spectec/src/xl/atom.ml:20`). -/
  | and
  /-- `Or`, rendered `"\\/"` (`spectec/src/xl/atom.ml:21`). -/
  | or
  /-- `Mem`, rendered `"<-"` (`spectec/src/xl/atom.ml:22`). -/
  | mem
  /-- `NotMem`, rendered as the characters `<`, `/`, `-` (`spectec/src/xl/atom.ml:23`). -/
  | notMem
  /-- `Arrow`, rendered `"->"` (`spectec/src/xl/atom.ml:24`). -/
  | arrow
  /-- `Arrow2`, rendered `"=>"` (`spectec/src/xl/atom.ml:25`). -/
  | arrow2
  /-- `ArrowSub`, rendered `"->_"` (`spectec/src/xl/atom.ml:26`). -/
  | arrowSub
  /-- `Arrow2Sub`, rendered `"=>_"` (`spectec/src/xl/atom.ml:27`). -/
  | arrow2Sub
  /-- `Colon`, rendered `":"` (`spectec/src/xl/atom.ml:28`). -/
  | colon
  /-- `ColonSub`, rendered `":_"` (`spectec/src/xl/atom.ml:29`). -/
  | colonSub
  /-- `Sub`, rendered `"<:"` (`spectec/src/xl/atom.ml:30`). -/
  | sub
  /-- `Sup`, rendered `":>"` (`spectec/src/xl/atom.ml:31`). -/
  | sup
  /-- `Assign`, rendered `":="` (`spectec/src/xl/atom.ml:32`). -/
  | assign
  /-- `Equal`, rendered `"="` (`spectec/src/xl/atom.ml:33`). -/
  | equal
  /-- `EqualSub`, rendered `"=_"` (`spectec/src/xl/atom.ml:34`). -/
  | equalSub
  /-- `NotEqual`, rendered `"=/="` (`spectec/src/xl/atom.ml:35`). -/
  | notEqual
  /-- `Less`, rendered `"<"` (`spectec/src/xl/atom.ml:36`). -/
  | less
  /-- `Greater`, rendered `">"` (`spectec/src/xl/atom.ml:37`). -/
  | greater
  /-- `LessEqual`, rendered `"<="` (`spectec/src/xl/atom.ml:38`). -/
  | lessEqual
  /-- `GreaterEqual`, rendered `">="` (`spectec/src/xl/atom.ml:39`). -/
  | greaterEqual
  /-- `Equiv`, rendered `"=="` (`spectec/src/xl/atom.ml:40`). -/
  | equiv
  /-- `EquivSub`, rendered `"==_"` (`spectec/src/xl/atom.ml:41`). -/
  | equivSub
  /-- `Approx`, rendered `"~~"` (`spectec/src/xl/atom.ml:42`). -/
  | approx
  /-- `ApproxSub`, rendered `"~~_"` (`spectec/src/xl/atom.ml:43`). -/
  | approxSub
  /-- `SqArrow`, rendered `"~>"` (`spectec/src/xl/atom.ml:44`). -/
  | sqArrow
  /-- `SqArrowSub`, rendered `"~>_"` (`spectec/src/xl/atom.ml:45`). -/
  | sqArrowSub
  /-- `SqArrowStar`, rendered `"~>*"` (`spectec/src/xl/atom.ml:46`). -/
  | sqArrowStar
  /-- `SqArrowStarSub`, rendered `"~>*_"` (`spectec/src/xl/atom.ml:47`). -/
  | sqArrowStarSub
  /-- `Prec`, rendered `"<<"` (`spectec/src/xl/atom.ml:48`). -/
  | prec
  /-- `Succ`, rendered `">>"` (`spectec/src/xl/atom.ml:49`). -/
  | succ
  /-- `PrecSub`, rendered `"<<_"` (`spectec/src/xl/atom.ml:50`). -/
  | precSub
  /-- `SuccSub`, rendered `">>_"` (`spectec/src/xl/atom.ml:51`). -/
  | succSub
  /-- `Turnstile`, rendered `"|-"` (`spectec/src/xl/atom.ml:52`). -/
  | turnstile
  /-- `TurnstileSub`, rendered `"|-_"` (`spectec/src/xl/atom.ml:53`). -/
  | turnstileSub
  /-- `Tilesturn`, rendered `"-|"` (`spectec/src/xl/atom.ml:54`). -/
  | tilesturn
  /-- `TilesturnSub`, rendered `"-|_"` (`spectec/src/xl/atom.ml:55`). -/
  | tilesturnSub
  /-- `Quest`, rendered `"^?"` (`spectec/src/xl/atom.ml:56`). -/
  | quest
  /-- `Star`, rendered `"^*"` (`spectec/src/xl/atom.ml:57`). -/
  | star
  /-- `Iter`, rendered `"^+"` (`spectec/src/xl/atom.ml:58`). -/
  | iter
  /-- `Plus`, rendered `"+"` (`spectec/src/xl/atom.ml:59`). -/
  | plus
  /-- `Minus`, rendered `"-"` (`spectec/src/xl/atom.ml:60`). -/
  | minus
  /-- `PlusMinus`, rendered `"+-"` (`spectec/src/xl/atom.ml:61`). -/
  | plusMinus
  /-- `MinusPlus`, rendered `"-+"` (`spectec/src/xl/atom.ml:62`). -/
  | minusPlus
  /-- `Times`, rendered `"*"` (`spectec/src/xl/atom.ml:63`). -/
  | times
  /-- `Comma`, rendered `","` (`spectec/src/xl/atom.ml:64`). -/
  | comma
  /-- `Cat`, rendered `"++"` (`spectec/src/xl/atom.ml:65`). -/
  | cat
  /-- `Bar`, rendered `"|"` (`spectec/src/xl/atom.ml:66`). -/
  | bar
  /-- `BigAnd`, rendered `"(/\\)"` (`spectec/src/xl/atom.ml:67`). -/
  | bigAnd
  /-- `BigOr`, rendered `"(\\/)"` (`spectec/src/xl/atom.ml:68`). -/
  | bigOr
  /-- `BigForall`, rendered `"(!)"` (`spectec/src/xl/atom.ml:69`). -/
  | bigForall
  /-- `BigExists`, rendered `"(?)"` (`spectec/src/xl/atom.ml:70`). -/
  | bigExists
  /-- `BigAdd`, rendered `"(+)"` (`spectec/src/xl/atom.ml:71`). -/
  | bigAdd
  /-- `BigMul`, rendered `"(*)"` (`spectec/src/xl/atom.ml:72`). -/
  | bigMul
  /-- `BigCat`, rendered `"(++)"` (`spectec/src/xl/atom.ml:73`). -/
  | bigCat
  /-- `LParen`, rendered `"("` (`spectec/src/xl/atom.ml:74`). -/
  | lParen
  /-- `RParen`, rendered `")"` (`spectec/src/xl/atom.ml:74`). -/
  | rParen
  /-- `LBrack`, rendered `"["` (`spectec/src/xl/atom.ml:75`). -/
  | lBrack
  /-- `RBrack`, rendered `"]"` (`spectec/src/xl/atom.ml:75`). -/
  | rBrack
  /-- `LBrace`, rendered `"{"` (`spectec/src/xl/atom.ml:76`). -/
  | lBrace
  /-- `RBrace`, rendered `"}"` (`spectec/src/xl/atom.ml:76`). -/
  | rBrace
  deriving DecidableEq, Repr, Inhabited

namespace Atom

/-- `Atom.to_string` (`spectec/src/xl/atom.ml:111`).

The OCaml function matches `Atom "_"` ahead of `Atom id`, but both branches
return the identifier unchanged, so the two collapse into the single case
below. -/
def toString : Atom → String
  | .atom id => id
  | .infinity => "infinity"
  | .bot => "_|_"
  | .top => "^|^"
  | .dot => "."
  | .dot2 => ".."
  | .dot3 => "..."
  | .semicolon => ";"
  | .slash => "/"
  | .backslash => "\\"
  | .not => "~"
  | .and => "/\\"
  | .or => "\\/"
  | .mem => "<-"
  | .notMem => "</-"
  | .arrow => "->"
  | .arrow2 => "=>"
  | .arrowSub => "->_"
  | .arrow2Sub => "=>_"
  | .colon => ":"
  | .colonSub => ":_"
  | .sub => "<:"
  | .sup => ":>"
  | .assign => ":="
  | .equal => "="
  | .equalSub => "=_"
  | .notEqual => "=/="
  | .less => "<"
  | .greater => ">"
  | .lessEqual => "<="
  | .greaterEqual => ">="
  | .equiv => "=="
  | .equivSub => "==_"
  | .approx => "~~"
  | .approxSub => "~~_"
  | .sqArrow => "~>"
  | .sqArrowSub => "~>_"
  | .sqArrowStar => "~>*"
  | .sqArrowStarSub => "~>*_"
  | .prec => "<<"
  | .succ => ">>"
  | .precSub => "<<_"
  | .succSub => ">>_"
  | .turnstile => "|-"
  | .turnstileSub => "|-_"
  | .tilesturn => "-|"
  | .tilesturnSub => "-|_"
  | .quest => "^?"
  | .star => "^*"
  | .iter => "^+"
  | .plus => "+"
  | .minus => "-"
  | .plusMinus => "+-"
  | .minusPlus => "-+"
  | .times => "*"
  | .comma => ","
  | .cat => "++"
  | .bar => "|"
  | .bigAnd => "(/\\)"
  | .bigOr => "(\\/)"
  | .bigForall => "(!)"
  | .bigExists => "(?)"
  | .bigAdd => "(+)"
  | .bigMul => "(*)"
  | .bigCat => "(++)"
  | .lParen => "("
  | .rParen => ")"
  | .lBrack => "["
  | .rBrack => "]"
  | .lBrace => "{"
  | .rBrace => "}"

/-- The section of `Atom.toString`: every string that some constructor other
than `Atom.atom` renders to is sent back to that constructor, and every other
string `s` to `Atom.atom s`.

`Atom.toString` is *not* injective — `Atom.atom "infinity"` and
`Atom.infinity` both render as `"infinity"` — so `ofString` cannot be its
inverse.  It picks the distinguished, non-`atom` constructor whenever one
exists, which makes it a section of `Atom.toString`
(`Atom.toString_ofString`) but not a retraction; `Atom.Normal` names the
atoms that it does recover. -/
def ofString (s : String) : Atom :=
  match s with
  | "infinity" => .infinity
  | "_|_" => .bot
  | "^|^" => .top
  | "." => .dot
  | ".." => .dot2
  | "..." => .dot3
  | ";" => .semicolon
  | "/" => .slash
  | "\\" => .backslash
  | "~" => .not
  | "/\\" => .and
  | "\\/" => .or
  | "<-" => .mem
  | "</-" => .notMem
  | "->" => .arrow
  | "=>" => .arrow2
  | "->_" => .arrowSub
  | "=>_" => .arrow2Sub
  | ":" => .colon
  | ":_" => .colonSub
  | "<:" => .sub
  | ":>" => .sup
  | ":=" => .assign
  | "=" => .equal
  | "=_" => .equalSub
  | "=/=" => .notEqual
  | "<" => .less
  | ">" => .greater
  | "<=" => .lessEqual
  | ">=" => .greaterEqual
  | "==" => .equiv
  | "==_" => .equivSub
  | "~~" => .approx
  | "~~_" => .approxSub
  | "~>" => .sqArrow
  | "~>_" => .sqArrowSub
  | "~>*" => .sqArrowStar
  | "~>*_" => .sqArrowStarSub
  | "<<" => .prec
  | ">>" => .succ
  | "<<_" => .precSub
  | ">>_" => .succSub
  | "|-" => .turnstile
  | "|-_" => .turnstileSub
  | "-|" => .tilesturn
  | "-|_" => .tilesturnSub
  | "^?" => .quest
  | "^*" => .star
  | "^+" => .iter
  | "+" => .plus
  | "-" => .minus
  | "+-" => .plusMinus
  | "-+" => .minusPlus
  | "*" => .times
  | "," => .comma
  | "++" => .cat
  | "|" => .bar
  | "(/\\)" => .bigAnd
  | "(\\/)" => .bigOr
  | "(!)" => .bigForall
  | "(?)" => .bigExists
  | "(+)" => .bigAdd
  | "(*)" => .bigMul
  | "(++)" => .bigCat
  | "(" => .lParen
  | ")" => .rParen
  | "[" => .lBrack
  | "]" => .rBrack
  | "{" => .lBrace
  | "}" => .rBrace
  | _ => .atom s

/-- `Atom.ofString` is a section of `Atom.toString`: every string whatsoever
is the rendering of the atom it is parsed into. -/
@[simp] theorem toString_ofString (s : String) : (ofString s).toString = s := by
  unfold ofString
  split <;> subst_vars <;> rfl

/-- An atom is *normal* when it is the one `Atom.ofString` picks for its own
rendering, i.e. when it is recoverable from an `--ast` stream.  Every
constructor other than `Atom.atom` is normal, and `Atom.atom s` is normal
exactly when `s` is not the rendering of some other constructor. -/
def Normal (a : Atom) : Prop := ofString a.toString = a

/-- Normality is decidable: it is an equation between concrete atoms. -/
instance (a : Atom) : Decidable a.Normal :=
  inferInstanceAs (Decidable (ofString a.toString = a))

/-- Everything in the image of `Atom.ofString` is normal. -/
theorem normal_ofString (s : String) : (ofString s).Normal := by
  show ofString (ofString s).toString = ofString s
  rw [toString_ofString]

/-- A normal atom is recovered from its rendering. -/
theorem ofString_toString_of_normal {a : Atom} (h : a.Normal) :
    ofString a.toString = a := h

/-- `Atom.toString` is injective on normal atoms, so a rendered atom
determines its normal preimage. -/
theorem toString_injective_on_normal {a b : Atom} (ha : a.Normal) (hb : b.Normal)
    (h : a.toString = b.toString) : a = b := by
  have hab : ofString a.toString = ofString b.toString := by rw [h]
  rwa [ofString_toString_of_normal ha, ofString_toString_of_normal hb] at hab

/-- The image of `Atom.ofString` is exactly the normal atoms.  In particular
`Atom.ofString` is *not* surjective: `Atom.atom "infinity"` is not normal,
because `Atom.ofString "infinity"` is `Atom.infinity`. -/
theorem exists_ofString_iff_normal (a : Atom) : (∃ s, ofString s = a) ↔ a.Normal := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h
    subst hs
    exact normal_ofString s
  · intro h
    exact ⟨a.toString, h⟩

end Atom

end Silmaril.SpecTec.IL
