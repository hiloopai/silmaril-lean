module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.DecodeSound
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.DecodeComplete
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.LexicalPrinter
public import Silmaril.Encoding.Lattice

/-!
# The `--ast` stream as an encoding relation

`Silmaril/Encoding/Relation.lean` treats an encoding as a value
`EncRel σ α : σ → α → Prop`.  This file packages the SpecTec IL's printed form
that way and places it in the lattice:

* `defRel : EncRel SExp Def` and `scriptRel : EncRel (List SExp) Script` are
  the graphs of `defS` and `scriptS`.  Both are **bijective** — functional
  because the printer is injective (`defS_injective`), deterministic because
  it is a function — and `decodeDef?`/`decodeScript?` are sound and complete
  decoders for them.
* `astRel width : EncRel String Script` composes that with the lexical layer:
  a string spells a script when it lexes to the script's printed form.  It is
  functional but *not* deterministic, because every `--ast-width` gives a
  different, equally valid spelling.

The one hypothesis the string level needs is `SExp.PrintableList`: the lexer
cannot read back an S-expression containing an atom that is not a token.  That
induction over the IL is `Silmaril/SpecTec/IL/Printable.lean`; it is not
repeated here, so the theorems below carry the hypothesis explicitly.  What
that file proves is an *iff* with a decidable side condition,

```
printableList_scriptS_iff :
  SExp.PrintableList (scriptS s) ↔ AllToken (realsScript s)
```

where `realsScript` collects the payloads of the script's `Num.realN`
numerals: every other atom `defS` emits is a quoted text, a numeral rendering
or a fixed bare run, and is a token by construction.

The condition is **necessary**, not an artefact of the proof.  `Num.realN`
carries an unchecked `String` which `numS` emits as a bare atom
(`print.ml:20`), so for a hand-built definition `d`:

* `SExp.Printable (defS d)` *fails* when `d` contains `Num.realN " "` — the
  printed atom `(real  )` lexes as a `real` node with no children;
* `Num.realN ""` prints the empty atom, which `SExp.render` erases entirely
  and the lexical convention does not accept at all
  (`Silmaril/SpecTec/SExp/Lexical.lean`);
* `SExp.render` is not injective on the image of `defS`, even though `defS`
  is (`defS_injective`): a payload spelling `))) (prod eps (num (real `
  closes the enclosing nodes and opens new ones, so a `gram` definition with
  one production whose expression is `Num.realN "r))) (prod eps (num (real r'"`
  renders, at any width wide enough to print both flat, exactly like the
  two-production definition carrying `Num.realN "r"` and `Num.realN "r'"`.

Nothing `spectec` writes is like that — `Printf.sprintf "%.17g"`
(`spectec/src/xl/num.ml:25`) can only emit characters from `[-+0-9.eE]`, plus
`inf` and `nan`, all bare tokens — and `Printable.lean` discharges the
condition for everything the decoder reads out of a lexable tree
(`allToken_realsScript_of_lexesStream`), which is what its end-to-end
corollary `astRel_astFile` needs.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

open Silmaril (EncRel)
open Silmaril.SpecTec

/-! ## The S-expression level -/

/-- `s` is the `--ast` rendering of the definition `d`. -/
def defRel : EncRel SExp Def := EncRel.ofFun defS

/-- `ss` is the `--ast` rendering of the script `s`. -/
def scriptRel : EncRel (List SExp) Script := EncRel.ofFun scriptS

theorem defRel_iff {s : SExp} {d : Def} : defRel s d ↔ defS d = s := Iff.rfl

theorem scriptRel_iff {ss : List SExp} {s : Script} : scriptRel ss s ↔ scriptS s = ss := Iff.rfl

/-- The printer is a function, so each definition has exactly one rendering. -/
theorem defRel_deterministic : defRel.Deterministic := EncRel.ofFun_deterministic defS

/-- Every definition has a rendering.  This is *not* printability in the sense
of `SExp.Printable`, which `Num.realN` can defeat; see the module
documentation. -/
theorem defRel_total : defRel.Total := EncRel.ofFun_total defS

/-- A rendering determines its definition: `defS` is injective. -/
theorem defRel_functional : defRel.Functional := by
  intro s d d' h h'
  exact defS_injective (h.trans h'.symm)

/-- `defS` is a partial bijection between definitions and their renderings. -/
theorem defRel_bijective : defRel.Bijective := ⟨defRel_functional, defRel_deterministic⟩

theorem scriptRel_deterministic : scriptRel.Deterministic := EncRel.ofFun_deterministic scriptS

theorem scriptRel_total : scriptRel.Total := EncRel.ofFun_total scriptS

theorem scriptRel_functional : scriptRel.Functional := by
  intro ss s s' h h'
  exact scriptS_injective (h.trans h'.symm)

theorem scriptRel_bijective : scriptRel.Bijective := ⟨scriptRel_functional, scriptRel_deterministic⟩

/-! ## The decoder -/

/-- `decodeDef?` only ever returns the definition its input renders. -/
theorem decodeDef?_sound : defRel.DecoderSound decodeDef? := fun _ _ h => defS_of_decodeDef? h

/-- `decodeDef?` decodes every rendering. -/
theorem decodeDef?_complete : defRel.DecoderComplete decodeDef? := by
  rintro s d rfl
  exact decodeDef?_defS d

/-- The relation *is* the decoder's graph: `decodeDef?` is exact. -/
theorem defRel_eq_ofDecoder : defRel = EncRel.ofDecoder decodeDef? := by
  ext s d
  exact ⟨fun h => decodeDef?_complete s d h, fun h => decodeDef?_sound s d h⟩

theorem decodeScript?_sound : scriptRel.DecoderSound decodeScript? :=
  fun _ _ h => scriptS_of_decodeScript? h

theorem decodeScript?_complete : scriptRel.DecoderComplete decodeScript? := by
  rintro ss s rfl
  exact decodeScript?_scriptS s

theorem scriptRel_eq_ofDecoder : scriptRel = EncRel.ofDecoder decodeScript? := by
  ext ss s
  exact ⟨fun h => decodeScript?_complete ss s h, fun h => decodeScript?_sound ss s h⟩

/-- The valid `--ast` definition trees are exactly the printed ones. -/
theorem defRel_domain : defRel.domain = Set.range defS := by
  ext s
  exact ⟨fun ⟨d, hd⟩ => ⟨d, hd⟩, fun ⟨d, hd⟩ => ⟨d, hd⟩⟩

/-- Every definition occurs. -/
theorem defRel_image : defRel.image = Set.univ := by
  ext d
  exact ⟨fun _ => trivial, fun _ => ⟨defS d, rfl⟩⟩

/-! ## The string level -/

/-- A string spells a script when it lexes to that script's `--ast`
rendering.  `EncRel.comp` layers the lexical convention
(`Silmaril/SpecTec/SExp/Lexical.lean`) under the IL's printed form. -/
def astRel : EncRel String Script := EncRel.comp streamRel scriptRel

theorem astRel_iff {s : String} {sc : Script} :
    astRel s sc ↔ LexesStream s.toList (scriptS sc) := by
  constructor
  · rintro ⟨ss, hss, rfl⟩; exact hss
  · intro h; exact ⟨scriptS sc, h, rfl⟩

/-- A string determines the script it spells: the lexical convention is
unambiguous and the printer is injective. -/
theorem astRel_functional : astRel.Functional := by
  rintro s sc sc' ⟨ss, hss, hsc⟩ ⟨ss', hss', hsc'⟩
  exact scriptS_functional_aux hss hss' hsc hsc'
where
  /-- Two spellings of the same string agree, hence so do their scripts. -/
  scriptS_functional_aux {s : String} {ss ss' : List SExp} {sc sc' : Script}
      (h : LexesStream s.toList ss) (h' : LexesStream s.toList ss')
      (hsc : scriptS sc = ss) (hsc' : scriptS sc' = ss') : sc = sc' := by
    have : ss = ss' := h.det h'
    exact scriptS_injective (hsc.trans (this.trans hsc'.symm))

/-- No single width is canonical: `astRel` admits every `--ast-width`. -/
theorem astFile_astRel {width : Nat} {sc : Script}
    (h : SExp.PrintableList (scriptS sc)) : astRel (astFile width sc) sc :=
  astRel_iff.mpr (lexesStream_astFile width (scriptS sc) h)

/-- `--ast` output is a correct encoder wherever the printed script is
lexable. -/
theorem astRel_encoderCorrectOn (width : Nat) :
    astRel.EncoderCorrectOn (fun sc => SExp.PrintableList (scriptS sc)) (astFile width) :=
  fun _ h => astFile_astRel h

end Silmaril.SpecTec.IL
