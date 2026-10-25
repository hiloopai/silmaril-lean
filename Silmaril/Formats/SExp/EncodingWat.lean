module

public import Silmaril.Formats.SExp.EncodingWatDefs
public import Silmaril.Formats.SExp.EncodingWatLex
public import Silmaril.Formats.SExp.EncodingWatLexTrees

/-!
# The WebAssembly text-format lexical conventions: functionality and examples

The relations `lexRel`, `treesRel` and `sexpWat` are defined, and the lexical
conventions documented, in `EncodingWatDefs.lean`.  Longest match makes
tokenization unique (`EncodingWatLex.lean`) and bracketing is unique
(`EncodingWatLexTrees.lean`), so `sexpWat p` is functional.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

/-! ## Functionality -/

/-- Longest match makes tokenization unique. -/
theorem lexRel_functional (p : Profile) : (lexRel p).Functional :=
  fun _ _ _ h₁ h₂ => lex_functional h₁ h₂

/-- Bracketing is unique. -/
theorem treesRel_functional : treesRel.Functional := by
  rintro ts x y ⟨xs, hxs, rfl⟩ ⟨ys, hys, rfl⟩
  rw [trees_functional hxs hys]

theorem sexpWat_functional (p : Profile) : (sexpWat p).Functional :=
  (lexRel_functional p).comp treesRel_functional

theorem sexpWatBytes_functional (p : Profile) : (sexpWatBytes p).Functional :=
  Unicode.functional_push_utf8 (sexpWat_functional p)

/-- The byte relation is the UTF-8 pushforward, i.e. the well-formed UTF-8 byte
strings whose decoding is a WAT text. -/
theorem sexpWatBytes_eq (p : Profile) :
    sexpWatBytes p = (sexpWat p).pullPartial Unicode.utf8? :=
  Unicode.push_utf8_eq _

/-! ## Example spellings -/

/-- `(module)` in either profile. -/
theorem sexpWat_module (p : Profile) : sexpWat p "(module)" (doc [listOf [kw "module"]]) := by
  have hm : ∀ c ∈ ['m', 'o', 'd', 'u', 'l', 'e'], IsIdChar c := by decide
  have hid : IdRun ['m', 'o', 'd', 'u', 'l', 'e'] (.sym "module") :=
    IdRun.sym (cs := ['m', 'o', 'd', 'u', 'l', 'e']) (by simp) hm (by simp)
  have hlex : Lex p true ['(', 'm', 'o', 'd', 'u', 'l', 'e', ')']
      [.lp, .atom (.sym "module"), .rp] := by
    refine Lex.step (s := []) (c := ['(']) (rest := ['m', 'o', 'd', 'u', 'l', 'e', ')'])
      Space.nil ?_ ?_ ?_
    · cases p <;> rfl
    · cases p <;> simp [Follow]
    refine Lex.step (s := []) (c := ['m', 'o', 'd', 'u', 'l', 'e']) (rest := [')'])
      Space.nil ?_ ?_ ?_
    · cases p
      · exact hid
      · exact ⟨.idRun hid, by decide⟩
    · cases p <;> simp [Follow] <;> decide
    refine Lex.step (s := []) (c := [')']) (rest := []) Space.nil ?_ ?_ (Lex.done Space.nil)
    · cases p <;> rfl
    · cases p <;> trivial
  refine ⟨[.lp, .atom (.sym "module"), .rp], hlex, [listOf [kw "module"]], ?_, rfl⟩
  have ht : Tree [.lp, .atom (.sym "module"), .rp] (listOf [kw "module"]) :=
    Tree.list (ts := [.atom (.sym "module")])
      (Trees.cons (a := [_]) (b := []) (Tree.atom _) Trees.nil)
  exact Trees.cons (b := []) ht Trees.nil

/-- An annotation is whitespace in Core 3.0. -/
theorem sexpWat3_annot : sexpWat3 "(@a)" (doc []) := by
  have hi : AnnotId ['a'] := Or.inl ⟨by simp, by decide⟩
  have hitem : SpaceItem .core3 ('(' :: '@' :: (['a'] ++ [] ++ [')'])) :=
    SpaceItem.annot hi (by simp) (Lex.done Space.nil) Balanced.nil
  have hlex : Lex .core3 true ['(', '@', 'a', ')'] [] :=
    Lex.done (Space.cons (b := []) hitem Space.nil)
  exact ⟨[], hlex, [], Trees.nil, rfl⟩

/-- In Wasm 1.0 `(@a)` is a list containing the bare token `@a`. -/
theorem sexpWat1_annot : sexpWat1 "(@a)" (doc [listOf [kw "@a"]]) := by
  have hid : IdRun ['@', 'a'] (.sym "@a") :=
    IdRun.sym (cs := ['@', 'a']) (by simp) (by decide) (by simp)
  have hlex : Lex .v1 true ['(', '@', 'a', ')'] [.lp, .atom (.sym "@a"), .rp] := by
    refine Lex.step (s := []) (c := ['(']) (rest := ['@', 'a', ')']) Space.nil rfl ?_ ?_
    · simp [Follow]
    refine Lex.step (s := []) (c := ['@', 'a']) (rest := [')']) Space.nil hid ?_ ?_
    · simp [Follow]; decide
    exact Lex.step (s := []) (c := [')']) (rest := []) Space.nil rfl trivial (Lex.done Space.nil)
  refine ⟨[.lp, .atom (.sym "@a"), .rp], hlex, [listOf [kw "@a"]], ?_, rfl⟩
  have ht : Tree [.lp, .atom (.sym "@a"), .rp] (listOf [kw "@a"]) :=
    Tree.list (ts := [.atom (.sym "@a")])
      (Trees.cons (a := [_]) (b := []) (Tree.atom _) Trees.nil)
  exact Trees.cons (b := []) ht Trees.nil

/-- Quoted identifiers exist in Core 3.0 only, and denote the same atom as the
plain spelling. -/
theorem sexpWat3_quotedId : sexpWat3 "$\"x\"" (doc [.atom (.id "x")]) := by
  have hb : StringBody ['x'] (charUtf8 'x') := by
    have := StringBody.cons (e := ['x']) (rest := [])
      (StringElem.char (c := 'x') (by decide) (by decide) (by decide) (by decide)) StringBody.nil
    simpa using this
  have hlen : (charUtf8 'x').length < 2 ^ 32 := by
    have h4 := Char.utf8Size_le_four 'x'
    have h1 : (String.singleton 'x').utf8ByteSize = 'x'.utf8Size := String.utf8ByteSize_singleton
    simp only [charUtf8, Unicode.utf8, Array.length_toList, ByteArray.size_data,
      String.toUTF8_eq_toByteArray, String.size_toByteArray, h1]
    omega
  have hs : StringLit ['"', 'x', '"'] (charUtf8 'x') := ⟨['x'], rfl, hb, hlen⟩
  have hn : NameLit ['"', 'x', '"'] "x" :=
    ⟨_, hs, by rw [charUtf8, Unicode.utf8?_utf8, String.singleton_eq_ofList]⟩
  have ha : RunAtom3 ['$', '"', 'x', '"'] (.id "x") := RunAtom3.quotedId hn (by decide)
  have hlex : Lex .core3 true ['$', '"', 'x', '"'] [.atom (.id "x")] :=
    Lex.step (s := []) (c := ['$', '"', 'x', '"']) (rest := []) Space.nil ⟨ha, by decide⟩
      (by simp [Follow]) (Lex.done Space.nil)
  exact ⟨_, hlex, [.atom (.id "x")], Trees.cons (b := []) (Tree.atom _) Trees.nil, rfl⟩

theorem sexpWat3_plainId : sexpWat3 "$x" (doc [.atom (.id "x")]) := by
  have hid : IdRun ['$', 'x'] (.id "x") := IdRun.id (rest := ['x']) (by simp) (by decide)
  have hlex : Lex .core3 true ['$', 'x'] [.atom (.id "x")] :=
    Lex.step (s := []) (c := ['$', 'x']) (rest := []) Space.nil ⟨.idRun hid, by decide⟩
      (by simp [Follow]) (Lex.done Space.nil)
  exact ⟨_, hlex, [.atom (.id "x")], Trees.cons (b := []) (Tree.atom _) Trees.nil, rfl⟩

/-- The Wasm 1.0 and Core 3.0 lexical conventions are incomparable: the
annotation syntax of 3.0 is an ordinary list in 1.0. -/
theorem sexpWat_v1_core3_incomparable : EncRel.Incomparable sexpWat1 sexpWat3 :=
  EncRel.incomparable_of_witness (sexpWat_functional _) (sexpWat_functional _)
    sexpWat1_annot sexpWat3_annot (by simp [listOf])

end Silmaril.Formats.SExpEncoding.Wat
