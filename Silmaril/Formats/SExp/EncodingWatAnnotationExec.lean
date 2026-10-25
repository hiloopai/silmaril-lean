module

public import Silmaril.Formats.SExp.EncodingWatFullString

@[expose] public section

/-! Checked Core3 annotations containing ordinary atom/string payloads.
Annotations are whitespace in the existing independent grammar. This parser
constructs that whitespace derivation for the complete original spelling; it
does not delete arbitrary parenthesized input. -/

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

theorem follow_core_prefix {a : Atom} {xs ys : Chars}
    (h : Follow .core3 (.atom a) (xs ++ ys)) : Follow .core3 (.atom a) xs := by
  cases xs with
  | nil => simp [Follow]
  | cons c xs => simpa [Follow] using h

structure AnnotationBody (cs : Chars) where
  body : Chars
  rest : Chars
  tokens : List Tok
  split : cs = body ++ ')' :: rest
  lexical : Lex .core3 false body tokens
  balanced : Balanced tokens

/-- A deliberately bounded annotation payload frontend. Nested groups and
reserved punctuation reject until their independent rules are implemented. -/
def annotationBodyFuel? : Nat → (cs : Chars) → Option (AnnotationBody cs)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, c :: r =>
      if hc : c = ')' then
        some ⟨[], r, [], by simp [hc], .done .nil, .nil⟩
      else if hs : IsSpaceChar c then do
        let tail ← annotationBodyFuel? fuel r
        some ⟨c :: tail.body, tail.rest, tail.tokens,
          by simp [tail.split],
          by simpa using lex_space (SpaceItem.char hs) tail.lexical,
          tail.balanced⟩
      else if hq : c = '"' then do
        match hp : fullStrBody? r with
        | none => none
        | some (spelling, bytes, rest) =>
            if hl : bytes.length < 2 ^ 32 ∧ followAtomB .core3 true rest = true then do
              let tail ← annotationBodyFuel? fuel rest
              let literal := '"' :: (spelling ++ ['"'])
              let hstr : StringLit literal bytes :=
                ⟨spelling, rfl, (fullStrBody?_sound hp).2, hl.1⟩
              let tok : Tok1 .core3 false literal (.atom (.str bytes)) :=
                ⟨.str hstr, by simp [literal]⟩
              some ⟨literal ++ tail.body, tail.rest, .atom (.str bytes) :: tail.tokens,
                by
                  have he := (fullStrBody?_sound hp).1
                  simp [hq, literal, he, tail.split, List.append_assoc],
                lex_tok tok (by
                  have hf := follow_atom_of (p := .core3) (a := .str bytes) hl.2
                  rw [tail.split] at hf
                  exact follow_core_prefix hf) tail.lexical,
                .tok (by simp) (by simp) tail.balanced⟩
            else none
      else if hi : IsIdChar c then
        let spelling := c :: (idRun r).1
        let rest := (idRun r).2
        if hf : followAtomB .core3 false rest = true then do
          let tail ← annotationBodyFuel? fuel rest
          let hall : ∀ x ∈ spelling, IsIdChar x := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hi
            · exact idRun_idChar r x hx
          let hrun := classify_sound (cs := spelling) (by simp [spelling]) hall
          let tok : Tok1 .core3 false spelling (.atom (classify spelling)) := by
            refine ⟨.idRun hrun, ?_⟩
            have hn := idChar_ne_semi hi
            cases hh : (idRun r).1 <;> simp [spelling, hh, hn]
          let follow : Follow .core3 (.atom (classify spelling)) rest := by
            have h := follow_atom_of (p := .core3) (a := .sym "") hf
            exact h
          some ⟨spelling ++ tail.body, tail.rest, .atom (classify spelling) :: tail.tokens,
            by
              calc
                c :: r = spelling ++ rest := by
                  simpa [spelling, rest] using congrArg (c :: ·) (idRun_append r).symm
                _ = (spelling ++ tail.body) ++ ')' :: tail.rest := by
                  simpa only [List.append_assoc] using congrArg (spelling ++ ·) tail.split,
            lex_tok tok (by
              rw [tail.split] at follow
              exact follow_core_prefix follow) tail.lexical,
            .tok (by simp) (by simp) tail.balanced⟩
        else none
      else none

structure AnnotationTail (cs : Chars) where
  spelling : Chars
  rest : Chars
  split : cs = spelling ++ rest
  sound : SpaceItem .core3 ('(' :: spelling)

/-- Parse an annotation after its opening parenthesis. Its identifier and
payload both retain the exact original character sequence. -/
def annotationTail? (cs : Chars) : Option (AnnotationTail cs) := do
  let '@' :: tail := cs | none
  let idc := (idRun tail).1
  let suffix := (idRun tail).2
  if hid : idc ≠ [] then do
    let body ← annotationBodyFuel? (suffix.length + 1) suffix
    if hf : followAtomB .core3 false body.body = true then
      if hs : cs = ('@' :: (idc ++ body.body ++ [')'])) ++ body.rest then
        some ⟨'@' :: (idc ++ body.body ++ [')']), body.rest, hs, by
          simpa [List.append_assoc] using SpaceItem.annot
            (.inl ⟨hid, idRun_idChar tail⟩) (follow_atom_of (p := .core3) (a := .sym "") hf) body.lexical body.balanced⟩
      else none
    else none
  else none

end Silmaril.Formats.SExpEncoding.Wat
