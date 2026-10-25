module

public import Silmaril.Formats.SExp.EncodingWatByteExec

@[expose] public section

/-! # An additive checked lexer for hexadecimal byte escapes

The original lexer is tried first, preserving every successful result exactly.
Only the fallback adds mixed plain UTF-8 and two-hex-digit byte string elements.
The original character-count fuel and decoded-string length bound remain.
-/

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

def lexGoBytes (p : Profile) : Nat → Chars → Option (List Tok)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, c :: r =>
      if IsSpaceChar c then lexGoBytes p n r
      else if c = ';' ∧ r.head? = some ';' then
        match (splitLine p r.tail).2 with
        | none => some []
        | some (_, rest) => lexGoBytes p n rest
      else if c = '(' ∧ r.head? = some ';' then
        match blockTail? (r.length + 1) r.tail with
        | none => none
        | some rest => lexGoBytes p n rest
      else if c = '(' then
        if p = .core3 ∧ r.head? = some '@' then none else (Tok.lp :: ·) <$> lexGoBytes p n r
      else if c = ')' then (Tok.rp :: ·) <$> lexGoBytes p n r
      else if c = '"' then
        match byteStrBody? r with
        | none => none
        | some (_b, bytes, rest) =>
          if bytes.length < 2 ^ 32 ∧
              followAtomB p true rest = true then
            (Tok.atom (.str bytes) :: ·) <$> lexGoBytes p n rest
          else none
      else if IsIdChar c then
        if followAtomB p false (idRun r).2 = true then
          (Tok.atom (classify (c :: (idRun r).1)) :: ·) <$> lexGoBytes p n (idRun r).2
        else none
      else none

theorem lexGoBytes_sound (p : Profile) : ∀ (n : Nat) (cs : Chars) (ts : List Tok),
    lexGoBytes p n cs = some ts → Lex p true cs ts := by
  intro n
  induction n with
  | zero => intro cs ts h; simp [lexGoBytes] at h
  | succ n ih =>
    intro cs ts h
    cases cs with
    | nil =>
      simp only [lexGoBytes, Option.some.injEq] at h
      subst h; exact Lex.done Space.nil
    | cons c r =>
      unfold lexGoBytes at h
      by_cases hsp : IsSpaceChar c
      · simp only [hsp, ↓reduceIte] at h
        exact lex_space (a := [c]) (SpaceItem.char hsp) (ih r ts h)
      simp only [hsp, ↓reduceIte] at h
      by_cases hlc : c = ';' ∧ r.head? = some ';'
      · simp only [hlc, and_self, ↓reduceIte] at h
        obtain ⟨rfl, hr⟩ := hlc
        cases r with
        | nil => simp at hr
        | cons d r =>
          simp only [List.head?_cons, Option.some.injEq] at hr
          subst hr
          simp only [List.tail_cons] at h
          cases hs : (splitLine p r).2 with
          | none =>
            simp only [hs, Option.some.injEq] at h
            subst h
            have e := splitLine_none p r hs
            have := Lex.doneEof (p := p) (s := []) Space.nil (splitLine_noNewline p r)
            rw [e]; simpa using this
          | some nr =>
            obtain ⟨nl, rest⟩ := nr
            simp only [hs] at h
            obtain ⟨e, hnl⟩ := splitLine_some p r hs
            have hi : SpaceItem p (';' :: ';' :: ((splitLine p r).1 ++ [nl])) :=
              SpaceItem.line (splitLine_noNewline p r) hnl
            have := lex_space hi (ih rest ts h)
            rw [e]; simpa using this
      simp only [hlc, ↓reduceIte] at h
      by_cases hbc : c = '(' ∧ r.head? = some ';'
      · simp only [hbc, and_self, ↓reduceIte] at h
        obtain ⟨rfl, hr⟩ := hbc
        cases hb : blockTail? (r.length + 1) r.tail with
        | none => simp [hb] at h
        | some rest =>
          simp only [hb] at h
          obtain ⟨t, e, ht⟩ := blockTail?_sound _ _ _ hb
          cases r with
          | nil => simp at hr
          | cons d r =>
            simp only [List.head?_cons, Option.some.injEq] at hr
            subst hr
            simp only [List.tail_cons] at e
            subst e
            have hi : SpaceItem p ('(' :: ';' :: t) := SpaceItem.block (BlockComment.mk ht)
            simpa using lex_space hi (ih rest ts h)
      simp only [hbc, ↓reduceIte] at h
      by_cases hlp : c = '('
      · subst hlp
        simp only [↓reduceIte] at h
        by_cases ha : p = .core3 ∧ r.head? = some '@'
        · simp [ha] at h
        simp only [ha, ↓reduceIte] at h
        cases hg : lexGoBytes p n r with
        | none => simp [hg] at h
        | some ts' =>
          simp only [hg, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
          subst h
          refine lex_tok (c := ['(']) (by cases p <;> rfl) ?_ (ih r ts' hg)
          have h1 : r.head? ≠ some ';' := fun e => hbc ⟨rfl, e⟩
          cases p with
          | v1 => exact h1
          | core3 => exact ⟨h1, fun e => ha ⟨rfl, e⟩⟩
      simp only [hlp, ↓reduceIte] at h
      by_cases hrp : c = ')'
      · subst hrp
        simp only [↓reduceIte] at h
        cases hg : lexGoBytes p n r with
        | none => simp [hg] at h
        | some ts' =>
          simp only [hg, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
          subst h
          exact lex_tok (c := [')']) (by cases p <;> rfl) (by cases p <;> trivial) (ih r ts' hg)
      simp only [hrp, ↓reduceIte] at h
      by_cases hq : c = '"'
      · subst hq
        simp only [↓reduceIte] at h
        cases hs : byteStrBody? r with
        | none => simp [hs] at h
        | some br =>
          obtain ⟨b, bytes, rest⟩ := br
          simp only [hs] at h
          obtain ⟨e, hb⟩ := byteStrBody?_sound r b bytes rest hs
          by_cases hc : bytes.length < 2 ^ 32 ∧
              followAtomB p true rest = true
          · simp only [hc, and_self, ↓reduceIte] at h
            cases hg : lexGoBytes p n rest with
            | none => simp [hg] at h
            | some ts' =>
              simp only [hg, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
              subst h
              have hlit : StringLit ('"' :: (b ++ ['"'])) bytes :=
                ⟨b, rfl, hb, hc.1⟩
              have h1 : Tok1 p true ('"' :: (b ++ ['"']))
                  (.atom (.str bytes)) := by
                cases p with
                | v1 => exact hlit
                | core3 => exact ⟨RunAtom3.str hlit, by simp⟩
              have := lex_tok h1 (follow_atom_of hc.2) (ih rest ts' hg)
              rw [e]; simpa using this
          · simp only [hc, ↓reduceIte, reduceCtorEq] at h
      simp only [hq, ↓reduceIte] at h
      by_cases hid : IsIdChar c
      · simp only [hid, ↓reduceIte] at h
        by_cases hf : followAtomB p false (idRun r).2 = true
        · simp only [hf, ↓reduceIte] at h
          cases hg : lexGoBytes p n (idRun r).2 with
          | none => simp [hg] at h
          | some ts' =>
            simp only [hg, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
            subst h
            have hall : ∀ x ∈ c :: (idRun r).1, IsIdChar x := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hid
              · exact idRun_idChar r x hx
            have hrun := classify_sound (cs := c :: (idRun r).1) (by simp) hall
            have h1 : Tok1 p true (c :: (idRun r).1) (.atom (classify (c :: (idRun r).1))) := by
              cases p with
              | core3 =>
                refine ⟨RunAtom3.idRun hrun, ?_⟩
                have := idChar_ne_semi hid
                cases hh : (idRun r).1 <;> simp [this]
              | v1 =>
                -- the atom is not a string
                revert hrun
                generalize classify (c :: (idRun r).1) = a
                intro hrun
                cases a with
                | str bs => cases hrun
                | sym s => exact hrun
                | id s => exact hrun
            have hf' : Follow p (.atom (classify (c :: (idRun r).1))) (idRun r).2 := by
              apply follow_atom_of
              revert hf
              generalize classify (c :: (idRun r).1) = a
              intro hf
              cases a <;> first | exact hf | (cases p <;> simp_all [followAtomB])
            have e : c :: r = (c :: (idRun r).1) ++ (idRun r).2 := by
              rw [List.cons_append, idRun_append]
            rw [e]; exact lex_tok h1 hf' (ih _ ts' hg)
        · simp [hf] at h
      · simp [hid] at h

/-- Lex and bracket with the unchanged lexer as the priority fast path. -/
def sexpWatByteExec? (p : Profile) (s : String) : Option SExp :=
  match sexpWatExec? p s with
  | some tree => some tree
  | none => (lexGoBytes p (s.toList.length + 1) s.toList).bind bracketExec?

/-- Every previous successful lexical result is retained exactly. -/
theorem sexpWatByteExec?_of_original {p : Profile} {s : String} {tree : SExp}
    (h : sexpWatExec? p s = some tree) : sexpWatByteExec? p s = some tree := by
  simp [sexpWatByteExec?, h]

/-- The new byte-escape fallback satisfies the same independent WAT grammar. -/
theorem sexpWat_of_byteExec {p : Profile} {s : String} {tree : SExp}
    (h : sexpWatByteExec? p s = some tree) : sexpWat p s tree := by
  unfold sexpWatByteExec? at h
  cases original : sexpWatExec? p s with
  | some result =>
    simp only [original, Option.some.injEq] at h
    subst h
    exact sexpWat_of_exec original
  | none =>
    simp only [original] at h
    cases hl : lexGoBytes p (s.toList.length + 1) s.toList with
    | none => simp [hl] at h
    | some tokens =>
      simp only [hl, Option.bind_some] at h
      exact ⟨tokens, lexGoBytes_sound p _ _ _ hl, bracketExec?_sound h⟩

end Silmaril.Formats.SExpEncoding.Wat
