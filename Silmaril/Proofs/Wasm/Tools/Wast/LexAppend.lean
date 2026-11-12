module

public import Silmaril.Wasm.Tools.Wast.Lex.Defs

/-!
# The WAT lexical grammar is closed under concatenation after a line break: proofs

Proofs for `Silmaril.Wasm.Tools.Wast.Lex.Thms` (`sexpWat_append`): if `s₁`
spells the document `xs₁`, `s₂` spells `xs₂`, and `s₁` ends with a line feed, then
`s₁ ++ s₂` spells `xs₁ ++ xs₂`. The line feed is what makes the chunks independent: no token
ends with it, so the last token of `s₁` keeps its follow character, and a line comment that
ends `s₁` without a line break (`Lex.doneEof`) is impossible.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast.LexAppend

open Silmaril.Formats Silmaril.Formats.SExpEncoding Silmaril.Formats.SExpEncoding.Wat
open Silmaril.Wasm.Tools.Wast (joinStr PNode chunkCheck)

theorem space_append {p : Profile} : ∀ {a b : Chars}, Space p a → Space p b → Space p (a ++ b)
  | _, _, .nil, h => h
  | _, _, .cons h₁ h₂, h => by
    rw [List.append_assoc]
    exact .cons h₁ (space_append h₂ h)

theorem lex_space_prepend {p : Profile} {top : Bool} {a b : Chars} {ts : List Tok}
    (ha : Space p a) (hb : Lex p top b ts) : Lex p top (a ++ b) ts := by
  cases hb with
  | done h => exact .done (space_append ha h)
  | doneEof h hn =>
    rw [← List.append_assoc]
    exact .doneEof (space_append ha h) hn
  | step h ht hf hl =>
    have := Lex.step (space_append ha h) ht hf hl
    simpa only [List.append_assoc] using this

theorem follow_head {p : Profile} {t : Tok} {r r' : Chars} (hh : r'.head? = r.head?)
    (h : Follow p t r) : Follow p t r' := by
  rcases p with _ | _ <;> rcases t with _ | _ | ⟨a⟩ | _ | _ <;> (try cases a) <;>
    simp_all [Follow]

theorem not_newline_idChar : ¬ IsIdChar '\n' := by decide

theorem getLast?_cons_snoc (x : Char) (l : Chars) (a : Char) :
    (x :: (l ++ [a])).getLast? = some a := by
  have e : x :: (l ++ [a]) = (x :: l) ++ [a] := rfl
  rw [e, List.getLast?_append_of_ne_nil _ (by simp)]
  rfl

theorem stringLit_getLast {cs : Chars} {bs : List UInt8} (h : StringLit cs bs) :
    cs.getLast? = some '"' := by
  obtain ⟨body, rfl, -, -⟩ := h
  exact getLast?_cons_snoc _ _ _

theorem runPieces_getLast {cs : Chars} (h : RunPieces cs) : ∀ x, cs.getLast? = some x →
    IsRunChar x ∨ x = '"' := by
  induction h with
  | nil => intro x h; simp at h
  | @char c rest hc _ ih =>
    intro x h
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      exact .inl (h ▸ hc)
    | cons y ys =>
      rw [List.getLast?_cons_cons] at h
      exact ih x h
  | @str s rest _ hs _ ih =>
    intro x h
    by_cases hrest : rest = []
    · subst hrest
      rw [List.append_nil, stringLit_getLast hs] at h
      exact .inr (Option.some.inj h).symm
    · rw [List.getLast?_append_of_ne_nil _ hrest] at h
      exact ih x h

theorem idRun_getLast {cs : Chars} {a : Atom} (h : IdRun cs a) (x : Char)
    (hx : cs.getLast? = some x) : x ≠ '\n' := by
  have hall : ∀ c ∈ cs, IsIdChar c := by
    cases h with
    | sym _ hc _ => exact hc
    | id _ hc =>
      intro c hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · decide
      · exact hc _ hc'
  rintro rfl
  exact not_newline_idChar (hall _ (List.mem_of_getLast? hx))

theorem runAtom3_getLast {cs : Chars} {a : Atom} (h : RunAtom3 cs a) (x : Char)
    (hx : cs.getLast? = some x) : x ≠ '\n' := by
  cases h with
  | str hs => rw [stringLit_getLast hs] at hx; cases hx; decide
  | idRun hr => exact idRun_getLast hr x hx
  | quotedId hq _ =>
    obtain ⟨bs, hs, -⟩ := hq
    obtain ⟨body, rfl, -, -⟩ := hs
    rw [List.getLast?_cons_cons, getLast?_cons_snoc] at hx
    cases hx; decide

/-- No token ends with a line feed. -/
theorem tok1_getLast {p : Profile} {top : Bool} {c : Chars} {t : Tok} (h : Tok1 p top c t)
    (x : Char) (hx : c.getLast? = some x) : x ≠ '\n' := by
  cases p <;> cases t <;> simp only [Tok1] at h
  case v1.lp | core3.lp => subst h; simp at hx; rw [← hx]; decide
  case v1.rp | core3.rp => subst h; simp at hx; rw [← hx]; decide
  case v1.atom a =>
    cases a
    case str bs => simp only at h; rw [stringLit_getLast h] at hx; cases hx; decide
    all_goals exact idRun_getLast h x hx
  case core3.atom a => exact runAtom3_getLast h.1 x hx
  case core3.reserved =>
    rcases runPieces_getLast h.2.1 x hx with hr | rfl
    · rintro rfl; exact not_newline_idChar hr
    · decide
  case core3.punct c' =>
    obtain ⟨-, hp, rfl⟩ := h
    simp at hx; subst hx
    rintro rfl; revert hp; decide

set_option linter.unusedTactic false in
theorem tok1_ne_nil {p : Profile} {top : Bool} {c : Chars} {t : Tok} (h : Tok1 p top c t) :
    c ≠ [] := by
  rintro rfl
  cases p <;> cases t <;> simp only [Tok1] at h
  case v1.lp | core3.lp | v1.rp | core3.rp => simp at h
  case v1.atom a =>
    cases a
    case str bs => obtain ⟨body, hb, -⟩ := h; simp at hb
    all_goals cases h <;> simp_all
  case core3.atom a =>
    rcases h.1 with ⟨hs⟩ | ⟨hr⟩ | ⟨-, -⟩
    · obtain ⟨body, hb, -⟩ := hs; simp at hb
    · cases hr
      simp_all
  case core3.reserved => exact h.2.2.1 rfl
  case core3.punct => simp at h

/-- **Concatenation of token sequences** after a line feed. -/
theorem lex_append {p : Profile} {top : Bool} :
    ∀ {s₁ s₂ : Chars} {ts₁ ts₂ : List Tok}, Lex p top s₁ ts₁ → Lex p top s₂ ts₂ →
      s₁.getLast? = some '\n' → Lex p top (s₁ ++ s₂) (ts₁ ++ ts₂)
  | _, _, _, _, .done h, h₂, _ => lex_space_prepend h h₂
  | _, _, _, _, @Lex.doneEof _ s body _ hn, _, hl => by
    exfalso
    have hl' : (';' :: ';' :: body).getLast? = some '\n' := by
      rw [List.getLast?_append_of_ne_nil _ (by simp)] at hl
      exact hl
    cases body with
    | nil => simp at hl'
    | cons b bs =>
      rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at hl'
      refine hn _ (List.mem_of_getLast? hl') ?_
      cases p <;> simp [IsNewlineP]
  | _, s₂, _, ts₂, @Lex.step _ _ s c rest t ts hs hc hf hr, h₂, hl =>
    show Lex p top (s ++ c ++ rest ++ s₂) ((t :: ts) ++ ts₂) from by
      have hcn : c ≠ [] := tok1_ne_nil hc
      -- the token cannot end the line feed, so something follows it in `s₁`
      have hrest : rest ≠ [] := by
        intro hrest
        have hl0 : (s ++ c).getLast? = some '\n' := by
          simpa only [hrest, List.append_nil] using hl
        have hlc : c.getLast? = some '\n' := by
          rw [← List.getLast?_append_of_ne_nil s hcn]; exact hl0
        exact tok1_getLast hc _ hlc rfl
      have hl' : rest.getLast? = some '\n' := by
        rw [← List.getLast?_append_of_ne_nil (s ++ c) hrest]; exact hl
      have ih : Lex p top (rest ++ s₂) (ts ++ ts₂) := lex_append hr h₂ hl'
      have hf' : Follow p t (rest ++ s₂) := by
        refine follow_head ?_ hf
        cases rest with
        | nil => exact absurd rfl hrest
        | cons _ _ => rfl
      have e : s ++ c ++ rest ++ s₂ = s ++ c ++ (rest ++ s₂) := by simp [List.append_assoc]
      rw [e, List.cons_append]
      exact .step hs hc hf' ih

theorem trees_append : ∀ {a b : List Tok} {xs ys : List SExp}, Trees a xs → Trees b ys →
    Trees (a ++ b) (xs ++ ys)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h₁ h₂, h => by
    rw [List.append_assoc, List.cons_append]
    exact .cons h₁ (trees_append h₂ h)

/-- **The lexical grammar is closed under concatenation after a line feed.** -/
theorem sexpWat_append {p : Profile} {s₁ s₂ : String} {xs₁ xs₂ : List SExp}
    (h₁ : sexpWat p s₁ (doc xs₁)) (h₂ : sexpWat p s₂ (doc xs₂))
    (hl : s₁.toList.getLast? = some '\n') : sexpWat p (s₁ ++ s₂) (doc (xs₁ ++ xs₂)) := by
  obtain ⟨ts₁, hl₁, ys₁, ht₁, he₁⟩ := h₁
  obtain ⟨ts₂, hl₂, ys₂, ht₂, he₂⟩ := h₂
  have e₁ := listOf_injective he₁
  have e₂ := listOf_injective he₂
  subst e₁ e₂
  refine ⟨ts₁ ++ ts₂, ?_, xs₁ ++ xs₂, trees_append ht₁ ht₂, rfl⟩
  show Lex p true (s₁ ++ s₂).toList (ts₁ ++ ts₂)
  rw [String.toList_append]
  exact lex_append hl₁ hl₂ hl

/-- The empty text spells the empty document. -/
theorem sexpWat_empty (p : Profile) : sexpWat p "" (doc []) :=
  ⟨[], .done .nil, [], .nil, rfl⟩

/-- **Chunks**: a list of texts, each but the last ending with a line feed, each spelling
its documents, spells the concatenation. -/
theorem sexpWat_chunks {p : Profile} :
    ∀ (cs : List (String × List SExp)),
      (∀ c ∈ cs, sexpWat p c.1 (doc c.2)) →
      (∀ c ∈ cs.dropLast, c.1.toList.getLast? = some '\n') →
      sexpWat p (joinStr (cs.map (·.1))) (doc (cs.flatMap (·.2)))
  | [], _, _ => sexpWat_empty p
  | [c], h, _ => by simpa [joinStr] using h c (by simp)
  | c :: d :: cs, h, hl => by
    have ih := sexpWat_chunks (d :: cs) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (fun x hx => hl x (by rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hx))
    have := sexpWat_append (h c (by simp)) ih (hl c (by rw [List.dropLast_cons_cons]; simp))
    simpa [joinStr] using this

theorem eraseList_eq (xs : List PNode) : PNode.eraseList xs = listOf (xs.map PNode.erase) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [PNode.eraseList, ih, listOf]

theorem flatMap_erase (gs : List (String × List PNode)) :
    (gs.map fun g => (g.1, g.2.map PNode.erase)).flatMap (·.2) =
      (gs.flatMap (·.2)).map PNode.erase := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, List.flatMap_cons, ih, List.map_append]

/-- **The chunk check is sound.** -/
theorem chunkCheck_sound {s : String} {gs : List (String × List PNode)}
    (h : chunkCheck s gs = true) :
    sexpWat .core3 s (doc ((gs.flatMap (·.2)).map PNode.erase)) := by
  simp only [chunkCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hj, hl⟩, hx⟩ := h
  let cs : List (String × List SExp) := gs.map fun g => (g.1, g.2.map PNode.erase)
  have h1 : ∀ c ∈ cs, sexpWat .core3 c.1 (doc c.2) := by
    intro c hc
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
    have := sexpWat_of_fullExec (hx g hg)
    rwa [eraseList_eq] at this
  have h2 : ∀ c ∈ cs.dropLast, c.1.toList.getLast? = some '\n' := by
    intro c hc
    rw [← List.map_dropLast] at hc
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
    exact hl g hg
  have := sexpWat_chunks cs h1 h2
  have e1 : cs.map (·.1) = gs.map (·.1) := by simp [cs]
  have e2 : cs.flatMap (·.2) = (gs.flatMap (·.2)).map PNode.erase := by
    exact flatMap_erase gs
  rwa [e1, hj, e2] at this

end Silmaril.Wasm.Tools.Wast.LexAppend
