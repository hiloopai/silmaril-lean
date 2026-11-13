module

public import Silmaril.Wasm.Wit.Text.Docs.Defs
public import Silmaril.Wasm.Wit.Text.Print.Defs

/-!
# WIT text with `wit-parser`'s doc comments: proofs

`normDocs_clean`: on `///` comments of one space and a clean line each (no leading
ASCII whitespace, no trailing whitespace, no newline), `wit-parser`'s normalisation is
the plain reading of `///` lines (`Parse.mkDocs` strips one space and joins the lines
with newlines). So the two front ends agree on such documentation; they differ on
indentation (dedent by the common amount, not by one space), trailing whitespace,
`//` and block comments.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

/-- A clean doc line: not empty, no leading ASCII whitespace, no trailing whitespace,
no newline. -/
def cleanLine (s : List Char) : Bool :=
  match s.head?, s.getLast? with
  | some a, some b => !isAsciiWs a && !isWs b && !s.contains '\n'
  | _, _ => false

theorem trimEnd_of_last (l : List Char) (b : Char) (hb : l.getLast? = some b) (hw : isWs b = false) :
    trimEnd l = l := by
  obtain ⟨l', rfl⟩ : ∃ l', l = l' ++ [b] := by
    rcases List.eq_nil_or_concat' l with rfl | ⟨l', z, rfl⟩
    · exact absurd hb (by simp)
    · have hz : z = b := by simpa using hb
      exact ⟨l', by rw [hz]⟩
  simp [trimEnd, hw]

theorem commentBody_clean (s : List Char) (h : cleanLine s = true) :
    commentBody ('/' :: '/' :: '/' :: ' ' :: s) = ' ' :: s := by
  obtain ⟨b, hb, hw⟩ : ∃ b, s.getLast? = some b ∧ isWs b = false := by
    unfold cleanLine at h
    cases ha : s.head? <;> cases hl : s.getLast? <;> simp_all
  have hl : (' ' :: s).getLast? = some b := by
    cases s with
    | nil => simp at hb
    | cons x xs => simpa [List.getLast?_cons] using hb
  have hd : ('/' :: '/' :: '/' :: ' ' :: s).dropWhile (· == '/') = ' ' :: s := by simp
  show trimEnd (('/' :: '/' :: '/' :: ' ' :: s).dropWhile (· == '/')) = ' ' :: s
  rw [hd, trimEnd_of_last _ b hl hw]

theorem leadWs_clean (s : List Char) (h : cleanLine s = true) : leadWs (' ' :: s) = 1 := by
  cases s with
  | nil => simp [cleanLine] at h
  | cons a r =>
    have ha : isAsciiWs a = false := by
      unfold cleanLine at h
      cases hl : (a :: r).getLast? <;> simp_all
    have hsp : isAsciiWs ' ' = true := rfl
    simp [leadWs, hsp, ha]

theorem min?_ones : ∀ l : List Nat, l ≠ [] → (∀ x ∈ l, x = 1) → l.min? = some 1
  | [], hne, _ => absurd rfl hne
  | [x], _, h => by rw [h x (by simp)]; rfl
  | x :: y :: l, _, h => by
    have ih : (y :: l).min? = some 1 :=
      min?_ones (y :: l) (by simp) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hx : x = 1 := h x (by simp)
    rw [List.min?_cons, ih, hx]; rfl

theorem splitNl_of_not_mem : ∀ s : List Char, '\n' ∉ s → splitNl s = [s]
  | [], _ => rfl
  | c :: r, h => by
    have hr : '\n' ∉ r := fun hm => h (List.mem_cons_of_mem _ hm)
    have ih : splitNl r = [r] := splitNl_of_not_mem r hr
    have hc : c ≠ '\n' := fun he => h (by simp [he])
    rw [splitNl.eq_def]
    split
    next he => exact absurd he (by simp)
    next r' he => exact absurd (List.cons.inj he).1 hc
    next c' r' _ he =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rw [ih]

theorem rustLines_clean (s : List Char) (h : cleanLine s = true) : rustLines s = [s] := by
  obtain ⟨b, hb, hw, hn⟩ : ∃ b, s.getLast? = some b ∧ isWs b = false ∧ '\n' ∉ s := by
    unfold cleanLine at h
    cases ha : s.head? <;> cases hl : s.getLast? <;> simp_all
  have hb1 : b ≠ '\n' := fun he => by simp [he, isWs] at hw
  have hb2 : b ≠ '\r' := fun he => by simp [he, isWs] at hw
  simp [rustLines, splitNl_of_not_mem s hn, hb, hb1, hb2]

theorem dropTrailingNl_append (x y : List Char) (h : dropTrailingNl y ≠ []) :
    dropTrailingNl (x ++ y) = x ++ dropTrailingNl y := by
  unfold dropTrailingNl at h ⊢
  have hne : (y.reverse.dropWhile (· == '\n')).isEmpty = false := by
    simpa using h
  rw [List.reverse_append, List.dropWhile_append, hne]
  simp

theorem dropTrailingNl_line (s : List Char) (h : cleanLine s = true) :
    dropTrailingNl (s ++ ['\n']) = s := by
  obtain ⟨b, hb, hw⟩ : ∃ b, s.getLast? = some b ∧ isWs b = false := by
    unfold cleanLine at h
    cases ha : s.head? <;> cases hl : s.getLast? <;> simp_all
  obtain ⟨s', rfl⟩ : ∃ s', s = s' ++ [b] := by
    rcases List.eq_nil_or_concat' s with rfl | ⟨s', z, rfl⟩
    · exact absurd hb (by simp)
    · have hz : z = b := by simpa using hb
      exact ⟨s', by rw [hz]⟩
  have hb1 : (b == '\n') = false := by
    cases hc : b == '\n'
    · rfl
    · have : b = '\n' := by simpa using hc
      simp [this, isWs] at hw
  simp [dropTrailingNl, hb1]

theorem dropTrailingNl_lines : ∀ ls : List (List Char), ls ≠ [] → (∀ s ∈ ls, cleanLine s = true) →
    dropTrailingNl (ls.flatMap (· ++ ['\n'])) = joinOn '\n' ls
  | [], hne, _ => absurd rfl hne
  | [s], _, h => by
    simpa [joinOn] using dropTrailingNl_line s (h s (List.mem_singleton_self _))
  | s :: t :: r, _, h => by
    have hr : ∀ x ∈ t :: r, cleanLine x = true := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ih : dropTrailingNl ((t :: r).flatMap (· ++ ['\n'])) = joinOn '\n' (t :: r) :=
      dropTrailingNl_lines (t :: r) (by simp) hr
    have hne : dropTrailingNl ((t :: r).flatMap (· ++ ['\n'])) ≠ [] := by
      rw [ih]
      have ht : cleanLine t = true := hr t (List.mem_cons_self ..)
      cases t with
      | nil => simp [cleanLine] at ht
      | cons c u => cases r <;> simp [joinOn]
    show dropTrailingNl ((s ++ ['\n']) ++ (t :: r).flatMap (· ++ ['\n'])) = s ++ '\n' :: joinOn '\n' (t :: r)
    rw [dropTrailingNl_append _ _ hne, ih]
    simp

/-- **`wit-parser`'s normalisation on clean `///` lines** is the plain reading: the
lines joined with newlines. -/
theorem normDocs_clean (ls : List (List Char)) (hne : ls ≠ []) (h : ∀ s ∈ ls, cleanLine s = true) :
    normDocs (ls.map fun s => '/' :: '/' :: '/' :: ' ' :: s) = some (joinOn '\n' ls) := by
  have hb : (ls.map fun s => '/' :: '/' :: '/' :: ' ' :: s).map commentBody = ls.map (' ' :: ·) := by
    rw [List.map_map]
    exact List.map_congr_left fun s hs => commentBody_clean s (h s hs)
  have hf : (ls.map (' ' :: ·)).filter (· ≠ []) = ls.map (' ' :: ·) := by
    simp
  have hm : ((ls.map (' ' :: ·)).map leadWs).min? = some 1 := by
    apply min?_ones
    · simpa using hne
    · intro x hx
      obtain ⟨s, hs, rfl⟩ : ∃ s ∈ ls, leadWs (' ' :: s) = x := by simpa using hx
      exact leadWs_clean s (h s hs)
  have hs : (ls.map (' ' :: ·)).map (stripSpaces 1) = ls := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id ls]
    exact List.map_congr_left fun s _ => by simp [stripSpaces]
  have hl : ls.flatMap (fun d => if d = [] then ['\n'] else (rustLines d).flatMap (· ++ ['\n'])) =
      ls.flatMap (· ++ ['\n']) := by
    apply List.flatMap_congr
    intro s hs'
    have hne' : s ≠ [] := by
      intro he
      have := h s hs'
      simp [he, cleanLine] at this
    simp [hne', rustLines_clean s (h s hs')]
  have hcons : (ls.map fun s => '/' :: '/' :: '/' :: ' ' :: s) ≠ [] := by simpa using hne
  unfold normDocs
  split
  · next he => exact absurd he hcons
  · simp only [hb, hf, hm, Option.getD_some, gt_iff_lt, Nat.lt_one_iff, ite_true, hs, hl]
    rw [dropTrailingNl_lines ls hne h]

/-! ## Examples -/

/-- A block doc comment keeps its line structure; its first line is empty. -/
theorem normDocs_block : normDocs ["/**\n * A\n */".toList] = some "\n * A".toList := by decide

/-- `///` lines are dedented by their common indentation; an empty one at the end
is dropped with the trailing newlines. -/
theorem normDocs_dedent :
    normDocs ["///   a".toList, "///     b".toList, "///".toList] = some "a\n  b".toList := by
  decide

/-- A plain block comment keeps its stars (`trim_start_matches('/')`). -/
theorem normDocs_plain_block : normDocs ["/* c */".toList] = some "* c */".toList := by decide

end Silmaril.Wasm.Wit.Text
