module

public import Silmaril.Cli.Clap.Help.Defs

/-!
# clap's help layout: wrapping only moves white space

* **`wrap_erase`**: `wrap hard s` and `s` are the same text up to white space: the wrapping
  (clap's `LineWrapper`, `Silmaril.Cli.Clap.Help.wrap`) only inserts line breaks and repeats a
  line's indentation, and drops trailing white space; it never changes, drops, reorders or adds
  a visible character, at any width.
* `trimEnd_erase`, `wrapWords_erase`, `words_flatten`, `linesIncl_flatten`: the steps.

The layout itself (where the breaks go) is checked byte for byte against clap by
`tools/cli-spec/tests/wasm-tools-surface.sh` (every help text of wasm-tools 1.262.0 at 100 and
80 columns).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Clap.Help

/-- The white space `trimEnd` drops. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- A text without its white space. -/
def erase (l : List Char) : List Char := l.filter fun c => !isWs c

theorem erase_append (a b : List Char) : erase (a ++ b) = erase a ++ erase b :=
  List.filter_append ..

theorem erase_reverse (l : List Char) : erase l.reverse = (erase l).reverse :=
  List.filter_reverse ..

/-- Dropping leading white space does not change the erased text. -/
theorem erase_dropWhile (l : List Char) : erase (l.dropWhile isWs) = erase l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : isWs c = true
    · have e : erase (c :: cs) = erase cs := by simp [erase, h]
      rw [List.dropWhile_cons_of_pos h, ih, e]
    · rw [List.dropWhile_cons_of_neg h]

/-- `trimEnd` drops white space only. -/
theorem trimEnd_erase (w : List Char) : erase (trimEnd w) = erase w := by
  have e : trimEnd w = (w.reverse.dropWhile isWs).reverse := rfl
  rw [e, erase_reverse, erase_dropWhile, erase_reverse, List.reverse_reverse]

/-- The erased text of a list of words. -/
theorem erase_flatten (L : List (List Char)) : erase L.flatten = (L.map erase).flatten := by
  induction L with
  | nil => rfl
  | cons l L ih => rw [List.flatten_cons, erase_append, ih]; rfl

/-- The words of a line are the line, cut. -/
theorem wordsAux_flatten (l cur : List Char) (inWs : Bool) :
    (wordsAux l cur inWs).flatten = cur.reverse ++ l := by
  induction l generalizing cur inWs with
  | nil =>
    unfold wordsAux
    by_cases h : cur.isEmpty = true
    · simp [List.isEmpty_iff.mp h]
    · simp [h]
  | cons c cs ih =>
    unfold wordsAux
    split
    · simp [ih]
    · simp [ih]

theorem words_flatten (l : List Char) : (words l).flatten = l := by
  simp [words, wordsAux_flatten]

/-- The lines of a text are the text, cut after its newlines. -/
theorem linesIncl_flatten (l cur : List Char) : (linesIncl l cur).flatten = cur.reverse ++ l := by
  induction l generalizing cur with
  | nil =>
    unfold linesIncl
    by_cases h : cur.isEmpty = true
    · simp [List.isEmpty_iff.mp h]
    · simp [h]
  | cons c cs ih =>
    by_cases h : c = '\n'
    · subst h
      simp [linesIncl, ih]
    · have e : linesIncl (c :: cs) cur = linesIncl cs (c :: cur) := by
        conv => lhs; unfold linesIncl
        split <;> simp_all
      simp [e, ih]

/-- A line's indentation is white space. -/
theorem indentOf_erase (ws : List (List Char)) : erase (indentOf ws) = [] := by
  unfold indentOf
  split
  · next w _ =>
    split
    · next h =>
      have e : trimEnd w = [] := List.isEmpty_iff.mp h
      rw [← trimEnd_erase, e]; rfl
    · rfl
  · rfl

/-- One word more on the accumulator (which is reversed). -/
theorem erase_rev_cons (w : List Char) (acc : List (List Char)) :
    erase (w :: acc).reverse.flatten = erase acc.reverse.flatten ++ erase w := by
  simp [List.flatten_append, erase_append]

/-- **One line's wrapping** keeps the erased text, when the repeated indentation is white
space. -/
theorem wrapWords_erase (hard : Nat) (ind : List Char) (hind : erase ind = []) :
    ∀ (ws : List (List Char)) (lw : Nat) (first : Bool) (acc : List (List Char)),
      erase (wrapWords hard ind lw first acc ws).reverse.flatten =
        erase acc.reverse.flatten ++ erase ws.flatten := by
  intro ws
  induction ws with
  | nil => intro _ _ acc; simp [wrapWords, erase]
  | cons w ws ih =>
    intro lw first acc
    have hw : erase (w :: ws).flatten = erase w ++ erase ws.flatten := by
      rw [List.flatten_cons, erase_append]
    unfold wrapWords
    simp only
    split
    · rw [ih, erase_rev_cons, hw, List.append_assoc]
    · split
      · rw [ih, erase_rev_cons, erase_rev_cons, erase_rev_cons, hind, hw]
        cases acc with
        | nil => simp [erase, isWs]
        | cons p ps =>
          simp only [erase_rev_cons, trimEnd_erase]
          simp [erase, isWs]
      · rw [ih, erase_rev_cons, hw, List.append_assoc]

/-- **clap's wrapping only moves white space**: at any width, `wrap hard s` is `s` with line
breaks and repeated indentation inserted and trailing white space dropped. -/
theorem wrap_erase (hard : Nat) (s : String) : erase (wrap hard s).toList = erase s.toList := by
  have hline : ∀ l : List Char,
      erase ((wrapWords hard (indentOf (words l)) 0 true [] (words l)).reverse.flatten) =
        erase l := by
    intro l
    rw [wrapWords_erase hard _ (indentOf_erase _), words_flatten]; rfl
  have hall : ∀ L : List (List Char),
      erase (L.flatMap fun l =>
        (wrapWords hard (indentOf (words l)) 0 true [] (words l)).reverse.flatten) =
        erase L.flatten := by
    intro L
    induction L with
    | nil => rfl
    | cons l L ih => rw [List.flatMap_cons, erase_append, ih, hline, List.flatten_cons, erase_append]
  simp only [wrap, String.toList_ofList]
  rw [trimEnd_erase, hall, linesIncl_flatten]; rfl

end Silmaril.Cli.Clap.Help
