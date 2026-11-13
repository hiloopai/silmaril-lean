module

public import Silmaril.Wasm.Component.Streams.Chunks.Defs
public import Silmaril.Wasm.Component.Streams.Spec.Thms

/-!
# Byte-chunk streams: proofs

Proofs of `Silmaril.Wasm.Component.Streams.Chunks.Thms`.

* `cut_append`: cutting a concatenation cuts the first part, then the remainder followed by the
  second part. `cut_rem_free`, `cut_free`, `cut_lines_free`, `cut_join`: the remainder and the
  lines contain no separator, and the lines with their separators and the remainder give the
  input back.
* `feed_linesT`: after feeding chunks from a separator-free buffer, the state and outputs are the
  remainder and the lines of the buffer followed by the concatenation.
* `chunksOf_append`, `flatten_chunksOf`, `chunksOf_lengths`: uniform chunks.
* `feed_rechunk`: after feeding chunks from a short buffer, the output is the full chunks of the
  buffer followed by the concatenation, and the state is the rest.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Chunks

open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Tr
open Silmaril.Proofs.Wasm.Component.Streams.Spec

variable {α β : Type}

/-! ## Lines -/

section Lines

variable (sep : α → Bool)

/-- Prepend a non-separator to a cut. -/
def push (b : α) : List (List α) × List α → List (List α) × List α
  | (l :: ls, r) => ((b :: l) :: ls, r)
  | ([], r) => ([], b :: r)

theorem cut_nil : cut sep [] = ([], []) := rfl

theorem cut_cons_sep (b : α) (bs : List α) (h : sep b = true) :
    cut sep (b :: bs) = ([] :: (cut sep bs).1, (cut sep bs).2) := by
  simp [cut, h]

theorem cut_cons_ne (b : α) (bs : List α) (h : sep b = false) :
    cut sep (b :: bs) = push b (cut sep bs) := by
  rw [cut.eq_2]
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  generalize cut sep bs = p
  rcases p with ⟨_ | ⟨l, ls⟩, r⟩ <;> rfl

theorem push_eta (b : α) (p : List (List α) × List α) : push b (p.1, p.2) = push b p := rfl

/-- The step of `cut_append` for a non-separator. -/
theorem push_cut_append (x : α) (hx : sep x = false) (p : List (List α) × List α) (ys : List α) :
    push x (p.1 ++ (cut sep (p.2 ++ ys)).1, (cut sep (p.2 ++ ys)).2) =
      ((push x p).1 ++ (cut sep ((push x p).2 ++ ys)).1, (cut sep ((push x p).2 ++ ys)).2) := by
  rcases p with ⟨_ | ⟨l, ls⟩, r⟩
  · show push x ((cut sep (r ++ ys)).1, (cut sep (r ++ ys)).2) =
      ([] ++ (cut sep (x :: (r ++ ys))).1, (cut sep (x :: (r ++ ys))).2)
    rw [List.nil_append, cut_cons_ne sep x _ hx, push_eta]
  · rfl

/-- **Cutting a concatenation.** -/
theorem cut_append (xs ys : List α) :
    cut sep (xs ++ ys) =
      ((cut sep xs).1 ++ (cut sep ((cut sep xs).2 ++ ys)).1, (cut sep ((cut sep xs).2 ++ ys)).2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : sep x
    · rw [List.cons_append, cut_cons_ne sep x _ hx, cut_cons_ne sep x _ hx, ih]
      exact push_cut_append sep x hx (cut sep xs) ys
    · rw [List.cons_append, cut_cons_sep sep x _ hx, cut_cons_sep sep x _ hx, ih]
      rfl

/-- No item of `l` is a separator. -/
@[expose] def Free (l : List α) : Prop := ∀ x ∈ l, sep x = false

theorem free_cons (b : α) (l : List α) (hb : sep b = false) (h : Free sep l) : Free sep (b :: l) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  · exact h x hx

theorem push_rem_free (b : α) (hb : sep b = false) (p : List (List α) × List α)
    (h : Free sep p.2) : Free sep (push b p).2 := by
  rcases p with ⟨_ | ⟨l, ls⟩, r⟩
  · exact free_cons sep b r hb h
  · exact h

/-- The remainder contains no separator. -/
theorem cut_rem_free (bs : List α) : Free sep (cut sep bs).2 := by
  induction bs with
  | nil => intro x hx; cases hx
  | cons b bs ih =>
    cases hb : sep b
    · rw [cut_cons_ne sep b bs hb]
      exact push_rem_free sep b hb _ ih
    · rw [cut_cons_sep sep b bs hb]
      exact ih

/-- A separator-free list is its own remainder. -/
theorem cut_free (bs : List α) (h : Free sep bs) : cut sep bs = ([], bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : sep b = false := h b List.mem_cons_self
    have hbs : Free sep bs := fun x m => h x (List.mem_cons_of_mem _ m)
    rw [cut_cons_ne sep b bs hb, ih hbs]
    rfl

theorem push_lines_free (b : α) (hb : sep b = false) (p : List (List α) × List α)
    (h : ∀ l ∈ p.1, Free sep l) : ∀ l ∈ (push b p).1, Free sep l := by
  rcases p with ⟨_ | ⟨l₀, ls⟩, r⟩
  · intro l hl
    cases hl
  · intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact free_cons sep b l₀ hb (h l₀ List.mem_cons_self)
    · exact h l (List.mem_cons_of_mem _ hl)

/-- The complete lines contain no separator. -/
theorem cut_lines_free (bs : List α) : ∀ l ∈ (cut sep bs).1, Free sep l := by
  induction bs with
  | nil => intro l hl; cases hl
  | cons b bs ih =>
    cases hb : sep b
    · rw [cut_cons_ne sep b bs hb]
      exact push_lines_free sep b hb _ ih
    · rw [cut_cons_sep sep b bs hb]
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · intro x hx
        cases hx
      · exact ih l hl

theorem push_join (nl b : α) (bs : List α) (p : List (List α) × List α)
    (h : p.1.flatMap (· ++ [nl]) ++ p.2 = bs) :
    (push b p).1.flatMap (· ++ [nl]) ++ (push b p).2 = b :: bs := by
  rcases p with ⟨_ | ⟨l₀, ls⟩, r⟩
  · simpa [push] using h
  · simpa [push] using h

/-- **The lines with their separators, then the remainder, give the input back**, when the
separator is a single item `nl`. -/
theorem cut_join (nl : α) (hsep : ∀ x, sep x = true → x = nl) (bs : List α) :
    (cut sep bs).1.flatMap (· ++ [nl]) ++ (cut sep bs).2 = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases hb : sep b
    · rw [cut_cons_ne sep b bs hb]
      exact push_join nl b bs _ ih
    · rw [cut_cons_sep sep b bs hb, hsep b hb]
      simpa using ih

theorem linesT_step (buf c : List α) :
    (linesT sep).step buf c = ((cut sep (buf ++ c)).2, (cut sep (buf ++ c)).1) := rfl

/-- **The line splitter's invariant.** -/
theorem feed_linesT (buf : List α) (hbuf : Free sep buf) (cs : List (List α)) :
    (linesT sep).feed buf cs =
      ((cut sep (buf ++ cs.flatten)).2, (cut sep (buf ++ cs.flatten)).1) := by
  induction cs generalizing buf with
  | nil => simp [feed_nil, cut_free sep buf hbuf]
  | cons c cs ih =>
    have hd : (linesT sep).done buf = false := rfl
    have ih' := ih (cut sep (buf ++ c)).2 (cut_rem_free sep _)
    have hcat : buf ++ (c :: cs).flatten = (buf ++ c) ++ cs.flatten := by simp
    rw [feed_cons, hd, ite_ff, linesT_step, ih', hcat, cut_append sep (buf ++ c)]

/-- **The line splitter computes the lines of the concatenation.** -/
theorem run_linesT (cs : List (List α)) : (linesT sep).run cs = lines sep cs.flatten := by
  show ((linesT sep).feed [] cs).2 ++ (linesT sep).flush ((linesT sep).feed [] cs).1 = _
  rw [feed_linesT sep [] (fun x hx => by cases hx) cs, List.nil_append]
  rfl

end Lines

/-! ## Uniform chunks -/

theorem chunksOf_nil (n : Nat) : chunksOf n ([] : List α) = [] := by
  rw [chunksOf]
  simp

theorem chunksOf_zero (bs : List α) (h : bs ≠ []) : chunksOf 0 bs = [bs] := by
  rw [chunksOf]
  simp [h]

theorem chunksOf_cons (n : Nat) (bs : List α) (h : bs ≠ []) (hn : n ≠ 0) :
    chunksOf n bs = bs.take n :: chunksOf n (bs.drop n) := by
  rw [chunksOf]
  simp [h, hn]

/-- A nonempty list of at most `n` items is one chunk. -/
theorem chunksOf_short (n : Nat) (bs : List α) (h : bs ≠ []) (hl : bs.length ≤ n) :
    chunksOf n bs = [bs] := by
  by_cases hn : n = 0
  · rw [hn]
    exact chunksOf_zero bs h
  · rw [chunksOf_cons n bs h hn, List.take_of_length_le hl, List.drop_of_length_le hl,
      chunksOf_nil]

/-- A rest with fewer than `n` items (`length / n = 0`) is the last chunk, if any. -/
theorem chunksOf_rest (n : Nat) (r : List α) (h : r.length / n = 0) :
    chunksOf n r = if r = [] then [] else [r] := by
  by_cases hr : r = []
  · simp [hr, chunksOf_nil]
  · simp only [hr, ↓reduceIte]
    by_cases hn : n = 0
    · rw [hn]
      exact chunksOf_zero r hr
    · have hlt : r.length < n := (Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero hn)).mp h
      exact chunksOf_short n r hr (Nat.le_of_lt hlt)

/-- **Chunking a concatenation whose first part is a whole number of chunks.** -/
theorem chunksOf_append (n : Nat) (xs ys : List α) (h : n ∣ xs.length) :
    chunksOf n (xs ++ ys) = chunksOf n xs ++ chunksOf n ys := by
  obtain ⟨k, hk⟩ := h
  by_cases hn : n = 0
  · have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa [hn] using hk)
    rw [hx, List.nil_append, chunksOf_nil, List.nil_append]
  induction k generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using hk)
    rw [hx, List.nil_append, chunksOf_nil, List.nil_append]
  | succ k ih =>
    have hle : n ≤ xs.length := by rw [hk]; exact Nat.le_mul_of_pos_right n (by omega)
    have hxs : xs ≠ [] := List.length_pos_iff.mp (by omega)
    have hxy : xs ++ ys ≠ [] := by simp [hxs]
    have hdrop : (xs.drop n).length = n * k := by
      rw [List.length_drop, hk, Nat.mul_succ]
      omega
    rw [chunksOf_cons n _ hxy hn, chunksOf_cons n _ hxs hn, List.take_append_of_le_length hle,
      List.drop_append_of_le_length hle, ih _ hdrop]
    rfl

/-- **Chunks concatenate to the input.** -/
theorem flatten_chunksOf (n : Nat) (bs : List α) : (chunksOf n bs).flatten = bs := by
  induction bs using chunksOf.induct n with
  | case1 => simp [chunksOf_nil]
  | case2 bs h hn =>
    rw [hn, chunksOf_zero bs h]
    simp
  | case3 bs h hn ih =>
    rw [chunksOf_cons n bs h hn, List.flatten_cons, ih, List.take_append_drop]

/-- The first chunk of a list with more than one chunk is full. -/
theorem take_full (n : Nat) (bs : List α) (hrest : bs.drop n ≠ []) : (bs.take n).length = n := by
  have hle : n ≤ bs.length := by
    rcases Nat.lt_or_ge bs.length n with hlt | hge
    · exact absurd (List.drop_eq_nil_of_le (Nat.le_of_lt hlt)) hrest
    · exact hge
  simp only [List.length_take]
  omega

/-- Every chunk has `1..n` items. -/
theorem chunksOf_pos_le (n : Nat) (hn : n ≠ 0) (bs : List α) :
    ∀ c ∈ chunksOf n bs, 0 < c.length ∧ c.length ≤ n := by
  induction bs using chunksOf.induct n with
  | case1 => simp [chunksOf_nil]
  | case2 bs _ hn' => exact absurd hn' hn
  | case3 bs h _ ih =>
    rw [chunksOf_cons n bs h hn]
    have hpos : 0 < bs.length := List.length_pos_iff.mpr h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp only [List.length_take]
      omega
    · exact ih c hc

/-- Every chunk but the last has exactly `n` items. -/
theorem chunksOf_dropLast_full (n : Nat) (hn : n ≠ 0) (bs : List α) :
    ∀ c ∈ (chunksOf n bs).dropLast, c.length = n := by
  induction bs using chunksOf.induct n with
  | case1 => simp [chunksOf_nil]
  | case2 bs _ hn' => exact absurd hn' hn
  | case3 bs h _ ih =>
    rw [chunksOf_cons n bs h hn]
    by_cases hrest : bs.drop n = []
    · simp [hrest, chunksOf_nil]
    · have hne : chunksOf n (bs.drop n) ≠ [] := by
        rw [chunksOf_cons n _ hrest hn]
        simp
      rw [List.dropLast_cons_of_ne_nil hne]
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact take_full n bs hrest
      · exact ih c hc

/-- **Chunk sizes**: every chunk has `1..n` items, every chunk but the last exactly `n`. -/
theorem chunksOf_lengths (n : Nat) (hn : n ≠ 0) (bs : List α) :
    (∀ c ∈ chunksOf n bs, 0 < c.length ∧ c.length ≤ n) ∧
      (∀ c ∈ (chunksOf n bs).dropLast, c.length = n) :=
  ⟨chunksOf_pos_le n hn bs, chunksOf_dropLast_full n hn bs⟩

/-! ## The rechunker -/

theorem rechunk_step (n : Nat) (buf c : List α) :
    (rechunk n).step buf c =
      ((buf ++ c).drop ((buf ++ c).length / n * n),
        chunksOf n ((buf ++ c).take ((buf ++ c).length / n * n))) := rfl

theorem rechunk_flush (n : Nat) (r : List α) :
    (rechunk n).flush r = if r = [] then [] else [r] := rfl

/-- The rest after the full chunks is short. -/
theorem rest_short (n : Nat) (b : List α) : (b.drop (b.length / n * n)).length / n = 0 := by
  rw [List.length_drop]
  by_cases hn : n = 0
  · simp [hn]
  · have h1 : b.length - b.length / n * n = b.length % n := by
      have := Nat.div_add_mod b.length n
      rw [Nat.mul_comm] at this
      omega
    rw [h1]
    exact Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))

/-- The cut point of a concatenation, through the cut point of its first part. -/
theorem cut_point (n : Nat) (b f : List α) :
    (b ++ f).length / n * n =
      b.length / n * n + ((b.drop (b.length / n * n)) ++ f).length / n * n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hle : b.length / n * n ≤ b.length := Nat.div_mul_le_self _ _
    -- `d` is the length after the cut point of `b`
    have hd : ((b.drop (b.length / n * n)) ++ f).length + b.length / n * n = (b ++ f).length := by
      simp only [List.length_append, List.length_drop]
      omega
    have hdiv : (b ++ f).length / n = ((b.drop (b.length / n * n)) ++ f).length / n + b.length / n := by
      rw [← hd, Nat.add_mul_div_right _ _ hpos]
    rw [hdiv, Nat.add_mul, Nat.add_comm]

/-- **The rechunker's invariant.** -/
theorem feed_rechunk (n : Nat) (buf : List α) (hbuf : buf.length / n = 0)
    (cs : List (List α)) :
    (rechunk n).feed buf cs =
      ((buf ++ cs.flatten).drop ((buf ++ cs.flatten).length / n * n),
        chunksOf n ((buf ++ cs.flatten).take ((buf ++ cs.flatten).length / n * n))) := by
  induction cs generalizing buf with
  | nil => simp [feed_nil, hbuf, chunksOf_nil]
  | cons c cs ih =>
    have hd : (rechunk n).done buf = false := rfl
    have ih' := ih ((buf ++ c).drop ((buf ++ c).length / n * n)) (rest_short n _)
    have hcat : buf ++ (c :: cs).flatten = (buf ++ c) ++ cs.flatten := by simp
    have hle : (buf ++ c).length / n * n ≤ (buf ++ c).length := Nat.div_mul_le_self _ _
    have hK := cut_point n (buf ++ c) cs.flatten
    have hdvd : n ∣ ((buf ++ c).take ((buf ++ c).length / n * n)).length := by
      rw [List.length_take, Nat.min_eq_left hle]
      exact Nat.dvd_mul_left _ _
    rw [feed_cons, hd, ite_ff, rechunk_step, ih', hcat, hK, List.take_add, ← List.drop_drop,
      List.take_append_of_le_length hle, List.drop_append_of_le_length hle,
      chunksOf_append n _ _ hdvd]

/-- **The rechunker computes the uniform chunks of the concatenation.** -/
theorem run_rechunk (n : Nat) (cs : List (List α)) :
    (rechunk n).run cs = chunksOf n cs.flatten := by
  show ((rechunk n).feed [] cs).2 ++ (rechunk n).flush ((rechunk n).feed [] cs).1 = _
  rw [feed_rechunk n [] (by simp) cs, List.nil_append]
  have hdvd : n ∣ (cs.flatten.take (cs.flatten.length / n * n)).length := by
    rw [List.length_take, Nat.min_eq_left (Nat.div_mul_le_self _ _)]
    exact Nat.dvd_mul_left _ _
  have hsplit : chunksOf n cs.flatten =
      chunksOf n (cs.flatten.take (cs.flatten.length / n * n)) ++
        chunksOf n (cs.flatten.drop (cs.flatten.length / n * n)) := by
    rw [← chunksOf_append n _ _ hdvd, List.take_append_drop]
  rw [hsplit, chunksOf_rest n _ (rest_short n _), rechunk_flush]

end Silmaril.Proofs.Wasm.Component.Streams.Chunks
