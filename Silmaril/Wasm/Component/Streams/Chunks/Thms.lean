module

public import Silmaril.Wasm.Component.Streams.Chunks.Defs
public import Silmaril.Wasm.Component.Streams.Laws.Thms
public import Silmaril.Proofs.Wasm.Component.Streams.Chunks

/-!
# Byte-chunk streams: results

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.Chunks`.

**The line splitter.**

* **`run_linesT`**: `(linesT sep).run cs = lines sep cs.flatten`: the output depends on the
  concatenation only, so `linesT` is invariant under rechunking its input (`linesT_invariant`).
* `runP_linesT`: before the end of the input it has emitted exactly the complete lines so far
  (each line is emitted as soon as its separator has been read).
* The specification `lines`: `lines_free` (no line contains the separator) and `unlines_lines`
  (the lines, each followed by the separator, are the input, followed by one separator when the
  input does not end with one).

**The uniform rechunker.**

* **`run_rechunk`**: `(rechunk n).run cs = chunksOf n cs.flatten`; `runP_rechunk`: the full chunks
  so far.
* `flatten_chunksOf`, `chunksOf_lengths`: chunking loses nothing, every chunk has `1..n` items and
  all but the last exactly `n`.

**Respecting reassociation.** `Determined.respects`, `Determined.invariant` (a determined
transformer gives equal outputs on reassociated inputs), `respects_comp`, `determined_comp`,
`bytes_respects`, `bytesFilter_respects`, `unchunk_determined`.

**Laws.**

* `rechunk_linesT`: rechunking before splitting lines changes nothing (any `m`):
  `rechunk m ⟫ linesT sep` and `linesT sep` have the same whole outputs; more generally
  `comp_determined` for any concatenation-preserving first stage.
* `rechunk_rechunk`: rechunking twice is rechunking once to the second size.
* `bytes_rechunk`: a byte map commutes with rechunking.
* `pipeline_lines_filter_map`: lines, then a filter, then a map: the closed form, and its
  invariance under rechunking the input.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams

open Silmaril.Proofs.Wasm.Component.Streams.Chunks

variable {α β γ : Type}

/-! ## The specification of lines -/

/-- No line contains a separator. -/
theorem lines_free (sep : α → Bool) (bs : List α) : ∀ l ∈ lines sep bs, ∀ x ∈ l, sep x = false := by
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact cut_lines_free sep bs l hl
  · by_cases hr : (cut sep bs).2 = []
    · simp [hr] at hl
    · have hl' : l = (cut sep bs).2 := by simpa [hr] using hl
      rw [hl']
      exact cut_rem_free sep bs

/-- **The lines give the input back**: when the separator is a single item `nl`, the lines, each
followed by `nl`, are the input, with one more `nl` when the input does not end with one. -/
theorem unlines_lines (sep : α → Bool) (nl : α) (hsep : ∀ x, sep x = true → x = nl)
    (bs : List α) :
    (lines sep bs).flatMap (· ++ [nl]) = if (cut sep bs).2 = [] then bs else bs ++ [nl] := by
  have hj := cut_join sep nl hsep bs
  by_cases hr : (cut sep bs).2 = []
  · simp only [lines, hr, ↓reduceIte, List.append_nil]
    simpa [hr] using hj
  · simp only [lines, hr, ↓reduceIte, List.flatMap_append, List.flatMap_singleton]
    rw [← List.append_assoc, hj]

namespace Tr

/-! ## The line splitter -/

/-- **The line splitter computes the lines of the concatenation of its input.** -/
theorem run_linesT (sep : α → Bool) (cs : List (List α)) :
    (linesT sep).run cs = lines sep cs.flatten :=
  Silmaril.Proofs.Wasm.Component.Streams.Chunks.run_linesT sep cs

/-- Before the end of the input, the line splitter has emitted the complete lines so far. -/
theorem runP_linesT (sep : α → Bool) (cs : List (List α)) :
    (linesT sep).runP cs = (cut sep cs.flatten).1 := by
  show ((linesT sep).feed [] cs).2 = _
  rw [feed_linesT sep [] (fun x hx => by cases hx) cs, List.nil_append]

theorem linesT_determined (sep : α → Bool) : (linesT sep).Determined (lines sep) :=
  run_linesT sep

/-! ## The uniform rechunker -/

/-- **The rechunker computes the uniform chunks of the concatenation of its input.** -/
theorem run_rechunk (n : Nat) (cs : List (List α)) : (rechunk n).run cs = chunksOf n cs.flatten :=
  Silmaril.Proofs.Wasm.Component.Streams.Chunks.run_rechunk n cs

/-- Before the end of the input, the rechunker has emitted the full chunks so far. -/
theorem runP_rechunk (n : Nat) (cs : List (List α)) :
    (rechunk n).runP cs = chunksOf n (cs.flatten.take (cs.flatten.length / n * n)) := by
  show ((rechunk n).feed [] cs).2 = _
  rw [feed_rechunk n [] (by simp) cs, List.nil_append]

theorem rechunk_determined (n : Nat) : (rechunk n : Tr (List α) _ _).Determined (chunksOf n) :=
  run_rechunk n

/-! ## Respecting reassociation -/

/-- A determined transformer respects reassociation of its input. -/
theorem Determined.respects {σ : Type} {T : Tr σ (List α) (List β)}
    {f : List α → List (List β)} (h : T.Determined f) : T.Respects := by
  intro cs ds hcd
  show (T.run cs).flatten = (T.run ds).flatten
  rw [h cs, h ds, hcd]

/-- **A determined transformer is invariant under rechunking its input.** -/
theorem Determined.invariant {σ : Type} {T : Tr σ (List α) γ} {f : List α → List γ}
    (h : T.Determined f) (cs ds : List (List α)) (hcd : ChunkEq cs ds) : T.run cs = T.run ds := by
  rw [h cs, h ds, hcd]

theorem linesT_invariant (sep : α → Bool) (cs ds : List (List α)) (hcd : ChunkEq cs ds) :
    (linesT sep).run cs = (linesT sep).run ds :=
  (linesT_determined sep).invariant cs ds hcd

theorem respects_comp {σ τ : Type} {T : Tr σ (List α) (List β)} {U : Tr τ (List β) (List γ)}
    (hT : T.Respects) (hU : U.Respects) : (T ⟫ U).Respects := by
  intro cs ds hcd
  show ((T ⟫ U).run cs).flatten = ((T ⟫ U).run ds).flatten
  rw [run_comp', run_comp']
  exact hU _ _ (hT cs ds hcd)

/-- A determined first stage makes the composite determined. -/
theorem determined_comp {σ τ : Type} {T : Tr σ (List α) β} {U : Tr τ β γ}
    {f : List α → List β} (hT : T.Determined f) : (T ⟫ U).Determined (fun bs => U.run (f bs)) := by
  intro cs
  rw [run_comp', hT cs]

theorem run_bytes (f : α → β) (cs : List (List α)) : (bytes f).run cs = cs.map (·.map f) :=
  run_map _ cs

theorem flatten_run_bytes (f : α → β) (cs : List (List α)) :
    ((bytes f).run cs).flatten = cs.flatten.map f := by
  rw [run_bytes, List.map_flatten]

theorem bytes_respects (f : α → β) : (bytes f).Respects := by
  intro cs ds hcd
  show ((bytes f).run cs).flatten = ((bytes f).run ds).flatten
  rw [flatten_run_bytes, flatten_run_bytes, hcd]

theorem flatten_run_bytesFilter (p : α → Bool) (cs : List (List α)) :
    ((bytesFilter p).run cs).flatten = cs.flatten.filter p := by
  show ((map fun c => c.filter p).run cs).flatten = _
  rw [run_map, List.filter_flatten]

theorem bytesFilter_respects (p : α → Bool) : (bytesFilter p).Respects := by
  intro cs ds hcd
  show ((bytesFilter p).run cs).flatten = ((bytesFilter p).run ds).flatten
  rw [flatten_run_bytesFilter, flatten_run_bytesFilter, hcd]

theorem unchunk_determined : (unchunk : Tr Unit (List α) α).Determined (fun bs => bs) := by
  intro cs
  show (flatMap fun c => c).run cs = cs.flatten
  rw [run_flatMap, List.flatMap_id']

/-! ## Laws -/

/-- **Any concatenation-preserving first stage before a determined transformer changes
nothing.** -/
theorem comp_determined {σ τ : Type} {T : Tr σ (List α) (List α)} {U : Tr τ (List α) γ}
    {f : List α → List γ} (hU : U.Determined f) (hT : ∀ cs, (T.run cs).flatten = cs.flatten) :
    (T ⟫ U).EquivF U := by
  intro cs
  rw [run_comp', hU, hU, hT]

theorem flatten_run_rechunk (n : Nat) (cs : List (List α)) :
    ((rechunk n).run cs).flatten = cs.flatten := by
  rw [run_rechunk, flatten_chunksOf]

/-- **Rechunking before splitting lines changes nothing.** -/
theorem rechunk_linesT (m : Nat) (sep : α → Bool) :
    ((rechunk m : Tr (List α) _ _) ⟫ linesT sep).EquivF (linesT sep) :=
  comp_determined (linesT_determined sep) (flatten_run_rechunk m)

/-- Rechunking twice is rechunking once to the second size. -/
theorem rechunk_rechunk (m n : Nat) :
    ((rechunk m : Tr (List α) _ _) ⟫ rechunk n).EquivF (rechunk n) :=
  comp_determined (rechunk_determined n) (flatten_run_rechunk m)

theorem chunksOf_map (n : Nat) (f : α → β) (bs : List α) :
    chunksOf n (bs.map f) = (chunksOf n bs).map (·.map f) := by
  induction bs using chunksOf.induct n with
  | case1 => simp [chunksOf_nil]
  | case2 bs h hn =>
    have hm : bs.map f ≠ [] := by simpa using h
    rw [hn, chunksOf_zero _ hm, chunksOf_zero _ h]
    rfl
  | case3 bs h hn ih =>
    have hm : bs.map f ≠ [] := by simpa using h
    rw [chunksOf_cons n _ hm hn, chunksOf_cons n _ h hn, List.map_cons, ← ih, List.map_take,
      List.map_drop]

/-- **A byte map commutes with rechunking.** -/
theorem bytes_rechunk (n : Nat) (f : α → β) :
    (bytes f ⟫ rechunk n).EquivF (rechunk n ⟫ bytes f) := by
  intro cs
  rw [run_comp', run_comp', run_rechunk, run_bytes, run_rechunk, run_bytes, ← chunksOf_map,
    List.map_flatten]

/-- **Lines, then a filter, then a map**: the closed form, invariant under rechunking. -/
theorem pipeline_lines_filter_map (sep : α → Bool) (p : List α → Bool)
    (g : List α → β) (cs ds : List (List α)) (hcd : ChunkEq cs ds) :
    ((linesT sep ⟫ filter p) ⟫ map g).run cs = ((lines sep cs.flatten).filter p).map g ∧
      ((linesT sep ⟫ filter p) ⟫ map g).run cs = ((linesT sep ⟫ filter p) ⟫ map g).run ds := by
  have hd : ((linesT sep ⟫ filter p) ⟫ map g).Determined
      (fun bs => (map g).run ((filter p).run (lines sep bs))) :=
    determined_comp (determined_comp (linesT_determined sep))
  refine ⟨?_, hd.invariant cs ds hcd⟩
  rw [hd cs]
  show (map g).run ((filter p).run (lines sep cs.flatten)) = _
  rw [run_filter, run_map]

end Tr

end Silmaril.Wasm.Component.Streams
