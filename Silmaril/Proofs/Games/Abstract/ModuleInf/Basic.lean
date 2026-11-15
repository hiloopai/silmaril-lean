module

public import Silmaril.Games.Abstract.ModuleInf.Defs

/-!
# Closing with productive runs inside one function (proofs)

Stream bookkeeping (`streamAppend`, `StreamConcat`), the per-call reading of `SubstPre`
(`substPre_res`), and the closure lemmas of `closeInfL`: it extends `closeInf`, is monotone in
the productive runs, contains every resolved productive run of the called function, and is
closed under a descent in front.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.ModuleInf

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape

universe u

variable {sh : Shape.{u}}

/-! ## Streams -/

theorem streamAppend_nil {α : Type u} (ω : Nat → α) : [] ++ω ω = ω := by
  funext i
  simp [streamAppend]

theorem streamAppend_lt {α : Type u} {l : List α} {ω : Nat → α} {i : Nat} (h : i < l.length) :
    (l ++ω ω) i = l[i] := by
  simp [streamAppend, h]

theorem streamAppend_ge {α : Type u} {l : List α} {ω : Nat → α} {i : Nat} (h : l.length ≤ i) :
    (l ++ω ω) i = ω (i - l.length) := by
  simp [streamAppend, Nat.not_lt.mpr h]

theorem streamAppend_append {α : Type u} (l₁ l₂ : List α) (ω : Nat → α) :
    (l₁ ++ l₂) ++ω ω = l₁ ++ω (l₂ ++ω ω) := by
  funext i
  by_cases h1 : i < l₁.length
  · rw [streamAppend_lt (by simp; omega), streamAppend_lt h1, List.getElem_append_left h1]
  · rw [streamAppend_ge (l := l₁) (by omega)]
    by_cases h2 : i - l₁.length < l₂.length
    · rw [streamAppend_lt (by simp; omega), streamAppend_lt h2,
        List.getElem_append_right (by omega)]
    · rw [streamAppend_ge (by simp; omega), streamAppend_ge (by omega), List.length_append]
      congr 1
      omega

/-- A prefix of the front list is a prefix of the stream. -/
theorem streamPrefix_of_prefix {α : Type u} {A L : List α} {ω : Nat → α} (h : A <+: L) :
    StreamPrefix A (L ++ω ω) := by
  intro i hi
  have hL : i < L.length := lt_of_lt_of_le hi h.length_le
  rw [streamAppend_lt hL, h.getElem hi]

/-- The front list, then a prefix of the rest. -/
theorem streamPrefix_append {α : Type u} {L B : List α} {ω : Nat → α}
    (h : StreamPrefix B ω) : StreamPrefix (L ++ B) (L ++ω ω) := by
  intro i hi
  by_cases hL : i < L.length
  · rw [streamAppend_lt hL, List.getElem_append_left hL]
  · rw [List.length_append] at hi
    rw [streamAppend_ge (by omega), List.getElem_append_right (by omega)]
    exact h _ (by omega)

theorem range_flatMap_streamAppend {α : Type u} (ls : List (List α)) (l : Nat → List α) :
    ∀ n, (List.range n).flatMap (ls ++ω l) =
      (ls.take n).flatten ++ (List.range (n - ls.length)).flatMap l
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, range_flatMap_streamAppend ls l n]
    by_cases hn : n < ls.length
    · rw [List.flatMap_singleton, streamAppend_lt hn, List.take_succ_eq_append_getElem hn,
        show n - ls.length = 0 by omega, show n + 1 - ls.length = 0 by omega]
      simp only [List.range_zero, List.flatMap_nil, List.append_nil]
      rw [List.flatten_append, List.flatten_singleton]
    · rw [List.flatMap_singleton, streamAppend_ge (by omega),
        List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        show n + 1 - ls.length = n - ls.length + 1 by omega, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- **A list of segments in front of a concatenation.** -/
theorem streamConcat_append {α : Type u} {ls : List (List α)} {l : Nat → List α}
    {ω : Nat → α} (h : StreamConcat l ω) : StreamConcat (ls ++ω l) (ls.flatten ++ω ω) := by
  obtain ⟨hp, hu⟩ := h
  refine ⟨fun n => ?_, fun N => ?_⟩
  · rw [range_flatMap_streamAppend]
    by_cases hn : n ≤ ls.length
    · rw [show n - ls.length = 0 by omega]
      simp only [List.range_zero, List.flatMap_nil, List.append_nil]
      exact streamPrefix_of_prefix
        ⟨(ls.drop n).flatten, by rw [← List.flatten_append, List.take_append_drop]⟩
    · rw [List.take_of_length_le (by omega)]
      exact streamPrefix_append (hp _)
  · obtain ⟨n, hn⟩ := hu N
    refine ⟨ls.length + n, ?_⟩
    rw [range_flatMap_streamAppend, List.take_of_length_le (by omega),
      show ls.length + n - ls.length = n by omega, List.length_append]
    omega

/-! ## Resolution -/

/-- **A resolved prefix is resolved call by call.** -/
theorem substPre_res {c : sh.ClosedMod} {u : List (Call (sh.E ⊕ₛ sh.self))}
    {q : List (Call sh.E)} (h : SubstPre c u q) :
    ∃ ls : List (List (Call sh.E)), ∃ hlen : ls.length = u.length,
      (∀ i (hi : i < u.length), Res1 c u[i] (ls[i]'(hlen ▸ hi))) ∧ q = ls.flatten := by
  induction h with
  | nil => exact ⟨[], rfl, ⟨fun i hi => by simp at hi, rfl⟩⟩
  | @ext m n _ _ _ ih =>
    obtain ⟨ls, hlen, h, rfl⟩ := ih
    refine ⟨[⟨m, n⟩] :: ls, by simp only [List.length_cons, hlen], fun i hi => ?_, rfl⟩
    rcases i with _ | i
    · exact .ext
    · exact h i (by simp only [List.length_cons] at hi; omega)
  | @int _ _ _ _ _ _ c₁ _ hc _ ih =>
    obtain ⟨ls, hlen, h, rfl⟩ := ih
    refine ⟨c₁ :: ls, by simp only [List.length_cons, hlen], fun i hi => ?_, rfl⟩
    rcases i with _ | i
    · exact .int hc
    · exact h i (by simp only [List.length_cons] at hi; omega)

theorem res1_mono {c c' : sh.ClosedMod} (h : c ≤ c') {x : Call (sh.E ⊕ₛ sh.self)}
    {l : List (Call sh.E)} (hx : Res1 c x l) : Res1 c' x l := by
  cases hx with
  | ext => exact .ext
  | int hc => exact .int (h _ _ _ hc)

theorem substInf_mono {c c' : sh.ClosedMod} (h : c ≤ c') {ν : Nat → Call (sh.E ⊕ₛ sh.self)}
    {ω : Nat → Call sh.E} (hs : SubstInf c ν ω) : SubstInf c' ν ω := by
  obtain ⟨l, hl, hc⟩ := hs
  exact ⟨l, fun i => res1_mono h (hl i), hc⟩

/-- **A resolved prefix in front of a resolved stream.** -/
theorem substInf_append {c : sh.ClosedMod} {u : List (Call (sh.E ⊕ₛ sh.self))}
    {q : List (Call sh.E)} {ν : Nat → Call (sh.E ⊕ₛ sh.self)} {ω : Nat → Call sh.E}
    (hu : SubstPre c u q) (h : SubstInf c ν ω) : SubstInf c (u ++ω ν) (q ++ω ω) := by
  obtain ⟨ls, hlen, hf, rfl⟩ := substPre_res hu
  obtain ⟨l, hl, hc⟩ := h
  refine ⟨ls ++ω l, fun i => ?_, streamConcat_append hc⟩
  by_cases hi : i < u.length
  · rw [streamAppend_lt hi, streamAppend_lt (hlen ▸ hi)]
    exact hf i hi
  · rw [streamAppend_ge (by omega), streamAppend_ge (by omega), hlen]
    exact hl _

/-! ## Concatenations of segments -/

theorem range_flatMap_succ {α : Type u} (l : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap l = (List.range n).flatMap l ++ l n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem range_flatMap_mono {α : Type u} (l : Nat → List α) {m n : Nat} (h : m ≤ n) :
    (List.range m).flatMap l <+: (List.range n).flatMap l := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => rw [range_flatMap_succ]; exact ih.trans (List.prefix_append _ _)

theorem streamPrefix_mono {α : Type u} {A B : List α} {ω : Nat → α} (h : StreamPrefix A ω)
    (hBA : B <+: A) : StreamPrefix B ω := fun i hi =>
  (h i (lt_of_lt_of_le hi hBA.length_le)).trans (hBA.getElem hi).symm

/-- Segments that are nonempty infinitely often have an unbounded concatenation. -/
theorem unbounded_of_frequently {α : Type u} (l : Nat → List α)
    (h : ∀ N, ∃ n, N ≤ n ∧ l n ≠ []) : ∀ M, ∃ n, M ≤ ((List.range n).flatMap l).length
  | 0 => ⟨0, Nat.zero_le _⟩
  | M + 1 => by
    obtain ⟨n, hn⟩ := unbounded_of_frequently l h M
    obtain ⟨n', hn', hne⟩ := h n
    refine ⟨n' + 1, ?_⟩
    rw [range_flatMap_succ, List.length_append]
    have h1 := (range_flatMap_mono l hn').length_le
    have h2 : 0 < (l n').length := List.length_pos_iff.mpr hne
    omega

/-- **An unbounded concatenation of segments is a stream.** -/
theorem exists_streamConcat {α : Type u} (l : Nat → List α)
    (hu : ∀ N, ∃ n, N ≤ ((List.range n).flatMap l).length) : ∃ ν, StreamConcat l ν := by
  choose N hN using fun i => hu (i + 1)
  refine ⟨fun i => ((List.range (N i)).flatMap l)[i]'(by have := hN i; omega),
    fun n i hi => ?_, hu⟩
  dsimp only
  rcases le_total n (N i) with h | h
  · exact ((range_flatMap_mono l h).getElem hi).symm
  · exact (range_flatMap_mono l h).getElem _

theorem streamConcat_map {α β : Type u} (f : α → β) {l : Nat → List α} {ν : Nat → α}
    (h : StreamConcat l ν) : StreamConcat (fun n => (l n).map f) (fun i => f (ν i)) := by
  have hfl : ∀ n, (List.range n).flatMap (fun n => (l n).map f) =
      ((List.range n).flatMap l).map f := fun n => by rw [List.map_flatMap]
  refine ⟨fun n i hi => ?_, fun N => ?_⟩
  · simp only [hfl, List.getElem_map]
    rw [h.1 n i (by simpa [hfl] using hi)]
  · obtain ⟨n, hn⟩ := h.2 N
    exact ⟨n, by rw [hfl, List.length_map]; exact hn⟩

theorem range_flatMap_getElem_rel {α β : Type u} {R : α → β → Prop} {u : Nat → List α}
    {v : Nat → List β} (hlen : ∀ n, (u n).length = (v n).length)
    (hR : ∀ n j (h1 : j < (u n).length) (h2 : j < (v n).length), R (u n)[j] (v n)[j]) :
    ∀ n i (h1 : i < ((List.range n).flatMap u).length)
      (h2 : i < ((List.range n).flatMap v).length),
      R ((List.range n).flatMap u)[i] ((List.range n).flatMap v)[i]
  | 0, i, h1, _ => by simp at h1
  | n + 1, i, h1, h2 => by
    have hl : ((List.range n).flatMap u).length = ((List.range n).flatMap v).length := by
      simp only [List.length_flatMap, hlen]
    simp only [range_flatMap_succ] at h1 h2 ⊢
    by_cases hi : i < ((List.range n).flatMap u).length
    · rw [List.getElem_append_left hi, List.getElem_append_left (hl ▸ hi)]
      exact range_flatMap_getElem_rel hlen hR n i hi _
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp only [List.length_append] at h1 h2
      convert hR n (i - ((List.range n).flatMap u).length) (by omega) (by omega) using 2
      rw [hl]

/-- Concatenations of pointwise related segments of equal lengths are pointwise related. -/
theorem streamConcat_rel {α β : Type u} {R : α → β → Prop} {u : Nat → List α}
    {v : Nat → List β} {ν : Nat → α} {μ : Nat → β} (hu : StreamConcat u ν)
    (hv : StreamConcat v μ) (hlen : ∀ n, (u n).length = (v n).length)
    (hR : ∀ n j (h1 : j < (u n).length) (h2 : j < (v n).length), R (u n)[j] (v n)[j])
    (i : Nat) : R (ν i) (μ i) := by
  obtain ⟨n, hn⟩ := hu.2 (i + 1)
  have hl : ((List.range n).flatMap u).length = ((List.range n).flatMap v).length := by
    simp only [List.length_flatMap, hlen]
  rw [hu.1 n i (by omega), hv.1 n i (by omega)]
  exact range_flatMap_getElem_rel hlen hR n i _ _

/-- **Segment-wise resolution is resolution, one choice per position**: segments `u n`
resolved to `q n`, their concatenations `ν` and `ω`. -/
theorem substInf_of_segments {c : sh.ClosedMod} {u : Nat → List (Call (sh.E ⊕ₛ sh.self))}
    {q : Nat → List (Call sh.E)} {ν : Nat → Call (sh.E ⊕ₛ sh.self)} {ω : Nat → Call sh.E}
    (hs : ∀ n, SubstPre c (u n) (q n)) (hu : StreamConcat u ν) (hq : StreamConcat q ω) :
    SubstInf c ν ω := by
  choose ls hlen hres hfl using fun n => substPre_res (hs n)
  have hlenF : ∀ n, ((List.range n).flatMap ls).length = ((List.range n).flatMap u).length := by
    intro n
    simp only [List.length_flatMap, hlen]
  obtain ⟨L, hL⟩ := exists_streamConcat ls fun N => by
    obtain ⟨n, hn⟩ := hu.2 N
    exact ⟨n, by rw [hlenF]; exact hn⟩
  have hflat : ∀ n, ((List.range n).flatMap ls).flatten = (List.range n).flatMap q := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [range_flatMap_succ, range_flatMap_succ, List.flatten_append, ih, hfl]
  have hmapL : ∀ n, (List.range ((List.range n).flatMap ls).length).flatMap L =
      (List.range n).flatMap q := by
    intro n
    have hm : (List.range ((List.range n).flatMap ls).length).map L =
        (List.range n).flatMap ls := by
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact hL.1 n j h2
    rw [List.flatMap_def, hm, hflat]
  refine ⟨L, fun i => streamConcat_rel (R := fun x y => Res1 c x y) hu hL
    (fun n => (hlen n).symm) (fun n j h1 _ => hres n j h1) i, fun i => ?_, fun N => ?_⟩
  · obtain ⟨n, hn⟩ := hu.2 i
    have hi : i ≤ ((List.range n).flatMap ls).length := by rw [hlenF]; exact hn
    refine streamPrefix_mono (B := (List.range i).flatMap L) ?_ (range_flatMap_mono L hi)
    rw [hmapL]
    exact hq.1 n
  · obtain ⟨n, hn⟩ := hq.2 N
    exact ⟨((List.range n).flatMap ls).length, by rw [hmapL]; exact hn⟩

/-- **A chain of streams, each a segment in front of the next**, is the concatenation of the
segments in front of every later stream. -/
theorem streamAppend_chain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ω w (n + 1)) : ∀ n, w 0 = ((List.range n).flatMap cs) ++ω w n
  | 0 => by simp [streamAppend_nil]
  | n + 1 => by
    rw [streamAppend_chain h n, h n, ← streamAppend_append, ← range_flatMap_succ]

theorem streamConcat_of_chain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ω w (n + 1))
    (hu : ∀ N, ∃ n, N ≤ ((List.range n).flatMap cs).length) : StreamConcat cs (w 0) :=
  ⟨fun n => by rw [streamAppend_chain h n]; exact streamPrefix_of_prefix (List.prefix_refl _), hu⟩

/-! ## `closeInfL` -/

/-- **A resolved productive run of the called function** is a productive run of the closure. -/
theorem mem_closeInfL_of_open {m : sh.OpenMod} {mi : OpenInf sh} {f : sh.F} {s : sh.S}
    {a : sh.A f} {ν : Nat → Call (sh.E ⊕ₛ sh.self)} {ω : Nat → Call sh.E} (hν : ν ∈ mi f s a)
    (h : SubstInf (close m) ν ω) : ω ∈ closeInfL m mi f s a :=
  .inr ⟨⟨f, (a, s)⟩, [], ν, ω, .refl _, hν, h, (streamAppend_nil ω).symm⟩

/-- **An infinite descent chain with a descent in front.** -/
theorem infChain_descends {m : sh.OpenMod} {c : sh.ClosedMod} {x y : sh.self.Op}
    {q : List (Call sh.E)} {ω : Nat → Call sh.E} (hxy : Descends m c x q y)
    (h : InfChain m c y ω) : InfChain m c x (q ++ω ω) := by
  obtain ⟨g, qq, hg, hD, hp, hu⟩ := h
  have hfl : ∀ n, (List.range (n + 1)).flatMap (fun n => match n with | 0 => q | n + 1 => qq n) =
      q ++ (List.range n).flatMap qq := fun n => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  refine ⟨fun n => match n with | 0 => x | n + 1 => g n,
    fun n => match n with | 0 => q | n + 1 => qq n, rfl, fun n => ?_, fun n => ?_, fun N => ?_⟩
  · rcases n with _ | n
    · show Descends m c x q (g 0)
      rw [hg]; exact hxy
    · exact hD n
  · rcases n with _ | n
    · intro i hi
      simp at hi
    · rw [hfl]
      exact streamPrefix_append (hp n)
  · obtain ⟨n, hn⟩ := hu N
    refine ⟨n + 1, ?_⟩
    rw [hfl, List.length_append]
    omega

/-- **`closeInfL` is closed under a descent in front**: a productive run of the callee, after
the import calls of the descent. -/
theorem closeInfL_descends {m : sh.OpenMod} {mi : OpenInf sh} {x y : sh.self.Op}
    {q : List (Call sh.E)} {ω : Nat → Call sh.E} (hxy : Descends m (close m) x q y)
    (h : ω ∈ closeInfL m mi y.1 y.2.2 y.2.1) : q ++ω ω ∈ closeInfL m mi x.1 x.2.2 x.2.1 := by
  rcases h with h | ⟨z, qs, ν, ω', hp, hν, hs, rfl⟩
  · exact .inl (infChain_descends hxy h)
  · exact .inr ⟨z, q ++ qs, ν, ω', .step hxy hp, hν, hs, (streamAppend_append _ _ _).symm⟩

/-- **A finite descent path in front.** -/
theorem closeInfL_descPath {m : sh.OpenMod} {mi : OpenInf sh} {x z : sh.self.Op}
    {qs : List (Call sh.E)} {ω : Nat → Call sh.E} (hp : DescPath m (close m) x qs z)
    (h : ω ∈ closeInfL m mi z.1 z.2.2 z.2.1) : qs ++ω ω ∈ closeInfL m mi x.1 x.2.2 x.2.1 := by
  induction hp with
  | refl => rwa [streamAppend_nil]
  | step hxy _ ih => rw [streamAppend_append]; exact closeInfL_descends hxy (ih h)

/-- With no productive run inside a function, `closeInfL` is `closeInf`. -/
theorem closeInfL_bot (m : sh.OpenMod) (f : sh.F) (s : sh.S) (a : sh.A f) :
    closeInfL m (fun _ _ _ => ∅) f s a = closeInf m f s a := by
  ext ω
  constructor
  · rintro (h | ⟨z, qs, ν, ω', -, hν, -⟩)
    · exact h
    · exact hν.elim
  · exact .inl

end Silmaril.Proofs.Games.Abstract.ModuleInf
