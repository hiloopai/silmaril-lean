module

public import Silmaril.Net.Quic.Reassembly.Defs

/-!
# QUIC stream reassembly: proofs

For `Silmaril.Net.Quic.Reassembly.Thms` (RFC 9000 §2.2). The contiguous prefix is
characterized by coverage alone (`contiguous_spec`), which makes it independent of arrival
order and duplication once all segments are slices of one byte string.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Quic.Reassembly

open Silmaril.Net.Quic

/-! ## `prefixFrom` -/

theorem prefixFrom_isSome {α : Type} (f : Nat → Option α) :
    ∀ k i j, j < (prefixFrom f k i).length → (f (i + j)).isSome := by
  intro k
  induction k with
  | zero => intro i j h; simp [prefixFrom] at h
  | succ k ih =>
    intro i j h
    simp only [prefixFrom] at h
    cases hf : f i with
    | none => simp [hf] at h
    | some b =>
      simp only [hf, List.length_cons] at h
      cases j with
      | zero => simp [hf]
      | succ j =>
        have := ih (i + 1) j (by omega)
        rwa [show i + 1 + j = i + (j + 1) by omega] at this

theorem prefixFrom_stop {α : Type} (f : Nat → Option α) :
    ∀ k i, (prefixFrom f k i).length = k ∨ f (i + (prefixFrom f k i).length) = none := by
  intro k
  induction k with
  | zero => intro i; simp [prefixFrom]
  | succ k ih =>
    intro i
    simp only [prefixFrom]
    cases hf : f i with
    | none => simp [hf]
    | some b =>
      simp only [List.length_cons]
      rcases ih (i + 1) with h | h
      · left; omega
      · right; rwa [show i + 1 + (prefixFrom f k (i + 1)).length =
          i + ((prefixFrom f k (i + 1)).length + 1) by omega] at h

theorem prefixFrom_prefix {α : Type} (f : Nat → Option α) (s : List α)
    (hf : ∀ j b, f j = some b → s[j]? = some b) : ∀ k i, prefixFrom f k i <+: s.drop i := by
  intro k
  induction k with
  | zero => intro i; exact List.nil_prefix
  | succ k ih =>
    intro i
    simp only [prefixFrom]
    cases h : f i with
    | none => exact List.nil_prefix
    | some b =>
      have hs := hf i b h
      have hi : i < s.length := by
        rcases Nat.lt_or_ge i s.length with h' | h'
        · exact h'
        · simp [List.getElem?_eq_none h'] at hs
      rw [List.drop_eq_getElem_cons hi, List.cons_prefix_cons]
      refine ⟨?_, ih (i + 1)⟩
      rw [List.getElem?_eq_getElem hi] at hs
      exact (Option.some.inj hs).symm

theorem prefixFrom_mono {α : Type} (f g : Nat → Option α)
    (hfg : ∀ j b, f j = some b → g j = some b) :
    ∀ k k' i, k ≤ k' → prefixFrom f k i <+: prefixFrom g k' i := by
  intro k
  induction k with
  | zero => intro _ _ _; exact List.nil_prefix
  | succ k ih =>
    intro k' i hk
    obtain ⟨k', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    simp only [prefixFrom]
    cases h : f i with
    | none => exact List.nil_prefix
    | some b =>
      simp only [hfg i b h, List.cons_prefix_cons, true_and]
      exact ih k' (i + 1) (by omega)

/-! ## Bytes and coverage -/

theorem Segment.byteAt_isSome (g : Segment) (i : Nat) : (g.byteAt i).isSome ↔ g.Covers i := by
  simp only [Segment.byteAt, Segment.Covers, Segment.stop]
  split
  · simp only [isSome_getElem?]; omega
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; omega

theorem byteAt_isSome (segs : List Segment) (i : Nat) :
    (byteAt segs i).isSome ↔ Covered segs i := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨g, hg, hgb⟩ := List.exists_of_findSome?_eq_some hb
    exact ⟨g, hg, (Segment.byteAt_isSome g i).1 (by simp [hgb])⟩
  · rintro ⟨g, hg, hc⟩
    cases h : byteAt segs i with
    | some _ => rfl
    | none =>
      have := List.findSome?_eq_none_iff.1 h g hg
      have := (Segment.byteAt_isSome g i).2 hc
      simp_all

theorem slice_getElem? {s : List UInt8} {g : Segment} (hg : g.SliceOf s) {k : Nat} {c : UInt8}
    (h : g.data[k]? = some c) : s[g.offset + k]? = some c := by
  have hd := hg.2
  rw [hd] at h
  simp only [List.getElem?_take, List.getElem?_drop] at h
  split at h
  · exact h
  · cases h

theorem byteAt_slice {s : List UInt8} {segs : List Segment} (hs : ∀ g ∈ segs, g.SliceOf s)
    {i : Nat} {b : UInt8} (h : byteAt segs i = some b) : s[i]? = some b := by
  obtain ⟨g, hg, hgb⟩ := List.exists_of_findSome?_eq_some h
  simp only [Segment.byteAt] at hgb
  split at hgb
  · have := slice_getElem? (hs g hg) hgb
    rwa [show g.offset + (i - g.offset) = i by omega] at this
  · cases hgb

theorem maxStop_ge {segs : List Segment} {g : Segment} (hg : g ∈ segs) : g.stop ≤ maxStop segs := by
  induction segs with
  | nil => cases hg
  | cons h segs ih =>
    simp only [maxStop, List.foldr_cons] at *
    rcases List.mem_cons.1 hg with rfl | hg
    · omega
    · have := ih hg; omega

theorem not_covered_maxStop (segs : List Segment) : ¬ Covered segs (maxStop segs) := by
  rintro ⟨g, hg, -, h⟩
  have := maxStop_ge hg; omega

/-! ## The contiguous prefix -/

theorem contiguous_spec (segs : List Segment) :
    (∀ j < (contiguous segs).length, Covered segs j) ∧
      ¬ Covered segs (contiguous segs).length := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have := prefixFrom_isSome (byteAt segs) (maxStop segs) 0 j hj
    rw [Nat.zero_add] at this
    exact (byteAt_isSome segs j).1 this
  · rcases prefixFrom_stop (byteAt segs) (maxStop segs) 0 with h | h
    · unfold contiguous; rw [h]; exact not_covered_maxStop segs
    · rw [Nat.zero_add] at h
      intro hc
      have := (byteAt_isSome segs _).2 hc
      unfold contiguous at this; rw [h] at this; cases this

theorem covered_le {segs : List Segment} {n : Nat} (h : ∀ j < n, Covered segs j) :
    n ≤ (contiguous segs).length := by
  refine Nat.le_of_not_lt fun hl => ?_
  exact (contiguous_spec segs).2 (h _ hl)

theorem contiguous_prefix {s : List UInt8} {segs : List Segment}
    (hs : ∀ g ∈ segs, g.SliceOf s) : contiguous segs <+: s := by
  have := prefixFrom_prefix (byteAt segs) s (fun _ _ h => byteAt_slice hs h) (maxStop segs) 0
  rwa [List.drop_zero] at this

theorem take_of_prefix {c s : List UInt8} (hp : c <+: s) {n : Nat} (hn : n ≤ c.length) :
    c.take n = s.take n := by
  rw [List.prefix_iff_eq_take.1 hp, List.take_take, Nat.min_eq_left hn]

theorem contiguous_take {s : List UInt8} {segs : List Segment} (hs : ∀ g ∈ segs, g.SliceOf s)
    {n : Nat} (h : ∀ j < n, Covered segs j) :
    (contiguous segs).take n = s.take n ∧ n ≤ (contiguous segs).length :=
  ⟨take_of_prefix (contiguous_prefix hs) (covered_le h), covered_le h⟩

theorem contiguous_length_unique {segs₁ segs₂ : List Segment}
    (hc : ∀ i, Covered segs₁ i ↔ Covered segs₂ i) :
    (contiguous segs₁).length = (contiguous segs₂).length := by
  have h1 := contiguous_spec segs₁
  have h2 := contiguous_spec segs₂
  rcases Nat.lt_trichotomy (contiguous segs₁).length (contiguous segs₂).length with h | h | h
  · exact absurd ((hc _).2 (h2.1 _ h)) h1.2
  · exact h
  · exact absurd ((hc _).1 (h1.1 _ h)) h2.2

theorem contiguous_eq_of_covered {s : List UInt8} {segs₁ segs₂ : List Segment}
    (hs₁ : ∀ g ∈ segs₁, g.SliceOf s) (hs₂ : ∀ g ∈ segs₂, g.SliceOf s)
    (hc : ∀ i, Covered segs₁ i ↔ Covered segs₂ i) : contiguous segs₁ = contiguous segs₂ := by
  rw [List.prefix_iff_eq_take.1 (contiguous_prefix hs₁),
    List.prefix_iff_eq_take.1 (contiguous_prefix hs₂), contiguous_length_unique hc]

theorem contiguous_eq_of_mem {s : List UInt8} {segs₁ segs₂ : List Segment}
    (hs₁ : ∀ g ∈ segs₁, g.SliceOf s) (hm : ∀ g, g ∈ segs₁ ↔ g ∈ segs₂) :
    contiguous segs₁ = contiguous segs₂ :=
  contiguous_eq_of_covered hs₁ (fun g hg => hs₁ g ((hm g).2 hg))
    (fun _ => ⟨fun ⟨g, hg, h⟩ => ⟨g, (hm g).1 hg, h⟩, fun ⟨g, hg, h⟩ => ⟨g, (hm g).2 hg, h⟩⟩)

theorem byteAt_append {segs more : List Segment} {i : Nat} {b : UInt8}
    (h : byteAt segs i = some b) : byteAt (segs ++ more) i = some b := by
  simp only [byteAt, List.findSome?_append] at *; rw [h]; rfl

theorem maxStop_append (segs more : List Segment) : maxStop segs ≤ maxStop (segs ++ more) := by
  induction segs with
  | nil => exact Nat.zero_le _
  | cons g segs ih => simp only [maxStop, List.foldr_cons, List.cons_append] at *; omega

theorem contiguous_append (segs more : List Segment) :
    contiguous segs <+: contiguous (segs ++ more) :=
  prefixFrom_mono _ _ (fun _ _ h => byteAt_append h) _ _ 0 (maxStop_append segs more)

/-! ## Conflicts -/

theorem conflict_slices {s : List UInt8} {segs : List Segment} (hs : ∀ g ∈ segs, g.SliceOf s)
    {g : Segment} (hg : g.SliceOf s) : conflict segs g = false := by
  simp only [conflict, List.any_eq_false, List.mem_range]
  intro k _
  split
  · rename_i b c hb hc
    have h1 := byteAt_slice hs hb
    have h2 := slice_getElem? hg hc
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    simp [h2]
  · simp

/-! ## The buffer -/

open RecvBuffer

/-- What a run has handed out so far is the contiguous prefix up to `delivered`. -/
def Inv (s : List UInt8) (b : RecvBuffer) : Prop :=
  SlicesOf s b ∧ b.delivered ≤ (contiguous b.segs).length

theorem insert_slices {s : List UInt8} {b : RecvBuffer} (strict : Bool) (hs : SlicesOf s b)
    {g : Segment} (hg : g.SliceOf s) :
    b.insert strict g = .ok { b with segs := b.segs ++ [g] } := by
  simp [RecvBuffer.insert, conflict_slices hs hg]

theorem insert_inv {s : List UInt8} {b : RecvBuffer} {g : Segment} (hb : Inv s b)
    (hg : g.SliceOf s) :
    Inv s { b with segs := b.segs ++ [g] } ∧
      (contiguous (b.segs ++ [g])).take b.delivered = (contiguous b.segs).take b.delivered := by
  obtain ⟨hs, hd⟩ := hb
  have hp := contiguous_append b.segs [g]
  refine ⟨⟨fun g' hg' => ?_, ?_⟩, ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hs g' h
    · exact hg
  · exact Nat.le_trans hd hp.length_le
  · exact (take_of_prefix hp hd).symm

theorem read_inv {s : List UInt8} {b : RecvBuffer} (hb : Inv s b) :
    Inv s b.read.2 ∧ (contiguous b.segs).take b.delivered ++ b.read.1 =
      (contiguous b.read.2.segs).take b.read.2.delivered ∧
      b.read.2.delivered = (contiguous b.read.2.segs).length := by
  obtain ⟨hs, hd⟩ := hb
  refine ⟨⟨hs, ?_⟩, ?_, ?_⟩ <;>
    simp only [RecvBuffer.read, Nat.max_eq_right hd, List.take_append_drop, List.take_length,
      Nat.le_refl]

theorem run_spec (strict : Bool) {s : List UInt8} :
    ∀ (es : List Event) (b : RecvBuffer), Inv s b →
      (∀ g, Event.recv g ∈ es → g.SliceOf s) →
      ∃ out b', run strict b es = .ok (out, b') ∧ Inv s b' ∧
        (contiguous b.segs).take b.delivered ++ out =
          (contiguous b'.segs).take b'.delivered ∧
        b'.segs = b.segs ++ es.filterMap Event.segment? ∧
        (es.getLast? = some .read → b'.delivered = (contiguous b'.segs).length) := by
  intro es
  induction es with
  | nil => intro b hb _; exact ⟨[], b, rfl, hb, by simp, by simp, by simp⟩
  | cons e es ih =>
    intro b hb hes
    cases e with
    | recv g =>
      have hg := hes g (by simp)
      obtain ⟨hi, ht⟩ := insert_inv hb hg
      obtain ⟨out, b', hr, hi', ho, hsg, hl⟩ :=
        ih _ hi (fun g' h => hes g' (List.mem_cons_of_mem _ h))
      refine ⟨out, b', ?_, hi', ?_, ?_, ?_⟩
      · simp only [run, insert_slices strict hb.1 hg, Except.bind, hr]
      · simp only at ho; rw [← ho, ht]
      · simp only at hsg; simp [hsg, Event.segment?]
      · intro hlast
        cases es with
        | nil => simp at hlast
        | cons e' es' => exact hl (by simpa using hlast)
    | read =>
      obtain ⟨hi, hrd, hfull⟩ := read_inv hb
      obtain ⟨out, b', hr, hi', ho, hsg, hl⟩ :=
        ih _ hi (fun g' h => hes g' (List.mem_cons_of_mem _ h))
      refine ⟨b.read.1 ++ out, b', ?_, hi', ?_, ?_, ?_⟩
      · simp only [run, hr, Except.map]
      · rw [← List.append_assoc, hrd, ho]
      · rw [hsg]; simp only [RecvBuffer.read]; rfl
      · intro hlast
        cases es with
        | nil =>
          simp only [run, Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨-, rfl⟩ := hr; exact hfull
        | cons e' es' => exact hl (by simpa using hlast)

theorem run_delivers (strict : Bool) {s : List UInt8} (es : List Event)
    (hes : ∀ g, Event.recv g ∈ es → g.SliceOf s) :
    ∃ out b', run strict {} es = .ok (out, b') ∧ out <+: s ∧
      out = (contiguous b'.segs).take b'.delivered ∧
      (es.getLast? = some .read → ∀ n, (∀ j < n, ∃ g, Event.recv g ∈ es ∧ g.Covers j) →
        out.take n = s.take n ∧ n ≤ out.length) := by
  have h0 : Inv s ({} : RecvBuffer) := ⟨fun g hg => (by cases hg), Nat.zero_le _⟩
  obtain ⟨out, b', hr, ⟨hs', -⟩, ho, hsg, hl⟩ := run_spec strict es {} h0 hes
  simp only [List.take_zero, List.nil_append] at ho
  refine ⟨out, b', hr, ?_, ho, fun hlast n hcov => ?_⟩
  · rw [ho]; exact (List.take_prefix _ _).trans (contiguous_prefix hs')
  · have hout : out = contiguous b'.segs := by rw [ho, hl hlast, List.take_length]
    have hc : ∀ j < n, Covered b'.segs j := by
      intro j hj
      obtain ⟨g, hg, hcv⟩ := hcov j hj
      refine ⟨g, ?_, hcv⟩
      rw [hsg]; simp only [List.nil_append, List.mem_filterMap]
      exact ⟨_, hg, rfl⟩
    rw [hout]; exact contiguous_take hs' hc

end Silmaril.Proofs.Net.Quic.Reassembly
