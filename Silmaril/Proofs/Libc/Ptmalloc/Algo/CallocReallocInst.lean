module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.WorldRealloc
public import Silmaril.Libc.Ptmalloc.Refine.Thms

/-!
# ptmalloc algorithm: `calloc` and `realloc` meet the allocator institution

With ghost tokens (`Algo.RefInv`: a well-formed world whose live payloads are the token heap's
blocks), a `calloc` or `realloc` step of the model keeps the refinement invariant and its outcome
is one the institution's loose contract `Silmaril.Libc.allocLoose` allows:

* `Algo.calloc_refines`: `calloc (k, m)` is an `allocate` of `k * m` bytes (and returns 0 when
  `k * m` overflows);
* `Algo.realloc_refines`: `realloc (p, n)` of a token `p`: `n = 0` frees it; otherwise it fails
  keeping the heap, or moves the token to a fresh block of `n` bytes.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

open Silmaril.Libc

variable {C : Config}

/-- **Tokens after an allocation** of `n` bytes returning `p` (`MallocLive`): the tokens follow
and the outcome is an `allocate`. -/
theorem tokens_alloc {w w' : World} {h : Heap} (htok : TokensMatch C w h) (hap : LiveApart (w.live C))
    (hap' : LiveApart (w'.live C)) {n p : Nat} (hML : MallocLive C n p (w.live C) (w'.live C)) :
    TokensMatch C w' (if p = 0 then h else h.add p n) ∧
      allocate h n (.ok (if p = 0 then h else h.add p n) p) := by
  by_cases hp : p = 0
  · subst hp
    simp only [ite_true]
    rcases hML with ⟨-, hperm⟩ | ⟨hp', -⟩
    · refine ⟨⟨fun q m hq => ?_, fun q u hq => htok.2 q u (hperm.subset hq)⟩, .inl rfl⟩
      obtain ⟨u, hu, hmu⟩ := htok.1 q m hq
      exact ⟨u, hperm.symm.subset hu, hmu⟩
    · exact absurd rfl hp'
  simp only [hp, ite_false]
  rcases hML with ⟨hp', -⟩ | ⟨-, -, u, hnu, hperm, hdis⟩
  · exact absurd hp' hp
  have hmem : (p, u) ∈ w'.live C := hperm.symm.subset (List.mem_cons_self ..)
  obtain ⟨-, hu0, hbd⟩ := hap'.2 _ hmem
  refine ⟨⟨fun q m hq => ?_, fun q u' hq => ?_⟩, .inr ⟨p, ⟨hp, by simp only at hbd hu0; omega,
    fun a m ham => ?_⟩, rfl⟩⟩
  · simp only [Heap.add] at hq
    by_cases hqp : q = p
    · subst hqp; simp only [ite_true, Option.some.injEq] at hq; subst hq
      exact ⟨u, hmem, hnu⟩
    · simp only [hqp, ite_false] at hq
      obtain ⟨u', hu', hmu⟩ := htok.1 q m hq
      exact ⟨u', hperm.symm.subset (List.mem_cons_of_mem _ hu'), hmu⟩
  · simp only [Heap.add]
    by_cases hqp : q = p
    · subst hqp; simp
    · simp only [hqp, ite_false]
      rcases List.mem_cons.mp (hperm.subset hq) with he | he
      · simp only [Prod.mk.injEq] at he; exact absurd he.1 hqp
      · exact htok.2 q u' he
  · obtain ⟨u', hm', hmu⟩ := htok.1 a m ham
    have hu'0 := (hap.2 _ hm').2.1
    rcases hdis _ hm' with h1 | h1 <;> simp only at h1 hu0 <;> omega

/-- The tokens other than `p` are the live payloads other than `(p, u)`. -/
theorem tokens_remove {w w' : World} {h : Heap} (htok : TokensMatch C w h) (hap : LiveApart (w.live C))
    {p u : Nat} (hpu : (p, u) ∈ w.live C)
    (hperm : (w'.live C).Perm ((w.live C).erase (p, u))) : TokensMatch C w' (h.remove p) := by
  have huniq := hap.start_unique
  have hnd : (w.live C).Nodup := nodup_of_fst_nodup huniq
  refine ⟨fun q m hq => ?_, fun q u' hq => ?_⟩
  · simp only [Heap.remove] at hq
    by_cases hqp : q = p
    · simp [hqp] at hq
    · simp only [hqp, ite_false] at hq
      obtain ⟨u', hu', hmu⟩ := htok.1 q m hq
      refine ⟨u', hperm.symm.subset (mem_erase_of_ne hu' ?_), hmu⟩
      intro he; simp only [Prod.mk.injEq] at he; exact hqp he.1
  · have hq' := List.mem_of_mem_erase (hperm.subset hq)
    simp only [Heap.remove]
    by_cases hqp : q = p
    · exfalso
      subst hqp
      have hcount : (q, u') = (q, u) := eq_of_fst_nodup huniq hq' hpu rfl
      rw [hcount] at hq
      exact (hnd.mem_erase_iff.mp (hperm.subset hq)).1 rfl
    · simp only [hqp, ite_false]; exact htok.2 q u' hq'

/-- **`calloc` refines the institution's `calloc`.** -/
theorem calloc_refines (hC : C.Ok) {tid : Nat} {w : World} {h : Heap} (hI : RefInv C tid ⟨w, h⟩)
    {k m p : Nat} {w' : World} (hc : (ptmalloc C).calloc w tid k m = .ok (p, w')) :
    RefInv C tid ⟨w', if p = 0 then h else h.add p (k * m)⟩ ∧
      allocLoose h (.calloc k m) (.ok (if p = 0 then h else h.add p (k * m)) p) := by
  obtain ⟨hw, ht, htok⟩ := hI
  obtain ⟨hw', htid, hML⟩ := calloc_wf hC (bodyMalloc_all C) hw ht hc
  obtain ⟨htok', hal⟩ := tokens_alloc htok (liveApart C hC w hw) (liveApart C hC w' hw') hML
  refine ⟨⟨hw', by rw [htid]; exact ht, htok'⟩, ?_⟩
  simp only [allocLoose]
  split
  · rename_i hbig
    have hp0 : p = 0 := by
      unfold Ops.calloc at hc
      simp only [show 2 ^ 63 ≤ k * m by omega, ↓reduceIte] at hc
      injection hc with hc; simp only [Prod.mk.injEq] at hc; exact hc.1.symm
    subst hp0; rfl
  · exact hal

/-- **`realloc` of a token refines the institution's `realloc`**: `n = 0` frees it; otherwise
the heap is kept (0: refused) or the token moves to a fresh block of `n` bytes. -/
theorem realloc_refines (hC : C.Ok) {tid : Nat} {w : World} {h : Heap} (hI : RefInv C tid ⟨w, h⟩)
    {p n q : Nat} {w' : World} (hp : (h p).isSome)
    (hr : (ptmalloc C).realloc w tid p n = .ok (q, w')) :
    RefInv C tid ⟨w', if n = 0 then h.remove p else if q = 0 then h else (h.remove p).add q n⟩ ∧
      allocLoose h (.realloc p n)
        (.ok (if n = 0 then h.remove p else if q = 0 then h else (h.remove p).add q n) q) := by
  obtain ⟨hw, ht, htok⟩ := hI
  obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨u, hpu, -⟩ := htok.1 p m₀ hm₀
  have hap := liveApart C hC w hw
  have hp0 : p ≠ 0 := (hap.2 _ hpu).1
  obtain ⟨hw', htid, hres⟩ := realloc_wf hC (bodyMalloc_all C) (bodyFree C) hw ht hpu hr
  have hap' := liveApart C hC w' hw'
  have ht' : tid ∈ w'.tids := by rw [htid]; exact ht
  simp only [allocLoose, hp0, ↓reduceIte, hp]
  rcases hres with ⟨rfl, rfl, hperm⟩ | ⟨hn, rfl, hperm⟩ | ⟨hn, hq, hML⟩
  · simp only [ite_true]
    exact ⟨⟨hw', ht', tokens_remove htok hap hpu hperm⟩, by simp [allocate]⟩
  · simp only [hn, ite_true, ite_false]
    refine ⟨⟨hw', ht', fun a m ha => ?_, fun a u' ha => htok.2 a u' (hperm.subset ha)⟩, by simp⟩
    obtain ⟨u', hu', hmu⟩ := htok.1 a m ha
    exact ⟨u', hperm.symm.subset hu', hmu⟩
  · simp only [hn, hq, ite_false]
    -- the tokens without `p` are the live payloads without `(p, u)`
    have huniq := hap.start_unique
    have hnd : (w.live C).Nodup := nodup_of_fst_nodup huniq
    have htokR : ∀ a m, (h.remove p) a = some m → ∃ u', (a, u') ∈ (w.live C).erase (p, u) ∧ m ≤ u' := by
      intro a m ha
      simp only [Heap.remove] at ha
      by_cases hap' : a = p
      · simp [hap'] at ha
      · simp only [hap', ite_false] at ha
        obtain ⟨u', hu', hmu⟩ := htok.1 a m ha
        refine ⟨u', mem_erase_of_ne hu' ?_, hmu⟩
        intro he; simp only [Prod.mk.injEq] at he; exact hap' he.1
    rcases hML with ⟨h0, -⟩ | ⟨-, -, u₂, hnu, hperm, hdis⟩
    · exact absurd h0 hq
    have hmem : (q, u₂) ∈ w'.live C := hperm.symm.subset (List.mem_cons_self ..)
    obtain ⟨-, hu0, hbd⟩ := hap'.2 _ hmem
    refine ⟨⟨hw', ht', fun a m ha => ?_, fun a u' ha => ?_⟩, .inr ⟨q, ⟨hq, by simp only at hbd hu0; omega,
      fun a m ham => ?_⟩, rfl⟩⟩
    · simp only [Heap.add] at ha
      by_cases haq : a = q
      · subst haq; simp only [ite_true, Option.some.injEq] at ha; subst ha
        exact ⟨u₂, hmem, hnu⟩
      · simp only [haq, ite_false] at ha
        obtain ⟨u', hu', hmu⟩ := htokR a m ha
        exact ⟨u', hperm.symm.subset (List.mem_cons_of_mem _ hu'), hmu⟩
    · simp only [Heap.add]
      by_cases haq : a = q
      · subst haq; simp
      · simp only [haq, ite_false]
        rcases List.mem_cons.mp (hperm.subset ha) with he | he
        · simp only [Prod.mk.injEq] at he; exact absurd he.1 haq
        · have ⟨hne, he'⟩ := hnd.mem_erase_iff.mp he
          simp only [Heap.remove]
          have hap'' : a ≠ p := fun hh => hne (eq_of_fst_nodup huniq he' hpu hh)
          simp only [hap'', ite_false]
          exact htok.2 a u' he'
    · obtain ⟨u', hm', hmu⟩ := htokR a m ham
      have hu'0 := (hap.2 _ (List.mem_of_mem_erase hm')).2.1
      rcases hdis _ hm' with h1 | h1 <;> simp only at h1 hu0 <;> omega

end Silmaril.Libc.Ptmalloc.Algo
