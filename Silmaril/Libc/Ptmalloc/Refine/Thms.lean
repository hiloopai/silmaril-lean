module

public import Silmaril.Libc.Ptmalloc.Refine.Defs

/-!
# ptmalloc: the safety reduction

`Algo.safeMF_of_tasks`: **any** `A : Ops C` whose world-level calls meet `Task.algo.wfWorld`,
`Task.algo.mallocTotal`, `Task.algo.liveApart` and `Task.algo.tidsKept` is a model of the
allocator institution's `safe` sentence on the `malloc`/`free` fragment (`SafeMF`, the fields of
`AbsAlloc.SatOn Frag.mf _ Inv allocLoose`), from any well-formed load-time world without live
blocks. The invariant is `RefInv`: `WorldWF`, the thread exists, and the ghost tokens match the
live set. So the institution-level proof is done once, here, and only the algorithm-level
obligations remain (for `ptmalloc C`, every `C`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

open Silmaril.Libc

/-- The refinement invariant. -/
def RefInv (C : Config) (tid : Nat) (s : TokSt) : Prop :=
  WorldWF C s.w ∧ tid ∈ s.w.tids ∧ TokensMatch C s.w s.h

/-- `free (NULL)` returns the world unchanged, for any `A`. -/
theorem Ops.free_zero {C : Config} (A : Ops C) (w : World) (tid : Nat) : A.free w tid 0 = .ok w := rfl

/-- In an apart live list with positive sizes, two payloads at the same start are equal and the
list has no duplicate start. -/
theorem LiveApart.start_unique {live : List (Nat × Nat)} (h : LiveApart live) :
    (live.map (·.1)).Nodup := by
  obtain ⟨hp, hb⟩ := h
  induction live with
  | nil => exact List.nodup_nil
  | cons q live ih =>
    rw [List.pairwise_cons] at hp
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hq => ?_, ih hp.2 fun r hr => hb r (List.mem_cons_of_mem _ hr)⟩
    obtain ⟨r, hr, hrq⟩ := List.mem_map.mp hq
    have h1 := hp.1 r hr
    have h2 := (hb q (List.mem_cons_self ..)).2.1
    have h3 := (hb r (List.mem_cons_of_mem _ hr)).2.1
    omega

theorem eq_of_fst_nodup {l : List (Nat × Nat)} (hn : (l.map (·.1)).Nodup) {x y : Nat × Nat}
    (hx : x ∈ l) (hy : y ∈ l) (h : x.1 = y.1) : x = y := by
  induction l with
  | nil => cases hx
  | cons e l ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy]
    · subst hx; exact absurd (by rw [h]; exact List.mem_map_of_mem (f := (·.1)) hy) hn.1
    · subst hy; exact absurd (by rw [← h]; exact List.mem_map_of_mem (f := (·.1)) hx) hn.1
    · exact ih hn.2 hx hy

theorem nodup_of_fst_nodup {l : List (Nat × Nat)} (hn : (l.map (·.1)).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons e l ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    exact List.nodup_cons.mpr ⟨fun he => hn.1 (List.mem_map_of_mem he), ih hn.2⟩

theorem mem_erase_of_ne {l : List (Nat × Nat)} {a b : Nat × Nat} (h : b ∈ l) (hne : b ≠ a) :
    b ∈ l.erase a := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    rw [List.erase_cons]
    by_cases hx : x = a
    · subst hx; simp only [beq_self_eq_true, ite_true]
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hne
      · exact h
    · simp only [show (x == a) = false from by simpa using hx, Bool.false_eq_true, ite_false]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- **The safety reduction.** -/
theorem safeMF_of_tasks (C : Config) (A : Ops C) (hC : C.Ok) (tid : Nat) (w0 : World)
    (hwf : Task.algo.wfWorld C A) (htot : Task.algo.mallocTotal C A)
    (hap : Task.algo.liveApart C) (htid : Task.algo.tidsKept C A)
    (h0 : WorldWF C w0) (ht0 : tid ∈ w0.tids) (hl0 : w0.live C = []) :
    SafeMF C A tid w0 (RefInv C tid) where
  init := ⟨h0, ht0, ⟨fun p n h => by simp [Heap.empty] at h, fun p u h => by simp [hl0] at h⟩⟩
  rel := by
    rintro ⟨w, h⟩ c o ⟨hw, ht, htok⟩ hc hs
    cases c with
    | malloc n =>
      obtain ⟨p, w', hm, rfl⟩ := hs
      have ⟨hw', hlive⟩ := (hwf hC w tid hw ht).1 n p w' hm
      by_cases hp : p = 0
      · simp only [hp, ite_true, absOut]; exact .inl rfl
      · simp only [hp, ite_false, absOut]
        refine .inr ⟨p, ?_, rfl⟩
        rcases hlive with ⟨hp0, -⟩ | ⟨-, -, u, hnu, hperm, hdis⟩
        · exact absurd hp0 hp
        have hmem : (p, u) ∈ w'.live C := hperm.symm.subset (List.mem_cons_self ..)
        obtain ⟨-, hu0, hbd⟩ := (hap hC w' hw').2 _ hmem
        refine ⟨hp, by simp only at hbd; omega, fun a m ham => ?_⟩
        obtain ⟨u', hm', hmu⟩ := htok.1 a m ham
        have hu'0 := ((hap hC w hw).2 _ hm').2.1
        rcases hdis _ hm' with h1 | h1 <;> simp only at h1 hu0 <;> omega
    | free p =>
      simp only [absStep] at hs
      by_cases hp : p = 0
      · simp only [hp, ite_true] at hs; subst hs; simp [allocLoose, absOut, hp]
      · simp only [hp, ite_false] at hs
        cases hhp : h p with
        | none => rw [hhp] at hs; subst hs; simp [allocLoose, absOut, hp, hhp]
        | some n =>
          rw [hhp] at hs; obtain ⟨w', -, rfl⟩ := hs
          simp [allocLoose, absOut, hp, hhp]
    | access p => rcases hs with ⟨hown, rfl⟩ | ⟨hown, rfl⟩ <;> simp [allocLoose, absOut, hown]
    | calloc _ _ => cases hc
    | realloc _ _ => cases hc
  inv := by
    rintro ⟨w, h⟩ c ⟨t, ht'⟩ r ⟨hw, ht, htok⟩ hc hs
    cases c with
    | malloc n =>
      obtain ⟨p, w', hm, hst⟩ := hs
      simp only [Option.some.injEq, Prod.mk.injEq, TokSt.mk.injEq] at hst
      obtain ⟨⟨h1, h2⟩, -⟩ := hst
      subst h1; subst h2
      have ⟨hw', hlive⟩ := (hwf hC w tid hw ht).1 n p _ hm
      refine ⟨hw', by rw [(htid hC w tid hw ht).1 n p _ hm]; exact ht, ?_, ?_⟩
      · intro q m hq
        by_cases hp : p = 0
        · simp only [hp, ite_true] at hq
          obtain ⟨u, hu, hmu⟩ := htok.1 q m hq
          rcases hlive with ⟨-, hperm⟩ | ⟨hp', -⟩
          · exact ⟨u, hperm.symm.subset hu, hmu⟩
          · exact absurd hp hp'
        · simp only [hp, ite_false, Heap.add] at hq
          rcases hlive with ⟨hp', -⟩ | ⟨-, -, u, hnu, hperm, -⟩
          · exact absurd hp' hp
          by_cases hqp : q = p
          · subst hqp; simp only [ite_true, Option.some.injEq] at hq; subst hq
            exact ⟨u, hperm.symm.subset (List.mem_cons_self ..), hnu⟩
          · simp only [hqp, ite_false] at hq
            obtain ⟨u', hu', hmu⟩ := htok.1 q m hq
            exact ⟨u', hperm.symm.subset (List.mem_cons_of_mem _ hu'), hmu⟩
      · intro q u hq
        by_cases hp : p = 0
        · simp only [hp, ite_true]
          rcases hlive with ⟨-, hperm⟩ | ⟨hp', -⟩
          · exact htok.2 q u (hperm.subset hq)
          · exact absurd hp hp'
        · simp only [hp, ite_false, Heap.add]
          rcases hlive with ⟨hp', -⟩ | ⟨-, -, u', hnu, hperm, -⟩
          · exact absurd hp' hp
          by_cases hqp : q = p
          · subst hqp; simp
          · simp only [hqp, ite_false]
            rcases List.mem_cons.mp (hperm.subset hq) with he | he
            · simp only [Prod.mk.injEq] at he; exact absurd he.1 hqp
            · exact htok.2 q u he
    | free p =>
      simp only [absStep] at hs
      by_cases hp : p = 0
      · simp only [hp, ite_true, Option.some.injEq, Prod.mk.injEq, TokSt.mk.injEq] at hs
        obtain ⟨⟨h1, h2⟩, -⟩ := hs; subst h1; subst h2; exact ⟨hw, ht, htok⟩
      · simp only [hp, ite_false] at hs
        cases hhp : h p with
        | none => rw [hhp] at hs; cases hs
        | some n =>
          rw [hhp] at hs
          obtain ⟨w', hf, hst⟩ := hs
          simp only [Option.some.injEq, Prod.mk.injEq, TokSt.mk.injEq] at hst
          obtain ⟨⟨h1, h2⟩, -⟩ := hst
          subst h1; subst h2
          obtain ⟨u, hu, hnu⟩ := htok.1 p n hhp
          have ⟨hw', hperm⟩ := (hwf hC w tid hw ht).2 p u _ hu hf
          have huniq := (hap hC w hw).start_unique
          refine ⟨hw', by rw [(htid hC w tid hw ht).2 p _ hf]; exact ht, ?_, ?_⟩
          · intro q m hq
            simp only [Heap.remove] at hq
            by_cases hqp : q = p
            · simp [hqp] at hq
            · simp only [hqp, ite_false] at hq
              obtain ⟨u', hu', hmu⟩ := htok.1 q m hq
              refine ⟨u', hperm.symm.subset (mem_erase_of_ne hu' ?_), hmu⟩
              intro he; simp only [Prod.mk.injEq] at he; exact hqp he.1
          · intro q u' hq
            have hq' := List.mem_of_mem_erase (hperm.subset hq)
            simp only [Heap.remove]
            by_cases hqp : q = p
            · -- the erased payload was the only one at `p`
              exfalso
              subst hqp
              have hcount : (q, u') = (q, u) := eq_of_fst_nodup huniq hq' hu rfl
              rw [hcount] at hq
              have hnd : (w.live C).Nodup := nodup_of_fst_nodup huniq
              exact (hnd.mem_erase_iff.mp (hperm.subset hq)).1 rfl
            · simp only [hqp, ite_false]; exact htok.2 q u' hq'
    | access p =>
      rcases hs with ⟨-, hst⟩ | ⟨-, hst⟩
      · simp only [Option.some.injEq, Prod.mk.injEq, TokSt.mk.injEq] at hst
        obtain ⟨⟨h1, h2⟩, -⟩ := hst; subst h1; subst h2; exact ⟨hw, ht, htok⟩
      · cases hst
    | calloc _ _ => cases hc
    | realloc _ _ => cases hc
  progress := by
    rintro ⟨w, h⟩ c ⟨hw, ht, htok⟩ hc
    cases c with
    | malloc n =>
      obtain ⟨⟨p, w'⟩, hm⟩ := (htot hC w tid hw ht).1 n
      exact ⟨_, p, w', hm, rfl⟩
    | free p =>
      by_cases hp : p = 0
      · exact ⟨some (⟨w, h⟩, 0), by simp [absStep, hp]⟩
      · cases hhp : h p with
        | none => exact ⟨none, by simp [absStep, hp, hhp]⟩
        | some n =>
          obtain ⟨u, hu, -⟩ := htok.1 p n hhp
          obtain ⟨w', hf⟩ := (htot hC w tid hw ht).2 p u hu
          exact ⟨_, by simp only [absStep, hp, ite_false, hhp]; exact ⟨w', hf, rfl⟩⟩
    | access p =>
      by_cases hown : h.Owns p
      · exact ⟨some (⟨w, h⟩, 0), .inl ⟨hown, rfl⟩⟩
      · exact ⟨none, .inr ⟨hown, rfl⟩⟩
    | calloc _ _ => cases hc
    | realloc _ _ => cases hc

end Silmaril.Libc.Ptmalloc.Algo
