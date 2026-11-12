module

public import Silmaril.Libc.Ptmalloc.Fastbins.Defs
public import Silmaril.Libc.Ptmalloc.Chunk.Thms

/-!
# ptmalloc component: the fastbins' lemmas

`FastWF.push` (`_int_free`'s fastbin path: the chunk at `a`, not in a fastbin, relabelled
`fast i` and pushed) and `FastWF.pop` (`_int_malloc`'s fastbin path and the tcache refill: the
head of fastbin `i` relabelled to a use that is not a fastbin), stated over the whole chunk list
(`cs`, distinct addresses) and its fast view.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

namespace FastWF

variable {C : Config} {fs : FastSt} {cs : List Chunk} {a : Nat}

theorem exact_all (h : FastWF C fs (Chunk.view Use.isFast cs)) (j : Nat) :
    ListExact (fs.lists j) cs (.fast j) :=
  (ListExact.view_iff (p := Use.isFast) rfl).mp (h.exact j)

theorem of_all (hex : ∀ j, ListExact (fs.lists j) cs (.fast j)) (hn : ∀ j, (fs.lists j).Nodup)
    (hs : ∀ c ∈ cs, ∀ i, c.use = .fast i → C.fidx c.size = i ∧ c.size ≤ C.maxFast ∧ i < C.nFast)
    (hf : (∃ i, fs.lists i ≠ []) → fs.haveFast = true) :
    FastWF C fs (Chunk.view Use.isFast cs) where
  exact j := (ListExact.view_iff (p := Use.isFast) rfl).mpr (hex j)
  nodup := hn
  size c hc := hs c (List.mem_filter.mp hc).1
  flag := hf

/-- **Fastbin push.** -/
theorem push (h : FastWF C fs (Chunk.view Use.isFast cs)) (hn : (cs.map (·.addr)).Nodup)
    {d : Chunk} (hd : d ∈ cs) (hda : d.addr = a) (hdf : d.use.isFast = false) {i : Nat}
    (hsz : C.fidx d.size = i ∧ d.size ≤ C.maxFast ∧ i < C.nFast) :
    FastWF C (fs.push a i) (Chunk.view Use.isFast (cs.map (Chunk.relabelAt a (.fast i)))) := by
  have hv : ∀ j, d.use ≠ .fast j := fun j he => by rw [he] at hdf; cases hdf
  refine of_all (fun j => ?_) (fun j => ?_) ?_ (fun _ => rfl)
  · by_cases hj : j = i
    · subst hj; simp only [FastSt.push, ite_true]
      exact (h.exact_all j).relabel_cons hn ⟨d, hd, hda, rfl⟩ (hv j)
    · simp only [FastSt.push, hj, ite_false]
      exact (h.exact_all j).relabel_keep hn ⟨d, hd, hda, rfl⟩ (fun he => hj (Use.fast.inj he).symm) (hv j)
  · by_cases hj : j = i
    · subst hj; simp only [FastSt.push, ite_true]
      refine List.nodup_cons.mpr ⟨fun ha => ?_, h.nodup j⟩
      obtain ⟨c, hc, hca, hcu⟩ := ((h.exact_all j) a).mp ha
      have := chunk_unique hn hc hd (hca.trans hda.symm); subst this; exact hv j hcu
    · simp only [FastSt.push, hj, ite_false]; exact h.nodup j
  · intro c hc k hk
    rcases mem_map_relabelAt.mp hc with ⟨e, he, hea, rfl⟩ | ⟨-, hc⟩
    · have := chunk_unique hn he hd (hea.trans hda.symm); subst this
      simp only [Use.fast.injEq] at hk; subst hk; exact hsz
    · exact h.size c (List.mem_filter.mpr ⟨hc, by rw [hk]; rfl⟩) k hk

/-- **Fastbin pop.** -/
theorem pop (h : FastWF C fs (Chunk.view Use.isFast cs)) (hn : (cs.map (·.addr)).Nodup) {i : Nat}
    {fs' : FastSt} (hp : fs.pop i = some (a, fs')) {u : Use} (hu : u.isFast = false) :
    FastWF C fs' (Chunk.view Use.isFast (cs.map (Chunk.relabelAt a u))) := by
  unfold FastSt.pop at hp
  split at hp
  · cases hp
  · rename_i b rest hl
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    have hne : ∀ j, u ≠ .fast j := fun j he => by rw [he] at hu; cases hu
    obtain ⟨d, hd, hda, hdu⟩ := ((h.exact_all i) b).mp (by rw [hl]; exact List.mem_cons_self ..)
    refine of_all (fun j => ?_) (fun j => ?_) ?_ ?_
    · by_cases hj : j = i
      · subst hj; simp only [ite_true]
        have := (h.exact_all j).relabel_erase (a := b) (h.nodup j) (hne j)
        rw [hl, List.erase_cons_head] at this; exact this
      · simp only [hj, ite_false]
        exact (h.exact_all j).relabel_keep hn ⟨d, hd, hda, hdu⟩ (hne j) (fun he => hj (Use.fast.inj he).symm)
    · by_cases hj : j = i
      · subst hj; simp only [ite_true]; have := h.nodup j; rw [hl] at this; exact (List.nodup_cons.mp this).2
      · simp only [hj, ite_false]; exact h.nodup j
    · intro c hc k hk
      rcases mem_map_relabelAt.mp hc with ⟨e, he, hea, rfl⟩ | ⟨-, hc⟩
      · exact absurd hk (hne k)
      · exact h.size c (List.mem_filter.mpr ⟨hc, by rw [hk]; rfl⟩) k hk
    · rintro ⟨j, hj⟩
      apply h.flag
      by_cases hji : j = i
      · subst hji; exact ⟨j, by rw [hl]; simp⟩
      · exact ⟨j, by simpa [hji] using hj⟩

end FastWF

end Silmaril.Libc.Ptmalloc
