module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Consolidate

/-!
# ptmalloc algorithm: `_int_malloc` from its paths

`Algo.wfIntMalloc_of`: `Task.algo.wfIntMalloc C (ptmalloc C)` from the three path obligations
`Task.algo.wfMallocFast`, `wfMallocSmall`, `wfMallocLoop` (`Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs`).
The request check (`ENOMEM`, `errno` only) and the large request's `malloc_consolidate` before the
loop (`Algo.wfConsolidate`: the live set up to order) are proved here.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem MallocLive.perm_left {n p : Nat} {live₀ live live' : List (Nat × Nat)} (hp : live.Perm live₀)
    (h : MallocLive C n p live live') : MallocLive C n p live₀ live' := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1, u, hu, h2, h3⟩
  · exact .inl ⟨h0, h1.trans hp⟩
  · exact .inr ⟨h0, h1, u, hu, h2.trans (List.Perm.cons _ hp), fun q hq => h3 q (hp.symm.subset hq)⟩

/-- The view's live set after a change of the arena alone that keeps the lent-out payloads up to
order. -/
theorem live_perm_of_out {l l' : Local} (hth : l'.thread = l.thread) (hsh : l'.shared = l.shared)
    (hout : (l'.av.out C).Perm (l.av.out C)) : (l'.live C).Perm (l.live C) := by
  unfold Local.live; rw [hth, hsh]
  exact List.Perm.append_right _ (hout.filter _)

/-- **The request check**: `ENOMEM` sets `errno` only. -/
theorem setErrno_ok {l : Local} (hw : LocalWF C l) (n : Nat) : MallocOK C n l 0 (setErrno l 12) :=
  ⟨hw.withThread _ hw.tcache (fun h0 => (hw.init h0).2.2), ⟨rfl, rfl, fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
    .inl ⟨rfl, List.Perm.refl _⟩⟩

/-- **`Algo.wfIntMalloc_of`**: `_int_malloc` from its paths. -/
theorem wfIntMalloc_of (C : Config) (hf : Task.algo.wfMallocFast C) (hs : Task.algo.wfMallocSmall C)
    (hl : Task.algo.wfMallocLoop C) : Task.algo.wfIntMalloc C (ptmalloc C) := by
  intro hC l l' n p hw h
  simp only [ptmalloc] at h
  unfold intMalloc at h
  cases hnb : C.checkedRequest2size n with
  | none =>
    simp only [hnb] at h
    injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact setErrno_ok hw n
  | some nb =>
    simp only [hnb] at h
    -- after the fastbin path
    have rest : (if C.inSmallRange nb = true then
          (match mallocSmall C l nb with
            | some r => (pure r : Res (Nat × Local))
            | _ => mallocLoop C nb 3 l)
        else if l.av.fast.haveFast = true then (consolidate C l >>= fun l => mallocLoop C nb 3 l)
          else ((pure l : Res Local) >>= fun l => mallocLoop C nb 3 l))
        = .ok (p, l') → MallocOK C n l p l' := by
      intro h
      split at h
      · rename_i hsm
        split at h
        · rename_i r hr
          injection h with h; subst h
          exact hs hC l l' n nb p hw hnb hsm hr
        · exact hl hC l l' n nb p hw hnb h
      · split at h
        · cases hc : consolidate C l with
          | error e => rw [hc] at h; cases h
          | ok l₁ =>
            rw [hc, ok_bind] at h
            obtain ⟨hw₁, hfp, hout, -⟩ := wfConsolidate C hC l l₁ hw hc
            obtain ⟨hw', hfp', hlive⟩ := hl hC l₁ l' n nb p hw₁ hnb h
            refine ⟨hw', ⟨hfp'.1.trans hfp.1, hfp'.2.1.trans hfp.2.1, fun h => absurd h (by decide),
              fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
              MallocLive.perm_left (live_perm_of_out (hfp.2.2.2.1 rfl) (hfp.2.2.2.2.1 rfl) hout) hlive⟩
        · exact hl hC l l' n nb p hw hnb h
    by_cases hmf : nb ≤ C.maxFast
    · cases hfr : mallocFast C l nb with
      | error e => simp [hmf, hfr] at h; cases h
      | ok o =>
        cases o with
        | none =>
          simp only [hmf, hfr, ite_true] at h
          exact rest h
        | some r =>
          obtain ⟨p₁, l₁⟩ := r
          simp only [hmf, hfr, ite_true] at h
          injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact hf hC l l₁ n nb p₁ hw hnb hmf hfr
    · simp only [hmf, ite_false] at h
      exact rest h

end Silmaril.Libc.Ptmalloc.Algo
