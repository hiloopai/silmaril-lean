module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocTop

/-!
# ptmalloc algorithm: `Task.algo.bodyMalloc` and `totalMalloc` from the paths

`Algo.loop_body`/`loop_total`: `mallocLoop` from the scan, large-bin, bin-map, consolidation and
`sysmalloc` obligations and the proved `use_top` (`Algo.useTop_body`); the fuel (3) suffices since
after one `malloc_consolidate` `have_fastchunks` is clear and nothing in the loop sets it.
`Algo.bodyMalloc_of`, `Algo.totalMalloc_of`: the whole of `intMalloc` (request check, fastbin and
small-bin paths, the large request's consolidation, the loop).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem loop_body (hC : C.Ok) (hscan : Task.algo.mallocScanBody C)
    (hlarge : Task.algo.mallocLargeBody C) (hbm : Task.algo.mallocBinmapBody C)
    (hcons : Task.algo.consolidateBody C) (hsys : Task.algo.sysmallocBody C)
    {n nb : Nat} (hnb : C.checkedRequest2size n = some nb) :
    ∀ fuel l l' p, LocalWF C l → LocalSp C l → l.shared.init = true →
      mallocLoop C nb fuel l = .ok (p, l') → MBody C n l p l'
  | 0, l, l', p, _, _, _, h => by simp [mallocLoop] at h
  | fuel + 1, l, l', p, hw, hsp, hi, h => by
    unfold mallocLoop at h
    dsimp only at h
    cases hs : unsortedScan C nb (tcOn C l (C.tidx nb)) l.av.unsorted.list.length 0 false 0 l with
    | error e => rw [hs] at h; cases h
    | ok rl =>
      obtain ⟨r, l₁⟩ := rl
      have H := hscan hC l l₁ n nb r hw hsp hnb hs
      rw [hs, ok_bind] at h
      cases r with
      | done q =>
        injection h with h; cases h; exact H
      | cached =>
        obtain ⟨q, l₂, hg, hb⟩ := H
        simp only [hg] at h
        injection h with h; cases h; exact hb
      | cont =>
        obtain ⟨hst, hfast⟩ := H
        have hw₁ := hst.1
        have hsp₁ := hst.sp hC hw hsp
        dsimp only at h
        have tail : (match binmapScan C C.nBins (C.binIndex nb + 1) l₁ with
            | (some (v, j), l) => pure (takeFit C l v j nb (C.inSmallRange nb))
            | (none, l) =>
              if l.av.tiles.start ≠ 0 ∧ l.av.tiles.systemMem < l.av.tiles.topSize then do
                Except.error Abort.corruptedTopSize
                if l.av.tiles.start ≠ 0 ∧ nb + C.minSize ≤ l.av.tiles.topSize then
                    pure (l.av.tiles.top + C.hdr, withTiles l (l.av.tiles.useTop nb Use.client))
                  else
                    if l.av.fast.haveFast = true then do
                      let l ← consolidate C l
                      mallocLoop C nb fuel l
                    else sysmalloc C l nb
              else
                if l.av.tiles.start ≠ 0 ∧ nb + C.minSize ≤ l.av.tiles.topSize then
                  pure (l.av.tiles.top + C.hdr, withTiles l (l.av.tiles.useTop nb Use.client))
                else
                  if l.av.fast.haveFast = true then do
                    let l ← consolidate C l
                    mallocLoop C nb fuel l
                  else sysmalloc C l nb : Res (Nat × Local)) = .ok (p, l') → MBody C n l p l' := by
          intro h
          cases hb : binmapScan C C.nBins (C.binIndex nb + 1) l₁ with
          | mk o l₂ =>
            have B := hbm hC l₁ l₂ n nb o hw₁ hsp₁ hnb hb
            rw [hb] at h
            cases o with
            | some vj =>
              obtain ⟨v, j⟩ := vj
              injection h with h
              dsimp only at B
              rw [h] at B
              exact MBody.of_step hC hw hsp hst B
            | none =>
              obtain ⟨hst₂, -⟩ := B
              have hst' := hst.trans hC hw hsp hst₂
              have hw₂ := hst'.1
              have hsp₂ := hst'.sp hC hw hsp
              have hi₂ : l₂.shared.init = true := hst'.2.2.1.init.trans hi
              dsimp only at h
              split at h
              · cases h
              · split at h
                · rename_i htop
                  injection h with h; cases h
                  exact MBody.of_step hC hw hsp hst' (useTop_body hC hw₂ hsp₂ hnb htop.1 htop.2)
                · rename_i htop
                  split at h
                  · cases hc : consolidate C l₂ with
                    | error e => rw [hc] at h; cases h
                    | ok l₃ =>
                      rw [hc, ok_bind] at h
                      obtain ⟨hst₃, -⟩ := hcons hC l₂ l₃ hw₂ hsp₂ hc
                      have hst'' := hst'.trans hC hw hsp hst₃
                      exact MBody.of_step hC hw hsp hst''
                        (loop_body hC hscan hlarge hbm hcons hsys hnb fuel l₃ l' p hst''.1
                          (hst''.sp hC hw hsp) (hst''.2.2.1.init.trans hi) h)
                  · have hlt : topSz l₂.av.tiles < nb + C.minSize := by
                      have := hC.minSize
                      unfold topSz; split
                      · omega
                      · rename_i h0; exact Nat.lt_of_not_le fun hle => htop ⟨h0, hle⟩
                    exact MBody.of_step hC hw hsp hst' (hsys hC l₂ l' n nb p hw₂ hsp₂ hi₂ hnb hlt h)
        split at h
        · rename_i hsm
          split at h
          · rename_i v hv
            injection h with h
            have B := hlarge hC l₁ n nb v hw₁ hsp₁ hnb (by simpa using hsm) hv
            rw [h] at B
            exact MBody.of_step hC hw hsp hst B
          · exact tail h
        · exact tail h

theorem topSz_lt (hC : C.Ok) {ts : TopSt} {nb : Nat} (h : ¬(ts.start ≠ 0 ∧ nb + C.minSize ≤ ts.topSize)) :
    topSz ts < nb + C.minSize := by
  have := hC.minSize
  unfold topSz; split
  · omega
  · rename_i h0; exact Nat.lt_of_not_le fun hle => h ⟨h0, hle⟩

/-- **The main loop does not abort**: at most one consolidation (the fuel is enough). -/
theorem loop_total (hC : C.Ok) (hscan : Task.algo.mallocScanBody C) (hscanT : Task.algo.mallocScanTotal C)
    (hbm : Task.algo.mallocBinmapBody C) (hcons : Task.algo.consolidateBody C)
    (hconsT : Task.algo.consolidateTotal C) (hsysT : Task.algo.sysmallocTotal C)
    {n nb : Nat} (hnb : C.checkedRequest2size n = some nb) :
    ∀ fuel l, LocalWF C l → LocalSp C l → (l.av.fast.haveFast = false ∨ 2 ≤ fuel) → 1 ≤ fuel →
      ∃ r, mallocLoop C nb fuel l = .ok r
  | 0, _, _, _, _, h1 => absurd h1 (by decide)
  | fuel + 1, l, hw, hsp, hfuel, _ => by
    unfold mallocLoop
    dsimp only
    obtain ⟨⟨r, l₁⟩, hs⟩ := hscanT hC l n nb hw hsp hnb
    have H := hscan hC l l₁ n nb r hw hsp hnb hs
    rw [hs, ok_bind]
    cases r with
    | done q => exact ⟨_, rfl⟩
    | cached =>
      obtain ⟨q, l₂, hg, -⟩ := H
      simp only [hg]; exact ⟨_, rfl⟩
    | cont =>
      obtain ⟨hst, hfast⟩ := H
      have hw₁ := hst.1
      have hsp₁ := hst.sp hC hw hsp
      dsimp only
      have tail : ∃ r, (match binmapScan C C.nBins (C.binIndex nb + 1) l₁ with
            | (some (v, j), l) => pure (takeFit C l v j nb (C.inSmallRange nb))
            | (none, l) =>
              if l.av.tiles.start ≠ 0 ∧ l.av.tiles.systemMem < l.av.tiles.topSize then do
                Except.error Abort.corruptedTopSize
                if l.av.tiles.start ≠ 0 ∧ nb + C.minSize ≤ l.av.tiles.topSize then
                    pure (l.av.tiles.top + C.hdr, withTiles l (l.av.tiles.useTop nb Use.client))
                  else
                    if l.av.fast.haveFast = true then do
                      let l ← consolidate C l
                      mallocLoop C nb fuel l
                    else sysmalloc C l nb
              else
                if l.av.tiles.start ≠ 0 ∧ nb + C.minSize ≤ l.av.tiles.topSize then
                  pure (l.av.tiles.top + C.hdr, withTiles l (l.av.tiles.useTop nb Use.client))
                else
                  if l.av.fast.haveFast = true then do
                    let l ← consolidate C l
                    mallocLoop C nb fuel l
                  else sysmalloc C l nb : Res (Nat × Local)) = .ok r := by
        cases hb : binmapScan C C.nBins (C.binIndex nb + 1) l₁ with
        | mk o l₂ =>
          have B := hbm hC l₁ l₂ n nb o hw₁ hsp₁ hnb hb
          cases o with
          | some vj => obtain ⟨v, j⟩ := vj; exact ⟨_, rfl⟩
          | none =>
            obtain ⟨hst₂, hfast₂⟩ := B
            have hst' := hst.trans hC hw hsp hst₂
            have hw₂ := hst'.1
            have hsp₂ := hst'.sp hC hw hsp
            dsimp only
            split
            · rename_i hbad
              exfalso
              have h1 := hw₂.arena.tiles.sysMem
              omega
            · split
              · exact ⟨_, rfl⟩
              · rename_i htop
                split
                · rename_i hhf
                  have hf' : l.av.fast.haveFast = true := by rw [← hfast, ← hfast₂]; exact hhf
                  have hk : 1 ≤ fuel := by
                    rcases hfuel with h | h
                    · rw [hf'] at h; cases h
                    · omega
                  obtain ⟨l₃, hc⟩ := hconsT hC l₂ hw₂ hsp₂
                  obtain ⟨hst₃, hhf₃⟩ := hcons hC l₂ l₃ hw₂ hsp₂ hc
                  rw [hc, ok_bind]
                  exact loop_total hC hscan hscanT hbm hcons hconsT hsysT hnb fuel l₃ hst₃.1
                    (hst₃.sp hC hw₂ hsp₂) (.inl hhf₃) hk
                · exact hsysT hC l₂ n nb hw₂ hsp₂ hnb (topSz_lt hC htop)
      split
      · split
        · exact ⟨_, rfl⟩
        · exact tail
      · exact tail

/-- **`Algo.bodyMalloc_of`**: `Task.algo.bodyMalloc` from the path obligations. -/
theorem bodyMalloc_of (C : Config) (hf : Task.algo.mallocFastBody C) (hsm : Task.algo.mallocSmallBody C)
    (hscan : Task.algo.mallocScanBody C) (hlarge : Task.algo.mallocLargeBody C)
    (hbm : Task.algo.mallocBinmapBody C) (hcons : Task.algo.consolidateBody C)
    (hsys : Task.algo.sysmallocBody C) : Task.algo.bodyMalloc C := by
  intro hC l l' n p hw hsp hi h
  show MBody C n l p l'
  unfold intMalloc at h
  cases hnb : C.checkedRequest2size n with
  | none =>
    simp only [hnb] at h
    injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact setErrno_body hw hsp n
  | some nb =>
    simp only [hnb] at h
    have loop := loop_body hC hscan hlarge hbm hcons hsys hnb
    have rest : (if C.inSmallRange nb = true then
          (match mallocSmall C l nb with
            | some r => (pure r : Res (Nat × Local))
            | _ => mallocLoop C nb 3 l)
        else if l.av.fast.haveFast = true then (consolidate C l >>= fun l => mallocLoop C nb 3 l)
          else ((pure l : Res Local) >>= fun l => mallocLoop C nb 3 l))
        = .ok (p, l') → MBody C n l p l' := by
      intro h
      split at h
      · rename_i hs
        split at h
        · rename_i r hr
          injection h with h; subst h
          exact hsm hC l l' n nb p hw hsp hnb hs hr
        · exact loop 3 l l' p hw hsp hi h
      · split at h
        · cases hc : consolidate C l with
          | error e => rw [hc] at h; cases h
          | ok l₁ =>
            rw [hc, ok_bind] at h
            obtain ⟨hst, -⟩ := hcons hC l l₁ hw hsp hc
            exact MBody.of_step hC hw hsp hst (loop 3 l₁ l' p hst.1 (hst.sp hC hw hsp) (hst.2.2.1.init.trans hi) h)
        · exact loop 3 l l' p hw hsp hi h
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
          exact hf hC l l₁ n nb p₁ hw hsp hnb hmf hfr
    · simp only [hmf, ite_false] at h
      exact rest h

/-- **`Algo.totalMalloc_of`**: `Task.algo.totalMalloc` from the path obligations. -/
theorem totalMalloc_of (C : Config) (hfT : Task.algo.mallocFastTotal C)
    (hscan : Task.algo.mallocScanBody C) (hscanT : Task.algo.mallocScanTotal C)
    (hbm : Task.algo.mallocBinmapBody C) (hcons : Task.algo.consolidateBody C)
    (hconsT : Task.algo.consolidateTotal C) (hsysT : Task.algo.sysmallocTotal C) :
    Task.algo.totalMalloc C := by
  intro hC l hw hsp n
  unfold intMalloc
  cases hnb : C.checkedRequest2size n with
  | none => exact ⟨_, rfl⟩
  | some nb =>
    simp only
    have loop := loop_total hC hscan hscanT hbm hcons hconsT hsysT hnb 3
    have rest : ∃ r, (if C.inSmallRange nb = true then
          (match mallocSmall C l nb with
            | some r => (pure r : Res (Nat × Local))
            | _ => mallocLoop C nb 3 l)
        else if l.av.fast.haveFast = true then (consolidate C l >>= fun l => mallocLoop C nb 3 l)
          else ((pure l : Res Local) >>= fun l => mallocLoop C nb 3 l)) = .ok r := by
      split
      · split
        · exact ⟨_, rfl⟩
        · exact loop l hw hsp (.inr (by decide)) (by decide)
      · split
        · obtain ⟨l₁, hc⟩ := hconsT hC l hw hsp
          obtain ⟨hst, -⟩ := hcons hC l l₁ hw hsp hc
          rw [hc, ok_bind]
          exact loop l₁ hst.1 (hst.sp hC hw hsp) (.inr (by decide)) (by decide)
        · exact loop l hw hsp (.inr (by decide)) (by decide)
    by_cases hmf : nb ≤ C.maxFast
    · obtain ⟨o, hfr⟩ := hfT hC l n nb hw hsp hnb hmf
      cases o with
      | none => simp only [hmf, hfr, ite_true]; exact rest
      | some r => simp only [hmf, hfr, ite_true]; exact ⟨_, rfl⟩
    · simp only [hmf, ite_false]; exact rest

end Silmaril.Libc.Ptmalloc.Algo
