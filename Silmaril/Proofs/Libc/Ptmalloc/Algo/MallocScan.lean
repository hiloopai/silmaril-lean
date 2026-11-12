module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocBinmap

/-!
# ptmalloc algorithm: the unsorted scan of `_int_malloc`

**`Algo.mallocScanBody`** (= `Task.algo.mallocScanBody`) and **`Algo.mallocScanTotal`**
(= `Task.algo.mallocScanTotal`), by induction on the scan's fuel with the invariant `ScanInv`:
the view is well formed with its spatial facts, an `MStep` from the start with the fastbins
kept, the tcache there when the request's bin is on, and, once `return_cached` is set, the head
of the request's tcache bin is a client chunk of the arena of `nb` bytes (it was stashed by this
scan; later steps keep it, they only add entries or keep client chunks).

Each turn: the size check cannot fire (a well-formed chunk has at least `MINSIZE` bytes and at
most `system_mem`); the `last_remainder` split is `splitLend`; the exact fit is `relabelLend` or
the stash `stashStep`; a chunk of another size is sorted into its bin (`relabelSort`, with
`BinsWF.pushSmall` or `Algo.binsInsertSorted`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} : (if c then a else b) = b := by
  simp [h]

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} : (if c then a else b) = a := by
  simp [h]

theorem le_sum_of_mem {L : List Nat} {x : Nat} (h : x ∈ L) : x ≤ L.sum := by
  induction L with
  | nil => cases h
  | cons y ys ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- A chunk of a well-formed tiling has at most `system_mem` bytes. -/
theorem size_le_sysMem {ts : TopSt} (ht : TopWF C ts) {c : Chunk} (hc : c ∈ ts.heapChunks) :
    c.size ≤ ts.systemMem := by
  have := le_sum_of_mem (List.mem_map_of_mem (f := (·.size)) hc)
  have := ht.sysMem
  omega

theorem binIndex_range (hC : C.Ok) {size : Nat} (h : 32 ≤ size) :
    2 ≤ C.binIndex size ∧ C.binIndex size ≤ C.lastBin ∧
      (C.inSmallRange size = true → C.binIndex size < C.nSmallBins) := by
  obtain ⟨hb1, hb2, hb3⟩ := hC.bins
  have h16 := hC.align
  unfold Config.binIndex Config.inSmallRange Config.lastBin
  rw [hb3, hb2, h16, hb1]
  by_cases hs : size < 64 * 16
  · simp only [hs, decide_true, ite_true, forall_const]
    omega
  · simp only [hs, decide_false, Bool.false_eq_true, ite_false, false_implies, and_true]
    unfold Config.largeIndex
    repeat' split
    all_goals omega

/-- **The scan's invariant** at a state `l` reached from `l0`, with `return_cached` `rc`. -/
structure ScanInv (C : Config) (nb : Nat) (tcNb : Bool) (l0 l : Local) (rc : Bool) : Prop where
  wf : LocalWF C l
  sp : LocalSp C l
  step : MStep C l0 l
  fast : l.av.fast = l0.av.fast
  tc : tcNb = true → (∃ tc, l.thread.tcache = some tc) ∧ C.tidx nb < C.tcacheBins
  cached : rc = true → ∃ tc e rest, l.thread.tcache = some tc ∧ tc.bins (C.tidx nb) = e :: rest ∧
    ∃ c ∈ l.av.chunks, c.addr = e.1 ∧ c.size = e.2 ∧ c.use = .client ∧ e.2 = nb

/-- What a scan run from `l0` ends with. -/
def ScanOK (C : Config) (n nb : Nat) (l0 : Local) : ScanRes × Local → Prop
  | (.done p, l') => MBody C n l0 p l'
  | (.cached, l') => ∃ p l'', l'.tcacheGet C (C.tidx nb) = some (p, l'') ∧ MBody C n l0 p l''
  | (.cont, l') => MStep C l0 l' ∧ l'.av.fast = l0.av.fast

/-- Stopping (`return_cached` or going on). -/
theorem ScanInv.stop (hC : C.Ok) {n nb : Nat} (hnb : C.checkedRequest2size n = some nb) {tcNb : Bool}
    {l0 l : Local} {rc : Bool} (hw0 : LocalWF C l0) (hs0 : LocalSp C l0)
    (h : ScanInv C nb tcNb l0 l rc) : ScanOK C n nb l0 ((if rc then .cached else .cont), l) := by
  cases rc with
  | false => exact ⟨h.step, h.fast⟩
  | true =>
    obtain ⟨tc, e, rest, htc, hb, c, hc, h1, h2, h3, h4⟩ := h.cached rfl
    obtain ⟨hn8, -, -⟩ := request2size_spec hC hnb
    obtain ⟨p, l'', hg, hbody⟩ := getLend (n := n) hC h.wf h.sp htc hb hc h1 h2 h3 (by omega)
    exact ⟨p, l'', hg, MBody.of_step hC hw0 hs0 h.step hbody⟩

/-- An arena-only internal step keeps the invariant. -/
theorem ScanInv.arena (hC : C.Ok) {nb : Nat} {tcNb : Bool} {l0 l l' : Local} {rc : Bool}
    (hw0 : LocalWF C l0) (hs0 : LocalSp C l0) (h : ScanInv C nb tcNb l0 l rc) (hst : MStep C l l')
    (hth : l'.thread = l.thread) (hf : l'.av.fast = l.av.fast) : ScanInv C nb tcNb l0 l' rc where
  wf := hst.1
  sp := MStep.sp hC h.wf h.sp hst
  step := MStep.trans hC hw0 hs0 h.step hst
  fast := hf.trans h.fast
  tc htn := by rw [hth]; exact h.tc htn
  cached hrc := by
    obtain ⟨tc, e, rest, htc, hb, c, hc, h1, h2, h3, h4⟩ := h.cached hrc
    exact ⟨tc, e, rest, by rw [hth]; exact htc, hb, c, hst.2.2.1.clients c hc h3 (by simp), h1, h2, h3, h4⟩

/-- **The unsorted scan** from a state with the invariant: it does not abort, and what it ends
with is `ScanOK`. -/
theorem scan_spec (hC : C.Ok) {n nb : Nat} (hnb : C.checkedRequest2size n = some nb) {tcNb : Bool}
    {l0 : Local} (hw0 : LocalWF C l0) (hs0 : LocalSp C l0) :
    ∀ fuel iters rc cnt l, ScanInv C nb tcNb l0 l rc →
      ∃ r, unsortedScan C nb tcNb fuel iters rc cnt l = .ok r ∧ ScanOK C n nb l0 r := by
  obtain ⟨hn8, hnba, hnbm⟩ := request2size_spec hC hnb
  have h8 := hC.sizeSz; have h16 := hC.align; have h32 := hC.minSize
  intro fuel
  induction fuel with
  | zero => intro iters rc cnt l h; exact ⟨_, rfl, h.stop hC hnb hw0 hs0⟩
  | succ fuel ih =>
    intro iters rc cnt l h
    have hw := h.wf; have hs := h.sp
    have ht := hw.arena.tiles; have hn' := ht.nodup
    unfold unsortedScan
    rcases hlast : l.av.unsorted.list.getLast? with _ | v
    · exact ⟨_, rfl, h.stop hC hnb hw0 hs0⟩
    simp only
    have hvm : v ∈ l.av.unsorted.list := List.mem_of_getLast? hlast
    obtain ⟨d, hd, rfl, hdu⟩ := ((hw.arena.unsorted.exact_all) v).mp hvm
    have hds : l.av.tiles.sizeAt d.addr = d.size := TopSt.sizeAt_of_mem hn' hd
    rw [hds]
    have hdmin := (ht.sizes d hd).2
    have hcheck : ¬ (d.size ≤ C.hdr ∨ l.av.tiles.systemMem < d.size) := by
      have := size_le_sysMem ht hd; unfold Config.hdr; omega
    rw [ite_neg' hcheck]
    have hfree : d.use.tagFree = true := by rw [hdu]; rfl
    have hsortedv : Chunk.view Use.isSorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)) =
        l.av.sortedView := by
      show Chunk.view _ (l.av.tiles.heapChunks.map _) = _
      rw [← TopSt.heapChunks_relabel]
      exact view_relabel_of hn' hd rfl (by rw [hdu]; rfl) rfl
    have hbins0 : BinsWF C l.av.bins (Chunk.view Use.isSorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)))
        l.av.tiles.sizeAt := by rw [hsortedv]; exact hw.arena.bins
    by_cases hlr : C.inSmallRange nb = true ∧ l.av.unsorted.list.length = 1 ∧ d.addr = l.av.unsorted.lastRem ∧
        nb + C.minSize < d.size
    · rw [ite_pos' hlr]
      refine ⟨_, rfl, ?_⟩
      obtain ⟨-, hlen, -, hlt⟩ := hlr
      have hlist : l.av.unsorted.list = [d.addr] := by
        match hl : l.av.unsorted.list, hlen with
        | [x], _ => rw [hl] at hlast; simp at hlast; rw [hlast]
      have hb := ht.bound d hd
      have := splitLend (n := n) hC hw hs hd hfree hnba hnbm (by omega) hn8 l.av.bins hbins0
        { list := [d.addr + nb], lastRem := d.addr + nb } (by simp [hlist]) (by simp only; omega)
      exact MBody.of_step hC hw0 hs0 h.step this
    rw [ite_neg' hlr]
    have htl : l.av.unsorted.takeLast =
        some (d.addr, { l.av.unsorted with list := l.av.unsorted.list.dropLast }) := by
      simp [UnsortedSt.takeLast, hlast]
    have htake : unsortedTake l = some (d.addr, { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .internal, unsorted := { l.av.unsorted with list := l.av.unsorted.list.dropLast } } }) := by
      simp [unsortedTake, htl]
    rw [htake]
    simp only
    have hus₁ := hw.arena.unsorted.takeLast htl (u := .internal) (by simp)
    have hrel : ∀ u : Use, Local.relabel { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .internal, unsorted := { l.av.unsorted with list := l.av.unsorted.list.dropLast } } } d.addr u =
        { l with av := { l.av with tiles := l.av.tiles.relabel d.addr u, unsorted := { l.av.unsorted with list := l.av.unsorted.list.dropLast } } } := by
      intro u; simp only [Local.relabel, TopSt.relabel_twice]
    by_cases hsz : d.size = nb
    · rw [ite_pos' hsz]
      split
      · -- the stash
        rename_i hst
        obtain ⟨⟨tc, htc⟩, htb⟩ := h.tc hst.1
        have hroom : (tc.bins (C.tidx nb)).length < C.tcacheCount := by
          have := hst.2; simpa [tcCount, htc] using this
        rw [hrel]
        have hstep := stashStep hC hw hs hd hdu _ hus₁ htc htb (by rw [hsz]) hroom
        have hput : tcPut { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := { l.av.unsorted with list := l.av.unsorted.list.dropLast } } } (d.addr, d.size) (C.tidx nb) =
            { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := { l.av.unsorted with list := l.av.unsorted.list.dropLast } }, thread := { l.thread with tcache := some (tc.put (d.addr, d.size) (C.tidx nb)) } } := by
          simp [tcPut, Local.tcachePut, htc]
        rw [hput] at hstep ⊢
        refine ih iters true cnt _ ⟨hstep.1, MStep.sp hC hw hs hstep, MStep.trans hC hw0 hs0 h.step hstep,
          h.fast, fun _ => ⟨⟨_, rfl⟩, htb⟩, fun _ => ⟨_, (d.addr, d.size), tc.bins (C.tidx nb), rfl,
            by simp [TcacheSt.put], { d with use := .client }, ?_, rfl, rfl, rfl, hsz⟩⟩
        show _ ∈ (l.av.tiles.relabel d.addr .client).heapChunks
        rw [TopSt.heapChunks_relabel]; exact List.mem_map.mpr ⟨d, hd, Chunk.relabelAt_of_eq rfl⟩
      · -- the exact fit, lent out
        refine ⟨_, rfl, ?_⟩
        show MBody C n l0 (d.addr + C.hdr) _
        rw [hrel]
        exact MBody.of_step hC hw0 hs0 h.step
          (relabelLend (n := n) hC hw hs hd hfree (by omega) l.av.bins _ hbins0 hus₁)
    rw [ite_neg' hsz]
    obtain ⟨hi2, hil, hism⟩ := binIndex_range hC (by omega : 32 ≤ d.size)
    have hcs : ((l.av.chunks.map (Chunk.relabelAt d.addr .internal)).map (·.addr)).Nodup := by
      rw [map_relabelAt_addr]; exact hn'
    have hdcs : { d with use := .internal } ∈ l.av.chunks.map (Chunk.relabelAt d.addr .internal) :=
      List.mem_map.mpr ⟨d, hd, Chunk.relabelAt_of_eq rfl⟩
    have key : ∃ l₂ : Local, (if C.inSmallRange d.size = true then
        Local.binPushFront { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .internal, unsorted := { l.av.unsorted with list := l.av.unsorted.list.dropLast } } } d.addr (C.binIndex d.size)
        else largeInsert { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .internal, unsorted := { l.av.unsorted with list := l.av.unsorted.list.dropLast } } } d.addr (C.binIndex d.size)) = l₂ ∧
        MStep C l l₂ ∧ l₂.thread = l.thread ∧ l₂.av.fast = l.av.fast := by
      cases hsm : C.inSmallRange d.size
      · simp only [Bool.false_eq_true, ite_false]
        have hb := binsInsertSorted C l.av.bins _ l.av.tiles.sizeAt d.addr (C.binIndex d.size) _
          hbins0 hcs hdcs rfl rfl hds hi2 hil rfl
        rw [map_relabelAt_twice] at hb
        refine ⟨_, rfl, ?_, rfl, rfl⟩
        have := relabelSort hw hs hd hdu hi2 _ _ hb hus₁
        simpa [largeInsert, TopSt.relabel_twice, TopSt.sizeAt_relabel] using this
      · simp only [ite_true]
        have hb := hbins0.pushSmall hcs hdcs rfl rfl ⟨hi2, hil, rfl⟩ (hism hsm)
        rw [map_relabelAt_twice] at hb
        refine ⟨_, rfl, ?_, rfl, rfl⟩
        have := relabelSort hw hs hd hdu hi2 _ _ hb hus₁
        simpa [Local.binPushFront, TopSt.relabel_twice] using this
    obtain ⟨l₂, hl₂, hst, hth, hf⟩ := key
    simp only [hl₂]
    have hinv := h.arena hC hw0 hs0 hst hth hf
    split
    · rename_i hc
      obtain ⟨hrc, -⟩ := hc
      subst hrc
      exact ⟨_, rfl, hinv.stop hC hnb hw0 hs0⟩
    split
    · exact ⟨_, rfl, hinv.stop hC hnb hw0 hs0⟩
    exact ih (iters + 1) rc (cnt + 1) l₂ hinv

theorem MStep.refl' {l : Local} (hw : LocalWF C l) (hs : LocalSp C l) : MStep C l l :=
  ⟨hw, List.Perm.refl _, Frame.of_eq rfl rfl rfl rfl rfl rfl rfl hs.covered,
    fun tc _ _ ht he _ => ⟨tc, ht, he⟩, id⟩

theorem scanInv_init {l : Local} (hw : LocalWF C l) (hs : LocalSp C l) (nb : Nat) :
    ScanInv C nb (tcOn C l (C.tidx nb)) l l false where
  wf := hw
  sp := hs
  step := MStep.refl' hw hs
  fast := rfl
  tc h := by
    unfold tcOn at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
    exact h
  cached h := by cases h

/-- **`Algo.mallocScanBody`**: `Task.algo.mallocScanBody`. -/
theorem mallocScanBody (C : Config) : Task.algo.mallocScanBody C := by
  intro hC l l' n nb r hw hs hnb hscan
  obtain ⟨r', hr', hok⟩ := scan_spec (n := n) hC hnb hw hs _ 0 false 0 l (scanInv_init hw hs nb)
  rw [hscan] at hr'
  cases hr'
  cases r <;> exact hok

/-- **`Algo.mallocScanTotal`**: `Task.algo.mallocScanTotal`. -/
theorem mallocScanTotal (C : Config) : Task.algo.mallocScanTotal C := by
  intro hC l n nb hw hs hnb
  obtain ⟨r', hr', -⟩ := scan_spec (n := n) hC hnb hw hs _ 0 false 0 l (scanInv_init hw hs nb)
  exact ⟨r', hr'⟩

end Silmaril.Libc.Ptmalloc.Algo
