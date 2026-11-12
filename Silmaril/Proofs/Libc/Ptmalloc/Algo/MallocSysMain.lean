module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSys
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.FreeBody
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocCons

/-!
# ptmalloc algorithm: `sysmalloc` on the main arena

`Algo.sysMainBody : Task.algo.sysMainBody C`, `Algo.sysMainTotal : Task.algo.sysMainTotal C`.

`sysmallocMain` is cut in two (`sysmallocMain_cut`): the memory got (`mainGot`: the `sbrk`, else
the `mmap` fallback; `mainGot_none`, `mainGot_some` with the fresh range as a `Grant`) and the rest
(`mainTail`). The rest is, case by case (`tail_cases`):
* the **contiguous extension** of top (`tail_ext`, `ext_step`: an `MStep`);
* a **new top**, non-contiguous (`tail_nc`) or the first `sbrk` (`tail_c`: no heap yet, so the
  front alignment and the end correction are both 0 and the second `sbrk (0)` asks nothing), with
  the old segment closed (`closeSeg_spec`, `newtop`): nothing to free (an `MStep`), or the old top
  a fresh client chunk (`Closed`) that `_int_free` gets (`Algo.bodyFree`, `Algo.totalFree`;
  `closed_step`, `Frame.trans_one`).
`glibc`'s "break adjusted to free malloc space" never fires: a contiguous main arena's break is the
top's end (`MainBrk`), and the model's `sbrk` returns the break (no foreign `sbrk`). The new
system memory stays a word by `LocalWF.sysMain` (the main arena's `system_mem` and the `mmap`ed
chunks' bytes are kernel bytes, at most `userTop`).

Hence `Algo.bodyMalloc_heap`, `Algo.totalMalloc_heap`: `Task.algo.bodyMalloc`/`totalMalloc`
conditional only on `sysmalloc`'s non-main part.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-! ## The kernel's answers to `sbrk` -/

variable {C}

theorem sbrk_some {k k' : KernelSt} {incr b : Nat} (h : k.sbrk incr = (some b, k')) :
    b = k.brk ∧ k'.brkStart = k.brkStart ∧ k'.maps = k.maps ∧ k'.brk = k.brk + incr ∧
      (k.brkStart ≤ k.brk → k'.total = k.total + incr) ∧
      (0 < incr → k.brk + incr ≤ KernelSt.userTop ∧ k.Free k.brk incr ∧ k'.total ≤ KernelSt.userTop) := by
  unfold KernelSt.sbrk at h
  split at h
  · rename_i h0; subst h0; cases h; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun h => absurd h (by omega)⟩
  · unfold KernelSt.ask at h
    cases ha : k.oracle.answer k.asked with
    | refuse => rw [ha] at h; simp at h
    | ok v =>
      rw [ha] at h; simp only at h
      split at h
      · rename_i hc
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, rfl, rfl, rfl, ?_, fun _ => ⟨hc.1, hc.2.1, ?_⟩⟩
        · intro hle; unfold KernelSt.total; simp only; omega
        · have := hc.2.2; unfold KernelSt.total at *; simp only at *; omega
      · simp at h

theorem sbrk_none {k k' : KernelSt} {incr : Nat} (h : k.sbrk incr = (none, k')) :
    k'.brkStart = k.brkStart ∧ k'.brk = k.brk ∧ k'.maps = k.maps := by
  unfold KernelSt.sbrk at h
  split at h
  · cases h
  · unfold KernelSt.ask at h
    cases ha : k.oracle.answer k.asked with
    | refuse => rw [ha] at h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
    | ok v =>
      rw [ha] at h; simp only at h
      split at h
      · simp at h
      · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩

theorem sbrk_zero (k : KernelSt) : k.sbrk 0 = (some k.brk, k) := by
  unfold KernelSt.sbrk; simp

/-- The bytes an `sbrk` grants are no byte of the process's memory. -/
theorem sbrk_away {k : KernelSt} {incr : Nat} (hi : 0 < incr) (hf : k.Free k.brk incr) {r : Nat × Nat}
    (hr : k.Covers r) (h0 : 0 < r.2) : r.1 + r.2 ≤ k.brk ∨ k.brk + incr ≤ r.1 := by
  by_cases h1 : r.1 + r.2 ≤ k.brk
  · exact .inl h1
  by_cases h2 : k.brk + incr ≤ r.1
  · exact .inr h2
  exfalso
  have key : ∀ x, r.1 ≤ x → x < r.1 + r.2 → k.brk ≤ x → x < k.brk + incr → False := by
    intro x hx1 hx2 hx3 hx4
    rcases hr x hx1 hx2 with ⟨-, hb2⟩ | ⟨m, hm, hm1, hm2⟩
    · omega
    · have := hf m hm; omega
  by_cases h3 : r.1 ≤ k.brk
  · exact key k.brk h3 (by omega) (Nat.le_refl _) (by omega)
  · exact key r.1 (Nat.le_refl _) (by omega) (by omega) (by omega)

theorem has_mono_le {k k' : KernelSt} (h1 : k'.brkStart = k.brkStart) (h2 : k.brk ≤ k'.brk)
    (h3 : ∀ m ∈ k.maps, m ∈ k'.maps) {x : Nat} (h : k.Has x) : k'.Has x := by
  rcases h with ⟨a, b⟩ | ⟨m, hm, hm1, hm2⟩
  · exact .inl ⟨by rw [h1]; exact a, by omega⟩
  · exact .inr ⟨m, h3 m hm, hm1, hm2⟩

/-! ## `sysmallocMain`, cut in two -/

variable (C)

/-- The first `sbrk`'s size. -/
def mainSize (l : Local) (nb : Nat) : Nat :=
  alignUp (if !l.av.tiles.noncontig then nb + C.topPad + C.minSize - topSz l.av.tiles
    else nb + C.topPad + C.minSize) C.page

/-- The `mmap` fallback's size. -/
def mainFs (l : Local) (nb : Nat) : Nat :=
  max (if !l.av.tiles.noncontig then alignUp (mainSize C l nb + topSz l.av.tiles) C.page
    else mainSize C l nb) C.mmapAsMorecore

/-- `sysmallocMain`'s first part: the memory got (`sbrk`, else the `mmap` fallback). -/
def mainGot (l : Local) (nb : Nat) : Option (Nat × Option Nat × Nat) × Local :=
  let (brk, k) := l.kernel.sbrk (mainSize C l nb)
  match brk with
  | some b => (some (b, none, mainSize C l nb), { l with kernel := k })
  | none =>
    if mainFs C l nb ≤ nb then (none, { l with kernel := k }) else
    match k.mmap C.page (mainFs C l nb) with
    | (none, k') => (none, { l with kernel := k' })
    | (some m, k') =>
      (some (m, some (m + mainFs C l nb), mainFs C l nb),
        { l with kernel := k', av := { l.av with tiles := { l.av.tiles with noncontig := true } } })

/-- `sysmallocMain`'s second part, on the memory got. -/
def mainTail (l : Local) (nb oldSize oldEnd b : Nat) (snd : Option Nat) (size : Nat) :
    Res (Nat × Local) := do
  let mp := l.shared.mm.mp
  let l := { l with shared := { l.shared with mm := { l.shared.mm with
    mp := { mp with sbrkBase := if mp.sbrkBase = 0 then b else mp.sbrkBase } } } }
  let ts := l.av.tiles
  let ts := { ts with systemMem := ts.systemMem + size }
  let l := withTiles l ts
  if ts.start ≠ 0 ∧ b = oldEnd ∧ snd = none then
    return sysCarve C (withTiles l { ts with topSize := size + oldSize }) nb
  let contig := !ts.noncontig
  if contig ∧ oldSize ≠ 0 ∧ b < oldEnd then .error .breakAdjusted
  let (aligned, snd', corr, l) : Nat × Nat × Nat × Local :=
    if contig then
      let gap := if oldSize ≠ 0 then b - oldEnd else 0
      let l := withTiles l { l.av.tiles with systemMem := l.av.tiles.systemMem + gap }
      let front := (b + C.hdr) % C.align
      let c0 := if front > 0 then C.align - front else 0
      let c1 := c0 + oldSize
      let e := b + size + c1
      let c2 := c1 + (alignUp e C.page - e)
      match l.kernel.sbrk c2 with
      | (some s, k) => (b + c0, s, c2, { l with kernel := k })
      | (none, k) => (b + c0, k.brk, 0, { l with kernel := k })
    else (b, snd.getD l.kernel.brk, 0, l)
  let newSize := snd' - aligned + corr
  let l := withTiles l { l.av.tiles with systemMem := l.av.tiles.systemMem + corr }
  let (freed, l) := closeSegment C l aligned newSize true
  let l ← freeOldTop C l freed
  return sysCarve C l nb

/-- **`sysmallocMain` cut in two**: the memory got, then the rest. -/
theorem sysmallocMain_cut {l : Local} {nb : Nat} {r : Nat × Local} (h : sysmallocMain C l nb = .ok r) :
    ((mainGot C l nb).1 = none ∧ sysCarve C (mainGot C l nb).2 nb = r) ∨
    ∃ b snd size, (mainGot C l nb).1 = some (b, snd, size) ∧
      mainTail C (mainGot C l nb).2 nb (topSz l.av.tiles) (l.av.tiles.top + topSz l.av.tiles) b snd size = .ok r := by
  unfold sysmallocMain at h
  dsimp only at h
  split at h
  · rename_i heq
    exact .inl ⟨heq, by injection h⟩
  · rename_i b snd size heq
    exact .inr ⟨b, snd, size, heq, h⟩

theorem sysmallocMain_of {l : Local} {nb : Nat}
    (h1 : (mainGot C l nb).1 = none → ∃ r, sysmallocMain C l nb = .ok r)
    (h2 : ∀ b snd size, (mainGot C l nb).1 = some (b, snd, size) →
      ∃ r, mainTail C (mainGot C l nb).2 nb (topSz l.av.tiles) (l.av.tiles.top + topSz l.av.tiles) b snd size = .ok r) :
    ∃ r, sysmallocMain C l nb = .ok r := by
  cases hg : (mainGot C l nb).1 with
  | none => exact h1 hg
  | some v =>
    obtain ⟨b, snd, size⟩ := v
    obtain ⟨r, hr⟩ := h2 b snd size hg
    refine ⟨r, ?_⟩
    unfold sysmallocMain
    dsimp only
    split
    · rename_i heq
      have : (mainGot C l nb).1 = none := heq
      rw [hg] at this; cases this
    · rename_i b' snd' size' heq
      have : (mainGot C l nb).1 = some (b', snd', size') := heq
      rw [hg] at this
      injection this with this
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl, rfl⟩ := this
      exact hr

/-! ## The memory got -/

variable {C}

/-- **Fresh memory from the kernel** for the main arena: `[b, b + size)` was no byte of the
process's and now is, the kernel's total grew by `size` and stays in the user address space. -/
structure Grant (C : Config) (l : Local) (k : KernelSt) (b size : Nat) : Prop where
  brkStart : k.brkStart = l.kernel.brkStart
  brkLe : l.kernel.brk ≤ k.brk
  maps : ∀ m ∈ l.kernel.maps, m ∈ k.maps
  total : k.total = l.kernel.total + size
  totalTop : k.total ≤ KernelSt.userTop
  fresh : ∀ r, 0 < r.2 → l.kernel.Covers r → r.1 + r.2 ≤ b ∨ b + size ≤ r.1
  covers : ∀ x, b ≤ x → x < b + size → k.Has x
  pos : C.page ≤ size
  aligned : b % C.page = 0 ∧ size % C.page = 0
  nonNull : b ≠ 0
  bound : b + size ≤ KernelSt.userTop
  brkPage : k.brk % C.page = 0

/-- The view with a new kernel and contiguity flag. -/
def setNC (l : Local) (k : KernelSt) (nc : Bool) : Local :=
  { l with kernel := k, av := { l.av with tiles := { l.av.tiles with noncontig := nc } } }

theorem mainSize_pos (hC : C.Ok) {l : Local} {nb : Nat} (hlt : topSz l.av.tiles < nb + C.minSize) :
    C.page ≤ mainSize C l nb ∧ mainSize C l nb % C.page = 0 := by
  unfold mainSize
  have hP := hC.page
  have hM := hC.minSize
  generalize hx : (if (!l.av.tiles.noncontig) = true then nb + C.topPad + C.minSize - topSz l.av.tiles
    else nb + C.topPad + C.minSize) = x
  have hx0 : 0 < x := by rw [← hx]; split <;> omega
  unfold alignUp; rw [hP]
  refine ⟨?_, by omega⟩
  have : 1 ≤ (x + 4096 - 1) / 4096 := by omega
  have := Nat.mul_le_mul_right 4096 this
  omega

theorem mainFs_ge (hC : C.Ok) {l : Local} {nb : Nat} :
    mainSize C l nb ≤ mainFs C l nb ∧ mainFs C l nb % C.page = 0 := by
  unfold mainFs
  have h1 := alignUp_page' hC (mainSize C l nb + topSz l.av.tiles)
  have h2 := hC.heapInfo.2
  split
  · refine ⟨by omega, ?_⟩
    rcases Nat.le_total (alignUp (mainSize C l nb + topSz l.av.tiles) C.page) C.mmapAsMorecore with h | h
    · rw [Nat.max_eq_right h]; exact h2
    · rw [Nat.max_eq_left h]; exact h1.2
  · refine ⟨by omega, ?_⟩
    have h3 := (alignUp_page' hC (if (!l.av.tiles.noncontig) = true then nb + C.topPad + C.minSize - topSz l.av.tiles
      else nb + C.topPad + C.minSize)).2
    rcases Nat.le_total (mainSize C l nb) C.mmapAsMorecore with h | h
    · rw [Nat.max_eq_right h]; exact h2
    · rw [Nat.max_eq_left h]; exact h3

theorem mainGot_none {l : Local} {nb : Nat} (h : (mainGot C l nb).1 = none) :
    ∃ k, (mainGot C l nb).2 = { l with kernel := k } ∧ k.brkStart = l.kernel.brkStart ∧
      k.brk = l.kernel.brk ∧ k.maps = l.kernel.maps := by
  unfold mainGot at h ⊢
  generalize hs : l.kernel.sbrk (mainSize C l nb) = sb at h ⊢
  obtain ⟨ob, k⟩ := sb
  simp only at h ⊢
  cases ob with
  | some b => simp at h
  | none =>
    obtain ⟨h1, h2, h3⟩ := sbrk_none hs
    simp only at h ⊢
    by_cases hfs : mainFs C l nb ≤ nb
    · simp only [hfs, ↓reduceIte]; exact ⟨k, rfl, h1, h2, h3⟩
    · simp only [hfs, ↓reduceIte] at h ⊢
      generalize hm : k.mmap C.page (mainFs C l nb) = mm at h ⊢
      obtain ⟨om, k'⟩ := mm
      cases om with
      | some m => simp at h
      | none =>
        obtain ⟨g1, g2, g3⟩ := mmap_none hm
        exact ⟨k', rfl, g1.trans h1, g2.trans h2, g3.trans h3⟩

theorem mainGot_some (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hmn : l.isMain = true) {nb : Nat}
    (hlt : topSz l.av.tiles < nb + C.minSize) {b : Nat} {snd : Option Nat} {size : Nat}
    (h : (mainGot C l nb).1 = some (b, snd, size)) :
    ∃ k nc, (mainGot C l nb).2 = setNC l k nc ∧ Grant C l k b size ∧
      ((snd = none ∧ k.brk = b + size ∧ b = l.kernel.brk ∧ nc = l.av.tiles.noncontig) ∨
       (snd = some (b + size) ∧ nc = true ∧ k.brk = l.kernel.brk)) := by
  obtain ⟨-, ⟨mb1, mb2, mb3, -⟩⟩ := hw.main hmn
  have hP := hC.page
  have htop : KernelSt.userTop = 2 ^ 47 := rfl
  obtain ⟨hz1, hz2⟩ := mainSize_pos hC hlt (l := l)
  obtain ⟨hf1, hf2⟩ := mainFs_ge hC (l := l) (nb := nb)
  unfold mainGot at h ⊢
  generalize hs : l.kernel.sbrk (mainSize C l nb) = sb at h ⊢
  obtain ⟨ob, k⟩ := sb
  simp only at h ⊢
  cases ob with
    | some b' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨g0, g1, g2, g3, g4, g5⟩ := sbrk_some hs
      subst g0
      obtain ⟨g6, g7, g8⟩ := g5 (by omega)
      refine ⟨k, l.av.tiles.noncontig, rfl, ?_, .inl ⟨rfl, g3, rfl, rfl⟩⟩
      exact
        { brkStart := g1
          brkLe := by omega
          maps := fun m hm => by rw [g2]; exact hm
          total := g4 mb2
          totalTop := g8
          fresh := fun r h0 hc => sbrk_away (by omega) g7 hc h0
          covers := fun x h1 h2 => .inl ⟨by rw [g1]; omega, by rw [g3]; exact h2⟩
          pos := hz1
          aligned := ⟨mb3, hz2⟩
          nonNull := by omega
          bound := g6
          brkPage := by rw [g3, hP]; rw [hP] at mb3 hz2; omega }
    | none =>
      obtain ⟨s1, s2, s3⟩ := sbrk_none hs
      by_cases hfs : mainFs C l nb ≤ nb
      · simp [hfs] at h
      · simp only [hfs, ↓reduceIte] at h ⊢
        generalize hm : k.mmap C.page (mainFs C l nb) = mm at h ⊢
        obtain ⟨om, k'⟩ := mm
        · cases om with
          | none => simp at h
          | some m =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨m1, m2, m3, hpl⟩ := mmap_some hm
            obtain ⟨p0, p1, p2, p3, p4, p5⟩ := id hpl
            have hcv : ∀ {r}, l.kernel.Covers r → k.Covers r := fun hc =>
              (kernel_covers_congr s1 s2 s3).mpr hc
            refine ⟨k', true, rfl, ?_, .inr ⟨rfl, rfl, m2.trans s2⟩⟩
            exact
              { brkStart := m1.trans s1
                brkLe := by rw [m2, s2]; exact Nat.le_refl _
                maps := fun x hx => by rw [m3, s3]; exact List.mem_cons_of_mem _ hx
                total := by
                  unfold KernelSt.total; rw [m1, m2, m3, s1, s2, s3]
                  simp only [List.map_cons, List.sum_cons]; omega
                totalTop := by
                  have := p5
                  unfold KernelSt.total at this ⊢; rw [m1, m2, m3]
                  simp only [List.map_cons, List.sum_cons]; omega
                fresh := fun r h0 hc => fresh_away hpl (by omega) (hcv hc) h0
                covers := fun x h1 h2 => .inr ⟨(m, mainFs C l nb), by rw [m3]; exact List.mem_cons_self .., h1, h2⟩
                pos := by omega
                aligned := ⟨p1, hf2⟩
                nonNull := p0
                bound := p2
                brkPage := by rw [m2, s2]; exact mb3 }

/-! ## The view after `sysmalloc` got memory -/

theorem _root_.Silmaril.Libc.Ptmalloc.Apart.cons_of {r : Nat × Nat} {R : List (Nat × Nat)} (h : Apart R)
    (h0 : 0 < r.2) (hr : ∀ q ∈ R, r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) : Apart (r :: R) :=
  ⟨List.pairwise_cons.mpr ⟨hr, h.1⟩, fun q hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h0
    · exact h.2 q hq⟩

theorem _root_.Silmaril.Libc.Ptmalloc.Apart.replace_mid {L X : List (Nat × Nat)} {r r' : Nat × Nat}
    (h : Apart (L ++ r :: X)) (h0 : 0 < r'.2) (hr : ∀ q ∈ L ++ X, r'.1 + r'.2 ≤ q.1 ∨ q.1 + q.2 ≤ r'.1) :
    Apart (L ++ r' :: X) := by
  have h1 := Apart.middle.mp h
  have h2 : Apart (L ++ X) := h1.sublist (List.sublist_cons_self _ _)
  exact Apart.middle.mpr (h2.cons_of h0 hr)

/-- The main arena after `sysmalloc` got memory: a new kernel, `mp_.sbrk_base`, a new tiling. -/
def grown (l : Local) (k : KernelSt) (sb : Nat) (ts : TopSt) : Local :=
  { l with
    kernel := k
    shared := { l.shared with mm := { l.shared.mm with mp := { l.shared.mm.mp with sbrkBase := sb } } }
    av := { l.av with tiles := ts } }

theorem view_append_clients (p : Use → Bool) (hp : p .client = false) (H X : List Chunk)
    (hX : ∀ c ∈ X, c.use = .client) : Chunk.view p (H ++ X) = Chunk.view p H := by
  have : Chunk.view p X = [] := by
    unfold Chunk.view
    exact List.filter_eq_nil_iff.mpr fun c hc => by simp [hX c hc, hp]
  unfold Chunk.view at this ⊢; rw [List.filter_append, this, List.append_nil]

theorem grown_out {l : Local} {k : KernelSt} {sb : Nat} {ts : TopSt} {X : List Chunk}
    (hch : ts.heapChunks = l.av.tiles.heapChunks ++ X) (hX : ∀ c ∈ X, c.use = .client) :
    (grown l k sb ts).av.out C = l.av.out C ++ X.map fun c => (c.addr + C.hdr, usable C c false) := by
  unfold ArenaSt.out ArenaSt.chunks
  show (Chunk.view (· = .client) ts.heapChunks).map _ = _
  rw [hch]
  unfold Chunk.view
  rw [List.filter_append, List.map_append]
  congr 1
  rw [List.filter_eq_self.mpr fun c hc => by simp [hX c hc]]

theorem grown_live_nil {l : Local} {k : KernelSt} {sb : Nat} {ts : TopSt}
    (hch : ts.heapChunks = l.av.tiles.heapChunks) : (grown l k sb ts).live C = l.live C := by
  have h := grown_out (C := C) (k := k) (sb := sb) (X := []) (by rw [hch, List.append_nil]) (by simp)
  rw [List.map_nil, List.append_nil] at h
  unfold Local.live
  rw [h]; rfl

/-- **The main arena after `sysmalloc` got memory is well formed and framed**, given the new
tiling's invariant and that its bytes are old bytes or the fresh ones. -/
theorem grow {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) (hi : l.shared.init = true)
    (hmn : l.isMain = true) {k : KernelSt} {b size : Nat} (G : Grant C l k b size) {sb : Nat} {ts : TopSt}
    {X : List Chunk} (hT : TopWF C ts) (hch : ts.heapChunks = l.av.tiles.heapChunks ++ X)
    (hX : ∀ c ∈ X, c.use = .client) (hap : Apart (grown l k sb ts).spans)
    (hcov : ∀ s ∈ ts.spans, ∀ x, s.1 ≤ x → x < s.1 + s.2 → InSpans l.spans x ∨ (b ≤ x ∧ x < b + size))
    (hms : MainSbrk (grown l k sb ts).shared (grown l k sb ts).av)
    (hmb : MainBrk C k (grown l k sb ts).av)
    (hsys : ts.systemMem ≤ l.av.tiles.systemMem + size) :
    LocalWF C (grown l k sb ts) ∧ Frame C l (grown l k sb ts) [] ∧ KeptAway l (grown l k sb ts) := by
  have hviews (p : Use → Bool) (hp : p .client = false) :
      Chunk.view p ts.heapChunks = Chunk.view p l.av.tiles.heapChunks := by
    rw [hch]; exact view_append_clients p hp _ _ hX
  have hA := hw.arena.withTilesViews ts hT (hviews _ rfl) (hviews _ rfl) (hviews _ rfl)
  have hm := hw.shared.mm
  have hmono : ∀ {x}, l.kernel.Has x → k.Has x := fun h => has_mono_le G.brkStart G.brkLe G.maps h
  have hsp' : ∀ s ∈ (grown l k sb ts).spans, ∀ x, s.1 ≤ x → x < s.1 + s.2 →
      InSpans l.spans x ∨ (b ≤ x ∧ x < b + size) := by
    intro s hs x h1 h2
    unfold Local.spans ArenaSt.spans at hs
    rcases List.mem_append.mp hs with hs | hs
    · rcases List.mem_append.mp hs with hs | hs
      · exact hcov s hs x h1 h2
      · refine .inl ⟨s, ?_, h1, h2⟩
        unfold Local.spans ArenaSt.spans
        exact List.mem_append_left _ (List.mem_append_right _ hs)
    · exact .inl ⟨s, List.mem_append_right _ hs, h1, h2⟩
  refine ⟨?_, ?_, fun tc _ _ ht he _ => ⟨tc, ht, he⟩⟩
  · exact
      { arena := hA
        shared :=
          { mm := { mpBound := hm.mpBound, trimMin := hm.trimMin, use := hm.use, page := hm.page,
                    nonNull := hm.nonNull, nodup := hm.nodup, mem := hm.mem }
            narenas := hw.shared.narenas
            freeListSub := hw.shared.freeListSub }
        tcache := hw.tcache
        main := fun _ => ⟨hms, hmb⟩
        init := fun h0 => absurd ((show l.shared.init = false from h0).symm.trans hi) (by decide)
        apart := hap
        mmSize := hw.mmSize
        sysMain := fun _ => by
          have h1 := hw.sysMain hmn
          have h2 := G.total
          show ts.systemMem + l.shared.mm.mp.mmappedMem ≤ k.total
          omega
        heap := fun h => absurd (hmn.symm.trans h) (by decide) }
  · exact
      { avAddr := rfl
        isMain := rfl
        spatial := fun r h0 hc ha => by
          refine ⟨fun x h1 h2 => hmono (hc x h1 h2), fun s hs => ?_⟩
          refine Classical.byContradiction fun hne => ?_
          have hs0 := hap.2 s hs
          have hfr := G.fresh r h0 hc
          rcases Nat.le_total r.1 s.1 with hle | hle
          · rcases hsp' s hs s.1 (Nat.le_refl _) (by omega) with ⟨s0, h0', a1, a2⟩ | ⟨a1, a2⟩
            · have := ha s0 h0'; omega
            · omega
          · rcases hsp' s hs r.1 hle (by omega) with ⟨s0, h0', a1, a2⟩ | ⟨a1, a2⟩
            · have := ha s0 h0'; omega
            · omega
        covered := fun s hs x h1 h2 => by
          rcases hsp' s hs x h1 h2 with ⟨s0, hs0, a1, a2⟩ | ⟨a1, a2⟩
          · exact hmono (hsp.covered s0 hs0 x a1 a2)
          · exact G.covers x a1 a2
        brkStart := G.brkStart
        nonMain := fun h => by rw [hmn] at h; cases h
        acct := fun h => by rw [hmn] at h; cases h
        init := rfl
        arenas := ⟨rfl, rfl, rfl⟩
        arena := rfl
        heaps := id
        clients := fun c hc _ _ => by
          show c ∈ ts.heapChunks
          rw [hch]; exact List.mem_append_left _ hc
        fresh := fun tc' i e ht he => .inl ⟨tc', i, ht, he⟩ }

/-- The `sbrk_base` after `sysmalloc` got memory at `b`. -/
abbrev newBase (l : Local) (b : Nat) : Nat :=
  if l.shared.mm.mp.sbrkBase = 0 then b else l.shared.mm.mp.sbrkBase

/-- The contiguous extension of top. -/
abbrev extTiles (l : Local) (size : Nat) : TopSt :=
  { l.av.tiles with systemMem := l.av.tiles.systemMem + size, topSize := size + topSz l.av.tiles }

/-- **The contiguous extension of top** is an `MStep`. -/
theorem ext_step (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) (hi : l.shared.init = true)
    (hmn : l.isMain = true) {k : KernelSt} {b size : Nat} (G : Grant C l k b size)
    (hs0 : l.av.tiles.start ≠ 0) (hb : b = l.av.tiles.top + topSz l.av.tiles) (hkb : k.brk = b + size) :
    MStep C l (grown l k (newBase l b) (extTiles l size)) := by
  have hT := hw.arena.tiles
  obtain ⟨⟨ms1, ms2⟩, ⟨mb1, mb2, mb3, mb4⟩⟩ := hw.main hmn
  have hz : topSz l.av.tiles = l.av.tiles.topSize := by unfold topSz; simp [hs0]
  rw [hz] at hb
  have hA := hC.align; have hP := hC.page
  have htopv : KernelSt.userTop = 2 ^ 47 := rfl
  have hGb := G.bound; have hGt := G.total; have hGT := G.totalTop
  have hsm := hw.sysMain hmn
  obtain ⟨ga1, ga2⟩ := G.aligned
  have hzp := top_pos hw hs0
  have hT' : TopWF C (extTiles l size) :=
    { sizes := hT.sizes, aligned := hT.aligned, nonNull := hT.nonNull, topAt := hT.topAt
      topAligned := by
        have := hT.topAligned; simp only [hz]; rw [hA] at this ⊢; rw [hP] at ga2; omega
      topMin := fun _ => by have := hT.topMin hs0; simp only [hz]; omega
      coalesced := hT.coalesced, lastUsed := hT.lastUsed, coalescedOld := hT.coalescedOld
      sysMem := by
        have := hT.sysMem
        show (l.av.tiles.heapChunks.map (·.size)).sum + (size + topSz l.av.tiles) ≤ l.av.tiles.systemMem + size
        rw [hz]; omega
      sysMemBound := by show l.av.tiles.systemMem + size < 2 ^ 64; omega
      noHeap := fun h => absurd h hs0, nodup := hT.nodup, bound := hT.bound
      topBound := fun _ => by show l.av.tiles.top + (size + topSz l.av.tiles) < 2 ^ 64; rw [hz]; omega }
  have hsp0 := spans_eq_top hs0 (l := l)
  have hspE : (grown l k (newBase l b) (extTiles l size)).spans =
      l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
        (l.av.tiles.top, size + l.av.tiles.topSize) :: (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))) := by
    rw [Local.spans_eq]
    show ((extTiles l size).heapChunks.map (fun c => (c.addr, c.size)) ++
      (if l.av.tiles.start = 0 then [] else [(l.av.tiles.top, size + topSz l.av.tiles)])) ++
        (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))) = _
    simp only [hs0, ↓reduceIte, hz, List.append_assoc, List.singleton_append]; rfl
  have hold : Apart (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
      (l.av.tiles.top, l.av.tiles.topSize) :: (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) := by
    have := hw.apart; rw [hsp0, List.append_assoc, List.singleton_append] at this; exact this
  have hmemold : ∀ q ∈ l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
      (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))), q ∈ l.spans := by
    intro q hq; rw [hsp0]
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ (List.mem_append_left _ hq)
    · exact List.mem_append_right _ hq
  have hap : Apart (grown l k (newBase l b) (extTiles l size)).spans := by
    rw [hspE]
    refine hold.replace_mid (by simp only; omega) fun q hq => ?_
    have h1 := (Apart.middle.mp hold).1
    have h1 := (List.pairwise_cons.mp h1).1 q hq
    have hq0 := hw.apart.2 q (hmemold q hq)
    have h2 := G.fresh q hq0 (hsp.covered q (hmemold q hq))
    simp only at h1 ⊢; omega
  have hcov : ∀ s ∈ (extTiles l size).spans, ∀ x, s.1 ≤ x → x < s.1 + s.2 →
      InSpans l.spans x ∨ (b ≤ x ∧ x < b + size) := by
    intro s hs x h1 h2
    unfold TopSt.spans at hs
    simp only [extTiles, hs0, ↓reduceIte, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact .inl ⟨s, by rw [hsp0]; exact List.mem_append_left _ (List.mem_append_left _ hs), h1, h2⟩
    · simp only [hz] at h1 h2
      by_cases hx : x < l.av.tiles.top + l.av.tiles.topSize
      · exact .inl ⟨(l.av.tiles.top, l.av.tiles.topSize), by rw [hsp0]; simp, h1, hx⟩
      · exact .inr ⟨by omega, by omega⟩
  have hbase : newBase l b = l.shared.mm.mp.sbrkBase := by
    have : l.shared.mm.mp.sbrkBase ≠ 0 := fun h => hs0 (ms1.mp h)
    simp [newBase, this]
  have hms : MainSbrk (grown l k (newBase l b) (extTiles l size)).shared
      (grown l k (newBase l b) (extTiles l size)).av := by
    unfold MainSbrk; simp only [grown, extTiles]; rw [hbase]; exact ⟨ms1, ms2⟩
  have hmb : MainBrk C k (grown l k (newBase l b) (extTiles l size)).av := by
    unfold MainBrk; simp only [grown, hz]
    refine ⟨by rw [G.brkStart]; exact mb1, by rw [G.brkStart]; have := G.brkLe; omega, G.brkPage,
      fun _ => ⟨?_, fun hnc => ⟨by rw [G.brkStart]; exact (mb4 hs0).2 hnc |>.1, by omega⟩⟩⟩
    rw [hP] at ga1 ga2 ⊢; omega
  obtain ⟨hwl, hF, hK⟩ := grow hw hsp hi hmn G (X := []) hT' (by rw [List.append_nil]; rfl) (by simp) hap hcov hms hmb
    (by show l.av.tiles.systemMem + size ≤ _; omega)
  exact ⟨hwl, by rw [grown_live_nil (by rfl)], hF, hK, id⟩

/-! ## Closing the old segment -/

/-- **`closeSegment` for the main arena**: no heap yet (nothing closed), or the old top closed
with two fence posts into a client chunk of `topSize - 2 * CHUNK_HDR_SZ` bytes (freed after), or
into a pad when that is under `MINSIZE`. -/
theorem closeSeg_spec (hC : C.Ok) (L : Local) (top' size' : Nat)
    (hT : L.av.tiles.start ≠ 0 → L.av.tiles.topSize % C.align = 0 ∧ C.minSize ≤ L.av.tiles.topSize) :
    ∃ segs fr, closeSegment C L top' size' true = (fr, withTiles L { L.av.tiles with
        start := top', chunks := [], top := top', topSize := size', old := L.av.tiles.old ++ segs }) ∧
      ((L.av.tiles.start = 0 ∧ segs = [] ∧ fr = none) ∨
       (L.av.tiles.start ≠ 0 ∧ C.minSize ≤ L.av.tiles.topSize - 2 * C.hdr ∧
         segs = [{ start := L.av.tiles.start, chunks := L.av.tiles.chunks ++ [(L.av.tiles.topSize - 2 * C.hdr, .client)] }] ∧
         fr = some L.av.tiles.top) ∨
       (L.av.tiles.start ≠ 0 ∧ L.av.tiles.topSize - 2 * C.hdr < C.minSize ∧
         segs = [{ start := L.av.tiles.start, chunks := L.av.tiles.chunks, pad := L.av.tiles.topSize - 2 * C.hdr }] ∧
         fr = none)) := by
  have hA := hC.align; have hM := hC.minSize; have hS := hC.sizeSz
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  unfold closeSegment
  by_cases hs : L.av.tiles.start = 0
  · refine ⟨[], none, ?_, .inl ⟨hs, rfl, rfl⟩⟩
    simp [topSz, hs]
  · obtain ⟨h1, h2⟩ := hT hs
    have hz : topSz L.av.tiles = L.av.tiles.topSize := by simp [topSz, hs]
    have hos : alignDown (L.av.tiles.topSize - 2 * C.hdr) C.align = L.av.tiles.topSize - 2 * C.hdr := by
      unfold alignDown; rw [hA, hhdr] at *; omega
    by_cases hm : C.minSize ≤ L.av.tiles.topSize - 2 * C.hdr
    · refine ⟨_, _, ?_, .inr (.inl ⟨hs, hm, rfl, rfl⟩)⟩
      simp only [hz, hos, hs, ne_eq, not_false_eq_true, true_and, hm, ↓reduceIte]
      have : L.av.tiles.topSize ≠ 0 := by omega
      simp [this]
    · refine ⟨_, _, ?_, .inr (.inr ⟨hs, by omega, rfl, rfl⟩)⟩
      simp only [hz, hos, hs, ne_eq, not_false_eq_true, true_and, hm, ↓reduceIte]
      have : L.av.tiles.topSize ≠ 0 := by omega
      simp [this]

/-- **A frame, then a frame freeing one fresh payload**, is a frame freeing nothing. -/
theorem Frame.trans_one {l l₁ l₂ : Local} {x : Nat × Nat} (h₁ : Frame C l l₁ []) (h₂ : Frame C l₁ l₂ [x])
    (hx : ∀ c ∈ l.av.chunks, c.addr + C.hdr ≠ x.1)
    (hpk : ∀ tc i e, l₁.thread.tcache = some tc → e ∈ tc.bins i → e.1 + C.hdr ≠ x.1) :
    Frame C l l₂ [] where
  avAddr := h₂.avAddr.trans h₁.avAddr
  isMain := h₂.isMain.trans h₁.isMain
  spatial r h0 hc ha :=
    let h := h₁.spatial r h0 hc ha
    h₂.spatial r h0 h.1 h.2
  covered := h₂.covered
  brkStart := h₂.brkStart.trans h₁.brkStart
  nonMain hm := by
    have a := h₁.nonMain hm
    have b := h₂.nonMain (by rw [h₁.isMain]; exact hm)
    exact ⟨b.1.trans a.1, b.2.trans a.2⟩
  acct hm := by
    have a := h₁.acct hm
    have b := h₂.acct (by rw [h₁.isMain]; exact hm)
    omega
  init := h₂.init.trans h₁.init
  arenas := ⟨h₂.arenas.1.trans h₁.arenas.1, h₂.arenas.2.1.trans h₁.arenas.2.1,
    h₂.arenas.2.2.trans h₁.arenas.2.2⟩
  arena := h₂.arena.trans h₁.arena
  heaps h := h₂.heaps (h₁.heaps h)
  clients c hc hu _ := h₂.clients c (h₁.clients c hc hu (by simp)) hu (by
    simp only [List.mem_singleton]; intro h; exact hx c hc (by rw [← h]))
  fresh tc'' i e ht he := by
    rcases h₂.fresh tc'' i e ht he with ⟨tc', j, ht', he'⟩ | ⟨hc, hfr⟩
    · rcases h₁.fresh tc' j e ht' he' with h | ⟨⟨c, hc, h1, h2, h3⟩, hfr'⟩
      · exact .inl h
      · refine .inr ⟨⟨c, h₂.clients c hc h3 ?_, h1, h2, h3⟩, hfr'⟩
        simp only [List.mem_singleton]; intro h
        exact hpk tc' j e ht' he' (by rw [← h, h1])
    · rcases hfr with hfr | hfr
      · refine .inr ⟨hc, .inr fun c hc' hca _ => ?_⟩
        simp only [List.mem_singleton] at hfr
        exact hx c hc' (by rw [hca, ← hfr])
      · exact .inr ⟨hc, .inr fun c hc' hca hcu => hfr c (h₁.clients c hc' hcu (by simp)) hca hcu⟩

/-- `_int_free` keeps an absent tcache absent. -/
theorem intFree_tcNone (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) {p u : Nat}
    (hpu : (p, u) ∈ l.arenaLive C) (h : intFree C l (p - C.hdr) = .ok l') (ht : l.thread.tcache = none) :
    l'.thread.tcache = none := by
  obtain ⟨ch, hch, hcu, rfl, rfl, -, hf, h1, h2⟩ := intFree_open hC hw hpu
  have hpc : ch.addr + C.hdr - C.hdr = ch.addr := by omega
  rw [hpc, intFree_eq hf hcu h1 h2, ht] at h
  simp only at h
  unfold freeRest at h
  split at h
  · split at h
    · cases h
    · cases h; exact ht
  · obtain ⟨-, -, -, h3, -, -⟩ := freeMerge_spec hC hw hch hcu h
    rw [h3]; exact ht

/-! ## A new top -/

/-- The tiling with a new top at `b` of `size` bytes and the closed segments `segs` added. -/
abbrev newTop (l : Local) (nc : Bool) (b size : Nat) (segs : List Seg) : TopSt :=
  { l.av.tiles with
    noncontig := nc
    systemMem := l.av.tiles.systemMem + size
    start := b
    chunks := []
    top := b
    topSize := size
    old := l.av.tiles.old ++ segs }

/-- **A new top** (the old one closed into `segs`, its chunks `X`) keeps `LocalWF`, with a frame. -/
theorem newtop_grow {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) (hi : l.shared.init = true)
    (hmn : l.isMain = true) {k : KernelSt} {b size : Nat} (G : Grant C l k b size) {nc : Bool}
    (hkb : nc = false → l.av.tiles.start = 0 ∧ b = l.kernel.brk ∧ k.brk = b + size)
    (hC : C.Ok) {segs : List Seg} {X : List Chunk}
    (hch : (newTop l nc b size segs).heapChunks = l.av.tiles.heapChunks ++ X)
    (hX : ∀ c ∈ X, c.use = .client ∧ c.size % C.align = 0 ∧ C.minSize ≤ c.size ∧ c.addr % C.align = 0 ∧
      c.addr ≠ 0 ∧ c.addr + c.size < 2 ^ 64)
    (hXn : ((l.av.tiles.heapChunks ++ X).map (·.addr)).Nodup)
    (hsum : ((l.av.tiles.heapChunks ++ X).map (·.size)).sum ≤ l.av.tiles.systemMem)
    (hco : ∀ g ∈ segs, Coalesced g.chunks)
    (hQ : Apart (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++ X.map (fun c => (c.addr, c.size)) ++
      (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))))
    (hXcov : ∀ c ∈ X, ∀ x, c.addr ≤ x → x < c.addr + c.size → InSpans l.spans x)
    (hold : nc = false → segs = []) :
    LocalWF C (grown l k (newBase l b) (newTop l nc b size segs)) ∧
      Frame C l (grown l k (newBase l b) (newTop l nc b size segs)) [] ∧
      KeptAway l (grown l k (newBase l b) (newTop l nc b size segs)) := by
  have hT := hw.arena.tiles
  obtain ⟨⟨ms1, ms2⟩, ⟨mb1, mb2, mb3, mb4⟩⟩ := hw.main hmn
  have hA := hC.align; have hP := hC.page; have hM := hC.minSize
  have htopv : KernelSt.userTop = 2 ^ 47 := rfl
  have hGb := G.bound; have hGt := G.total; have hGT := G.totalTop; have hGp := G.pos
  have hb0 := G.nonNull
  have hsm := hw.sysMain hmn
  obtain ⟨ga1, ga2⟩ := G.aligned
  have hHX : ∀ c ∈ (newTop l nc b size segs).heapChunks, c ∈ l.av.tiles.heapChunks ∨ c ∈ X := by
    intro c hc; rw [hch] at hc; exact List.mem_append.mp hc
  have hT' : TopWF C (newTop l nc b size segs) :=
    { sizes := fun c hc => by
        rcases hHX c hc with hc | hc
        · exact hT.sizes c hc
        · exact ⟨(hX c hc).2.1, (hX c hc).2.2.1⟩
      aligned := fun c hc => by
        rcases hHX c hc with hc | hc
        · exact hT.aligned c hc
        · exact (hX c hc).2.2.2.1
      nonNull := fun c hc => by
        rcases hHX c hc with hc | hc
        · exact hT.nonNull c hc
        · exact (hX c hc).2.2.2.2.1
      topAt := fun _ => by simp
      topAligned := by show b % C.align = 0 ∧ size % C.align = 0; rw [hA]; rw [hP] at ga1 ga2; omega
      topMin := fun _ => by show C.minSize ≤ size; rw [hP] at hGp; omega
      coalesced := rfl
      lastUsed := by simp
      coalescedOld := fun g hg => by
        have hg : g ∈ l.av.tiles.old ++ segs := hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hT.coalescedOld g hg
        · exact hco g hg
      sysMem := by
        show ((newTop l nc b size segs).heapChunks.map (·.size)).sum + size ≤ l.av.tiles.systemMem + size
        rw [hch]; omega
      sysMemBound := by show l.av.tiles.systemMem + size < 2 ^ 64; omega
      noHeap := fun h => absurd h hb0
      nodup := by rw [hch]; exact hXn
      bound := fun c hc => by
        rcases hHX c hc with hc | hc
        · exact hT.bound c hc
        · exact (hX c hc).2.2.2.2.2
      topBound := fun _ => by show b + size < 2 ^ 64; omega }
  have hspN : (grown l k (newBase l b) (newTop l nc b size segs)).spans =
      (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++ X.map (fun c => (c.addr, c.size))) ++
        (b, size) :: (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))) := by
    rw [Local.spans_eq]
    show ((newTop l nc b size segs).heapChunks.map (fun c => (c.addr, c.size)) ++
      (if b = 0 then [] else [(b, size)])) ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))) = _
    rw [hch]; simp [hb0]
  have hcovq : ∀ q ∈ l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++ X.map (fun c => (c.addr, c.size)) ++
      (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))), l.kernel.Covers q := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
        exact hsp.covered _ (mem_spans_of_chunk hc)
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
        intro x h1 h2
        obtain ⟨s0, hs0, a1, a2⟩ := hXcov c hc x h1 h2
        exact hsp.covered s0 hs0 x a1 a2
    · exact hsp.covered q (by rw [Local.spans_eq]; exact List.mem_append_right _ hq)
  have hap : Apart (grown l k (newBase l b) (newTop l nc b size segs)).spans := by
    rw [hspN]
    refine Apart.middle.mpr (Apart.cons_of hQ (by simp only; omega) fun q hq => ?_)
    exact (G.fresh q (hQ.2 q hq) (hcovq q hq)).symm
  have hcov : ∀ s ∈ (newTop l nc b size segs).spans, ∀ x, s.1 ≤ x → x < s.1 + s.2 →
      InSpans l.spans x ∨ (b ≤ x ∧ x < b + size) := by
    intro s hs x h1 h2
    have hs' : s ∈ (newTop l nc b size segs).heapChunks.map (fun c => (c.addr, c.size)) ++
        (if b = 0 then [] else [(b, size)]) := hs
    rw [hch] at hs'
    simp only [hb0, ↓reduceIte, List.mem_append, List.mem_singleton, List.map_append] at hs'
    rcases hs' with (hs' | hs') | rfl
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs'
      exact .inl ⟨_, mem_spans_of_chunk hc, h1, h2⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs'
      exact .inl (hXcov c hc x h1 h2)
    · exact .inr ⟨h1, h2⟩
  have hnb0 : newBase l b ≠ 0 := by
    unfold newBase; split
    · exact hb0
    · assumption
  have hms : MainSbrk (grown l k (newBase l b) (newTop l nc b size segs)).shared
      (grown l k (newBase l b) (newTop l nc b size segs)).av := by
    refine ⟨⟨fun h => absurd h hnb0, fun h => absurd h hb0⟩, fun hnc => ?_⟩
    obtain ⟨hs0, -, -⟩ := hkb hnc
    have hsb : l.shared.mm.mp.sbrkBase = 0 := ms1.mpr hs0
    refine ⟨by simp [newBase, grown, hsb], ?_⟩
    show l.av.tiles.old ++ segs = []
    rw [(hT.noHeap hs0).2, hold hnc]; rfl
  have hmb : MainBrk C k (grown l k (newBase l b) (newTop l nc b size segs)).av := by
    refine ⟨by rw [G.brkStart]; exact mb1, by rw [G.brkStart]; have := G.brkLe; omega, G.brkPage,
      fun _ => ⟨?_, fun hnc => ?_⟩⟩
    · show (b + size) % C.page = 0
      rw [hP] at ga1 ga2 ⊢; omega
    · obtain ⟨-, hbb, hkk⟩ := hkb hnc
      exact ⟨by rw [G.brkStart]; show l.kernel.brkStart ≤ b; omega, hkk⟩
  exact grow hw hsp hi hmn G hT' hch (fun c hc => (hX c hc).1) hap hcov hms hmb
    (by show l.av.tiles.systemMem + size ≤ _; omega)

/-- The tiling before the old segment is closed. -/
abbrev preTiles (l : Local) (nc : Bool) (size : Nat) : TopSt :=
  { l.av.tiles with noncontig := nc, systemMem := l.av.tiles.systemMem + size }

/-- **The old top closed into a client chunk `t` of `os` bytes**, which `_int_free` then gets. -/
structure Closed (C : Config) (l N : Local) (t os : Nat) : Prop where
  wf : LocalWF C N
  sp : LocalSp C N
  frame : Frame C l N []
  kept : KeptAway l N
  thread : N.thread = l.thread
  mem : (t + C.hdr, os - C.sizeSz) ∈ N.arenaLive C
  live : (N.live C).Perm ((t + C.hdr, os - C.sizeSz) :: l.live C)
  fresh : ∀ c ∈ l.av.chunks, c.addr + C.hdr ≠ (t + C.hdr, os - C.sizeSz).1
  notEntry : ∀ tc i e, N.thread.tcache = some tc → e ∈ tc.bins i → e.1 + C.hdr ≠ (t + C.hdr, os - C.sizeSz).1

/-- **A new top**: the old segment closed, nothing to free (an `MStep`), or its old top a client
chunk to free (`Closed`). -/
theorem newtop (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) (hi : l.shared.init = true)
    (hmn : l.isMain = true) {k : KernelSt} {b size : Nat} (G : Grant C l k b size) {nc : Bool}
    (hkb : nc = false → l.av.tiles.start = 0 ∧ b = l.kernel.brk ∧ k.brk = b + size) :
    ((closeSegment C (grown l k (newBase l b) (preTiles l nc size)) b size true).1 = none ∧
      MStep C l (closeSegment C (grown l k (newBase l b) (preTiles l nc size)) b size true).2) ∨
    ∃ t os, (closeSegment C (grown l k (newBase l b) (preTiles l nc size)) b size true).1 = some t ∧
      Closed C l (closeSegment C (grown l k (newBase l b) (preTiles l nc size)) b size true).2 t os := by
  have hT := hw.arena.tiles
  have hA := hC.align; have hM := hC.minSize; have hS := hC.sizeSz
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  obtain ⟨segs, fr, hcs, hcases⟩ := closeSeg_spec hC (grown l k (newBase l b) (preTiles l nc size)) b size
    (fun hs => ⟨hT.topAligned.2, hT.topMin hs⟩)
  rw [hcs]
  show (fr = none ∧ MStep C l (grown l k (newBase l b) (newTop l nc b size segs))) ∨
    ∃ t os, fr = some t ∧ Closed C l (grown l k (newBase l b) (newTop l nc b size segs)) t os
  have hHn := hT.nodup
  rcases hcases with ⟨hs0, rfl, rfl⟩ | ⟨hs0, hm, rfl, rfl⟩ | ⟨hs0, hm, rfl, rfl⟩
  · -- no heap yet
    have hs0 : l.av.tiles.start = 0 := hs0
    obtain ⟨hc0, ho0⟩ := hT.noHeap hs0
    have hH : l.av.tiles.heapChunks = [] := by simp [TopSt.heapChunks, hc0, ho0]
    have hch : (newTop l nc b size []).heapChunks = l.av.tiles.heapChunks ++ [] := by
      rw [hH]; simp [TopSt.heapChunks, ho0]
    have hQ : Apart (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++ ([] : List Chunk).map
        (fun c => (c.addr, c.size)) ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) := by
      have := hw.apart
      unfold Local.spans ArenaSt.spans TopSt.spans at this
      simpa [hs0] using this
    obtain ⟨hwl, hF, hK⟩ := newtop_grow hw hsp hi hmn G hkb hC hch (by simp) (by simpa using hHn)
      (by have := hT.sysMem; simp only [List.append_nil]; omega) (by simp) hQ (by simp) (fun _ => rfl)
    refine .inl ⟨rfl, hwl, ?_, hF, hK, id⟩
    rw [grown_live_nil (by rw [hch, List.append_nil])]
  · -- the old top closed into a client chunk
    show _ ∨ ∃ t os, some l.av.tiles.top = some t ∧ Closed C l (grown l k (newBase l b) (newTop l nc b size
      [{ start := l.av.tiles.start, chunks := l.av.tiles.chunks ++ [(l.av.tiles.topSize - 2 * C.hdr, .client)] }])) t os
    have hs0 : l.av.tiles.start ≠ 0 := hs0
    have hm : C.minSize ≤ l.av.tiles.topSize - 2 * C.hdr := hm
    have htA := hT.topAligned
    have htB := hT.topBound hs0
    have htop := hT.topAt hs0
    have hsS := hT.sysMem
    have hch : (newTop l nc b size [{ start := l.av.tiles.start, chunks := l.av.tiles.chunks ++ [((l.av.tiles.topSize - 2 * C.hdr), .client)] }]).heapChunks =
        l.av.tiles.heapChunks ++ [⟨l.av.tiles.top, (l.av.tiles.topSize - 2 * C.hdr), .client⟩] := by
      unfold TopSt.heapChunks
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, layout_nil]
      rw [layout_append, htop]
      simp [layout, runLen, List.append_assoc]
    have hfresh : ∀ c ∈ l.av.tiles.heapChunks, c.addr ≠ l.av.tiles.top := by
      intro c hc heq
      have := top_apart_chunk hw hs0 hc
      have := (hT.sizes c hc).2
      omega
    have hQ : Apart (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
        [(⟨l.av.tiles.top, (l.av.tiles.topSize - 2 * C.hdr), .client⟩ : Chunk)].map (fun c => (c.addr, c.size)) ++
        (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) := by
      have h0 := hw.apart
      rw [spans_eq_top hs0, List.append_assoc, List.singleton_append] at h0
      have := Apart.shrink_mid h0 (s := (l.av.tiles.topSize - 2 * C.hdr)) (by omega) (by simp only; omega)
      simpa [List.append_assoc] using this
    have htmem : (l.av.tiles.top, l.av.tiles.topSize) ∈ l.spans := by rw [spans_eq_top hs0]; simp
    have hXc : (⟨l.av.tiles.top, l.av.tiles.topSize - 2 * C.hdr, .client⟩ : Chunk).use = .client ∧
        (l.av.tiles.topSize - 2 * C.hdr) % C.align = 0 ∧ C.minSize ≤ l.av.tiles.topSize - 2 * C.hdr ∧
        l.av.tiles.top % C.align = 0 ∧ l.av.tiles.top ≠ 0 ∧
        l.av.tiles.top + (l.av.tiles.topSize - 2 * C.hdr) < 2 ^ 64 := by
      refine ⟨rfl, ?_, hm, htA.1, ?_, by omega⟩
      · rw [hA] at htA ⊢; rw [hhdr]; omega
      · rw [htop]; omega
    obtain ⟨hwl, hF, hK⟩ := newtop_grow hw hsp hi hmn G hkb hC hch
      (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact hXc)
      (by
        rw [List.map_append, List.nodup_append]
        refine ⟨hHn, by simp, ?_⟩
        intro a ha c hc; simp at hc; subst hc
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
        exact hfresh d hd)
      (by simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil]; omega)
      (fun g hg => by
        simp only [List.mem_singleton] at hg; subst hg
        exact (coalescedB_mid_used ((l.av.tiles.topSize - 2 * C.hdr), .client) [] l.av.tiles.chunks rfl).mpr ⟨hT.coalesced, rfl⟩)
      hQ
      (fun c hc x h1 h2 => by
        simp only [List.mem_singleton] at hc; subst hc
        exact ⟨_, htmem, h1, by simp only at h2 ⊢; omega⟩)
      (fun hnc => absurd (hkb hnc).1 hs0)
    refine .inr ⟨l.av.tiles.top, (l.av.tiles.topSize - 2 * C.hdr), rfl, ?_⟩
    have hout := grown_out (C := C) (k := k) (sb := newBase l b) hch (fun c hc => by simp at hc; rw [hc])
    have hnp : (l.thread.parked C).contains (l.av.tiles.top + C.hdr, (l.av.tiles.topSize - 2 * C.hdr) - C.sizeSz) = false := by
      rw [contains_false]
      intro hmem
      obtain ⟨tc, htc, i, -, e, he, hpe⟩ := mem_parked.mp hmem
      simp only [epay, Prod.mk.injEq] at hpe
      exact top_not_entry hC hw hsp hs0 htc he (by omega)
    have hx : usable C ⟨l.av.tiles.top, (l.av.tiles.topSize - 2 * C.hdr), .client⟩ false = (l.av.tiles.topSize - 2 * C.hdr) - C.sizeSz := by simp [usable]
    exact
      { wf := hwl
        sp := LocalSp.of_frame hC hw hsp hF
        frame := hF
        kept := hK
        thread := rfl
        mem := by
          unfold Local.arenaLive
          rw [hout]
          refine List.mem_filter.mpr ⟨List.mem_append_right _ (by simp [hx]), ?_⟩
          show (!(l.thread.parked C).contains _) = true
          rw [hnp]; rfl
        live := by
          unfold Local.live
          rw [hout, List.filter_append]
          show ((List.filter _ (l.av.out C) ++ List.filter (fun pu => !(l.thread.parked C).contains pu)
            [(l.av.tiles.top + C.hdr, usable C ⟨l.av.tiles.top, (l.av.tiles.topSize - 2 * C.hdr), .client⟩ false)]) ++ l.shared.live C).Perm _
          rw [hx, List.filter_cons_of_pos (by rw [hnp]; rfl), List.filter_nil, List.append_assoc,
            List.singleton_append]
          exact List.perm_middle
        fresh := fun c hc => by
          have := hfresh c hc
          simp only; omega
        notEntry := fun tc i e htc he => by
          have := top_not_entry hC hw hsp hs0 htc he
          simp only; omega }
  · -- the old top closed into a pad
    show (none = none ∧ MStep C l (grown l k (newBase l b) (newTop l nc b size
      [{ start := l.av.tiles.start, chunks := l.av.tiles.chunks, pad := l.av.tiles.topSize - 2 * C.hdr }]))) ∨ _
    have hs0 : l.av.tiles.start ≠ 0 := hs0
    have hch : (newTop l nc b size
        [{ start := l.av.tiles.start, chunks := l.av.tiles.chunks, pad := l.av.tiles.topSize - 2 * C.hdr }]).heapChunks =
        l.av.tiles.heapChunks ++ [] := by
      unfold TopSt.heapChunks
      simp
    have hQ : Apart (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++ ([] : List Chunk).map
        (fun c => (c.addr, c.size)) ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) := by
      have h0 := hw.apart
      rw [spans_eq_top hs0] at h0
      refine h0.sublist ?_
      simp only [List.map_nil, List.append_nil]
      exact List.Sublist.append (List.sublist_append_left _ _) (List.Sublist.refl _)
    obtain ⟨hwl, hF, hK⟩ := newtop_grow hw hsp hi hmn G hkb hC hch (by simp) (by simpa using hHn)
      (by have := hT.sysMem; simp only [List.append_nil]; omega)
      (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hT.coalesced) hQ (by simp)
      (fun hnc => absurd (hkb hnc).1 hs0)
    refine .inl ⟨rfl, hwl, ?_, hF, hK, id⟩
    rw [grown_live_nil (by rw [hch, List.append_nil])]

/-- **Freeing the closed old top**, then nothing else: an `MStep`. -/
theorem closed_step (hC : C.Ok) {l N l₄ : Local} (hw : LocalWF C l) (hsp : LocalSp C l) {t os : Nat}
    (hc : Closed C l N t os) (h : intFree C N t = .ok l₄) : MStep C l l₄ := by
  have hpc : t + C.hdr - C.hdr = t := by omega
  obtain ⟨hw4, hF4, hK4, hp4⟩ := bodyFree C hC N l₄ (t + C.hdr) (os - C.sizeSz) hc.wf hc.sp hc.mem
    (by rw [hpc]; exact h)
  refine ⟨hw4, ?_, Frame.trans_one hc.frame hF4 hc.fresh hc.notEntry,
    KeptAway.trans hC hw hsp hc.frame hc.kept hK4, fun ht => ?_⟩
  · refine hp4.trans ((hc.live.erase _).trans ?_)
    rw [List.erase_cons_head]
  · exact intFree_tcNone hC hc.wf hc.mem (by rw [hpc]; exact h) (by rw [hc.thread]; exact ht)

theorem closed_total (hC : C.Ok) {l N : Local} {t os : Nat} (hc : Closed C l N t os) :
    ∃ l₄, intFree C N t = .ok l₄ := by
  have hpc : t + C.hdr - C.hdr = t := by omega
  obtain ⟨l₄, h⟩ := totalFree C hC N hc.wf hc.sp _ _ hc.mem
  rw [hpc] at h
  exact ⟨l₄, h⟩

variable (C) in
/-- `sysmalloc`'s end after a new top: free the closed old top, then the final carve. -/
def tailEnd (cs : Option Nat × Local) (nb : Nat) : Res (Nat × Local) := do
  let l ← freeOldTop C cs.2 cs.1
  return sysCarve C l nb

/-- **The new top, non-contiguous**. -/
theorem tail_nc {l : Local} {k : KernelSt} {nb b size : Nat} {snd : Option Nat}
    (hsnd : snd.getD k.brk = b + size)
    (hnext : ¬ (l.av.tiles.start ≠ 0 ∧ b = l.av.tiles.top + topSz l.av.tiles ∧ snd = none)) :
    mainTail C (setNC l k true) nb (topSz l.av.tiles) (l.av.tiles.top + topSz l.av.tiles) b snd size =
      tailEnd C (closeSegment C (grown l k (newBase l b) (preTiles l true size)) b size true) nb := by
  unfold mainTail setNC
  dsimp only
  split
  · rename_i hc; exact absurd hc hnext
  · split
    · rename_i hc; simp at hc
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      dsimp only [withTiles]
      rw [hsnd, Nat.add_sub_cancel_left]
      rfl

/-- **The new top, contiguous** (the first `sbrk`: no heap yet, so no correction). -/
theorem tail_c (hC : C.Ok) {l : Local} {k : KernelSt} {nb b size : Nat} (hs0 : l.av.tiles.start = 0)
    (hb : b % C.page = 0) (hsz : size % C.page = 0) (hkb : k.brk = b + size) :
    mainTail C (setNC l k false) nb (topSz l.av.tiles) (l.av.tiles.top + topSz l.av.tiles) b none size =
      tailEnd C (closeSegment C (grown l k (newBase l b) (preTiles l false size)) b size true) nb := by
  have hz : topSz l.av.tiles = 0 := by simp [topSz, hs0]
  have hA := hC.align; have hP := hC.page; have hS := hC.sizeSz
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  have hf : (b + C.hdr) % C.align = 0 := by rw [hA, hhdr]; rw [hP] at hb; omega
  have ha : alignUp (b + size) C.page = b + size := by
    unfold alignUp; rw [hP] at hb hsz ⊢; omega
  rw [hz]
  unfold mainTail setNC
  dsimp only
  split
  · rename_i hc; exact absurd hs0 hc.1
  · split
    · rename_i hc; simp at hc
    · simp only [Bool.not_false, ↓reduceIte, ne_eq, not_true_eq_false, hf, gt_iff_lt, Nat.lt_irrefl,
        Nat.add_zero, ha, Nat.sub_self]
      dsimp only [withTiles]
      rw [sbrk_zero]
      dsimp only
      rw [hkb, Nat.add_sub_cancel_left]
      rfl

/-- **The contiguous extension of top.** -/
theorem tail_ext {l : Local} {k : KernelSt} {nb b size : Nat} {snd : Option Nat}
    (hext : l.av.tiles.start ≠ 0 ∧ b = l.av.tiles.top + topSz l.av.tiles ∧ snd = none) :
    mainTail C (setNC l k l.av.tiles.noncontig) nb (topSz l.av.tiles) (l.av.tiles.top + topSz l.av.tiles) b snd size =
      .ok (sysCarve C (grown l k (newBase l b) (extTiles l size)) nb) := by
  unfold mainTail setNC
  dsimp only
  split
  · rfl
  · rename_i hc; exact absurd hext hc

/-- **The rest of `sysmallocMain`, case by case**: the contiguous extension (an `MStep` then the
carve), or a new top (non-contiguous, or the first `sbrk`), whose end frees the closed old top. -/
theorem tail_cases (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) (hi : l.shared.init = true)
    (hmn : l.isMain = true) {k : KernelSt} {nc : Bool} {b size nb : Nat} {snd : Option Nat}
    (G : Grant C l k b size)
    (hsnd : (snd = none ∧ k.brk = b + size ∧ b = l.kernel.brk ∧ nc = l.av.tiles.noncontig) ∨
      (snd = some (b + size) ∧ nc = true ∧ k.brk = l.kernel.brk)) :
    (∃ E, mainTail C (setNC l k nc) nb (topSz l.av.tiles) (l.av.tiles.top + topSz l.av.tiles) b snd size =
        .ok (sysCarve C E nb) ∧ MStep C l E) ∨
    (∃ L, mainTail C (setNC l k nc) nb (topSz l.av.tiles) (l.av.tiles.top + topSz l.av.tiles) b snd size =
        tailEnd C (closeSegment C L b size true) nb ∧
      (((closeSegment C L b size true).1 = none ∧ MStep C l (closeSegment C L b size true).2) ∨
        ∃ t os, (closeSegment C L b size true).1 = some t ∧ Closed C l (closeSegment C L b size true).2 t os)) := by
  obtain ⟨-, ⟨mb1, mb2, mb3, mb4⟩⟩ := hw.main hmn
  by_cases hext : l.av.tiles.start ≠ 0 ∧ b = l.av.tiles.top + topSz l.av.tiles ∧ snd = none
  · -- the contiguous extension
    have hnc : nc = l.av.tiles.noncontig := by
      rcases hsnd with ⟨-, -, -, h⟩ | ⟨h, -, -⟩
      · exact h
      · rw [hext.2.2] at h; cases h
    have hkb : k.brk = b + size := by
      rcases hsnd with ⟨-, h, -, -⟩ | ⟨h, -, -⟩
      · exact h
      · rw [hext.2.2] at h; cases h
    subst hnc
    exact .inl ⟨_, tail_ext hext, ext_step hC hw hsp hi hmn G hext.1 hext.2.1 hkb⟩
  · cases hnc : nc with
    | true =>
      have hsg : snd.getD k.brk = b + size := by
        rcases hsnd with ⟨rfl, h, -, -⟩ | ⟨rfl, -, -⟩
        · exact h
        · rfl
      exact .inr ⟨_, tail_nc hsg hext, newtop hC hw hsp hi hmn G (fun h => by cases h)⟩
    | false =>
      rw [hnc] at hsnd
      obtain ⟨rfl, hkb, hbb, hnc'⟩ : snd = none ∧ k.brk = b + size ∧ b = l.kernel.brk ∧ false = l.av.tiles.noncontig := by
        rcases hsnd with h | ⟨-, h, -⟩
        · exact h
        · cases h
      have hs0 : l.av.tiles.start = 0 := by
        refine Classical.byContradiction fun hs0 => hext ⟨hs0, ?_, rfl⟩
        have := ((mb4 hs0).2 hnc'.symm).2
        have hz : topSz l.av.tiles = l.av.tiles.topSize := by simp [topSz, hs0]
        rw [hz]; omega
      exact .inr ⟨_, tail_c hC hs0 G.aligned.1 G.aligned.2 hkb,
        newtop hC hw hsp hi hmn G (fun _ => ⟨hs0, hbb, hkb⟩)⟩

/-! ## The main-arena part of `sysmalloc` -/

theorem tailEnd_none {nb : Nat} {cs : Option Nat × Local} (h : cs.1 = none) :
    tailEnd C cs nb = .ok (sysCarve C cs.2 nb) := by
  obtain ⟨fr, N⟩ := cs
  simp only at h; subst h; rfl

theorem tailEnd_some {nb : Nat} {cs : Option Nat × Local} {t : Nat} (h : cs.1 = some t) :
    tailEnd C cs nb = (intFree C cs.2 t).bind fun l => .ok (sysCarve C l nb) := by
  obtain ⟨fr, N⟩ := cs
  simp only at h; subst h; rfl

/-- **`Algo.sysMainBody`**: `sysmalloc`'s main-arena part is a body. -/
theorem sysMainBody (C : Config) : Task.algo.sysMainBody C := by
  intro hC l l' n nb p hw hsp hi hmn hnb hlt h
  rcases sysmallocMain_cut C h with ⟨hg, hc⟩ | ⟨b, snd, size, hg, ht⟩
  · obtain ⟨k, h2, h3, h4, h5⟩ := mainGot_none hg
    rw [h2] at hc
    have hS := kernel_step hw hsp h3 h4 h5
    have hB := sysCarve_body hC hS.1 (hS.sp hC hw hsp) hnb (l := { l with kernel := k })
    rw [hc] at hB
    exact MBody.of_step hC hw hsp hS hB
  · obtain ⟨k, nc, h2, G, hsnd⟩ := mainGot_some hC hw hmn hlt hg
    rw [h2] at ht
    rcases tail_cases (nb := nb) hC hw hsp hi hmn G hsnd with ⟨E, hE, hS⟩ | ⟨L, hL, hN⟩
    · rw [hE] at ht
      injection ht with ht
      have hB := sysCarve_body hC hS.1 (hS.sp hC hw hsp) hnb (l := E)
      rw [ht] at hB
      exact MBody.of_step hC hw hsp hS hB
    · rw [hL] at ht
      rcases hN with ⟨hfr, hS⟩ | ⟨t, os, hfr, hcl⟩
      · rw [tailEnd_none hfr] at ht
        injection ht with ht
        have hB := sysCarve_body hC hS.1 (hS.sp hC hw hsp) hnb (l := (closeSegment C L b size true).2)
        rw [ht] at hB
        exact MBody.of_step hC hw hsp hS hB
      · rw [tailEnd_some hfr] at ht
        cases hI : intFree C (closeSegment C L b size true).2 t with
        | error e => rw [hI] at ht; cases ht
        | ok l₄ =>
          rw [hI] at ht
          injection ht with ht
          have hS := closed_step hC hw hsp hcl hI
          have hB := sysCarve_body hC hS.1 (hS.sp hC hw hsp) hnb (l := l₄)
          rw [ht] at hB
          exact MBody.of_step hC hw hsp hS hB

/-- **`Algo.sysMainTotal`**: `sysmalloc`'s main-arena part does not abort. -/
theorem sysMainTotal (C : Config) : Task.algo.sysMainTotal C := by
  intro hC l n nb hw hsp hmn hnb hlt
  refine sysmallocMain_of C (fun hg0 => ?_) fun b snd size hg => ?_
  · unfold sysmallocMain
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · rename_i b snd size heq
      have : (mainGot C l nb).1 = some (b, snd, size) := heq
      rw [hg0] at this; cases this
  · obtain ⟨k, nc, h2, G, hsnd⟩ := mainGot_some hC hw hmn hlt hg
    rw [h2]
    by_cases hi : l.shared.init = true
    · rcases tail_cases (nb := nb) hC hw hsp hi hmn G hsnd with ⟨E, hE, -⟩ | ⟨L, hL, hN⟩
      · exact ⟨_, hE⟩
      · rw [hL]
        rcases hN with ⟨hfr, -⟩ | ⟨t, os, hfr, hcl⟩
        · exact ⟨_, tailEnd_none hfr⟩
        · rw [tailEnd_some hfr]
          obtain ⟨l₄, hI⟩ := closed_total hC hcl
          rw [hI]; exact ⟨_, rfl⟩
    · -- before `ptmalloc_init` there is no heap: nothing to close, nothing to free
      have hs0 : l.av.tiles.start = 0 := (hw.init (by simpa using hi)).1
      have hext : ¬ (l.av.tiles.start ≠ 0 ∧ b = l.av.tiles.top + topSz l.av.tiles ∧ snd = none) :=
        fun h => h.1 hs0
      have hfr : ∀ L : Local, L.av.tiles.start = 0 → (closeSegment C L b size true).1 = none := by
        intro L hL
        obtain ⟨segs, fr, hcs, hc⟩ := closeSeg_spec hC L b size (fun h => absurd hL h)
        rw [hcs]
        rcases hc with ⟨-, -, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · rfl
        · exact absurd hL h
        · exact absurd hL h
      cases hnc : nc with
      | true =>
        subst hnc
        have hsg : snd.getD k.brk = b + size := by
          rcases hsnd with ⟨rfl, h, -, -⟩ | ⟨rfl, -, -⟩
          · exact h
          · rfl
        rw [tail_nc hsg hext]
        exact ⟨_, tailEnd_none (hfr _ hs0)⟩
      | false =>
        subst hnc
        obtain ⟨rfl, hkb, -, -⟩ : snd = none ∧ k.brk = b + size ∧ b = l.kernel.brk ∧ false = l.av.tiles.noncontig := by
          rcases hsnd with h | ⟨-, h, -⟩
          · exact h
          · cases h
        rw [tail_c hC hs0 G.aligned.1 G.aligned.2 hkb]
        exact ⟨_, tailEnd_none (hfr _ hs0)⟩

/-- **`Task.algo.bodyMalloc` conditional only on `sysmalloc`'s non-main part.** -/
theorem bodyMalloc_heap (C : Config) (hheap : Task.algo.sysHeapBody C) : Task.algo.bodyMalloc C :=
  bodyMalloc_cons C (sysMainBody C) hheap

/-- **`Task.algo.totalMalloc` conditional only on `sysmalloc`'s non-main part.** -/
theorem totalMalloc_heap (C : Config) (hheapT : Task.algo.sysHeapTotal C) : Task.algo.totalMalloc C :=
  totalMalloc_cons C (sysMainTotal C) hheapT

end Silmaril.Libc.Ptmalloc.Algo
