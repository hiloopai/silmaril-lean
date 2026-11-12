module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcPutCore
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.Frame

/-!
# ptmalloc x86sim: what `free`'s tcache path reads from the representation (any version)

Layer-(c) facts the x86 composition of `free`'s tcache path needs, stated for any `Config` and
`Layout` (no code, no version):

* `mem_arenaFrag_hdr`: every chunk of the arena has its size word (`size`, plus `PREV_INUSE` or
  not) in the arena's fragment (`Silmaril.Data.BoundaryTag.run`): so `IS_MMAPPED` and
  `NON_MAIN_ARENA` read 0 (the representation does not yet set `NON_MAIN_ARENA` for chunks of
  non-main arenas; see the module docstring of `V239.FreePath`);
* `mem_tcacheFrag_linkAt`: the link cell of every entry of a tcache bin (not only the head's);
* `exists_cell_of_backed`: backed, writable bytes hold some cell (the client's `e->key` word);
* `store_id`: storing a cell that already holds changes nothing (`errno := errno`);
* `localAt_view`: `LocalAt` reads only the memory view;
* `touch_*`: the bytes `LocalAt` reads (`RepTouches`), for the frame lemmas.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (MState Word)
open Silmaril.Process (Memory)
open Silmaril.Data
open Silmaril.Data.SepList (SLinks slist)
namespace Silmaril.Libc.Ptmalloc.X86sim

/-! ## Chunk headers -/

theorem mem_run_hdr (T : Silmaril.Data.BoundaryTag.Tag) :
    ∀ (pf : Bool) (bs : List Silmaril.Data.BoundaryTag.Blk) (b : Silmaril.Data.BoundaryTag.Blk), b ∈ bs →
      ∃ f, (f = 0 ∨ f = T.prevInuse) ∧
        (⟨b.addr + T.sizeOff, T.ws, b.size + f⟩ : Cell) ∈ Silmaril.Data.BoundaryTag.run T pf bs
  | _, [], _, h => absurd h List.not_mem_nil
  | pf, c :: cs, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨if pf then 0 else T.prevInuse, by split <;> simp, by
        simp [Silmaril.Data.BoundaryTag.run]⟩
    · obtain ⟨f, hf, hm⟩ := mem_run_hdr T c.free cs b h
      exact ⟨f, hf, by
        simp only [Silmaril.Data.BoundaryTag.run]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)⟩

theorem mem_tilesFrag_hdr {C : Config} {L : Layout} {avAddr : Nat} {ts : TopSt} {ch : Chunk}
    (h : ch ∈ ts.heapChunks) :
    ∃ f, (f = 0 ∨ f = 1) ∧ (⟨ch.addr + 8, 8, ch.size + f⟩ : Cell) ∈ tilesFrag C L avAddr ts := by
  unfold TopSt.heapChunks at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨g, hg, hc⟩ := List.mem_flatMap.1 h
    obtain ⟨f, hf, hm⟩ := mem_run_hdr chunkTag false _ ch.blk (List.mem_map.2 ⟨ch, hc, rfl⟩)
    refine ⟨f, hf, ?_⟩
    unfold tilesFrag
    refine List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨g, hg, List.mem_append_left _ ?_⟩)))
    simpa [chunkTag, Chunk.blk] using hm
  · obtain ⟨f, hf, hm⟩ := mem_run_hdr chunkTag false _ ch.blk (List.mem_map.2 ⟨ch, h, rfl⟩)
    refine ⟨f, hf, ?_⟩
    unfold tilesFrag
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    simpa [chunkTag, Chunk.blk] using hm

/-- **Every chunk's size word is in the arena's fragment.** -/
theorem mem_arenaFrag_hdr {C : Config} {L : Layout} {avAddr : Nat} {av : ArenaSt} {ch : Chunk}
    (h : ch ∈ av.chunks) :
    ∃ f, (f = 0 ∨ f = 1) ∧ (⟨ch.addr + 8, 8, ch.size + f⟩ : Cell) ∈ arenaFrag C L avAddr av := by
  obtain ⟨f, hf, hm⟩ := mem_tilesFrag_hdr (C := C) (L := L) (avAddr := avAddr) h
  refine ⟨f, hf, ?_⟩
  unfold arenaFrag
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ hm)))

/-- **Every chunk's size word is in an initialised arena's representation** (`arenaRep` is
`arenaFrag` once `__malloc_initialized` is set, D1). -/
theorem mem_arenaRep_hdr {C : Config} {L : Layout} {init : Bool} {avAddr : Nat} {av : ArenaSt}
    {ch : Chunk} (hinit : init = true) (h : ch ∈ av.chunks) :
    ∃ f, (f = 0 ∨ f = 1) ∧ (⟨ch.addr + 8, 8, ch.size + f⟩ : Cell) ∈ arenaRep C L init avAddr av := by
  subst hinit; exact mem_arenaFrag_hdr h

/-! ## Tcache links -/

theorem mem_slist_suffix (K : SLinks) {x : Nat} {xs : List Nat} :
    ∀ l : List Nat, (x :: xs) <:+ l → (⟨x + K.link, K.ws, K.enc (x + K.link) (xs.headD K.nil)⟩ : Cell) ∈ slist K l
  | [], h => by simp at h
  | y :: ys, h => by
    rcases List.suffix_cons_iff.1 h with h | h
    · cases h; simp [slist]
    · simp only [slist]; exact List.mem_cons_of_mem _ (mem_slist_suffix K ys h)

theorem mem_tcacheFrag_suffix {C : Config} {L : Layout} {key : Nat} {tc : TcacheSt} {i : Nat}
    {c : Nat × Nat} {rest : List (Nat × Nat)} (hi : i < C.tcacheBins) (hb : (c :: rest) <:+ tc.bins i) :
    (⟨c.1 + C.hdr + 0, 8, C.protect (c.1 + C.hdr + 0) ((rest.map (·.1 + C.hdr)).headD 0)⟩ : Cell) ∈
      tcacheFrag C L key tc := by
  unfold tcacheFrag
  refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))⟩
  have := mem_slist_suffix (tcLinks C) (x := c.1 + C.hdr) (xs := rest.map (·.1 + C.hdr))
    ((tc.bins i).map (·.1 + C.hdr)) (by simpa using hb.map (·.1 + C.hdr))
  simpa [tcLinks] using this

/-- **The link cell of entry `j` of tcache bin `i`.** -/
theorem mem_tcacheFrag_linkAt {C : Config} {L : Layout} {key : Nat} {tc : TcacheSt} {i j : Nat}
    (hi : i < C.tcacheBins) (hj : j < (tc.bins i).length) :
    let ps := (tc.bins i).map (·.1 + C.hdr)
    (⟨ps.getD j 0 + 0, 8, C.protect (ps.getD j 0 + 0) (ps.getD (j + 1) 0)⟩ : Cell) ∈ tcacheFrag C L key tc := by
  intro ps
  have hd : (tc.bins i).drop j = (tc.bins i)[j] :: (tc.bins i).drop (j + 1) := List.drop_eq_getElem_cons hj
  have hsuf : ((tc.bins i)[j] :: (tc.bins i).drop (j + 1)) <:+ tc.bins i := hd ▸ List.drop_suffix _ _
  have hm := mem_tcacheFrag_suffix (L := L) (key := key) hi hsuf
  have e1 : ps.getD j 0 = (tc.bins i)[j].1 + C.hdr := by
    simp [ps, List.getD_eq_getElem?_getD, hj]
  have e2 : ps.getD (j + 1) 0 = (((tc.bins i).drop (j + 1)).map (·.1 + C.hdr)).headD 0 := by
    simp only [ps, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h : (tc.bins i)[j + 1]? with
    | none =>
      have : (tc.bins i).length ≤ j + 1 := List.getElem?_eq_none_iff.1 h
      simp [List.drop_eq_nil_of_le this]
    | some c =>
      obtain ⟨hl, hc⟩ := List.getElem?_eq_some_iff.1 h
      rw [List.drop_eq_getElem_cons hl]
      simp [hc]
  rw [e1, e2]; exact hm

/-! ## Memory views -/

/-- Backed, writable bytes hold some cell. -/
theorem exists_cell_of_backed {v : MemView} :
    ∀ (k a : Nat), (∀ j < k, (v.byte (a + j)).isSome = true ∧ v.writable (a + j) = true) →
      ∃ x, (⟨a, k, x⟩ : Cell).Holds v
  | 0, a, _ => ⟨0, by simp [Cell.Holds, MemView.load]⟩
  | k + 1, a, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h 0 (by omega)).1
    rw [Nat.add_zero] at hb
    obtain ⟨r, hr, -⟩ := exists_cell_of_backed k (a + 1) fun j hj => by
      have := h (j + 1) (by omega); rwa [show a + (j + 1) = a + 1 + j by omega] at this
    refine ⟨b + 256 * r, ?_, fun j hj => (h j hj).2⟩
    simp only [MemView.load] at hr ⊢
    simp [hb, hr]

theorem bytes_of_load {v : MemView} (hs : SaneView v) :
    ∀ (k a x : Nat), v.load a k = some x → ∀ j < k, v.byte (a + j) = some (x / 256 ^ j % 256)
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, a, x, h, j, hj => by
    simp only [MemView.load] at h
    cases hb : v.byte a with
    | none => simp [hb] at h
    | some b =>
      cases hr : v.load (a + 1) k with
      | none => simp [hb, hr] at h
      | some r =>
        simp only [hb, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        have hb256 := (hs a b hb).1
        subst h
        cases j with
        | zero => simp [hb]; omega
        | succ j =>
          have := bytes_of_load hs k (a + 1) r hr j (by omega)
          have e : (b + 256 * r) / 256 = r := by omega
          rw [show a + (j + 1) = a + 1 + j by omega, this, Nat.pow_succ', ← Nat.div_div_eq_div_mul, e]

/-- **Storing a cell that already holds changes nothing.** -/
theorem store_id {v : MemView} (hs : SaneView v) {c : Cell} (h : v.load c.addr c.width = some c.val) :
    v.store c = v := by
  have hb := bytes_of_load hs c.width c.addr c.val h
  cases v with
  | mk byte wr =>
    simp only [MemView.store, MemView.mk.injEq, and_true]
    funext a
    split
    · next ha =>
      have := hb (a - c.addr) (by omega)
      rw [show c.addr + (a - c.addr) = a by omega] at this
      exact this.symm
    · rfl

/-- `LocalAt` reads only the memory view. -/
theorem localAt_view {C : Config} {P : RepAt} {x : AState} {s s' : MState}
    (h : LocalAt C P fsMach x s) (he : memView s'.memory = memView s.memory) : LocalAt C P fsMach x s' := by
  have : fsMach.view s' = fsMach.view s := he
  unfold LocalAt at h ⊢
  rw [this]; exact h

/-! ## The bytes `LocalAt` reads -/

theorem touch_rep {C : Config} {P : RepAt} {x : AState} {c : Cell}
    (hc : c ∈ arenaRep C P.layout x.1.shared.init x.1.avAddr x.1.av ++
      threadFrag C P.layout P.tls x.1.avAddr x.1.shared.key x.1.shared.init x.1.thread ++
      sharedFrag C P.layout P.statics x.1.shared) {k : Nat} (hk : k < c.width) :
    RepTouches C P x (c.addr + k) :=
  .inl (mem_bytes hc hk)

theorem touch_env {C : Config} {P : RepAt} {x : AState} {c : Cell}
    (hc : c ∈ envFrag C P.layout P.env x.2.1) {k : Nat} (hk : k < c.width) :
    RepTouches C P x (c.addr + k) :=
  .inr (.inl (mem_bytes hc hk))

theorem touch_span {C : Config} {P : RepAt} {x : AState} {d : Chunk} (hd : d ∈ x.1.av.chunks)
    {k : Nat} (hk : k < d.size + 8) : RepTouches C P x (d.addr + k) :=
  .inr (.inr ⟨(d.addr, d.size + 8), mem_spans hd, by simp, by simp; omega⟩)

/-- An address range `LocalAt` reads is apart from a window it does not read. -/
theorem apart_of_touch {C : Config} {P : RepAt} {x : AState} {lo hi a k : Nat}
    (hst : ∀ b, lo ≤ b → b < hi → ¬ RepTouches C P x b) (h : ∀ j < k, RepTouches C P x (a + j)) :
    Apart a k lo hi := fun j hj ⟨h1, h2⟩ => hst _ h1 h2 (h j hj)

end Silmaril.Libc.Ptmalloc.X86sim
