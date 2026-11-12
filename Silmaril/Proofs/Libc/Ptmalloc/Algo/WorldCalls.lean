module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.WorldOps
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Malloc

/-!
# ptmalloc algorithm: `malloc` and `free` at world level

`Algo.wfWorld_of` and `Algo.mallocTotal_of`: `Task.algo.wfWorld` and `Task.algo.mallocTotal`
for the model from the body obligations `Task.algo.{bodyMalloc, bodyFree, totalMalloc,
totalFree}` (and the proved `munmap_chunk` path).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- **A calm world step**: `WorldWF` kept, the live set unchanged up to order. -/
structure Calm (C : Config) (w w' : World) : Prop where
  wf : WorldWF C w'
  live : (w'.live C).Perm (w.live C)
  tids : w'.tids = w.tids
  init : w'.shared.init = w.shared.init
  main : w'.mainArena = w.mainArena
  /-- A live chunk of an arena stays a chunk of that arena. -/
  keep : ∀ b av d, w.arenas b = some av → d ∈ av.chunks → d.use = .client →
    (d.addr + C.hdr, d.size - C.sizeSz) ∈ w.live C → ∃ av', w'.arenas b = some av' ∧ d ∈ av'.chunks

theorem Quiet.calm {w w' : World} (h : Quiet C w w') : Calm C w w' :=
  ⟨h.wf, h.live, h.tids, h.init, h.main, fun b av _ hb hd _ _ => ⟨av, h.arenasKept b av hb, hd⟩⟩

theorem Calm.refl {w : World} (hw : WorldWF C w) : Calm C w w :=
  ⟨hw, List.Perm.refl _, rfl, rfl, rfl, fun _ av _ hb hd _ _ => ⟨av, hb, hd⟩⟩

theorem Calm.trans {w₁ w₂ w₃ : World} (h₁ : Calm C w₁ w₂) (h₂ : Calm C w₂ w₃) : Calm C w₁ w₃ :=
  ⟨h₂.wf, h₂.live.trans h₁.live, h₂.tids.trans h₁.tids, h₂.init.trans h₁.init, h₂.main.trans h₁.main,
    fun b av d hb hd hu hl => by
      obtain ⟨av₂, hb₂, hd₂⟩ := h₁.keep b av d hb hd hu hl
      exact h₂.keep b av₂ d hb₂ hd₂ hu (h₁.live.symm.subset hl)⟩

theorem live_ge_hdr {w : World} {y : Nat × Nat} (hy : y ∈ w.live C) : C.hdr ≤ y.1 := by
  rcases mem_live.mp hy with ⟨⟨b, -, av, -, hyb⟩, -⟩ | hm
  · obtain ⟨d, -, -, rfl⟩ := mem_out.mp hyb; simp
  · obtain ⟨d, -, -, rfl⟩ := mem_shlive.mp hm; simp

/-- A lent-out chunk not freed stays a chunk of its arena after a put. -/
theorem put_keep {w : World} {tid a : Nat} {l l' : Local} {freed : List (Nat × Nat)}
    (hl : w.local? tid a = some l) (hF : Frame C l l' freed) {b : Nat} {av : ArenaSt} {d : Chunk}
    (hb : w.arenas b = some av) (hd : d ∈ av.chunks) (hu : d.use = .client)
    (hnf : (d.addr + C.hdr, d.size - C.sizeSz) ∉ freed) :
    ∃ av', (w.put tid l').arenas b = some av' ∧ d ∈ av'.chunks := by
  obtain ⟨av₀, hav, hlav, -⟩ := local?_fields hl
  rw [put_arenas hl hF]
  by_cases hba : b = a
  · subst hba; rw [hav] at hb; cases hb
    exact ⟨l'.av, by simp, hF.clients d (by rw [hlav]; exact hd) hu (by simpa [usable] using hnf)⟩
  · exact ⟨av, by simp [hba, hb], hd⟩

/-! ## A `malloc` body, put back -/

theorem body_put (hC : C.Ok) (hB : Task.algo.bodyMalloc C) {w : World} (hw : WorldWF C w)
    (hi : w.shared.init = true)
    {tid a : Nat} (ht : tid ∈ w.tids) {l : Local} (hl : Ops.localAt w tid a = .ok l) {n p : Nat}
    {l' : Local} (hm : intMalloc C l n = .ok (p, l')) :
    WorldWF C (w.put tid l') ∧ MallocLive C n p (w.live C) ((w.put tid l').live C) ∧
      MallocLive C n p (l.live C) (l'.live C) ∧ Frame C l l' [] ∧
      (w.put tid l').shared.init = w.shared.init ∧
      (l.thread.tcache = none → l'.thread.tcache = none) ∧ l.thread = w.threads tid ∧
      l.avAddr = a := by
  have hl' := localAt_inv hl
  have hil : l.shared.init = true := by
    obtain ⟨-, -, -, -, -, -, hls, -⟩ := local?_fields hl'; rw [hls]; exact hi
  obtain ⟨⟨hwf', -, hML⟩, hF, hK, htn⟩ :=
    hB hC l l' n p (hw.locals tid a l ht hl') (localSp hw ht hl') hil hm
  have := put_malloc hC hw ht hl' hwf' hF hK hML
  obtain ⟨av, hav, hlav, hla, hlm, hlt, hls, hlk⟩ := local?_fields hl'
  exact ⟨this.1, this.2, hML, hF, by show l'.shared.init = _; rw [hF.init, hls], htn, hlt, hla⟩

/-- Where a fresh payload of a body lies, after the put. -/
theorem body_loc {w : World} {tid a : Nat} {l l' : Local} {freed : List (Nat × Nat)}
    (hla : l.avAddr = a) (hF : Frame C l l' freed) {y : Nat × Nat} (hy : y ∈ l'.live C) :
    (∃ av, (w.put tid l').arenas a = some av ∧ y ∈ av.out C) ∨ y ∈ (w.put tid l').shared.live C := by
  rcases mem_llive.mp hy with ⟨hyo, -⟩ | hys
  · left; exact ⟨l'.av, by simp [World.put, hF.avAddr, hla], hyo⟩
  · right; exact hys

/-! ## `tcache_init` -/

theorem live_of_parked {w w' : World} (hA : w'.arenaAddrs = w.arenaAddrs) (har : w'.arenas = w.arenas)
    (htids : w'.tids = w.tids) (hmm : w'.shared.mm = w.shared.mm)
    (hpk : ∀ t, (w'.threads t).parked C = (w.threads t).parked C) : w'.live C = w.live C := by
  simp [World.live, hA, har, htids, hpk, SharedSt.live, hmm]

/-- Install the empty tcache at payload `p` for a thread without one. -/
theorem setTcache_wf (hC : C.Ok) {w : World} (hw : WorldWF C w) {tid p : Nat} (ht : tid ∈ w.tids)
    (hi : w.shared.init = true) (hp : p ≠ 0) (hnone : (w.threads tid).tcache = none) :
    WorldWF C { w with threads := fun x => if x = tid then
        { w.threads x with tcache := some { addr := p, bins := fun _ => [] } } else w.threads x } ∧
      ({ w with threads := fun x => if x = tid then
        { w.threads x with tcache := some { addr := p, bins := fun _ => [] } } else w.threads x } :
          World).live C = w.live C := by
  have hmain : w.mainArena ∈ w.arenaAddrs := List.mem_cons_self ..
  obtain ⟨l, hl⟩ := local?_of_mem hw hmain tid
  obtain ⟨av, hav, hlav, hla, hlm, hlt, hls, hlk⟩ := local?_fields hl
  have hwf := put_thread_wf hC hw ht hl { l.thread with tcache := some { addr := p, bins := fun _ => [] } }
    (fun tc htc => by
      cases htc
      exact { bins := fun _ _ => rfl
              nodup := fun _ => ⟨List.nodup_nil, Nat.zero_le _⟩
              size := fun _ _ h => by cases h
              nonNull := fun _ _ h => by cases h
              struct := hp })
    (fun tc' i e htc he => by cases htc; cases he) rfl (fun h => by rw [hls, hi] at h; cases h)
  have heq : w.put tid { l with thread := { l.thread with tcache := some { addr := p, bins := fun _ => [] } } } =
      { w with threads := fun x => if x = tid then
        { w.threads x with tcache := some { addr := p, bins := fun _ => [] } } else w.threads x } := by
    have harr : ∀ x, (if x = w.mainArena then some l.av else w.arenas x) = w.arenas x := fun x => by
      by_cases hx : x = w.mainArena
      · subst hx; rw [hav, hlav]; simp
      · simp [hx]
    simp only [World.put, hla, hls, hlk, harr, hlt]
    congr 1
    funext x; by_cases hx : x = tid
    · subst hx; simp
    · simp [hx]
  rw [← heq]
  refine ⟨hwf, ?_⟩
  rw [heq]
  refine live_of_parked rfl rfl rfl rfl fun t => ?_
  by_cases htt : t = tid
  · subst htt; simp [ThreadSt.parked, TcacheSt.payloads, hnone]
  · simp [htt]

/-- The last steps of `tcache_init`: hold the struct, install the tcache. -/
theorem tcFinish (hC : C.Ok) {w : World} (hw : WorldWF C w) {tid a p u : Nat} (ht : tid ∈ w.tids)
    (hi : w.shared.init = true) (ha : a ∈ w.arenaAddrs) (hp : p ≠ 0) (hpu : (p, u) ∈ w.live C)
    (hloc : (∃ av, w.arenas a = some av ∧ (p, u) ∈ av.out C) ∨ (p, u) ∈ w.shared.live C)
    (hnone : (w.threads tid).tcache = none) :
    WorldWF C { markInternal C w a p with threads := fun x => if x = tid then
        { (markInternal C w a p).threads x with tcache := some { addr := p, bins := fun _ => [] } }
        else (markInternal C w a p).threads x } ∧
      (({ markInternal C w a p with threads := fun x => if x = tid then
        { (markInternal C w a p).threads x with tcache := some { addr := p, bins := fun _ => [] } }
        else (markInternal C w a p).threads x } : World).live C).Perm ((w.live C).erase (p, u)) ∧
      ({ markInternal C w a p with threads := fun x => if x = tid then
        { (markInternal C w a p).threads x with tcache := some { addr := p, bins := fun _ => [] } }
        else (markInternal C w a p).threads x } : World).shared.init = w.shared.init ∧
      ({ markInternal C w a p with threads := fun x => if x = tid then
        { (markInternal C w a p).threads x with tcache := some { addr := p, bins := fun _ => [] } }
        else (markInternal C w a p).threads x } : World).mainArena = w.mainArena ∧
      ({ markInternal C w a p with threads := fun x => if x = tid then
        { (markInternal C w a p).threads x with tcache := some { addr := p, bins := fun _ => [] } }
        else (markInternal C w a p).threads x } : World).tids = w.tids := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := markInternal_wf hC hw ht ha hpu hloc
  have hs := setTcache_wf hC h1 (h3 ▸ ht) (h4.trans hi) hp (by rw [h5]; exact hnone)
  exact ⟨hs.1, by rw [hs.2]; exact h2, h4, h6, h3⟩

theorem markInternal_keep {w : World} {a q b : Nat} {av : ArenaSt} {d : Chunk}
    (hb : w.arenas b = some av) (hd : d ∈ av.chunks) (hne : d.addr ≠ q - C.hdr) :
    ∃ av', (markInternal C w a q).arenas b = some av' ∧ d ∈ av'.chunks := by
  by_cases hany : (w.shared.mm.chunks.any fun x => decide (x.addr = q - C.hdr)) = true
  · rw [markInternal_of_mm hany]; exact ⟨av, hb, hd⟩
  · rw [markInternal_of_arena hany]
    by_cases hba : b = a
    · subst hba
      refine ⟨{ av with tiles := av.tiles.relabel (q - C.hdr) .internal }, by simp [hb], ?_⟩
      show d ∈ (av.tiles.relabel (q - C.hdr) .internal).heapChunks
      rw [TopSt.heapChunks_relabel]; exact List.mem_map.mpr ⟨d, hd, Chunk.relabelAt_of_ne hne⟩
    · exact ⟨av, by simp [hba, hb], hd⟩

/-- A body that returns 0, put back: calm. -/
theorem body_put_zero (hC : C.Ok) (hB : Task.algo.bodyMalloc C) {w : World} (hw : WorldWF C w)
    (hi : w.shared.init = true) {tid a : Nat} (ht : tid ∈ w.tids) {l : Local} (hl : Ops.localAt w tid a = .ok l) {n : Nat}
    {l' : Local} (hm : intMalloc C l n = .ok (0, l')) : Calm C w (w.put tid l') := by
  obtain ⟨hw2, hML, -, -, hi2, -⟩ := body_put hC hB hw hi ht hl hm
  obtain ⟨-, -, -, hF, -⟩ := body_put hC hB hw hi ht hl hm
  rcases hML with ⟨-, hp⟩ | ⟨h0, -⟩
  · exact ⟨hw2, hp, rfl, hi2, rfl, fun b av d hb hd hu _ =>
      put_keep (localAt_inv hl) hF hb hd hu (by simp)⟩
  · exact absurd rfl h0

/-- A body that returns `q ≠ 0`, put back, the struct held and the tcache installed (the end of
`tcache_init`). -/
theorem tcBody (hC : C.Ok) (hB : Task.algo.bodyMalloc C) {w wB : World} {tid b q : Nat}
    {lB lB' : Local} (hc : Calm C w wB) (htB : tid ∈ wB.tids) (hiB : wB.shared.init = true)
    (hnB : (wB.threads tid).tcache = none) (hlB : Ops.localAt wB tid b = .ok lB)
    (hmB : intMalloc C lB (tcacheStructSize C) = .ok (q, lB')) (hq : q ≠ 0) :
    Calm C w { markInternal C (wB.put tid lB') b q with threads := fun x => if x = tid then
        { (markInternal C (wB.put tid lB') b q).threads x with tcache := some { addr := q, bins := fun _ => [] } }
        else (markInternal C (wB.put tid lB') b q).threads x } := by
  have hlB' := localAt_inv hlB
  have hilB : lB.shared.init = true := by
    obtain ⟨-, -, -, -, -, -, hls, -⟩ := local?_fields hlB'; rw [hls]; exact hiB
  obtain ⟨⟨hwf', -, hMLl⟩, hF, hK, htn⟩ :=
    hB hC lB lB' _ q (hc.wf.locals tid b lB htB hlB') (localSp hc.wf htB hlB') hilB hmB
  obtain ⟨hw2, hMLW, -, -, hi2, -, hlt, hla⟩ := body_put hC hB hc.wf hiB htB hlB hmB
  rcases hMLl with ⟨hq0, -⟩ | ⟨-, -, u, -, hpermL, hdis⟩
  · exact absurd hq0 hq
  rcases hMLW with ⟨hq0, -⟩ | ⟨-, -, u', -, hpermW, -⟩
  · exact absurd hq0 hq
  have hmem := put_malloc_new hC hc.wf htB hlB' hwf' hF hK hpermL hdis
  have hmem' : (q, u') ∈ (wB.put tid lB').live C := hpermW.symm.subset (List.mem_cons_self ..)
  have huu : (q, u) = (q, u') :=
    eq_of_fst_nodup (liveApart C hC _ hw2).start_unique hmem hmem' rfl
  rw [← huu] at hpermW
  have hloc := body_loc (w := wB) (tid := tid) hla hF (hpermL.symm.subset (List.mem_cons_self ..))
  have hb : b ∈ (wB.put tid lB').arenaAddrs := by
    rw [put_addrs hlB' hF]
    obtain ⟨av, hav, -⟩ := local?_fields hlB'
    exact hc.wf.mem_addrs hav
  have hn' : ((wB.put tid lB').threads tid).tcache = none := by
    show (if tid = tid then lB'.thread else wB.threads tid).tcache = none
    simp only [ite_true]; exact htn (by rw [hlt]; exact hnB)
  obtain ⟨f1, f2, f3, f4, f5⟩ := tcFinish hC hw2 htB (hi2.trans hiB) hb hq hmem hloc hn'
  have hqn : (q, u) ∉ wB.live C := by
    intro hin
    have hnd := live_nodup hC hw2
    rw [hpermW.nodup_iff] at hnd
    exact (List.nodup_cons.mp hnd).1 hin
  refine ⟨f1, f2.trans ?_, f5.trans hc.tids, f3.trans (hi2.trans hc.init), f4.trans hc.main, ?_⟩
  · refine ((hpermW.erase (q, u)).trans ?_).trans hc.live
    simp
  · intro b' av d hb' hd hu hdl
    obtain ⟨avB, hbB, hdB⟩ := hc.keep b' av d hb' hd hu hdl
    have hdlB : (d.addr + C.hdr, d.size - C.sizeSz) ∈ wB.live C := hc.live.symm.subset hdl
    obtain ⟨av₂, hb₂, hd₂⟩ := put_keep hlB' hF hbB hdB hu (by simp)
    have hdl₂ : (d.addr + C.hdr, d.size - C.sizeSz) ∈ (wB.put tid lB').live C :=
      hpermW.symm.subset (List.mem_cons_of_mem _ hdlB)
    have hne : d.addr ≠ q - C.hdr := by
      intro he
      have : (d.addr + C.hdr, d.size - C.sizeSz) = (q, u) :=
        eq_of_fst_nodup (liveApart C hC _ hw2).start_unique hdl₂ hmem
          (by have h1 := live_ge_hdr (C := C) hmem; simp only at h1 ⊢; omega)
      exact hqn (this ▸ hdlB)
    exact markInternal_keep hb₂ hd₂ hne

/-- **`tcache_init`** is calm (`init` done). -/
theorem tcacheInit_wf (hC : C.Ok) (hB : Task.algo.bodyMalloc C) {w w' : World} {tid : Nat}
    (hw : WorldWF C w) (ht : tid ∈ w.tids) (hi : w.shared.init = true)
    (h : tcacheInit C w tid = .ok w') : Calm C w w' := by
  unfold tcacheInit at h
  dsimp only at h
  split at h
  · injection h with h; subst h; exact Calm.refl hw
  rename_i hcond
  have hnone : (w.threads tid).tcache = none := by
    cases hx : (w.threads tid).tcache with
    | none => rfl
    | some _ => exact absurd (.inl (by simp [hx])) hcond
  obtain ⟨⟨a, w₁⟩, h1, h⟩ := bind_ok_inv h
  try dsimp only at h
  obtain ⟨q1, ha1⟩ := arenaGet_quiet hC hw ht hi h1
  have ht1 : tid ∈ w₁.tids := q1.tids ▸ ht
  have hi1 : w₁.shared.init = true := q1.init.trans hi
  have hn1 : (w₁.threads tid).tcache = none := (q1.tcache tid).trans hnone
  obtain ⟨l, hla, h⟩ := bind_ok_inv h
  try dsimp only at h
  obtain ⟨⟨p, l₁⟩, hm, h⟩ := bind_ok_inv h
  try dsimp only at h
  split at h
  · rename_i hp
    obtain ⟨x, hx, h⟩ := bind_ok_inv h
    injection hx with hx; subst hx; try dsimp only at h
    split at h
    · exact absurd ‹_› hp
    · injection h with h; subst h
      exact tcBody hC hB q1.calm ht1 hi1 hn1 hla hm hp
  · rename_i hp
    have hp0 : p = 0 := by simpa using hp
    subst hp0
    have c2 := body_put_zero hC hB q1.wf hi1 ht1 hla hm
    have c2' : Calm C w (w₁.put tid l₁) := q1.calm.trans c2
    obtain ⟨-, -, -, -, -, htn, hlt, -⟩ := body_put hC hB q1.wf hi1 ht1 hla hm
    have hn2 : ((w₁.put tid l₁).threads tid).tcache = none := by
      show (if tid = tid then l₁.thread else w₁.threads tid).tcache = none
      simp only [ite_true]; exact htn (by rw [hlt]; exact hn1)
    obtain ⟨⟨r, w₃⟩, h5, h⟩ := bind_ok_inv h
    try dsimp only at h
    obtain ⟨q3, hr3⟩ := arenaRetry_quiet hC c2'.wf (c2'.tids ▸ ht) (c2'.init.trans hi) h5
    have c3 := c2'.trans q3.calm
    have ht3 : tid ∈ w₃.tids := c3.tids ▸ ht
    have hi3 : w₃.shared.init = true := c3.init.trans hi
    have hn3 : (w₃.threads tid).tcache = none := (q3.tcache tid).trans hn2
    split at h
    · obtain ⟨x, hx, h⟩ := bind_ok_inv h
      injection hx with hx; subst hx; try dsimp only at h
      split at h
      · injection h with h; subst h; exact c3
      · exact absurd rfl ‹_›
    · obtain ⟨l₂, hl2, h⟩ := bind_ok_inv h
      try dsimp only at h
      obtain ⟨⟨p₂, l₃⟩, hm2, h⟩ := bind_ok_inv h
      try dsimp only at h
      obtain ⟨x, hx, h⟩ := bind_ok_inv h
      injection hx with hx; subst hx; try dsimp only at h
      by_cases hp2 : p₂ = 0
      · simp only [hp2, ite_true] at h
        injection h with h; subst h
        rw [hp2] at hm2
        exact c3.trans (body_put_zero hC hB c3.wf hi3 ht3 hl2 hm2)
      · simp only [hp2, ite_false] at h
        injection h with h; subst h
        exact tcBody hC hB c3 ht3 hi3 hn3 hl2 hm2 hp2

/-! ## `malloc` -/

theorem withArena_wf (hC : C.Ok) (hB : Task.algo.bodyMalloc C) {w w' : World} {tid nb n p : Nat}
    (hw : WorldWF C w) (ht : tid ∈ w.tids) (hi : w.shared.init = true)
    (h : (ptmalloc C).withArena w tid nb (fun l => (ptmalloc C).intMalloc l n) = .ok (p, w')) :
    WorldWF C w' ∧ MallocLive C n p (w.live C) (w'.live C) := by
  have hmain : w.mainArena ∈ w.arenaAddrs := List.mem_cons_self ..
  unfold Ops.withArena at h
  split at h
  · obtain ⟨l, hl, h⟩ := bind_ok_inv h
    try dsimp only at h
    obtain ⟨⟨p₁, l₁⟩, hm, h⟩ := bind_ok_inv h
    try dsimp only at h
    injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hw2, hML, -⟩ := body_put hC hB hw hi ht hl hm
    exact ⟨hw2, hML⟩
  · obtain ⟨⟨a, w₁⟩, h1, h⟩ := bind_ok_inv h
    try dsimp only at h
    obtain ⟨q1, -⟩ := arenaGet_quiet hC hw ht hi (h1 : arenaGet C w tid nb = _)
    have ht1 : tid ∈ w₁.tids := q1.tids ▸ ht
    obtain ⟨l, hl, h⟩ := bind_ok_inv h
    try dsimp only at h
    obtain ⟨⟨p₁, l₁⟩, hm, h⟩ := bind_ok_inv h
    try dsimp only at h
    by_cases hp1 : p₁ = 0
    · simp only [hp1, ne_eq, not_true_eq_false, ite_false] at h
      rw [hp1] at hm
      have c2 := q1.calm.trans (body_put_zero hC hB q1.wf (q1.init.trans hi) ht1 hl hm)
      obtain ⟨⟨r, w₃⟩, h2, h⟩ := bind_ok_inv h
      try dsimp only at h
      obtain ⟨q3, -⟩ := arenaRetry_quiet hC c2.wf (c2.tids ▸ ht) (c2.init.trans hi)
        (h2 : arenaRetry C _ tid a nb = _)
      have c3 := c2.trans q3.calm
      split at h
      · injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨c3.wf, .inl ⟨rfl, c3.live⟩⟩
      · obtain ⟨l₂, hl2, h⟩ := bind_ok_inv h
        try dsimp only at h
        obtain ⟨⟨p₂, l₃⟩, hm2, h⟩ := bind_ok_inv h
        try dsimp only at h
        injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hw4, hML, -⟩ := body_put hC hB c3.wf (c3.init.trans hi) (c3.tids ▸ ht) hl2 hm2
        exact ⟨hw4, MallocLive.perm_left c3.live hML⟩
    · simp only [ne_eq, hp1, not_false_eq_true, ite_true] at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hw2, hML, -⟩ := body_put hC hB q1.wf (q1.init.trans hi) ht1 hl hm
      exact ⟨hw2, MallocLive.perm_left q1.live hML⟩

theorem malloc_wf (hC : C.Ok) (hB : Task.algo.bodyMalloc C) {w w' : World} {tid n p : Nat}
    (hw : WorldWF C w) (ht : tid ∈ w.tids) (h : (ptmalloc C).malloc w tid n = .ok (p, w')) :
    WorldWF C w' ∧ MallocLive C n p (w.live C) (w'.live C) := by
  unfold Ops.malloc at h
  obtain ⟨w₁, h1, h⟩ := bind_ok_inv h
  try dsimp only at h
  obtain ⟨hw1, hl1, ht1, hi1, -, -⟩ := init_wf hw h1
  have ht1' : tid ∈ w₁.tids := ht1 ▸ ht
  split at h
  · injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have := setErrno_wf (tid := tid) (e := 12) hw1
    exact ⟨this.1, .inl ⟨rfl, by rw [this.2, hl1]⟩⟩
  · rename_i nb hnb
    obtain ⟨w₂, h2, h⟩ := bind_ok_inv h
    try dsimp only at h
    have c2 := tcacheInit_wf hC hB hw1 ht1' hi1 (h2 : tcacheInit C w₁ tid = _)
    have ht2 : tid ∈ w₂.tids := c2.tids ▸ ht1'
    have hlive2 : (w₂.live C).Perm (w.live C) := by rw [← hl1]; exact c2.live
    obtain ⟨l0, hl0, h⟩ := bind_ok_inv h
    try dsimp only at h
    split at h
    · rename_i p₁ l₁ hg
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      split at hg
      · have := tcacheGet_world hC c2.wf ht2 (localAt_inv hl0) hg hnb rfl
        exact ⟨this.1, MallocLive.perm_left hlive2 this.2⟩
      · cases hg
    · have := withArena_wf hC hB c2.wf ht2 (c2.init.trans hi1) h
      exact ⟨this.1, MallocLive.perm_left hlive2 this.2⟩

/-! ## `free` of an `mmap`ed chunk: the dynamic threshold and `munmap_chunk` -/

theorem mm_addrs_nodup {l : Local} (hw : LocalWF C l) : (l.shared.mm.chunks.map (·.addr)).Nodup := by
  have hap := Apart.right hw.apart
  have hp := hap.1
  rw [List.pairwise_map] at hp
  show List.Pairwise _ _
  rw [List.pairwise_map]
  refine hp.imp_of_mem fun hx hy h he => ?_
  have h2 := hap.2 _ (List.mem_map.mpr ⟨_, hx, rfl⟩)
  have h3 := hap.2 _ (List.mem_map.mpr ⟨_, hy, rfl⟩)
  simp only at h h2 h3 he; omega

theorem sum_erase_size {cs : List Chunk} {c : Chunk} (h : c ∈ cs) :
    ((cs.erase c).map (·.size)).sum + c.size = (cs.map (·.size)).sum := by
  induction cs with
  | nil => cases h
  | cons d cs ih =>
    by_cases hd : d = c
    · subst hd; simp only [List.erase_cons_head, List.map_cons, List.sum_cons]; omega
    · have hc : c ∈ cs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hd
        · exact h
      have hne : (d == c) = false := by simpa using hd
      simp only [List.erase_cons, hne, List.map_cons, List.sum_cons]
      have := ih hc; simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]; omega

theorem raise_chunks (ms : MmapSt) (sz : Nat) : (ms.raise C sz).chunks = ms.chunks := by
  unfold MmapSt.raise; split <;> rfl

theorem raise_sbrk (ms : MmapSt) (sz : Nat) : (ms.raise C sz).mp.sbrkBase = ms.mp.sbrkBase := by
  unfold MmapSt.raise; split <;> rfl

theorem raise_wf (hC : C.Ok) {ms : MmapSt} (h : MmapWF C ms) {sz : Nat} (hsz : sz % C.page = 0) :
    MmapWF C (ms.raise C sz) := by
  unfold MmapSt.raise
  split
  · rename_i hc
    obtain ⟨-, hlt, hle⟩ := hc
    obtain ⟨hd1, hd2⟩ := hC.dynThreshold
    have hwd := hC.words
    have hpg := hC.page
    obtain ⟨ht1, ht2⟩ := h.trimMin
    rw [hpg] at hd1 hsz
    have hmm : Config.isMmapped = 2 := rfl
    rw [hmm] at hlt hle
    have hsz' : C.mmapThreshold ≤ sz := by omega
    exact { mpBound := ⟨by simp only; omega, by simp only; omega, h.mpBound.2.2.1, h.mpBound.2.2.2⟩
            trimMin := ⟨by simp only; omega, by simp only; omega⟩
            mem := h.mem
            use := h.use, page := h.page, nonNull := h.nonNull, nodup := h.nodup }
  · exact h

theorem covers_munmap {k : KernelSt} {r : Nat × Nat} (h : k.Covers r) {c n : Nat}
    (hap : r.1 + r.2 ≤ c ∨ c + n ≤ r.1) : (k.munmap c n).Covers r := by
  intro x hx1 hx2
  rcases h x hx1 hx2 with hb | ⟨m, hm, hm1, hm2⟩
  · exact .inl hb
  · refine .inr ⟨m, ?_, hm1, hm2⟩
    show m ∈ k.maps.erase (c, n)
    refine (List.mem_erase_of_ne ?_).mpr hm
    rintro rfl; simp only at hm1 hm2; omega

/-- **`free` of a live `mmap`ed chunk `ch`** on the main arena's view: `WorldWF` and the live set
without it. -/
theorem mmFree_put (hC : C.Ok) {w : World} (hw : WorldWF C w) {tid : Nat} (ht : tid ∈ w.tids)
    {ch : Chunk} (hch : ch ∈ w.shared.mm.chunks) (hcu : ch.use = .client) {l l₂ : Local}
    (hl : w.local? tid w.mainArena = some l)
    (hm : munmapChunk C { l with shared := { l.shared with mm := l.shared.mm.raise C ch.size } }
      ch.addr = .ok l₂) :
    WorldWF C (w.put tid l₂) ∧
      ((w.put tid l₂).live C).Perm ((w.live C).erase (ch.addr + C.hdr, ch.size - 2 * C.sizeSz)) := by
  obtain ⟨av, hav, hlav, hla, hlm, hlt, hls, hlk⟩ := local?_fields hl
  have hwl := hw.locals tid _ l ht hl
  have hsp := localSp hw ht hl
  have hch' : ch ∈ l.shared.mm.chunks := by rw [hls]; exact hch
  have hpg := hwl.shared.mm.page ch hch' hcu
  have hfind : mmFind? { l with shared := { l.shared with mm := l.shared.mm.raise C ch.size } } ch.addr =
      some ch := by
    unfold mmFind?; simp only [raise_chunks]; exact find?_addr (mm_addrs_nodup hwl) hch'
  unfold munmapChunk at hm
  rw [hfind] at hm
  simp only [hpg.1, hpg.2, ne_eq, not_true_eq_false, or_self, ite_false] at hm
  injection hm with hm; subst hm
  -- the view after
  generalize hl₂ : ({ l with
      kernel := l.kernel.munmap ch.addr ch.size
      shared := { l.shared with mm := (l.shared.mm.raise C ch.size).remove ch } } : Local) = l₂
  have hmm₂ : l₂.shared.mm.chunks = l.shared.mm.chunks.erase ch := by
    rw [← hl₂]; simp [MmapSt.remove, raise_chunks]
  have hnd := hwl.shared.mm.nodup
  have hsub : l₂.shared.mm.chunks ⊆ l.shared.mm.chunks := fun d hd => by
    rw [hmm₂] at hd; exact List.mem_of_mem_erase hd
  have hspl : l.spans.Perm ((ch.addr, ch.size) :: l₂.spans) := by
    unfold Local.spans
    rw [hmm₂, show l₂.av = l.av by rw [← hl₂]]
    refine (List.Perm.append_left _ ((List.perm_cons_erase hch').map _)).trans ?_
    simp only [List.map_cons]
    exact List.perm_middle
  have hap₂ := hwl.apart.perm hspl
  have hchap : ∀ s ∈ l₂.spans, s.1 + s.2 ≤ ch.addr ∨ ch.addr + ch.size ≤ s.1 := fun s hs =>
    ((List.pairwise_cons.mp hap₂.1).1 s hs).symm
  have hwl₂ : LocalWF C l₂ := by
    have hmmwf := raise_wf hC hwl.shared.mm (sz := ch.size) hpg.2
    rw [← hl₂]
    refine
      { arena := hwl.arena
        shared :=
          { mm :=
              { mpBound := by
                  have := hmmwf.mpBound
                  simp only [MmapSt.remove]; refine ⟨this.1, this.2.1, ?_, this.2.2.2⟩; omega
                trimMin := hmmwf.trimMin
                use := fun d hd => hmmwf.use d (List.mem_of_mem_erase hd)
                page := fun d hd => hmmwf.page d (List.mem_of_mem_erase hd)
                nonNull := fun d hd => hmmwf.nonNull d (List.mem_of_mem_erase hd)
                nodup := hmmwf.nodup.erase _
                mem := by
                  have hm := hmmwf.mem
                  have he := sum_erase_size (raise_chunks (C := C) l.shared.mm ch.size ▸ hch')
                  simp only [MmapSt.remove]; omega }
            narenas := hwl.shared.narenas
            freeListSub := hwl.shared.freeListSub }
        tcache := hwl.tcache
        main := fun hm => by
          have ⟨h1, h2⟩ := hwl.main hm
          unfold MainSbrk MainBrk at *
          simp only [MmapSt.remove, raise_sbrk, KernelSt.munmap]
          exact ⟨h1, h2⟩
        init := fun hi => absurd ((hwl.init hi).2.1 ▸ hch') (List.not_mem_nil)
        apart := ?_
        mmSize := fun d hd => hwl.mmSize d (List.mem_of_mem_erase (by simpa [MmapSt.remove, raise_chunks] using hd))
        heap := hwl.heap
        sysMain := fun hmn => by
          have h0 := hwl.sysMain hmn
          have h1 := KernelSt.total_munmap l.kernel ch.addr ch.size
          have hm1 := hmmwf.mem
          have hm0 := hwl.shared.mm.mem
          have he := sum_erase_size hch'
          rw [raise_chunks] at hm1
          simp only [MmapSt.remove]
          omega }
    have := Apart.right (List.pairwise_cons.mp hap₂.1 |> fun _ => hap₂.perm (List.Perm.refl _) |>
      fun h => (show Apart ([(ch.addr, ch.size)] ++ l₂.spans) from h))
    rw [← hl₂] at this; exact this
  have hF : Frame C l l₂ [(ch.addr + C.hdr, ch.size - 2 * C.sizeSz)] :=
    { avAddr := by rw [← hl₂]
      isMain := by rw [← hl₂]
      spatial := fun r h0 hc haw => by
        have hrc := haw (ch.addr, ch.size) (hspl.symm.subset (List.mem_cons_self ..))
        refine ⟨by rw [← hl₂]; exact covers_munmap hc hrc, fun s hs => haw s (hspl.symm.subset
          (List.mem_cons_of_mem _ hs))⟩
      covered := fun s hs => by
        have hc := hsp.covered s (hspl.symm.subset (List.mem_cons_of_mem _ hs))
        rw [← hl₂]; exact covers_munmap hc (hchap s hs)
      brkStart := by rw [← hl₂]; rfl
      nonMain := fun h => by rw [hlm] at h; simp at h
      acct := fun h => by rw [hlm] at h; simp at h
      init := by rw [← hl₂]
      arenas := by rw [← hl₂]; exact ⟨rfl, rfl, rfl⟩
      arena := by rw [← hl₂]
      heaps := fun h => by rw [← hl₂]; exact h
      clients := fun c hc _ _ => by rw [← hl₂]; exact hc
      fresh := fun tc' i e htc he => .inl ⟨tc', i, by rw [← hl₂] at htc; exact htc, he⟩ }
  have hK : KeptAway l l₂ := fun tc i e htc he _ => ⟨tc, by rw [← hl₂]; exact htc, he⟩
  have hpw : (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) ∈ w.live C :=
    mem_live.mpr (.inr (mem_shlive.mpr ⟨ch, hch, hcu, rfl⟩))
  have hpl : (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) ∈ l.live C :=
    mem_llive.mpr (.inr (mem_shlive.mpr ⟨ch, hch', hcu, rfl⟩))
  have hperm : (l₂.live C).Perm ((l.live C).erase (ch.addr + C.hdr, ch.size - 2 * C.sizeSz)) := by
    have hnl := nodup_of_liveApart (llive_apart hC hwl)
    refine (List.perm_ext_iff_of_nodup (nodup_of_liveApart (llive_apart hC hwl₂)) (hnl.erase _)).mpr
      fun y => ?_
    rw [hnl.mem_erase_iff, mem_llive, mem_llive]
    have hav₂ : l₂.av = l.av := by rw [← hl₂]
    have hth₂ : l₂.thread = l.thread := by rw [← hl₂]
    rw [hav₂, hth₂]
    have hsh : ∀ y, y ∈ l₂.shared.live C ↔ y ∈ l.shared.live C ∧ y ≠ (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) := by
      intro y
      rw [mem_shlive, mem_shlive, hmm₂]
      constructor
      · rintro ⟨d, hd, hdu, rfl⟩
        have ⟨hdne, hd'⟩ := (hnd.mem_erase_iff).mp hd
        refine ⟨⟨d, hd', hdu, rfl⟩, fun he => hdne ?_⟩
        simp only [Prod.mk.injEq] at he
        exact mm_addr_inj hwl hd' hch' (by omega)
      · rintro ⟨⟨d, hd, hdu, rfl⟩, hne⟩
        refine ⟨d, (hnd.mem_erase_iff).mpr ⟨fun h => hne (by rw [h]), hd⟩, hdu, rfl⟩
    constructor
    · rintro (⟨hy, hnp⟩ | hy)
      · refine ⟨fun he => ?_, .inl ⟨hy, hnp⟩⟩
        subst he
        obtain ⟨d, hd, -, hde⟩ := mem_out.mp hy
        simp only [Prod.mk.injEq] at hde
        exact clash_mm hw hav (by rw [← hlav]; exact hd) hch (by omega)
      · exact ⟨((hsh y).mp hy).2, .inr ((hsh y).mp hy).1⟩
    · rintro ⟨hne, (⟨hy, hnp⟩ | hy)⟩
      · exact .inl ⟨hy, hnp⟩
      · exact .inr ((hsh y).mpr ⟨hy, hne⟩)
  exact put_free hC hw ht hl hwl hwl₂ hF hK hpw hpl hperm

/-! ## `free` -/

theorem arenaOf_some {w : World} {c a : Nat} (h : Ops.arenaOf w c = some a) :
    a ∈ w.arenaAddrs ∧ ∃ av, w.arenas a = some av ∧ ∃ d ∈ av.chunks, d.addr = c := by
  unfold Ops.arenaOf at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have hp := List.find?_some h
  cases ha : w.arenas a with
  | none => rw [ha] at hp; simp at hp
  | some av =>
    rw [ha] at hp
    simp only [Option.map_some, Option.getD_some, List.any_eq_true, decide_eq_true_eq] at hp
    exact ⟨av, rfl, hp⟩

theorem mmapped?_some {w : World} {c : Nat} {ch : Chunk} (h : Ops.mmapped? w c = some ch) :
    ch ∈ w.shared.mm.chunks ∧ ch.addr = c := by
  unfold Ops.mmapped? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A world with a live payload has run `ptmalloc_init`. -/
theorem init_of_live {w : World} (hw : WorldWF C w) {tid : Nat} (ht : tid ∈ w.tids) {y : Nat × Nat}
    (hy : y ∈ w.live C) : w.shared.init = true := by
  cases hi : w.shared.init with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨h1, h2, -⟩ := hw.initOK ht hi
    rcases mem_live.mp hy with ⟨⟨b, -, av, hab, hyb⟩, -⟩ | hm
    · obtain ⟨d, hd, -, -⟩ := mem_out.mp hyb
      have := (hw.arenaWF b av hab).tiles.noHeap (h1 b av hab)
      have hd' : d ∈ av.tiles.heapChunks := hd
      simp [TopSt.heapChunks, this.1, this.2, h1 b av hab] at hd'
    · obtain ⟨m, hm, -, -⟩ := mem_shlive.mp hm
      rw [h2] at hm; cases hm

theorem free_wf (hC : C.Ok) (hB : Task.algo.bodyMalloc C) (hFb : Task.algo.bodyFree C)
    {w w' : World} {tid p u : Nat} (hw : WorldWF C w) (ht : tid ∈ w.tids) (hpu : (p, u) ∈ w.live C)
    (h : (ptmalloc C).free w tid p = .ok w') :
    WorldWF C w' ∧ (w'.live C).Perm ((w.live C).erase (p, u)) := by
  have hmain : w.mainArena ∈ w.arenaAddrs := List.mem_cons_self ..
  have hp0 : p ≠ 0 := ((liveApart C hC w hw).2 _ hpu).1
  unfold Ops.free at h
  split at h
  · exact absurd ‹_› hp0
  dsimp only at h
  split at h
  · rename_i ch hmm
    obtain ⟨hch, hca⟩ := mmapped?_some hmm
    obtain ⟨l, hl, h⟩ := bind_ok_inv h
    try dsimp only at h
    obtain ⟨l₂, hm2, h⟩ := bind_ok_inv h
    injection h with h; subst h
    have hl' := localAt_inv hl
    have hwl := hw.locals tid _ l ht hl'
    obtain ⟨-, -, -, -, -, -, hls, -⟩ := local?_fields hl'
    -- the payload is `ch`'s
    have hpch : (p, u) = (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) ∧ ch.use = .client := by
      rcases mem_live.mp hpu with ⟨⟨b, -, av, hab, hyb⟩, -⟩ | hm
      · exfalso
        obtain ⟨d, hd, -, hde⟩ := mem_out.mp hyb
        simp only [Prod.mk.injEq] at hde
        exact clash_mm hw hab hd hch (by have := hC.sizeSz; unfold Config.hdr at *; omega)
      · obtain ⟨m, hm, hmu, hme⟩ := mem_shlive.mp hm
        simp only [Prod.mk.injEq] at hme
        have : m = ch := mm_addr_inj hwl (by rw [hls]; exact hm) (by rw [hls]; exact hch)
          (by have := hC.sizeSz; unfold Config.hdr at *; omega)
        subst this
        exact ⟨by rw [hme.1, hme.2], hmu⟩
    rw [← hca] at hm2
    have := mmFree_put hC hw ht hch hpch.2 hl' hm2
    rw [hpch.1]; exact this
  · obtain ⟨w₁, h1, h⟩ := bind_ok_inv h
    try dsimp only at h
    have c1 := tcacheInit_wf hC hB hw ht (init_of_live hw ht hpu) (h1 : tcacheInit C w tid = _)
    have ht1 : tid ∈ w₁.tids := c1.tids ▸ ht
    have hpu1 : (p, u) ∈ w₁.live C := c1.live.symm.subset hpu
    split at h
    · cases h
    · rename_i a ha
      obtain ⟨ha1, av, hav, d, hd, hda⟩ := arenaOf_some ha
      obtain ⟨l, hl, h⟩ := bind_ok_inv h
      try dsimp only at h
      obtain ⟨l₂, hm2, h⟩ := bind_ok_inv h
      injection h with h; subst h
      have hl' := localAt_inv hl
      obtain ⟨av', hav', hlav, hla, -, hlt, hls, -⟩ := local?_fields hl'
      rw [hav] at hav'; cases hav'
      have hwl := c1.wf.locals tid a l ht1 hl'
      -- the payload is a live payload of arena `a`
      have hal : (p, u) ∈ l.arenaLive C := by
        rcases mem_live.mp hpu1 with ⟨⟨b, -, avb, hab, hyb⟩, hnp⟩ | hm
        · obtain ⟨d', hd', hdu', hde⟩ := mem_out.mp hyb
          simp only [Prod.mk.injEq] at hde
          have hba : b = a := by
            refine Classical.byContradiction fun hne => ?_
            exact clash_arenas c1.wf hne hab hav hd' hd (by have := hC.sizeSz; unfold Config.hdr at *; omega)
          subst hba
          rw [hav] at hab; cases hab
          refine List.mem_filter.mpr ⟨by rw [hlav]; exact hyb, ?_⟩
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, contains_false]
          intro hp'
          exact hnp ((old_allParked ht1).mpr (.inl (by rw [← hlt]; exact hp')))
        · exfalso
          obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp hm
          simp only [Prod.mk.injEq] at hme
          exact clash_mm c1.wf hav hd hm (by have := hC.sizeSz; unfold Config.hdr at *; omega)
      have hpl : (p, u) ∈ l.live C := by
        unfold Local.live; exact List.mem_append_left _ hal
      obtain ⟨hwl₂, hF, hK, hperm⟩ := hFb hC l l₂ p u hwl (localSp c1.wf ht1 hl') hal hm2
      have := put_free hC c1.wf ht1 hl' hwl hwl₂ hF hK hpu1 hpl hperm
      exact ⟨this.1, this.2.trans (c1.live.erase _)⟩

/-- **`Task.algo.wfWorld` for the model**, from the body obligations. -/
theorem wfWorld_of (C : Config) (hB : Task.algo.bodyMalloc C) (hFb : Task.algo.bodyFree C) :
    Task.algo.wfWorld C (ptmalloc C) := fun hC _ _ hw ht =>
  ⟨fun _ _ _ h => malloc_wf hC hB hw ht h, fun _ _ _ hpu h => free_wf hC hB hFb hw ht hpu h⟩

/-! ## No abort at world level (`Task.algo.mallocTotal`) -/

theorem pure_bind' {α β : Type} (a : α) (f : α → Res β) : (pure a >>= f : Res β) = f a := rfl

theorem arenaGet2_ok (w : World) (tid nb : Nat) : ∃ r, arenaGet2 C w tid nb = .ok r := by
  unfold arenaGet2
  split
  · exact ⟨_, rfl⟩
  · split
    · split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem arenaGet_ok (w : World) (tid nb : Nat) : ∃ r, arenaGet C w tid nb = .ok r := by
  unfold arenaGet
  split
  · exact ⟨_, rfl⟩
  · exact arenaGet2_ok w tid nb

theorem arenaRetry_ok (w : World) (tid a nb : Nat) : ∃ r, arenaRetry C w tid a nb = .ok r := by
  unfold arenaRetry
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨r, h⟩ := arenaGet2_ok (C := C) w tid nb
    rw [h]; exact ⟨_, rfl⟩

theorem body_ok (hC : C.Ok) (htM : Task.algo.totalMalloc C) {w : World} (hw : WorldWF C w)
    {tid a : Nat} (ht : tid ∈ w.tids) (ha : a ∈ w.arenaAddrs) (n : Nat) :
    ∃ l r, Ops.localAt w tid a = .ok l ∧ intMalloc C l n = .ok r := by
  obtain ⟨l, hl, hl'⟩ := localAt_ok hw ha (tid := tid)
  obtain ⟨r, hr⟩ := htM hC l (hw.locals tid a l ht hl') (localSp hw ht hl') n
  exact ⟨l, r, hl, hr⟩

theorem tcacheInit_ok (hC : C.Ok) (hB : Task.algo.bodyMalloc C) (htM : Task.algo.totalMalloc C)
    {w : World} {tid : Nat} (hw : WorldWF C w) (ht : tid ∈ w.tids) (hi : w.shared.init = true) :
    ∃ w', tcacheInit C w tid = .ok w' := by
  unfold tcacheInit
  dsimp only
  split
  · exact ⟨_, rfl⟩
  obtain ⟨⟨a, w₁⟩, h1⟩ := arenaGet_ok (C := C) w tid (tcacheStructSize C)
  obtain ⟨q1, ha1⟩ := arenaGet_quiet hC hw ht hi h1
  have ht1 : tid ∈ w₁.tids := q1.tids ▸ ht
  obtain ⟨l, ⟨p, l₁⟩, hl, hm⟩ := body_ok hC htM q1.wf ht1 ha1 (tcacheStructSize C)
  rw [h1, ok_bind]; dsimp only; rw [hl, ok_bind, hm, ok_bind]; dsimp only
  split
  · rename_i hp
    rw [pure_bind']; try dsimp only
    split
    · exact absurd ‹_› hp
    · exact ⟨_, rfl⟩
  · rename_i hp
    have hp0 : p = 0 := by simpa using hp
    rw [hp0] at hm
    have c2 := q1.calm.trans (body_put_zero hC hB q1.wf (q1.init.trans hi) ht1 hl hm)
    obtain ⟨⟨r, w₃⟩, h5⟩ := arenaRetry_ok (C := C) (w₁.put tid l₁) tid a (tcacheStructSize C)
    obtain ⟨q3, hr3⟩ := arenaRetry_quiet hC c2.wf (c2.tids ▸ ht) (c2.init.trans hi) h5
    have c3 := c2.trans q3.calm
    rw [h5, ok_bind]; dsimp only
    cases r with
    | none => exact ⟨_, rfl⟩
    | some a' =>
      obtain ⟨l₂, ⟨p₂, l₃⟩, hl2, hm2⟩ := body_ok hC htM c3.wf (c3.tids ▸ ht) (hr3 a' rfl)
        (tcacheStructSize C)
      try dsimp only
      rw [hl2, ok_bind, hm2, ok_bind]; try dsimp only
      rw [pure_bind']; try dsimp only
      split <;> exact ⟨_, rfl⟩

theorem withArena_ok (hC : C.Ok) (hB : Task.algo.bodyMalloc C) (htM : Task.algo.totalMalloc C)
    {w : World} {tid nb n : Nat} (hw : WorldWF C w) (ht : tid ∈ w.tids) (hi : w.shared.init = true) :
    ∃ r, (ptmalloc C).withArena w tid nb (fun l => (ptmalloc C).intMalloc l n) = .ok r := by
  have hmain : w.mainArena ∈ w.arenaAddrs := List.mem_cons_self ..
  unfold Ops.withArena
  split
  · obtain ⟨l, ⟨p, l₁⟩, hl, hm⟩ := body_ok hC htM hw ht hmain n
    rw [hl, ok_bind]; dsimp only
    rw [show (ptmalloc C).intMalloc l n = intMalloc C l n from rfl, hm, ok_bind]
    exact ⟨_, rfl⟩
  · obtain ⟨⟨a, w₁⟩, h1⟩ := arenaGet_ok (C := C) w tid nb
    obtain ⟨q1, ha1⟩ := arenaGet_quiet hC hw ht hi h1
    have ht1 : tid ∈ w₁.tids := q1.tids ▸ ht
    obtain ⟨l, ⟨p, l₁⟩, hl, hm⟩ := body_ok hC htM q1.wf ht1 ha1 n
    rw [show (ptmalloc C).arenaGet w tid nb = arenaGet C w tid nb from rfl, h1, ok_bind]
    dsimp only
    rw [hl, ok_bind, show (ptmalloc C).intMalloc l n = intMalloc C l n from rfl, hm, ok_bind]
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · rename_i hp
      have hp0 : p = 0 := by simpa using hp
      rw [hp0] at hm
      have c2 := q1.calm.trans (body_put_zero hC hB q1.wf (q1.init.trans hi) ht1 hl hm)
      obtain ⟨⟨r, w₃⟩, h5⟩ := arenaRetry_ok (C := C) (w₁.put tid l₁) tid a nb
      obtain ⟨q3, hr3⟩ := arenaRetry_quiet hC c2.wf (c2.tids ▸ ht) (c2.init.trans hi) h5
      have c3 := c2.trans q3.calm
      rw [show (ptmalloc C).arenaRetry (w₁.put tid l₁) tid a nb = arenaRetry C (w₁.put tid l₁) tid a nb
        from rfl, h5, ok_bind]
      try dsimp only
      cases r with
      | none => exact ⟨_, rfl⟩
      | some a' =>
        obtain ⟨l₂, ⟨p₂, l₃⟩, hl2, hm2⟩ := body_ok hC htM c3.wf (c3.tids ▸ ht) (hr3 a' rfl) n
        try dsimp only
        rw [hl2, ok_bind, show (ptmalloc C).intMalloc l₂ n = intMalloc C l₂ n from rfl, hm2, ok_bind]
        exact ⟨_, rfl⟩

theorem malloc_ok (hC : C.Ok) (hB : Task.algo.bodyMalloc C) (htM : Task.algo.totalMalloc C)
    {w : World} {tid : Nat} (hw : WorldWF C w) (ht : tid ∈ w.tids) (n : Nat) :
    ∃ r, (ptmalloc C).malloc w tid n = .ok r := by
  unfold Ops.malloc
  have hinit : ∃ w₁, (ptmalloc C).init w tid = .ok w₁ := by
    unfold Ops.init; split
    · exact ⟨_, rfl⟩
    · obtain ⟨key, k, he, -⟩ := ptmallocInit_eq w tid; exact ⟨_, he⟩
  obtain ⟨w₁, h1⟩ := hinit
  obtain ⟨hw1, -, ht1, hi1, -, -⟩ := init_wf hw h1
  have ht1' : tid ∈ w₁.tids := ht1 ▸ ht
  rw [h1, ok_bind]; dsimp only
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨w₂, h2⟩ := tcacheInit_ok hC hB htM hw1 ht1' hi1
    have c2 := tcacheInit_wf hC hB hw1 ht1' hi1 h2
    have ht2 : tid ∈ w₂.tids := c2.tids ▸ ht1'
    rw [show (ptmalloc C).tcacheInit w₁ tid = tcacheInit C w₁ tid from rfl, h2, ok_bind]
    try dsimp only
    have ha0 : ((w₂.threads tid).arena).getD w₂.mainArena ∈ w₂.arenaAddrs := by
      cases hx : (w₂.threads tid).arena with
      | none => exact List.mem_cons_self ..
      | some b => exact c2.wf.threadArena tid b ht2 hx
    obtain ⟨l0, hl0, -⟩ := localAt_ok c2.wf ha0 (tid := tid)
    rw [hl0, ok_bind]; try dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact withArena_ok hC hB htM c2.wf ht2 (c2.init.trans hi1)

theorem free_ok (hC : C.Ok) (hB : Task.algo.bodyMalloc C) (htM : Task.algo.totalMalloc C)
    (htF : Task.algo.totalFree C) {w : World} {tid p u : Nat} (hw : WorldWF C w) (ht : tid ∈ w.tids)
    (hpu : (p, u) ∈ w.live C) : ∃ w', (ptmalloc C).free w tid p = .ok w' := by
  have hmain : w.mainArena ∈ w.arenaAddrs := List.mem_cons_self ..
  unfold Ops.free
  split
  · exact ⟨_, rfl⟩
  dsimp only
  split
  · rename_i ch hmm
    obtain ⟨hch, hca⟩ := mmapped?_some hmm
    obtain ⟨l, hl, hl'⟩ := localAt_ok hw hmain (tid := tid)
    have hwl := hw.locals tid _ l ht hl'
    obtain ⟨-, -, -, -, -, -, hls, -⟩ := local?_fields hl'
    have hch' : ch ∈ l.shared.mm.chunks := by rw [hls]; exact hch
    -- the payload is `ch`'s, so `ch` is lent out
    have hcu : ch.use = .client := by
      rcases mem_live.mp hpu with ⟨⟨b, -, av, hab, hyb⟩, -⟩ | hm
      · exfalso
        obtain ⟨d, hd, -, hde⟩ := mem_out.mp hyb
        simp only [Prod.mk.injEq] at hde
        exact clash_mm hw hab hd hch (by have := hC.sizeSz; unfold Config.hdr at *; omega)
      · obtain ⟨m, hm, hmu, hme⟩ := mem_shlive.mp hm
        simp only [Prod.mk.injEq] at hme
        have : m = ch := mm_addr_inj hwl (by rw [hls]; exact hm) hch'
          (by have := hC.sizeSz; unfold Config.hdr at *; omega)
        subst this; exact hmu
    have hpg := hwl.shared.mm.page ch hch' hcu
    rw [hl, ok_bind]; try dsimp only
    rw [← hca]
    have hfind : mmFind? { l with shared := { l.shared with mm := l.shared.mm.raise C ch.size } } ch.addr =
        some ch := by
      unfold mmFind?; simp only [raise_chunks]; exact find?_addr (mm_addrs_nodup hwl) hch'
    show ∃ w', (munmapChunk C _ ch.addr >>= _) = _
    unfold munmapChunk
    rw [hfind]
    simp only [hpg.1, hpg.2, ne_eq, not_true_eq_false, or_self, ite_false]
    exact ⟨_, rfl⟩
  · obtain ⟨w₁, h1⟩ := tcacheInit_ok hC hB htM hw ht (init_of_live hw ht hpu)
    have c1 := tcacheInit_wf hC hB hw ht (init_of_live hw ht hpu) h1
    have ht1 : tid ∈ w₁.tids := c1.tids ▸ ht
    have hpu1 : (p, u) ∈ w₁.live C := c1.live.symm.subset hpu
    rw [show (ptmalloc C).tcacheInit w tid = tcacheInit C w tid from rfl, h1, ok_bind]
    try dsimp only
    -- the payload's chunk lies in an arena of `w`, and stays in it
    rename_i hnone
    obtain ⟨b, hb, avb, hab, d, hd, hdu, hde⟩ : ∃ b ∈ w.arenaAddrs, ∃ av, w.arenas b = some av ∧
        ∃ d ∈ av.chunks, d.use = .client ∧ (p, u) = (d.addr + C.hdr, d.size - C.sizeSz) := by
      rcases mem_live.mp hpu with ⟨⟨b, hb, avb, hab, hyb⟩, -⟩ | hm
      · obtain ⟨d, hd, hdu, hde⟩ := mem_out.mp hyb
        exact ⟨b, hb, avb, hab, d, hd, hdu, hde⟩
      · exfalso
        obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp hm
        simp only [Prod.mk.injEq] at hme
        unfold Ops.mmapped? at hnone
        rw [List.find?_eq_none] at hnone
        exact hnone m hm (by simp; omega)
    simp only [Prod.mk.injEq] at hde
    obtain ⟨hpd, hud⟩ := hde
    obtain ⟨av₁, hab₁, hd₁⟩ := c1.keep b avb d hab hd hdu (by rw [← hpd, ← hud]; exact hpu)
    have hfind : ∃ a, Ops.arenaOf w₁ (p - C.hdr) = some a := by
      unfold Ops.arenaOf
      cases hf : w₁.arenaAddrs.find? (fun x => ((w₁.arenas x).map fun av =>
          av.chunks.any (·.addr = p - C.hdr)).getD false) with
      | some a => exact ⟨a, rfl⟩
      | none =>
        exfalso
        rw [List.find?_eq_none] at hf
        have := hf b (c1.wf.mem_addrs hab₁)
        rw [hab₁] at this
        simp only [Option.map_some, Option.getD_some, List.any_eq_true, decide_eq_true_eq] at this
        exact this ⟨d, hd₁, by omega⟩
    obtain ⟨a, ha⟩ := hfind
    rw [ha]
    try dsimp only
    obtain ⟨ha1, av, hav, d', hd', hda⟩ := arenaOf_some ha
    obtain ⟨l, hl, hl'⟩ := localAt_ok c1.wf ha1 (tid := tid)
    rw [hl, ok_bind]
    obtain ⟨av', hav', hlav, hla, -, hlt, hls, -⟩ := local?_fields hl'
    rw [hav] at hav'; cases hav'
    have hwl := c1.wf.locals tid a l ht1 hl'
    have hal : (p, u) ∈ l.arenaLive C := by
      rcases mem_live.mp hpu1 with ⟨⟨b, -, avb, hab, hyb⟩, hnp⟩ | hm
      · obtain ⟨d'', hd'', -, hde⟩ := mem_out.mp hyb
        simp only [Prod.mk.injEq] at hde
        have hba : b = a := by
          refine Classical.byContradiction fun hne => ?_
          exact clash_arenas c1.wf hne hab hav hd'' hd' (by have := hC.sizeSz; unfold Config.hdr at *; omega)
        subst hba
        rw [hav] at hab; cases hab
        refine List.mem_filter.mpr ⟨by rw [hlav]; exact hyb, ?_⟩
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, contains_false]
        intro hp'
        exact hnp ((old_allParked ht1).mpr (.inl (by rw [← hlt]; exact hp')))
      · exfalso
        obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp hm
        simp only [Prod.mk.injEq] at hme
        exact clash_mm c1.wf hav hd' hm (by have := hC.sizeSz; unfold Config.hdr at *; omega)
    obtain ⟨l₂, hl₂⟩ := htF hC l hwl (localSp c1.wf ht1 hl') p u hal
    rw [show (ptmalloc C).intFree l (p - C.hdr) = intFree C l (p - C.hdr) from rfl, hl₂, ok_bind]
    exact ⟨_, rfl⟩

/-- **`Task.algo.mallocTotal` for the model**, from the body obligations. -/
theorem mallocTotal_of (C : Config) (hB : Task.algo.bodyMalloc C) (htM : Task.algo.totalMalloc C)
    (htF : Task.algo.totalFree C) : Task.algo.mallocTotal C (ptmalloc C) := fun hC _ _ hw ht =>
  ⟨fun n => malloc_ok hC hB htM hw ht n, fun _ _ hpu => free_ok hC hB htM htF hw ht hpu⟩

end Silmaril.Libc.Ptmalloc.Algo
