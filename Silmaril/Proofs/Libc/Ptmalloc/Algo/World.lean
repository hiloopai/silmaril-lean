module

public import Silmaril.Libc.Ptmalloc.Refine.Thms
public import Silmaril.Libc.Ptmalloc.Algo.Impl.Defs

/-!
# ptmalloc algorithm: world-level facts

* `Algo.liveApart : ∀ C, Task.algo.liveApart C`: the live payloads of a well-formed world are
  apart and bounded. Every live payload is the payload of an arena chunk or an `mmap`ed chunk
  (`live_sublist`), those chunks are apart (`WorldWF.apart`), and a payload stays inside its
  chunk up to the next chunk's `prev_size` word (`pay_apart`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem flatMap_sublist_flatMap {α β : Type} {f g : α → List β} (h : ∀ x, (f x).Sublist (g x)) :
    ∀ l : List α, (l.flatMap f).Sublist (l.flatMap g)
  | [] => List.Sublist.slnil
  | x :: l => by
    simp only [List.flatMap_cons]
    exact (h x).append (flatMap_sublist_flatMap h l)

/-- A chunk with its kind (`true`: `mmap`ed). -/
abbrev KChunk := Chunk × Bool

def kspan (x : KChunk) : Nat × Nat := (x.1.addr, x.1.size)
def kpay (C : Config) (x : KChunk) : Nat × Nat := (x.1.addr + C.hdr, usable C x.1 x.2)

/-- The kinded chunks of a world: every arena's chunks, then the `mmap`ed chunks. -/
def World.kchunks (w : World) : List KChunk :=
  w.chunks.map (fun c => (c, false)) ++ w.shared.mm.chunks.map (fun c => (c, true))

theorem out_sublist (av : ArenaSt) :
    (av.out C).Sublist (av.chunks.map fun c => (c.addr + C.hdr, usable C c false)) :=
  (List.filter_sublist ..).map _

theorem live_sublist (w : World) : (w.live C).Sublist ((World.kchunks w).map (kpay C)) := by
  unfold World.live World.kchunks
  simp only [List.map_append, List.map_map]
  refine List.Sublist.append ?_ ?_
  · refine (List.filter_sublist ..).trans ?_
    unfold World.chunks
    rw [List.map_flatMap]
    refine flatMap_sublist_flatMap (fun a => ?_) _
    cases w.arenas a with
    | none => exact List.Sublist.slnil
    | some av => exact out_sublist av
  · exact (List.filter_sublist ..).map _

theorem kspans_sublist (w : World) : ((World.kchunks w).map kspan).Sublist w.spans := by
  unfold World.kchunks World.spans World.chunks
  simp only [List.map_append, List.map_map]
  refine List.Sublist.append ?_ (List.Sublist.refl _)
  rw [List.map_flatMap]
  refine flatMap_sublist_flatMap (fun a => ?_) _
  cases w.arenas a with
  | none => exact List.Sublist.slnil
  | some av =>
    simp only [Option.map_some, Option.getD_some, ArenaSt.spans, TopSt.spans, ArenaSt.chunks]
    exact (List.sublist_append_left ..).trans (List.sublist_append_left ..)

/-- The per-chunk facts a payload bound needs. -/
def KOk (C : Config) (x : KChunk) : Prop :=
  if x.2 then C.hdr < x.1.size ∧ x.1.addr + x.1.size ≤ 2 ^ 64
  else C.minSize ≤ x.1.size ∧ x.1.addr % C.align = 0 ∧ x.1.size % C.align = 0 ∧
    x.1.addr + x.1.size < 2 ^ 64

theorem kpay_bounds (hC : C.Ok) {x : KChunk} (hx : KOk C x) :
    C.hdr + x.1.addr ≤ (kpay C x).1 ∧ (kpay C x).1 + (kpay C x).2 ≤ x.1.addr + x.1.size + C.sizeSz ∧
      (kpay C x).1 ≠ 0 ∧ 0 < (kpay C x).2 ∧ (kpay C x).1 + (kpay C x).2 ≤ 2 ^ 64 := by
  obtain ⟨c, b⟩ := x
  have h8 := hC.sizeSz; have h16 := hC.align; have h32 := hC.minSize
  unfold KOk at hx; unfold kpay usable Config.hdr
  cases b with
  | true => simp only [ite_true] at hx ⊢; unfold Config.hdr at hx; rw [h8] at hx ⊢; omega
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hx ⊢
    rw [h8]; rw [h16, h32] at hx; omega

theorem pay_apart (hC : C.Ok) {x y : KChunk} (hx : KOk C x) (hy : KOk C y)
    (h : (kspan x).1 + (kspan x).2 ≤ (kspan y).1 ∨ (kspan y).1 + (kspan y).2 ≤ (kspan x).1) :
    (kpay C x).1 + (kpay C x).2 ≤ (kpay C y).1 ∨ (kpay C y).1 + (kpay C y).2 ≤ (kpay C x).1 := by
  have bx := kpay_bounds hC hx; have by' := kpay_bounds hC hy
  have h8 := hC.sizeSz
  unfold kspan at h; unfold Config.hdr at bx by'
  rw [h8] at bx by'
  omega

theorem kchunks_ok {w : World} (hw : WorldWF C w) : ∀ x ∈ World.kchunks w, KOk C x := by
  intro x hx
  unfold World.kchunks at hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    unfold World.chunks at hc
    obtain ⟨a, -, hca⟩ := List.mem_flatMap.mp hc
    cases ha : w.arenas a with
    | none => rw [ha] at hca; cases hca
    | some av =>
      rw [ha] at hca
      have ht := (hw.arenaWF a av ha).tiles
      have hc' : c ∈ av.tiles.heapChunks := hca
      unfold KOk
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨(ht.sizes c hc').2, ht.aligned c hc', (ht.sizes c hc').1, ht.bound c hc'⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    unfold KOk; simp only [ite_true]
    exact hw.mmSize c hc

/-- **`Algo.liveApart`**. -/
theorem liveApart (C : Config) : Task.algo.liveApart C := by
  intro hC w hw
  have hok := kchunks_ok hw
  have hsp := hw.apart.1.sublist (kspans_sublist w)
  rw [List.pairwise_map] at hsp
  have hpay : ((World.kchunks w).map (kpay C)).Pairwise
      (fun q r => q.1 + q.2 ≤ r.1 ∨ r.1 + r.2 ≤ q.1) := by
    rw [List.pairwise_map]
    exact hsp.imp_of_mem fun hx hy h => pay_apart hC (hok _ hx) (hok _ hy) h
  refine ⟨hpay.sublist (live_sublist w), fun q hq => ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((live_sublist w).subset hq)
  have := kpay_bounds hC (hok x hx)
  exact ⟨this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩

end Silmaril.Libc.Ptmalloc.Algo

/-! ## The threads are kept (`Task.algo.tidsKept`) -/

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem ptmallocInit_tids {w w' : World} {tid : Nat} (h : ptmallocInit w tid = .ok w') :
    w'.tids = w.tids := by
  unfold ptmallocInit at h
  repeat' split at h
  all_goals (injection h with h; subst h; rfl)

theorem heapAttempt_tids (w : World) (sz : Nat) : (heapAttempt C w sz).2.tids = w.tids := by
  unfold heapAttempt
  split
  · rfl
  · split <;> rfl

theorem newArena_tids (w : World) (tid nb : Nat) : (newArena C w tid nb).2.tids = w.tids := by
  unfold newArena
  dsimp only
  generalize max (alignUp (nb + (C.heapInfoSize + C.stateSize + C.align) + C.topPad) C.page) heapMinSize = t1
  generalize max (alignUp (C.heapInfoSize + C.stateSize + C.align) C.page) heapMinSize = t2
  have a1 := heapAttempt_tids (C := C) w t1
  cases h1 : heapAttempt C w t1 with
  | mk r1 w1 =>
    rw [h1] at a1
    cases r1 with
    | some v => obtain ⟨hp, sz⟩ := v; exact a1
    | none =>
      simp only
      have a2 := heapAttempt_tids (C := C) w1 t2
      cases h2 : heapAttempt C w1 t2 with
      | mk r2 w2 =>
        rw [h2] at a2
        cases r2 with
        | none => exact a2.trans a1
        | some v => obtain ⟨hp, sz⟩ := v; exact a2.trans a1

theorem arenaGet2_tids {w w' : World} {tid nb a : Nat} (h : arenaGet2 C w tid nb = .ok (a, w')) :
    w'.tids = w.tids := by
  unfold arenaGet2 at h
  repeat' split at h
  all_goals (try (injection h with h; injection h with h1 h; subst h; rfl))
  all_goals (rename_i heq; injection h with h; injection h with h1 h; subst h
             have := newArena_tids (C := C) w tid nb; rw [heq] at this; exact this)

theorem arenaGet_tids {w w' : World} {tid nb a : Nat} (h : arenaGet C w tid nb = .ok (a, w')) :
    w'.tids = w.tids := by
  unfold arenaGet at h
  split at h
  · injection h with h; injection h with h1 h; subst h; rfl
  · exact arenaGet2_tids h

theorem arenaRetry_tids {w w' : World} {tid a nb : Nat} {r : Option Nat}
    (h : arenaRetry C w tid a nb = .ok (r, w')) : w'.tids = w.tids := by
  unfold arenaRetry at h
  split at h
  · injection h with h; injection h with h1 h; subst h; rfl
  · cases h2 : arenaGet2 C w tid nb with
    | error e => rw [h2] at h; cases h
    | ok v =>
      obtain ⟨a', w''⟩ := v
      rw [h2] at h
      injection h with h; injection h with h1 h; subst h
      exact arenaGet2_tids h2

theorem markInternal_tids (w : World) (a p : Nat) : (markInternal C w a p).tids = w.tids := by
  unfold markInternal; dsimp only; split <;> rfl

theorem localAt_put_tids (w : World) (tid : Nat) (l : Local) : (w.put tid l).tids = w.tids := rfl

theorem bind_ok_inv {α β : Type} {x : Res α} {f : α → Res β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem tcacheInit_tids {w w' : World} {tid : Nat} (h : tcacheInit C w tid = .ok w') :
    w'.tids = w.tids := by
  unfold tcacheInit at h
  dsimp only at h
  split at h
  · injection h with h; subst h; rfl
  obtain ⟨⟨a, w₁⟩, h1, h⟩ := bind_ok_inv h
  try dsimp only at h
  have t1 := arenaGet_tids h1
  obtain ⟨l, -, h⟩ := bind_ok_inv h
  try dsimp only at h
  obtain ⟨⟨p, l₁⟩, -, h⟩ := bind_ok_inv h
  try dsimp only at h
  split at h
  · obtain ⟨x, hx, h⟩ := bind_ok_inv h
    injection hx with hx; subst hx; try dsimp only at h
    split at h <;> (injection h with h; subst h; simp [markInternal_tids, localAt_put_tids, t1])
  · obtain ⟨⟨r, w₃⟩, h5, h⟩ := bind_ok_inv h
    have t3 := arenaRetry_tids h5
    try dsimp only at h
    split at h
    · obtain ⟨x, hx, h⟩ := bind_ok_inv h
      injection hx with hx; subst hx; try dsimp only at h
      split at h <;> (injection h with h; subst h; simp [markInternal_tids, t3, localAt_put_tids, t1])
    · obtain ⟨l₂, -, h⟩ := bind_ok_inv h
      try dsimp only at h
      obtain ⟨⟨p₂, l₃⟩, -, h⟩ := bind_ok_inv h
      try dsimp only at h
      obtain ⟨x, hx, h⟩ := bind_ok_inv h
      injection hx with hx; subst hx; try dsimp only at h
      split at h <;> (injection h with h; subst h; simp [markInternal_tids, localAt_put_tids, t3, t1])

theorem withArena_tids {w w' : World} {tid nb p : Nat} {body : Local → Res (Nat × Local)}
    (h : (ptmalloc C).withArena w tid nb body = .ok (p, w')) : w'.tids = w.tids := by
  unfold Ops.withArena at h
  split at h
  · obtain ⟨l, -, h⟩ := bind_ok_inv h
    try dsimp only at h
    obtain ⟨⟨p₁, l₁⟩, -, h⟩ := bind_ok_inv h
    try dsimp only at h
    injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
  · obtain ⟨⟨a, w₁⟩, h1, h⟩ := bind_ok_inv h
    try dsimp only at h
    have t1 := arenaGet_tids (C := C) h1
    obtain ⟨l, -, h⟩ := bind_ok_inv h
    try dsimp only at h
    obtain ⟨⟨p₁, l₁⟩, -, h⟩ := bind_ok_inv h
    try dsimp only at h
    split at h
    · injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      rw [localAt_put_tids, t1]
    · obtain ⟨⟨r, w₂⟩, h2, h⟩ := bind_ok_inv h
      try dsimp only at h
      have t2 := arenaRetry_tids (C := C) h2
      split at h
      · injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
        rw [t2, localAt_put_tids, t1]
      · obtain ⟨l₂, -, h⟩ := bind_ok_inv h
        try dsimp only at h
        obtain ⟨⟨p₂, l₃⟩, -, h⟩ := bind_ok_inv h
        try dsimp only at h
        injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
        rw [localAt_put_tids, t2, localAt_put_tids, t1]

theorem init_tids {w w' : World} {tid : Nat} (h : (ptmalloc C).init w tid = .ok w') : w'.tids = w.tids := by
  unfold Ops.init at h
  split at h
  · injection h with h; subst h; rfl
  · exact ptmallocInit_tids h

theorem malloc_tids {w w' : World} {tid n p : Nat} (h : (ptmalloc C).malloc w tid n = .ok (p, w')) :
    w'.tids = w.tids := by
  unfold Ops.malloc at h
  obtain ⟨w₁, h1, h⟩ := bind_ok_inv h
  try dsimp only at h
  have t1 := init_tids h1
  split at h
  · injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact t1
  · obtain ⟨w₂, h2, h⟩ := bind_ok_inv h
    try dsimp only at h
    have t2 := tcacheInit_tids (C := C) h2
    obtain ⟨l, -, h⟩ := bind_ok_inv h
    try dsimp only at h
    split at h
    · injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      rw [localAt_put_tids, t2, t1]
    · rw [withArena_tids h, t2, t1]

theorem free_tids {w w' : World} {tid p : Nat} (h : (ptmalloc C).free w tid p = .ok w') :
    w'.tids = w.tids := by
  unfold Ops.free at h
  split at h
  · injection h with h; subst h; rfl
  dsimp only at h
  split at h
  · obtain ⟨l, -, h⟩ := bind_ok_inv h
    try dsimp only at h
    obtain ⟨l₁, -, h⟩ := bind_ok_inv h
    try dsimp only at h
    injection h with h; subst h; rfl
  · obtain ⟨w₁, h1, h⟩ := bind_ok_inv h
    try dsimp only at h
    have t1 := tcacheInit_tids (C := C) h1
    split at h
    · cases h
    · obtain ⟨l, -, h⟩ := bind_ok_inv h
      try dsimp only at h
      obtain ⟨l₁, -, h⟩ := bind_ok_inv h
      try dsimp only at h
      injection h with h; subst h; rw [localAt_put_tids, t1]

/-- **`Algo.tidsKept`**. -/
theorem tidsKept (C : Config) : Task.algo.tidsKept C (ptmalloc C) :=
  fun _ _ _ _ _ => ⟨fun _ _ _ h => malloc_tids h, fun _ _ h => free_tids h⟩

end Silmaril.Libc.Ptmalloc.Algo
