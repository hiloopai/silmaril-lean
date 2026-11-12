module

public import Silmaril.Libc.Ptmalloc.Algo.Defs
public import Silmaril.Libc.Ptmalloc.Rep.Defs

/-!
# ptmalloc x86sim: the representation step of `tcache_get` (layer c), proved

`repTcacheGet_of`: `tcache_get`'s three stores (`entries[i]`, `counts[i]`, the popped entry's
`key`) turn `LocalRep … l` into `LocalRep … l'` for `l.tcacheGet C i = some (p, l')`, on any
`MemView` whose bytes are machine bytes (`MemView.Sane`: values below 256 at addresses below
`2^64`, as `memView` of a silmaril memory). It discharges `Task.x86sim.repTcacheGet`.

The argument is generic: the stored cells replace cells of the same shape, the new thread
fragment is a permutation of the old one with two cells dropped and two re-valued
(`ft' ~ O ++ [K', E']`, `ft ~ O ++ [K, E, L, Kp]`), so every kept cell is disjoint from the
stores by the `Nodup` of `LocalRep`, and the new bytes are a sub-permutation of the old.
The cell lemmas (`load_of_bytes`, `store_self`, `store_frame`, `backs_store`) are not
allocator-specific.
-/

@[expose] public section

open Silmaril.Data
open Silmaril.Data.SepList (SLinks slist)
namespace Silmaril.Libc.Ptmalloc.X86sim

/-- **A view of machine bytes**: values below 256, at addresses below `2^64`. -/
def SaneView (v : MemView) : Prop := ∀ a b, v.byte a = some b → b < 256 ∧ a < 2 ^ 64

/-! ## Cells and stores (generic) -/

theorem load_lt {v : MemView} (hs : SaneView v) : ∀ (k a x : Nat), v.load a k = some x → x < 256 ^ k
  | 0, a, x, h => by simp [MemView.load] at h; omega
  | k + 1, a, x, h => by
    simp only [MemView.load] at h
    cases hb : v.byte a with
    | none => simp [hb] at h
    | some b =>
      cases hr : v.load (a + 1) k with
      | none => simp [hb, hr] at h
      | some r =>
        simp only [hb, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        have h1 := (hs a b hb).1
        have h2 := load_lt hs k (a + 1) r hr
        rw [Nat.pow_succ']; subst h
        have : 256 * r + 256 ≤ 256 * 256 ^ k := by
          have := Nat.mul_le_mul_left 256 (show r + 1 ≤ 256 ^ k by omega); omega
        omega

theorem load_addr {v : MemView} (hs : SaneView v) {k a x : Nat} (h : v.load a (k + 1) = some x) :
    a < 2 ^ 64 := by
  simp only [MemView.load] at h
  cases hb : v.byte a with
  | none => simp [hb] at h
  | some b => exact (hs a b hb).2

theorem load_of_bytes {v : MemView} : ∀ (k a x : Nat),
    (∀ j < k, v.byte (a + j) = some (x / 256 ^ j % 256)) → v.load a k = some (x % 256 ^ k)
  | 0, a, x, _ => by simp [MemView.load, Nat.mod_one]
  | k + 1, a, x, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
    have ih := load_of_bytes k (a + 1) (x / 256) fun j hj => by
      have := h (j + 1) (by omega)
      rw [show a + (j + 1) = a + 1 + j by omega, Nat.pow_succ', ← Nat.div_div_eq_div_mul] at this
      exact this
    simp only [MemView.load, h0, ih, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [Nat.pow_succ', Nat.mod_mul]

/-- A stored cell holds (its bytes writable, its value fitting). -/
theorem store_self {v : MemView} {s : Cell} (hw : ∀ k < s.width, v.writable (s.addr + k) = true)
    (hv : s.val < 256 ^ s.width) : s.Holds (v.store s) := by
  refine ⟨?_, fun k hk => hw k hk⟩
  rw [← Nat.mod_eq_of_lt hv]
  apply load_of_bytes
  intro j hj
  simp only [MemView.store, show s.addr ≤ s.addr + j from by omega,
    show s.addr + j < s.addr + s.width from by omega, and_self, ↓reduceIte,
    show s.addr + j - s.addr = j by omega]

theorem store_agree {v : MemView} {s : Cell} {a : Nat} (ha : a ∉ List.range' s.addr s.width) :
    (v.store s).byte a = v.byte a ∧ (v.store s).writable a = v.writable a := by
  refine ⟨?_, rfl⟩
  simp only [MemView.store]
  split
  · rename_i h
    exact absurd (List.mem_range'.2 ⟨a - s.addr, by omega, by omega⟩) ha
  · rfl

/-- A cell apart from a store survives it. -/
theorem store_frame {v : MemView} {c s : Cell} (h : c.Holds v)
    (hd : ∀ a ∈ List.range' c.addr c.width, a ∉ List.range' s.addr s.width) : c.Holds (v.store s) := by
  have := Frag.holds_frame (f := [c]) (v' := v.store s) (fun d hd' => by
    simp only [List.mem_singleton] at hd'; subst hd'; exact h) (fun a ha => by
      simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil] at ha
      have := store_agree (v := v) (hd a ha)
      exact ⟨this.1.symm, this.2.symm⟩)
  exact this c (List.mem_singleton_self c)

theorem backs_store {v : MemView} {s : Cell} {sp : List (Nat × Nat)} (h : v.Backs sp) :
    (v.store s).Backs sp := by
  intro x hx k hk
  obtain ⟨h1, h2⟩ := h x hx k hk
  refine ⟨?_, h2⟩
  simp only [MemView.store]
  split
  · rfl
  · exact h1

theorem sane_store {v : MemView} {s : Cell} (hs : SaneView v) (hb : s.addr + s.width ≤ 2 ^ 64) :
    SaneView (v.store s) := by
  intro a b h
  simp only [MemView.store] at h
  split at h
  · rename_i hin; cases h; exact ⟨Nat.mod_lt _ (by omega), by omega⟩
  · exact hs a b h

/-! ## Lists -/

theorem slist_cons (K : SLinks) (a : Nat) (l : List Nat) :
    slist K (a :: l) = ⟨a + K.link, K.ws, K.enc (a + K.link) (l.headD K.nil)⟩ :: slist K l := rfl

theorem flatMap_congr' {f g : Nat → Frag} : ∀ {l : List Nat}, (∀ k ∈ l, f k = g k) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | k :: l, h => by
    simp only [List.flatMap_cons, h k List.mem_cons_self,
      flatMap_congr' fun k' hk' => h k' (List.mem_cons_of_mem _ hk')]

/-- A `flatMap` over a list with one block changed to a permutation of another block plus `X`. -/
theorem flatMap_perm_one {f g : Nat → Frag} {X : Frag} {i : Nat} :
    ∀ {l : List Nat}, l.Nodup → i ∈ l → (f i).Perm (g i ++ X) → (∀ j ∈ l, j ≠ i → f j = g j) →
      (l.flatMap f).Perm (l.flatMap g ++ X)
  | [], _, h, _, _ => absurd h (List.not_mem_nil)
  | j :: l, hnd, hi, hp, he => by
    simp only [List.flatMap_cons]
    have hnd' := List.nodup_cons.1 hnd
    by_cases hji : j = i
    · subst hji
      have hrest : l.flatMap f = l.flatMap g :=
        flatMap_congr' fun k hk => he k (List.mem_cons_of_mem _ hk) (fun h => hnd'.1 (h ▸ hk))
      rw [hrest]
      refine (hp.append_right _).trans ?_
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    · have hi' : i ∈ l := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm hji
        · exact h
      rw [he j List.mem_cons_self hji, List.append_assoc]
      exact List.Perm.append_left _ (flatMap_perm_one hnd'.2 hi' hp fun k hk => he k (List.mem_cons_of_mem _ hk))

theorem bytes_perm {f g : Frag} (h : f.Perm g) : f.bytes.Perm g.bytes := h.flatMap_right _

theorem bytes_append (f g : Frag) : (f ++ g).bytes = f.bytes ++ g.bytes := List.flatMap_append

/-! ## The tcache fragment, block by block -/

/-- Bin `j`'s cells in the tcache fragment. -/
def tcBlock (C : Config) (L : Layout) (key : Nat) (tc : TcacheSt) (j : Nat) : Frag :=
  ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * j, C.tcacheCountWidth, (tc.bins j).length⟩ ::
    Cell.w (tc.addr + L.tcEntries + 8 * j) (((tc.bins j).map (·.1 + C.hdr)).headD 0) ::
      (slist (tcLinks C) ((tc.bins j).map (·.1 + C.hdr)) ++
        ((tc.bins j).map (·.1 + C.hdr)).map fun p => Cell.w (p + 8) key)

theorem getD_one_cons' {a : Nat} {l : List Nat} : (a :: l).getD 1 0 = l.headD 0 := by
  cases l <;> rfl

theorem tcacheFrag_eq (C : Config) (L : Layout) (key : Nat) (tc : TcacheSt) :
    tcacheFrag C L key tc = (List.range C.tcacheBins).flatMap (tcBlock C L key tc) := rfl

theorem mem_bytes' {f : Frag} {c : Cell} (hc : c ∈ f) {a : Nat} (ha : a ∈ List.range' c.addr c.width) :
    a ∈ f.bytes := List.mem_flatMap.2 ⟨c, hc, ha⟩

theorem bytes_single (c : Cell) : Frag.bytes [c] = List.range' c.addr c.width := by
  simp [Frag.bytes]

set_option maxHeartbeats 1600000 in
/-- **The representation step of `tcache_get`** (`Task.x86sim.repTcacheGet` on sane views). -/
theorem repTcacheGet_of {C : Config} {L : Layout} {St : Statics} {T : TlsAddrs} {l l' : Local}
    {tc : TcacheSt} {i p : Nat} {v : MemView} (hrep : LocalRep C L St T l v) (hs : SaneView v)
    (htc : l.thread.tcache = some tc) (hi : i < C.tcacheBins) (hget : l.tcacheGet C i = some (p, l')) :
    LocalRep C L St T l' (v.storeAll
      [Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).getD 1 0),
       ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length - 1⟩,
       Cell.w (p + 8) 0]) := by
  -- the abstract step
  obtain ⟨c, rest, hb⟩ : ∃ c rest, tc.bins i = c :: rest := by
    cases h : tc.bins i with
    | nil => simp [Local.tcacheGet, htc, TcacheSt.get, h] at hget
    | cons c r => exact ⟨c, r, rfl⟩
  let tc' : TcacheSt := { tc with bins := fun j => if j = i then rest else tc.bins j }
  have hget' : l.tcacheGet C i = some (c.1 + C.hdr, { l with thread := { l.thread with tcache := some tc' } }) := by
    simp [Local.tcacheGet, htc, TcacheSt.get, hb, tc']
  rw [hget'] at hget
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hget)
  -- names
  let K : Cell := ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, rest.length + 1⟩
  let E : Cell := Cell.w (tc.addr + L.tcEntries + 8 * i) (c.1 + C.hdr)
  let Lp : Cell := ⟨(c.1 + C.hdr) + 0, 8, C.protect ((c.1 + C.hdr) + 0) ((rest.map (·.1 + C.hdr)).headD 0)⟩
  let Kp : Cell := Cell.w ((c.1 + C.hdr) + 8) l.shared.key
  let K' : Cell := ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, rest.length⟩
  let E' : Cell := Cell.w (tc.addr + L.tcEntries + 8 * i) ((rest.map (·.1 + C.hdr)).headD 0)
  let Z : Cell := Cell.w ((c.1 + C.hdr) + 8) 0
  let g : Nat → Frag := fun j => if j = i then slist (tcLinks C) (rest.map (·.1 + C.hdr)) ++ (rest.map (·.1 + C.hdr)).map (fun q => Cell.w (q + 8) l.shared.key)
    else tcBlock C L l.shared.key tc j
  let tls : Frag := [Cell.w T.tcache tc.addr, Cell.w T.arena (if l.shared.init then l.thread.arena.getD l.avAddr else 0),
    ⟨T.shutdown, 1, if l.thread.shuttingDown then 1 else 0⟩]
  let O : Frag := tls ++ (List.range C.tcacheBins).flatMap g
  have hft : threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread = tls ++ tcacheFrag C L l.shared.key tc := by
    simp [threadFrag, htc, tls]
  have hft' : threadFrag C L T l.avAddr l.shared.key l.shared.init { l.thread with tcache := some tc' } =
      tls ++ tcacheFrag C L l.shared.key tc' := by
    simp [threadFrag, tls, tc']
  have hrange : (List.range C.tcacheBins).Nodup := List.nodup_range
  have hiR : i ∈ List.range C.tcacheBins := List.mem_range.2 hi
  have P1 : (tcBlock C L l.shared.key tc i).Perm (g i ++ [K, E, Lp, Kp]) := by
    simp only [tcBlock, hb, g, List.map_cons, List.length_cons, List.headD_cons, slist_cons,
      tcLinks, ↓reduceIte, K, E, Lp, Kp]
    rw [List.perm_iff_count]; intro a
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have P2 : (tcBlock C L l.shared.key tc' i).Perm (g i ++ [K', E']) := by
    simp only [tcBlock, tc', g, ↓reduceIte, K', E']
    rw [List.perm_iff_count]; intro a
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have Pft : (tls ++ tcacheFrag C L l.shared.key tc).Perm (O ++ [K, E, Lp, Kp]) := by
    rw [tcacheFrag_eq, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_one hrange hiR P1 fun j _ hj => by simp [g, hj])
  have Pft' : (tls ++ tcacheFrag C L l.shared.key tc').Perm (O ++ [K', E']) := by
    rw [tcacheFrag_eq, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_one hrange hiR P2 fun j _ hj => by
      simp [g, hj, tcBlock, tc'])
  -- the stores, as cells of the old fragment's shape
  have hstores : ([Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).getD 1 0),
       ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length - 1⟩,
       Cell.w (c.1 + C.hdr + 8) 0] : Frag) = [E', K', Z] := by
    simp only [hb, List.map_cons, getD_one_cons', List.length_cons, Nat.add_sub_cancel, E', K', Z]
  rw [hstores]
  show LocalRep C L St T _ (((v.store E').store K').store Z)
  obtain ⟨hfa, hftH, hfs, hback, hnd⟩ := hrep
  rw [hft] at hftH hnd
  -- disjointness, from the Nodup
  rw [bytes_append, bytes_append] at hnd
  obtain ⟨hnd12, -, h3⟩ := List.nodup_append.1 hnd
  obtain ⟨-, hndft, h12⟩ := List.nodup_append.1 hnd12
  have hndO := (bytes_perm Pft).nodup_iff.1 hndft
  rw [bytes_append] at hndO
  obtain ⟨-, hndX, hOX⟩ := List.nodup_append.1 hndO
  simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hndX
  obtain ⟨-, hX1, hKr⟩ := List.nodup_append.1 hndX
  obtain ⟨-, hX2, hEr⟩ := List.nodup_append.1 hX1
  obtain ⟨-, -, hLr⟩ := List.nodup_append.1 hX2
  have memft : ∀ d, d ∈ O ++ [K, E, Lp, Kp] → d ∈ tls ++ tcacheFrag C L l.shared.key tc :=
    fun d hd => Pft.mem_iff.2 hd
  have inK : K ∈ tls ++ tcacheFrag C L l.shared.key tc := memft K (by simp)
  have inE : E ∈ tls ++ tcacheFrag C L l.shared.key tc := memft E (by simp)
  have inLp : Lp ∈ tls ++ tcacheFrag C L l.shared.key tc := memft Lp (by simp)
  have inKp : Kp ∈ tls ++ tcacheFrag C L l.shared.key tc := memft Kp (by simp)
  -- every byte of a store is a byte of the old thread fragment
  have stft : ∀ a, (a ∈ List.range' E.addr E.width ∨ a ∈ List.range' K.addr K.width ∨
      a ∈ List.range' Kp.addr Kp.width) → a ∈ (tls ++ tcacheFrag C L l.shared.key tc).bytes := by
    rintro a (h | h | h)
    · exact mem_bytes' inE h
    · exact mem_bytes' inK h
    · exact mem_bytes' inKp h
  have st3 : ∀ d : Cell, d.Holds v → (∀ a ∈ List.range' d.addr d.width, ¬ (a ∈ List.range' E.addr E.width ∨
      a ∈ List.range' K.addr K.width ∨ a ∈ List.range' Kp.addr Kp.width)) →
      d.Holds (((v.store E').store K').store Z) := fun d hd hdis =>
    store_frame (store_frame (store_frame hd fun a ha h => hdis a ha (.inl h))
      fun a ha h => hdis a ha (.inr (.inl h))) fun a ha h => hdis a ha (.inr (.inr h))
  -- values
  obtain ⟨hKl, hKw⟩ := hftH K inK
  obtain ⟨hEl, hEw⟩ := hftH E inE
  obtain ⟨hLl, -⟩ := hftH Lp inLp
  have hKv := load_lt hs _ _ _ hKl
  have hLv := load_lt hs _ _ _ hLl
  have hLa : c.1 + C.hdr + 0 < 2 ^ 64 := load_addr hs (k := 7) hLl
  have hnxt : (rest.map (·.1 + C.hdr)).headD 0 < 256 ^ 8 := by
    simp only [Lp, Config.protect] at hLv
    split at hLv
    · have h1 : (c.1 + C.hdr + 0) / 4096 < 2 ^ 64 := by omega
      have := Nat.xor_lt_two_pow h1 (show _ < 2 ^ 64 from hLv)
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
      exact this
    · exact hLv
  refine ⟨?_, ?_, ?_, backs_store (backs_store (backs_store hback)), ?_⟩
  · -- the arena's cells
    intro d hd
    refine st3 d (hfa d hd) fun a ha h => ?_
    exact h12 a (mem_bytes' hd ha) a (stft a h) rfl
  · -- the thread's cells
    show (threadFrag C L T l.avAddr l.shared.key l.shared.init { l.thread with tcache := some tc' }).Holds _
    rw [hft']
    intro d hd
    rcases List.mem_append.1 (Pft'.mem_iff.1 hd) with hO | hd'
    · refine st3 d (hftH d (memft d (List.mem_append_left _ hO))) fun a ha h => ?_
      exact hOX a (mem_bytes' hO ha) a (by
        rcases h with h | h | h
        · exact List.mem_append_right _ (List.mem_append_left _ h)
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (by
            simpa using h)))) rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
      rcases hd' with rfl | rfl
      · -- K'
        refine store_frame (store_self (v := v.store E') (fun k hk => hKw k hk) (by
          have : rest.length + 1 < 256 ^ C.tcacheCountWidth := hKv
          show rest.length < 256 ^ C.tcacheCountWidth; omega)) fun a ha h => ?_
        exact hKr a ha a (List.mem_append_right _ (List.mem_append_right _
          (show a ∈ List.range' Kp.addr Kp.width from h))) rfl
      · -- E'
        refine store_frame (store_frame (store_self (fun k hk => hEw k hk) hnxt) fun a ha h => ?_)
          fun a ha h => ?_
        · exact hKr a h a (List.mem_append_left _ ha) rfl
        · exact hEr a ha a (List.mem_append_right _
            (show a ∈ List.range' Kp.addr Kp.width from h)) rfl
  · -- the shared cells
    intro d hd
    refine st3 d (hfs d hd) fun a ha h => ?_
    exact h3 a (List.mem_append_right _ (stft a h)) a (mem_bytes' hd ha) rfl
  · -- the bytes stay distinct
    show (Frag.bytes (arenaRep C L l.shared.init l.avAddr l.av ++ threadFrag C L T l.avAddr l.shared.key l.shared.init
      { l.thread with tcache := some tc' } ++ sharedFrag C L St l.shared)).Nodup
    rw [hft', bytes_append, bytes_append]
    have hp1 := bytes_perm Pft'
    have hsub : (O ++ [K', E']).bytes.Sublist (O ++ [K, E, Lp, Kp]).bytes := by
      rw [bytes_append O [K', E'], bytes_append O [K, E, Lp, Kp]]
      refine List.Sublist.append_left ?_ _
      simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.Sublist.append_left (List.sublist_append_left _ _) _
    have hall : ((arenaRep C L l.shared.init l.avAddr l.av).bytes ++ (O ++ [K, E, Lp, Kp]).bytes ++
        (sharedFrag C L St l.shared).bytes).Nodup :=
      (((List.Perm.refl _).append (bytes_perm Pft)).append (List.Perm.refl _)).nodup_iff.1 hnd
    exact (((List.Perm.refl _).append hp1).append (List.Perm.refl _)).nodup_iff.2
      (hall.sublist ((List.Sublist.refl _).append hsub |>.append (List.Sublist.refl _)))

set_option maxHeartbeats 1600000 in
/-- **`tcache_get` adds no byte to the representation**: the new thread fragment's bytes are bytes
of the old one, and the arena and shared parts are unchanged (for `RepApart`). -/
theorem tcGet_thread_bytes {C : Config} {L : Layout} {T : TlsAddrs} {l l' : Local} {tc : TcacheSt}
    {i p : Nat} (htc : l.thread.tcache = some tc) (hi : i < C.tcacheBins)
    (hget : l.tcacheGet C i = some (p, l')) :
    l'.avAddr = l.avAddr ∧ l'.av = l.av ∧ l'.shared = l.shared ∧
      ∀ a ∈ (threadFrag C L T l'.avAddr l'.shared.key l'.shared.init l'.thread).bytes,
        a ∈ (threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread).bytes := by
  obtain ⟨c, rest, hb⟩ : ∃ c rest, tc.bins i = c :: rest := by
    cases h : tc.bins i with
    | nil => simp [Local.tcacheGet, htc, TcacheSt.get, h] at hget
    | cons c r => exact ⟨c, r, rfl⟩
  let tc' : TcacheSt := { tc with bins := fun j => if j = i then rest else tc.bins j }
  have hget' : l.tcacheGet C i = some (c.1 + C.hdr, { l with thread := { l.thread with tcache := some tc' } }) := by
    simp [Local.tcacheGet, htc, TcacheSt.get, hb, tc']
  rw [hget'] at hget
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hget)
  refine ⟨rfl, rfl, rfl, ?_⟩
  let K : Cell := ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, rest.length + 1⟩
  let E : Cell := Cell.w (tc.addr + L.tcEntries + 8 * i) (c.1 + C.hdr)
  let Lp : Cell := ⟨(c.1 + C.hdr) + 0, 8, C.protect ((c.1 + C.hdr) + 0) ((rest.map (·.1 + C.hdr)).headD 0)⟩
  let Kp : Cell := Cell.w ((c.1 + C.hdr) + 8) l.shared.key
  let K' : Cell := ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, rest.length⟩
  let E' : Cell := Cell.w (tc.addr + L.tcEntries + 8 * i) ((rest.map (·.1 + C.hdr)).headD 0)
  let g : Nat → Frag := fun j => if j = i then slist (tcLinks C) (rest.map (·.1 + C.hdr)) ++ (rest.map (·.1 + C.hdr)).map (fun q => Cell.w (q + 8) l.shared.key)
    else tcBlock C L l.shared.key tc j
  let tls : Frag := [Cell.w T.tcache tc.addr, Cell.w T.arena (if l.shared.init then l.thread.arena.getD l.avAddr else 0),
    ⟨T.shutdown, 1, if l.thread.shuttingDown then 1 else 0⟩]
  let O : Frag := tls ++ (List.range C.tcacheBins).flatMap g
  have hft : threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread = tls ++ tcacheFrag C L l.shared.key tc := by
    simp [threadFrag, htc, tls]
  have hft' : threadFrag C L T l.avAddr l.shared.key l.shared.init { l.thread with tcache := some tc' } =
      tls ++ tcacheFrag C L l.shared.key tc' := by
    simp [threadFrag, tls, tc']
  have hrange : (List.range C.tcacheBins).Nodup := List.nodup_range
  have hiR : i ∈ List.range C.tcacheBins := List.mem_range.2 hi
  have P1 : (tcBlock C L l.shared.key tc i).Perm (g i ++ [K, E, Lp, Kp]) := by
    simp only [tcBlock, hb, g, List.map_cons, List.length_cons, List.headD_cons, slist_cons,
      tcLinks, ↓reduceIte, K, E, Lp, Kp]
    rw [List.perm_iff_count]; intro a
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have P2 : (tcBlock C L l.shared.key tc' i).Perm (g i ++ [K', E']) := by
    simp only [tcBlock, tc', g, ↓reduceIte, K', E']
    rw [List.perm_iff_count]; intro a
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have Pft : (tls ++ tcacheFrag C L l.shared.key tc).Perm (O ++ [K, E, Lp, Kp]) := by
    rw [tcacheFrag_eq, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_one hrange hiR P1 fun j _ hj => by simp [g, hj])
  have Pft' : (tls ++ tcacheFrag C L l.shared.key tc').Perm (O ++ [K', E']) := by
    rw [tcacheFrag_eq, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_one hrange hiR P2 fun j _ hj => by
      simp [g, hj, tcBlock, tc'])
  intro a ha
  change a ∈ (threadFrag C L T l.avAddr l.shared.key l.shared.init { l.thread with tcache := some tc' }).bytes at ha
  rw [hft'] at ha
  rw [hft]
  have ha' := (bytes_perm Pft').mem_iff.1 ha
  refine (bytes_perm Pft).mem_iff.2 ?_
  rw [bytes_append] at ha' ⊢
  rcases List.mem_append.1 ha' with h | h
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ ?_
    simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end Silmaril.Libc.Ptmalloc.X86sim
