module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.RepTcGet

/-!
# ptmalloc x86sim: the representation step of `tcache_put` (layer c), proved

`repTcachePut_of`: `tcache_put`'s four stores (`e->key`, `e->next`, `entries[i]`, `counts[i]`)
turn `LocalRep … l` into `LocalRep … l'` for `l.tcachePut (a, sz) i = some l'`, for a chunk of
the arena whose first two payload words hold no cell (`PayloadFresh`), on a view of machine
bytes. x86-free; the same permutation argument as `repTcacheGet_of`, with two fresh cells.
-/

@[expose] public section

open Silmaril.Data
open Silmaril.Data.SepList (SLinks slist)
namespace Silmaril.Libc.Ptmalloc.X86sim

/-- **The chunk's first two payload words hold no cell** of the representation of `l`. -/
def PayloadFresh (C : Config) (L : Layout) (St : Statics) (T : TlsAddrs) (l : Local) (a : Nat) :
    Prop :=
  ∀ k < 16, a + C.hdr + k ∉ (arenaRep C L l.shared.init l.avAddr l.av ++
    threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread ++ sharedFrag C L St l.shared).bytes

/-- **The abstract preconditions of `tcache_put`** at its call in `_int_free`. -/
def TcPutAbs (C : Config) (l : Local) (a sz i : Nat) (tc : TcacheSt) : Prop :=
  l.thread.tcache = some tc ∧ i < C.tcacheBins ∧ C.tidx sz = i ∧ sz % C.align = 0 ∧ C.minSize ≤ sz ∧
    a ≠ 0 ∧ a % C.align = 0 ∧ (a, sz) ∉ tc.bins i ∧ (tc.bins i).length < C.tcacheCount ∧
    ∃ d ∈ l.av.chunks, d.addr = a ∧ d.size = sz


set_option maxHeartbeats 1600000 in
/-- **The representation step of `tcache_put`.** -/
theorem repTcachePut_of {C : Config} {L : Layout} {St : Statics} {T : TlsAddrs} {l l' : Local}
    {tc : TcacheSt} {a sz i : Nat} {v : MemView} (hok : C.Ok) (hcw : C.tcacheCount < 256 ^ C.tcacheCountWidth)
    (hrep : LocalRep C L St T l v) (hs : SaneView v) (habs : TcPutAbs C l a sz i tc)
    (hfresh : PayloadFresh C L St T l a) (hput : l.tcachePut (a, sz) i = some l') :
    LocalRep C L St T l' (v.storeAll
      [Cell.w (a + C.hdr + 8) l.shared.key,
       Cell.w (a + C.hdr) (C.protect (a + C.hdr) (((tc.bins i).map (·.1 + C.hdr)).headD 0)),
       Cell.w (tc.addr + L.tcEntries + 8 * i) (a + C.hdr),
       ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length + 1⟩]) := by
  obtain ⟨htc, hi, -, -, hszm, -, -, -, hroom, d, hd, hda, hds⟩ := habs
  let tc' := tc.put (a, sz) i
  have hput' : l.tcachePut (a, sz) i = some { l with thread := { l.thread with tcache := some tc' } } := by
    simp [Local.tcachePut, htc, tc']
  rw [hput'] at hput
  cases Option.some.inj hput
  let K : Cell := ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length⟩
  let E : Cell := Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).headD 0)
  let K' : Cell := ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length + 1⟩
  let E' : Cell := Cell.w (tc.addr + L.tcEntries + 8 * i) (a + C.hdr)
  let Le : Cell := ⟨a + C.hdr + 0, 8, C.protect (a + C.hdr + 0) (((tc.bins i).map (·.1 + C.hdr)).headD 0)⟩
  let Kp : Cell := Cell.w (a + C.hdr + 8) l.shared.key
  let g : Nat → Frag := fun j => if j = i then
      slist (tcLinks C) ((tc.bins i).map (·.1 + C.hdr)) ++
        ((tc.bins i).map (·.1 + C.hdr)).map (fun q => Cell.w (q + 8) l.shared.key)
    else tcBlock C L l.shared.key tc j
  let tls : Frag := [Cell.w T.tcache tc.addr, Cell.w T.arena (if l.shared.init then l.thread.arena.getD l.avAddr else 0),
    ⟨T.shutdown, 1, if l.thread.shuttingDown then 1 else 0⟩]
  let O : Frag := tls ++ (List.range C.tcacheBins).flatMap g
  have hft : threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread = tls ++ tcacheFrag C L l.shared.key tc := by
    simp [threadFrag, htc, tls]
  have hft' : threadFrag C L T l.avAddr l.shared.key l.shared.init { l.thread with tcache := some tc' } =
      tls ++ tcacheFrag C L l.shared.key tc' := by
    simp [threadFrag, tls, tc', TcacheSt.put]
  have hrange : (List.range C.tcacheBins).Nodup := List.nodup_range
  have hiR : i ∈ List.range C.tcacheBins := List.mem_range.2 hi
  have P1 : (tcBlock C L l.shared.key tc i).Perm (g i ++ [K, E]) := by
    simp only [tcBlock, g, ↓reduceIte, K, E]
    rw [List.perm_iff_count]; intro x
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have P2 : (tcBlock C L l.shared.key tc' i).Perm (g i ++ [K', E', Le, Kp]) := by
    simp only [tcBlock, tc', TcacheSt.put, g, ↓reduceIte, List.map_cons, List.length_cons, List.headD_cons,
      slist_cons, tcLinks, K', E', Le, Kp]
    rw [List.perm_iff_count]; intro x
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have Pft : (tls ++ tcacheFrag C L l.shared.key tc).Perm (O ++ [K, E]) := by
    rw [tcacheFrag_eq, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_one hrange hiR P1 fun j _ hj => by simp [g, hj])
  have Pft' : (tls ++ tcacheFrag C L l.shared.key tc').Perm (O ++ [K', E', Le, Kp]) := by
    rw [tcacheFrag_eq, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_one hrange hiR P2 fun j _ hj => by
      simp [g, hj, tcBlock, tc', TcacheSt.put])
  have hhdr : C.hdr = 16 := by simp [Config.hdr, hok.sizeSz]
  have hsz32 : 32 ≤ d.size := by rw [hds, ← hok.minSize]; exact hszm
  -- the stores, named
  have hLe : Cell.w (a + C.hdr) (C.protect (a + C.hdr) (((tc.bins i).map (·.1 + C.hdr)).headD 0)) = Le := by
    simp [Cell.w, Le]
  rw [hLe]
  show LocalRep C L St T _ ((((v.store Kp).store Le).store E').store K')
  obtain ⟨hfa, hftH, hfs, hback, hnd⟩ := hrep
  simp only [PayloadFresh] at hfresh
  rw [hft] at hftH hnd hfresh
  rw [bytes_append, bytes_append] at hnd
  obtain ⟨hnd12, -, h3⟩ := List.nodup_append.1 hnd
  obtain ⟨-, hndft, h12⟩ := List.nodup_append.1 hnd12
  have hndO := (bytes_perm Pft).nodup_iff.1 hndft
  rw [bytes_append] at hndO
  obtain ⟨-, hndX, hOX⟩ := List.nodup_append.1 hndO
  simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hndX
  obtain ⟨-, -, hKE⟩ := List.nodup_append.1 hndX
  have memft : ∀ c, c ∈ O ++ [K, E] → c ∈ tls ++ tcacheFrag C L l.shared.key tc :=
    fun c hc => Pft.mem_iff.2 hc
  have inK : K ∈ tls ++ tcacheFrag C L l.shared.key tc := memft K (by simp)
  have inE : E ∈ tls ++ tcacheFrag C L l.shared.key tc := memft E (by simp)
  -- every old byte avoids the payload words
  have fr : ∀ x, x ∈ (arenaRep C L l.shared.init l.avAddr l.av).bytes ++ (tls ++ tcacheFrag C L l.shared.key tc).bytes ++
      (sharedFrag C L St l.shared).bytes → ∀ k < 16, x ≠ a + C.hdr + k := by
    intro x hx k hk h; subst h
    exact hfresh k hk (by rw [bytes_append, bytes_append]; exact hx)
  have inF : ∀ x, (x ∈ List.range' Le.addr Le.width ∨ x ∈ List.range' Kp.addr Kp.width) →
      ∃ k < 16, x = a + C.hdr + k := by
    rintro x (h | h)
    · obtain ⟨k, hk, rfl⟩ := List.mem_range'.1 h
      exact ⟨k, by have : Le.width = 8 := rfl; omega, by simp [Le]⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_range'.1 h
      exact ⟨8 + k, by simp [Kp, Cell.w] at hk; omega, by simp [Kp, Cell.w]; omega⟩
  have oldF : ∀ x, x ∈ (arenaRep C L l.shared.init l.avAddr l.av).bytes ++ (tls ++ tcacheFrag C L l.shared.key tc).bytes ++
      (sharedFrag C L St l.shared).bytes → ¬ (x ∈ List.range' Le.addr Le.width ∨ x ∈ List.range' Kp.addr Kp.width) :=
    fun x hx h => by obtain ⟨k, hk, rfl⟩ := inF x h; exact fr _ hx k hk rfl
  have st4 : ∀ c : Cell, c.Holds v → (∀ x ∈ List.range' c.addr c.width, ¬ (x ∈ List.range' Le.addr Le.width ∨
      x ∈ List.range' Kp.addr Kp.width) ∧ ¬ (x ∈ List.range' E.addr E.width ∨ x ∈ List.range' K.addr K.width)) →
      c.Holds ((((v.store Kp).store Le).store E').store K') := fun c hc hdis =>
    store_frame (store_frame (store_frame (store_frame hc fun x hx h => (hdis x hx).1 (.inr h))
      fun x hx h => (hdis x hx).1 (.inl h)) fun x hx h => (hdis x hx).2 (.inl h))
      fun x hx h => (hdis x hx).2 (.inr h)
  have ft_EK : ∀ x, (x ∈ List.range' E.addr E.width ∨ x ∈ List.range' K.addr K.width) →
      x ∈ (tls ++ tcacheFrag C L l.shared.key tc).bytes := by
    rintro x (h | h)
    · exact mem_bytes' inE h
    · exact mem_bytes' inK h
  -- values and permissions
  obtain ⟨hKl, hKw⟩ := hftH K inK
  obtain ⟨hEl, hEw⟩ := hftH E inE
  obtain ⟨hkl, -⟩ := hfs (Cell.w St.tcacheKey l.shared.key) (by simp [sharedFrag])
  have hkv := load_lt hs _ _ _ hkl
  have hEv := load_lt hs _ _ _ hEl
  have hbk := hback _ (List.mem_append_left _ (List.mem_map.2 ⟨d, hd, rfl⟩))
  rw [hda] at hbk
  have pw : ∀ k < 16, v.writable (a + C.hdr + k) = true := fun k hk => by
    have := (hbk (C.hdr + k) (by rw [hds]; omega)).2
    rwa [← Nat.add_assoc] at this
  have he64 : a + C.hdr + 15 < 2 ^ 64 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hbk (C.hdr + 15) (by rw [hds]; omega)).1
    rw [← Nat.add_assoc] at hb
    exact (hs _ b hb).2
  have hLv : Le.val < 256 ^ Le.width := by
    show C.protect (a + C.hdr + 0) _ < 256 ^ 8
    simp only [Config.protect]
    split
    · exact Nat.xor_lt_two_pow (show _ < 2 ^ 64 by omega) (show _ < 2 ^ 64 from hEv)
    · exact hEv
  refine ⟨?_, ?_, ?_, backs_store (backs_store (backs_store (backs_store hback))), ?_⟩
  · intro c hc
    refine st4 c (hfa c hc) fun x hx => ⟨oldF x ?_, fun h => h12 x (mem_bytes' hc hx) x (ft_EK x h) rfl⟩
    exact List.mem_append_left _ (List.mem_append_left _ (mem_bytes' hc hx))
  · show (threadFrag C L T l.avAddr l.shared.key l.shared.init { l.thread with tcache := some tc' }).Holds _
    rw [hft']
    intro c hc
    rcases List.mem_append.1 (Pft'.mem_iff.1 hc) with hO | hc'
    · refine st4 c (hftH c (memft c (List.mem_append_left _ hO))) fun x hx => ⟨oldF x ?_, fun h => ?_⟩
      · exact List.mem_append_left _ (List.mem_append_right _
          (mem_bytes' (memft c (List.mem_append_left _ hO)) hx))
      · exact hOX x (mem_bytes' hO hx) x (by
          rcases h with h | h
          · exact List.mem_append_right _ h
          · exact List.mem_append_left _ h) rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      have oldEK : ∀ x, (x ∈ List.range' E.addr E.width ∨ x ∈ List.range' K.addr K.width) →
          ¬ (x ∈ List.range' Le.addr Le.width ∨ x ∈ List.range' Kp.addr Kp.width) := fun x h =>
        oldF x (List.mem_append_left _ (List.mem_append_right _ (ft_EK x h)))
      rcases hc' with rfl | rfl | rfl | rfl
      · -- K'
        exact store_self (fun k hk => hKw k hk) (show (tc.bins i).length + 1 < 256 ^ C.tcacheCountWidth by omega)
      · -- E'
        refine store_frame (store_self (fun k hk => hEw k hk) (show a + C.hdr < 256 ^ 8 by omega)) ?_
        intro x hx h; exact hKE x h x hx rfl
      · -- Le
        refine store_frame (store_frame (store_self (fun k hk => by
            have h8 : Le.width = 8 := rfl
            show v.writable _ = true
            simpa [Le] using pw k (by omega)) hLv) ?_) ?_
        · intro x hx h; exact oldEK x (.inl h) (.inl hx)
        · intro x hx h; exact oldEK x (.inr h) (.inl hx)
      · -- Kp
        refine store_frame (store_frame (store_frame (store_self (fun k hk => by
            simpa [Kp, Cell.w, Nat.add_assoc] using pw (8 + k) (by simp [Kp, Cell.w] at hk; omega))
            (show l.shared.key < 256 ^ 8 from hkv)) ?_) ?_) ?_
        · intro x hx h
          obtain ⟨k, hk, rfl⟩ := List.mem_range'.1 hx
          obtain ⟨k', hk', hkk⟩ := List.mem_range'.1 h
          simp [Kp, Le, Cell.w] at hk hk' hkk; omega
        · intro x hx h; exact oldEK x (.inl h) (.inr hx)
        · intro x hx h; exact oldEK x (.inr h) (.inr hx)
  · intro c hc
    refine st4 c (hfs c hc) fun x hx => ⟨oldF x ?_, fun h => h3 x (List.mem_append_right _ (ft_EK x h)) x
      (mem_bytes' hc hx) rfl⟩
    exact List.mem_append_right _ (mem_bytes' hc hx)
  · show (Frag.bytes (arenaRep C L l.shared.init l.avAddr l.av ++ threadFrag C L T l.avAddr l.shared.key l.shared.init
      { l.thread with tcache := some tc' } ++ sharedFrag C L St l.shared)).Nodup
    rw [hft', bytes_append (arenaRep C L l.shared.init l.avAddr l.av ++ (tls ++ tcacheFrag C L l.shared.key tc')),
      bytes_append (arenaRep C L l.shared.init l.avAddr l.av)]
    have hF : (List.range' Le.addr Le.width ++ List.range' Kp.addr Kp.width).Nodup := by
      have : List.range' Le.addr Le.width ++ List.range' Kp.addr Kp.width = List.range' (a + C.hdr) 16 := by
        simp [Le, Kp, Cell.w, List.range'_append_1]
      rw [this]; exact List.nodup_range'
    have hall : ((arenaRep C L l.shared.init l.avAddr l.av).bytes ++ (tls ++ tcacheFrag C L l.shared.key tc).bytes ++
        (sharedFrag C L St l.shared).bytes ++ (List.range' Le.addr Le.width ++ List.range' Kp.addr Kp.width)).Nodup :=
      List.nodup_append.2 ⟨hnd, hF, fun x hx y hy hxy => by subst hxy; exact oldF x hx (List.mem_append.1 hy)⟩
    have q1 : (tls ++ tcacheFrag C L l.shared.key tc').bytes.Perm
        ((tls ++ tcacheFrag C L l.shared.key tc).bytes ++
          (List.range' Le.addr Le.width ++ List.range' Kp.addr Kp.width)) := by
      refine (bytes_perm Pft').trans ?_
      have : (O ++ [K', E', Le, Kp]).bytes = (O ++ [K, E]).bytes ++
          (List.range' Le.addr Le.width ++ List.range' Kp.addr Kp.width) := by
        rw [bytes_append O, bytes_append O]
        simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
        rfl
      rw [this]; exact (bytes_perm Pft).symm.append_right _
    refine (List.Perm.nodup_iff ?_).2 hall
    refine ((List.Perm.refl _).append q1).append (List.Perm.refl _) |>.trans ?_
    generalize (arenaRep C L l.shared.init l.avAddr l.av).bytes = A
    generalize (tls ++ tcacheFrag C L l.shared.key tc).bytes = B
    generalize (sharedFrag C L St l.shared).bytes = D
    generalize List.range' Le.addr Le.width ++ List.range' Kp.addr Kp.width = F
    rw [List.append_assoc A (B ++ F) D, List.append_assoc B F D,
      List.append_assoc A B D, List.append_assoc A (B ++ D) F, List.append_assoc B D F]
    exact List.Perm.append_left _ (List.Perm.append_left _ List.perm_append_comm)

set_option maxHeartbeats 1600000 in
/-- **`tcache_put` adds only the entry's two words to the representation**: every byte of the new
thread fragment is a byte of the old one or one of the 16 bytes at the payload, and the arena and
shared parts are unchanged (for `RepApart`). -/
theorem tcPut_thread_bytes {C : Config} {L : Layout} {T : TlsAddrs} {l l' : Local} {tc : TcacheSt}
    {a sz i : Nat} (htc : l.thread.tcache = some tc) (hi : i < C.tcacheBins)
    (hput : l.tcachePut (a, sz) i = some l') :
    l'.avAddr = l.avAddr ∧ l'.av = l.av ∧ l'.shared = l.shared ∧
      ∀ x ∈ (threadFrag C L T l'.avAddr l'.shared.key l'.shared.init l'.thread).bytes,
        x ∈ (threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread).bytes ∨
          ∃ k < 16, x = a + C.hdr + k := by
  let tc' := tc.put (a, sz) i
  have hput' : l.tcachePut (a, sz) i = some { l with thread := { l.thread with tcache := some tc' } } := by
    simp [Local.tcachePut, htc, tc']
  rw [hput'] at hput
  cases Option.some.inj hput
  refine ⟨rfl, rfl, rfl, ?_⟩
  let K : Cell := ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length⟩
  let E : Cell := Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).headD 0)
  let K' : Cell := ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length + 1⟩
  let E' : Cell := Cell.w (tc.addr + L.tcEntries + 8 * i) (a + C.hdr)
  let Le : Cell := ⟨a + C.hdr + 0, 8, C.protect (a + C.hdr + 0) (((tc.bins i).map (·.1 + C.hdr)).headD 0)⟩
  let Kp : Cell := Cell.w (a + C.hdr + 8) l.shared.key
  let g : Nat → Frag := fun j => if j = i then
      slist (tcLinks C) ((tc.bins i).map (·.1 + C.hdr)) ++
        ((tc.bins i).map (·.1 + C.hdr)).map (fun q => Cell.w (q + 8) l.shared.key)
    else tcBlock C L l.shared.key tc j
  let tls : Frag := [Cell.w T.tcache tc.addr, Cell.w T.arena (if l.shared.init then l.thread.arena.getD l.avAddr else 0),
    ⟨T.shutdown, 1, if l.thread.shuttingDown then 1 else 0⟩]
  let O : Frag := tls ++ (List.range C.tcacheBins).flatMap g
  have hft : threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread = tls ++ tcacheFrag C L l.shared.key tc := by
    simp [threadFrag, htc, tls]
  have hft' : threadFrag C L T l.avAddr l.shared.key l.shared.init { l.thread with tcache := some tc' } =
      tls ++ tcacheFrag C L l.shared.key tc' := by
    simp [threadFrag, tls, tc', TcacheSt.put]
  have hrange : (List.range C.tcacheBins).Nodup := List.nodup_range
  have hiR : i ∈ List.range C.tcacheBins := List.mem_range.2 hi
  have P1 : (tcBlock C L l.shared.key tc i).Perm (g i ++ [K, E]) := by
    simp only [tcBlock, g, ↓reduceIte, K, E]
    rw [List.perm_iff_count]; intro x
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have P2 : (tcBlock C L l.shared.key tc' i).Perm (g i ++ [K', E', Le, Kp]) := by
    simp only [tcBlock, tc', TcacheSt.put, g, ↓reduceIte, List.map_cons, List.length_cons, List.headD_cons,
      slist_cons, tcLinks, K', E', Le, Kp]
    rw [List.perm_iff_count]; intro x
    simp only [List.count_cons, List.count_append, List.count_nil]
    omega
  have Pft : (tls ++ tcacheFrag C L l.shared.key tc).Perm (O ++ [K, E]) := by
    rw [tcacheFrag_eq, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_one hrange hiR P1 fun j _ hj => by simp [g, hj])
  have Pft' : (tls ++ tcacheFrag C L l.shared.key tc').Perm (O ++ [K', E', Le, Kp]) := by
    rw [tcacheFrag_eq, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_one hrange hiR P2 fun j _ hj => by
      simp [g, hj, tcBlock, tc', TcacheSt.put])
  intro x hx
  change x ∈ (threadFrag C L T l.avAddr l.shared.key l.shared.init { l.thread with tcache := some tc' }).bytes at hx
  rw [hft'] at hx
  rw [hft]
  have hx' := (bytes_perm Pft').mem_iff.1 hx
  rw [bytes_append] at hx'
  rcases List.mem_append.1 hx' with h | h
  · exact .inl ((bytes_perm Pft).mem_iff.2 (by rw [bytes_append]; exact List.mem_append_left _ h))
  · simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at h
    rcases h with h | h | h | h
    · refine .inl ((bytes_perm Pft).mem_iff.2 (by
        rw [bytes_append]; refine List.mem_append_right _ ?_
        simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
        exact Or.inl h))
    · refine .inl ((bytes_perm Pft).mem_iff.2 (by
        rw [bytes_append]; refine List.mem_append_right _ ?_
        simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
        exact Or.inr h))
    · obtain ⟨k, hk, rfl⟩ := List.mem_range'.1 h
      exact .inr ⟨k, by have : Le.width = 8 := rfl; omega, by simp [Le]⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_range'.1 h
      exact .inr ⟨8 + k, by simp [Kp, Cell.w] at hk; omega, by simp [Kp, Cell.w]; omega⟩

end Silmaril.Libc.Ptmalloc.X86sim
