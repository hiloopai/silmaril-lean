module

public import Silmaril.Proofs.Libc.Ptmalloc.Seplist.Tcache
public import Silmaril.Data.Cells.Thms
public import Silmaril.Data.SepList.Thms
public import Silmaril.Data.Bitmap.Thms

/-!
# ptmalloc, representation: the leaf operations' stores

Each leaf operation of `Silmaril.Libc.Ptmalloc.Algo` changes one component's fragment by a listed
set of stores, in glibc's order: old fragment + stores = new fragment
(`Frag.holds_update_perm`: the old fragment and its fresh cells are a permutation of the store
slots and the kept cells).

* `leafFastPush` (`_int_free`'s fastbin path: `have_fastchunks = true`, `p->fd =
  PROTECT_PTR (&p->fd, old)`, `*fb = p`), `leafFastPop` (`_int_malloc`'s: `*fb =
  REVEAL_PTR (victim->fd)`);
* `leafBinPushFront` (a small bin: `dll` push at the bin's sentinel, then `mark_bin`);
* `leafTcachePut` (`tcache_put`: `e->key`, `e->next`, `entries[i]`, `counts[i]`; the
  `LocalRep`-level step with the machine's view is `X86sim.repTcachePut`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Libc.Ptmalloc.Seplist

open Silmaril.Data
open Silmaril.Data.SepList (slist)

/-- One fastbin's fragment (the body of `fastFrag`). -/
def fastBlk (C : Config) (L : Layout) (avAddr : Nat) (fs : FastSt) (j : Nat) : Frag :=
  Cell.w (avAddr + L.arFastbins + 8 * j) ((fs.lists j).headD 0) :: slist (fastLinks C) (fs.lists j)

theorem fastFrag_eq (C : Config) (L : Layout) (avAddr : Nat) (fs : FastSt) :
    fastFrag C L avAddr fs = ⟨avAddr + L.arHaveFast, 4, if fs.haveFast then 1 else 0⟩ ::
      (List.range C.nFast).flatMap (fastBlk C L avAddr fs) := rfl

theorem range_rest_ne {n i j : Nat} (hj : j ∈ List.range' 0 i ++ List.range' (i + 1) (n - i - 1)) :
    j ≠ i := by
  rcases List.mem_append.1 hj with h | h <;> (rw [List.mem_range'] at h; omega)

/-- `fastFrag` split at bin `i`, for any state that agrees with `fs` on the other bins. -/
theorem fastFrag_split {C : Config} {L : Layout} {avAddr i : Nat} (hi : i < C.nFast) (fs fs' : FastSt)
    (h : ∀ j, j ≠ i → fs'.lists j = fs.lists j) :
    fastFrag C L avAddr fs' = ⟨avAddr + L.arHaveFast, 4, if fs'.haveFast then 1 else 0⟩ ::
      ((List.range' 0 i).flatMap (fastBlk C L avAddr fs) ++ fastBlk C L avAddr fs' i ++
        (List.range' (i + 1) (C.nFast - i - 1)).flatMap (fastBlk C L avAddr fs)) := by
  have hrest : ∀ j ∈ List.range' 0 i ++ List.range' (i + 1) (C.nFast - i - 1),
      fastBlk C L avAddr fs' j = fastBlk C L avAddr fs j := by
    intro j hj
    simp only [fastBlk, h j (range_rest_ne hj)]
  rw [fastFrag_eq, range_split hi, List.flatMap_append, List.flatMap_cons,
    flatMap_congr_mem fun j hj => hrest j (List.mem_append_left _ hj),
    flatMap_congr_mem (l := List.range' (i + 1) _) fun j hj => hrest j (List.mem_append_right _ hj)]
  simp only [List.append_assoc]

/-- **Fastbin push**: `have_fastchunks := 1`, the chunk's `fd := PROTECT_PTR (&fd, head)`, the
head `:= a`. -/
theorem leafFastPush {C : Config} {L : Layout} {avAddr : Nat} {fs : FastSt} {a i : Nat} {v : MemView}
    (hi : i < C.nFast) (hf : (fastFrag C L avAddr fs).Holds v)
    (hS : Frag.Sep (fastFrag C L avAddr fs ++ [⟨a + 16, 8, 0⟩]))
    (hw : ∀ k < 8, v.writable (a + 16 + k) = true) (ha : a < 256 ^ 8)
    (hp : C.protect (a + 16) ((fs.lists i).headD 0) < 256 ^ 8) :
    (fastFrag C L avAddr (fs.push a i)).Holds (v.storeAll
      [⟨avAddr + L.arHaveFast, 4, 1⟩, ⟨a + 16, 8, C.protect (a + 16) ((fs.lists i).headD 0)⟩,
       Cell.w (avAddr + L.arFastbins + 8 * i) a]) := by
  have e0 := fastFrag_split (L := L) (avAddr := avAddr) hi fs fs fun _ _ => rfl
  have e1 := fastFrag_split (L := L) (avAddr := avAddr) hi fs (fs.push a i) fun j hj => by
    simp [FastSt.push, hj]
  have b0 : fastBlk C L avAddr fs i =
      Cell.w (avAddr + L.arFastbins + 8 * i) ((fs.lists i).headD 0) :: slist (fastLinks C) (fs.lists i) := rfl
  have b1 : fastBlk C L avAddr (fs.push a i) i =
      Cell.w (avAddr + L.arFastbins + 8 * i) a ::
        (⟨a + 16, 8, C.protect (a + 16) ((fs.lists i).headD 0)⟩ :: slist (fastLinks C) (fs.lists i)) := by
    simp [fastBlk, FastSt.push, slist, fastLinks]
  have h1 : (fs.push a i).haveFast = true := rfl
  rw [e0, b0] at hf hS
  rw [e1, b1, h1]
  generalize (List.range' 0 i).flatMap (fastBlk C L avAddr fs) = A at hf hS ⊢
  generalize (List.range' (i + 1) (C.nFast - i - 1)).flatMap (fastBlk C L avAddr fs) = B at hf hS ⊢
  generalize slist (fastLinks C) (fs.lists i) = S at hf hS ⊢
  generalize hHF : (⟨avAddr + L.arHaveFast, 4, if fs.haveFast = true then 1 else 0⟩ : Cell) = HF at hf hS
  generalize hHd : Cell.w (avAddr + L.arFastbins + 8 * i) ((fs.lists i).headD 0) = Hd at hf hS
  have hHFH := hf HF (by simp)
  have hHdH := hf Hd (by simp)
  refine Frag.holds_update_perm (X := [⟨a + 16, 8, 0⟩]) (M := [HF, ⟨a + 16, 8, 0⟩, Hd])
    (R := A ++ S ++ B) hS ?_ hf ?_ ?_ ?_
  · rw [List.perm_iff_count]; intro x
    simp only [List.count_cons, List.count_append, List.count_nil, List.cons_append, List.nil_append]
    omega
  · subst hHF hHd; rfl
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · refine ⟨show 1 < 256 ^ 4 by decide, fun k hk => ?_⟩
      subst hHF; exact hHFH.2 k hk
    · exact ⟨hp, hw⟩
    · refine ⟨ha, fun k hk => ?_⟩
      subst hHd; exact hHdH.2 k hk
  · intro c hc
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with h | ((h | h | h | h) | h)
    all_goals first
      | (left; simp [h]; done)
      | (right; constructor <;> simp [h])

/-- **Fastbin pop**: the head `:= REVEAL_PTR (victim->fd)` (the next chunk). -/
theorem leafFastPop {C : Config} {L : Layout} {avAddr : Nat} {fs fs' : FastSt} {a i : Nat}
    {v : MemView} (hi : i < C.nFast) (hpop : fs.pop i = some (a, fs'))
    (hfit : ∀ x ∈ fs.lists i, x < 256 ^ 8)
    (hf : (fastFrag C L avAddr fs).Holds v) (hS : Frag.Sep (fastFrag C L avAddr fs)) :
    (fastFrag C L avAddr fs').Holds (v.storeAll
      [Cell.w (avAddr + L.arFastbins + 8 * i) ((fs'.lists i).headD 0)]) := by
  unfold FastSt.pop at hpop
  split at hpop
  · exact nomatch hpop
  rename_i a' rest hbi
  simp only [Option.some.injEq, Prod.mk.injEq] at hpop
  obtain ⟨rfl, rfl⟩ := hpop
  have hrfit : rest.headD 0 < 256 ^ 8 := by
    cases rest with
    | nil => simp
    | cons x xs => exact hfit x (by rw [hbi]; simp)
  let fs' : FastSt := { fs with lists := fun j => if j = i then rest else fs.lists j }
  have e0 := fastFrag_split (L := L) (avAddr := avAddr) hi fs fs fun _ _ => rfl
  have e1 := fastFrag_split (L := L) (avAddr := avAddr) hi fs fs' fun j hj => by simp [fs', hj]
  have b0 : fastBlk C L avAddr fs i =
      Cell.w (avAddr + L.arFastbins + 8 * i) a' ::
        (⟨a' + 16, 8, C.protect (a' + 16) (rest.headD 0)⟩ :: slist (fastLinks C) rest) := by
    simp [fastBlk, hbi, slist, fastLinks]
  have b1 : fastBlk C L avAddr fs' i =
      Cell.w (avAddr + L.arFastbins + 8 * i) (rest.headD 0) :: slist (fastLinks C) rest := by
    simp [fastBlk, fs']
  have hl1 : (fs'.lists i).headD 0 = rest.headD 0 := by simp [fs']
  have hh1 : fs'.haveFast = fs.haveFast := rfl
  rw [e0, b0] at hf hS
  show (fastFrag C L avAddr fs').Holds _
  rw [e1, b1, hl1, hh1]
  generalize (List.range' 0 i).flatMap (fastBlk C L avAddr fs) = A at hf hS ⊢
  generalize (List.range' (i + 1) (C.nFast - i - 1)).flatMap (fastBlk C L avAddr fs) = B at hf hS ⊢
  generalize slist (fastLinks C) rest = S at hf hS ⊢
  generalize (⟨avAddr + L.arHaveFast, 4, if fs.haveFast = true then 1 else 0⟩ : Cell) = HF at hf hS ⊢
  generalize (⟨a' + 16, 8, C.protect (a' + 16) (rest.headD 0)⟩ : Cell) = Le at hf hS
  generalize hHd : Cell.w (avAddr + L.arFastbins + 8 * i) a' = Hd at hf hS
  have hHdH := hf Hd (by simp)
  refine Frag.holds_update_perm (X := []) (M := [Hd]) (R := HF :: (A ++ Le :: S ++ B))
    (by simpa using hS) ?_ hf ?_ ?_ ?_
  · rw [List.perm_iff_count]; intro x
    simp only [List.count_cons, List.count_append, List.count_nil, List.cons_append, List.nil_append,
      List.append_nil]
    omega
  · subst hHd; rfl
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    refine ⟨hrfit, fun k hk => ?_⟩
    subst hHd; exact hHdH.2 k hk
  · intro c hc
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with h | ((h | h | h) | h)
    all_goals first
      | (left; simp [h]; done)
      | (right; constructor <;> simp [h])

/-- `tcacheFrag` split at bin `i`, for any tcache that agrees with `tc` elsewhere. -/
theorem tcacheFrag_split {C : Config} {L : Layout} {key i : Nat} (hi : i < C.tcacheBins) (tc tc' : TcacheSt)
    (ha : tc'.addr = tc.addr) (h : ∀ j, j ≠ i → tc'.bins j = tc.bins j) :
    tcacheFrag C L key tc' =
      (List.range' 0 i).flatMap (tcBinFrag C L key tc) ++ tcBinFrag C L key tc' i ++
        (List.range' (i + 1) (C.tcacheBins - i - 1)).flatMap (tcBinFrag C L key tc) := by
  have hrest : ∀ j ∈ List.range' 0 i ++ List.range' (i + 1) (C.tcacheBins - i - 1),
      tcBinFrag C L key tc' j = tcBinFrag C L key tc j := by
    intro j hj
    simp only [tcBinFrag, h j (range_rest_ne hj), ha]
  rw [tcacheFrag_eq, range_split hi, List.flatMap_append, List.flatMap_cons,
    flatMap_congr_mem fun j hj => hrest j (List.mem_append_left _ hj),
    flatMap_congr_mem (l := List.range' (i + 1) _) fun j hj => hrest j (List.mem_append_right _ hj)]
  simp only [List.append_assoc]

/-- **`tcache_put`** at the tcache fragment: `e->key := key`, `e->next := PROTECT_PTR (&e->next,
head)`, `entries[i] := e`, `counts[i] += 1` (glibc's order), for an entry `e` (the chunk's
payload) whose two words are fresh. -/
theorem leafTcachePut {C : Config} {L : Layout} {key : Nat} {tc : TcacheSt} {c : Nat × Nat} {i : Nat}
    {v : MemView} (hi : i < C.tcacheBins)
    (hroom : (tc.bins i).length + 1 < 256 ^ C.tcacheCountWidth)
    (hf : (tcacheFrag C L key tc).Holds v)
    (hS : Frag.Sep (tcacheFrag C L key tc ++ [Cell.w (c.1 + C.hdr) 0, Cell.w (c.1 + C.hdr + 8) 0]))
    (hw : ∀ k < 16, v.writable (c.1 + C.hdr + k) = true) (hp : c.1 + C.hdr < 256 ^ 8)
    (hkey : key < 256 ^ 8)
    (hpr : C.protect (c.1 + C.hdr) (((tc.bins i).map (·.1 + C.hdr)).headD 0) < 256 ^ 8) :
    (tcacheFrag C L key (tc.put c i)).Holds (v.storeAll
      [Cell.w (c.1 + C.hdr + 8) key,
       Cell.w (c.1 + C.hdr) (C.protect (c.1 + C.hdr) (((tc.bins i).map (·.1 + C.hdr)).headD 0)),
       Cell.w (tc.addr + L.tcEntries + 8 * i) (c.1 + C.hdr),
       ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length + 1⟩]) := by
  have e0 := tcacheFrag_split (L := L) (key := key) hi tc tc rfl fun _ _ => rfl
  have e1 := tcacheFrag_split (L := L) (key := key) hi tc (tc.put c i) rfl fun j hj => by
    simp [TcacheSt.put, hj]
  have b0 : tcBinFrag C L key tc i =
      ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length⟩ ::
        Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).headD 0) ::
          (slist (tcLinks C) ((tc.bins i).map (·.1 + C.hdr)) ++
            ((tc.bins i).map (·.1 + C.hdr)).map fun p => Cell.w (p + 8) key) := rfl
  have b1 : tcBinFrag C L key (tc.put c i) i =
      ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length + 1⟩ ::
        Cell.w (tc.addr + L.tcEntries + 8 * i) (c.1 + C.hdr) ::
          (Cell.w (c.1 + C.hdr) (C.protect (c.1 + C.hdr) (((tc.bins i).map (·.1 + C.hdr)).headD 0)) ::
            slist (tcLinks C) ((tc.bins i).map (·.1 + C.hdr)) ++
            Cell.w (c.1 + C.hdr + 8) key :: ((tc.bins i).map (·.1 + C.hdr)).map fun p => Cell.w (p + 8) key) := by
    simp [tcBinFrag, TcacheSt.put, slist, tcLinks, Cell.w]
  rw [e0, b0] at hf hS
  rw [e1, b1]
  generalize (List.range' 0 i).flatMap (tcBinFrag C L key tc) = A at hf hS ⊢
  generalize (List.range' (i + 1) (C.tcacheBins - i - 1)).flatMap (tcBinFrag C L key tc) = B at hf hS ⊢
  generalize slist (tcLinks C) ((tc.bins i).map (·.1 + C.hdr)) = S at hf hS ⊢
  generalize ((tc.bins i).map (·.1 + C.hdr)).map (fun p => Cell.w (p + 8) key) = KS at hf hS ⊢
  generalize hK : (⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth,
    (tc.bins i).length⟩ : Cell) = K at hf hS
  generalize hE : Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).headD 0) = E
    at hf hS
  have hKH := hf K (by simp)
  have hEH := hf E (by simp)
  refine Frag.holds_update_perm (X := [Cell.w (c.1 + C.hdr) 0, Cell.w (c.1 + C.hdr + 8) 0])
    (M := [Cell.w (c.1 + C.hdr + 8) 0, Cell.w (c.1 + C.hdr) 0, E, K])
    (R := A ++ S ++ KS ++ B) hS ?_ hf ?_ ?_ ?_
  · rw [List.perm_iff_count]; intro x
    simp only [List.count_cons, List.count_append, List.count_nil, List.cons_append, List.nil_append]
    omega
  · subst hK hE; rfl
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · refine ⟨hkey, fun k hk => ?_⟩
      have := hw (8 + k) (by simp [Cell.w] at hk; omega)
      simpa [Cell.w, Nat.add_assoc] using this
    · exact ⟨hpr, fun k hk => hw k (by simp [Cell.w] at hk; omega)⟩
    · refine ⟨hp, fun k hk => ?_⟩
      subst hE; exact hEH.2 k hk
    · refine ⟨hroom, fun k hk => ?_⟩
      subst hK; exact hKH.2 k hk
  · intro c' hc
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc ⊢
    grind

/-- One bin's fragment (the body of `binsFrag`, bin `k + 2`). -/
def binBlk (C : Config) (L : Layout) (avAddr : Nat) (bs : BinsSt) (sz : Nat → Nat) (k : Nat) : Frag :=
  SepList.dll binLinks (binAt L avAddr (k + 2)) (bs.lists (k + 2)) ++
    (if C.nSmallBins ≤ k + 2 then SepList.skip nsLinks sz (bs.lists (k + 2)) else [])

theorem binsFrag_eq (C : Config) (L : Layout) (avAddr : Nat) (bs : BinsSt) (sz : Nat → Nat) :
    binsFrag C L avAddr bs sz = (List.range (C.nBins - 2)).flatMap (binBlk C L avAddr bs sz) ++
      Silmaril.Data.Bitmap.frag (avAddr + L.arBinmap) 4 4 bs.binmap := rfl

/-- `binsFrag` split at bin `i`, for any bins agreeing with `bs` on the other lists. -/
theorem binsFrag_split {C : Config} {L : Layout} {avAddr i : Nat} {sz : Nat → Nat} (h2 : 2 ≤ i)
    (hiB : i < C.nBins) (bs bs' : BinsSt) (h : ∀ j, j ≠ i → bs'.lists j = bs.lists j) :
    binsFrag C L avAddr bs' sz =
      (List.range' 0 (i - 2)).flatMap (binBlk C L avAddr bs sz) ++ binBlk C L avAddr bs' sz (i - 2) ++
        (List.range' (i - 2 + 1) (C.nBins - 2 - (i - 2) - 1)).flatMap (binBlk C L avAddr bs sz) ++
      Silmaril.Data.Bitmap.frag (avAddr + L.arBinmap) 4 4 bs'.binmap := by
  have hrest : ∀ j ∈ List.range' 0 (i - 2) ++ List.range' (i - 2 + 1) (C.nBins - 2 - (i - 2) - 1),
      binBlk C L avAddr bs' sz j = binBlk C L avAddr bs sz j := by
    intro j hj
    have := range_rest_ne hj
    simp only [binBlk, h (j + 2) (by omega)]
  rw [binsFrag_eq, range_split (show i - 2 < C.nBins - 2 by omega), List.flatMap_append,
    List.flatMap_cons, flatMap_congr_mem fun j hj => hrest j (List.mem_append_left _ hj),
    flatMap_congr_mem (l := List.range' (i - 2 + 1) _) fun j hj => hrest j (List.mem_append_right _ hj)]
  simp only [List.append_assoc]

/-- **Small-bin insertion at the front** (`bck = bin_at (av, i); fwd = bck->fd`): the `dll`
push's four stores (`victim->fd`, `victim->bk`, `bck->fd`, `fwd->bk`), then `mark_bin`'s binmap
word. The stores are pairwise apart, so glibc's order (`mark_bin` first) gives the same state. -/
theorem leafBinPushFront {C : Config} {L : Layout} {avAddr : Nat} {bs : BinsSt} {sz : Nat → Nat}
    {a i : Nat} {v : MemView} (h2 : 2 ≤ i) (hiS : i < C.nSmallBins) (hiB : i < C.nBins)
    (hi128 : i < 128)
    (hf : (binsFrag C L avAddr bs sz).Holds v)
    (hS : Frag.Sep (binsFrag C L avAddr bs sz ++ binLinks.node a 0 0))
    (hfit : ∀ x ∈ binAt L avAddr i :: a :: bs.lists i, x < 256 ^ 8)
    (hw : ∀ k < 8, v.writable (a + 16 + k) = true ∧ v.writable (a + 24 + k) = true) :
    (binsFrag C L avAddr ((bs.pushFront a i).mark i) sz).Holds (v.storeAll
      ([⟨a + 16, 8, (bs.lists i).headD (binAt L avAddr i)⟩, ⟨a + 24, 8, binAt L avAddr i⟩,
        ⟨binAt L avAddr i + 16, 8, a⟩, ⟨(bs.lists i).headD (binAt L avAddr i) + 24, 8, a⟩] ++
       [⟨avAddr + L.arBinmap + 4 * (i / 32), 4,
         Silmaril.Data.Bitmap.word 4 (Silmaril.Data.Bitmap.set bs.binmap i) (i / 32)⟩])) := by
  have hk : i - 2 + 2 = i := by omega
  have e0 := binsFrag_split (L := L) (avAddr := avAddr) (sz := sz) h2 hiB bs bs fun _ _ => rfl
  have e1 := binsFrag_split (L := L) (avAddr := avAddr) (sz := sz) h2 hiB bs ((bs.pushFront a i).mark i)
    fun j hj => by simp [BinsSt.mark, BinsSt.pushFront, hj]
  have hsmall : ¬ C.nSmallBins ≤ i := by omega
  have b0 : binBlk C L avAddr bs sz (i - 2) = SepList.dll binLinks (binAt L avAddr i) (bs.lists i) := by
    simp only [binBlk, hk, hsmall, ↓reduceIte, List.append_nil]
  have b1 : binBlk C L avAddr ((bs.pushFront a i).mark i) sz (i - 2) =
      SepList.dll binLinks (binAt L avAddr i) (a :: bs.lists i) := by
    simp only [binBlk, hk, hsmall, ↓reduceIte, List.append_nil, BinsSt.mark, BinsSt.pushFront]
  have hbm : ((bs.pushFront a i).mark i).binmap = Silmaril.Data.Bitmap.set bs.binmap i := rfl
  rw [e0, b0] at hf hS
  rw [e1, b1, hbm]
  generalize (List.range' 0 (i - 2)).flatMap (binBlk C L avAddr bs sz) = P at hf hS ⊢
  generalize (List.range' (i - 2 + 1) (C.nBins - 2 - (i - 2) - 1)).flatMap (binBlk C L avAddr bs sz) = Q
    at hf hS ⊢
  generalize hs : binAt L avAddr i = s at hf hS hfit ⊢
  generalize hl : bs.lists i = l at hf hS hfit ⊢
  generalize hBM : Silmaril.Data.Bitmap.frag (avAddr + L.arBinmap) 4 4 bs.binmap = BM at hf hS
  -- the separation facts
  have hSa : Frag.Sep ((P ++ SepList.dll binLinks s l ++ (Q ++ BM)) ++ binLinks.node a 0 0) := by
    simpa only [List.append_assoc] using hS
  obtain ⟨hSF, hSX, hFX⟩ := Frag.sep_append.1 hSa
  have hSD : Frag.Sep (SepList.dll binLinks s l) :=
    (Frag.sep_append.1 (Frag.sep_append.1 hSF).1).2.1
  have hslots : (binLinks.slots (a :: s :: l)).Sep := by
    have hXD : Frag.Sep (binLinks.node a 0 0 ++ SepList.dll binLinks s l) :=
      Frag.sep_append.2 ⟨hSX, hSD, fun c hc d hd =>
        (hFX d (List.mem_append_left _ (List.mem_append_right _ hd)) c hc).symm⟩
    unfold Frag.Sep at hXD ⊢
    rw [SepList.slots_cons, Frag.bytes_append, ← SepList.dll_bytes]
    rwa [Frag.bytes_append] at hXD
  have hD : (SepList.dll binLinks s l).Holds v := fun c hc => hf c (by simp [hc])
  have hD' := SepList.dllPushFront binLinks v s a l (by decide) hD hslots
    (fun x hx => hfit x (by simp only [List.mem_cons] at hx ⊢; omega)) fun k hk => hw k hk
  -- the stores' slots
  have hslot : ∀ d ∈ ([⟨a + 16, 8, l.headD s⟩, ⟨a + 24, 8, s⟩, ⟨s + 16, 8, a⟩,
      ⟨l.headD s + 24, 8, a⟩] : Frag), ∃ e ∈ SepList.dll binLinks s l ++ binLinks.node a 0 0,
        e.addr = d.addr ∧ e.width = d.width := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨⟨a + 16, 8, 0⟩, by simp [SepList.Links.node, binLinks], rfl, rfl⟩
    · exact ⟨⟨a + 24, 8, 0⟩, by simp [SepList.Links.node, binLinks], rfl, rfl⟩
    · exact ⟨⟨s + 16, 8, l.headD s⟩, by simp [SepList.dll, binLinks], rfl, rfl⟩
    · cases l with
      | nil => exact ⟨⟨s + 24, 8, s⟩, by simp [SepList.dll, binLinks], rfl, rfl⟩
      | cons x xs => exact ⟨⟨x + 24, 8, s⟩, by simp [SepList.dll, SepList.dseg, binLinks], rfl, rfl⟩
  have hA := Frag.holds_block_step (P := P) (D := SepList.dll binLinks s l) (Q := Q ++ BM)
    (X := binLinks.node a 0 0) hSa (by simpa only [List.append_assoc] using hf) hD' hslot
  -- the binmap store
  have hA' : Frag.Holds (v.storeAll
      [⟨a + 16, 8, l.headD s⟩, ⟨a + 24, 8, s⟩, ⟨s + 16, 8, a⟩, ⟨l.headD s + 24, 8, a⟩])
      (P ++ SepList.dll binLinks s (a :: l) ++ (Q ++ BM)) := hA
  clear hA
  have hsplit : ∀ (st : Frag) (W : Cell), v.storeAll (st ++ [W]) = (v.storeAll st).store W := by
    intro st W; simp [MemView.storeAll, List.foldl_append]
  rw [hsplit]
  generalize v.storeAll [⟨a + 16, 8, l.headD s⟩, ⟨a + 24, 8, s⟩, ⟨s + 16, 8, a⟩,
    ⟨l.headD s + 24, 8, a⟩] = v1 at hA' ⊢
  have hA := hA'
  have hBM1 : BM.Holds v1 := fun c hc => hA c (by simp [hc])
  rw [← hBM] at hBM1
  have hset := Silmaril.Data.Bitmap.bitmapSet (avAddr + L.arBinmap) 4 4 bs.binmap v1 i true (by decide)
    (by omega) hBM1
  simp only [↓reduceIte, show 8 * 4 = 32 from rfl] at hset
  -- the word cell of the old binmap that the store replaces
  have hWc : (⟨avAddr + L.arBinmap + 4 * (i / 32), 4, Silmaril.Data.Bitmap.word 4 bs.binmap (i / 32)⟩ : Cell) ∈ BM := by
    rw [← hBM]
    exact List.mem_map.2 ⟨i / 32, List.mem_range.2 (by omega), rfl⟩
  have hall : (Frag.bytes P ++ (SepList.dll binLinks s l).bytes ++ Frag.bytes Q ++ Frag.bytes BM ++
      (binLinks.node a 0 0).bytes).Nodup := by
    have := hS; unfold Frag.Sep at this
    simpa only [Frag.bytes_append, List.append_assoc] using this
  have nd : ∀ {l1 l2 : List Nat}, (l1 ++ l2).Nodup → ∀ {x}, x ∈ l1 → x ∈ l2 → False :=
    fun h _ h1 h2 => (List.nodup_append.1 h).2.2 _ h1 _ h2 rfl
  have hn4 := (List.nodup_append.1 hall).1
  have eD : (SepList.dll binLinks s l).bytes =
      (binLinks.node s 0 0).bytes ++ (binLinks.slots l).bytes := by
    rw [SepList.dll_bytes, SepList.slots_cons, Frag.bytes_append]
  have hfar : ∀ c ∈ P ++ SepList.dll binLinks s (a :: l) ++ Q, c.Apart
      ⟨avAddr + L.arBinmap + 4 * (i / 32), 4, Silmaril.Data.Bitmap.word 4 (Silmaril.Data.Bitmap.set bs.binmap i) (i / 32)⟩ := by
    intro c hc
    refine Cell.apart_of_bytes fun x hx hxW => ?_
    have hxBM : x ∈ Frag.bytes BM := List.mem_flatMap.2 ⟨_, hWc, hxW⟩
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact nd hn4 (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.2 ⟨c, hc, hx⟩ : x ∈ Frag.bytes P))) hxBM
    · have hxD' : x ∈ (SepList.dll binLinks s (a :: l)).bytes := List.mem_flatMap.2 ⟨c, hc, hx⟩
      have e3 : (binLinks.slots (s :: a :: l)).bytes = (binLinks.node s 0 0).bytes ++
          ((binLinks.node a 0 0).bytes ++ (binLinks.slots l).bytes) := by
        rw [SepList.slots_cons, SepList.slots_cons, Frag.bytes_append, Frag.bytes_append]
      rw [SepList.dll_bytes, e3] at hxD'
      rcases List.mem_append.1 hxD' with h | h
      · exact nd hn4 (List.mem_append_left _ (List.mem_append_right _
          (show x ∈ (SepList.dll binLinks s l).bytes by rw [eD]; exact List.mem_append_left _ h))) hxBM
      · rcases List.mem_append.1 h with h | h
        · exact nd hall (List.mem_append_right _ hxBM) h
        · exact nd hn4 (List.mem_append_left _ (List.mem_append_right _
            (show x ∈ (SepList.dll binLinks s l).bytes by rw [eD]; exact List.mem_append_right _ h))) hxBM
    · exact nd hn4 (List.mem_append_right _
        (List.mem_flatMap.2 ⟨c, hc, hx⟩ : x ∈ Frag.bytes Q)) hxBM
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · exact (Cell.holds_store_apart (hfar c (by simp [hc]))).2 (hA c (by simp [hc]))
  · exact (Cell.holds_store_apart (hfar c (by simp [hc]))).2 (hA c (by simp [hc]))
  · exact (Cell.holds_store_apart (hfar c (by simp [hc]))).2 (hA c (by simp [hc]))
  · exact hset c hc

end Silmaril.Libc.Ptmalloc.Seplist
