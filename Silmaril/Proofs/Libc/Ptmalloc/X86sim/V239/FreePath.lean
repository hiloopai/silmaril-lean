module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.FreeWords
public import Silmaril.Libc.Ptmalloc.Algo.Thms

/-!
# ptmalloc x86sim, glibc 2.39: `__libc_free`'s tcache path simulates `_int_free`

`freeTcachePut239` (on `Str9Fs`) and `freeTcachePut239K` (on `Str9K`): from the entry of
`__libc_free (p)` with `FreeEntry` (the chunk `ch` at `p - 16` is a lent-out chunk of the arena
the body sees, the thread has a tcache whose bin `tidx ch.size` has room and does not hold
`ch`), the run returns to the caller with the callee-saved registers restored, the model's
`_int_free` of `ch` succeeds with `l'`, the machine represents `(l', surr, [])`, and the run
wrote only its two stack frames (`fstk`) and `tcache_put`'s four cells. `errno` is saved and
restored (`errno := errno`): its bytes are unchanged, so it is not in the footprint.

It is a composition of blocks:

* `free_front` (copied runs, memory abstract: `FreeFront`): `__libc_free`'s entry, `_int_free`'s
  checks and either branch of the `e->key == tcache_key` test, the bin walked (`tcWalk_of`: a
  represented bin is the list the walk follows), the count test; the frame lemma `localAt_ww`
  keeps `LocalAt` (it writes only the stack);
* the generic `tcache_put` block with its frame (`tcPutCore`);
* `int_ret` and `free_ret`, the two epilogues.

The heap reasoning is the leaf lemma pair `Task.algo.leafTcachePut` / `Task.x86sim.repTcachePut`
of `tcPutCore` and the algorithm's `Algo.intFree_tcache_eq` (`_int_free`'s tcache case is
`tcache_put`).

Representation facts this path needs, carried by `FreeEntry` until `LocalAt` states them (the
x86sim findings 2 and 3): the stack window and the block's cells apart from the representation,
the surroundings, the code and each other, and `PayloadFresh`. The chunk's size word reads
neither `IS_MMAPPED` nor `NON_MAIN_ARENA` (`mem_arenaFrag_hdr`): `LocalRep` does not record
`NON_MAIN_ARENA` for a non-main arena's chunks, so for such an arena this theorem is about a
representation glibc would not produce (design finding F-1: `arenaFrag` should set the bit off
the main arena; then `__libc_free` takes `arena_for_chunk`'s `heap_for_ptr` branch, not
proved here).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Data
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.V239
set_option maxRecDepth 100000

/-- The arguments of `_int_free`'s `tcache_put` for the chunk `ch`: address, size, bin. -/
def freeArgs (ch : Chunk) : List Nat := [ch.addr, ch.size, pin239.config.tidx ch.size]

/-- `tcache_put`'s cells for freeing `ch` from the state `x`. -/
abbrev freeCells (L : Layout) (x : AState) (ch : Chunk) : Frag :=
  tcPutCells pin239.config L (x.1, x.2.1, freeArgs ch)

/-- **The entry of `__libc_free (ch.addr + 16)` on its tcache path**, at load base `base`, thread
pointer `tp`, TLS offset `off`, stack pointer `sp`, return address `ret`, registers `regs`. -/
structure FreeEntry (base tp off : Nat) (x : AState) (ch : Chunk) (sp ret : Word) (regs : Reg → Word)
    (m : MState) : Prop where
  loaded : Loaded m.memory (freeAt base) freeCode
  loadedI : Loaded m.memory (intFreeAt base) intFreeCode
  rip : m.core.rip = freeAt base + BitVec.ofNat 64 0
  regsEq : ∀ r, m.core.read r = regs r
  rsp : regs .rsp = sp
  rdi : regs .rdi = BitVec.ofNat 64 (ch.addr + 16)
  sp96 : 96 ≤ sp.toNat
  sp64 : sp.toNat + 8 < 2 ^ 64
  w : m.memory.Permitted .write (sp.toNat - 96) 96
  r : m.memory.Permitted .read (sp.toNat - 96) 96
  ret : m.memory.readBytes sp.toNat 8 = some (encodeWords [ret])
  /-- The stack window `[sp - 96, sp + 8)` misses both codes. -/
  codeF : ∀ i < 272, ¬ (sp.toNat - 96 ≤ (freeAt base).toNat + i ∧ (freeAt base).toNat + i < sp.toNat + 8)
  codeI : ∀ i < 897,
    ¬ (sp.toNat - 96 ≤ (intFreeAt base).toNat + i ∧ (intFreeAt base).toNat + i < sp.toNat + 8)
  /-- The GOT slots of `errno`'s and `tcache`'s TLS offsets (the image's relocations). -/
  gotE : ∃ o, loadN m.memory (freeAt base + 0x155fc8#64) 8 = some o ∧
    m.core.fsBase + o = BitVec.ofNat 64 (pin239.repAt base tp off).tls.errno ∧
    Apart (freeAt base + 0x155fc8#64).toNat 8 (sp.toNat - 96) (sp.toNat + 8)
  gotT : ∃ o, loadN m.memory (freeAt base + 0x155f68#64) 8 = some o ∧
    m.core.fsBase + o = BitVec.ofNat 64 (pin239.repAt base tp off).tls.tcache ∧
    Apart (freeAt base + 0x155f68#64).toNat 8 (sp.toNat - 96) (sp.toNat + 8)
  /-- `errno` is mapped and writable (some value), apart from the stack window, the block's
  cells and `__libc_free`'s code. -/
  errno : ∃ ev, (⟨(pin239.repAt base tp off).tls.errno, 4, ev⟩ : Cell).Holds (memView m.memory)
  errnoApart : ∀ k < 4,
    ¬ (sp.toNat - 96 ≤ (pin239.repAt base tp off).tls.errno + k ∧
        (pin239.repAt base tp off).tls.errno + k < sp.toNat + 8) ∧
      (pin239.repAt base tp off).tls.errno + k ∉ (freeCells pin239.layout x ch).bytes ∧
      ¬ ((freeAt base).toNat ≤ (pin239.repAt base tp off).tls.errno + k ∧
        (pin239.repAt base tp off).tls.errno + k < (freeAt base).toNat + 272)
  /-- The stack window holds no byte the representation reads. -/
  stack : ∀ a, sp.toNat - 96 ≤ a → a < sp.toNat + 8 → ¬ RepTouches pin239.config (pin239.repAt base tp off) x a
  /-- The abstract tcache path: a lent-out chunk of the arena, a tcache, a bin with room that does
  not hold the chunk (no double free). -/
  chunk : ch ∈ x.1.av.chunks
  client : ch.use = .client
  tcb : ∃ tc, x.1.thread.tcache = some tc ∧ pin239.config.tidx ch.size < pin239.config.tcacheBins ∧
    (ch.addr, ch.size) ∉ tc.bins (pin239.config.tidx ch.size) ∧
    (tc.bins (pin239.config.tidx ch.size)).length < pin239.config.tcacheCount
  /-- The chunk's first payload words hold no cell (x86sim finding 3). -/
  fresh : PayloadFresh pin239.config pin239.layout (pin239.repAt base tp off).statics
    (pin239.repAt base tp off).tls x.1 ch.addr
  /-- `tcache_put`'s cells miss the surroundings, both codes and the stack window. -/
  cells : FpApart (freeCells pin239.layout x ch)
    (envFrag pin239.config pin239.layout (pin239.repAt base tp off).env x.2.1) (intFreeAt base)
    intFreeCode.length
  cellsF : ∀ a ∈ (freeCells pin239.layout x ch).bytes,
    ¬ ((freeAt base).toNat ≤ a ∧ a < (freeAt base).toNat + 272)
  cellsStack : ∀ a ∈ (freeCells pin239.layout x ch).bytes, ¬ (sp.toNat - 96 ≤ a ∧ a < sp.toNat + 8)

theorem pin239_consts : pin239.config.align = 16 ∧ pin239.config.minSize = 32 ∧
    pin239.config.hdr = 16 ∧ pin239.config.tcacheBins = 64 ∧ pin239.config.tcacheCount = 7 ∧
    pin239.config.tcacheCountWidth = 2 ∧ pin239.layout.tcCounts = 0 ∧
    pin239.layout.tcEntries = 0x80 := by decide

/-- `ofNat (base + a) + ofNat b`, for a literal sum. -/
theorem ofNat_lit {base a b c : Nat} (h : a + b = c) :
    BitVec.ofNat 64 (base + a) + BitVec.ofNat 64 b = BitVec.ofNat 64 (base + c) := by
  rw [BitVec.ofNat_add_ofNat, Nat.add_assoc, h]

/-- A cell survives a run that keeps its bytes. -/
theorem cell_frame {v v' : MemView} {c : Cell} (h : c.Holds v)
    (hag : ∀ k < c.width, v.byte (c.addr + k) = v'.byte (c.addr + k) ∧
      v.writable (c.addr + k) = v'.writable (c.addr + k)) : c.Holds v' := by
  have := Frag.holds_frame (f := [c]) (v := v) (v' := v') (fun d hd => by
    simp only [List.mem_singleton] at hd; subst hd; exact h) (fun a ha => by
    simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_range',
      Nat.one_mul] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    exact hag k hk)
  exact this c (List.mem_singleton_self _)

/-- A member of a list of address ranges, each apart from a window. -/
theorem apart_pair {lo hi a k X n : Nat} (h : Apart X n lo hi) (e : (a, k) = (X, n)) : Apart a k lo hi := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e; exact h

set_option maxHeartbeats 16000000 in
/-- **`free (ch.addr + 16)` into the tcache** (glibc 2.39, `Str9Fs`). -/
theorem freeTcachePut239 (hA : Task.algo.leafTcachePut) (base tp off : Nat) (x : AState)
    (ch : Chunk) (sp ret : Word) (regs : Reg → Word) :
    fsMach.Triple
      (fun m => LocalAt pin239.config (pin239.repAt base tp off) fsMach x m ∧
        FreeEntry base tp off x ch sp ret regs m)
      (fun m' => ∃ l', x.1.tcachePut (ch.addr, ch.size) (pin239.config.tidx ch.size) = some l' ∧
        Algo.intFree pin239.config x.1 ch.addr = .ok l' ∧
        LocalAt pin239.config (pin239.repAt base tp off) fsMach (l', x.2.1, []) m' ∧
        m'.core.rip = ret ∧ m'.core.read .rsp = sp + 8#64 ∧
        ∀ r ∈ sysv64.calleeSaved, m'.core.read r = regs r)
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) := by
  intro m0 ⟨hLA, he⟩
  obtain ⟨hA16, hM32, hH16, hB64, hC7, hW2, hTC0, hTE⟩ := pin239_consts
  obtain ⟨tc, htc, hi, hnot, hroom⟩ := he.tcb
  obtain ⟨oE, hgE, hoE, hgEA⟩ := he.gotE
  obtain ⟨oT, hgT, hoT, hgTA⟩ := he.gotT
  obtain ⟨evN, hEv⟩ := he.errno
  have hwf := hLA.1
  have htw := hwf.arena.tiles
  have hsz := htw.sizes ch he.chunk
  have hal := htw.aligned ch he.chunk
  have hbd := htw.bound ch he.chunk
  have hnn := htw.nonNull ch he.chunk
  have htwf := hwf.tcache tc htc
  rw [hA16] at hsz hal
  rw [hM32] at hsz
  generalize hcdef : ch.addr = c at hal hbd hnn
  generalize hsdef : ch.size = s at hsz hbd
  generalize hidef : pin239.config.tidx s = i
  have hi' : i < 64 := by rw [← hidef, ← hsdef, ← hB64]; exact hi
  have hroom' : (tc.bins i).length < 7 := by rw [← hidef, ← hsdef, ← hC7]; exact hroom
  have hlen16 : (tc.bins i).length < 2 ^ 16 := by omega
  -- the representation
  obtain ⟨hwf0, ⟨hfa, hft, hfs, hback, hnd⟩, henv, hsurr, hra⟩ := hLA
  -- a tcache exists, so `ptmalloc_init` has run (`LocalWF.init`) and the arena is `arenaFrag`
  have hinit : x.1.shared.init = true := by
    cases hb : x.1.shared.init
    · obtain ⟨tc0, htc0, -⟩ := he.tcb
      have := (hwf0.init hb).2.2
      rw [htc0] at this; cases this
    · rfl
  have hst : ∀ b, sp.toNat - 96 ≤ b → b < sp.toNat → ¬ RepTouches pin239.config (pin239.repAt base tp off) x b :=
    fun b h1 h2 => he.stack b h1 (by omega)
  -- the chunk's size word
  obtain ⟨f, hf, hmH⟩ := mem_arenaRep_hdr (C := pin239.config) (L := pin239.layout)
    (avAddr := x.1.avAddr) hinit he.chunk
  rw [hcdef, hsdef] at hmH
  obtain ⟨kSz, bSz, -, -, vSz⟩ := cell_load (hfa _ hmH) (by simp)
  simp only [addressLimit] at bSz
  have hvSz : s + f < 2 ^ 64 := by simpa using vSz
  obtain ⟨hb2, hb4, hb8, hcs⟩ := sz_bits hsz.1 hf hvSz
  have hft' : ftidx (BitVec.ofNat 64 s) = BitVec.ofNat 64 i := by
    rw [← hidef]; exact ftidx_ofNat hsz.2 (by omega)
  -- the payload words (`e->key` the client may have written)
  have hbk := hback _ (mem_spans he.chunk)
  rw [hcdef, hsdef] at hbk
  obtain ⟨ekN, hEk⟩ := exists_cell_of_backed (v := memView m0.memory) 8 (c + 24) fun j hj => by
    rw [show c + 24 + j = c + (24 + j) by omega]; exact hbk (24 + j) (by omega)
  obtain ⟨kEk, -, -, -, -⟩ := cell_load hEk (by simp)
  -- the thread's cells
  have hT : (tcacheFrag pin239.config pin239.layout x.1.shared.key tc).Holds (memView m0.memory) :=
    Frag.holds_sub hft (tcacheFrag_sub htc)
  have mCnt := mem_tcacheFrag_count (L := pin239.layout) (key := x.1.shared.key) (tc := tc) hi
  have mEnt := mem_tcacheFrag_entry (L := pin239.layout) (key := x.1.shared.key) (tc := tc) hi
  rw [hsdef, hidef] at mCnt mEnt
  obtain ⟨kCnt, bCnt, -, -, vCnt⟩ := cell_load (hT _ mCnt) (by simp [hW2])
  obtain ⟨kEnt, bEnt, -, -, vEnt⟩ := cell_load (hT _ mEnt) (by simp [Cell.w])
  simp only [Cell.w, hW2, hTC0, hTE, Nat.add_zero, addressLimit] at kCnt bCnt vCnt kEnt bEnt vEnt
  have mTc : Cell.w (pin239.repAt base tp off).tls.tcache tc.addr ∈ threadFrag pin239.config pin239.layout (pin239.repAt base tp off).tls x.1.avAddr
      x.1.shared.key x.1.shared.init x.1.thread := by simp [threadFrag, htc]
  obtain ⟨kTc, bTc, -, -, vTc⟩ := cell_load (hft _ mTc) (by simp [Cell.w])
  simp only [Cell.w, addressLimit] at kTc bTc vTc
  have htc0 : BitVec.ofNat 64 tc.addr ≠ 0 := fun h0 =>
    ofNat_ne (b := 0) (by simpa using vTc) (by decide) htwf.struct h0
  -- the shared and the surroundings' cells
  obtain ⟨kKey, bKey, -, -, -⟩ := cell_load (hfs _ mem_sharedFrag_key) (by simp [Cell.w])
  have mBins : Cell.w ((pin239.repAt base tp off).env.mp + pin239.layout.mpTcacheBins) pin239.config.tcacheBins ∈
      envFrag pin239.config pin239.layout (pin239.repAt base tp off).env x.2.1 := by simp [envFrag, mpConstFrag]
  have mCmax : Cell.w ((pin239.repAt base tp off).env.mp + pin239.layout.mpTcacheCount) pin239.config.tcacheCount ∈
      envFrag pin239.config pin239.layout (pin239.repAt base tp off).env x.2.1 := by simp [envFrag, mpConstFrag]
  obtain ⟨kBins, bBins, -, -, -⟩ := cell_load (henv _ mBins) (by simp [Cell.w])
  obtain ⟨kCmax, bCmax, -, -, -⟩ := cell_load (henv _ mCmax) (by simp [Cell.w])
  simp only [Cell.w, addressLimit] at kKey bKey kBins bBins kCmax bCmax
  -- errno
  obtain ⟨kEv, bEv, -, -, vEv⟩ := cell_load hEv (by simp)
  simp only [addressLimit] at bEv
  -- the addresses
  have aBins : freeAt base + 0x1563b8#64 = BitVec.ofNat 64 ((pin239.repAt base tp off).env.mp + pin239.layout.mpTcacheBins) := by
    show BitVec.ofNat 64 (base + 0xade30) + BitVec.ofNat 64 0x1563b8 = BitVec.ofNat 64 (base + 0x204180 + 0x68)
    rw [ofNat_lit (c := 0x2041e8) rfl, Nat.add_assoc]
  have aCmax : freeAt base + 0x1563c8#64 = BitVec.ofNat 64 ((pin239.repAt base tp off).env.mp + pin239.layout.mpTcacheCount) := by
    show BitVec.ofNat 64 (base + 0xade30) + BitVec.ofNat 64 0x1563c8 = BitVec.ofNat 64 (base + 0x204180 + 0x78)
    rw [ofNat_lit (c := 0x2041f8) rfl, Nat.add_assoc]
  have aKey : freeAt base + 0x15d348#64 = BitVec.ofNat 64 (pin239.repAt base tp off).statics.tcacheKey := by
    show BitVec.ofNat 64 (base + 0xade30) + BitVec.ofNat 64 0x15d348 = BitVec.ofNat 64 (base + 0x20b178)
    rw [ofNat_lit (c := 0x20b178) rfl]
  have hp64 : c + 16 < 2 ^ 64 := by omega
  have aP8 : BitVec.ofNat 64 (c + 16) - 8#64 = BitVec.ofNat 64 (c + 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have aP16 : BitVec.ofNat 64 (c + 16) - 0x10#64 = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have aPk : BitVec.ofNat 64 (c + 16) + 8#64 = BitVec.ofNat 64 (c + 24) := by rw [w_key]
  have hp0 : BitVec.ofNat 64 (c + 16) ≠ 0 := fun h0 => ofNat_ne (b := 0) hp64 (by decide) (by omega) h0
  -- the bin's walk (either branch of the key test)
  have hpe : ∀ d ∈ tc.bins i, d.1 + pin239.config.hdr ≠ c + 16 := by
    intro d hd heq
    rw [hH16] at heq
    have hdc : d.1 = c := by omega
    have hds := htwf.size i d hd
    rw [hA16, hM32] at hds
    have hde : d.2 = s := by
      have h1 := hds.1; rw [← hidef] at h1
      have h1' : (d.2 - 32 + 16 - 1) / 16 = (s - 32 + 16 - 1) / 16 := h1
      omega
    exact hnot (by rw [← hidef] at hd; rw [hcdef, hsdef]; exact (show (c, s) = d by
      rw [← hdc, ← hde]) ▸ hd)
  have hwalk := tcWalk_of (key := x.1.shared.key) (m := m0.memory) tcShape239 htwf (by omega) hT hpe hp64
  rw [hH16, hC7] at hwalk
  -- apartness from the stack window
  have touchT : ∀ {d : Cell}, d ∈ tcacheFrag pin239.config pin239.layout x.1.shared.key tc →
      ∀ k < d.width, RepTouches pin239.config (pin239.repAt base tp off) x (d.addr + k) := fun hd k hk =>
    touch_rep (List.mem_append_left _ (List.mem_append_right _ (tcacheFrag_sub htc _ hd))) hk
  have apL : ∀ j < (((tc.bins i).map (·.1 + 16)).map (BitVec.ofNat 64)).length,
      Apart ((((tc.bins i).map (·.1 + 16)).map (BitVec.ofNat 64)).getD j 0).toNat 8
        (sp.toNat - 96) sp.toNat := by
    intro j hj
    simp only [List.length_map] at hj
    have hm := mem_tcacheFrag_linkAt (L := pin239.layout) (key := x.1.shared.key) (by omega : i < pin239.config.tcacheBins) hj
    simp only [Nat.add_zero, hH16] at hm
    obtain ⟨-, bL, -, -, -⟩ := cell_load (hT _ hm) (by simp)
    simp only [addressLimit] at bL
    rw [getD_map_ofNat, toNat_ofNat_lt (by omega)]
    exact apart_of_touch hst fun k hk => touchT hm k hk
  have apR : ∀ {d : Cell}, d ∈ arenaRep pin239.config (pin239.repAt base tp off).layout x.1.shared.init x.1.avAddr x.1.av ++
      threadFrag pin239.config (pin239.repAt base tp off).layout (pin239.repAt base tp off).tls x.1.avAddr x.1.shared.key x.1.shared.init x.1.thread ++
      sharedFrag pin239.config (pin239.repAt base tp off).layout (pin239.repAt base tp off).statics x.1.shared → Apart d.addr d.width (sp.toNat - 96) sp.toNat :=
    fun hd => apart_of_touch hst fun k hk => touch_rep hd hk
  have apV : ∀ {d : Cell}, d ∈ envFrag pin239.config (pin239.repAt base tp off).layout (pin239.repAt base tp off).env x.2.1 →
      Apart d.addr d.width (sp.toNat - 96) sp.toNat :=
    fun hd => apart_of_touch hst fun k hk => touch_env hd hk
  have apSz : Apart (c + 8) 8 (sp.toNat - 96) sp.toNat :=
    apR (List.mem_append_left _ (List.mem_append_left _ hmH))
  have apEk : Apart (c + 24) 8 (sp.toNat - 96) sp.toNat := apart_of_touch hst fun k hk => by
    have := touch_span (C := pin239.config) (P := pin239.repAt base tp off) (x := x) he.chunk (k := 24 + k) (by rw [hsdef]; omega)
    rwa [hcdef, show c + (24 + k) = c + 24 + k by omega] at this
  have apTc : Apart (pin239.repAt base tp off).tls.tcache 8 (sp.toNat - 96) sp.toNat :=
    apR (d := Cell.w (pin239.repAt base tp off).tls.tcache tc.addr) (List.mem_append_left _ (List.mem_append_right _ mTc))
  have apKey : Apart (pin239.repAt base tp off).statics.tcacheKey 8 (sp.toNat - 96) sp.toNat :=
    apR (d := Cell.w (pin239.repAt base tp off).statics.tcacheKey x.1.shared.key) (List.mem_append_right _ mem_sharedFrag_key)
  have apBins : Apart ((pin239.repAt base tp off).env.mp + pin239.layout.mpTcacheBins) 8 (sp.toNat - 96) sp.toNat := apV mBins
  have apCmax : Apart ((pin239.repAt base tp off).env.mp + pin239.layout.mpTcacheCount) 8 (sp.toNat - 96) sp.toNat := apV mCmax
  have apCnt : Apart (tc.addr + 0 + 2 * i) 2 (sp.toNat - 96) sp.toNat := by
    have h := apart_of_touch hst fun k hk => touchT mCnt k hk
    simpa [hW2, hTC0] using h
  have apEnt : Apart (tc.addr + 128 + 8 * i) 8 (sp.toNat - 96) sp.toNat := by
    have h := apart_of_touch hst fun k hk => touchT mEnt k hk
    simpa [Cell.w, hTE] using h
  have apErr : Apart (pin239.repAt base tp off).tls.errno 4 (sp.toNat - 96) sp.toNat :=
    fun k hk h => (he.errnoApart k hk).1 ⟨h.1, by have := h.2; omega⟩
  -- the words
  have eErr : (m0.core.fsBase + oE).toNat = (pin239.repAt base tp off).tls.errno := by rw [hoE, toNat_ofNat_lt (by omega)]
  have eTc : (m0.core.fsBase + oT).toNat = (pin239.repAt base tp off).tls.tcache := by rw [hoT, toNat_ofNat_lt (by omega)]
  have eCnt : BitVec.ofNat 64 tc.addr + (ftidx (csize (BitVec.ofNat 64 (s + f))) <<< 1) =
      BitVec.ofNat 64 (tc.addr + 0 + 2 * i) := by rw [hcs, hft', w_count]
  have eEnt : BitVec.ofNat 64 tc.addr + (ftidx (csize (BitVec.ofNat 64 (s + f))) <<< 3) + 0x80#64 =
      BitVec.ofNat 64 (tc.addr + 128 + 8 * i) := by rw [hcs, hft', w_entry']
  have tCnt : (BitVec.ofNat 64 (tc.addr + 0 + 2 * i)).toNat = tc.addr + 0 + 2 * i := toNat_ofNat_lt (by omega)
  have tEnt : (BitVec.ofNat 64 (tc.addr + 128 + 8 * i)).toNat = tc.addr + 128 + 8 * i := toNat_ofNat_lt (by omega)
  have tLit : ∀ {a : Nat}, a + 8 ≤ 2 ^ 64 → (BitVec.ofNat 64 a).toNat = a := fun h => toNat_ofNat_lt (by omega)
  have herr : loadN m0.memory (m0.core.fsBase + oE) 4 = some (BitVec.ofNat 64 evN) := by
    rw [hoE]; exact kEv
  have htcL : loadN m0.memory (m0.core.fsBase + oT) 8 = some (BitVec.ofNat 64 tc.addr) := by
    rw [hoT]; exact kTc
  have hszL : loadN m0.memory (BitVec.ofNat 64 (c + 16) - 8#64) 8 = some (BitVec.ofNat 64 (s + f)) := by
    rw [aP8]; exact kSz
  -- 1. from the entry to `tcache_put`
  obtain ⟨mF, rF, ripF, rspF, rsiF, r10F, r8F, raxF, rcxF, frF, fsF, wwF, s0, s1, s2, s3, s7, s8, s9,
      s10, s11⟩ :=
    free_front (m := m0) (A := freeAt base) (sp := sp) (p := BitVec.ofNat 64 (c + 16)) (offE := oE)
      (sz := BitVec.ofNat 64 (s + f)) (ev := BitVec.ofNat 64 evN) (offT := oT)
      (tc := BitVec.ofNat 64 tc.addr) (bins := BitVec.ofNat 64 pin239.config.tcacheBins)
      (cmax := BitVec.ofNat 64 7) (key := BitVec.ofNat 64 x.1.shared.key)
      (ekey := BitVec.ofNat 64 ekN) (cnt := BitVec.ofNat 64 (tc.bins i).length)
      (h := BitVec.ofNat 64 (((tc.bins i).map (·.1 + 16)).headD 0))
      he.loaded (by rw [intA_freeAt]; exact he.loadedI) he.rip ((he.regsEq _).trans he.rsp)
      ((he.regsEq _).trans (by rw [he.rdi, hcdef])) hp0 he.sp96 he.w he.r
      (fun j hj h => he.codeF j hj ⟨h.1, by unfold fstk at h; omega⟩)
      (fun j hj h => by
        rw [intA_freeAt] at h; unfold fstk at h; exact he.codeI j hj ⟨h.1, by omega⟩)
      hgE hszL herr hb2 hb4 hgT htcL htc0
      (by
        rw [aP16, hcs, toNat_ofNat_lt (by omega)]
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega)
      (by rw [aP16]; exact aligned_ofNat (by omega))
      (by rw [hcs, toNat_ofNat_lt (by omega)]; omega) hb8
      (by rw [aBins]; exact kBins)
      (by rw [hcs, hft', toNat_ofNat_lt (by omega), hB64, toNat_ofNat_lt (by decide)]; exact hi')
      (by rw [aCmax, ← hC7]; exact kCmax) (by rw [aKey]; exact kKey) (by rw [aPk]; exact kEk)
      (.inr ⟨_, hwalk, apL⟩) (by rw [eCnt]; exact kCnt)
      (by
        rw [toNat_ofNat_lt (by decide)]
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega)
      (by rw [eEnt]; exact kEnt) (by rw [eEnt, tEnt]; exact apEnt)
      (fun a k hm => by
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (apart_mono hgEA (Nat.le_refl _) (by omega)) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (by rw [aP8, tLit (by omega)]; exact apSz) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (by rw [eErr]; exact apErr) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (apart_mono hgTA (Nat.le_refl _) (by omega)) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (by rw [eTc]; exact apTc) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (by rw [aBins, tLit (by omega)]; exact apBins) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (by rw [aCmax, tLit (by omega)]; exact apCmax) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (by rw [aKey, tLit (by omega)]; exact apKey) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (by rw [aPk, tLit (by omega)]; exact apEk) e
        rcases List.mem_cons.1 hm with e | hm
        · exact apart_pair (by rw [eCnt, tCnt]; exact apCnt) e
        exact absurd hm List.not_mem_nil)
  have hfstk : ∀ a, fstk sp a → ¬ RepTouches pin239.config (pin239.repAt base tp off) x a := fun a h =>
    he.stack a h.1 (by unfold fstk at h; omega)
  have LF : LocalAt pin239.config (pin239.repAt base tp off) fsMach x mF :=
    localAt_ww ⟨hwf, ⟨hfa, hft, hfs, hback, hnd⟩, henv, hsurr, hra⟩ wwF hfstk
  have hlIF : Loaded mF.memory (intFreeAt base) intFreeCode :=
    loadedC_ww intFreeCode_length he.loadedI wwF (fun j hj h => he.codeI j hj ⟨h.1, by unfold fstk at h; omega⟩)
  have hlF : Loaded mF.memory (freeAt base) freeCode :=
    loadedC_ww freeCode_length he.loaded wwF (fun j hj h => he.codeF j hj ⟨h.1, by unfold fstk at h; omega⟩)
  -- 2. `tcache_put`
  have hargs : (freeArgs ch).getD 0 0 = c ∧ (freeArgs ch).getD 1 0 = s ∧ (freeArgs ch).getD 2 0 = i := by
    simp [freeArgs, hcdef, hsdef, hidef]
  obtain ⟨g0, g1, g2⟩ := hargs
  obtain ⟨mG, rG, ripG, frG, fsG, wwG, l', hput, LG, hlIG⟩ :=
    tcPutCore tcShape239 intFreeTcPut (intFreeAt base) (tcKey239 base tp off) hA repTcachePut
      (x.1, x.2.1, freeArgs ch) mF (localAt_args LF)
      ⟨hlIF, tc, by
        simp only [g0, g1, g2]
        refine ⟨htc, by rw [hB64]; exact hi', hidef, by rw [hA16]; exact hsz.1, by rw [hM32]; exact hsz.2,
          hnn, by rw [hA16]; exact hal, by rw [← hidef, ← hsdef, ← hcdef]; exact hnot,
          by rw [hC7]; exact hroom', ch, he.chunk, hcdef, hsdef⟩,
        by simp only [g0]; rw [rsiF, aP16],
        by simp only [g0]; rw [r10F, aP16],
        r8F, by simp only [g2]; rw [raxF, hcs, hft'],
        by simp only [g2]; rw [rcxF, count_ofNat hlen16],
        by simp only [g0]; rw [← hcdef]; exact he.fresh, he.cells⟩
      (by rw [ripF, intA_freeAt])
  have hputC : x.1.tcachePut (c, s) i = some l' := by
    simpa only [g0, g1, g2] using hput
  have hputCh : x.1.tcachePut (ch.addr, ch.size) (pin239.config.tidx ch.size) = some l' := by
    rw [hcdef, hsdef, hidef]; exact hputC
  -- 3. `_int_free`'s epilogue
  have rdG : ∀ {a : Nat} {bs : List Byte}, sp.toNat - 96 ≤ a → a + 8 ≤ sp.toNat + 8 →
      mF.memory.readBytes a 8 = some bs → mG.memory.readBytes a 8 = some bs :=
    fun h1 h2 h => rd_ww wwG (fun j hj hc => he.cellsStack _ hc ⟨by omega, by omega⟩) h
  have ripG' : mG.core.rip = intFreeAt base + BitVec.ofNat 64 301 := by
    rw [ripG, BitVec.add_assoc]; congr 1
  have rspG : mG.core.read .rsp = sp - 0x88#64 := by rw [frG _ (by decide) (by decide), rspF]
  obtain ⟨mH, rH, ripH, rspH, rbxH, r12H, r13H, rbpH, frH, fsH, memH⟩ :=
    int_ret (B := intFreeAt base) hlIG ripG' rspG he.sp96 (rdG (by omega) (by omega) s11)
      (rdG (by omega) (by omega) s10) (rdG (by omega) (by omega) s9) (rdG (by omega) (by omega) s8)
      (rdG (by omega) (by omega) s7)
  -- 4. `__libc_free`'s epilogue (`errno := errno`)
  have hlH : Loaded mH.memory (freeAt base) freeCode := by
    rw [memH]; exact loadedC_ww freeCode_length hlF wwG (fun j hj hc => he.cellsF _ hc ⟨by omega, by omega⟩)
  have hEvF : (⟨(pin239.repAt base tp off).tls.errno, 4, evN⟩ : Cell).Holds (memView mF.memory) :=
    cell_frame hEv fun k hk => within_of_ww wwF _ fun h => by
      unfold fstk at h; simp only at h
      exact (he.errnoApart k hk).1 ⟨h.1, by omega⟩
  have hEvH : (⟨(pin239.repAt base tp off).tls.errno, 4, evN⟩ : Cell).Holds (memView mH.memory) := by
    rw [memH]
    exact cell_frame hEvF fun k hk => within_of_ww wwG _ fun h => (he.errnoApart k hk).2.1 h
  obtain ⟨-, -, rEvH, wEvH, -⟩ := cell_load hEvH (by simp)
  have eErrH : mH.core.fsBase + mH.core.read .rbx = BitVec.ofNat 64 (pin239.repAt base tp off).tls.errno := by
    rw [fsH, fsG, fsF, rbxH, hoE]
  have hrsp0 : m0.core.read .rsp = sp := (he.regsEq _).trans he.rsp
  obtain ⟨mI, rI, ripI, rspI, rbxI, r12I, r13I, rbpI, frI, fsI, stI⟩ :=
    free_ret (A := freeAt base) (sp := sp) hlH ripH rspH he.sp96 he.sp64
      (by rw [eErrH, toNat_ofNat_lt (by omega)]; exact wEvH)
      (by rw [eErrH, toNat_ofNat_lt (by omega)]; exact fun k hk h => (he.errnoApart k hk).1 ⟨by omega, h.2⟩)
      (by rw [eErrH, toNat_ofNat_lt (by omega)]; exact fun k hk h => (he.errnoApart k hk).2.2 h)
      (by rw [memH]; exact rdG (by omega) (by omega) s3) (by rw [memH]; exact rdG (by omega) (by omega) s2)
      (by rw [memH]; exact rdG (by omega) (by omega) s1) (by rw [memH]; exact rdG (by omega) (by omega) s0)
      (by
        rw [memH]
        refine rd_ww wwG (fun j hj hc => he.cellsStack _ hc ⟨by omega, by omega⟩) ?_
        exact rd_ww wwF (fun j hj h => by unfold fstk at h; omega) he.ret)
  have hvI : memView mI.memory = memView mG.memory := by
    have hE64 : (pin239.repAt base tp off).tls.errno < 2 ^ 64 := by omega
    have hv32 : evN < 2 ^ 32 := by simpa using vEv
    have v := memView_storeN stI (by rw [eErrH, toNat_ofNat_lt hE64]; exact rEvH)
    rw [eErrH, toNat_ofNat_lt hE64, r12H, ext32_ofNat hv32,
      toNat_ofNat_lt (show evN < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show evN < 2 ^ (8 * 4) by simpa using hv32)] at v
    rw [v, store_id (memView_sane _) hEvH.1, memH]
  refine ⟨mI, rF.trans (rG.trans (rH.trans rI)), ⟨l', hputC, ?_, localAt_view LG hvI, ripI, rspI, ?_⟩,
    fun a ha => ?_⟩
  · have hf := Algo.find?_addr htw.nodup he.chunk
    have := Algo.intFree_tcache_eq hf he.client (by rw [hA16, hcdef]; exact hal) (by rw [hcdef, hsdef]; exact hbd)
      (by rw [hM32, hsdef]; exact hsz.2) (by rw [hA16, hsdef]; exact hsz.1) htc hi hnot hroom
    rw [← hcdef, this]
    simp [Algo.tcPut, hputCh]
  · intro r hr
    have h' : r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 := by
      simpa [Silmaril.X86.sysv64] using hr
    rcases h' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbxI, he.regsEq]
    · rw [rbpI, he.regsEq]
    · rw [r12I, he.regsEq]
    · rw [r13I, he.regsEq]
    all_goals
      rw [frI _ (by decide) (by decide) (by decide) (by decide) (by decide),
        frH _ (by decide) (by decide) (by decide) (by decide) (by decide),
        frG _ (by decide) (by decide),
        frF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.regsEq]
  · have h1 := within_of_ww wwF a fun h => ha (.inl h)
    have h2 := within_of_ww wwG a fun h => ha (.inr h)
    show (memView m0.memory).byte a = (memView mI.memory).byte a ∧
      (memView m0.memory).writable a = (memView mI.memory).writable a
    rw [hvI]
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- **`free (ch.addr + 16)` into the tcache, on `Str9K`** (the process machine; the path makes no
system call). -/
theorem freeTcachePut239K (hA : Task.algo.leafTcachePut) (base tp off : Nat) (x : AState)
    (ch : Chunk) (sp ret : Word) (regs : Reg → Word) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        FreeEntry base tp off x ch sp ret regs (projK s))
      (fun s' => ∃ l', x.1.tcachePut (ch.addr, ch.size) (pin239.config.tidx ch.size) = some l' ∧
        Algo.intFree pin239.config x.1 ch.addr = .ok l' ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧
        (projK s').core.rip = ret ∧ (projK s').core.read .rsp = sp + 8#64 ∧
        ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r)
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) :=
  Triple.liftK (freeTcachePut239 hA base tp off x ch sp ret regs)

/-- `freeTcachePut239K` with the algorithm's leaf lemma (`Algo.leafTcachePut`): unconditional. -/
theorem freeTcachePut239K' (base tp off : Nat) (x : AState) (ch : Chunk) (sp ret : Word)
    (regs : Reg → Word) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        FreeEntry base tp off x ch sp ret regs (projK s))
      (fun s' => ∃ l', x.1.tcachePut (ch.addr, ch.size) (pin239.config.tidx ch.size) = some l' ∧
        Algo.intFree pin239.config x.1 ch.addr = .ok l' ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧
        (projK s').core.rip = ret ∧ (projK s').core.read .rsp = sp + 8#64 ∧
        ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r)
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) :=
  freeTcachePut239K Algo.leafTcachePut base tp off x ch sp ret regs

end Silmaril.Libc.Ptmalloc.X86sim.V239
