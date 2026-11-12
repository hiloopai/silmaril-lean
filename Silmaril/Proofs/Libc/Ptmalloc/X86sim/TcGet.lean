module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.Mem
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcGetRun
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.RepTcGet

/-!
# ptmalloc x86sim: the `tcache_get` block simulates `Local.tcacheGet`

For **any** code carrying gcc's `tcache_get` sequence (`TcGetSeqR code o ri l0 l34`, any index
register `ri`), loaded at any `A`,
and any configuration/layout with the x86-64 tcache shape (`TcShape`: 2-byte counts at offset 0,
entries at `0x80`, safe-linking), the block from `o` to `o + tcGetLen l0 l34` simulates the leaf operation
`Local.tcacheGet` through `LocalAt` (`tcGetSim`):

* the **pre** names only registers (`rdx` = the tcache, `ri` = the bin, `rcx` = its count, as
  the preceding test left them), the loaded code, and two address facts about the block's own
  footprint (apart from the surroundings' cells and from the code);
* the **footprint** is the three cells `tcache_get` writes (`tcGetCells`): `entries[i]`,
  `counts[i]`, the popped entry's `key`; everything else, every other arena, thread and the
  surroundings, is framed;
* the **post** gives `rax` = the payload.

The representation change is the layer-(c) leaf lemma `Task.x86sim.repTcacheGet` (old fragment +
the three stores = new fragment) and the well-formedness is the layer-(b) leaf lemma
`Task.algo.leafTcacheGet`; `tcGetSim` takes both as hypotheses, so it is proved once, here, for
every block that is a copy of this sequence.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Data
open Silmaril.Data.SepList (SLinks slist)
namespace Silmaril.Libc.Ptmalloc.X86sim

/-! ## The block -/

/-- **The three cells `tcache_get (i)` writes** in the state `x` (`i = x.2.2.headD 0`), with their
new values, in the machine's store order: `entries[i] := REVEAL_PTR (e->next)`,
`counts[i] -= 1`, `e->key := 0`. -/
def tcGetCells (C : Config) (L : Layout) (x : AState) : Frag :=
  match x.1.thread.tcache with
  | none => []
  | some tc =>
    let i := x.2.2.headD 0
    [Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).getD 1 0),
     ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length - 1⟩,
     Cell.w (((tc.bins i).headD (0, 0)).1 + C.hdr + 8) 0]

/-- A block footprint `f` is apart from the surroundings' cells `g` and from the code
`[A, A + n)`. -/
def FpApart (f g : Frag) (A : Word) (n : Nat) : Prop :=
  ∀ a ∈ f.bytes, a ∉ g.bytes ∧ ¬ (A.toNat ≤ a ∧ a < A.toNat + n)

/-- **The pre of the `tcache_get` block**: the code is loaded; the registers hold the tcache, the
bin (in `ri`) and its count; the bin is in range and non-empty (the test before the block); the
footprint is apart from the surroundings and the code. -/
def tcGetPreR (ri : Reg) (C : Config) (P : RepAt) (code : List Byte) (A : Word) (x : AState)
    (s : MState) : Prop :=
  Loaded s.memory A code ∧
  ∃ tc, x.1.thread.tcache = some tc ∧ x.2.2.headD 0 < C.tcacheBins ∧ tc.bins (x.2.2.headD 0) ≠ [] ∧
    s.core.read .rdx = BitVec.ofNat 64 tc.addr ∧ s.core.read ri = BitVec.ofNat 64 (x.2.2.headD 0) ∧
    s.core.read .rcx = BitVec.ofNat 64 (tc.bins (x.2.2.headD 0)).length ∧
    FpApart (tcGetCells C P.layout x) (envFrag C P.layout P.env x.2.1) A code.length

/-- `tcGetPreR` with the bin in `r12` (gcc 13/14). -/
abbrev tcGetPre (C : Config) (P : RepAt) (code : List Byte) (A : Word) (x : AState) (s : MState) :
    Prop := tcGetPreR .r12 C P code A x s

/-- **The `tcache_get` block** of `code` at `A + o` (the bin in `ri`; the sequence's two
`ri`-addressed instructions `l0` and `l34` bytes long; defaults: gcc 13/14's `r12`). -/
def tcGetBlock (C : Config) (P : RepAt) (code : List Byte) (A : Word) (o : Nat)
    (ri : Reg := .r12) (l0 : Nat := 5) (l34 : Nat := 5) : Block fsMach AState where
  entry := (A + BitVec.ofNat 64 o).toNat
  exits := [(A + BitVec.ofNat 64 (o + tcGetLen l0 l34)).toNat]
  pre := tcGetPreR ri C P code A
  post x s := Loaded s.memory A code ∧ s.core.read .rax = BitVec.ofNat 64 (x.2.2.headD 0)
  fp x a := a ∈ (tcGetCells C P.layout x).bytes

/-- **The x86-64 tcache shape** the sequence hard-codes: 2-byte counts at offset 0, entries at
`0x80`, safe-linking on, `SIZE_SZ = 8`, 16-byte alignment. -/
structure TcShape (C : Config) (L : Layout) : Prop where
  ok : C.Ok
  counts : L.tcCounts = 0
  entries : L.tcEntries = 0x80
  width : C.tcacheCountWidth = 2
  safe : C.safeLinking = true

/-! ## The layer-(c) leaf lemma it needs -/

/-- **`Task.x86sim.repTcacheGet`**: `tcache_get`'s three stores (in the machine's order) turn the
representation of `l` into that of `l'`. The instance of `Task.seplist.leafTcacheGet` +
`Task.seplist.localFrame` the block needs, stated with the hypotheses the block has
(`LocalWF`, `LocalRep` including its `Nodup`, a view of machine bytes). Proved:
`repTcacheGet`. -/
def Task.x86sim.repTcacheGet : Prop :=
  ∀ (C : Config) (L : Layout) (St : Statics) (T : TlsAddrs) (l l' : Local) (tc : TcacheSt)
    (i p : Nat) (v : MemView),
    C.Ok → LocalWF C l → LocalRep C L St T l v → SaneView v → l.thread.tcache = some tc →
    i < C.tcacheBins → l.tcacheGet C i = some (p, l') →
    LocalRep C L St T l' (v.storeAll
      [Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).getD 1 0),
       ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length - 1⟩,
       Cell.w (p + 8) 0])

/-- `memView` is a view of machine bytes. -/
theorem memView_sane (m : Silmaril.Process.Memory) : SaneView (memView m) := fun a b h => by
  obtain ⟨h1, -, x, -, rfl⟩ := byte_memView_some h
  exact ⟨x.isLt, by simpa [addressLimit] using h1⟩

/-- **`Task.x86sim.repTcacheGet` holds** (layer c; `repTcacheGet_of`). -/
theorem repTcacheGet : Task.x86sim.repTcacheGet :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hrep hs htc hi hget => repTcacheGet_of hrep hs htc hi hget

/-! ## Arithmetic -/

theorem w_entry {a i : Nat} :
    BitVec.ofNat 64 a + ((BitVec.ofNat 64 i + 16#64) <<< 3) = BitVec.ofNat 64 (a + 0x80 + 8 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem w_count {a i : Nat} :
    BitVec.ofNat 64 a + (BitVec.ofNat 64 i <<< 1) = BitVec.ofNat 64 (a + 0 + 2 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem w_key {p : Nat} : BitVec.ofNat 64 p + 8#64 = BitVec.ofNat 64 (p + 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_ofNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem aligned_ofNat {p : Nat} (h : p % 16 = 0) : (BitVec.ofNat 64 p).setWidth 8 &&& 0xf#8 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (15 : Nat) % 2 ^ 8 = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [show (0 : BitVec 8).toNat = 0 from rfl]
  omega

theorem reveal_ofNat {p n : Nat} (hp : p < 2 ^ 64) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 p >>> 12) ^^^ BitVec.ofNat 64 (p / 4096 ^^^ n)).toNat % 2 ^ (8 * 8) = n := by
  have h1 : p / 4096 < 2 ^ 64 := by omega
  have h2 : p / 4096 ^^^ n < 2 ^ 64 := Nat.xor_lt_two_pow h1 hn
  simp only [BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt h2, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 12 = 4096 by rfl, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  exact Nat.mod_eq_of_lt hn

theorem count_dec {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 16) :
    (((BitVec.ofNat 64 n).setWidth 32 - 1#32).setWidth 64).toNat % 2 ^ (8 * 2) = n - 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ## Reading the representation -/

section
variable {C : Config} {L : Layout} {key : Nat} {tc : TcacheSt} {i : Nat}

theorem mem_tcacheFrag_count (hi : i < C.tcacheBins) :
    (⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length⟩ : Cell) ∈
      tcacheFrag C L key tc := by
  unfold tcacheFrag
  exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_cons_self⟩

theorem mem_tcacheFrag_entry (hi : i < C.tcacheBins) :
    Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).headD 0) ∈
      tcacheFrag C L key tc := by
  unfold tcacheFrag
  exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem mem_tcacheFrag_link {c : Nat × Nat} {rest : List (Nat × Nat)} (hi : i < C.tcacheBins)
    (hb : tc.bins i = c :: rest) :
    (⟨c.1 + C.hdr + 0, 8, C.protect (c.1 + C.hdr + 0) ((rest.map (·.1 + C.hdr)).headD 0)⟩ : Cell) ∈
      tcacheFrag C L key tc := by
  unfold tcacheFrag
  refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))⟩
  rw [hb]
  simp only [slist, tcLinks, List.map_cons]
  exact List.mem_cons_self

theorem mem_tcacheFrag_key {c : Nat × Nat} {rest : List (Nat × Nat)} (hi : i < C.tcacheBins)
    (hb : tc.bins i = c :: rest) : Cell.w (c.1 + C.hdr + 8) key ∈ tcacheFrag C L key tc := by
  unfold tcacheFrag
  refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))⟩
  rw [hb]
  simp

end

/-- The thread's fragment contains its tcache's. -/
theorem tcacheFrag_sub {C : Config} {L : Layout} {T : TlsAddrs} {av key : Nat} {init : Bool}
    {t : ThreadSt} {tc : TcacheSt} (h : t.tcache = some tc) :
    ∀ c ∈ tcacheFrag C L key tc, c ∈ threadFrag C L T av key init t := by
  intro c hc
  simp only [threadFrag, h, Option.map_some, Option.getD_some]
  exact List.mem_append_right _ hc

theorem getD_one_cons {a : Nat} {l : List Nat} : (a :: l).getD 1 0 = l.headD 0 := by
  cases l <;> rfl

theorem mem_bytes {f : Frag} {c : Cell} (hc : c ∈ f) {k : Nat} (hk : k < c.width) :
    c.addr + k ∈ f.bytes :=
  List.mem_flatMap.2 ⟨c, hc, List.mem_range'.2 ⟨k, hk, by omega⟩⟩

theorem FpApart.code {f g : Frag} {A : Word} {n : Nat} (h : FpApart f g A n) {c : Cell} (hc : c ∈ f) :
    Apart c.addr c.width A.toNat (A.toNat + n) := fun _ hk => (h _ (mem_bytes hc hk)).2

theorem span_sub {f : Frag} {c : Cell} (hc : c ∈ f) {a : Word} (ha : a.toNat = c.addr) :
    ∀ x, span a c.width x → x ∈ f.bytes := by
  intro x ⟨h1, h2⟩
  have := mem_bytes hc (k := x - c.addr) (by omega)
  rwa [show c.addr + (x - c.addr) = x by omega] at this

/-- **`RepApart` across a thread-only step** (any version, any block): if the step keeps the
arena and the shared part and every new thread byte is an old one or lies in a heap span, the
surroundings stay apart from the representation. -/
theorem repApart_thread {C : Config} {P : RepAt} {l l' : Local} {e : Surr} {args args' : List Nat}
    (h : RepApart C P (l, e, args)) (hA : l'.avAddr = l.avAddr) (hav : l'.av = l.av)
    (hsh : l'.shared = l.shared)
    (hsub : ∀ a ∈ (threadFrag C P.layout P.tls l'.avAddr l'.shared.key l'.shared.init l'.thread).bytes,
      a ∈ (threadFrag C P.layout P.tls l.avAddr l.shared.key l.shared.init l.thread).bytes ∨
        ∃ s ∈ spansOf l.av, s.1 ≤ a ∧ a < s.1 + s.2) :
    RepApart C P (l', e, args') := by
  intro a ha
  obtain ⟨h1, h2⟩ := h a ha
  refine ⟨fun hm => ?_, by rw [hav]; exact h2⟩
  simp only [repFrag, bytes_append, List.mem_append] at hm h1
  rcases hm with (hm | hm) | hm
  · rw [hsh, hA, hav] at hm; exact h1 (.inl (.inl hm))
  · rcases hsub a hm with h3 | ⟨s, hs, h3⟩
    · exact h1 (.inl (.inr h3))
    · exact h2 s hs h3
  · rw [hsh] at hm; exact h1 (.inr hm)

set_option maxHeartbeats 4000000 in
/-- **The `tcache_get` block, with its frame**: the simulation step of `tcGetSim`, plus what a
caller composing it needs: every register but `rax`, `rcx`, `rdi`, `rsi` and the FS base are
unchanged, and memory changes only on the block's cells. -/
theorem tcGetCore {C : Config} {P : RepAt} (hS : TcShape C P.layout) {code : List Byte} {o : Nat}
    {ri : Reg} {l0 l34 : Nat}
    (hs : TcGetSeqR code o ri l0 l34) (A : Word) (hA : Task.algo.leafTcacheGet)
    (hR : Task.x86sim.repTcacheGet) (x : AState) (m : MState) (hLA : LocalAt C P fsMach x m)
    (hpre : tcGetPreR ri C P code A x m) (hpc : m.core.rip.toNat = (A + BitVec.ofNat 64 o).toNat) :
    ∃ m', Reaches Silmaril.X86.Str9Fs.step m m' ∧
      m'.core.rip = A + BitVec.ofNat 64 (o + tcGetLen l0 l34) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (fun a => a ∈ (tcGetCells C P.layout x).bytes) ∧
      ∃ p l', x.1.tcacheGet C (x.2.2.headD 0) = some (p, l') ∧
        LocalAt C P fsMach (l', x.2.1, [p]) m' ∧ Loaded m'.memory A code ∧
        m'.core.read .rax = BitVec.ofNat 64 p := by
  obtain ⟨l, surr, args⟩ := x
  obtain ⟨hwf, hrep, henv, hsurr, hra⟩ := hLA
  obtain ⟨hl, tc, htc, hi, hne, hrdx, hr12, hrcx, hap⟩ := hpre
  simp only at hwf hrep henv hsurr htc hi hne hrdx hr12 hrcx hap
  have hcells0 : tcGetCells C P.layout (l, surr, args) =
      [Cell.w (tc.addr + P.layout.tcEntries + 8 * args.headD 0)
        (((tc.bins (args.headD 0)).map (·.1 + C.hdr)).getD 1 0),
       ⟨tc.addr + P.layout.tcCounts + C.tcacheCountWidth * args.headD 0, C.tcacheCountWidth,
        (tc.bins (args.headD 0)).length - 1⟩,
       Cell.w (((tc.bins (args.headD 0)).headD (0, 0)).1 + C.hdr + 8) 0] := by
    simp only [tcGetCells, htc]
  rw [hcells0] at hap
  generalize hidef : args.headD 0 = i at hi hne hr12 hrcx hap
  obtain ⟨c, rest, hb⟩ : ∃ c rest, tc.bins i = c :: rest := by
    cases h : tc.bins i with
    | nil => exact absurd h hne
    | cons c r => exact ⟨c, r, rfl⟩
  have hok := hS.ok
  have hhdr : C.hdr = 16 := by simp [Config.hdr, hok.sizeSz]
  have htwf := hwf.tcache tc htc
  have hcnn := htwf.nonNull i c (by rw [hb]; exact List.mem_cons_self)
  -- the abstract step
  let tc' : TcacheSt := { tc with bins := fun j => if j = i then rest else tc.bins j }
  let l' : Local := { l with thread := { l.thread with tcache := some tc' } }
  have hget : l.tcacheGet C i = some (c.1 + C.hdr, l') := by
    simp [Local.tcacheGet, htc, TcacheSt.get, hb, l', tc']
  -- the four cells read
  obtain ⟨hfa, hft, hfs, hback, hnd⟩ := hrep
  have hT : (tcacheFrag C P.layout l.shared.key tc).Holds (memView m.memory) :=
    Frag.holds_sub hft (tcacheFrag_sub htc)
  obtain ⟨lC, bC, rC, wC, vC⟩ := cell_load (hT _ (mem_tcacheFrag_count (key := l.shared.key) hi))
    (by simp [hS.width])
  obtain ⟨lE, bE, rE, wE, -⟩ := cell_load (hT _ (mem_tcacheFrag_entry (key := l.shared.key) hi))
    (by simp [Cell.w])
  obtain ⟨lL, bL, -, -, vL⟩ := cell_load (hT _ (mem_tcacheFrag_link (key := l.shared.key) hi hb))
    (by simp)
  obtain ⟨-, bK, rK, wK, -⟩ := cell_load (hT _ (mem_tcacheFrag_key (key := l.shared.key) hi hb))
    (by simp [Cell.w])
  simp only [Cell.w, hb, List.length_cons, List.map_cons, List.headD_cons, hS.width, hS.counts,
    hS.entries, Nat.add_zero] at lC bC rC wC vC lE bE rE wE lL bL vL bK rK wK
  have hc16 : c.1 % 16 = 0 := by rw [← hok.align]; exact hcnn.2
  have hp16 : (c.1 + C.hdr) % 16 = 0 := by rw [hhdr]; omega
  have hprot : C.protect (c.1 + C.hdr) ((rest.map (·.1 + C.hdr)).headD 0) =
      (c.1 + C.hdr) / 4096 ^^^ (rest.map (·.1 + C.hdr)).headD 0 := by simp [Config.protect, hS.safe]
  rw [hprot] at lL vL
  generalize hp : c.1 + C.hdr = p at hget hp16 lL vL bL bK rK wK lE
  generalize hnxt : (rest.map (·.1 + C.hdr)).headD 0 = nxt at lL vL
  have hnxtlt : nxt < 2 ^ 64 := by
    have h1 : p / 4096 < 2 ^ 64 := by simp [addressLimit] at bL; omega
    have := Nat.xor_lt_two_pow h1 vL
    rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
  -- the footprint, concretely
  have hcells : [Cell.w (tc.addr + P.layout.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).getD 1 0),
       ⟨tc.addr + P.layout.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length - 1⟩,
       Cell.w (((tc.bins i).headD (0, 0)).1 + C.hdr + 8) 0] =
      [Cell.w (tc.addr + 128 + 8 * i) nxt, (⟨tc.addr + 2 * i, 2, rest.length⟩ : Cell),
       Cell.w (p + 8) 0] := by
    rw [← hnxt, ← hp, hb, hS.width, hS.counts, hS.entries]
    simp only [List.map_cons, getD_one_cons, List.length_cons, List.headD_cons, Nat.add_sub_cancel,
      Nat.add_zero]
  rw [hcells] at hap
  have m1 : Cell.w (tc.addr + 128 + 8 * i) nxt ∈ [Cell.w (tc.addr + 128 + 8 * i) nxt,
      (⟨tc.addr + 2 * i, 2, rest.length⟩ : Cell), Cell.w (p + 8) 0] := by simp
  have m2 : (⟨tc.addr + 2 * i, 2, rest.length⟩ : Cell) ∈ [Cell.w (tc.addr + 128 + 8 * i) nxt,
      (⟨tc.addr + 2 * i, 2, rest.length⟩ : Cell), Cell.w (p + 8) 0] := by simp
  have m3 : Cell.w (p + 8) 0 ∈ [Cell.w (tc.addr + 128 + 8 * i) nxt,
      (⟨tc.addr + 2 * i, 2, rest.length⟩ : Cell), Cell.w (p + 8) 0] := by simp
  -- addresses as words
  have aE : (BitVec.ofNat 64 tc.addr + ((BitVec.ofNat 64 i + 16#64) <<< 3)).toNat =
      tc.addr + 128 + 8 * i := by
    rw [w_entry, toNat_ofNat_lt (by simp [addressLimit] at bE; omega)]
  have aC : (BitVec.ofNat 64 tc.addr + (BitVec.ofNat 64 i <<< 1)).toNat = tc.addr + 2 * i := by
    rw [w_count, toNat_ofNat_lt (by simp [addressLimit] at bC; omega)]; rfl
  have aK : (BitVec.ofNat 64 p + 8#64).toNat = p + 8 := by
    rw [w_key, toNat_ofNat_lt (by simp [addressLimit] at bK; omega)]
  -- the run
  obtain ⟨m', hrun, hrip', hrax', hfr', hfs', hl', mm1, mm2, h1, h2, h3⟩ :=
    tcGetRun (A := A) (tc := BitVec.ofNat 64 tc.addr) (idx := BitVec.ofNat 64 i)
      (cnt := BitVec.ofNat 64 (rest.length + 1)) (e := BitVec.ofNat 64 p)
      (v := BitVec.ofNat 64 (p / 4096 ^^^ nxt)) hs hl
      (BitVec.eq_of_toNat_eq hpc) hrdx hr12 (by rw [hrcx, hb]; rfl)
      (by rw [w_entry]; exact lE) (aligned_ofNat hp16) (by simpa using lL)
      (by rw [aE]; exact wE) (by rw [aC]; exact wC) (by rw [aK]; exact wK)
      (by rw [aE]; exact hap.code m1) (by rw [aC]; exact hap.code m2) (by rw [aK]; exact hap.code m3)
  -- the views
  have v1 := memView_storeN h1 (by rw [aE]; exact rE)
  have v2 := memView_storeN h2 (by rw [aC]; exact perm_store h1 rC)
  have v3 := memView_storeN h3 (by rw [aK]; exact perm_store h2 (perm_store h1 rK))
  rw [aE, reveal_ofNat (by simp [addressLimit] at bL; omega) hnxtlt] at v1
  rw [aC, count_dec (by omega) (by simpa using vC)] at v2
  rw [aK] at v3
  have hview : memView m'.memory = (memView m.memory).storeAll
      [Cell.w (tc.addr + 128 + 8 * i) nxt, ⟨tc.addr + 2 * i, 2, rest.length⟩, Cell.w (p + 8) 0] := by
    rw [v3, v2, v1]; rfl
  -- the footprint of the run
  have hww : m.memory.WritesWithin m'.memory (fun a => a ∈ Frag.bytes
      [Cell.w (tc.addr + 128 + 8 * i) nxt, ⟨tc.addr + 2 * i, 2, rest.length⟩, Cell.w (p + 8) 0]) :=
    ((ww_store h1).mono (span_sub m1 aE)).trans
      (((ww_store h2).mono (span_sub m2 aC)).trans ((ww_store h3).mono (span_sub m3 aK)))
  have hww' : m.memory.WritesWithin m'.memory
      (fun a => a ∈ (tcGetCells C P.layout (l, surr, args)).bytes) := by
    rw [hcells0, hidef, hcells]; exact hww
  refine ⟨m', hrun, hrip', hfr', hfs', hww', p, l', ?_,
    ⟨(hA C l l' i p hok hwf hget).1, ?_, ?_, hsurr, ?_⟩, hl', by simpa using hrax'⟩
  · exact hget
  · have := hR C P.layout P.statics P.tls l l' tc i p (memView m.memory) hok hwf
      ⟨hfa, hft, hfs, hback, hnd⟩ (memView_sane m.memory) htc hi hget
    have hl2 : ([Cell.w (tc.addr + P.layout.tcEntries + 8 * i) (((tc.bins i).map (·.1 + C.hdr)).getD 1 0),
        ⟨tc.addr + P.layout.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth,
          (tc.bins i).length - 1⟩, Cell.w (p + 8) 0] : Frag) =
        [Cell.w (tc.addr + 128 + 8 * i) nxt, ⟨tc.addr + 2 * i, 2, rest.length⟩, Cell.w (p + 8) 0] := by
      rw [← hnxt, hb, hS.width, hS.counts, hS.entries]
      simp only [List.map_cons, getD_one_cons, List.length_cons, Nat.add_sub_cancel, Nat.add_zero]
    rw [hl2] at this
    show LocalRep C P.layout P.statics P.tls l' (memView m'.memory)
    rw [hview]; exact this
  · refine Frag.holds_frame henv fun a ha => within_of_ww hww a ?_
    exact fun hb' => (hap a hb').1 ha
  · obtain ⟨e1, e2, e3, e4⟩ := tcGet_thread_bytes (L := P.layout) (T := P.tls) htc hi hget
    exact repApart_thread hra e1 e2 e3 fun a ha => .inl (e4 a ha)

/-- **`tcache_get` simulates `Local.tcacheGet`** (any code carrying the sequence, any load
address, any `Config`/`Layout` of the x86-64 tcache shape), given the layer-(b) and layer-(c)
leaf lemmas. -/
theorem tcGetSim {C : Config} {P : RepAt} (hS : TcShape C P.layout) {code : List Byte} {o : Nat}
    {ri : Reg} {l0 l34 : Nat}
    (hs : TcGetSeqR code o ri l0 l34) (A : Word) (hA : Task.algo.leafTcacheGet)
    (hR : Task.x86sim.repTcacheGet) :
    BlockSim (LocalAt C P fsMach)
      (fun x x' => ∃ p l', x.1.tcacheGet C (x.2.2.headD 0) = some (p, l') ∧ x' = (l', x.2.1, [p]))
      (tcGetBlock C P code A o ri l0 l34) := by
  intro x m ⟨hLA, hpre, hpc⟩
  obtain ⟨m', hrun, hrip', -, -, hww, p, l', hget, hLA', hl', hrax'⟩ :=
    tcGetCore hS hs A hA hR x m hLA hpre hpc
  exact ⟨m', hrun, ⟨by simp [tcGetBlock, fsMach, hrip'], (l', x.2.1, [p]), ⟨p, l', hget, rfl⟩, hLA',
    hl', by simpa using hrax'⟩, fun a ha => within_of_ww hww a ha⟩

end Silmaril.Libc.Ptmalloc.X86sim
