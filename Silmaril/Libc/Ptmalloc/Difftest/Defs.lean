module

public import Silmaril.Libc.Ptmalloc.Algo.Defs
public import Silmaril.Libc.Ptmalloc.Version.Defs
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# ptmalloc: differential test against the real libc

Untrusted test tooling (a pass is evidence, not proof). A harness (not part of this library)
runs a malloc/calloc/realloc/free trace on the host libc (the glibc 2.39 pin) and dumps, after each
operation, `main_arena`, `mp_`, the allocator statics, the thread's TLS words, the canary, the
heap segments and the `mmap`ed chunks' headers. This module

* parses the dump (`Snap`, format below);
* **reads back** the abstract state (`readLocal`: a `Local` and a `Surr`) by following the
  free structures forward only (tcache and fastbin `next` words through `Config.reveal`, bin
  `fd` words, chunk sizes from each segment's start);
* **check A**: evaluates the representation itself, `LocalRep`, `envFrag`, `SurrInv`, by
  `decide` on the dumped bytes (per fragment and per component, with the first failing cell),
  and every field of `LocalWF`/`ArenaWF`/component `*WF`, `SharedWF`, `TcacheWF`, `MainSbrk`,
  `MainBrk`, the `WorldWF` parked conditions, through Boolean mirrors (`chk*`; a mirror
  quantifies over the indices the read-back can populate, the rest are `[]` by construction);
* checks the model's **live set** (`Local.live`) against the harness's (pointer,
  `malloc_usable_size`) list, and `MallocLive`/the free contract between consecutive snapshots;
* **check B (partial)**: the tcache leaf operations (`Local.tcacheGet`, `Local.tcachePut`)
  predict malloc/free on glibc's tcache paths: the payload, the new tcache, the arena
  unchanged. The full replay through `ptmalloc pin239.config` waits for `algo`'s `Ops`.

Dump format (all words u64 little-endian): per snapshot, magic `0x50414e5354464444`, op index,
op kind (ASCII), slot, a, b, result, errno, load base, thread pointer, current break (raw
`brk(0)`), initial break, the four TLS `tpoff`s (tcache, thread_arena, tcache_shutting_down,
errno), the blocking page (0: none), the live count and (pointer, usable size) pairs, then
regions (kind, address, length, writable, bytes padded to 8; heap regions with bit 1 of the
writable word set are zero-run elided: a segment count, then (offset, length, bytes padded to 8)
segments, every other byte 0) up to kind `0xffff`. The file
ends with `0x444e4554464444`. Region kinds: 0 static, 1 the brk heap, 2 another anonymous
mapping (heap segment), 3 an `mmap`ed chunk's header, 4 a TLS word, 5 the canary.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Difftest

open Silmaril.Data

/-! ## The dump -/

/-- One dumped memory region. -/
structure Region where
  kind : Nat
  addr : Nat
  len : Nat
  writable : Bool
  bytes : ByteArray

/-- One snapshot: the op that preceded it, the process facts, the live list, the regions. -/
structure Snap where
  idx : Nat
  op : Nat
  slot : Nat
  a : Nat
  b : Nat
  res : Nat
  err : Nat
  base : Nat
  tp : Nat
  brk : Nat
  brk0 : Nat
  tlsOff : Array Nat
  blockPage : Nat
  live : Array (Nat × Nat)
  regions : Array Region

/-- Little-endian u64 at `o`. -/
def u64 (d : ByteArray) (o : Nat) : Nat :=
  (List.range 8).foldr (fun i acc => acc * 256 + (d.get! (o + i)).toNat) 0

/-- The bytes of a zero-run-elided region (writable word bit 1): `n` segments (offset, length,
bytes padded to 8) over zeros; returns the bytes and the offset after the record. -/
partial def parseRle (d : ByteArray) (o len : Nat) : Except String (ByteArray × Nat) :=
  if o + 8 > d.size then .error "truncated rle region" else
  let n := u64 d o
  let rec go (k o : Nat) (out : ByteArray) : Except String (ByteArray × Nat) :=
    if k = 0 then .ok (out, o) else
    if o + 16 > d.size then .error "truncated rle segment" else
    let off := u64 d o
    let sl := u64 d (o + 8)
    let st := o + 16
    let padded := (sl + 7) / 8 * 8
    if st + padded > d.size ∨ off + sl > len then .error "bad rle segment" else
    go (k - 1) (st + padded) (d.copySlice st out off sl)
  go n (o + 8) (ByteArray.mk (Array.replicate len 0))

partial def parseRegions (d : ByteArray) (o : Nat) (acc : Array Region) :
    Except String (Array Region × Nat) :=
  if o + 8 > d.size then .error "truncated region list" else
  let k := u64 d o
  if k = 0xffff then .ok (acc, o + 8) else
  let addr := u64 d (o + 8)
  let len := u64 d (o + 16)
  let w := u64 d (o + 24)
  let st := o + 32
  if w &&& 2 ≠ 0 then
    match parseRle d st len with
    | .error e => .error e
    | .ok (bs, o') => parseRegions d o' (acc.push ⟨k, addr, len, w &&& 1 ≠ 0, bs⟩)
  else
  let padded := (len + 7) / 8 * 8
  if st + padded > d.size then .error "truncated region" else
  parseRegions d (st + padded) (acc.push ⟨k, addr, len, w ≠ 0, d.extract st (st + len)⟩)

def snapMagic : Nat := 0x50414e5354464444
def endMagic : Nat := 0x444e4554464444

partial def parseSnaps (d : ByteArray) (o : Nat) (acc : Array Snap) : Except String (Array Snap) :=
  if o + 8 > d.size then .error "missing end marker" else
  let m := u64 d o
  if m = endMagic then .ok acc else
  if m ≠ snapMagic then .error s!"bad magic at {o}" else
  let w := fun i => u64 d (o + 8 * i)
  let nlive := w 17
  let lo := o + 8 * 18
  let live := (Array.range nlive).map fun j => (u64 d (lo + 16 * j), u64 d (lo + 16 * j + 8))
  match parseRegions d (lo + 16 * nlive) #[] with
  | .error e => .error e
  | .ok (rs, o') =>
    -- largest region first: the heap is where most loads go
    let rs := rs.qsort fun x y => x.len > y.len
    parseSnaps d o' (acc.push
      { idx := w 1, op := w 2, slot := w 3, a := w 4, b := w 5, res := w 6, err := w 7,
        base := w 8, tp := w 9, brk := w 10, brk0 := w 11,
        tlsOff := #[w 12, w 13, w 14, w 15], blockPage := w 16, live, regions := rs })

/-- The region containing byte `a` (the largest first: regions are sorted by size). -/
def regionAt (rs : List Region) (a : Nat) : Option Region :=
  rs.find? fun r => r.addr ≤ a ∧ a < r.addr + r.len

/-- **The dumped memory** as a `MemView`: a byte is known iff dumped; writable iff some region
holding it lies in a writable mapping (the harness checks `/proc/self/maps`). -/
def Snap.view (s : Snap) : MemView where
  byte a := (regionAt s.regions.toList a).map fun r => (r.bytes.get! (a - r.addr)).toNat
  writable a := s.regions.toList.any fun r => r.writable && decide (r.addr ≤ a ∧ a < r.addr + r.len)

/-- `MemView.Backs` by regions: every span lies inside one writable region (sound:
`Difftest.backsFast_sound`; the `decide` instance visits every byte). -/
def backsFast (s : Snap) (spans : List (Nat × Nat)) : Bool :=
  spans.all fun sp => sp.2 = 0 || s.regions.toList.any fun r =>
    r.writable && decide (r.addr ≤ sp.1 ∧ sp.1 + sp.2 ≤ r.addr + r.len)

/-! ## Read-back -/

/-- `x mod 2^64` as a signed offset added to `b`. -/
def addOff (b x : Nat) : Nat := (b + x) % 2 ^ 64

/-- Follow a singly linked list from `a` (stop at 0) through `next`, at most `fuel` nodes. -/
def walkS (next : Nat → Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc.reverse
  | fuel + 1, a, acc => if a = 0 then acc.reverse else walkS next fuel (next a) (a :: acc)

/-- Follow a circular list from sentinel `s` through `fd` (stop at `s` or 0). -/
def walkD (fd : Nat → Nat) (s : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc.reverse
  | fuel + 1, a, acc => if a = s ∨ a = 0 then acc.reverse else walkD fd s fuel (fd a) (a :: acc)

/-- Walk the chunks of a segment from `a`: `some (true, chunks, 0)` when the walk reaches `top`,
`some (false, chunks, pad)` at a fence-post pair (a closed segment; `pad = 16` when an old top
too small to free stays as a 16-byte in-use stub before the fences, A1's `Seg.pad`), `none`
otherwise. -/
def walkSeg (sz : Nat → Option Nat) (top : Nat) : Nat → Nat → Array (Nat × Nat) →
    Option (Bool × Array (Nat × Nat) × Nat)
  | 0, _, _ => none
  | fuel + 1, a, acc =>
    if a = top then some (true, acc, 0) else
    match sz a, sz (a + 16) with
    | some 16, some 16 => some (false, acc, if sz (a + 32) = some 16 then 16 else 0)
    | some s, _ => if s < 32 then none else walkSeg sz top fuel (a + s) (acc.push (a, s))
    | none, _ => none

/-- **Read back** `(Local, Surr)` from a snapshot, for pin `P`. -/
def readLocal (P : Pin) (s : Snap) : Local × Surr × Array String := Id.run do
  let C := P.config
  let L := P.layout
  let v := s.view
  let ld := fun (a k : Nat) => (v.load a k).getD 0
  let mut notes : Array String := #[]
  let av := P.mainArena s.base
  let St := P.statics s.base
  let E := P.envAddrs s.base s.tp
  let fuel := 4000000
  -- thread: TLS words through the GOT's tpoffs
  let tcAddr := addOff s.tp (s.tlsOff[0]!)
  let taAddr := addOff s.tp (s.tlsOff[1]!)
  let sdAddr := addOff s.tp (s.tlsOff[2]!)
  let tc := ld tcAddr 8
  let csize := fun (c : Nat) => let x := ld (c + 8) 8; x - x % 8
  -- tcache bins: (chunk, size), head first
  let tbins : Array (List (Nat × Nat)) := (Array.range C.tcacheBins).map fun i =>
    if tc = 0 then [] else
    let e := ld (tc + L.tcEntries + 8 * i) 8
    (walkS (fun p => C.reveal p (ld p 8)) 70000 e []).map fun p => (p - C.hdr, csize (p - C.hdr))
  -- fastbins, bins (1 = unsorted)
  let fbins : Array (List Nat) := (Array.range C.nFast).map fun i =>
    walkS (fun a => C.reveal (a + 16) (ld (a + 16) 8)) fuel (ld (av + L.arFastbins + 8 * i) 8) []
  let rbins : Array (List Nat) := (Array.range C.nBins).map fun i =>
    if i = 0 then [] else
    let sent := binAt L av i
    walkD (fun a => ld (a + 16) 8) sent fuel (ld (sent + 16) 8) []
  for i in [0:C.nFast] do
    if (fbins[i]!).length ≥ fuel then notes := notes.push s!"fastbin {i} walk truncated"
  for i in [0:C.nBins] do
    if (rbins[i]!).length ≥ fuel then notes := notes.push s!"bin {i} walk truncated"
  -- uses
  let mut use : Std.HashMap Nat Use := {}
  for i in [0:C.nBins] do
    for a in rbins[i]! do use := use.insert a (.bin i)
  for i in [0:C.nFast] do
    for a in fbins[i]! do use := use.insert a (.fast i)
  if tc ≠ 0 then use := use.insert (tc - C.hdr) .internal
  let useOf := fun (a : Nat) => use.getD a .client
  -- segments
  let top := ld (av + L.arTop) 8
  let sbrkBase := ld (St.mp + L.mpSbrkBase) 8
  let szOpt := fun (a : Nat) => (v.load (a + 8) 8).map fun x => x - x % 8
  -- segment starts: sbrk_base, each new anonymous region, and the address after each closed
  -- segment's fence posts (a later brk segment starts at the old break, M3: e + 2 * hdr)
  let mut work := (#[sbrkBase] ++ (s.regions.filter (fun r => r.kind = 1 ∨ r.kind = 2)).map (·.addr)).toList.eraseDups
  let mut seen : List Nat := []
  let mut cur : Option (Nat × Array (Nat × Nat)) := none
  let mut old : List Seg := []
  if sbrkBase ≠ 0 then
    for _ in [0:256] do
      match work with
      | [] => break
      | c :: rest =>
        work := rest
        if seen.contains c then continue
        seen := c :: seen
        match walkSeg szOpt top fuel c #[] with
        | some (true, cs, _) => if cur.isNone then cur := some (c, cs)
        | some (false, cs, pad) =>
          if cs.size > 0 then
            old := old ++ [⟨c, cs.toList.map (fun (a, sz) => (sz, useOf a)), pad⟩]
            let e := (cs.back?.map fun (a, sz) => a + sz).getD c
            work := work ++ [e + pad + 2 * C.hdr]
        | none => if c = sbrkBase then notes := notes.push s!"segment walk from sbrk_base {c} failed"
    if cur.isNone then notes := notes.push "current segment (ending at top) not found"
  let (start, chunks) := match cur with
    | some (c, cs) => (c, cs.toList.map fun (a, sz) => ((sz, useOf a) : Nat × Use))
    | none => (0, [])
  let tiles : TopSt :=
    { start, chunks, old, top, topSize := (if start = 0 then 0 else csize top),
      noncontig := (ld (av + L.arFlags) 4) % 4 ≥ 2,
      systemMem := ld (av + L.arSystemMem) 8, maxSystemMem := ld (av + L.arMaxSystemMem) 8 }
  let fast : FastSt := { lists := fun i => fbins.getD i [], haveFast := ld (av + L.arHaveFast) 4 ≠ 0 }
  let bmw := fun k => ld (av + L.arBinmap + 4 * k) 4
  let bins : BinsSt :=
    { lists := fun i => if i < 2 then [] else rbins.getD i [],
      binmap := fun j => decide (j < 128) && (bmw (j / 32) / 2 ^ (j % 32)) % 2 = 1 }
  let unsorted : UnsortedSt := { list := rbins.getD 1 [], lastRem := ld (av + L.arLastRem) 8 }
  let arena : ArenaSt := { tiles, fast, bins, unsorted, attached := ld (av + L.arAttached) 8 }
  let thread : ThreadSt :=
    { tcache := if tc = 0 then none else some { addr := tc, bins := fun i => tbins.getD i [] },
      arena := (let a := ld taAddr 8; if a = 0 then none else some a),
      shuttingDown := ld sdAddr 1 ≠ 0 }
  let mmChunks : List Chunk := ((s.regions.filter (·.kind = 3)).map fun r =>
    ({ addr := r.addr, size := csize r.addr, use := .client } : Chunk)).toList
  let mp : MpSt :=
    { trimThreshold := ld (St.mp + L.mpTrim) 8, mmapThreshold := ld (St.mp + L.mpMmapThreshold) 8,
      nMmaps := ld (St.mp + L.mpNMmaps) 4, maxNMmaps := ld (St.mp + L.mpMaxNMmaps) 4,
      mmappedMem := ld (St.mp + L.mpMmappedMem) 8, maxMmappedMem := ld (St.mp + L.mpMaxMmappedMem) 8,
      sbrkBase, noDyn := ld (St.mp + L.mpNoDyn) 4 ≠ 0 }
  let nextAr := ld (av + L.arNext) 8
  if nextAr ≠ av then notes := notes.push s!"main_arena.next = {nextAr} ≠ main_arena (other arenas: not read back)"
  let fl := ld St.freeList 8
  let shared : SharedSt :=
    { init := ld St.mallocInitialized 1 ≠ 0, key := ld St.tcacheKey 8, mm := { chunks := mmChunks, mp },
      arenas := [], freeList := if fl = 0 then [] else [fl], narenas := ld St.narenas 8 }
  let kernel : KernelSt := { brkStart := s.brk0, brk := s.brk, oracle := ⟨fun _ => .refuse⟩ }
  let l : Local := { avAddr := av, isMain := true, av := arena, thread, shared, kernel }
  let surr : Surr :=
    { curbrk := ld E.curbrk 8, singleThreaded := ld E.singleAddr E.singleWidth = E.singleVal,
      libcInitial := ld E.libcInitial 1 ≠ 0, alwaysFailMorecore := ld E.alwaysFailMorecore 1 ≠ 0,
      prctlSupported := (E.prctlSupported.map fun a => ld a 4).getD 1,
      narenasLimit := ld E.narenasLimit 8, freeListLock := ld E.freeListLock 4,
      listLock := ld E.listLock 4, canary := ld E.canary 8 }
  return (l, surr, notes)

/-- The `off` of `Pin.tlsAddrs` that puts `tcache` where the GOT's tpoff says. -/
def tlsOffOf (P : Pin) (s : Snap) : Nat := s.tp + P.syms.tlsTcache - addOff s.tp (s.tlsOff[0]!)

/-! ## Check A: the representation, evaluated by `decide` -/

/-- The first cell of `f` that does not hold in `v`: the cell, the loaded value, writability. -/
def firstBad (v : MemView) (f : Frag) : Option (Cell × Option Nat × Bool) :=
  (f.find? fun c => !decide (c.Holds v)).map fun c =>
    (c, v.load c.addr c.width, (List.range c.width).all fun i => v.writable (c.addr + i))

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def showBad : Option (Cell × Option Nat × Bool) → String
  | none => "ok"
  | some (c, got, w) =>
    s!"cell {hex c.addr}/{c.width} want {hex c.val} got {(got.map hex).getD "unmapped"}{if w then "" else " (not writable)"}"

/-- `nodupFast` from a set of seen elements. -/
def nodupGo : Std.HashSet Nat → List Nat → Bool
  | _, [] => true
  | s, a :: l => !s.contains a && nodupGo (s.insert a) l

/-- Nodup through a hash set (the `decide` instance is quadratic); sound:
`Difftest.nodupFast_sound`. -/
def nodupFast (l : List Nat) : Bool := nodupGo ∅ l

/-- The first byte owned twice in a fragment, with the cells owning it. -/
def firstDup (f : Frag) : Option (Nat × List Cell) :=
  let a := (f.bytes.toArray.qsort (· < ·))
  ((List.range (a.size - 1)).find? fun i => a[i]! = a[i + 1]!).map fun i =>
    (a[i]!, f.filter fun c => c.addr ≤ a[i]! ∧ a[i]! < c.addr + c.width)

def showDup : Option (Nat × List Cell) → String
  | none => ""
  | some (b, cs) => s!"byte {hex b} in {cs.map fun c => (hex c.addr, c.width, hex c.val)}"

/-! ## Linear-time evaluation of the list fragments

`SepList.dll`/`slist` index the list with `getD` (quadratic): on a 10000-chunk unsorted bin
the literal evaluation takes minutes. The checker evaluates these linear versions instead; they
are equal to the library's (`Difftest.dll_eq_dllT`, `slist_eq_slistT`, and per fragment
`fastFragF_eq`, `binsFragF_eq`, `unsortedFragF_eq`, `arenaFragT_eq`). -/

open Silmaril.Data.SepList in
/-- The node cells of `dll`, by recursion (`prev`: the previous node, the sentinel first). -/
def dllNodes (K : Links) (s : Nat) : Nat → List Nat → Frag
  | _, [] => []
  | prev, x :: r => ⟨x + K.fd, K.ws, r.headD s⟩ :: ⟨x + K.bk, K.ws, prev⟩ :: dllNodes K s x r

open Silmaril.Data.SepList in
/-- `dll` in linear time. -/
def dllT (K : Links) (s : Nat) (l : List Nat) : Frag :=
  ⟨s + K.fd, K.ws, l.headD s⟩ :: ⟨s + K.bk, K.ws, l.getLastD s⟩ :: dllNodes K s s l

open Silmaril.Data.SepList in
/-- `slist` in linear time. -/
def slistT (K : SLinks) : List Nat → Frag
  | [] => []
  | x :: r => ⟨x + K.link, K.ws, K.enc (x + K.link) (r.headD K.nil)⟩ :: slistT K r

section
variable (C : Config) (L : Layout)

/-- `fastFrag` through `slistT`. -/
def fastFragF (avAddr : Nat) (fs : FastSt) : Frag :=
  ⟨avAddr + L.arHaveFast, 4, if fs.haveFast then 1 else 0⟩ ::
  (List.range C.nFast).flatMap fun i =>
    Cell.w (avAddr + L.arFastbins + 8 * i) ((fs.lists i).headD 0) :: slistT (fastLinks C) (fs.lists i)

/-- `binsFrag` through `dllT`. -/
def binsFragF (avAddr : Nat) (bs : BinsSt) (sz : Nat → Nat) : Frag :=
  ((List.range (C.nBins - 2)).flatMap fun k =>
    let i := k + 2
    dllT binLinks (binAt L avAddr i) (bs.lists i) ++
      (if C.nSmallBins ≤ i then Silmaril.Data.SepList.skip nsLinks sz (bs.lists i) else [])) ++
  Silmaril.Data.Bitmap.frag (avAddr + L.arBinmap) 4 4 bs.binmap

/-- `unsortedFrag` through `dllT`. -/
def unsortedFragF (avAddr : Nat) (us : UnsortedSt) (sz : Nat → Nat) : Frag :=
  Cell.w (avAddr + L.arLastRem) us.lastRem :: dllT binLinks (binAt L avAddr 1) us.list ++
  (us.list.filter fun a => C.minLargeSize ≤ sz a).flatMap fun a => [Cell.w (a + 32) 0, Cell.w (a + 40) 0]

end

/-- `TopSt.sizeAt` through a hash table (`sizeAt` scans a freshly built chunk list per call,
which makes `binsFrag`/`unsortedFrag` quadratic on a 10000-chunk heap). Equal to `sizeAt`:
`Difftest.sizeTable_eq`. -/
def sizeTable (cs : List Chunk) : Std.HashMap Nat Nat :=
  cs.foldr (fun c m => m.insert c.addr c.size) ∅

/-- A size lookup from a table (bind the table once: `szOf (sizeTable …)` inside a loop would
rebuild it per call). -/
def szOf (t : Std.HashMap Nat Nat) (a : Nat) : Nat := t.getD a 0

/-- `sizeAt` from the table (`sizeAtT_eq`). -/
def sizeAtT (ts : TopSt) : Nat → Nat := szOf (sizeTable ts.heapChunks)

/-- `arenaFrag` with the tabled size lookup and the linear list fragments (`arenaFragT_eq`:
the same fragment). -/
def arenaFragT (C : Config) (L : Layout) (avAddr : Nat) (av : ArenaSt) : Frag :=
  let t := sizeTable av.tiles.heapChunks
  let sz := szOf t
  [⟨avAddr + L.arMutex, 4, 0⟩, Cell.w (avAddr + L.arAttached) av.attached] ++
  tilesFrag C L avAddr av.tiles ++ fastFragF C L avAddr av.fast ++
  binsFragF C L avAddr av.bins sz ++ unsortedFragF C L avAddr av.unsorted sz

/-- `arenaRep` with `arenaFragT` (`arenaRepT_eq`). -/
def arenaRepT (C : Config) (L : Layout) (init : Bool) (avAddr : Nat) (av : ArenaSt) : Frag :=
  if init then arenaFragT C L avAddr av else arenaFragPre C L avAddr av

/-! ## Check A: invariant fields, Boolean mirrors

Each `chk` returns `(field, ok)`; fields quantify over the indices the read-back populates
(other indices are `[]` by construction of `readLocal`). -/

def chunksWithUse (cs : List Chunk) (u : Use) : List Nat := (cs.filter (·.use = u)).map (·.addr)

/-- `ListExact l cs u`, decided. -/
def listExact (l : List Nat) (cs : List Chunk) (u : Use) : Bool :=
  let w := chunksWithUse cs u
  let sw : Std.HashSet Nat := Std.HashSet.ofList w
  let sl : Std.HashSet Nat := Std.HashSet.ofList l
  l.all (sw.contains ·) && w.all (sl.contains ·)

def chkTop (C : Config) (ts : TopSt) : List (String × Bool) :=
  let hc := ts.heapChunks
  [("TopWF.sizes", hc.all fun c => c.size % C.align = 0 && decide (C.minSize ≤ c.size)),
   ("TopWF.aligned", hc.all fun c => c.addr % C.align = 0),
   ("TopWF.nonNull", hc.all fun c => c.addr ≠ 0),
   ("TopWF.topAt", ts.start = 0 || ts.top = ts.start + (ts.chunks.map (·.1)).sum),
   ("TopWF.topAligned", ts.top % C.align = 0 && ts.topSize % C.align = 0),
   ("TopWF.topMin", ts.start = 0 || decide (C.minSize ≤ ts.topSize)),
   ("TopWF.coalesced", coalescedB ts.chunks),
   ("TopWF.lastUsed", (ts.chunks.getLast?.map fun c => !c.2.tagFree).getD true),
   ("TopWF.coalescedOld", ts.old.all fun g => coalescedB g.chunks),
   ("TopWF.sysMem", decide ((hc.map (·.size)).sum + ts.topSize ≤ ts.systemMem)),
   ("TopWF.sysMemBound", decide (ts.systemMem < 2 ^ 64)),
   ("TopWF.noHeap", ts.start ≠ 0 || (ts.chunks.isEmpty && ts.old.isEmpty)),
   ("TopWF.nodup", nodupFast (hc.map (·.addr))),
   ("TopWF.bound", hc.all fun c => decide (c.addr + c.size < 2 ^ 64)),
   ("TopWF.topBound", ts.start = 0 || decide (ts.top + ts.topSize < 2 ^ 64))]

def chkFast (C : Config) (fs : FastSt) (cs : List Chunk) : List (String × Bool) :=
  [("FastWF.exact", (List.range C.nFast).all fun i => listExact (fs.lists i) cs (.fast i)),
   ("FastWF.nodup", (List.range C.nFast).all fun i => nodupFast (fs.lists i)),
   ("FastWF.size", cs.all fun c => match c.use with
      | .fast i => C.fidx c.size = i && decide (c.size ≤ C.maxFast) && decide (i < C.nFast)
      | _ => true),
   ("FastWF.flag", !((List.range C.nFast).any fun i => !(fs.lists i).isEmpty) || fs.haveFast)]

def chkBins (C : Config) (bs : BinsSt) (cs : List Chunk) (sz : Nat → Nat) : List (String × Bool) :=
  let idx := List.range C.nBins
  [("BinsWF.exact", (idx.filter (2 ≤ ·)).all fun i => listExact (bs.lists i) cs (.bin i)),
   ("BinsWF.outside", (idx.filter fun i => i < 2 ∨ C.lastBin < i).all fun i => (bs.lists i).isEmpty),
   ("BinsWF.nodup", idx.all fun i => nodupFast (bs.lists i)),
   ("BinsWF.size", cs.all fun c => match c.use with
      | .bin i => decide (2 ≤ i) && decide (i ≤ C.lastBin) && C.binIndex c.size = i
      | _ => true),
   ("BinsWF.sorted", (idx.filter (C.nSmallBins ≤ ·)).all fun i =>
      let l := (bs.lists i).map sz
      (List.range (l.length - 1)).all fun j => decide (l.getD (j + 1) 0 ≤ l.getD j 0)),
   ("BinsWF.binmap", idx.all fun i => (bs.lists i).isEmpty || bs.binmap i)]

def chkUnsorted (C : Config) (us : UnsortedSt) (cs : List Chunk) : List (String × Bool) :=
  [("UnsortedWF.exact", listExact us.list cs (.bin 1)),
   ("UnsortedWF.nodup", nodupFast us.list),
   ("UnsortedWF.size", cs.all fun c => decide (C.minSize ≤ c.size)),
   ("UnsortedWF.lastRemBound", decide (us.lastRem < 2 ^ 64))]

def chkMmap (C : Config) (ms : MmapSt) : List (String × Bool) :=
  [("MmapWF.mpBound", decide (ms.mp.trimThreshold < 2 ^ 64 ∧ ms.mp.mmapThreshold < 2 ^ 64 ∧
      ms.mp.mmappedMem < 2 ^ 64 ∧ ms.mp.maxMmappedMem < 2 ^ 64)),
   ("MmapWF.trimMin", decide (C.trimThreshold ≤ ms.mp.trimThreshold ∧ C.mmapThreshold ≤ ms.mp.mmapThreshold)),
   ("MmapWF.use", ms.chunks.all fun c => c.use = .client || c.use = .internal),
   ("MmapWF.page", ms.chunks.all fun c => c.use ≠ .client || (c.addr % C.page = 0 && c.size % C.page = 0)),
   ("MmapWF.nonNull", ms.chunks.all fun c => c.addr ≠ 0),
   ("MmapWF.nodup", nodupFast (ms.chunks.map (·.addr))),
   ("MmapWF.mem", decide (ms.mp.mmappedMem = (ms.chunks.map (·.size)).sum))]

def chkTcache (C : Config) (tc : TcacheSt) : List (String × Bool) :=
  let idx := List.range C.tcacheBins
  [("TcacheWF.nodup", idx.all fun i => nodupFast ((tc.bins i).map (·.1)) && decide ((tc.bins i).length ≤ C.tcacheCount)),
   ("TcacheWF.size", idx.all fun i => (tc.bins i).all fun c =>
      C.tidx c.2 = i && c.2 % C.align = 0 && decide (C.minSize ≤ c.2)),
   ("TcacheWF.nonNull", idx.all fun i => (tc.bins i).all fun c => c.1 ≠ 0 && c.1 % C.align = 0),
   ("TcacheWF.struct", decide (tc.addr ≠ 0))]

/-- `WorldWF.parked` for one thread: every tcache chunk is a lent-out chunk of the tiling. -/
def parkedOk (C : Config) (l : Local) : Bool :=
  match l.thread.tcache with
  | none => true
  | some tc => (List.range C.tcacheBins).all fun i => (tc.bins i).all fun c =>
      l.av.chunks.any fun d => d.addr = c.1 && d.size = c.2 && d.use = .client

def chkLocal (C : Config) (l : Local) : List (String × Bool) :=
  let av := l.av
  let tbl := sizeTable av.tiles.heapChunks
  let sh := l.shared
  chkTop C av.tiles ++ chkFast C av.fast av.fastView ++
  chkBins C av.bins av.sortedView (szOf tbl) ++ chkUnsorted C av.unsorted av.unsortedView ++
  [("ArenaWF.internal", av.chunks.all fun c => c.use ≠ .internal || decide (C.minSize ≤ c.size))] ++
  chkMmap C sh.mm ++
  [("SharedWF.narenas", decide (sh.narenas = sh.arenas.length + 1)),
   ("SharedWF.freeListSub", sh.freeList.all (sh.arenas.contains ·))] ++
  ((l.thread.tcache.map (chkTcache C)).getD []) ++
  (if l.isMain then
    [("MainSbrk", ((sh.mm.mp.sbrkBase == 0) == (av.tiles.start == 0)) &&
        (av.tiles.noncontig || (sh.mm.mp.sbrkBase == av.tiles.start && av.tiles.old.isEmpty))),
     ("MainBrk.page≤brkStart≤brk", decide (C.page ≤ l.kernel.brkStart ∧ l.kernel.brkStart ≤ l.kernel.brk)),
     ("MainBrk.brkAligned", decide (l.kernel.brk % C.page = 0)),
     ("MainBrk.topEnd", av.tiles.start = 0 || (av.tiles.top + av.tiles.topSize) % C.page = 0),
     ("MainBrk.contig", av.tiles.start = 0 || av.tiles.noncontig ||
        (decide (l.kernel.brkStart ≤ av.tiles.start) && l.kernel.brk = av.tiles.top + av.tiles.topSize)),
     ("LocalWF.sysMain", decide (av.tiles.systemMem + sh.mm.mp.mmappedMem ≤ l.kernel.total))]
  else []) ++
  [("LocalWF.init", sh.init || (av.tiles.start = 0 && sh.mm.chunks.isEmpty && l.thread.tcache.isNone)),
   ("WorldWF.parked", parkedOk C l),
   ("WorldWF.parkedOnce", nodupFast ((l.thread.parked C).map (·.1)))]

/-- Sorted (payload, usable) pairs. -/
def sortPairs (l : List (Nat × Nat)) : List (Nat × Nat) :=
  (l.toArray.qsort fun x y => x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)).toList

/-! ## Driving -/

/-- One check result. -/
structure Check where
  name : String
  ok : Bool
  detail : String := ""

/-- **Check A** on one snapshot (and the live-set agreement). `full`: also decide `LocalRep`
as one proposition (its byte `Nodup` is quadratic; the per-part checks use `nodupFast`). -/
def checkSnap (P : Pin) (s : Snap) (full : Bool) : Local × Array Check := Id.run do
  let C := P.config
  let L := P.layout
  let (l, surr, notes) := readLocal P s
  let v := s.view
  let St := P.statics s.base
  let off := tlsOffOf P s
  let T := P.tlsAddrs s.tp off
  let E := P.envAddrs s.base s.tp
  let mut rs : Array Check := notes.map fun m => { name := "readback", ok := false, detail := m }
  -- TLS offsets of the pin agree with the binary's GOT
  let tlsOk := T.arena = addOff s.tp (s.tlsOff[1]!) ∧ T.shutdown = addOff s.tp (s.tlsOff[2]!) ∧
    T.errno = addOff s.tp (s.tlsOff[3]!)
  rs := rs.push { name := "pin.tlsOffsets", ok := decide tlsOk }
  -- fragments
  let av := l.av
  let tbl := sizeTable av.tiles.heapChunks
  -- D1: before `ptmalloc_init` the arena is the static (zero) image
  let arenaParts : List (String × Frag) := if l.shared.init then
    [("rep.arena.cells", [⟨l.avAddr + L.arMutex, 4, 0⟩, Cell.w (l.avAddr + L.arAttached) av.attached]),
     ("rep.tilesFrag", tilesFrag C L l.avAddr av.tiles),
     ("rep.fastFrag", fastFragF C L l.avAddr av.fast),
     ("rep.binsFrag", binsFragF C L l.avAddr av.bins (szOf tbl)),
     ("rep.unsortedFrag", unsortedFragF C L l.avAddr av.unsorted (szOf tbl))]
    else [("rep.arenaFragPre", arenaFragPre C L l.avAddr av)]
  let parts : List (String × Frag) := arenaParts ++
    [("rep.threadFrag", threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread),
     ("rep.sharedFrag", sharedFrag C L St l.shared),
     ("env.envFrag", envFrag C L E surr)]
  for (nm, f) in parts do
    let b := firstBad v f
    rs := rs.push { name := nm, ok := b.isNone, detail := showBad b }
  let spans := spansOf av
  rs := rs.push { name := "rep.backs", ok := backsFast s spans }
  if full then
    rs := rs.push { name := "rep.backs(decide)", ok := decide (v.Backs spans) }
  let fa := arenaRepT C L l.shared.init l.avAddr av
  let ft := threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread
  let fs := sharedFrag C L St l.shared
  let ok1 := nodupFast (fa ++ ft ++ fs).bytes
  rs := rs.push { name := "rep.nodup", ok := ok1, detail := if ok1 then "" else showDup (firstDup (fa ++ ft ++ fs)) }
  let fe := fa ++ ft ++ fs ++ envFrag C L E surr
  let ok2 := nodupFast fe.bytes
  rs := rs.push { name := "env.disjointRep", ok := ok2, detail := if ok2 then "" else showDup (firstDup fe) }
  -- `RepApart`'s second half: no surroundings byte in a heap span
  let envB := (envFrag C L E surr).bytes
  let okS := envB.all fun a => spans.all fun sp => !(decide (sp.1 ≤ a) && decide (a < sp.1 + sp.2))
  rs := rs.push { name := "env.apartSpans", ok := okS }
  if full then
    rs := rs.push { name := "rep.LocalRep(decide)", ok := decide (LocalRep C L St T l v) }
  rs := rs.push { name := "env.SurrInv", ok := decide (SurrInv surr l.kernel l.shared) }
  for (nm, ok) in chkLocal C l do
    rs := rs.push { name := nm, ok }
  -- W11/M10: the canary is not in a live payload
  let liveM := Local.live C l
  rs := rs.push { name := "M10.canaryApart", ok := liveM.all fun (p, u) => !(p ≤ E.canary + 7 ∧ E.canary < p + u) }
  -- live set: model vs harness
  let a := sortPairs liveM
  let b := sortPairs s.live.toList
  let showL := fun (x : List (Nat × Nat)) => (x.take 4).map fun (p, u) => (hex p, u)
  let det := if a == b then "" else
    s!"model-only {showL (a.filter (!b.contains ·))} harness-only {showL (b.filter (!a.contains ·))}"
  rs := rs.push { name := "live.agree", ok := a == b, detail := det }
  return (l, rs)

/-- The tcache bins of a `Local` as a comparable list. -/
def tcBins (C : Config) (l : Local) : Option (Nat × List (List (Nat × Nat))) :=
  l.thread.tcache.map fun tc => (tc.addr, (List.range C.tcacheBins).map tc.bins)

/-- The arena's comparable shape. -/
def arenaShape (C : Config) (l : Local) :=
  (l.av.chunks, l.av.tiles.top, l.av.tiles.topSize, (List.range C.nFast).map l.av.fast.lists,
   (List.range C.nBins).map l.av.bins.lists, l.av.unsorted.list)

/-! ## Check B: replaying an algorithm model (`Ops`) -/

/-- The single-thread world of a read-back `Local` (thread id 0). -/
def worldOf (l : Local) : World :=
  { mainArena := l.avAddr, arenas := fun a => if a = l.avAddr then some l.av else none,
    tids := [0], threads := fun _ => l.thread, shared := l.shared, kernel := l.kernel }

/-- All interleavings of two lists, each kept in order. -/
def interleave {α : Type} : List α → List α → List (List α)
  | [], ys => [ys]
  | xs, [] => [xs]
  | x :: xs, y :: ys => (interleave xs (y :: ys)).map (x :: ·) ++ (interleave (x :: xs) ys).map (y :: ·)

/-- **Candidate kernel answers** for the op between two snapshots. The kernel is
nondeterministic and the dump shows only the net effect, so check B asks whether SOME
consistent answer sequence makes the model agree: `tcache_key`'s random word first when
`ptmalloc_init` runs, then the new mappings in address order of discovery (new `mmap`ed chunks,
`mremap` targets, new heap segments; each `.ok addr`), interleaved with up to two `brk`
answers (granted `.ok 0`, which no `mmap` accepts; or one refusal while the break is blocked);
every later question is refused. -/
def oracles (s0 s1 : Snap) (l0 l1 : Local) : List KOracle :=
  let key : List KAns := if l0.shared.init then [] else [.ok l1.shared.key]
  let mm := (l1.shared.mm.chunks.filter fun c => !l0.shared.mm.chunks.contains c).map fun c => KAns.ok c.addr
  let segs0 := (s0.regions.filter (·.kind = 2)).map (·.addr)
  let segs := ((s1.regions.filter fun r => r.kind = 2 ∧ !segs0.contains r.addr).map fun r => KAns.ok r.addr).toList
  let brks : List (List KAns) := if s0.blockPage ≠ 0 then [[], [.refuse]]
    else [[], [.ok 0], [.ok 0, .ok 0], [.ok 0, .ok 0, .ok 0]]
  (brks.flatMap fun b => interleave b (mm ++ segs)).map fun xs =>
    let ys := key ++ xs
    ⟨fun i => ys.getD i .refuse⟩

/-- Chunks by address. -/
def sortChunks (cs : List Chunk) : List Chunk := (cs.toArray.qsort fun x y => x.addr < y.addr).toList

/-- A short rendering of one `shapeDiff` field (the first few entries of a list). -/
def showField (C : Config) (nm : String) (l : Local) : String :=
  let cs := fun (xs : List Chunk) => toString ((xs.take 6).map fun c => (hex c.addr, hex c.size, repr c.use))
  match nm with
  | "chunks" => cs (l.av.chunks.drop (l.av.chunks.length - 6))
  | "old" => toString (l.av.tiles.old.map fun g => (hex g.start, g.chunks.length, g.pad))
  | "top" => s!"start {hex l.av.tiles.start} top {hex l.av.tiles.top} size {hex l.av.tiles.topSize}"
  | "systemMem" => s!"{hex l.av.tiles.systemMem}/{hex l.av.tiles.maxSystemMem}"
  | "mmapped" => cs l.shared.mm.chunks
  | "mp" => let m := l.shared.mm.mp
    s!"trim {hex m.trimThreshold} mmap {hex m.mmapThreshold} n {m.nMmaps}/{m.maxNMmaps} mem {hex m.mmappedMem}/{hex m.maxMmappedMem} sbrk {hex m.sbrkBase}"
  | "brk" => hex l.kernel.brk
  | "unsorted" => toString ((l.av.unsorted.list.take 6).map hex)
  | "lastRem" => hex l.av.unsorted.lastRem
  | "tcache" => toString ((tcBins C l).map fun (a, bs) => (hex a, (bs.filter (· ≠ [])).length))
  | "bins" => toString (((List.range C.nBins).filter fun i => l.av.bins.lists i ≠ []).map fun i =>
      (i, (l.av.bins.lists i).map hex))
  | "fastbins" => toString (((List.range C.nFast).filter fun i => l.av.fast.lists i ≠ []).map fun i =>
      (i, (l.av.fast.lists i).map hex))
  | _ => ""

/-- The observable abstract state of a `Local`, compared field by field: the first differing
field's name, or `none`. (`tcache_key` is random: not compared when `init` was false.) -/
def shapeDiff (C : Config) (keyToo : Bool) (x y : Local) : Option String :=
  let mp := fun (l : Local) => let m := l.shared.mm.mp
    [m.trimThreshold, m.mmapThreshold, m.nMmaps, m.maxNMmaps, m.mmappedMem, m.maxMmappedMem, m.sbrkBase]
  let fields : List (String × Bool) :=
    [("chunks", x.av.chunks == y.av.chunks), ("old", x.av.tiles.old == y.av.tiles.old),
     ("top", x.av.tiles.top == y.av.tiles.top && x.av.tiles.topSize == y.av.tiles.topSize),
     ("systemMem", x.av.tiles.systemMem == y.av.tiles.systemMem && x.av.tiles.maxSystemMem == y.av.tiles.maxSystemMem),
     ("noncontig", x.av.tiles.noncontig == y.av.tiles.noncontig),
     ("fastbins", (List.range C.nFast).map x.av.fast.lists == (List.range C.nFast).map y.av.fast.lists),
     ("haveFast", x.av.fast.haveFast == y.av.fast.haveFast),
     ("bins", (List.range C.nBins).map x.av.bins.lists == (List.range C.nBins).map y.av.bins.lists),
     ("binmap", (List.range C.nBins).map x.av.bins.binmap == (List.range C.nBins).map y.av.bins.binmap),
     ("unsorted", x.av.unsorted.list == y.av.unsorted.list),
     ("lastRem", x.av.unsorted.lastRem == y.av.unsorted.lastRem),
     ("tcache", tcBins C x == tcBins C y),
     ("init", x.shared.init == y.shared.init), ("key", !keyToo || x.shared.key == y.shared.key),
     ("mmapped", sortChunks x.shared.mm.chunks == sortChunks y.shared.mm.chunks), ("mp", mp x == mp y),
     ("brk", x.kernel.brk == y.kernel.brk)]
  (fields.find? (!·.2)).map fun (nm, _) => nm ++ " " ++ showField C nm x ++ " vs glibc " ++ showField C nm y

/-- glibc's refill of tcache bin `i` from another list (the fastbin and smallbin paths of
`_int_malloc`): while the bin has room and `pop` yields a chunk, `Local.tcachePut` it. -/
def stash (C : Config) (pop : Local → Option (Nat × Local)) (sz i : Nat) : Nat → Local → Local
  | 0, l => l
  | k + 1, l =>
    match l.thread.tcache with
    | none => l
    | some tc =>
      if (tc.bins i).length < C.tcacheCount then
        match pop l with
        | some (a, l') =>
          match l'.tcachePut (a, sz) i with
          | some l'' => stash C pop sz i k l''
          | none => l'
        | none => l
      else l

/-- **Leaf prediction of `malloc (n)`** from the model's leaf operations, on the paths where
glibc 2.39's choice is determined by the abstract state: a tcache hit (`tcacheGet`); a fastbin
hit (`fastPop`, then the stash into the tcache); a smallbin hit (`binRemove` of the bin's last
chunk, then the stash). The path name, the payload, the predicted `Local`. -/
def predictMalloc (C : Config) (l : Local) (n : Nat) : Option (String × Nat × Local) := do
  let nb ← C.checkedRequest2size n
  let tc ← l.thread.tcache
  let i := C.tidx nb
  if i < C.tcacheBins ∧ tc.bins i ≠ [] then
    let (p, l') ← l.tcacheGet C i
    return ("B.leaf.tcacheGet", p, l')
  if nb ≤ C.maxFast ∧ l.av.fast.lists (C.fidx nb) ≠ [] then
    let fi := C.fidx nb
    let (a, l') ← l.fastPop fi
    let l'' := if i < C.tcacheBins then stash C (fun x => x.fastPop fi) nb i C.tcacheCount l' else l'
    return ("B.leaf.fastPop+stash", a + C.hdr, l'')
  if C.inSmallRange nb ∧ l.av.bins.lists (C.binIndex nb) ≠ [] then
    let bi := C.binIndex nb
    let popLast := fun (x : Local) =>
      (x.av.bins.lists bi).getLast?.map fun a => (a, x.binRemove a bi .client)
    let (a, l') ← popLast l
    let l'' := if i < C.tcacheBins then stash C popLast nb i C.tcacheCount l' else l'
    return ("B.leaf.smallbin+stash", a + C.hdr, l'')
  none

/-- **Leaf prediction of `free`** of chunk `c`: into the tcache (`tcachePut`) when its bin has
room; else a fastbin (`fastPush`) up to `global_max_fast`; else the unsorted bin
(`unsortedPush`) when no neighbour merges, the next chunk is not top and the size is below
`FASTBIN_CONSOLIDATION_THRESHOLD`. -/
def predictFree (C : Config) (l : Local) (c : Nat) : Option (String × Local) := do
  let tc ← l.thread.tcache
  let ch ← l.av.chunks.find? (·.addr = c)
  let i := C.tidx ch.size
  if i < C.tcacheBins ∧ (tc.bins i).length < C.tcacheCount then
    let l' ← l.tcachePut (c, ch.size) i
    return ("B.leaf.tcachePut", l')
  if ch.size ≤ C.maxFast then
    return ("B.leaf.fastPush", l.fastPush c (C.fidx ch.size))
  let prevFree := l.av.chunks.any fun d => d.addr + d.size = c && d.use.tagFree
  let nextFree := l.av.chunks.any fun d => d.addr = c + ch.size && d.use.tagFree
  if prevFree || nextFree || c + ch.size = l.av.tiles.top || decide (C.consolidationThreshold ≤ ch.size) then
    none
  else return ("B.leaf.unsortedPush", l.unsortedPush c)

/-- **Op checks** between consecutive snapshots `s0 → s1` (op `s1.op`): the live-set contract
(`MallocLive`; free removes exactly the payload) on the model's live sets, and the leaf
predictions (partial check B). -/
def checkOp (P : Pin) (s1 : Snap) (l0 l1 : Local) : Array Check := Id.run do
  let C := P.config
  let mut rs : Array Check := #[]
  let live0 := Local.live C l0
  let live1 := Local.live C l1
  let op := Char.ofNat s1.op
  if op = 'm' ∨ op = 'c' then
    let n := if op = 'm' then s1.a else s1.a * s1.b
    let p := s1.res
    let ok := if p = 0 then sortPairs live1 == sortPairs live0 else
      p % C.align = 0 && (live1.filter (·.1 = p)).length = 1 &&
      (match live1.find? (·.1 = p) with
       | some (_, u) => decide (n ≤ u) && sortPairs live1 == sortPairs ((p, u) :: live0) &&
           live0.all fun q => decide (q.1 + q.2 ≤ p ∨ p + u ≤ q.1)
       | none => false)
    rs := rs.push { name := "B.MallocLive", ok }
    if op = 'm' then
      match predictMalloc C l0 n with
      | some (nm, q, l') =>
        let d := shapeDiff C true l' l1
        let det := s!"payload predicted {hex q} glibc {hex p}; first differing field {d.getD "-"}"
        rs := rs.push { name := nm, ok := q = p && d.isNone, detail := det }
      | none => pure ()
  if op = 'f' then
    -- the freed payload is the one live in s0 but not in s1
    let gone := live0.filter fun pu => !live1.contains pu
    match gone with
    | [(p, u)] =>
      rs := rs.push { name := "B.freeLive", ok := sortPairs live1 == sortPairs (live0.erase (p, u)) }
      match predictFree C l0 (p - C.hdr) with
      | some (nm, l') =>
        let d := shapeDiff C true l' l1
        rs := rs.push { name := nm, ok := d.isNone, detail := s!"first differing field {d.getD "-"}" }
      | none => pure ()
    | [] => rs := rs.push { name := "B.freeLive", ok := true, detail := "free (NULL)" }
    | _ => rs := rs.push { name := "B.freeLive", ok := false, detail := "several payloads disappeared" }
  return rs

/-- **Check B** for an algorithm model `A`: replay the op of `s1` (malloc, calloc, realloc,
free) through `A`'s wrappers on the world read back from the previous snapshot, with the
kernel answers among `oracles` (any one agreeing passes), and compare the returned payload and the abstract state
with the read-back of `s1` (`shapeDiff`). -/
def checkReplay {C : Config} (A : Ops C) (s0 s1 : Snap) (l0 l1 : Local) : Array Check :=
  let op := Char.ofNat s1.op
  let run := fun (o : KOracle) =>
    let w := { worldOf l0 with kernel := { l0.kernel with oracle := o } }
    -- for free and realloc the harness reports the slot's old pointer as `b`
    let r : Option (Ptmalloc.Res (Nat × World)) :=
      if op = 'm' then some (A.malloc w 0 s1.a)
      else if op = 'c' then some (A.calloc w 0 s1.a s1.b)
      else if op = 'f' then some ((A.free w 0 s1.b).map fun w' => (s1.res, w'))
      else if op = 'r' then some (A.realloc w 0 s1.b s1.a)
      else none
    r.map fun r => match r with
      | .error e => (false, s!"model aborts {repr e}")
      | .ok (p, w') =>
        match w'.local? 0 l1.avAddr with
        | none => (false, "no main arena after the op")
        | some l' =>
          let d := shapeDiff C true l' l1
          (p = s1.res && d.isNone,
            s!"payload model {hex p} glibc {hex s1.res}; first differing field {d.getD "-"}")
  let nm := s!"B.replay.{match op with | 'm' => "malloc" | 'c' => "calloc" | 'f' => "free" | _ => "realloc"}"
  let os := oracles s0 s1 l0 l1
  match os.findSome? fun o => (run o).bind fun (ok, _) => if ok then some () else none with
  | some () => #[{ name := nm, ok := true }]
  | none =>
    match os.head?.bind run with
    | some (_, det) => #[{ name := nm, ok := false, detail := s!"no kernel answers agree ({os.length} tried); first: {det}" }]
    | none => #[]

/-- The static regions the harness dumps for pin `P`, as `off:len` (len 0: a GOT slot holding
a TLS tpoff: tcache, thread_arena, tcache_shutting_down, errno, in this order). -/
def regionSpec (P : Pin) : String :=
  let got := fun nm => ((P.syms.got.find? (·.1 = nm)).map (·.2)).getD 0
  let y := P.syms
  let hx := fun n => String.ofList (Nat.toDigits 16 n)
  let items : List (Nat × Nat) :=
    [(got "tcache", 0), (got "thread_arena", 0), (got "tcache_shutting_down", 0), (got "errno", 0),
     (y.mainArena, P.layout.arSize), (y.mp, P.layout.mpSize),
     (y.mallocInitialized, 1), (y.tcacheKey, 8), (y.globalMaxFast, y.globalMaxFastWidth), (y.perturbByte, 4),
     (y.curbrk, 8), (y.singleThreaded, 1), (y.libcInitial, 1), (y.alwaysFailMorecore, 1),
     (y.freeList, 8), (y.freeListLock, 4), (y.listLock, 4), (y.narenas, 8), (y.narenasLimit, 8)] ++
    ((y.prctlSupported.map fun a => [(a, 4)]).getD [])
  ",".intercalate (items.map fun (o, n) => s!"{hx o}:{hx n}")

/-- **The checker's entry point.** `regions` prints `regionSpec pin239`; `check DUMP [full]`
checks every snapshot and every consecutive pair, printing `SNAP`/`FAIL`/`SUM` lines. With an
algorithm model `ops` (`algo`'s `ptmalloc pin239.config`), each op is also replayed (check B). -/
def runWith (ops : Option (Ops pin239.config)) (args : List String) : IO UInt32 := do
  let P := pin239
  match args with
  | ["regions"] => IO.println (regionSpec P); return 0
  | "check" :: path :: rest =>
    let full := rest.contains "full"
    let d ← IO.FS.readBinFile path
    match parseSnaps d 0 #[] with
    | .error e => IO.eprintln s!"parse: {e}"; return 2
    | .ok snaps =>
      let mut prev : Option (Snap × Local) := none
      let mut nfail := 0
      let mut nchecks := 0
      let mut counts : Std.HashMap String (Nat × Nat) := {}
      for s in snaps do
        let (l, rs) := checkSnap P s full
        let rs := match prev with
          | some (s0, l0) =>
            if s.idx = s0.idx + 1 then
              rs ++ checkOp P s l0 l ++ ((ops.map fun A => checkReplay A s0 s l0 l).getD #[])
            else rs
          | none => rs
        let bad := rs.filter (!·.ok)
        nchecks := nchecks + rs.size
        for r in rs do
          let (a, b) := counts.getD r.name (0, 0)
          counts := counts.insert r.name (if r.ok then (a + 1, b) else (a, b + 1))
        nfail := nfail + bad.size
        IO.println s!"SNAP {s.idx} {Char.ofNat s.op} {s.slot} {s.a} {s.b} {hex s.res} checks={rs.size} fail={bad.size} chunks={l.av.chunks.length} tcache={(l.thread.parked P.config).length} unsorted={l.av.unsorted.list.length} old={l.av.tiles.old.length} noncontig={l.av.tiles.noncontig}"
        for r in bad do
          IO.println s!"FAIL {s.idx} {r.name} {r.detail}"
        prev := some (s, l)
      for (nm, (a, b)) in counts.toList do
        IO.println s!"COUNT {nm} {a} {b}"
      IO.println s!"SUM snaps={snaps.size} checks={nchecks} fail={nfail}"
      return (if nfail = 0 then 0 else 1)
  | _ => IO.eprintln "usage: regions | check DUMP [full]"; return 2

/-- The checker without an algorithm model (check B partial: the tcache leaf operations). -/
def run (args : List String) : IO UInt32 := runWith none args

end Silmaril.Libc.Ptmalloc.Difftest
