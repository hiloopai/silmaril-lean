module

public import Silmaril.X86.Concurrency.Cir.Fj.Defs
public import Silmaril.X86.Ladder.ZlibChecksums.Defs

/-!
# Parallel hashing on CIR: definitions

The program
(`examples/litmus-c/par-hash/par_hash.c`):

```c
static void *worker(void *p) {             /* thread k + 1 */
  struct job *j = p;
  res[j->k] = crc32_z(0, j->buf, j->len);  /* zlib 1.3.1, rung 03 */
  return 0;
}
int main(void) {                            /* thread 0 */
  for (k = 0; k < N; k++) pthread_create(&t[k], 0, worker, &jobs[k]);
  for (k = 0; k < N; k++) pthread_join(t[k], 0);
  out = crc32_z(0, (const unsigned char *)res, 8 * N);   /* hash of the hashes */
}
```

In CIR each worker is **one** `local(B)` block (`leafJob`): it reads its buffer (one byte cell
per byte) and writes its 8-byte result cell (`z_crc_t` is `unsigned long`). Its summary
`crcFn` is the function that zlib's verified `crc32_z` contract
(`ZlibChecksums.crc32zContract`) puts in `rax`: `crc32 0` of the buffer bytes. The combine
(`rootJob`) is the same contract applied to the result array. The program is a fork-join
program (`Fj.Par`), so the fork-join theorem applies with no reasoning about the memory model.

The expected results are stated directly on the initial memory: `leaf m b` is the CRC of
buffer `b`, `root m bufs` the CRC of the little-endian bytes of the leaves.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.ParHash

open Silmaril.X86.Concurrency.Cir.Fj
open Silmaril.X86.Ladder.ZlibChecksums (crc32)

/-- Input values as bytes. -/
def toBytes (vs : List Nat) : List (BitVec 8) := vs.map (BitVec.ofNat 8)

/-- **The summary of `crc32_z(0, buf, len)`**: one 8-byte output, the CRC of the input bytes
(the function `crc32zContract` puts in `rax`). -/
def crcFn (vs : List Nat) : List Nat := [(crc32 0 (toBytes vs)).toNat]

/-- A buffer `(addr, len)` as one byte cell per byte. -/
def bufCells (b : Nat × Nat) : List (Nat × Nat) := (List.range b.2).map fun k => (b.1 + k, 1)

/-- **A worker**: `res = crc32_z(0, buf, len)` for buffer `b` and result cell `r`. -/
def leafJob (b : Nat × Nat) (r : Nat) : Job := ⟨"crc32_z", bufCells b, [(r, 8)], crcFn⟩

/-- The `n` 8-byte result cells from `res`. -/
def resCells (res n : Nat) : List (Nat × Nat) := (List.range n).map fun i => (res + 8 * i, 8)

/-- The summary of `crc32_z(0, res, 8 * n)` over 8-byte cells: the CRC of their
little-endian bytes. -/
def rootFn (vs : List Nat) : List Nat := [(crc32 0 (vs.flatMap fun v => natBytes v 8)).toNat]

/-- **The combine**: `out = crc32_z(0, res, 8 * n)`. -/
def rootJob (res n out : Nat) : Job := ⟨"crc32_z", resCells res n, [(out, 8)], rootFn⟩

/-- **The parallel hashing program**: buffers `bufs`, result array at `res`, output at `out`. -/
def par (locs : List Silmaril.X86.MemoryModel.Litmus.Loc) (bufs : List (Nat × Nat)) (res out : Nat) :
    Par :=
  ⟨locs, bufs.mapIdx (fun i b => leafJob b (res + 8 * i)), rootJob res bufs.length out⟩

/-- The bytes of buffer `b` in a flat memory (unmapped bytes read as `0`). -/
def memBytes (m : Mem) (b : Nat × Nat) : List (BitVec 8) :=
  (List.range b.2).map fun k => (m (b.1 + k)).getD 0

/-- The expected hash of buffer `b`. -/
def leaf (m : Mem) (b : Nat × Nat) : BitVec 32 := crc32 0 (memBytes m b)

/-- The expected hash of the hashes. -/
def root (m : Mem) (bufs : List (Nat × Nat)) : BitVec 32 :=
  crc32 0 (bufs.flatMap fun b => natBytes (leaf m b).toNat 8)

/-! ## A small instance, for the enumerator -/

/-- Two one-byte buffers holding `7` and `9`. -/
def tinyLocs : List Silmaril.X86.MemoryModel.Litmus.Loc := [⟨"b0", 0x100, 1, 7⟩, ⟨"b1", 0x140, 1, 9⟩]

/-- The buffers of the small instance. -/
def tinyBufs : List (Nat × Nat) := [(0x100, 1), (0x140, 1)]

/-- The small instance: results at `0x200`, output at `0x300`. -/
def tiny : Par := par tinyLocs tinyBufs 0x200 0x300

/-- The value domain of the small instance: the initial bytes and the three CRCs. -/
def tinyDom : List Nat :=
  [0, 7, 9, (leaf (Silmaril.X86.MemoryModel.Litmus.initByte tinyLocs) (0x100, 1)).toNat,
    (leaf (Silmaril.X86.MemoryModel.Litmus.initByte tinyLocs) (0x140, 1)).toNat,
    (root (Silmaril.X86.MemoryModel.Litmus.initByte tinyLocs) tinyBufs).toNat]

/-- The small instance as a litmus test observing the output. -/
def tinyTest : Silmaril.X86.MemoryModel.Litmus.Test :=
  { tiny.prog.memTest with
    cond := .atom
      (.mem 0x300 8 (root (Silmaril.X86.MemoryModel.Litmus.initByte tinyLocs) tinyBufs).toNat) }


/-- **Mutant**: the small instance with the main thread's joins removed. -/
def tinyNoJoin : Prog :=
  ⟨tinyLocs, ⟨.seq (seqs [.spawn 1, .spawn 2]) (.local tiny.comb.block), false⟩ ::
    tiny.jobs.map fun j => ⟨.local j.block, true⟩⟩

/-- The combine's output when it reads both result cells before the workers wrote them. -/
def staleRoot : Nat := (crc32 0 (natBytes 0 8 ++ natBytes 0 8)).toNat

/-- The mutant's domain: the initial bytes, the leaves and the combine outputs it can see. -/
def tinyNoJoinDom : List Nat := tinyDom ++ [staleRoot]

/-- The mutant as a litmus test observing the output. -/
def tinyNoJoinTest : Silmaril.X86.MemoryModel.Litmus.Test :=
  { tinyNoJoin.memTest with cond := .atom (.mem 0x300 8 staleRoot) }

end Silmaril.X86.Concurrency.Cir.ParHash
