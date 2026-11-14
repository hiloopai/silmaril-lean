module

public import Silmaril.X86.Concurrency.Cir.ParHash.Defs
public import Silmaril.X86.Concurrency.Cir.Fj.Thms
public import Silmaril.X86.Concurrency.Lift.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.ParHash

/-!
# Parallel hashing on CIR: what is proved

PROVED (standard axioms):

* **`par_hash`**: for every layout of `N` buffers, a result array and an output cell that
  passes the footprint check (`(par locs bufs res out).okB`), and every model `M ⊑ XL`
  (`par_hash_models`: SC, x86-TSO, XL), every behaviour of the parallel hashing program ends
  with `res[k] = crc32(0, buffer k)` for every worker `k` and `out = crc32(0, res)`, all
  computed on the initial memory. It is `Fj.Par.behav_job` and `Fj.Par.behav_comb`
  instantiated: no reasoning about the memory model.
* **The worker block's summary is zlib's contract** (no re-proof):
  * `leaf_spec_of_post`: the postcondition of `crc32zContract` for `crc32_z(0, buf, len)`
    gives the block's contract `crcFn` for the value in `rax`;
  * `leaf_total`: every entry state meeting the contract runs to such a state
    (`ZlibChecksums.crc32z_total`, unchanged);
  * `leaf_total_under`: the same run reads the same under every `SC ⊑ M ⊑ XL`
    (`Lift.crc32z_total_under`; unconditional since the glue
    `Lift.Task.openFlatStep` is proved).
* `ex`: a concrete layout (four 64-byte buffers) passes the check (`ex_okB`, by `decide`), so
  `ex_hash` holds for it.
* **Non-vacuity** (`tiny_behav`): a small instance (two one-byte buffers) has an SC behaviour,
  found by the enumerator (`decide +kernel`, about 7 s), hence TSO and XL behaviours; and
  every behaviour under every `M ⊑ XL` has the expected output. So `par_hash` is not about an
  empty set of behaviours.
* **The joins are load-bearing** (`tinyNoJoin_stale`): with the joins removed, an SC
  behaviour hashes the initial zero results, an output other than the expected one.

What is not proved: that the gcc-compiled `par_hash.c` translation-validates to `par` (the
C source is in `examples/litmus-c/par-hash/`; CIR's x86 checker does not yet handle calls or
`pthread_create`), and that the threads are real LPS threads (LPS has none).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.ParHash

open Silmaril.X86.Concurrency.Cir.Fj
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (leValue initByte Loc Final)
open Silmaril.X86.Ladder.ZlibChecksums (crc32zContract buf crc32z_total)

/-- **Parallel hashing under every `M ⊑ XL`**: each worker's result is the CRC of its buffer,
and the output is the CRC of the results. -/
theorem par_hash {locs : List Loc} {bufs : List (Nat × Nat)} {res out : Nat}
    (hok : (par locs bufs res out).okB = true) {M : Exec → Prop} (hM : M ⊑ Exec.Xl) {f : Final}
    (h : Behav (par locs bufs res out).prog M f) :
    (∀ (k : Nat) (hk : k < bufs.length),
      leValue f.mem (res + 8 * k) 8 = some (leaf (initByte locs) bufs[k]).toNat) ∧
    leValue f.mem out 8 = some (root (initByte locs) bufs).toNat :=
  ⟨Silmaril.Proofs.X86.Concurrency.Cir.ParHash.behav_leaf (Par.ok_of_okB hok) hM h,
    Silmaril.Proofs.X86.Concurrency.Cir.ParHash.behav_root (Par.ok_of_okB hok) hM h⟩

/-- The output under SC, x86-TSO and XL. -/
theorem par_hash_models {locs : List Loc} {bufs : List (Nat × Nat)} {res out : Nat}
    (hok : (par locs bufs res out).okB = true) :
    ∀ M ∈ [Exec.Sc, Exec.Tso, Exec.Xl], Safe (par locs bufs res out).prog M
      fun f => leValue f.mem out 8 = some (root (initByte locs) bufs).toNat := by
  intro M hM f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl
  · exact (par_hash hok sc_le_xl hf).2
  · exact (par_hash hok tso_le_xl hf).2
  · exact (par_hash hok (MLe.refl _) hf).2

/-! ## The worker block is zlib's `crc32_z` contract -/

/-- The contract's postcondition, for `crc32_z(0, buf, len)` on a buffer holding `ivs`, is the
worker block's summary for `rax`. -/
theorem leaf_spec_of_post {entry : Silmaril.X86.Word} {s t : Silmaril.X86.MState}
    (hpost : (crc32zContract entry).post s t) (hrdi : s.core.read .rdi = 0)
    (hnz : Silmaril.X86.Stencils.ByteLoop.arg1 s ≠ 0) {ivs : List Nat}
    (hbuf : buf s = toBytes ivs) (b : Nat × Nat) (r : Nat) :
    (leafJob b r).block.spec ivs [(t.core.read .rax).toNat] :=
  Silmaril.Proofs.X86.Concurrency.Cir.ParHash.leaf_spec_of_post hpost hrdi hnz hbuf b r

/-- **The x86 code meets the block summary**: from zlib's unchanged total-correctness theorem,
every entry state of `crc32_z(0, buf, len)` runs to a state whose `rax` the block's contract
allows. -/
theorem leaf_total (entry : Silmaril.X86.Word) {s : Silmaril.X86.MState}
    (hlive : Silmaril.X86.Open.isa.live s)
    (habi : Silmaril.X86.FnContract.AbiEntry (Silmaril.X86.Open.isa.core s)
      (Silmaril.X86.Open.isa.mem s))
    (hentry : (crc32zContract entry).entry s) (hrdi : s.core.read .rdi = 0)
    (hnz : Silmaril.X86.Stencils.ByteLoop.arg1 s ≠ 0) {ivs : List Nat}
    (hbuf : buf s = toBytes ivs) (b : Nat × Nat) (r : Nat) :
    ∃ t, Silmaril.Machine.Execution.Reaches Silmaril.X86.Open.isa.step s t ∧
      (leafJob b r).block.spec ivs [(t.core.read .rax).toNat] := by
  obtain ⟨t, hr, hres⟩ := crc32z_total entry s hlive habi hentry
  exact ⟨t, hr, leaf_spec_of_post hres.post hrdi hnz hbuf b r⟩

/-- **`leaf_total` with no buffer hypothesis**: the block's input values are the
bytes `crc32_z` reads from x86 memory at `(rsi, rdx)`, the block's buffer is that range, and
it has one input value per byte cell. So `hbuf` of `leaf_total` is always satisfiable, and the
CIR block and the x86 call read the same range. -/
theorem leaf_total_at (entry : Silmaril.X86.Word) {s : Silmaril.X86.MState}
    (hlive : Silmaril.X86.Open.isa.live s)
    (habi : Silmaril.X86.FnContract.AbiEntry (Silmaril.X86.Open.isa.core s)
      (Silmaril.X86.Open.isa.mem s))
    (hentry : (crc32zContract entry).entry s) (hrdi : s.core.read .rdi = 0)
    (hnz : Silmaril.X86.Stencils.ByteLoop.arg1 s ≠ 0) (r : Nat) :
    ∃ t, Silmaril.Machine.Execution.Reaches Silmaril.X86.Open.isa.step s t ∧
      (leafJob (Silmaril.X86.Stencils.ByteLoop.arg1 s,
          Silmaril.X86.Stencils.ByteLoop.arg2 s) r).block.spec
        ((buf s).map BitVec.toNat) [(t.core.read .rax).toNat] ∧
      ((buf s).map BitVec.toNat).length =
        (leafJob (Silmaril.X86.Stencils.ByteLoop.arg1 s,
          Silmaril.X86.Stencils.ByteLoop.arg2 s) r).ins.length := by
  have hb : buf s = toBytes ((buf s).map BitVec.toNat) := by
    simp [toBytes, Function.comp_def]
  obtain ⟨t, hr, hs⟩ := leaf_total entry hlive habi hentry hrdi hnz hb _ r
  refine ⟨t, hr, hs, ?_⟩
  simp [leafJob, bufCells, buf, Silmaril.X86.Stencils.TableFold.bytesAt]

/-- **The same under every `SC ⊑ M ⊑ XL`**: the run also reads the same as one thread under
`M`. -/
theorem leaf_total_under (entry : Silmaril.X86.Word) {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl)
    {s : Silmaril.X86.MState} (hlive : Silmaril.X86.Open.isa.live s)
    (habi : Silmaril.X86.FnContract.AbiEntry (Silmaril.X86.Open.isa.core s)
      (Silmaril.X86.Open.isa.mem s))
    (hentry : (crc32zContract entry).entry s) (hrdi : s.core.read .rdi = 0)
    (hnz : Silmaril.X86.Stencils.ByteLoop.arg1 s ≠ 0) {ivs : List Nat}
    (hbuf : buf s = toBytes ivs) (b : Nat × Nat) (r : Nat) :
    ∃ t, Silmaril.Machine.Execution.Reaches Silmaril.X86.Open.isa.step s t ∧
      (leafJob b r).block.spec ivs [(t.core.read .rax).toNat] ∧
      Silmaril.X86.Concurrency.Lift.RunUnder M Silmaril.X86.Open.isa.step
        (fun s => Silmaril.X86.Concurrency.Lift.flat (Silmaril.X86.Open.isa.mem s))
        Silmaril.X86.Concurrency.Lift.openActs s t := by
  obtain ⟨t, hr, hres, hu⟩ :=
    Silmaril.X86.Concurrency.Lift.crc32z_total_under entry hsc hxl s hlive habi hentry
  exact ⟨t, hr, leaf_spec_of_post hres.post hrdi hnz hbuf b r, hu⟩

/-! ## A concrete layout -/

/-- Four 64-byte buffers at `0x10000 + 0x100 k`, initialised to `k + 1` in every byte. -/
def exBufs : List (Nat × Nat) := (List.range 4).map fun k => (0x10000 + 0x100 * k, 64)

/-- The buffers' initial contents, as litmus locations. -/
def exLocs : List Loc :=
  (List.range 4).map fun k =>
    ⟨s!"buf{k}", 0x10000 + 0x100 * k, 64,
      (List.range 64).foldl (fun v j => v + (k + 1) * 256 ^ j) 0⟩

/-- The example program: results at `0x20000`, output at `0x20100`. -/
def ex : Par := par exLocs exBufs 0x20000 0x20100

theorem ex_okB : ex.okB = true := by decide

/-- **The example under every `M ⊑ XL`.** -/
theorem ex_hash {M : Exec → Prop} (hM : M ⊑ Exec.Xl) {f : Final} (h : Behav ex.prog M f) :
    leValue f.mem 0x20100 8 = some (root (initByte exLocs) exBufs).toNat :=
  (par_hash ex_okB hM h).2


/-! ## Non-vacuity -/

theorem tiny_okB : tiny.okB = true := by decide

/-- **The small instance has behaviours under SC, TSO and XL, and every behaviour under every
`M ⊑ XL` ends with the expected hash of hashes.** -/
theorem tiny_behav :
    (∀ M ∈ [Exec.Sc, Exec.Tso, Exec.Xl], ∃ f, Behav tiny.prog M f) ∧
    ∀ {M : Exec → Prop}, M ⊑ Exec.Xl → ∀ f, Behav tiny.prog M f →
      leValue f.mem 0x300 8 = some (root (initByte tinyLocs) tinyBufs).toNat := by
  obtain ⟨f, hf, -⟩ := Silmaril.Proofs.X86.Concurrency.Cir.ParHash.tiny_some
  refine ⟨fun M hM => ?_, fun hM f h => (par_hash tiny_okB hM h).2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl
  · exact ⟨f, hf⟩
  · exact ⟨f, behav_mono sc_le_tso hf⟩
  · exact ⟨f, behav_mono sc_le_xl hf⟩


/-- **The joins are load-bearing**: without them, the small instance has an SC behaviour
(hence TSO and XL ones) whose output is the hash of the initial zero results, not the
expected hash of hashes. -/
theorem tinyNoJoin_stale :
    (∃ f, Behav tinyNoJoin Exec.Sc f ∧ leValue f.mem 0x300 8 = some staleRoot) ∧
      staleRoot ≠ (root (initByte tinyLocs) tinyBufs).toNat :=
  ⟨Silmaril.Proofs.X86.Concurrency.Cir.ParHash.tinyNoJoin_stale,
    Silmaril.Proofs.X86.Concurrency.Cir.ParHash.staleRoot_ne⟩

end Silmaril.X86.Concurrency.Cir.ParHash
