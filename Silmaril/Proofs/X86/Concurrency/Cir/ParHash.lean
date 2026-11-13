module

public import Silmaril.X86.Concurrency.Cir.ParHash.Defs
public import Silmaril.X86.Concurrency.Cir.Fj.Thms
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms

/-!
# Parallel hashing on CIR: proofs

The instance of the fork-join theorem: the values of the result
cells and of the output after every behaviour under `M ⊑ XL`. Nothing here mentions a memory
model or a candidate execution; it is list bookkeeping about `ParHash.par`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.ParHash

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Fj
open Silmaril.X86.Concurrency.Cir.ParHash
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (leValue initByte Loc Final)

theorem cellVal_byte (m : Mem) (a : Nat) : cellVal m (a, 1) = ((m a).getD 0).toNat := by
  simp [cellVal, Mem.val, leValue]

theorem toBytes_buf (m : Mem) (b : Nat × Nat) :
    toBytes ((bufCells b).map (cellVal m)) = memBytes m b := by
  simp [toBytes, bufCells, memBytes, cellVal_byte]

theorem crc_lt (c : BitVec 32) : c.toNat < 2 ^ (8 * 8) :=
  lt_of_lt_of_le c.isLt (by decide)

theorem jobs_len (locs : List Loc) (bufs : List (Nat × Nat)) (res out : Nat) :
    (par locs bufs res out).jobs.length = bufs.length := by
  simp [par]

theorem job_get {locs : List Loc} {bufs : List (Nat × Nat)} {res out i : Nat}
    (hi : i < (par locs bufs res out).jobs.length) :
    (par locs bufs res out).jobs[i] =
      leafJob (bufs[i]'(by simpa [par] using hi)) (res + 8 * i) := by
  simp [par]

/-- A worker's output triple in the sequential meaning. -/
theorem leaf_mem {locs : List Loc} {bufs : List (Nat × Nat)} {res out i : Nat}
    (hi : i < (par locs bufs res out).jobs.length) :
    (res + 8 * i, 8, (leaf (initByte locs) (bufs[i]'(by simpa [par] using hi))).toNat) ∈
      cellVals (par locs bufs res out).jobs[i].outs ((par locs bufs res out).jobs[i].fn
        ((par locs bufs res out).jobs[i].ins.map (cellVal (par locs bufs res out).init))) := by
  rw [job_get hi]
  simp only [leafJob, crcFn, toBytes_buf, cellVals, List.mem_singleton]
  rfl

theorem leaf_cellVal {locs : List Loc} {bufs : List (Nat × Nat)} {res out : Nat}
    (hok : (par locs bufs res out).Ok) {i : Nat} (hi : i < (par locs bufs res out).jobs.length) :
    cellVal (par locs bufs res out).jobsMem (res + 8 * i, 8) =
      (leaf (initByte locs) (bufs[i]'(by simpa [par] using hi))).toNat :=
  (Par.jobsMem_val hok (List.getElem_mem hi) (leaf_mem hi) (crc_lt _)).2

theorem res_vals {locs : List Loc} {bufs : List (Nat × Nat)} {res out : Nat}
    (hok : (par locs bufs res out).Ok) :
    (resCells res bufs.length).map (cellVal (par locs bufs res out).jobsMem) =
      bufs.map fun b => (leaf (initByte locs) b).toNat := by
  apply List.ext_getElem (by simp [resCells])
  intro i h1 h2
  simp only [resCells, List.getElem_map, List.getElem_range]
  exact leaf_cellVal hok (i := i) (by simpa [par, resCells] using h1)

theorem root_mem {locs : List Loc} {bufs : List (Nat × Nat)} {res out : Nat}
    (hok : (par locs bufs res out).Ok) :
    (out, 8, (root (initByte locs) bufs).toNat) ∈
      cellVals (par locs bufs res out).comb.outs ((par locs bufs res out).comb.fn
        ((par locs bufs res out).comb.ins.map (cellVal (par locs bufs res out).jobsMem))) := by
  have h := res_vals hok
  simp only [par, rootJob] at h ⊢
  simp only [h, rootFn, cellVals, List.flatMap_map, List.mem_singleton]
  rfl

/-- **Every worker's result** after every behaviour under `M ⊑ XL`. -/
theorem behav_leaf {locs : List Loc} {bufs : List (Nat × Nat)} {res out : Nat}
    (hok : (par locs bufs res out).Ok) {M : Exec → Prop} (hM : M ⊑ Exec.Xl)
    {f : Final} (h : Behav (par locs bufs res out).prog M f) (i : Nat)
    (hi : i < bufs.length) :
    leValue f.mem (res + 8 * i) 8 = some (leaf (initByte locs) bufs[i]).toNat := by
  have hi' : i < (par locs bufs res out).jobs.length := by simpa [par] using hi
  have hlow := hok.jobsLow _ (List.getElem_mem hi') (res + 8 * i, 8)
    (by rw [job_get hi']; simp [leafJob])
  exact Par.behav_job _ hok hM h (List.getElem_mem hi') (leaf_mem hi') (crc_lt _) hlow

/-- **The hash of the hashes** after every behaviour under `M ⊑ XL`. -/
theorem behav_root {locs : List Loc} {bufs : List (Nat × Nat)} {res out : Nat}
    (hok : (par locs bufs res out).Ok) {M : Exec → Prop} (hM : M ⊑ Exec.Xl)
    {f : Final} (h : Behav (par locs bufs res out).prog M f) :
    leValue f.mem out 8 = some (root (initByte locs) bufs).toNat :=
  Par.behav_comb _ hok hM h (root_mem hok) (crc_lt _)
    (hok.combLow (out, 8) (by simp [par, rootJob]))


/-! ## The block summary is the x86 contract -/

open Silmaril.X86.Ladder.ZlibChecksums (crc32zContract buf) in
/-- The postcondition of zlib's `crc32_z` contract, called as `crc32_z(0, buf, len)` on a
buffer holding `ivs`, is the worker block's summary for the value in `rax`. -/
theorem leaf_spec_of_post {entry : Silmaril.X86.Word} {s t : Silmaril.X86.MState}
    (hpost : (crc32zContract entry).post s t) (hrdi : s.core.read .rdi = 0)
    (hnz : Silmaril.X86.Stencils.ByteLoop.arg1 s ≠ 0) {ivs : List Nat}
    (hbuf : buf s = toBytes ivs)
    (b : Nat × Nat) (r : Nat) : (leafJob b r).block.spec ivs [(t.core.read .rax).toNat] := by
  simp only [crc32zContract] at hpost
  simp only [Job.block, leafJob, crcFn, List.cons.injEq, and_true]
  rw [hpost, hrdi, ← hbuf]
  simp only [hnz, ↓reduceIte, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (BitVec.isLt _) (by decide))


/-! ## Non-vacuity: the small instance has an SC behaviour -/

open Silmaril.X86.MemoryModel.Litmus (outsBy Model axJudge_spec AxReach)

/-- The enumerator on the small instance: exactly one SC outcome, the expected output. -/
theorem tiny_check :
    (tinyTest.axJudge (tiny.prog.traces tinyDom)).map (fun js => outsBy js Model.sc.sel) =
    some [[some (root (initByte tinyLocs) tinyBufs).toNat]] := by
  decide +kernel

/-- **The small instance has an SC behaviour**, with the expected output. -/
theorem tiny_some : ∃ f, Behav tiny.prog Exec.Sc f ∧
    leValue f.mem 0x300 8 = some (root (initByte tinyLocs) tinyBufs).toNat := by
  have h := tiny_check
  cases hjs : tinyTest.axJudge (tiny.prog.traces tinyDom) with
  | none => rw [hjs] at h; cases h
  | some js =>
    rw [hjs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have ho : [some (root (initByte tinyLocs) tinyBufs).toNat] ∈ outsBy js Model.sc.sel := by
      rw [h]; exact List.mem_singleton_self _
    obtain ⟨f, hf, hfo⟩ := (axJudge_spec hjs Model.sc _).mp ho
    refine ⟨f, ⟨tinyDom, hf⟩, ?_⟩
    have hk : tinyTest.keys = [.mem 0x300 8] := rfl
    rw [Silmaril.X86.MemoryModel.Litmus.Test.outcome, hk] at hfo
    simpa [Silmaril.X86.MemoryModel.Litmus.Key.eval] using hfo


/-! ## The joins are load-bearing -/

/-- The enumerator on the no-join mutant: some SC outcome has the stale output. -/
theorem tinyNoJoin_check :
    ((tinyNoJoinTest.axJudge (tinyNoJoin.traces tinyNoJoinDom)).map fun js =>
      (outsBy js Model.sc.sel).contains [some staleRoot]) = some true := by
  decide +kernel

/-- **Without the joins, the combine can hash the initial (zero) results** under SC. -/
theorem tinyNoJoin_stale :
    ∃ f, Behav tinyNoJoin Exec.Sc f ∧ leValue f.mem 0x300 8 = some staleRoot := by
  have h := tinyNoJoin_check
  cases hjs : tinyNoJoinTest.axJudge (tinyNoJoin.traces tinyNoJoinDom) with
  | none => rw [hjs] at h; cases h
  | some js =>
    rw [hjs] at h
    simp only [Option.map_some, Option.some.injEq, List.contains_iff_mem] at h
    obtain ⟨f, hf, hfo⟩ := (axJudge_spec hjs Model.sc _).mp h
    refine ⟨f, ⟨tinyNoJoinDom, hf⟩, ?_⟩
    have hk : tinyNoJoinTest.keys = [.mem 0x300 8] := rfl
    rw [Silmaril.X86.MemoryModel.Litmus.Test.outcome, hk] at hfo
    simpa [Silmaril.X86.MemoryModel.Litmus.Key.eval] using hfo

theorem staleRoot_ne : staleRoot ≠ (root (initByte tinyLocs) tinyBufs).toNat := by
  decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.ParHash
