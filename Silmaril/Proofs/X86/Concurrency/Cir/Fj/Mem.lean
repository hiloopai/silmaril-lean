module

public import Silmaril.X86.Concurrency.Cir.Fj.Defs

/-!
# Fork-join CIR: flat-memory facts

Values as bytes (`cellVal_of_bytes`), writes of disjoint cells
(`putAll_in`, `putAll_out`), and the sequential meaning of a fork-join program byte by byte
(`jobsMem_in`, `jobsMem_out`, `seqMem_in`, `seqMem_out`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Fj

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Fj
open Silmaril.X86.MemoryModel.Litmus (Byte leValue)

/-! ## Values and bytes -/

/-- Byte `k` of the `sz`-byte little-endian value `v`. -/
def byteOf (v k : Nat) : Byte := BitVec.ofNat 8 (v / 256 ^ k)

theorem natBytes_getD {v sz k : Nat} (hk : k < sz) : (natBytes v sz).getD k 0 = byteOf v k := by
  simp [natBytes, List.getD, hk, byteOf]

theorem natBytes_length (v sz : Nat) : (natBytes v sz).length = sz := by simp [natBytes]

/-- A value that fits is determined by its bytes. -/
theorem val_of_bytes (m : Mem) : ∀ (sz a v : Nat), v < 2 ^ (8 * sz) →
    (∀ k < sz, byteOf v k = (m (a + k)).getD 0) → m.val a sz = some v
  | 0, a, v, hv, _ => by simp [Mem.val, leValue] at hv ⊢; omega
  | sz + 1, a, v, hv, h => by
    have h0 := h 0 (by omega)
    have ih := val_of_bytes m sz (a + 1) (v / 256) (by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc v < 2 ^ (8 * (sz + 1)) := hv
        _ = 2 ^ (8 * sz) * 256 := by rw [Nat.mul_succ, Nat.pow_add])
      (fun k hk => by
        have := h (k + 1) (by omega)
        simp only [byteOf, Nat.pow_succ, Nat.div_div_eq_div_mul] at this ⊢
        rw [show a + 1 + k = a + (k + 1) by omega, ← this, Nat.mul_comm 256])
    simp only [Mem.val, leValue] at ih ⊢
    rw [ih]
    simp only [byteOf, Nat.pow_zero, Nat.div_one, Nat.add_zero] at h0
    rw [← h0]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, BitVec.toNat_ofNat]
    congr 1
    omega

theorem cellVal_of_bytes {m : Mem} {a sz v : Nat} (hv : v < 2 ^ (8 * sz))
    (h : ∀ k < sz, byteOf v k = (m (a + k)).getD 0) : cellVal m (a, sz) = v := by
  simp [cellVal, val_of_bytes m sz a v hv h]

theorem val_congr {m m' : Mem} : ∀ (sz a : Nat), (∀ y, a ≤ y → y < a + sz → m y = m' y) →
    m.val a sz = m'.val a sz
  | 0, _, _ => rfl
  | sz + 1, a, h => by
    have ih := val_congr sz (a + 1) fun y h1 h2 => h y (by omega) (by omega)
    simp only [Mem.val, leValue] at ih ⊢
    rw [ih, h a (le_refl _) (by omega)]

theorem cellVal_congr {m m' : Mem} {c : Nat × Nat} (h : ∀ y, Cell.has c y → m y = m' y) :
    cellVal m c = cellVal m' c := by
  simp only [cellVal]; rw [val_congr c.2 c.1 fun y h1 h2 => h y ⟨h1, h2⟩]

/-! ## Writes -/

theorem put_in {m : Mem} {a sz v y : Nat} (h : Cell.has (a, sz) y) :
    m.put a sz v y = some (byteOf v (y - a)) := by
  simp [Mem.put, Cell.has] at h ⊢; simp [h.1, h.2, byteOf]

theorem put_out {m : Mem} {a sz v y : Nat} (h : ¬ Cell.has (a, sz) y) : m.put a sz v y = m y := by
  simp only [Cell.has] at h; simp [Mem.put, h]

theorem disjB_iff {c d : Nat × Nat} (h : Cell.disjB c d = true) :
    ∀ y, ¬ (Cell.has c y ∧ Cell.has d y) := by
  simp only [Cell.disjB, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Cell.has]
  rintro y ⟨⟨h1, h2⟩, h3, h4⟩
  omega

/-- The cell of a cell-value triple. -/
def cellOf (c : Nat × Nat × Nat) : Nat × Nat := (c.1, c.2.1)

theorem putAll_out {y : Nat} : ∀ {m : Mem} {l : List (Nat × Nat × Nat)},
    (∀ c ∈ l, ¬ Cell.has (cellOf c) y) → putAll m l y = m y
  | _, [], _ => rfl
  | m, c :: l, h => by
    simp only [putAll, List.foldl_cons] at h ⊢
    rw [show List.foldl _ _ l = putAll (m.put c.1 c.2.1 c.2.2) l from rfl,
      putAll_out fun d hd => h d (List.mem_cons_of_mem _ hd), put_out (h c List.mem_cons_self)]

theorem putAll_in {y : Nat} : ∀ {m : Mem} {l : List (Nat × Nat × Nat)},
    (l.map cellOf).Pairwise (fun c d => Cell.disjB c d) →
    ∀ c ∈ l, Cell.has (cellOf c) y → putAll m l y = some (byteOf c.2.2 (y - c.1))
  | _, [], _, _, h, _ => by simp at h
  | m, d :: l, hp, c, hc, hy => by
    simp only [List.map_cons, List.pairwise_cons] at hp
    show putAll (m.put d.1 d.2.1 d.2.2) l y = _
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [putAll_out fun e he hey => (disjB_iff (hp.1 _ (List.mem_map_of_mem he))) y ⟨hy, hey⟩]
      exact put_in hy
    · exact putAll_in hp.2 c hc hy

theorem mem_cellVals {cs : List (Nat × Nat)} {vs : List Nat} {c : Nat × Nat × Nat}
    (h : c ∈ cellVals cs vs) : cellOf c ∈ cs := by
  induction cs generalizing vs with
  | nil => cases vs <;> simp [cellVals] at h
  | cons d cs ih =>
    cases vs with
    | nil => simp [cellVals] at h
    | cons v vs =>
      simp only [cellVals, List.mem_cons] at h
      rcases h with rfl | h
      · simp [cellOf]
      · exact List.mem_cons_of_mem _ (ih h)

theorem cellVals_sublist (cs : List (Nat × Nat)) (vs : List Nat) :
    ((cellVals cs vs).map cellOf).Sublist cs := by
  induction cs generalizing vs with
  | nil => cases vs <;> simp [cellVals]
  | cons d cs ih =>
    cases vs with
    | nil => simp [cellVals]
    | cons v vs => simpa [cellVals, cellOf] using (ih vs).cons_cons d

theorem run_out {j : Job} {m : Mem} {y : Nat}
    (h : ∀ d ∈ j.outs, ¬ Cell.has d y) : j.run m y = m y :=
  putAll_out fun _ hc => h _ (mem_cellVals hc)

theorem run_in {j : Job} {m : Mem} {y : Nat} (hp : j.outs.Pairwise fun c d => Cell.disjB c d)
    {c : Nat × Nat × Nat} (hc : c ∈ cellVals j.outs (j.fn (j.ins.map (cellVal m))))
    (hy : Cell.has (cellOf c) y) : j.run m y = some (byteOf c.2.2 (y - c.1)) :=
  putAll_in (hp.sublist (cellVals_sublist _ _)) c hc hy

/-! ## The sequential meaning, byte by byte -/

/-- The worker jobs' inputs read the initial memory. -/
def InsInit (m0 : Mem) (J : List Job) (m : Mem) : Prop :=
  ∀ j ∈ J, ∀ c ∈ j.ins, ∀ y, Cell.has c y → m y = m0 y

theorem pairwise_flatMap_cons {j : Job} {J : List Job}
    (h : ((j :: J).flatMap Job.outs).Pairwise fun c d => Cell.disjB c d) :
    j.outs.Pairwise (fun c d => Cell.disjB c d) ∧
      (J.flatMap Job.outs).Pairwise (fun c d => Cell.disjB c d) ∧
      ∀ c ∈ j.outs, ∀ k ∈ J, ∀ d ∈ k.outs, Cell.disjB c d := by
  simp only [List.flatMap_cons, List.pairwise_append, List.mem_flatMap] at h
  exact ⟨h.1, h.2.1, fun c hc k hk d hd => h.2.2 c hc d ⟨k, hk, hd⟩⟩

/-- **A job's output byte**: the jobs run in order; a byte of an output cell of job `j` ends
with `j`'s value computed from the initial memory. -/
theorem fold_in {m0 : Mem} {y : Nat} : ∀ {J : List Job} {m : Mem},
    (J.flatMap Job.outs).Pairwise (fun c d => Cell.disjB c d) →
    (∀ j ∈ J, ∀ c ∈ j.ins, ∀ k ∈ J, ∀ d ∈ k.outs, Cell.disjB c d) → InsInit m0 J m →
    ∀ j ∈ J, ∀ c ∈ cellVals j.outs (j.fn (j.ins.map (cellVal m0))), Cell.has (cellOf c) y →
      J.foldl (fun m j => j.run m) m y = some (byteOf c.2.2 (y - c.1))
  | [], _, _, _, _, j, hj, _, _, _ => by simp at hj
  | j' :: J, m, hp, hins, hm, j, hj, c, hc, hy => by
    obtain ⟨hp1, hp2, hp3⟩ := pairwise_flatMap_cons hp
    simp only [List.foldl_cons]
    have hm' : InsInit m0 J (j'.run m) := by
      intro k hk d hd z hz
      rw [run_out fun e he hez => (disjB_iff (hins k (List.mem_cons_of_mem _ hk) d hd j'
        List.mem_cons_self e he)) z ⟨hz, hez⟩]
      exact hm k (List.mem_cons_of_mem _ hk) d hd z hz
    have hins' : ∀ j ∈ J, ∀ c ∈ j.ins, ∀ k ∈ J, ∀ d ∈ k.outs, Cell.disjB c d :=
      fun j hj c hc k hk d hd =>
        hins j (List.mem_cons_of_mem _ hj) c hc k (List.mem_cons_of_mem _ hk) d hd
    rcases List.mem_cons.mp hj with rfl | hj
    · -- `y` is an output byte of the first job: later jobs do not touch it
      have hv : j.ins.map (cellVal m) = j.ins.map (cellVal m0) :=
        List.map_congr_left fun d hd => cellVal_congr fun z hz => hm j List.mem_cons_self d hd z hz
      rw [← hv] at hc
      have hrun := run_in hp1 hc hy
      suffices H : ∀ (K : List Job) (m' : Mem), (∀ k ∈ K, ∀ d ∈ k.outs, ¬ Cell.has d y) →
          K.foldl (fun m j => j.run m) m' y = m' y by
        rw [H J _ fun k hk d hd hdy => (disjB_iff (hp3 _ (mem_cellVals hc) k hk d hd)) y ⟨hy, hdy⟩]
        exact hrun
      intro K
      induction K with
      | nil => intro _ _; rfl
      | cons k K ih =>
        intro m' hK
        simp only [List.foldl_cons]
        rw [ih _ fun k' hk' => hK k' (List.mem_cons_of_mem _ hk'),
          run_out (hK k List.mem_cons_self)]
    · exact fold_in hp2 hins' hm' j hj c hc hy

/-- A byte no job writes keeps its value. -/
theorem fold_out {y : Nat} : ∀ {J : List Job} {m : Mem},
    (∀ j ∈ J, ∀ d ∈ j.outs, ¬ Cell.has d y) → J.foldl (fun m j => j.run m) m y = m y
  | [], _, _ => rfl
  | j :: J, m, h => by
    simp only [List.foldl_cons]
    rw [fold_out fun k hk => h k (List.mem_cons_of_mem _ hk), run_out (h j List.mem_cons_self)]

/-- The worker jobs' inputs are unchanged by the jobs: every job reads the initial memory. -/
theorem jobsMem_ins {F : Par} (hok : F.Ok) {j : Job} (hj : j ∈ F.jobs) {c : Nat × Nat}
    (hc : c ∈ j.ins) : cellVal F.jobsMem c = cellVal F.init c :=
  cellVal_congr fun y hy => fold_out fun k hk d hd hdy =>
    (disjB_iff (hok.insFree j hj c hc k (List.mem_append_left _ hk) d hd)) y ⟨hy, hdy⟩

theorem outsDisj_jobs {F : Par} (hok : F.Ok) :
    (F.jobs.flatMap Job.outs).Pairwise fun c d => Cell.disjB c d := by
  have := hok.outsDisj
  simp only [List.flatMap_append, List.pairwise_append] at this
  exact this.1

theorem jobsMem_in {F : Par} (hok : F.Ok) {j : Job} (hj : j ∈ F.jobs) {c : Nat × Nat × Nat}
    (hc : c ∈ cellVals j.outs (j.fn (j.ins.map (cellVal F.init)))) {y : Nat}
    (hy : Cell.has (cellOf c) y) : F.jobsMem y = some (byteOf c.2.2 (y - c.1)) :=
  fold_in (outsDisj_jobs hok)
    (fun j hj c hc k hk d hd => hok.insFree j hj c hc k (List.mem_append_left _ hk) d hd)
    (fun _ _ _ _ _ _ => rfl) j hj c hc hy

theorem jobsMem_out {F : Par} {y : Nat} (h : ∀ j ∈ F.jobs, ∀ d ∈ j.outs, ¬ Cell.has d y) :
    F.jobsMem y = F.init y := fold_out h

theorem comb_pairwise {F : Par} (hok : F.Ok) : F.comb.outs.Pairwise fun c d => Cell.disjB c d := by
  have := hok.outsDisj
  simp only [List.flatMap_append, List.pairwise_append] at this
  simpa using this.2.1

/-- Every worker output cell is disjoint from every combine output cell. -/
theorem jobs_comb_disj {F : Par} (hok : F.Ok) {j : Job} (hj : j ∈ F.jobs) {c d : Nat × Nat}
    (hc : c ∈ j.outs) (hd : d ∈ F.comb.outs) : Cell.disjB c d := by
  have := hok.outsDisj
  simp only [List.flatMap_append, List.pairwise_append] at this
  exact this.2.2 c (List.mem_flatMap.mpr ⟨j, hj, hc⟩) d (by simpa using hd)

theorem seqMem_in {F : Par} (hok : F.Ok) {c : Nat × Nat × Nat}
    (hc : c ∈ cellVals F.comb.outs (F.comb.fn (F.comb.ins.map (cellVal F.jobsMem)))) {y : Nat}
    (hy : Cell.has (cellOf c) y) : F.seqMem y = some (byteOf c.2.2 (y - c.1)) :=
  run_in (comb_pairwise hok) hc hy

theorem seqMem_out {F : Par} {y : Nat} (h : ∀ d ∈ F.comb.outs, ¬ Cell.has d y) :
    F.seqMem y = F.jobsMem y := run_out h


/-! ## Values of output cells -/

theorem leValue_of_bytes {m : Nat → Option Byte} : ∀ (sz a v : Nat), v < 2 ^ (8 * sz) →
    (∀ k < sz, m (a + k) = some (byteOf v k)) → leValue m a sz = some v
  | 0, a, v, hv, _ => by simp [leValue] at hv ⊢; omega
  | sz + 1, a, v, hv, h => by
    have h0 := h 0 (by omega)
    have ih := leValue_of_bytes (m := m) sz (a + 1) (v / 256) (by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc v < 2 ^ (8 * (sz + 1)) := hv
        _ = 2 ^ (8 * sz) * 256 := by rw [Nat.mul_succ, Nat.pow_add])
      (fun k hk => by
        have := h (k + 1) (by omega)
        rw [show a + 1 + k = a + (k + 1) by omega, this]
        simp only [byteOf, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm 256])
    simp only [leValue, Nat.add_zero] at h0 ⊢
    rw [h0, ih]
    simp only [byteOf, Nat.pow_zero, Nat.div_one, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, BitVec.toNat_ofNat, Option.some.injEq]
    omega

/-- A memory whose bytes at a cell are those of `v` has value `v` there, in both readings. -/
theorem cell_of_bytes {m : Mem} {a sz v : Nat} (hv : v < 2 ^ (8 * sz))
    (h : ∀ y, Cell.has (a, sz) y → m y = some (byteOf v (y - a))) :
    leValue m a sz = some v ∧ cellVal m (a, sz) = v := by
  have hb : ∀ k < sz, m (a + k) = some (byteOf v k) := fun k hk => by
    rw [h (a + k) (by simp [Cell.has]; omega), Nat.add_sub_cancel_left]
  refine ⟨leValue_of_bytes sz a v hv hb, ?_⟩
  simp only [cellVal, Mem.val]
  rw [leValue_of_bytes sz a v hv fun k hk => by rw [hb k hk]; rfl]
  rfl

theorem jobsMem_val {F : Par} (hok : F.Ok) {j : Job} (hj : j ∈ F.jobs) {c : Nat × Nat × Nat}
    (hc : c ∈ cellVals j.outs (j.fn (j.ins.map (cellVal F.init)))) (hv : c.2.2 < 2 ^ (8 * c.2.1)) :
    leValue F.jobsMem c.1 c.2.1 = some c.2.2 ∧ cellVal F.jobsMem (cellOf c) = c.2.2 :=
  cell_of_bytes hv fun _ hy => jobsMem_in hok hj hc hy

theorem seqMem_val {F : Par} (hok : F.Ok) {c : Nat × Nat × Nat}
    (hc : c ∈ cellVals F.comb.outs (F.comb.fn (F.comb.ins.map (cellVal F.jobsMem))))
    (hv : c.2.2 < 2 ^ (8 * c.2.1)) :
    leValue F.seqMem c.1 c.2.1 = some c.2.2 ∧ cellVal F.seqMem (cellOf c) = c.2.2 :=
  cell_of_bytes hv fun _ hy => seqMem_in hok hc hy


theorem seqMem_job_val {F : Par} (hok : F.Ok) {j : Job} (hj : j ∈ F.jobs) {c : Nat × Nat × Nat}
    (hc : c ∈ cellVals j.outs (j.fn (j.ins.map (cellVal F.init)))) (hv : c.2.2 < 2 ^ (8 * c.2.1)) :
    leValue F.seqMem c.1 c.2.1 = some c.2.2 :=
  (cell_of_bytes hv fun y hy => by
    rw [seqMem_out fun d hd hdy =>
      disjB_iff (jobs_comb_disj hok hj (mem_cellVals hc) hd) y ⟨hy, hdy⟩]
    exact jobsMem_in hok hj hc hy).1

end Silmaril.Proofs.X86.Concurrency.Cir.Fj
