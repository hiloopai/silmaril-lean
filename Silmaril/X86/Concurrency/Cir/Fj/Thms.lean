module

public import Silmaril.X86.Concurrency.Cir.Fj.Defs
public import Silmaril.X86.Concurrency.Cir.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Fj.Main
import Silmaril.Proofs.X86.Concurrency.Cir.Fj.Ok

/-!
# Fork-join CIR: what is proved

All statements are PROVED with the standard axioms. The proofs are in
`Silmaril/Proofs/X86/Concurrency/Cir/Fj/`.

* `Par.ok_of_okB`: the footprint check is sound.
* **`Par.behav_mem`** (the fork-join theorem): for every fork-join program with disjoint
  footprints (`Par.Ok`) and every model `M ⊑ XL` (so SC, TSO, XL, and the synchronising
  variants), every behaviour of the CIR program `F.prog` ends with the **sequential**
  memory `F.seqMem` (the jobs one after another, then the combine) on every data byte.
* `Par.behav_val`: the same for the value of any cell in the data region, as litmus conditions
  read it (`leValue`).
* `Par.safe`, `Par.behav_models`: the same as CIR `Safe` statements.
* `Par.jobsMem_val`, `Par.seqMem_val`: the sequential meaning at an output cell is the job's
  value (when it fits), so `Par.behav_comb` reads a combine output after every behaviour.

The proof uses only XL's `acyclic ghbXl` and `Exec.Wf`: a combine load of a worker's output
byte that took the initial byte closes the cycle
`load -fr-> worker store -lock-> worker end -rfe-> join -lock-> load`, and every other byte
has exactly one writer up to equal bytes. Nothing about the jobs is used except their
contracts `outs = fn ins`: a job's sequential proof is reused unchanged.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Fj

open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (leValue)

/-- The footprint check is sound. -/
theorem Par.ok_of_okB {F : Par} (h : F.okB = true) : F.Ok :=
  Silmaril.Proofs.X86.Concurrency.Cir.Fj.ok_of_okB h

/-- **The fork-join theorem.** Under every model `M ⊑ XL`, every behaviour of a fork-join
program with disjoint footprints ends with the sequential memory on every data byte. -/
theorem Par.behav_mem (F : Par) (hok : F.Ok) {M : Exec → Prop} (hM : M ⊑ Exec.Xl)
    {f : Silmaril.X86.MemoryModel.Litmus.Final} (h : Behav F.prog M f) :
    ∀ y < dataTop, f.mem y = F.seqMem y :=
  Silmaril.Proofs.X86.Concurrency.Cir.Fj.behav_mem F hok hM h

theorem leValue_congr {m m' : Nat → Option Silmaril.X86.MemoryModel.Litmus.Byte} :
    ∀ (n a : Nat), (∀ y, a ≤ y → y < a + n → m y = m' y) → leValue m a n = leValue m' a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [leValue]
    rw [h a (le_refl _) (by omega),
      leValue_congr n (a + 1) fun y h1 h2 => h y (by omega) (by omega)]

/-- **The value of any data cell** after every behaviour under `M ⊑ XL` is its sequential
value. -/
theorem Par.behav_val (F : Par) (hok : F.Ok) {M : Exec → Prop} (hM : M ⊑ Exec.Xl)
    {f : Silmaril.X86.MemoryModel.Litmus.Final} (h : Behav F.prog M f) {a n : Nat}
    (ha : a + n ≤ dataTop) : leValue f.mem a n = leValue F.seqMem a n :=
  leValue_congr n a fun y _ h2 => F.behav_mem hok hM h y (by omega)

/-- `Par.behav_mem` as a CIR safety statement. -/
theorem Par.safe (F : Par) (hok : F.Ok) {M : Exec → Prop} (hM : M ⊑ Exec.Xl) :
    Safe F.prog M fun f => ∀ y < dataTop, f.mem y = F.seqMem y :=
  fun _ h => F.behav_mem hok hM h

/-- The fork-join theorem under SC, x86-TSO and XL. -/
theorem Par.behav_models (F : Par) (hok : F.Ok) :
    Safe F.prog Exec.Sc (fun f => ∀ y < dataTop, f.mem y = F.seqMem y) ∧
      Safe F.prog Exec.Tso (fun f => ∀ y < dataTop, f.mem y = F.seqMem y) ∧
      Safe F.prog Exec.Xl (fun f => ∀ y < dataTop, f.mem y = F.seqMem y) :=
  ⟨F.safe hok sc_le_xl, F.safe hok tso_le_xl, F.safe hok (MLe.refl _)⟩


/-- The value of a worker's output cell after the jobs: its job's value on the initial
memory. -/
theorem Par.jobsMem_val {F : Par} (hok : F.Ok) {j : Job} (hj : j ∈ F.jobs) {a sz v : Nat}
    (hc : (a, sz, v) ∈ cellVals j.outs (j.fn (j.ins.map (cellVal F.init))))
    (hv : v < 2 ^ (8 * sz)) :
    leValue F.jobsMem a sz = some v ∧ cellVal F.jobsMem (a, sz) = v :=
  Silmaril.Proofs.X86.Concurrency.Cir.Fj.jobsMem_val hok hj hc hv

/-- The value of a combine output cell in the sequential meaning. -/
theorem Par.seqMem_val {F : Par} (hok : F.Ok) {a sz v : Nat}
    (hc : (a, sz, v) ∈ cellVals F.comb.outs (F.comb.fn (F.comb.ins.map (cellVal F.jobsMem))))
    (hv : v < 2 ^ (8 * sz)) : leValue F.seqMem a sz = some v ∧ cellVal F.seqMem (a, sz) = v :=
  Silmaril.Proofs.X86.Concurrency.Cir.Fj.seqMem_val hok hc hv

/-- **A combine output after every behaviour under `M ⊑ XL`**: its sequential value. -/
theorem Par.behav_comb (F : Par) (hok : F.Ok) {M : Exec → Prop} (hM : M ⊑ Exec.Xl)
    {f : Silmaril.X86.MemoryModel.Litmus.Final} (h : Behav F.prog M f) {a sz v : Nat}
    (hc : (a, sz, v) ∈ cellVals F.comb.outs (F.comb.fn (F.comb.ins.map (cellVal F.jobsMem))))
    (hv : v < 2 ^ (8 * sz)) (hlow : a + sz ≤ dataTop) : leValue f.mem a sz = some v := by
  rw [F.behav_val hok hM h hlow]; exact (Par.seqMem_val hok hc hv).1


/-- **A worker output after every behaviour under `M ⊑ XL`**: its job's value on the initial
memory. -/
theorem Par.behav_job (F : Par) (hok : F.Ok) {M : Exec → Prop} (hM : M ⊑ Exec.Xl)
    {f : Silmaril.X86.MemoryModel.Litmus.Final} (h : Behav F.prog M f) {j : Job} (hj : j ∈ F.jobs)
    {a sz v : Nat} (hc : (a, sz, v) ∈ cellVals j.outs (j.fn (j.ins.map (cellVal F.init))))
    (hv : v < 2 ^ (8 * sz)) (hlow : a + sz ≤ dataTop) : leValue f.mem a sz = some v := by
  rw [F.behav_val hok hM h hlow]
  exact Silmaril.Proofs.X86.Concurrency.Cir.Fj.seqMem_job_val hok hj hc hv

end Silmaril.X86.Concurrency.Cir.Fj
