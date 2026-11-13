module

public import Silmaril.X86.Concurrency.Cir.Seq.Tv.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Thms
public import Silmaril.X86.Concurrency.Cir.Tv.Thms

/-!
# The single-threaded lift through translation validation: proofs

* `TvTest.solo_sound`: for a validated **one-thread** test whose CIR thread is thread-free with
  positive sizes, every x86 behaviour of the bytes under `M ⊑ XL` has the witness value of a
  sequential run of the CIR thread;
* `ownWrite_ok` (one `decide +kernel`): `ownWriteTv`'s certificate checks against the bytes, the
  domain fits, and the bytes extract;
* `ownWrite_eax`: under every `M ⊑ XL`, the x86 bytes of `ownWrite` end with `eax = 1`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Seq.Tv

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.Concurrency.Cir.Seq Silmaril.X86.Concurrency.Cir.Seq.Tv
open Silmaril.X86.MemoryModel.Litmus (Test Final AxReach XTrace initByte)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

theorem prog_solo {c : TvTest} {ct : Cert} (hc : c.certs = [ct]) :
    c.prog = solo c.test.locs ct.body := by
  simp [TvTest.prog, solo, hc]

/-- **One validated x86 thread is sequential under `M ⊑ XL`.** -/
theorem TvTest.solo_sound {c : TvTest} {ct : Cert} (hc : c.certs = [ct]) (h : c.tvOk = true)
    (hd : c.domOk = true) (ht : ct.body.threadFree = true) (hp : ct.body.posSizes = true)
    {T : List (List XTrace)} (hT : c.test.traces = some T) {M : Exec → Prop} (hxl : M ⊑ Exec.Xl)
    {f : Final} (hf : AxReach c.test T M f) :
    ∃ tr rs m, SeqRun ct.body Regs.zero (initByte c.test.locs) tr rs m ∧
      c.test.witness.eval (soloFinal rs m) = c.test.witness.eval f := by
  obtain ⟨f', hf', hw⟩ := Silmaril.X86.Concurrency.Cir.Tv.TvTest.refines h hd hT hf
  rw [prog_solo hc] at hf'
  obtain ⟨tr, rs, m, hr, rfl⟩ := solo_behav_sound c.test.locs ct.body ht hp hxl ⟨_, hf'⟩
  exact ⟨tr, rs, m, hr, hw⟩

set_option maxRecDepth 4096 in
/-- `ownWriteTv` checks: certificate, domain and extraction. -/
theorem ownWrite_ok : ownWriteTv.tvOk = true ∧ ownWriteTv.domOk = true ∧
    ownWriteTv.test.traces.isSome = true := by decide +kernel

/-- The cell after the store holds `1`. -/
theorem ownWrite_val : (Mem.put (initByte ownWrite.locs) 0x10000 4 1).val 0x10000 4 = some 1 := by
  decide

/-- Every sequential run of `ownWrite`'s CIR thread ends with `rax = 1`. -/
theorem ownWrite_seq {tr : List Lab} {rs : Regs} {m : Mem}
    (h : SeqRun (ownWriteTv.certs.getD 0 ⟨[], []⟩).body Regs.zero (initByte ownWrite.locs) tr rs m) :
    rs .rax = 1 := by
  obtain ⟨⟨dom, hrun⟩, hrep⟩ := h
  simp only [ownWriteTv, List.getD_cons_zero, Cert.body, Cert.ops, Cert.proOps, chain,
    List.map_nil, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append] at hrun
  simp only [run, Res.bind, List.mem_flatMap, List.mem_map, List.mem_singleton] at hrun
  obtain ⟨a, rfl, b, ⟨c, ⟨v, -, rfl⟩, d, rfl, rfl⟩, he⟩ := hrun
  simp only [Prod.mk.injEq, List.append_nil, List.singleton_append] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [replay, Lab.replay, Option.bind_some] at hrep
  have h1 : (BitVec.ofNat 64 1).toNat % 2 ^ (8 * 4) = 1 := by decide
  have e : (BitVec.ofNat 64 65536).toNat = 0x10000 := by decide
  simp only [Expr.eval, h1, e, ownWrite_val] at hrep
  split at hrep
  · rename_i hval
    cases hval
    simp [Regs.set]
  · cases hrep

theorem ownWrite_body : (ownWriteTv.certs.getD 0 ⟨[], []⟩).body.threadFree = true ∧
    (ownWriteTv.certs.getD 0 ⟨[], []⟩).body.posSizes = true := by decide

/-- **The x86 bytes of `ownWrite` read back their write under every `M ⊑ XL`**: by translation
validation into CIR and the single-threaded lift, from one sequential run. -/
theorem ownWrite_eax {T : List (List XTrace)} (hT : ownWrite.traces = some T) {M : Exec → Prop}
    (hxl : M ⊑ Exec.Xl) {f : Final} (hf : AxReach ownWrite T M f) :
    (f.regs 0 .rax).toNat % 2 ^ 32 = 1 := by
  obtain ⟨h1, h2, -⟩ := ownWrite_ok
  obtain ⟨tr, rs, m, hr, hw⟩ := TvTest.solo_sound (c := ownWriteTv) rfl h1 h2 ownWrite_body.1
    ownWrite_body.2 hT hxl hf
  have hrax := ownWrite_seq hr
  simp only [Test.witness, ownWriteTv, ownWrite, Silmaril.X86.MemoryModel.Litmus.Cond.eval,
    Silmaril.X86.MemoryModel.Litmus.Atom.eval, soloFinal, ite_true, hrax] at hw
  simpa using hw.symm

set_option maxRecDepth 8192 in
/-- `ownWriteCheck` holds. -/
theorem ownWriteCheck_ok : ownWriteCheck = true := by decide +kernel

/-- `ownWrite` has a behaviour under every `SC ⊑ M ⊑ XL`. -/
theorem ownWrite_some {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) :
    ∃ T f, ownWrite.traces = some T ∧ AxReach ownWrite T M f := by
  have h := ownWriteCheck_ok
  unfold ownWriteCheck at h
  split at h
  · rename_i T hT
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      Option.isSome_iff_exists] at h
    obtain ⟨hok, tr, htr, m, hm⟩ := h
    exact ⟨[T], _, hT, (axReach_one_iff ownWrite T hok hsc hxl _).mpr ⟨tr, htr, m, hm, rfl⟩⟩
  · cases h

end Silmaril.Proofs.X86.Concurrency.Cir.Seq.Tv
