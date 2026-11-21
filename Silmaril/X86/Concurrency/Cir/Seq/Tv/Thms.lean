module

public import Silmaril.X86.Concurrency.Cir.Seq.Tv.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Thms
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Seq.Tv

/-!
# The single-threaded lift through translation validation: what is proved

PROVED, standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Seq/Tv.lean`).

* `TvTest.solo_sound`: **one validated x86 thread is sequential**. For a test with one thread
  whose certificate checks (`tvOk`, `domOk`), and whose CIR thread is thread-free with
  positive sizes, every x86 behaviour of the bytes (`AxReach` over the extracted traces)
  under any `M ⊑ XL` has the witness value of a **sequential run** of the CIR thread. This chains
  `TvTest.refines` (x86 to CIR) with `solo_behav_sound` (CIR to sequential).
* `ownWrite_eax`: the demonstration. The x86 bytes `movl $1, 0x10000; movl 0x10000, %eax`
  end with `eax = 1` under every `M ⊑ XL`, from one sequential run of the CIR thread.

Only witness values transfer, as in `Tv`: `TvTest.refines` relates final states through the
test's condition, and registers outside the clobber set.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Seq.Tv

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (Final AxReach XTrace initByte)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- **One validated x86 thread is sequential under `M ⊑ XL`.** -/
theorem TvTest.solo_sound {c : TvTest} {ct : Cert} (hc : c.certs = [ct]) (h : c.tvOk = true)
    (hd : c.domOk = true) (ht : ct.body.threadFree = true) (hp : ct.body.posSizes = true)
    {T : List (List XTrace)} (hT : c.test.traces = some T) {M : Exec → Prop} (hxl : M ⊑ Exec.Xl)
    {f : Final} (hf : AxReach c.test T M f) :
    ∃ tr rs m, SeqRun ct.body Regs.zero (initByte c.test.locs) tr rs m ∧
      c.test.witness.eval (soloFinal rs m) = c.test.witness.eval f :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.Tv.TvTest.solo_sound hc h hd ht hp hT hxl hf

/-- `ownWriteTv` checks: certificate, domain and extraction (`decide +kernel`). -/
theorem ownWrite_ok : ownWriteTv.tvOk = true ∧ ownWriteTv.domOk = true ∧
    ownWriteTv.test.traces.isSome = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.Tv.ownWrite_ok

/-- **The x86 bytes of `ownWrite` read back their write under every `M ⊑ XL`.** -/
theorem ownWrite_eax {T : List (List XTrace)} (hT : ownWrite.traces = some T) {M : Exec → Prop}
    (hxl : M ⊑ Exec.Xl) {f : Final} (hf : AxReach ownWrite T M f) :
    (f.regs 0 .rax).toNat % 2 ^ 32 = 1 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.Tv.ownWrite_eax hT hxl hf

/-- `ownWriteCheck` holds (`decide +kernel`). -/
theorem ownWriteCheck_ok : ownWriteCheck = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.Tv.ownWriteCheck_ok

/-- **`ownWrite_eax` is not vacuous**: the x86 bytes of `ownWrite` have a
behaviour under every `SC ⊑ M ⊑ XL`. (Their extracted traces also contain a trace whose load
returns `0`; the lift is what rules it out.) -/
theorem ownWrite_some {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) :
    ∃ T f, ownWrite.traces = some T ∧ AxReach ownWrite T M f :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.Tv.ownWrite_some hsc hxl

end Silmaril.X86.Concurrency.Cir.Seq.Tv
