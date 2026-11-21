module

public import Silmaril.X86.Concurrency.Lift.Process.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Thms
public import Silmaril.Process.LpsBridge.Defs

/-!
# The single-threaded lift for processes: proofs

* `sharingNo_unmodeled`: `unmodeled` is an outcome of the native table for each sharing
  syscall (they are pending arms, as `clone`/`clone3`/`futex` in `LpsBridge.Threads`);
* `singleThreaded_of_psafe`: a process-safe configuration is single-threaded;
* `nativeStepUnder_of`: under `Task.lpsNativeFlat`, the native steps read the same under every
  `SC ⊑ M ⊑ XL`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Lift.Process

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LpsBridge
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.Concurrency.Lift
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

theorem sharingNo_unmodeled (i : SyscallInput) (m : Model) (h : sharingNo i.sysno.toNat) :
    spec i m .unmodeled := by
  rcases h with h | h | h | h | h | h | h | h <;>
    (simp only [spec, NativeX86.extendedSyscallSpec, dispatch, h]; rfl)

/-- **A process-safe configuration is single-threaded.** -/
theorem singleThreaded_of_psafe {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}
    {Allowed : List Event → Prop} {c : Config (machine oracle)}
    (h : PSafe segs refused Allowed c) : SingleThreaded segs refused c := by
  rintro tr ⟨ms, model⟩ hs ⟨alive, x8, hp, hn⟩
  exact h.2 tr _ [] hs (.syscallUnmodeled alive hp (sharingNo_unmodeled _ _ hn))

/-- Under the glue, the native steps read the same under every `SC ⊑ M ⊑ XL`. -/
theorem nativeStepUnder_of (hF : Task.lpsNativeFlat) {M : Exec → Prop} (hsc : Exec.Sc ⊑ M)
    (hxl : M ⊑ Exec.Xl) : NativeStepUnder M := by
  intro s r hs hp
  obtain ⟨acts, hP, hok, hr⟩ := hF s r hs hp
  refine ⟨acts, hP, fun m => ?_⟩
  rw [oneSem_iff hsc hxl _ acts hok, hr]
  exact ⟨fun h => (Option.some.inj h).symm, fun h => h ▸ rfl⟩

theorem ext_fetch_of_ext8_decoded {memory : Silmaril.Process.Memory} {address : Nat}
    {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (h : Silmaril.X86.Ext8.fetch memory address = .inl (.decoded i n)) :
    Silmaril.X86.Ext.fetch memory address = .decoded i n := by
  unfold Silmaril.X86.Ext8.fetch at h
  cases hx : Silmaril.X86.Ext.fetch memory address with
  | undecodable =>
    rw [hx] at h
    simp only at h
    split at h
    · split at h <;> cases h
    · cases h
  | truncated => rw [hx] at h; cases h
  | decoded i' n' => rw [hx] at h; cases h; rfl

/-- **A non-syscall native step is an `Open.step`.** -/
theorem open_step_of_native {s : X86State} {r : AccessReport X86State}
    (hs : x86NativeStep8 s = .ok r) (hp : r.value.pending = none) :
    Silmaril.X86.Open.step s.m = some r.value.m := by
  unfold x86NativeStep8 at hs
  split at hs
  · split at hs
    · cases hs
    · cases hs; simp at hp
  · unfold Silmaril.X86.Open.step
    split at hs
    · cases hs
    · cases hs
    · rename_i i n e
      rw [e]
      have hn : n = i.length := by
        obtain ⟨b, -, hd⟩ := Silmaril.X86.Ext.fetch_eq_decoded_iff.mp (ext_fetch_of_ext8_decoded e)
        exact (Silmaril.X86.Ext.decode_length hd).1
      subst hn
      unfold x86ExecResult at hs
      split at hs <;> cases hs
      simp_all [Silmaril.X86.Open.ofResult]
    · rename_i i n e
      rw [e]
      unfold x86ExecResult at hs
      split at hs <;> cases hs
      simp_all [Silmaril.X86.Open.ofResult]

/-- The native glue follows from the `Open` glue. -/
theorem lpsNativeFlat_of_openFlatStep (hF : Task.openFlatStep) : Task.lpsNativeFlat :=
  fun s r hs hp => hF s.m r.value.m (open_step_of_native hs hp)

end Silmaril.Proofs.X86.Concurrency.Lift.Process
