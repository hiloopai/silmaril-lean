module

public import Silmaril.Proofs.Wasi.Runtime.Launch.Image
public import Silmaril.Process.LPS.Probes.Launches

/-!
# Proofs: valid launches of `helloImage`, and non-vacuity

* **`hello_processSafe_valid`**: every launch of a snapshot of `helloImage` that passes LPS's
  launch check (`X86Launch.ValidEntry`) is process-safe for "a prefix of `hi` on channel `1`
  (the OS image of `hello`'s WASI run against `stdoutImpl`), then `exit 0`". The entry-block
  fit comes from silmaril's `stackFits_of`, the image placement from `ValidEntry`.
* **`helloSnapshot_valid`**: `helloSnapshot` passes the check on `helloEn`/`helloInp`.
* **`hello_nonvacuous`**: so some valid launch of `helloImage` exists, and it is process-safe.

The concrete facts are decided by `decide +kernel` (no native evaluation).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Runtime.Launch

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Wasi.Os

/-- **Every valid launch of a snapshot of `helloImage` is process-safe.** -/
theorem hello_processSafe_valid {snapshot : X86Launch.Snapshot} {en : ExecEntry}
    {inp : ProcInput} (refusals : SpuriousCfg) (limit : Int) (himg : snapshot.image = helloImage)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafe snapshot refusals limit en inp
      (fun tr => tr <+: osTrace 1 (Silmaril.Wasi.wtrace helloRun) ++ [.exitEv 0 inp.fs]) := by
  obtain ⟨-, -, -, -, -, -, -, -, htop, hsegs⟩ := hv
  have hnw := Silmaril.Process.LPS.Probes.Probe.stackFits_of en inp snapshot.image htop
  have hd := hsegs helloDataSeg (by rw [himg]; simp [helloImage])
  have hu : uns en.sp = (en.sp.toNat : Int) := rfl
  have hsm : stackMaxSize = 8388608 := rfl
  have hsm' : stackMaxSize.toNat = 8388608 := rfl
  rw [hu, hsm] at hd
  have hb : 0x402072 ≤ en.sp.toNat - stackMaxSize.toNat := by
    simp only [helloDataSeg, phent] at hd
    omega
  exact hello_processSafe refusals limit himg hnw hb

set_option maxRecDepth 100000 in
theorem helloHeader_matches : X86Launch.HeaderMatches helloSnapshot := by
  unfold X86Launch.HeaderMatches
  decide +kernel

theorem codeSeg_flags : helloCodeSeg.executable = true ∧ helloCodeSeg.writable = false ∧
    helloCodeSeg.readable = true := by
  simp [Segment.executable, Segment.writable, Segment.readable, helloCodeSeg]

theorem dataSeg_flags : helloDataSeg.executable = false ∧ helloDataSeg.writable = false ∧
    helloDataSeg.readable = true := by
  simp [Segment.executable, Segment.writable, Segment.readable, helloDataSeg]

theorem helloLayout_matches : X86Launch.LoadLayoutMatches helloSnapshot := by
  obtain ⟨c1, c2, c3⟩ := codeSeg_flags
  obtain ⟨d1, d2, d3⟩ := dataSeg_flags
  unfold X86Launch.LoadLayoutMatches X86Launch.ProgramHeaderMatches
  simp only [helloSnapshot, helloImage, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left, c1, c2, c3, d1, d2, d3]
  simp (config := { decide := true })

/-- The entry instruction is fetchable from the segment-only memory. -/
theorem helloEntry_fetched :
    (initialMemory helloImage.segments 0 []).fetchBytes 0x401000 5 =
      some [0xbe, 0x00, 0x20, 0x40, 0x00] := by
  have hc := codeSeg_flags.1
  refine Silmaril.Process.Memory.readWith_eq _ .execute 0x401000 [0xbe, 0x00, 0x20, 0x40, 0x00]
    ((Silmaril.Process.Memory.checkSpan_iff _ _ _ _).2 ⟨by decide, by decide, fun o ho => ?_⟩) ?_
  · refine permits_of_mem (r := segmentRegion helloCodeSeg)
      (by simp [initialMemory, helloImage]) ?_ ?_
    · simp only [Silmaril.Process.Region.Contains, segmentRegion, helloCodeSeg]
      simp only [List.length_cons, List.length_nil] at ho
      omega
    · simp [segmentRegion, segmentPermissions, hc, Silmaril.Process.Permissions.allows]
  · intro i hi
    rw [initialMemory_segments_get _ _ helloImage_nowrap]
    have hl : helloCode.length = 42 := rfl
    have h := code_view i (by simp only [List.length_cons, List.length_nil] at hi; omega)
    rw [h]
    simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with
      rfl | rfl | rfl | rfl | rfl <;> rfl

theorem helloEntry_fetchable :
    x86ExtNative.entryFetchable helloSnapshot.image.segments helloSnapshot.image.initPc = true := by
  have fetchedD := Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
    ⟨[0xbe, 0x00, 0x20, 0x40, 0x00], helloEntry_fetched,
      (by decide : Silmaril.X86.Ext.decode [0xbe, 0x00, 0x20, 0x40, 0x00] =
        some (.movI32 .rsi 0x402000#32, 5))⟩
  change (match Silmaril.X86.Ext.fetch (initialMemory helloImage.segments 0 []) 0x401000 with
      | .decoded _ _ => true
      | _ => decide ((initialMemory helloImage.segments 0 []).fetchBytes 0x401000 2 =
        some [0x0f, 0x05])) = true
  rw [fetchedD]

set_option maxRecDepth 100000 in
theorem helloPhdrs_readable : (memoryRead helloSnapshot.image.segments
    (zw helloSnapshot.image.phdrs.addr)
      (helloSnapshot.image.phdrs.num * helloSnapshot.image.phdrs.ent)).isSome = true := by
  have m : ((List.range 112).mapM fun k => helloDataSeg.byteAt (2 + k)).isSome = true := by
    decide +kernel
  simp only [helloSnapshot, helloImage, helloPhdrs, memoryRead, findSegment, phent]
  simpa [zw, uns, Segment.readable, helloCodeSeg, helloDataSeg, phent] using m

set_option maxRecDepth 100000 in
theorem helloBrk_valid : ValidBrk helloSnapshot.image.segments helloEn.brk := by
  unfold ValidBrk
  decide +kernel

set_option maxRecDepth 100000 in
theorem helloSnapshot_valid : X86Launch.ValidEntry x86ExtNative helloSnapshot helloEn helloInp := by
  refine ⟨⟨helloHeader_matches, helloLayout_matches, ?_, ?_, helloEntry_fetchable,
    helloPhdrs_readable⟩, ?_, ?_, ?_, helloBrk_valid, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

/-- **Non-vacuity**: a valid launch of `helloImage` exists, and every one is process-safe. -/
theorem hello_nonvacuous : ∃ (snapshot : X86Launch.Snapshot) (en : ExecEntry) (inp : ProcInput),
    snapshot.image = helloImage ∧ X86Launch.ValidEntry x86ExtNative snapshot en inp ∧
      ∀ refusals limit, ProcessSafe snapshot refusals limit en inp
        (fun tr => tr <+: osTrace 1 (Silmaril.Wasi.wtrace helloRun) ++ [.exitEv 0 inp.fs]) :=
  ⟨helloSnapshot, helloEn, helloInp, rfl, helloSnapshot_valid,
    fun refusals limit => hello_processSafe_valid refusals limit rfl helloSnapshot_valid⟩

end Silmaril.Wasi.Runtime.Launch
