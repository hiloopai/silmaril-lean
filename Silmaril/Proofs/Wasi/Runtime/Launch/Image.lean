module

public import Silmaril.Proofs.Wasi.Runtime.Launch.Loop
public import Silmaril.Machine.Process.LpsBridge.Thms

/-!
# Proofs: `hello`'s runtime launched by LPS from the ELF image `helloImage`

* `launch_bytes`: below the stack reservation, the launch memory of a snapshot of
  `helloImage` holds the image's bytes (`segmentsView`).
* `permits_of_mem`: a byte of a mapped region with the right permission is permitted.
* **`launch_helloMem`**: the launch memory holds the program (`HelloMem`), when the entry block
  does not wrap and the image lies below the stack reservation.
* `launch_rip`: the launch state starts at `codeBase`.
* **`helloLaunch`**: the launch state starts a `HelloLoop Open.step segs ch e`.
* **`hello_processSafe`**: every such launch of a snapshot of `helloImage` is LPS process-safe
  (`ProcessSafe`, every flag oracle of the release machine `x86WithFlagOracle8`) for "a prefix
  of the OS image of `hello`'s WASI run against `stdoutImpl` on channel `1`, then `exit 0`".
  The configuration is LPS's own `X86Launch.init`, aligned with the launch state by
  `initF_aligned`; nothing is assumed about it.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Runtime.Launch

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Process (Memory Region Access)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Wasi.Os
open Silmaril.Wasi.Runtime (codeBase dataBase helloCode HelloLoop)
open Silmaril.Wasi.Examples (hiBytes)

variable {snapshot : X86Launch.Snapshot} {en : ExecEntry} {inp : ProcInput}

/-- The image's segments do not wrap. -/
theorem helloImage_nowrap : ∀ seg ∈ helloImage.segments, seg.base + seg.bytes.length ≤ 2 ^ 64 := by
  decide

/-- **Below the stack reservation, the launch memory holds the image's bytes.** -/
theorem launch_bytes (himg : snapshot.image = helloImage)
    (hnw : en.sp.toNat + (X86Launch.entryStack snapshot.image en inp).length ≤ 2 ^ 64)
    {a : Nat} (ha : a < en.sp.toNat - stackMaxSize.toNat) :
    (launchState snapshot en inp).memory.bytes.get? a =
      segmentsView helloImage.segments a none := by
  have hmem : (launchState snapshot en inp).memory =
      initialMemory snapshot.image.segments en.sp (X86Launch.entryStack snapshot.image en inp) :=
    rfl
  rw [hmem, X86Launch.initialMemory_below_stack_get _ _ _ _ ha hnw, himg,
    initialMemory_segments_get _ _ helloImage_nowrap]

/-- A byte of a mapped region with the right permission is permitted. -/
theorem permits_of_mem {M : Memory} {r : Region} {acc : Access} {a : Nat} (hr : r ∈ M.regions)
    (hc : r.Contains a) (hp : r.permissions.allows acc = true) : M.permits acc a = true := by
  unfold Memory.permits
  rw [List.any_eq_true]
  exact ⟨r, hr, by simp [hc, hp]⟩

theorem launch_regions (himg : snapshot.image = helloImage) {r : Region}
    (hr : r ∈ helloImage.segments.map segmentRegion) :
    r ∈ (launchState snapshot en inp).memory.regions := by
  have h : (launchState snapshot en inp).memory.regions =
      snapshot.image.segments.map segmentRegion ++ _ := rfl
  rw [h, himg]
  exact List.mem_append_left _ hr

theorem codeSeg_mem : segmentRegion helloCodeSeg ∈ helloImage.segments.map segmentRegion :=
  List.mem_map_of_mem (by simp [helloImage])

theorem dataSeg_mem : segmentRegion helloDataSeg ∈ helloImage.segments.map segmentRegion :=
  List.mem_map_of_mem (by simp [helloImage])

theorem code_view : ∀ i (h : i < helloCode.length),
    segmentsView helloImage.segments (0x401000 + i) none = some helloCode[i] := by
  decide

theorem codeSeg_exec : (segmentRegion helloCodeSeg).permissions.allows .execute = true := by
  simp [segmentRegion, segmentPermissions, Segment.executable, helloCodeSeg,
    Silmaril.Process.Permissions.allows]

theorem dataSeg_read : (segmentRegion helloDataSeg).permissions.allows .read = true := by
  simp [segmentRegion, segmentPermissions, Segment.readable, helloDataSeg,
    Silmaril.Process.Permissions.allows]

/-- **The launch memory holds the program.** -/
theorem launch_helloMem (himg : snapshot.image = helloImage)
    (hnw : en.sp.toNat + (X86Launch.entryStack snapshot.image en inp).length ≤ 2 ^ 64)
    (hbelow : 0x402072 ≤ en.sp.toNat - stackMaxSize.toNat) :
    HelloMem (launchState snapshot en inp).memory := by
  have hcode : ∀ i < 42,
      (launchState snapshot en inp).memory.permits .execute (0x401000 + i) = true :=
    fun i hi => permits_of_mem (launch_regions himg codeSeg_mem)
      (by simp only [Region.Contains, segmentRegion, helloCodeSeg]; omega) codeSeg_exec
  have hdata : ∀ i < 2, (launchState snapshot en inp).memory.permits .read (0x402000 + i) = true :=
    fun i hi => permits_of_mem (launch_regions himg dataSeg_mem)
      (by simp only [Region.Contains, segmentRegion, helloDataSeg, phent]; omega) dataSeg_read
  have hd0 := launch_bytes himg hnw (a := 0x402000) (by omega)
  have hd1 := launch_bytes himg hnw (a := 0x402001) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold Silmaril.X86.Ext.Loaded Memory.fetchBytes
    refine Memory.readWith_eq _ _ _ _ ((Memory.checkSpan_iff _ _ _ _).2
      ⟨by decide, by decide, fun o ho => hcode o ho⟩) ?_
    intro i hi
    have hl : helloCode.length = 42 := rfl
    have hb : codeBase.toNat = 0x401000 := rfl
    rw [launch_bytes himg hnw (by omega), hb]
    exact code_view i hi
  · have p0 : (launchState snapshot en inp).memory.permits .read 0x402000 = true :=
      hdata 0 (by omega)
    simp only [viewByte, show dataBase.toNat = 0x402000 from rfl, p0, ↓reduceIte]
    rw [← Std.ExtHashMap.get?_eq_getElem?, hd0]
    decide
  · have p1 : (launchState snapshot en inp).memory.permits .read 0x402001 = true :=
      hdata 1 (by omega)
    simp only [viewByte, show (dataBase + 1#64).toNat = 0x402001 from rfl, p1, ↓reduceIte]
    rw [← Std.ExtHashMap.get?_eq_getElem?, hd1]
    decide

/-- The launch state starts at `codeBase`. -/
theorem launch_rip (himg : snapshot.image = helloImage) :
    (launchState snapshot en inp).core.rip = codeBase := by
  simp [launchState, launchCore, himg, helloImage, codeBase]

/-- **The launch state starts a runtime of `hello`.** -/
def helloLaunch (segs : List Segment) (himg : snapshot.image = helloImage)
    (hnw : en.sp.toNat + (X86Launch.entryStack snapshot.image en inp).length ≤ 2 ^ 64)
    (hbelow : 0x402072 ≤ en.sp.toNat - stackMaxSize.toNat) {e : Silmaril.Process.LPS.Model}
    {ch : Word} (hfd : fdLookup e.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    HelloLoop Silmaril.Machine.X86.Open.step segs ch e :=
  helloLoopAt segs (launch_helloMem himg hnw hbelow) rfl (launch_rip himg) hfd hch

/-- **Every launch of a snapshot of `helloImage` is LPS process-safe**, for every flag oracle
of the release machine, with the traces "a prefix of the OS image of `hello`'s WASI run against
`stdoutImpl` on channel `1`, then `exit 0`". -/
theorem hello_processSafe (refusals : SpuriousCfg) (limit : Int)
    (himg : snapshot.image = helloImage)
    (hnw : en.sp.toNat + (X86Launch.entryStack snapshot.image en inp).length ≤ 2 ^ 64)
    (hbelow : 0x402072 ≤ en.sp.toNat - stackMaxSize.toNat) :
    ProcessSafe snapshot refusals limit en inp
      (fun tr => tr <+: osTrace 1 (Silmaril.Wasi.wtrace helloRun) ++ [.exitEv 0 inp.fs]) := by
  intro oracle
  rw [Silmaril.Wasi.Os.helloRun_os]
  exact (Silmaril.Proofs.Machine.Process.LpsBridge.psafeF_iff (oracle := oracle)).1 <|
    Silmaril.Wasi.Runtime.helloLoop_psafe Silmaril.Proofs.Machine.Process.LpsBridge.agrees_open8
      (helloLaunch snapshot.image.segments himg hnw hbelow rfl (by decide))
      (Silmaril.Proofs.Machine.Process.LpsBridge.initF_aligned oracle _ snapshot en limit inp) rfl

end Silmaril.Wasi.Runtime.Launch
