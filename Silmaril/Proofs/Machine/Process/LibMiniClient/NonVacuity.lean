module

public import Silmaril.Machine.Process.LibMiniClient.Defs
public import Silmaril.Formats.ELF.Reader

/-!
# Proofs: rung 12's launch hypotheses are satisfiable (review)

`rung12_processSafe` assumes `snapshot.image = image` and `X86Launch.ValidEntry x86ExtNative
snapshot en inp`. If no snapshot of the parsed rung-12 image passed LPS's launch check, the
theorem (and `Task.startRun`) would hold vacuously. This module exhibits one:

* `hdr_ok`, `phs_ok`: the ELF header and the three program headers (two `PT_LOAD`, one
  `PT_GNU_STACK`) are what silmaril's ELF reader returns on the fixture bytes `exe.bytes`
  (kernel evaluation), so `snap` is built from the same bytes as `image`.
* **`launch_nonvacuous`**: `snap` with `image`, the entry `en` (`sp = 0x7fffffffe000`,
  `brk = 0x402000`, `mmapBase = 0x40000000`) and the input `inp` (`argv = ["a"]`, no
  environment) satisfies `ValidEntry` (header and load-layout match, segment sizes and
  disjointness, the entry instruction `31 ed` fetchable, the program-header table readable,
  the stack/brk/mmap windows).
* `header_mutated_rejected`: changing the header's entry point breaks `ValidEntry`.

`Segment.readable`/`executable` go through `String.contains`, which the kernel does not
reduce, so the permission facts are rewritten first (`seg_perms`); the rest is `decide
+kernel` on the fixture. Standard axioms only.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LibMiniClient.Launch

open Silmaril.Process.LPS Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LibMiniClient
open Silmaril.Machine.Link.Fixtures.LibMiniClientBfd

namespace NV
export Silmaril.Proofs.Machine.Link.LibMiniClient.NonVacuity (seg0 seg1 loadImg_segments seg0_facts seg1_facts)
end NV

def hdr : Silmaril.Formats.ELF.Header := ⟨0, 0, 2, 62, 1, 0x401000, 64, 4808, 0, 64, 56, 3, 64, 5, 4⟩
def phs : List Silmaril.Formats.ELF.ProgramHeader :=
  [⟨1, 4, 0, 0x400000, 0x400000, 0xe8, 0xe8, 0x1000⟩,
   ⟨1, 5, 0x1000, 0x401000, 0x401000, 0x113, 0x113, 0x1000⟩,
   ⟨0x6474e551, 6, 0, 0, 0, 0, 0, 0x10⟩]

set_option maxRecDepth 100000 in
theorem hdr_ok : Silmaril.Formats.ELF.readHeader exe.bytes = some hdr := by decide +kernel
set_option maxRecDepth 100000 in
theorem phs_ok : Silmaril.Formats.ELF.readProgramHeaders exe.bytes hdr = some phs := by decide +kernel

def snap : X86Launch.Snapshot := ⟨hdr, phs, image⟩
def inp : ProcInput where
  argv := [[97]]
  envp := []
  imageFs := []
  stdin := InputStream.eof
  uid := 1000
  gid := 100
  groups := []
  net := netSilent
  nofile := 1024
  sigmask := 0
  hwcap := 0
  abortTerminal := false
  vaSize := .sv48
  urandom := InputStream.defaultUrandom
  tmp := []

def en : ExecEntry := ⟨0x7fffffffe000, 0x402000, 0x40000000, ⟨0, fun _ => 0⟩⟩

set_option maxRecDepth 100000 in
theorem header_matches : X86Launch.HeaderMatches snap := by
  unfold X86Launch.HeaderMatches; decide +kernel
set_option maxRecDepth 100000 in
theorem seg_perms : NV.seg0.perms = "r" ∧
    NV.seg1.perms = "rx" := by decide +kernel
set_option maxRecDepth 100000 in
theorem layout_matches : X86Launch.LoadLayoutMatches snap := by
  have e : snap.image.segments = [NV.seg0,
    NV.seg1] :=
    NV.loadImg_segments
  obtain ⟨b0, s0, -⟩ := NV.seg0_facts
  obtain ⟨b1, s1, -⟩ := NV.seg1_facts
  obtain ⟨p0, p1⟩ := seg_perms
  unfold X86Launch.LoadLayoutMatches X86Launch.ProgramHeaderMatches
  rw [e]
  simp only [snap, phs, b0, s0, b1, s1,
    Segment.executable, Segment.writable, Segment.readable, p0, p1, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left]
  simp (config := { decide := true })
set_option maxRecDepth 100000 in
theorem segs_sized : (∀ segment ∈ snap.image.segments,
      segment.bytes.length = segment.size ∧ 0 < segment.size ∧
        (segment.base : Int) + segment.size ≤ x86AddressSpace.taskSize) := by decide +kernel
set_option maxRecDepth 100000 in
theorem segs_disjoint : snap.image.segments.Pairwise (fun first second =>
      first.base + first.size ≤ second.base ∨ second.base + second.size ≤ first.base) := by decide +kernel
theorem segs_eq : snap.image.segments = [NV.seg0, NV.seg1] := NV.loadImg_segments

theorem initPc_eq : snap.image.initPc = 0x401000 := by decide +kernel

set_option maxRecDepth 100000 in
theorem nowrap : ∀ segment ∈ snap.image.segments, segment.base + segment.bytes.length ≤ 2 ^ 64 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem permitted : (initialMemory snap.image.segments 0 []).checkSpan .execute 0x401000 2 = true := by
  obtain ⟨b0, s0, -⟩ := NV.seg0_facts
  obtain ⟨b1, s1, -⟩ := NV.seg1_facts
  obtain ⟨p0, p1⟩ := seg_perms
  apply (Silmaril.Process.Memory.checkSpan_iff _ _ _ _).mpr
  refine ⟨by decide, by decide, ?_⟩
  intro offset bound
  rw [segs_eq]
  simp [Silmaril.Process.Memory.permits, initialMemory, segmentRegion, segmentPermissions,
    Segment.readable, Segment.writable, Segment.executable, b0, s0, b1, s1, p0, p1,
    Silmaril.Process.Region.Contains, Silmaril.Process.Permissions.allows]
  omega

set_option maxRecDepth 100000 in
theorem view : ∀ i < 2, segmentsView snap.image.segments (0x401000 + i) none = some ([0x31, 0xed] : List Byte)[i]! := by
  decide +kernel

theorem fetched : (initialMemory snap.image.segments 0 []).fetchBytes 0x401000 2 = some [0x31, 0xed] := by
  apply Silmaril.Process.Memory.readWith_eq _ .execute 0x401000 [0x31, 0xed] permitted
  intro i hi
  rw [initialMemory_segments_get _ _ nowrap, view i hi]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem entry_fetchable : x86ExtNative.entryFetchable snap.image.segments snap.image.initPc = true := by
  have fetchedD := Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨[0x31, 0xed], fetched, (by decide : Silmaril.X86.Ext.decode [0x31, 0xed] = some (.alu .d .xor (.reg .rbp) .rbp, 2))⟩
  rw [initPc_eq]
  change (match Silmaril.X86.Ext.fetch (initialMemory snap.image.segments 0 []) 0x401000 with
      | .decoded _ _ => true
      | _ => decide ((initialMemory snap.image.segments 0 []).fetchBytes 0x401000 2 =
        some [0x0f, 0x05])) = true
  rw [fetchedD]

set_option maxRecDepth 100000 in
theorem phdrs_readable : (memoryRead snap.image.segments (zw snap.image.phdrs.addr)
      (snap.image.phdrs.num * snap.image.phdrs.ent)).isSome = true := by
  have : snap.image.phdrs = ⟨0x400040, 56, 3⟩ := by decide +kernel
  obtain ⟨b0, s0, -⟩ := NV.seg0_facts
  obtain ⟨p0, -⟩ := seg_perms
  have r0 : NV.seg0.readable = true := by
    simp [Segment.readable, p0]
  have m : ((List.range 168).mapM fun k =>
      NV.seg0.byteAt (64 + k)).isSome = true := by
    decide +kernel
  rw [this, segs_eq]
  simp only [memoryRead, findSegment, b0, s0]
  simpa [zw, uns, r0, b0] using m
set_option maxRecDepth 100000 in
theorem brk_valid : ValidBrk snap.image.segments en.brk := by unfold ValidBrk; decide +kernel

set_option maxRecDepth 100000 in
theorem valid : X86Launch.ValidEntry x86ExtNative snap en inp := by
  refine ⟨⟨header_matches, layout_matches, segs_sized, segs_disjoint, entry_fetchable, phdrs_readable⟩, ?_, ?_, ?_, brk_valid, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

/-- **The launch hypotheses of `rung12_processSafe` are jointly satisfiable.** -/
theorem launch_nonvacuous : ∃ (snapshot : X86Launch.Snapshot) (en : ExecEntry) (inp : ProcInput),
    snapshot.image = image ∧ X86Launch.ValidEntry x86ExtNative snapshot en inp :=
  ⟨snap, en, inp, rfl, valid⟩

set_option maxRecDepth 100000 in
/-- Mutation check: a header whose entry point is not the image's `initPc` is rejected. -/
theorem header_mutated_rejected :
    ¬ X86Launch.ValidEntry x86ExtNative { snap with header := { hdr with entry := 0x401001 } } en inp := by
  intro h
  have := h.1.1.2.2.2.2.2.2.2.2.2.2.1
  rw [show ({ snap with header := { hdr with entry := 0x401001 } } : X86Launch.Snapshot).image.initPc
    = 0x401000 from initPc_eq] at this
  exact absurd this (by decide)

end Silmaril.Proofs.Machine.Process.LibMiniClient.Launch
