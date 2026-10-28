module

public import Silmaril.Process.LPS.Machines.X86Features
public import Silmaril.Process.LPS.Machines.X86LaunchExecution

/-!
# A missing feature is a death, and a larger processor continues

The image is the launch control of `X86LaunchControls` with `vpxor xmm0, xmm0,
xmm0` (`C5 F9 EF C0`, VEX.128, CPUID AVX) in front of `mov eax, 60; sub edi,
edi; syscall`. With the AVX lane (`avxConfig F = ⟨F, [Avx.ext]⟩`):

* under `baseline64` (x87, SSE, SSE2) the first instruction is `featureUD .avx`,
  a death (SIGILL): the launch errors, and every execution errors
  (`baseline64_errors`, `baseline64_allErrors`);
* under `baseline64 ∪ {avx}` it retires, and the launch exits with status 0
  (`avx_exit_trace`, `avx_not_allErrors`).

So `baseline64 ≤ baseline64 ∪ {avx}` (`baseline_le_avx`), and the
all-traces-error judgment does not transfer upward without the hypothesis of
`X86Features.transfer_of_settles` (`no_upward_transfer`): the image reaches
`featureUD` under the smaller configuration.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Silmaril.Process.LPS.Machines.X86Features.Controls

open Silmaril.X86 (Byte)
open Silmaril.X86.Features (FeatureSet Feature)
open Silmaril.X86.Features.FeatureSet (baseline64)
open X86Launch.Controls (headerBytes programHeaderBytes entry input header programHeader
  mov_execution sub_execution movExitNumber zeroExitStatus native_exit_zero)

local notation "FConfig" => Silmaril.X86.Features.Config

/-- The AVX lane on feature set `F`. -/
def avxConfig (F : FeatureSet) : FConfig := ⟨F, [Silmaril.X86.Features.Avx.ext], List.pairwise_singleton _ _⟩

/-- `baseline64` with AVX. -/
def avx64 : FeatureSet := insert Feature.avx baseline64

theorem baseline_le_avx : avxConfig baseline64 ≤ avxConfig avx64 :=
  ⟨fun f hf => by
    change (f == Feature.avx || baseline64.has f) = true
    rw [show baseline64.has f = true from hf, Bool.or_true],
   Silmaril.X86.Features.Included.refl _⟩

/-- `vpxor xmm0, xmm0, xmm0; mov eax, 60; sub edi, edi; syscall`. -/
def code : List Byte := [0xc5, 0xf9, 0xef, 0xc0, 0xb8, 0x3c, 0, 0, 0, 0x29, 0xff, 0x0f, 0x05]

def fileBytes : List Byte := headerBytes ++ programHeaderBytes ++ code

def image : Image := ⟨[⟨0x400000, 133, "rx", fileBytes⟩], 0x400078, ⟨0x400040, 56, 1⟩⟩

def snapshot : X86Launch.Snapshot := ⟨header, [programHeader], image⟩

/-- The launch under configuration `c`. -/
def initial (c : FConfig) : LPS.Config (x86Features c) :=
  X86Launch.init (x86Features c) snapshot entry sourceAllocLimit input

/-- The launched machine state under configuration `c`. -/
def s0 (c : FConfig) : X86FState := (initial c).ms

theorem entry_code_fetched :
    (initialMemory image.segments 0 []).fetchBytes image.initPc 13 = some code := by
  have permitted : (initialMemory image.segments 0 []).checkSpan .execute image.initPc 13 = true := by
    apply (Silmaril.Process.Memory.checkSpan_iff _ _ _ _).mpr
    refine ⟨by decide, by decide, ?_⟩
    intro offset bound
    simp [Silmaril.Process.Memory.permits, initialMemory, image, segmentRegion,
      segmentPermissions, Segment.readable, Segment.writable, Segment.executable,
      Silmaril.Process.Region.Contains, Silmaril.Process.Permissions.allows]
    change decide (4194304 ≤ 4194424 + offset ∧ 4194424 + offset < 4194437) = true
    exact decide_eq_true (by omega)
  apply Silmaril.Process.Memory.readWith_eq (initialMemory image.segments 0 []) .execute
    image.initPc code permitted
  intro index bound
  change (installWrapping ∅ 0x400000 fileBytes)[0x400078 + index]? = _
  unfold installWrapping
  rw [show fileBytes = (headerBytes ++ programHeaderBytes) ++ code from
    rfl, List.zipIdx_append, List.foldl_append]
  generalize ((headerBytes ++ programHeaderBytes).zipIdx.foldl
    (fun (acc : Silmaril.Process.ByteMemory) (pair : Byte × Nat) =>
      acc.insert ((0x400000 + pair.2) % 2 ^ 64) pair.1) ∅) = prior
  change ((code.zipIdx 120).foldl
    (fun (acc : Silmaril.Process.ByteMemory) (pair : Byte × Nat) =>
      acc.insert ((0x400000 + pair.2) % 2 ^ 64) pair.1) prior)[0x400078 + index]? = _
  change index < 13 at bound
  have options : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
      index = 11 ∨ index = 12 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [code, List.zipIdx_cons, List.zipIdx_nil, Std.ExtHashMap.getElem_insert]

/-- The code, in the launched memory of every configuration. -/
theorem loaded_code_fetched (c : FConfig) :
    (s0 c).m.memory.fetchBytes image.initPc 13 = some code := by
  change (initialMemory snapshot.image.segments entry.sp
    (X86Launch.entryStack snapshot.image entry input)).fetchBytes image.initPc 13 = some code
  have permitted : (initialMemory snapshot.image.segments entry.sp
      (X86Launch.entryStack snapshot.image entry input)).checkSpan .execute image.initPc 13 = true := by
    apply (Silmaril.Process.Memory.checkSpan_iff _ _ _ _).mpr
    refine ⟨by decide, by decide, ?_⟩
    intro offset bound
    simp [Silmaril.Process.Memory.permits, initialMemory, snapshot, image, segmentRegion,
      segmentPermissions, Segment.readable, Segment.writable, Segment.executable,
      Silmaril.Process.Region.Contains, Silmaril.Process.Permissions.allows]
    change decide (4194304 ≤ 4194424 + offset ∧ 4194424 + offset < 4194437) = true
    exact decide_eq_true (by omega)
  apply Silmaril.Process.Memory.readWith_eq _ .execute image.initPc code permitted
  intro index bound
  rw [X86Launch.initialMemory_below_stack_get]
  · exact Silmaril.Process.Memory.readWith_get entry_code_fetched index bound
  · change 0x400078 + index < entry.sp.toNat - stackMaxSize.toNat
    change index < 13 at bound
    have lower : entry.sp.toNat - stackMaxSize.toNat = 0x7fffff7fe000 := by decide
    rw [lower]
    omega
  · decide +kernel

theorem initial_rip (c : FConfig) : (s0 c).m.state.core.rip.toNat = image.initPc := rfl

theorem code_at (c : FConfig) (offset len : Nat) (h : offset + len ≤ 13) (h' : offset < 13) :
    (s0 c).m.memory.fetchBytes (image.initPc + offset) len = some ((code.drop offset).take len) :=
  Silmaril.Process.Memory.readWith_sub_range (loaded_code_fetched c) h' h

/-! ## The first instruction -/

/-- `vpxor xmm0, xmm0, xmm0`. -/
def vpxor : Silmaril.X86.Features.Avx.Syntax :=
  ⟨⟨.pxor, false, false, 0, 0, .reg 0, 0⟩, by decide⟩

theorem decode_vpxor :
    Silmaril.X86.Features.Avx.decode [0xc5, 0xf9, 0xef, 0xc0] = some (vpxor, 4) := by decide

theorem vpxor_requires : Silmaril.X86.Features.Avx.ext.requires vpxor = [Feature.avx] := rfl

theorem window_decode (c : FConfig) :
    Silmaril.X86.Features.Avx.decode (Silmaril.X86.fetchWindow (s0 c).m.memory
      Silmaril.X86.maxInstrLength (s0 c).m.state.core.rip.toNat) = some (vpxor, 4) := by
  obtain ⟨rest, image⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow
    (limit := Silmaril.X86.maxInstrLength) (loaded_code_fetched c) (by decide)
  rw [initial_rip, ← image]
  exact Silmaril.X86.Features.Avx.byteDecoder.decode_append
    ([0xb8, 0x3c, 0, 0, 0, 0x29, 0xff, 0x0f, 0x05] ++ rest)
    (show Silmaril.X86.Features.Avx.byteDecoder.decode [0xc5, 0xf9, 0xef, 0xc0] = some (vpxor, 4)
      from decode_vpxor)

theorem vpxor_permitted (c : FConfig) :
    (s0 c).m.memory.Permitted .execute (s0 c).m.state.core.rip.toNat 4 :=
  Silmaril.Process.Memory.readWith_permitted
    (Silmaril.Process.Memory.readWith_sub_range (loaded_code_fetched c) (offset := 0) (len := 4)
      (by decide) (by decide))

theorem step_initial (F : FeatureSet) :
    (avxConfig F).step 0 (s0 (avxConfig F)).m =
      Silmaril.X86.Features.extStep F Silmaril.X86.Features.Avx.ext vpxor 4
        (s0 (avxConfig F)).m :=
  Silmaril.X86.Features.Avx.step_of_decode (List.pairwise_singleton _ _) (List.mem_singleton_self _)
    (window_decode _) (vpxor_permitted _)

theorem not_syscall (c : FConfig) :
    ¬ (s0 c).m.memory.fetchBytes (s0 c).m.state.core.rip.toNat 2 =
      some [0x0f, 0x05] := by
  rw [initial_rip, show image.initPc = image.initPc + 0 from rfl,
    code_at c 0 2 (by decide) (by decide)]
  decide

theorem not_rep (c : FConfig) :
    ¬ (s0 c).m.memory.fetchBytes (s0 c).m.state.core.rip.toNat 3 =
      some X86RepStosq.bytes := by
  rw [initial_rip, show image.initPc = image.initPc + 0 from rfl,
    code_at c 0 3 (by decide) (by decide)]
  decide

/-- Under `baseline64`, `vpxor` is `featureUD .avx`: a death. -/
theorem step_baseline64 :
    (x86Features (avxConfig baseline64)).step image.segments (s0 (avxConfig baseline64)) =
      .fault := by
  change step defaultSpans (avxConfig baseline64) (s0 (avxConfig baseline64)) = .fault
  unfold step
  rw [ite_eq_right (not_syscall _), ite_eq_right (not_rep _), step_initial]
  rfl

/-! ## Under `baseline64 ∪ {avx}` -/

/-- The state after `vpxor`. -/
def s1 : X86FState :=
  ⟨⟨((s0 (avxConfig avx64)).m.state.writeXmmVex (Silmaril.X86.Features.Avx.vreg 0)
      (((s0 (avxConfig avx64)).m.state.ymm (Silmaril.X86.Features.Avx.vreg 0) ^^^
        (s0 (avxConfig avx64)).m.state.ymm (Silmaril.X86.Features.Avx.vreg 0)).setWidth 128)).advance 4,
    (s0 (avxConfig avx64)).m.memory⟩, none⟩

theorem not_wire_vpxor (rest : List Byte) :
    Silmaril.X86.Ext.Wire.decode ([0xc5, 0xf9, 0xef, 0xc0] ++ rest) = none := by rfl

theorem spans_initial :
    spansAt defaultSpans (avxConfig avx64).exts (s0 (avxConfig avx64)).m =
      some [((s0 (avxConfig avx64)).m.state.core.rip, 4)] := by
  have hw := window_decode (avxConfig avx64)
  obtain ⟨rest, image⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow
    (limit := Silmaril.X86.maxInstrLength) (loaded_code_fetched (avxConfig avx64)) (by decide)
  have hext : Silmaril.X86.Ext.decode (Silmaril.X86.fetchWindow (s0 (avxConfig avx64)).m.memory
      Silmaril.X86.maxInstrLength (s0 (avxConfig avx64)).m.state.core.rip.toNat) = none := by
    rw [initial_rip, ← image]
    exact Silmaril.X86.Features.Avx.ext_decode_encode vpxor
      ([0xb8, 0x3c, 0, 0, 0, 0x29, 0xff, 0x0f, 0x05] ++ rest)
  have hnot : ∀ i n, Silmaril.X86.Ext.fetch (s0 (avxConfig avx64)).m.memory
      (s0 (avxConfig avx64)).m.state.core.rip.toNat ≠ .decoded i n := by
    intro i n h
    obtain ⟨bytes, fb, dec⟩ := Silmaril.X86.Ext.fetch_eq_decoded_iff.mp h
    obtain ⟨more, hmore⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow fb
      (limit := Silmaril.X86.maxInstrLength) (Silmaril.X86.Ext.decode_length dec).2.2.1
    have := Silmaril.X86.Ext.decode_append more dec
    rw [hmore, hext] at this
    cases this
  unfold spansAt
  cases hf : Silmaril.X86.Ext.fetch (s0 (avxConfig avx64)).m.memory
      (s0 (avxConfig avx64)).m.state.core.rip.toNat with
  | decoded i n => exact absurd hf (hnot i n)
  | truncated | undecodable =>
    simp only
    rw [show Silmaril.X86.Features.extDecode (avxConfig avx64).exts
        (Silmaril.X86.fetchWindow (s0 (avxConfig avx64)).m.memory Silmaril.X86.maxInstrLength
          (s0 (avxConfig avx64)).m.state.core.rip.toNat) =
        some ⟨Silmaril.X86.Features.Avx.ext, vpxor, 4⟩ from by
      change Silmaril.X86.Features.extDecode [Silmaril.X86.Features.Avx.ext] _ = _
      simp only [Silmaril.X86.Features.extDecode, Silmaril.X86.Features.Avx.ext_decode, hw]]
    have hws : wireSpans (Silmaril.X86.fetchWindow (s0 (avxConfig avx64)).m.memory
        Silmaril.X86.maxInstrLength (s0 (avxConfig avx64)).m.state.core.rip.toNat) 4
        (s0 (avxConfig avx64)).m.state = none := by
      unfold wireSpans
      rw [initial_rip, ← image, show code ++ rest = [0xc5, 0xf9, 0xef, 0xc0] ++
        ([0xb8, 0x3c, 0, 0, 0, 0x29, 0xff, 0x0f, 0x05] ++ rest) from rfl, not_wire_vpxor]
    simp only [defaultSpans, ExtSpans.orElse, hws, avxSpans, hw]
    rfl

theorem step_avx :
    (x86Features (avxConfig avx64)).step image.segments (s0 (avxConfig avx64)) =
      .ok ⟨s1, [((s0 (avxConfig avx64)).m.state.core.rip, 4)]⟩ := by
  change step defaultSpans (avxConfig avx64) (s0 (avxConfig avx64)) = _
  unfold step
  rw [ite_eq_right (not_syscall _), ite_eq_right (not_rep _), step_initial, spans_initial]
  rfl

/-! ### The integer tail, through `step_native` -/

theorem tail_fetched (offset len : Nat) (h : offset + len ≤ 13) (h' : offset < 13) :
    s1.m.memory.fetchBytes (image.initPc + offset) len = some ((code.drop offset).take len) :=
  code_at (avxConfig avx64) offset len h h'

/-- Integer steps of the tail are native steps. -/
theorem step_of_native (s : X86FState) {i : Silmaril.X86.Ext.Instr} {n : Nat} {bytes : List Byte}
    (fetched : s.m.memory.fetchBytes s.m.state.core.rip.toNat n = some bytes)
    (decoded : Silmaril.X86.Ext.decode bytes = some (i, n))
    (hb : Silmaril.X86.Features.baseCheck avx64 i = none) :
    step defaultSpans (avxConfig avx64) s = liftResult s.m.state (x86NativeStep (proj s)) :=
  step_native _ defaultSpans s
    (.inr ⟨i, n, Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩, hb⟩)

def s2 : X86FState := embed s1.m.state (movExitNumber (proj s1))
def s3 : X86FState := embed s2.m.state (zeroExitStatus (proj s2))
def s4 : X86FState := { s3 with pending := some 60 }

theorem s1_rip : s1.m.state.core.rip.toNat = image.initPc + 4 := by decide
theorem s2_rip : s2.m.state.core.rip.toNat = image.initPc + 9 := by decide
theorem s3_rip : s3.m.state.core.rip.toNat = image.initPc + 11 := by decide

theorem step_s1 : step defaultSpans (avxConfig avx64) s1 =
    .ok ⟨s2, [(s1.m.state.core.rip, 5)]⟩ := by
  have fetched : s1.m.memory.fetchBytes s1.m.state.core.rip.toNat 5 = some [0xb8, 0x3c, 0, 0, 0] := by
    rw [s1_rip]; exact tail_fetched 4 5 (by decide) (by decide)
  have decoded : Silmaril.X86.Ext.decode [0xb8, 0x3c, 0, 0, 0] = some (.movI32 .rax 60, 5) := by
    decide +kernel
  rw [step_of_native s1 fetched decoded rfl]
  have ns : (proj s1).m.memory.fetchBytes (proj s1).m.core.rip.toNat 2 ≠ some [0x0f, 0x05] := by
    change s1.m.memory.fetchBytes s1.m.state.core.rip.toNat 2 ≠ _
    rw [s1_rip, tail_fetched 4 2 (by decide) (by decide)]
    decide
  rw [x86NativeStep_of_fetch (proj s1) ns fetched decoded,
    show X86Accesses.canonical (proj s1).m.core 5 (.movI32 .rax 60) = [] from rfl, mov_execution]
  rfl

theorem step_s2 : step defaultSpans (avxConfig avx64) s2 =
    .ok ⟨s3, [(s2.m.state.core.rip, 2)]⟩ := by
  have fetched : s2.m.memory.fetchBytes s2.m.state.core.rip.toNat 2 = some [0x29, 0xff] := by
    rw [s2_rip]; exact tail_fetched 9 2 (by decide) (by decide)
  have decoded : Silmaril.X86.Ext.decode [0x29, 0xff] =
      some (.alu .d .sub (.reg .rdi) .rdi, 2) := by decide +kernel
  rw [step_of_native s2 fetched decoded rfl]
  have ns : (proj s2).m.memory.fetchBytes (proj s2).m.core.rip.toNat 2 ≠ some [0x0f, 0x05] := by
    change s2.m.memory.fetchBytes s2.m.state.core.rip.toNat 2 ≠ _
    rw [fetched]
    decide
  rw [x86NativeStep_of_fetch (proj s2) ns fetched decoded,
    show X86Accesses.canonical (proj s2).m.core 2 (.alu .d .sub (.reg .rdi) .rdi) = [] from rfl,
    sub_execution]
  rfl

theorem step_s3 : step defaultSpans (avxConfig avx64) s3 =
    .ok ⟨s4, [(s3.m.state.core.rip, 2)]⟩ := by
  have fetched : s3.m.memory.fetchBytes s3.m.state.core.rip.toNat 2 = some [0x0f, 0x05] := by
    rw [s3_rip]; exact tail_fetched 11 2 (by decide) (by decide)
  rw [step_native _ defaultSpans s3 (.inl fetched),
    x86NativeStep_syscall (proj s3) fetched rfl]
  rfl

/-! ### The process run -/

def c1 : LPS.Config (x86Features (avxConfig avx64)) := ⟨s1, (initial (avxConfig avx64)).model⟩
def c2 : LPS.Config (x86Features (avxConfig avx64)) := ⟨s2, (initial (avxConfig avx64)).model⟩
def c3 : LPS.Config (x86Features (avxConfig avx64)) := ⟨s3, (initial (avxConfig avx64)).model⟩
def c4 : LPS.Config (x86Features (avxConfig avx64)) := ⟨s4, (initial (avxConfig avx64)).model⟩
def c5 : LPS.Config (x86Features (avxConfig avx64)) :=
  ⟨s4, (initial (avxConfig avx64)).model.withHalted 0⟩

theorem exit_path (refused : RefusalFilter) :
    Star image.segments NativeX86.extendedSyscallSpec refused (initial (avxConfig avx64))
      [.exitEv 0 (initial (avxConfig avx64)).model.fs] c5 := by
  have i1 : SStep image.segments NativeX86.extendedSyscallSpec refused
      (initial (avxConfig avx64)) [] (.next c1) :=
    SStep.instr rfl rfl (Progress.accountStep_of_noLazy (isa := x86Features (avxConfig avx64))
      (segments := image.segments) (s0 (avxConfig avx64)) s1 _ _ rfl step_avx)
  have i2 : SStep image.segments NativeX86.extendedSyscallSpec refused c1 [] (.next c2) :=
    SStep.instr rfl rfl (Progress.accountStep_of_noLazy (isa := x86Features (avxConfig avx64))
      (segments := image.segments) c1.ms s2 _ _ rfl step_s1)
  have i3 : SStep image.segments NativeX86.extendedSyscallSpec refused c2 [] (.next c3) :=
    SStep.instr rfl rfl (Progress.accountStep_of_noLazy (isa := x86Features (avxConfig avx64))
      (segments := image.segments) c2.ms s3 _ _ rfl step_s2)
  have i4 : SStep image.segments NativeX86.extendedSyscallSpec refused c3 [] (.next c4) :=
    SStep.instr rfl rfl (Progress.accountStep_of_noLazy (isa := x86Features (avxConfig avx64))
      (segments := image.segments) c3.ms s4 _ _ rfl step_s3)
  have i5 : SStep image.segments NativeX86.extendedSyscallSpec refused c4
      [.exitEv 0 (initial (avxConfig avx64)).model.fs] (.next c5) :=
    SStep.exit rfl rfl (native_exit_zero _ _ rfl rfl) rfl rfl
  exact .step i1 (.step i2 (.step i3 (.step i4 (.step i5 (.refl _)))))

/-- **Under `baseline64 ∪ {avx}`**, the launch retires `vpxor` and exits 0. -/
theorem avx_exit_trace (refused : RefusalFilter) :
    (X86Launch.runWith (x86Features (avxConfig avx64)) NativeX86.extendedSyscallSpec refused
      snapshot sourceAllocLimit entry input).traces [.exitEv 0 input.fs] :=
  ⟨_, c5, exit_path refused, ⟨[], rfl⟩⟩

theorem avx_not_allErrors (refused : RefusalFilter) :
    ¬ (X86Launch.runWith (x86Features (avxConfig avx64)) NativeX86.extendedSyscallSpec refused
      snapshot sourceAllocLimit entry input).allErrors :=
  Progress.halting_path_not_allTracesError (exit_path refused) (by decide)

/-! ## Under `baseline64` -/

theorem fault_step (refused : RefusalFilter) :
    SStep image.segments NativeX86.extendedSyscallSpec refused (initial (avxConfig baseline64)) []
      .error := by
  refine SStep.instrFault rfl rfl ?_
  show accountStep (x86Features (avxConfig baseline64)) image.segments (s0 (avxConfig baseline64))
    (initial (avxConfig baseline64)).model = .fault
  unfold accountStep
  rw [step_baseline64]
  rfl

/-- **Under `baseline64`**, the launch dies on its first instruction (SIGILL). -/
theorem baseline64_errors (refused : RefusalFilter) :
    (X86Launch.runWith (x86Features (avxConfig baseline64)) NativeX86.extendedSyscallSpec refused
      snapshot sourceAllocLimit entry input).errors :=
  ⟨[], _, [], .refl _, fault_step refused⟩

/-- Every execution errors: the only step from the launch is the death. -/
theorem baseline64_allErrors (refused : RefusalFilter) :
    (X86Launch.runWith (x86Features (avxConfig baseline64)) NativeX86.extendedSyscallSpec refused
      snapshot sourceAllocLimit entry input).allErrors := by
  refine .intro ⟨[], _, fault_step refused⟩ ?_
  intro evs c' s
  cases s with
  | instr h1 h2 h3 =>
    have : accountStep (x86Features (avxConfig baseline64)) image.segments
        (s0 (avxConfig baseline64)) (initial (avxConfig baseline64)).model = .fault := by
      unfold accountStep
      rw [step_baseline64]
      rfl
    cases this.symm.trans h3
  | syscall h1 h2 => cases h2
  | exit h1 h2 => cases h2
  | killed h1 h2 => cases h2

/-- **No upward transfer without settling**: `baseline64 ≤ baseline64 ∪ {avx}`,
every execution errors under the first, and an execution exits under the
second. -/
theorem no_upward_transfer (refused : RefusalFilter) :
    avxConfig baseline64 ≤ avxConfig avx64 ∧
      (X86Launch.runWith (x86Features (avxConfig baseline64)) NativeX86.extendedSyscallSpec refused
        snapshot sourceAllocLimit entry input).allErrors ∧
      ¬ (X86Launch.runWith (x86Features (avxConfig avx64)) NativeX86.extendedSyscallSpec refused
        snapshot sourceAllocLimit entry input).allErrors :=
  ⟨baseline_le_avx, baseline64_allErrors refused, avx_not_allErrors refused⟩

end Silmaril.Process.LPS.Machines.X86Features.Controls
