module

public import Silmaril.Process.LPS.Machines.X86Launch
public import Silmaril.Formats.ELF.Reader
public import Silmaril.Process.LPS.Machines.X86ArchPrctl

/-! # Nonempty static x86 launch controls

A tiny ELF64 executable with one PT_LOAD segment. Its header and program header
are checked against explicit file bytes by the existing Lean ELF reader. The
loaded snapshot uses those same bytes at the segment's advertised address.
Startup-register and address-profile facts concern the actual LPS initializer;
no total-correctness claim for this executable is made here.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Silmaril.Process.LPS.Machines.X86Launch.Controls

def header : Silmaril.Formats.ELF.Header :=
  ⟨0, 0, 2, 62, 1, 0x400078, 64, 0, 0, 64, 56, 1, 0, 0, 0⟩

def programHeader : Silmaril.Formats.ELF.ProgramHeader :=
  ⟨1, 5, 0, 0x400000, 0x400000, 129, 129, 4096⟩

/-- `mov eax,60; sub edi,edi; syscall`. -/
def code : List Byte := [0xb8, 0x3c, 0, 0, 0, 0x29, 0xff, 0x0f, 0x05]

def headerBytes : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
    zToLeBytes 2 2 ++ zToLeBytes 2 62 ++ zToLeBytes 4 1 ++ zToLeBytes 8 0x400078 ++
    zToLeBytes 8 64 ++ zToLeBytes 8 0 ++ zToLeBytes 4 0 ++ zToLeBytes 2 64 ++
    zToLeBytes 2 56 ++ zToLeBytes 2 1 ++ zToLeBytes 2 0 ++ zToLeBytes 2 0 ++ zToLeBytes 2 0

def programHeaderBytes : List Byte :=
  zToLeBytes 4 1 ++ zToLeBytes 4 5 ++ zToLeBytes 8 0 ++
    zToLeBytes 8 0x400000 ++ zToLeBytes 8 0x400000 ++ zToLeBytes 8 129 ++
    zToLeBytes 8 129 ++ zToLeBytes 8 4096

def fileBytes : List Byte := headerBytes ++ programHeaderBytes ++ code

theorem header_from_bytes :
    Silmaril.Formats.ELF.readHeader fileBytes.toArray = some header := by decide +kernel

theorem programHeaders_from_bytes :
    Silmaril.Formats.ELF.readProgramHeaders fileBytes.toArray header = some [programHeader] := by
  decide +kernel

theorem entry_code_from_bytes : fileBytes.drop 120 = code := by decide +kernel

def image : Image :=
  ⟨[⟨0x400000, 129, "rx", fileBytes⟩], 0x400078, ⟨0x400040, 56, 1⟩⟩

def snapshot : Snapshot := ⟨header, [programHeader], image⟩

def input : ProcInput where
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

def entry : ExecEntry :=
  ⟨0x7fffffffe000, 0x401000, 0x40000000, ⟨0, fun _ => 0⟩⟩

theorem header_matches : HeaderMatches snapshot := by
  simp [HeaderMatches, snapshot, header, image, programHeader]

theorem load_layout_matches : LoadLayoutMatches snapshot := by
  simp [LoadLayoutMatches, snapshot, image, ProgramHeaderMatches, programHeader,
    Segment.executable, Segment.writable, Segment.readable]

theorem entry_code_fetched :
    (initialMemory image.segments 0 []).fetchBytes image.initPc 9 = some code := by
  have permitted : (initialMemory image.segments 0 []).checkSpan .execute image.initPc 9 = true := by
    apply (Silmaril.Process.Memory.checkSpan_iff _ _ _ _).mpr
    refine ⟨by decide, by decide, ?_⟩
    intro offset bound
    simp [Silmaril.Process.Memory.permits, initialMemory, image, segmentRegion,
      segmentPermissions, Segment.readable, Segment.writable, Segment.executable,
      Silmaril.Process.Region.Contains, Silmaril.Process.Permissions.allows]
    change decide (4194304 ≤ 4194424 + offset ∧ 4194424 + offset < 4194433) = true
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
  have options : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
    change index < 9 at bound
    omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [code, List.zipIdx_cons, List.zipIdx_nil, Std.ExtHashMap.getElem_insert]

theorem entry_instruction_fetched :
    (initialMemory image.segments 0 []).fetchBytes image.initPc 5 = some [0xb8, 0x3c, 0, 0, 0] :=
  Silmaril.Process.Memory.readWith_sub_range entry_code_fetched
    (offset := 0) (len := 5) (by decide) (by decide)

theorem snapshot_valid : ValidSnapshot x86ExtNative snapshot := by
  refine ⟨header_matches, load_layout_matches, ?_, ?_, ?_, ?_⟩
  · simp only [snapshot, image, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq]
    decide +kernel
  · exact List.pairwise_singleton _ _
  · have fetched := Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨[0xb8, 0x3c, 0, 0, 0], entry_instruction_fetched,
        (by decide : Silmaril.X86.Ext.decode [0xb8, 0x3c, 0, 0, 0] =
          some (.movI32 .rax 60, 5))⟩
    change (match Silmaril.X86.Ext.fetch (initialMemory image.segments 0 []) image.initPc with
      | .decoded _ _ => true
      | _ => decide ((initialMemory image.segments 0 []).fetchBytes image.initPc 2 =
        some [0x0f, 0x05])) = true
    rw [fetched]
  · simp [memoryRead, findSegment, Segment.readable, Segment.byteAt, snapshot,
      image, zw, uns, fileBytes, headerBytes, programHeaderBytes, code, zToLeBytes, zb]
    decide +kernel

theorem input_valid : ValidInput input := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ValidArgv, input, totalArgBytes, pathHasSlash]
    · simp [ValidEnvp, input, totalArgBytes]
    · simp [input, ProcInput.fs, fsSeedTmp, Fs.ValidFs, Fs.sorted]
    · simp [input, Fs.KeysRelative]
    · unfold ValidCreds ValidId
      decide +kernel
    · unfold ValidNofile
      decide +kernel
    · unfold ValidSigmask
      decide +kernel
    · intro n
      rfl
  · rfl

theorem entry_valid : ValidEntry x86ExtNative snapshot entry input := by
  refine ⟨snapshot_valid, ?_⟩
  simp only [ValidBrk, snapshot, image, entry, input]
  decide +kernel

/-- A guarded launch has a concrete initial configuration, not an empty
valid-entry domain or an absent initialization relation. -/
theorem launch_nonempty :
    ∃ configuration, Launched x86ExtNative snapshot entry sourceAllocLimit input configuration :=
  (launch_exists_iff _ _ _ _ _).mpr ⟨input_valid, entry_valid⟩

theorem wrong_riscv_header_rejected :
    ¬ ∃ configuration,
      Launched x86ExtNative {snapshot with header := {header with machine := 243}}
        entry sourceAllocLimit input configuration :=
  wrong_machine_no_launch _ _ _ _ _ (by decide)

theorem misaligned_stack_rejected :
    ¬ ∃ configuration,
      Launched x86ExtNative snapshot {entry with sp := entry.sp + 1}
        sourceAllocLimit input configuration :=
  misaligned_stack_no_launch _ _ _ _ _ (by decide +kernel)

theorem stack_past_task_size_rejected :
    ¬ ValidEntry x86ExtNative snapshot {entry with sp := 0x800000000000} input := by
  intro valid
  have limit := valid.2.2.1
  have impossible : ¬ (uns (0x800000000000 : Word) ≤ x86LaunchBounds.spWindowHi) := by decide
  exact impossible limit

theorem startup_rsp :
    (init x86ExtNative snapshot entry sourceAllocLimit input).ms.m.core.read .rsp = entry.sp := by
  rfl

theorem startup_rip :
    (init x86ExtNative snapshot entry sourceAllocLimit input).ms.m.core.rip =
      natToWord image.initPc := rfl

theorem startup_no_tls :
    (init x86ExtNative snapshot entry sourceAllocLimit input).ms.m.core.fsBase = 0 := rfl

theorem startup_no_finalizer :
    (init x86ExtNative snapshot entry sourceAllocLimit input).ms.m.core.read .rdx = 0 := by
  rfl

theorem startup_no_pending_call :
    x86ExtNative.svcPending (init x86ExtNative snapshot entry sourceAllocLimit input).ms = none := rfl

theorem startup_uses_x86_stack :
    (init x86ExtNative snapshot entry sourceAllocLimit input).ms.m.memory =
      initialMemory snapshot.image.segments entry.sp (entryStack snapshot.image entry input) :=
  init_native_memory snapshot entry sourceAllocLimit input

theorem startup_uses_x86_address_space :
    (init x86ExtNative snapshot entry sourceAllocLimit input).model.addressSpace =
      x86AddressSpace := rfl

theorem startup_live :
    (init x86ExtNative snapshot entry sourceAllocLimit input).model.halted = none := rfl

theorem startup_fs :
    (init x86ExtNative snapshot entry sourceAllocLimit input).model.fs = input.fs := rfl

theorem startup_budget :
    (init x86ExtNative snapshot entry sourceAllocLimit input).model.vmmaps.limit = sourceAllocLimit := rfl

/-- Code is fetched from the actual initialized memory, beneath the symbolic
8 MiB stack reservation. No stack map is evaluated to prove this fact. -/
theorem loaded_code_fetched :
    (init x86ExtNative snapshot entry sourceAllocLimit input).ms.m.memory.fetchBytes
      image.initPc 9 = some code := by
  rw [init_native_memory]
  have permitted : (initialMemory snapshot.image.segments entry.sp (entryStack snapshot.image entry input)).checkSpan
      .execute image.initPc 9 = true := by
    apply (Silmaril.Process.Memory.checkSpan_iff _ _ _ _).mpr
    refine ⟨by decide, by decide, ?_⟩
    intro offset bound
    simp [Silmaril.Process.Memory.permits, initialMemory, snapshot, image, segmentRegion,
      segmentPermissions, Segment.readable, Segment.writable, Segment.executable,
      Silmaril.Process.Region.Contains, Silmaril.Process.Permissions.allows]
    change decide (4194304 ≤ 4194424 + offset ∧ 4194424 + offset < 4194433) = true
    exact decide_eq_true (by omega)
  apply Silmaril.Process.Memory.readWith_eq
    (initialMemory snapshot.image.segments entry.sp (entryStack snapshot.image entry input))
    .execute image.initPc code permitted
  intro index bound
  rw [initialMemory_below_stack_get]
  · exact Silmaril.Process.Memory.readWith_get entry_code_fetched index bound
  · change 0x400078 + index < entry.sp.toNat - stackMaxSize.toNat
    change index < 9 at bound
    have lower : entry.sp.toNat - stackMaxSize.toNat = 0x7fffff7fe000 := by decide
    rw [lower]
    omega
  · decide +kernel

theorem loaded_entry_instruction_fetched :
    (init x86ExtNative snapshot entry sourceAllocLimit input).ms.m.memory.fetchBytes
      image.initPc 5 = some [0xb8, 0x3c, 0, 0, 0] :=
  Silmaril.Process.Memory.readWith_sub_range loaded_code_fetched
    (offset := 0) (len := 5) (by decide) (by decide)

theorem minimal_hwcap_advertised :
    (AT_HWCAP, 0) ∈ auxiliaryEntries image entry.sp input := by
  simp [auxiliaryEntries, input]

theorem platform_string_advertised :
    (AT_PLATFORM, entry.sp + natToWord (platformOffset input.argv input.envp)) ∈
      auxiliaryEntries image entry.sp input := by
  simp [auxiliaryEntries]

end Silmaril.Process.LPS.Machines.X86Launch.Controls
