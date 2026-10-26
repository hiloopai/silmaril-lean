module

public import Silmaril.Process.LPS.Basic

/-!
# Architecture-specific user address bounds

The syscall buffer boundary and the launch policy are separate. In particular, the
literal LPS port has always used the Sv48 `TASK_SIZE` for syscall gates even when an
input declares Sv39 or Sv57. `legacySv48AddressSpace` retains that interpretation;
`riscvAddressSpace` is an explicit width-sensitive alternative.

The x86 profile fixes four-level paging. Its `TASK_SIZE` is one page below the Sv48
limit (Linux x86 `TASK_SIZE_MAX`). The x86 launch windows are checked against Linux
x86-64 v6.13-v6.18 ASLR in `Machines.X86LaunchAslr`: each window contains every
placement Linux produces for every `randomize_va_space` setting, `mmap_rnd_bits <= 32`,
stack rlimit, `stack_guard_gap` and layout choice (`linuxSp_mem_window`,
`linuxBrk_mem_window`, `linuxMmapBase_mem_window`).
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- The upper user-memory boundary used by kernel buffer and mapping checks.
This is distinct from a policy restricting initial stack and mmap placement. -/
structure AddressSpaceProfile where
  taskSize : Int
  deriving DecidableEq, Repr

/-- The unchanged buffer boundary of the literal LPS port. -/
def legacySv48AddressSpace : AddressSpaceProfile := ⟨taskSize⟩

/-- An explicitly selected width-sensitive RISC-V user-memory boundary. -/
def riscvAddressSpace (v : VaSize) : AddressSpaceProfile := ⟨vaTaskSize v⟩

/-- Linux x86-64 four-level `TASK_SIZE_MAX = (1 << 47) - PAGE_SIZE`. -/
def x86AddressSpace : AddressSpaceProfile := ⟨0x7ffffffff000⟩

/-- `access_ok` at an explicit architecture boundary. As in the upstream definition,
the caller supplies a nonnegative length (typically the unsigned value of a word). -/
def accessOkbFor (profile : AddressSpaceProfile) (base : Word) (len : Int) : Bool :=
  decide (len ≤ profile.taskSize) && decide (uns base ≤ profile.taskSize - len)

/-- Restricting the user boundary cannot admit a buffer the larger boundary rejects.
This is a buffer-check lemma, not a refinement theorem for complete process runs. -/
theorem accessOkbFor_mono {small large : AddressSpaceProfile}
    (h : small.taskSize ≤ large.taskSize) {base : Word} {len : Int}
    (ok : accessOkbFor small base len = true) :
    accessOkbFor large base len = true := by
  simp only [accessOkbFor, Bool.and_eq_true, decide_eq_true_eq] at ok ⊢
  exact ⟨le_trans ok.1 h, le_trans ok.2 (Int.sub_le_sub_right h len)⟩

/-- Launch-placement policy, separate from the syscall access boundary. -/
structure LaunchBounds where
  spWindowLo : Int
  spWindowHi : Int
  mmapBaseMin : Int
  mmapBaseMax : Int
  deriving DecidableEq, Repr

/-- The existing width-dependent RISC-V launch windows. This does not change the
legacy syscall boundary to `vaTaskSize`. -/
def riscvLaunchBounds (v : VaSize) : LaunchBounds :=
  ⟨vaSpWindowLo v, vaSpWindowHi v, vaMmapBaseMin v, vaMmapBaseMax v⟩

/-- The largest downward shift of the x86-64 stack VMA top below `STACK_TOP`:
`randomize_stack_top` subtracts up to `STACK_RND_MASK = 0x3fffff` pages (mm/util.c:341-355,
arch/x86/include/asm/elf.h:328-329 at v6.18), and `setup_arg_pages` then applies
`arch_align_stack` (at most 8191 bytes, then 16-byte alignment, arch/x86/kernel/process.c:1019-1023)
before `PAGE_ALIGN` (fs/exec.c:635-636), at most two more pages. That is
`(0x3fffff + 2) * 4096`, just over 16 GiB. -/
def x86StackTopShiftMax : Int := (0x3fffff + 2) * 4096

/-- x86 launch policy: the stack window reaches 2 GiB (LPS's entry-block allowance, as in
`va_sp_window_lo`) below the lowest randomized stack top, so it contains every initial
`rsp` of Linux x86-64 v6.13-v6.18 (`Machines.X86LaunchAslr.linuxSp_mem_window`). Before
this was checked, the window was the riscv64 2 GiB below `TASK_SIZE`, which excluded
most x86-64 stack placements (x86-64 randomizes the stack over 16 GiB, riscv64 over 1 GiB).
mmap bases lie above 64 KiB and at least 128 MiB below `TASK_SIZE`; every Linux base
satisfies this (`linuxMmapBase_mem_window`). The 64-KiB floor is the default
`mmap_min_addr`; Linux bases never come close to it. -/
def x86LaunchBounds : LaunchBounds :=
  ⟨x86AddressSpace.taskSize - x86StackTopShiftMax - 2 * 1024 * 1024 * 1024,
    x86AddressSpace.taskSize, 0x10000,
    x86AddressSpace.taskSize - 128 * 1024 * 1024⟩

theorem riscv_sv48_addressSpace : riscvAddressSpace .sv48 = legacySv48AddressSpace := rfl

/-- A buffer ending exactly at the x86 boundary is permitted. -/
theorem x86_access_last_byte :
    accessOkbFor x86AddressSpace 0x7fffffffefff 1 = true := by decide

/-- The first byte of the final Sv48 page is outside the x86 user boundary. -/
theorem x86_rejects_sv48_last_page :
    accessOkbFor x86AddressSpace 0x7ffffffff000 1 = false := by decide

theorem sv48_accepts_last_page :
    accessOkbFor legacySv48AddressSpace 0x7ffffffff000 1 = true := by decide

/-- The x86 boundary admits an empty range at its upper boundary. -/
theorem x86_access_empty_at_boundary :
    accessOkbFor x86AddressSpace 0x7ffffffff000 0 = true := by decide

theorem x86_rejects_empty_beyond_boundary :
    accessOkbFor x86AddressSpace 0x7ffffffff001 0 = false := by decide

theorem x86_access_implies_sv48 {base : Word} {len : Int}
    (h : accessOkbFor x86AddressSpace base len = true) :
    accessOkbFor legacySv48AddressSpace base len = true :=
  accessOkbFor_mono (by decide) h

theorem sv39_rejects_sv48_address :
    accessOkbFor (riscvAddressSpace .sv39) 0x4000000000 1 = false := by decide

theorem sv57_accepts_beyond_sv48 :
    accessOkbFor (riscvAddressSpace .sv57) 0x800000000000 1 = true := by decide

end Silmaril.Process.LPS
