module

public import Silmaril.Process.LPS.NativeX86AllStatements
public import Silmaril.Process.LPS.Machines.X86LaunchControls

/-! # Controls for the complete native x86-64 table

Per family, a positive dispatch example (the native number reaches the family's x86-64 arm,
translated) and a negative one (the riscv64 number of the same call does not reach it on
x86-64), all through `nativeTable` and checked by `decide`. Semantic examples show that the
installed specification is the family's x86-64 specification (`getpid`, the x86-64 `fstat`
layout, `read`), that the boundary guard declines, and that it is not always on.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86.All.Controls

open Silmaril.Process.LPS

/-- The name and status at a native number. -/
def at? (n : Nat) : Option (String × ArmStatus) :=
  (lookupArm nativeTable n).map fun a => (a.name, a.status)

/-! ## Per family: positive (native number) and negative (riscv64 number) -/

-- fs-io: read is 0 (riscv64 63, which is uname on x86-64)
theorem fsIo_positive : at? 0 = some ("read", .translated) := by decide +kernel
theorem fsIo_negative : at? 63 ≠ some ("read", .translated) := by decide +kernel
-- fs-meta: getcwd is 79 (riscv64 17, which is pread64 on x86-64)
theorem fsMeta_positive : at? 79 = some ("getcwd", .translated) := by decide +kernel
theorem fsMeta_negative : at? 17 = some ("pread64", .translated) := by decide +kernel
-- fs-ctl: fcntl is 72 (riscv64 25, which is mremap on x86-64)
theorem fsCtl_positive : at? 72 = some ("fcntl", .translated) := by decide +kernel
theorem fsCtl_negative : at? 25 = some ("mremap", .translated) := by decide +kernel
-- fd-events: pipe2 is 293 (riscv64 59, execve on x86-64: not modelled)
theorem fdEvents_positive : at? 293 = some ("pipe2", .translated) := by decide +kernel
theorem fdEvents_negative : at? 59 = none := by decide +kernel
-- mm: mmap is 9 (riscv64 222, timer_create on x86-64: not modelled)
theorem mm_positive : at? 9 = some ("mmap", .translated) := by decide +kernel
theorem mm_negative : at? 222 = none := by decide +kernel
-- exit: exit_group is 231 (riscv64 94, lchown on x86-64: not modelled)
theorem exit_positive : at? 231 = some ("exit_group", .translated) := by decide +kernel
theorem exit_negative : at? 94 = none := by decide +kernel
-- fork: clone is 56 (riscv64 220, semtimedop on x86-64: not modelled)
theorem fork_positive : at? 56 = some ("clone", .translated) := by decide +kernel
theorem fork_negative : at? 220 = none := by decide +kernel
-- kernel-sys: getpid is 39 (riscv64 172, iopl on x86-64: not modelled)
theorem kernelSys_positive : at? 39 = some ("getpid", .translated) := by decide +kernel
theorem kernelSys_negative : at? 172 = none := by decide +kernel
-- signal: rt_sigaction is 13 (riscv64 134, uselib on x86-64: not modelled)
theorem signal_positive : at? 13 = some ("rt_sigaction", .translated) := by decide +kernel
theorem signal_negative : at? 134 = none := by decide +kernel
-- futex: futex is 202 (riscv64 98, getrusage on x86-64: not modelled)
theorem futex_positive : at? 202 = some ("futex", .translated) := by decide +kernel
theorem futex_negative : at? 98 = none := by decide +kernel
-- socket: socket is 41 (riscv64 198, lremovexattr on x86-64: not modelled)
theorem socket_positive : at? 41 = some ("socket", .translated) := by decide +kernel
theorem socket_negative : at? 198 = none := by decide +kernel
-- uapi layouts: fstat is 5 (riscv64 80, which is chdir on x86-64: not modelled)
theorem uapi_positive : at? 5 = some ("fstat", .translated) := by decide +kernel
theorem uapi_negative : at? 80 = none := by decide +kernel
-- extensions: the legacy entry points and arch_prctl, outside the reference slots
theorem extension_open : at? 2 = some ("open", .translated) := by decide +kernel
theorem extension_getrlimit : at? 97 = some ("getrlimit", .translated) := by decide +kernel
theorem extension_archPrctl : at? 158 = some ("arch_prctl", .translated) := by decide +kernel
theorem extension_unknown : at? 999 = none := by decide +kernel

/-- In #3476's reviewed default table the `socket` slot is still pending; the complete table
makes it live (`socket_positive`). -/
theorem socket_was_pending :
    ((table specTable).filter (fun a => a.no = 41)).map (·.status) = [.pending] := by
  decide +kernel

/-! ## Semantic examples -/

theorem lookupArm_of_mem {t : List SpecArm} (nd : (armNumbers t).Nodup) {a : SpecArm}
    (mem : a ∈ t) : lookupArm t a.no = some a := by
  induction t with
  | nil => simp at mem
  | cons b r ih =>
    simp only [armNumbers, List.map_cons, List.nodup_cons] at nd
    simp only [lookupArm]
    rcases List.mem_cons.1 mem with rfl | mem
    · simp
    · have : b.no ≠ a.no := fun e => nd.1 (e ▸ List.mem_map_of_mem mem)
      simp only [this, ↓reduceIte]; exact ih nd.2 mem

/-- The family arm at a native number, by its unique membership. -/
theorem family_src {src : SpecArm} (mem : src ∈ familyX86Arms) :
    lookupArm familyX86Arms src.no = some src := lookupArm_of_mem familyX86Arms_nodup mem

theorem getpid_family :
    lookupArm familyX86Arms 39 = some (arm 39 "getpid" (fun _ => getpidSpec)) := rfl

theorem fstat_family :
    lookupArm familyX86Arms 5 =
      some (arm 5 "fstat" (fun i => fstatSpecX86 (fd32 (i.arg 0)) (i.arg 1))) := rfl

theorem read_family :
    lookupArm familyX86Arms 0 =
      some (arm 0 "read" (fun i => readSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2))) := rfl

/-- The native table's spec at a reference slot is the chaos form of the given family arm. -/
theorem dispatch_slot (row : NativeNumber) (mem : row ∈ numbers) (src : SpecArm)
    (family : lookupArm familyX86Arms row.nativeNo = some src)
    (input : SyscallInput) (number : input.sysno.toNat = row.nativeNo) (model : Model)
    (outcome : Outcome SyscallEffect) :
    dispatch nativeTable input model outcome ↔ (chaos src).spec input model outcome := by
  obtain ⟨src', srcMem, srcNo, -, h⟩ := dispatch_referenceSlot row mem input number
  have := family_src srcMem
  rw [srcNo, family] at this
  cases this
  exact h model outcome

/-- Positive semantic example: at 39 off the boundary, the native table is LPS's `getpid`. -/
theorem getpid_dispatch (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno.toNat = 39) (clear : boundarySuspect 39 input = false) :
    dispatch nativeTable input model outcome ↔ getpidSpec input model outcome := by
  rw [dispatch_slot ⟨172, 39, "getpid"⟩ (by decide) _ getpid_family input number]
  simp [chaos, sigaltstackChaos, epollOrderChaos, epollOrderDiffers, guard, arm, clear]

/-- Positive semantic example: at 5 off the boundary the native table is the 144-byte
x86-64 `fstat`, not LPS's riscv64 one. -/
theorem fstat_dispatch (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno.toNat = 5) (clear : boundarySuspect 5 input = false) :
    dispatch nativeTable input model outcome ↔
      fstatSpecX86 (fd32 (input.arg 0)) (input.arg 1) input model outcome := by
  rw [dispatch_slot ⟨80, 5, "fstat"⟩ (by decide) _ fstat_family input number]
  simp [chaos, sigaltstackChaos, epollOrderChaos, epollOrderDiffers, guard, arm, clear]

theorem read_dispatch (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno.toNat = 0) (clear : boundarySuspect 0 input = false) :
    dispatch nativeTable input model outcome ↔
      readSpecX86 (fd32 (input.arg 0)) (input.arg 1) (input.arg 2) input model outcome := by
  rw [dispatch_slot ⟨63, 0, "read"⟩ (by decide) _ read_family input number]
  simp [chaos, sigaltstackChaos, epollOrderChaos, epollOrderDiffers, guard, arm, clear]

/-- A concrete input. -/
def input (no : Nat) (args : List Word) : SyscallInput :=
  ⟨BitVec.ofNat 64 no, args, fun _ => none, fun _ => none⟩

/-- The guard is not always on: ordinary arguments are clear. -/
theorem fstat_clear : boundarySuspect 5 (input 5 [3, 0x7ffffff00000]) = false := by decide

/-- A `struct stat` pointer 100 bytes below `TASK_SIZE_MAX` is in the band. -/
theorem fstat_band : boundarySuspect 5 (input 5 [3, 0x7ffffffff000 - 100]) = true := by decide

/-- 200 bytes below is not (the 144-byte object fits). -/
theorem fstat_below_band : boundarySuspect 5 (input 5 [3, 0x7ffffffff000 - 200]) = false := by
  decide

/-- `read` has no constant-size pointer: a buffer in the last page is exact. -/
theorem read_last_page_clear : boundarySuspect 0 (input 0 [0, 0x7ffffffff000 - 100, 50]) = false := by
  decide

/-- Every register in `[TASK_SIZE_MAX, 2^47]` is suspect. -/
theorem guard_window : boundarySuspect 39 (input 39 [0x7ffffffff000]) = true := by decide

/-- Negative semantic example: in the band, fstat only declines (no `-EFAULT` claim). -/
theorem fstat_band_declines (model : Model) (outcome : Outcome SyscallEffect) :
    dispatch nativeTable (input 5 [3, 0x7ffffffff000 - 100]) model outcome ↔
      outcome = .unmodeled := by
  rw [dispatch_slot ⟨80, 5, "fstat"⟩ (by decide) _ fstat_family _ (by decide)]
  simp only [chaos, sigaltstackChaos, arm]
  exact guard_spec_of_suspect _ _ _ _ (by decide)

/-! ## The extensions' refusal families -/

/-- The reading in which no family may fail without cause. -/
def noFailCfg : SpuriousCfg := ⟨false, false, false, false, false, false⟩

/-- `fork` (57) has `clone`'s injected family under the extended reading, none under the
catalogue-only one, in the reading where no family may fail without cause. -/
theorem fork_family_off :
    injectedFamilyOffX86Ext noFailCfg (input 57 []) = true ∧
      injectedFamilyOffX86 noFailCfg (input 57 []) = false := by
  decide

/-- `clone`'s `EAGAIN` is a refusal; for `fork` only under the extended reading. -/
theorem fork_eagain_refusal (m : Model) :
    refusalBX86Ext (input 57 []) m (errnoRet EAGAIN) = true ∧
      refusalBX86 (input 57 []) m (errnoRet EAGAIN) = false :=
  ⟨rfl, rfl⟩

/-- Negative: an unmapped extension (`stat`, 4) has no family under either reading. -/
theorem stat_family_none :
    injectedFamilyOffX86Ext noFailCfg (input 4 []) = false := by decide

/-- Positive on the catalogue: `openat` (257) is refused as LPS's `openat` (56). -/
theorem openat_family_off :
    injectedFamilyOffX86Ext noFailCfg (input 257 []) = true := by decide

/-! ## The domain controls -/

theorem fixture_input_quantified :
    ValidInputFor none false Machines.X86Launch.Controls.input :=
  ⟨Machines.X86Launch.Controls.input_valid.1, rfl, trivial⟩

theorem fixture_input_minimal :
    ValidInputFor (some minimal) false Machines.X86Launch.Controls.input :=
  (validInputFor_minimal false _).1 ⟨Machines.X86Launch.Controls.input_valid, rfl⟩

theorem fixture_low : ∀ segment ∈ Machines.X86Launch.Controls.snapshot.image.segments,
    (segment.base : Int) + segment.size ≤ spWitnessLevel - stackMaxSize := by
  decide +kernel

theorem fixture_reserved :
    reservedTop (segmentsReserved Machines.X86Launch.Controls.snapshot.image.segments) ≤ 2 ^ 62 := by
  decide +kernel

/-- The general witness applies to the checked exit ELF: its domain is inhabited for every
entry draw, through `validEntry_witness`, not through a hand-picked entry. -/
theorem fixture_domain (draw : EntryDraw) :
    ∃ plainEntry sanitizedEntry,
      (profile Machines.x86ExtNative none).validEntry Machines.X86Launch.Controls.snapshot
          plainEntry Machines.X86Launch.Controls.input ∧
        (profile Machines.x86ExtNative none).validEntry Machines.X86Launch.Controls.snapshot
          sanitizedEntry Machines.X86Launch.Controls.input ∧
        plainEntry.draw = draw ∧ sanitizedEntry.draw = draw :=
  domain_nonempty _ none _ _ Machines.X86Launch.Controls.snapshot_valid
    Machines.X86Launch.Controls.snapshot_valid fixture_low fixture_low fixture_reserved
    fixture_reserved false _ fixture_input_quantified draw

end Silmaril.Process.LPS.NativeX86.All.Controls
