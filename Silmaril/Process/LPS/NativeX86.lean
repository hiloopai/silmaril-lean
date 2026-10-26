module

public import Silmaril.Process.LPS.Run

/-! # Native x86-64 numbering for the translated LPS arms

The ninety records below pair pinned LPS f1006fe8 syscall arms with Linux v6.12
native x86-64 numbers. This module rekeys actual `SpecArm`s, preserving their
translation status and their specifications. It does not implement any pending
arm or certify architecture-dependent structure layouts.

The machine retains the native RAX value. Only a selected specification's input
and the reference refusal classifier are adapted to the reference number; no
synthetic out-of-table number is installed in machine state. Tables are built
from a supplied reference table. Newly translated families need an explicit
ABI review before the native table enables them: renumbering alone does not
translate x86 structures. Linux's trailing `clone` arguments also differ;
the pinned LPS fork-only arm reads just the flags, so that difference is inert
for that arm, but would matter for a more extensive clone model.
-/

@[expose] public section
set_option autoImplicit false
namespace Silmaril.Process.LPS.NativeX86

structure NativeNumber where
  referenceNo : Nat
  nativeNo : Nat
  name : String
  deriving DecidableEq, Repr

def numbers : List NativeNumber := [
  ⟨17, 79, "getcwd"⟩,
  ⟨19, 290, "eventfd2"⟩,
  ⟨20, 291, "epoll_create1"⟩,
  ⟨21, 233, "epoll_ctl"⟩,
  ⟨22, 281, "epoll_pwait"⟩,
  ⟨23, 32, "dup"⟩,
  ⟨24, 292, "dup3"⟩,
  ⟨25, 72, "fcntl"⟩,
  ⟨29, 16, "ioctl"⟩,
  ⟨32, 73, "flock"⟩,
  ⟨35, 263, "unlinkat"⟩,
  ⟨46, 77, "ftruncate"⟩,
  ⟨48, 269, "faccessat"⟩,
  ⟨56, 257, "openat"⟩,
  ⟨57, 3, "close"⟩,
  ⟨59, 293, "pipe2"⟩,
  ⟨61, 217, "getdents64"⟩,
  ⟨62, 8, "lseek"⟩,
  ⟨63, 0, "read"⟩,
  ⟨64, 1, "write"⟩,
  ⟨65, 19, "readv"⟩,
  ⟨66, 20, "writev"⟩,
  ⟨67, 17, "pread64"⟩,
  ⟨68, 18, "pwrite64"⟩,
  ⟨72, 270, "pselect6"⟩,
  ⟨73, 271, "ppoll"⟩,
  ⟨78, 267, "readlinkat"⟩,
  ⟨79, 262, "newfstatat"⟩,
  ⟨80, 5, "fstat"⟩,
  ⟨82, 74, "fsync"⟩,
  ⟨83, 75, "fdatasync"⟩,
  ⟨85, 283, "timerfd_create"⟩,
  ⟨93, 60, "exit"⟩,
  ⟨94, 231, "exit_group"⟩,
  ⟨96, 218, "set_tid_address"⟩,
  ⟨98, 202, "futex"⟩,
  ⟨101, 35, "nanosleep"⟩,
  ⟨113, 228, "clock_gettime"⟩,
  ⟨119, 144, "sched_setscheduler"⟩,
  ⟨123, 204, "sched_getaffinity"⟩,
  ⟨124, 24, "sched_yield"⟩,
  ⟨130, 200, "tkill"⟩,
  ⟨131, 234, "tgkill"⟩,
  ⟨132, 131, "sigaltstack"⟩,
  ⟨134, 13, "rt_sigaction"⟩,
  ⟨135, 14, "rt_sigprocmask"⟩,
  ⟨144, 106, "setgid"⟩,
  ⟨146, 105, "setuid"⟩,
  ⟨147, 117, "setresuid"⟩,
  ⟨149, 119, "setresgid"⟩,
  ⟨157, 112, "setsid"⟩,
  ⟨158, 115, "getgroups"⟩,
  ⟨159, 116, "setgroups"⟩,
  ⟨160, 63, "uname"⟩,
  ⟨167, 157, "prctl"⟩,
  ⟨169, 96, "gettimeofday"⟩,
  ⟨172, 39, "getpid"⟩,
  ⟨174, 102, "getuid"⟩,
  ⟨175, 107, "geteuid"⟩,
  ⟨176, 104, "getgid"⟩,
  ⟨177, 108, "getegid"⟩,
  ⟨178, 186, "gettid"⟩,
  ⟨198, 41, "socket"⟩,
  ⟨199, 53, "socketpair"⟩,
  ⟨200, 49, "bind"⟩,
  ⟨201, 50, "listen"⟩,
  ⟨202, 43, "accept"⟩,
  ⟨203, 42, "connect"⟩,
  ⟨204, 51, "getsockname"⟩,
  ⟨205, 52, "getpeername"⟩,
  ⟨206, 44, "sendto"⟩,
  ⟨207, 45, "recvfrom"⟩,
  ⟨208, 54, "setsockopt"⟩,
  ⟨209, 55, "getsockopt"⟩,
  ⟨210, 48, "shutdown"⟩,
  ⟨211, 46, "sendmsg"⟩,
  ⟨212, 47, "recvmsg"⟩,
  ⟨214, 12, "brk"⟩,
  ⟨215, 11, "munmap"⟩,
  ⟨216, 25, "mremap"⟩,
  ⟨220, 56, "clone"⟩,
  ⟨222, 9, "mmap"⟩,
  ⟨226, 10, "mprotect"⟩,
  ⟨233, 28, "madvise"⟩,
  ⟨242, 288, "accept4"⟩,
  ⟨260, 61, "wait4"⟩,
  ⟨261, 302, "prlimit64"⟩,
  ⟨278, 318, "getrandom"⟩,
  ⟨435, 435, "clone3"⟩,
  ⟨439, 439, "faccessat2"⟩
]

def byNative (number : Nat) : Option NativeNumber :=
  numbers.find? (fun row => row.nativeNo = number)

def byReference (number : Nat) (name : String) : Option NativeNumber :=
  numbers.find? (fun row => row.referenceNo = number ∧ row.name = name)

/-- Preserve the complete memory views and arguments at the ABI boundary. -/
def referenceInputFor (row : NativeNumber) (input : SyscallInput) : SyscallInput :=
  { input with sysno := zw row.referenceNo }

def referenceInput (input : SyscallInput) : Option SyscallInput :=
  (byNative input.sysno.toNat).map (fun row => referenceInputFor row input)

/-- Rekey an actual translated/pending arm; the status is preserved exactly. -/
def rekey (row : NativeNumber) (source : SpecArm) : SpecArm :=
  { source with
    no := row.nativeNo
    spec := fun input => source.spec (referenceInputFor row input) }

/-- Arms reviewed for register/structure ABI compatibility in this milestone.
This is a review boundary, not a proof that the source models Linux hardware.
In particular, adding a reference `clone` or `stat` arm does not silently enable
it without review. `NativeX86Families` supports native layout-aware overrides.
The five FsCtl names have additionally been reviewed against family PR #3489:
same scalar narrowings/constants, no architecture-specific output structure.
Reviewing a name does not mark a pending reference translation as implemented. -/
def reviewedNames : List String :=
  ["close", "read", "write", "exit", "exit_group", "set_tid_address", "getpid",
   "getuid", "geteuid", "getgid", "getegid", "gettid", "brk", "munmap", "mmap",
   "wait4", "getrandom", "fcntl", "ioctl", "flock", "fsync", "fdatasync"]

def reviewedArm (row : NativeNumber) (source : SpecArm) : SpecArm :=
  if source.name ∈ reviewedNames then rekey row source
  else pendingArm row.nativeNo source.name

def table (reference : List SpecArm) : List SpecArm :=
  reference.filterMap fun source =>
    (byReference source.no source.name).map (fun row => reviewedArm row source)

/-- This is a native table of the actual LPS arms, not a parallel effects list. -/
def syscallSpec : Sys SyscallEffect := dispatch (table specTable)

/-- The source refusal classifier uses reference numbers too. Native callers
must use this adapter with the same reference specification that supplied their
arms. Architecture-only extensions have no reference spurious-refusal family. -/
def refusalFilter (reference : Sys SyscallEffect) (cfg : SpuriousCfg) : RefusalFilter :=
  fun input model effect =>
    match referenceInput input with
    | some source => spuriousRefusalCfg reference cfg source model effect
    | none => False

@[simp] theorem rekey_status (row : NativeNumber) (source : SpecArm) :
    (rekey row source).status = source.status := rfl

@[simp] theorem rekey_name (row : NativeNumber) (source : SpecArm) :
    (rekey row source).name = source.name := rfl

@[simp] theorem rekey_number (row : NativeNumber) (source : SpecArm) :
    (rekey row source).no = row.nativeNo := rfl

theorem rekey_spec (row : NativeNumber) (source : SpecArm)
    (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect) :
    (rekey row source).spec input model outcome ↔
      source.spec (referenceInputFor row input) model outcome := Iff.rfl

@[simp] theorem referenceInputFor_args (row : NativeNumber) (input : SyscallInput) :
    (referenceInputFor row input).args = input.args := rfl

@[simp] theorem referenceInputFor_mem (row : NativeNumber) (input : SyscallInput) :
    (referenceInputFor row input).mem = input.mem := rfl

@[simp] theorem referenceInputFor_wmem (row : NativeNumber) (input : SyscallInput) :
    (referenceInputFor row input).wmem = input.wmem := rfl

theorem numbers_length : numbers.length = 90 := by decide

theorem native_numbers_nodup : (numbers.map NativeNumber.nativeNo).Nodup := by decide

theorem reference_numbers_nodup : (numbers.map NativeNumber.referenceNo).Nodup := by decide

/-- Every reference arm is accounted for, including pending arms and aliases. -/
theorem reference_surface :
    specTable.map (fun source => (source.no, source.name)) =
      numbers.map (fun row => (row.referenceNo, row.name)) := by decide

theorem table_length : (table specTable).length = 90 := by decide

theorem table_numbers_nodup : (armNumbers (table specTable)).Nodup := by decide

/-- Unknown native calls really stay unknown; no synthetic number is invented. -/
theorem unknown_999 : byNative 999 = none := by decide

theorem native_getpid : byNative 39 = some ⟨172, 39, "getpid"⟩ := by decide

theorem native_exit : byNative 60 = some ⟨93, 60, "exit"⟩ := by decide

/-- A new reference translation is held pending until its native ABI is reviewed. -/
theorem clone_stays_pending (spec : Sys SyscallEffect) :
    (reviewedArm ⟨220, 56, "clone"⟩ ⟨220, "clone", .translated, spec⟩).status =
      .pending := by simp [reviewedArm, reviewedNames, pendingArm]

theorem reviewedArm_status (row : NativeNumber) (source : SpecArm)
    (reviewed : source.name ∈ reviewedNames) :
    (reviewedArm row source).status = source.status := by
  simp [reviewedArm, reviewed, rekey]

theorem getpid_dispatch (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) (number : input.sysno = 39) :
    syscallSpec input model outcome ↔
      getpidSpec (referenceInputFor ⟨172, 39, "getpid"⟩ input) model outcome := by
  simp only [syscallSpec, dispatch, number]
  rfl

theorem unknown_dispatch (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) (number : input.sysno = 999) :
    syscallSpec input model outcome ↔ outcome = .unmodeled := by
  simp only [syscallSpec, dispatch, number]
  rfl

theorem unknown_not_refused (reference : Sys SyscallEffect) (cfg : SpuriousCfg)
    (input : SyscallInput) (model : Model) (effect : SyscallEffect)
    (number : input.sysno = 999) :
    ¬ refusalFilter reference cfg input model effect := by
  simp [refusalFilter, referenceInput, number, byNative, numbers]

end Silmaril.Process.LPS.NativeX86
